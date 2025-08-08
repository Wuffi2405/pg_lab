#include <float.h>

#include "postgres.h"
#include "fmgr.h"
#include "catalog/pg_statistic.h"
#include "lib/stringinfo.h"
#include "optimizer/geqo.h"
#include "optimizer/joininfo.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/tlist.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/selfuncs.h"

#include "ues.h"

PG_MODULE_MAGIC;

extern join_search_hook_type join_search_hook;

extern PGDLLEXPORT void _PG_init(void);
extern PGDLLEXPORT void _PG_fini(void);

static bool ues_enabled = false;

static join_search_hook_type prev_join_search_hook = NULL;

RelOptInfo* ues_join_search(PlannerInfo *root, int levels_needed, List *initial_rels);

static UesState*
ues_join_search_init(PlannerInfo *root)
{
    UesState *state = palloc0(sizeof(UesState));
    state->current_intermediate = NULL;
    state->current_bound        = 0;
    state->joined_keys          = NIL;
    state->candidate_keys       = NIL;
    state->expanding_joins      = NIL;
    state->filter_joins         = NIL;

    root->join_search_private = state;
    return state;
}

static void
ues_join_search_cleanup(PlannerInfo *root)
{
    UesState *state = root->join_search_private;
    list_free_deep(state->joined_keys);
    list_free_deep(state->candidate_keys);
    //list_free_deep(state->expanding_joins);
    //list_free_deep(state->filter_joins);
    pfree(state);
    root->join_search_private = NULL;
}

static bool
ues_supported_query(PlannerInfo *root)
{
    /*
     * TODO
     * We probably need an expression_walker to do this properly.
     * Expect some (read: a lot) of backend crashes until we do so.
     */
    return root->parse->commandType == CMD_SELECT &&
        root->ec_merging_done && root->eq_classes != NIL &&
        bms_is_empty(root->outer_join_rels) &&
        root->parse->setOperations == NULL;
}

static void
ues_print_state(PlannerInfo *root, UesState *ues_state)
{
    ListCell    *lc;
    StringInfo   msg = makeStringInfo();
    int          i = -1;

    appendStringInfo(msg, "\n  Current intermediate: ");
    if (ues_state->current_intermediate)
    {
        while ((i = bms_next_member(ues_state->current_intermediate->relids, i)) >= 0)
        {
            RangeTblEntry *baserel = root->simple_rte_array[i];
            appendStringInfo(msg, "%s ", baserel->eref->aliasname);
        }
        appendStringInfo(msg, "[%f]\n", ues_state->current_bound);
    }
    else
    {
        appendStringInfo(msg, "(not yet selected)\n");
    }

    appendStringInfo(msg, "  Candidate keys:");
    foreach(lc, ues_state->candidate_keys)
    {
        UesJoinKey  *key = (UesJoinKey *) lfirst(lc);
        Oid          rel = root->simple_rte_array[key->baserel->relid]->relid;
        
        char *relname = get_rel_name(rel);
        char *attname = get_attname(rel, key->join_key->varattno, false);
        char *keytype = key->key_type == KT_PRIMARY ? " [PK]" : (key->key_type == KT_FOREIGN ? " [FK]" : "");
        appendStringInfo(msg, "\n\t%s.%s: MF=%f%s;", relname, attname, key->max_freq, keytype);
    }
    
    //elog(INFO, "UES state: %s", msg->data);
    destroyStringInfo(msg);
}


/*
 * Determine all join keys, fetch their maximum frequency and check for any PK/FK constraints.
 *
 * This function assumes that the UesState has already been initialized and attached to the PlannerInfo.
 */
static void
ues_init_baserels(PlannerInfo *root, List **rels)
{
    ListCell    *relc, /* list cell for relations */
                *ecc;  /* list cell for equivalence classes */
    UesState    *ues_state = (UesState*) root->join_search_private;

    foreach(relc, *rels)
    {
        RelOptInfo  *baserel = lfirst(relc);
        int          i = -1; /* index into the equivalence classes */

        if (!baserel->has_eclass_joins)
            ereport(ERROR, (errcode(ERRCODE_ASSERT_FAILURE),
                errmsg("Cross join not supported for UES. This should never be called.")));

        /*
         * The join keys of the current relation are spread across different equivalence classes.
         * Each EC corresponds to a different partition of columns that are equi-joined together in the join graph.
         * So, for each EC we need to extract the specific join key (i.e. its Var) that belongs to the current relation.
         * Based on the Var, we can then determine the maximum frequency as well as index structures on the join key.
         */

        while ((i = bms_next_member(baserel->eclass_indexes, i)) >= 0)
        {
            EquivalenceClass    *eqc = (EquivalenceClass*) list_nth(root->eq_classes, i);
            EquivalenceMember   *em = NULL;
            UesJoinKey          *key = NULL;
            AttStatsSlot         sslot;
            VariableStatData     vardata;
            Freq                 max_freq;
            KeyType              key_type = KT_NONE;

            if (eqc->ec_has_const)
                continue;

            foreach(ecc, eqc->ec_members)
            {
                em = (EquivalenceMember *) lfirst(ecc);
                if (bms_equal(em->em_relids, baserel->relids))
                    break;
            }


            Assert(em != NULL);
            Assert(IsA(em->em_expr, Var));

            /* We found the Var, use it to determine the frequency */

            examine_variable(root, (Node *) em->em_expr, 0, &vardata);
            get_attstatsslot(&sslot, vardata.statsTuple, STATISTIC_KIND_MCV, InvalidOid,
                             ATTSTATSSLOT_VALUES | ATTSTATSSLOT_NUMBERS);

            if (sslot.nvalues > 0)
            {
                /* We found an MCV list, use it */
                max_freq = sslot.numbers[0] * baserel->tuples; /* index 0 is the highest frequency */
            }
            else
            {
                /* No MCV found, assume equal distribution */
                bool    default_est; /* we don't use this variable, but PG wants it */
                double  ndistinct;

                ndistinct = get_variable_numdistinct(&vardata, &default_est);

                if (ndistinct < 0) /* negative means ND is a fraction of the table size, unwrap it */
                    ndistinct *= -1.0 * baserel->tuples;
                max_freq = baserel->tuples / ndistinct;
            }

            /* Now, lets also check for index constraints */

            if (vardata.isunique)
            {
                key_type = KT_PRIMARY;
            }
            else if (root->fkey_list != NIL)
            {
                ListCell *fkc;
                foreach(fkc, root->fkey_list)
                {
                    ForeignKeyOptInfo *fkey = (ForeignKeyOptInfo *) lfirst(fkc);
                    if (fkey->con_relid == baserel->relid &&
                        fkey->nkeys == 1 &&
                        fkey->conkey[0] == ((Var *) em->em_expr)->varattno)
                    {
                        key_type = KT_FOREIGN;
                        break;
                    }
                }
            }

            ReleaseVariableStats(vardata);

            key = (UesJoinKey *) palloc0(sizeof(UesJoinKey));
            key->baserel  = baserel;
            key->join_key = (Var *) em->em_expr;
            key->max_freq = max_freq;
            key->key_type = key_type;

            ues_state->candidate_keys = lappend(ues_state->candidate_keys, key);
        }

    }
}

static void
ues_print_joins(PlannerInfo *root, UesState *ues_state)
{
    StringInfo      msg = makeStringInfo();
    ListCell*       ejlc;
    UesJoinInfo*    uji;
    Oid             rel1;
    Oid             rel2;

    appendStringInfo(msg, "\n===\nJOINS CURRENTLY KLASSIFIED AS EXPANDING");
    if(ues_state->expanding_joins != NULL && ues_state->expanding_joins != NIL)
    {
        appendStringInfo(msg, " (%d)", ues_state->expanding_joins->length);
    }

    foreach(ejlc, ues_state->expanding_joins){
        uji = lfirst(ejlc);
        rel1 = root->simple_rte_array[uji->rel1->baserel->relid]->relid;
        rel2 = root->simple_rte_array[uji->rel2->baserel->relid]->relid;
        appendStringInfo(msg, "\n\tRel1: \033[1;36m%s\033[0m\n\tRel2: \033[1;36m%s\033[0m\n\tUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
    }
    appendStringInfo(msg, "\nJOINS CURRENTLY KLASSIFIED AS FILTER");
    if(ues_state->filter_joins != NULL && ues_state->filter_joins != NIL)
    {
        appendStringInfo(msg, " (%d)", ues_state->filter_joins->length);
    }

    foreach(ejlc, ues_state->filter_joins){
        uji = lfirst(ejlc);
        rel1 = root->simple_rte_array[uji->rel1->baserel->relid]->relid;
        rel2 = root->simple_rte_array[uji->rel2->baserel->relid]->relid;
        appendStringInfo(msg, "\n\tRel1: \033[1;36m%s\033[0m\n\tRel2: \033[1;36m%s\033[0m\n\tUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
    }
    appendStringInfo(msg, "\n===\n");
    //elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);
}

/**
 * Generates all joins that are
 * possible with our candidate_keys.
 * 
 * The generated joins are storend
 * in ues_state->expanding joins and
 * ues_state->filter_joins.
 * 
 * To do so, we iterate over all
 * candidate_keys if they have a
 * eclass joinclauses with any
 * candidate keys.
 * 
 * This function expects that a 
 * UesState object is stored in 
 * root->join_search_private and
 * ues_state->candidate_keys not
 * to be empty.  
 */
static void
ues_get_all_joins(PlannerInfo *root)
{
    UesState*       ues_state;

    ListCell*       lc_outer;
    ListCell*       lc_inner;
    UesJoinInfo*    join_info;
    UesJoinType     join_type;
    UesJoinKey*     key_outer;
    UesJoinKey*     key_inner;

    ues_state = (UesState*) root->join_search_private;

    /* outer loop for all candidate keys */
    foreach(lc_outer, ues_state->candidate_keys)
    {
        key_outer = (UesJoinKey*) lfirst(lc_outer);

        /**
         * Inner loop for all candidate keys.
         * 
         * We can start at the index of the outer loop
         * because the key pairs that are potentially 
         * skipped are covered in the other direction. 
         * Since the direction of the JoinInfo elements 
         * doesn't matter, this works.
         */
        for_each_from(lc_inner, ues_state->candidate_keys, foreach_current_index(lc_outer)+1)
        {
            key_inner = (UesJoinKey*) lfirst(lc_inner);
                       
            /* skip, if both keys haven't common join */
            if(!have_relevant_eclass_joinclause(root, key_outer->baserel, key_inner->baserel))
            {
                continue;
            }

            join_type = ues_get_jointype(key_outer, key_inner);

            /* put UesJoinInfo together */
            join_info = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
            join_info->join_type = join_type;
            join_info->rel1 = key_outer;
            join_info->rel2 = key_inner;
            join_info->upper_bound = get_upper_bound_old(root, key_outer, key_inner);
            
            /* Adding the join_info to corresponding list */
            if(join_type == UES_JOIN_EXPANDING)
            {
                ues_state->expanding_joins = lappend(ues_state->expanding_joins, join_info);
            }else
            {
                ues_state->filter_joins = lappend(ues_state->filter_joins, join_info);
            }
        } /* end of inner loop*/
    } /* end of outer loop */
    
    /**
     * At last we sort the elements of both 
     * lists based on their upperbounds. So
     * we can assue in all other functions
     * the lists as sorted. 
     */
    list_sort(ues_state->expanding_joins, compare_UesJoinInfo);
    list_sort(ues_state->filter_joins, compare_UesJoinInfo);
}

UpperBound get_upper_bound_old(PlannerInfo* root, UesJoinKey* left_key, UesJoinKey* right_key)
{
    // TODO: muss für Filter nicht berechnet werden.
    Freq            freq_left,
                    freq_right;
    Cardinality     card_left,
                    card_right;
    double  maximal_pair_appearance;
    double  most_common_values_prod;
    double  max_apperance_left;
    double  max_appearance_right;

    freq_left = left_key->max_freq;
    freq_right = right_key->max_freq;

    card_left = left_key->baserel->tuples;
    card_right = right_key->baserel->tuples;

    max_apperance_left = card_left / freq_left;
    max_appearance_right = card_right / freq_right;

    maximal_pair_appearance = Min(max_apperance_left, max_appearance_right);

    most_common_values_prod = freq_left * freq_right;

    Oid rel1 = root->simple_rte_array[left_key->baserel->relid]->relid;
    Oid rel2 = root->simple_rte_array[right_key->baserel->relid]->relid;
    /// //elog(NOTICE, "\ncalc upper_bound for \033[1;36m%s\033[0m and \033[1;36m%s\033[0m\n\
        card_left: %f\ncard_right: %f\nmax_app_left: %f\nmax_app_right: %f\n\
        max_pair: %f\nmost_common: %f\n\n", get_rel_name(rel1), get_rel_name(rel2), card_left, card_right, max_apperance_left, max_appearance_right, maximal_pair_appearance, most_common_values_prod);

    return (UpperBound) maximal_pair_appearance * most_common_values_prod;
}

UpperBound get_upper_bound_new(PlannerInfo* root, UesJoinKey* left_key, UesJoinKey* right_key)
{
    // TODO: muss für Filter nicht berechnet werden.
    UesState*       ues_state;
    Freq            freq_left,
                    freq_right;
    Cardinality     card_left,
                    card_right;

    ues_state = root->join_search_private; 

    double maximal_pair_appearance;
    double most_common_values_prod;
    double max_apperance_left;
    double max_appearance_right;

    freq_left = left_key->max_freq;
    freq_right = right_key->max_freq;

    card_left = ues_state->current_bound;
    card_right = right_key->baserel->tuples;
    // TODO: rows statt tuples benutzen
    // TODO: fix freq

    max_apperance_left = card_left / freq_left;
    max_appearance_right = card_right / freq_right;

    maximal_pair_appearance = Min(max_apperance_left, max_appearance_right);

    most_common_values_prod = freq_left * freq_right;

    Oid rel1 = root->simple_rte_array[left_key->baserel->relid]->relid;
    Oid rel2 = root->simple_rte_array[right_key->baserel->relid]->relid;
    /// //elog(NOTICE, "\ncalc upper_bound for \033[1;36m%s\033[0m and \033[1;36m%s\033[0m\n\
        card_left: %f\ncard_right: %f\nmax_app_left: %f\nmax_app_right: %f\n\
        max_pair: %f\nmost_common: %f\n\n", get_rel_name(rel1), get_rel_name(rel2), card_left, card_right, max_apperance_left, max_appearance_right, maximal_pair_appearance, most_common_values_prod);
    // //elog(NOTICE, "\n\ncard_left: %f\ncard_right: %f\nmax_app_left: %f\nmax_app_right: %f\n\\
    //     max_pair: %f\nmost_common: %f\n\n", 
    //     card_left, card_right, max_apperance_left, max_appearance_right, maximal_pair_appearance, most_common_values_prod);

    return (UpperBound) maximal_pair_appearance * most_common_values_prod;
}

static int
compare_UesJoinInfo(const ListCell *a, const ListCell *b)
{
    UesJoinInfo*    jinfo1 = lfirst(a);
    UesJoinInfo*    jinfo2 = lfirst(b);
    double  upperbound_a = jinfo1->upper_bound;
    double  upperbound_b = jinfo2->upper_bound;

    if(upperbound_a < upperbound_b)
    {
        return -1;
    }else if(upperbound_a > upperbound_b)
    {
        return 1;
    }else
    {
        return 0;
    }
}

/*
 * This function returns the initial relation to be joined to.
 * To do so, we are looking for the UesJoinInfo elements in
 * ues_state->expanding_joins with the lowest upper_bound and
 * select one of the joins relation. We assume that the list 
 * is already sorted.
 * 
 * There are some cases where no expanding_joins are available.
 * In these cases we take a look at the filter_joins list. If
 * filter joins are available we will take the filter withthe 
 * lowest upper_bound. We also assume here, that the list is
 * already sorted.
 * 
 * There should't be any cases where we run into this function
 * without any joins available. Nevertheless we cover this case.
 */
RelOptInfo* ues_get_start_rel(PlannerInfo* root)
{
    UesState*       ues_state;
    UesJoinInfo*    join;
    List*           affected_keys; /* not used in this context */

    /* debug print */
    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_get_start_rel");
    
    ues_state = root->join_search_private;
    affected_keys = NIL;

    /**
     * If there are expanding joins available
     * we take one, if not we are taking a
     * filter join.
     * If nothing we take an error.
     */
    if(ues_state->expanding_joins != NIL &
        ues_state->expanding_joins->length > 0){

        /* debug print */
        //elog(NOTICE, "%d expanding join(s) are available", ues_state->expanding_joins->length);
        
        /* get our join with the lowest upper_bound */
        join = (UesJoinInfo*) linitial(ues_state->expanding_joins);

    }else if(ues_state->filter_joins != NIL &
        ues_state->filter_joins->length > 0)
    {
        /* debug print */
        //elog(NOTICE, "There are no expanding joins available, but %d filter join(s)", ues_state->filter_joins->length);
        
        /* get our join with the lowest upper_bound */
        join = (UesJoinInfo*) linitial(ues_state->filter_joins);
        
    }else{
        //elog(ERROR, "There are no expanding joins and no filter joins available. This query is not determining");
    }
    
    /**
     * Update Rules:
     * We have to set the upper_bound of
     * our relation to the current_bound,
     * because we are kind of joining
     * into our current_intermediate.
     * 
     * We also have to move the key into
     * the joined_keys list when chosing 
     * a candidat_key.
     */
    ues_state->current_bound = join->rel1->baserel->tuples;
    ues_switch_key_in_list(root, join->rel1, &affected_keys);
    
    /* debug print */
    //elog(NOTICE, "\033[1;32m[finished]\033[0m ues_get_start_rel");
    
    return join->rel1->baserel;    

}

RelOptInfo* ues_get_start_rel_alt(PlannerInfo* root)
{
    UesState*       ues_state;
    ListCell*       lc;
    UesJoinKey*     rel;
    UesJoinKey*     min_rel;
    UpperBound      min_bound;
    List*           affected_keys; /* not used in this context */


    /* debug print */
    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_get_start_rel");
    
    ues_state = root->join_search_private;
    min_bound = DBL_MAX;
    affected_keys = NIL;

    foreach(lc, ues_state->candidate_keys)
    {
        rel = (UesJoinKey*) lfirst(lc);

        if(rel->baserel->tuples <= min_bound)
        {
            min_rel = rel;
            min_bound = rel->baserel->tuples;
        }


    }

    Oid oid = root->simple_rte_array[min_rel->baserel->relid]->relid;
    char* name_rel = get_rel_name(oid);
    char* name_att = get_attname(oid, min_rel->join_key->varattno, false);
    //elog(NOTICE, "\tfound first row %s from rel \033[1;36m%s\033[0m", name_att, name_rel);

    /**
     * Update Rules:
     * We have to set the upper_bound of
     * our relation to the current_bound,
     * because we are kind of joining
     * into our current_intermediate.
     * 
     * We also have to move the key into
     * the joined_keys list when chosing 
     * a candidat_key.
     */
    ues_state->current_bound = min_bound;
    ues_switch_key_in_list(root, min_rel, &affected_keys);
    
    /* debug print */
    //elog(NOTICE, "\033[1;32m[finished]\033[0m ues_get_start_rel");
    
    return min_rel->baserel;    

}

/*
* returns the next join to do
*
* checks for: exactly one join key is already contained in curr_intermediate

@ToDo: needs überarbeitung
*/
RelOptInfo* ues_next_join(PlannerInfo* root, UesJoinInfo** ujinfo)
{
    UesState*       ues_state;
    UesJoinInfo*    join;
    ListCell*       lc;
    RelOptInfo*     elem1;
    RelOptInfo*     elem2;
    RelOptInfo*     elem_curr;

    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_next_join");

    ues_state = root->join_search_private;
    elem_curr = ues_state->current_intermediate;

    if(ues_state->expanding_joins == NULL)
    {
        //elog(NOTICE, "expanding joins is NULL");
        return NULL;
    }

    foreach(lc, ues_state->expanding_joins)
    {
        join = lfirst(lc);
        elem1 = join->rel1->baserel;
        elem2 = join->rel2->baserel;

        /* check if elem1 is in elem_curr */
        if(bms_is_subset(elem1->relids, elem_curr->relids))
        {   
            /* continue if both are already part of intermediate */
            // if(bms_overlap(elem_curr->relids, elem2->relids))
            // {
            //     list_delete_cell(ues_state->expanding_joins, join);
            //     continue;
            // }
            /* choose rel2 as next join */
            if(have_relevant_eclass_joinclause(root, elem_curr, elem2))
            {
                *ujinfo = join;
                return elem2;
            }
        }
        /* do the same but mirrored */
        /* check if elem2 is in elem_curr */
        if(bms_is_subset(elem2->relids, elem_curr->relids))
        {   
            /* continue if both are already part of intermediate */
            // if(bms_overlap(elem_curr->relids, elem1->relids))
            // {
            //     list_delete_cell(ues_state->expanding_joins, join);
            //     continue;
            // }
            /* choose rel1 as next join */
            if(have_relevant_eclass_joinclause(root, elem_curr, elem1))
            {   
                *ujinfo = join;
                return elem1;
            }
        }
        /* 
        * we get here, if both rels of the expanding join object 
        * are not part of current intermediate. That means, that there
        * is no way to join this element, so we continue with the next
        * expanding join object.
        */
    }
    /*
    * we get here, when we couldnt find any fitting expanding join. We can
    * assume that there are expanding joins left, as a consequence of the
    * call hierarchy from which this function is called. We just return NULL 
    * here and handle that error higher in the call hierarchy.
    */
    return NULL;
}

void
ues_get_affected_keys(PlannerInfo* root, List** affected_keys)
{

}

void
ues_switch_key_in_list(PlannerInfo* root, UesJoinKey* jkey, List** affected_keys)
{
    UesState*   ues_state;
    UesJoinKey* key;
    UesJoinKey* dummy;
    UesJoinKey* affected;
    UesJoinKey* key_to_change;
    ListCell*   lc;
    ListCell*   cell;
    ListCell*   lc_ck;
    ListCell*   lc_cak;
    Oid         rel;
    char*       name_rel;
    char*       name_att;

    ues_state = root->join_search_private;
    cell = NULL;
    key = jkey;
    *affected_keys = NIL;

    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_switch_key_in_list");

    foreach(lc_ck, ues_state->candidate_keys)
    {
        affected = (UesJoinKey*) lfirst(lc_ck);

        if(key->baserel == affected->baserel)
        {
            Oid relA = root->simple_rte_array[affected->baserel->relid]->relid;
            char* name_relA = get_rel_name(relA);
            char* name_attA = get_attname(relA, affected->join_key->varattno, false);
            //elog(NOTICE, "affected: %s from rel \033[1;36m%s\033[0m", name_attA, name_relA);

            *affected_keys = lappend(*affected_keys, affected);
        }
    }

    // if(list_member(ues_state->candidate_keys, key))
    // {
    foreach(lc_cak, *affected_keys)
    {
        key_to_change = (UesJoinKey*) lfirst(lc_cak);

        foreach(lc, ues_state->candidate_keys)
        {   
            dummy = (UesJoinKey*) lfirst(lc);
            if(dummy == key_to_change)
            {
                cell = lc;
                break;
            }
        }

        if(cell == NULL)
        {
            continue;
        }

        ues_state->candidate_keys = list_delete_cell(ues_state->candidate_keys, cell);
        ues_state->joined_keys = lappend(ues_state->joined_keys, key_to_change);
        
        rel = root->simple_rte_array[key_to_change->baserel->relid]->relid;
        name_rel = get_rel_name(rel);
        name_att = get_attname(rel, key_to_change->join_key->varattno, false);
        //elog(NOTICE, "\tswitched %s from rel \033[1;36m%s\033[0m", name_att, name_rel);
    }   
    // }

    //elog(NOTICE, "\033[1;32m[finished]\033[0m ues_switch_key_in_list");

    ues_print_state(root, ues_state);
}

/*
 * Makes an relation for ues. Assumes that an UesState
 * is stored in root->join_search_private. At the end
 * this function calls the default make_join_rel from
 * postgres. But before and after so, we have to work 
 * off the following ToDo:
 *
 * a) push used candidate_keys into joined_keys
 * b) update key types (Primary->Foregin)
 * c) update frequencies
 * d) perform the join
 * e) rebuild expanding_joins and filter_joins list
 */
RelOptInfo*
ues_make_join_rel(PlannerInfo* root, RelOptInfo* rel1, RelOptInfo* rel2, UesJoinInfo* jinfo)
{
    RelOptInfo*     join;
    UesJoinInfo*    info;
    UesState*       ues_state;
    ListCell*       cell;
    ListCell*       lc;
    UesJoinInfo*    dummy;
    List*           affected_joinkeys;

    ues_state = root->join_search_private;
    info = jinfo;
    affected_joinkeys = NIL;

    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_make_join_rel");
    /*
     * a) At first we have to move the used keys
     * from the candidate_keys list into the
     * joined_keys list.
     */
    //ues_switch_key_in_list(root, rel2, &affected_joinkeys);
    ues_switch_key_in_list(root, jinfo->rel1, &affected_joinkeys);
    ues_switch_key_in_list(root, jinfo->rel2, &affected_joinkeys);

    /*
     * b) update the key types. When joining a
     * primary key on a foregin key the joined
     * tuple set has no longer a primary key. 
     * Values from the former primary key can
     * appear multiple times. This affects our
     * filter rules when joining two relations
     * using UES. Since the key is not primary
     * keying anymore, joins with this key are
     * no longer filter joins.
     */
    if(jinfo->rel1->key_type == KT_PRIMARY &&
        jinfo->rel2->key_type != KT_PRIMARY)
    {
        jinfo->rel1->key_type = KT_FOREIGN;
    }
    
    if(jinfo->rel2->key_type == KT_PRIMARY &&
        jinfo->rel1->key_type != KT_PRIMARY)
    {
        jinfo->rel2->key_type = KT_FOREIGN;
    }

    /*
     * c) update frequencies. Since both max_freq
     * values are standing for the value which is
     * the most common, the new maximum frequency 
     * is the product of both max_freq values.
     * 
     * When performing a filter join we dont need
     * to calculate anything as the max_freq value
     * of the primary join will be one. We can just
     * take the Max() of both max_freq values. 
     */
    if(jinfo->rel1->key_type == KT_PRIMARY ||
        jinfo->rel2->key_type == KT_PRIMARY)
    {
        jinfo->rel1->max_freq = Max(jinfo->rel1->max_freq, jinfo->rel2->max_freq);
        jinfo->rel2->max_freq = jinfo->rel1->max_freq;
    }else
    {
        jinfo->rel1->max_freq = jinfo->rel1->max_freq * jinfo->rel2->max_freq;
        jinfo->rel2->max_freq = jinfo->rel1->max_freq;
    }
    
    /*
     * After performing the steps above
     * we can perform the join operation 
     * using the postgres join method.
     * 
     * Afterwards we need to delete
     * slow and inefficent paths. To do
     * so we call just set_cheapest.
     */
    join = make_join_rel(root, rel1, rel2);
    set_cheapest(join);

    /*
     * e) update the key lists in ues_state.
     * It seems to be the most efficient to 
     * just rebuild the expanding_joins and 
     * filter_joins lists. Otherwise we would
     * need to iterate over all list entries
     * and check if they are effected by a
     * key type change. 
     * 
     * From a logic view it would make more
     * sense to do this step after
     * performing the acutual join, but in
     * reality it doesnt matter, because
     * the make_join_rel from postgres does
     * not use any of our datastrures. So
     * we keep the things together: we
     * change everything that needs to be
     * changed before performing the join.
     */
    ues_state->current_intermediate = join; // this is not fine, it just covers a quick bug
    ues_get_possible_joins(root);
    

    //elog(NOTICE, "join: %f", jinfo->upper_bound);
    //elog(NOTICE, "rel1: %f", rel1->tuples);
    //elog(NOTICE, "rel2: %f", rel2->tuples);



    /*
     * Print the current intermediate,
     * candidate_keys and all detected
     * joins to track the algorithms'
     * work.
     */
    //elog(NOTICE, "\033[1;32m[finished]\033[0m ues_make_join_rel. Current UesState and detected joins following: (intermediate wrong)");
    ues_print_state(root, ues_state);
    ues_print_joins(root, ues_state);

    return join;
}

/*
* iterate over all filter joins and check if they can
* be joined on rel. Iterates until all possible filters
* are joinded.
*
* Assumes that initialized UesState is stored in root->
* join_search_private.
*/
RelOptInfo*
ues_join_filters(PlannerInfo* root, RelOptInfo* jrel)
{
    UesState*       ues_state;
    RelOptInfo*     rel;
    bool            interrupted;
    ListCell*       lcfj;
    UesJoinInfo*    filter;
    RelOptInfo*     filter_rel1;
    RelOptInfo*     filter_rel2;
    Oid             rel_oid;
    char*           relname;

    ues_state = root->join_search_private;
    rel = jrel;
    interrupted = true;

    if(jrel->rtekind == RTE_RELATION)
    {
        rel_oid = root->simple_rte_array[rel->relid]->relid;
        relname = get_rel_name(rel_oid);
    }else{
        relname = "current_intermediate";
    }
    //elog(NOTICE, "\033[1;32m[called]\033[0m ues_join_filters for rel \033[1;36m%s\033[0m. Deteced joins followed:", relname);
    ues_print_joins(root, ues_state);

    /*
    * So long as filter joins still exist and we
    * joined one relation in last iteration, we
    * do another run-through. 
    * 
    * At the time when no filters left or we did
    * a run-through without any new joins we are
    * finished here.
    */
    
    int i = 0;
    while(ues_state->filter_joins != NULL &&
            ues_state->filter_joins != NIL && 
            interrupted)
    {
        //elog(NOTICE, "while iteration over filters: %d", i++);
        interrupted = false;
        foreach(lcfj, ues_state->filter_joins)
        {
            filter = (UesJoinInfo*) lfirst(lcfj);
            filter_rel1 = filter->rel1->baserel;
            filter_rel2 = filter->rel2->baserel;
            
            /*
            * check if the current filter has a relation
            * joinable on rel. If not, we can skip this for now.
            */
            if(!have_relevant_eclass_joinclause(root, rel, filter_rel1) &&
                !have_relevant_eclass_joinclause(root, rel, filter_rel2))
            {
                //elog(NOTICE, "no eclass join possible with this filter");
                continue;
            }

            /* 
            * At this point we check if we can join a filter relation.
            * For that purpose we dirst check if filter_rel1 is already
            * part of current intermediate. If it is, we gonna check if
            * there is a joinclause with the other filter relation. If
            * so, we do a join.
            * Afterwards we check the same, for the other relation.
            */
            if(bms_is_subset(filter_rel1->relids, rel->relids))
            {   
                if(have_relevant_eclass_joinclause(root, rel, filter_rel2))
                {
                    rel= ues_make_join_rel(root, rel, filter_rel2, filter);
                    interrupted = true;
                    break;
                }
            }
            if(bms_is_subset(filter_rel2->relids, rel->relids))
            {   
                if(have_relevant_eclass_joinclause(root, rel, filter_rel1))
                {
                    rel = ues_make_join_rel(root, rel, filter_rel1, filter);
                    interrupted = true;
                    break;
                }
            }

        }
    }
    
    //elog(NOTICE, "Remaining joins:");
    ues_print_joins(root, ues_state);
    //elog(NOTICE, "\033[1;32m[finished]\033[0m ues_join_filters");
    return rel;
}

UesJoinType
ues_get_jointype(UesJoinKey* key1, UesJoinKey* key2)
{
    UesJoinType     join_type;

    if(key1->key_type == KT_PRIMARY)
    {
        if(key2->key_type == KT_PRIMARY || key2->key_type == KT_FOREIGN)
        {
            join_type = UES_JOIN_FILTER;
        }
    }else if(key2->key_type == KT_PRIMARY)
    {
        if(key1->key_type == KT_PRIMARY || key1->key_type == KT_FOREIGN)
        {
            join_type = UES_JOIN_FILTER;
        }
    }else
    {
        join_type = UES_JOIN_EXPANDING;
    }

    return join_type;
}

bool
have_vars_join_relation(PlannerInfo* root, Var* var1, Var* var2)
{
    ListCell*           lc;
    ListCell*           lc_mem;
    EquivalenceClass*   ec;
    EquivalenceMember*  em;
    Var*                var;
    bool                var1_found;
    bool                var2_found;
    
    foreach(lc, root->eq_classes)
    {
        ec = (EquivalenceClass*) lfirst(lc);
        var1_found = false;
        var2_found = false;

        foreach(lc_mem, ec->ec_members)
        {
            em = (EquivalenceMember*) lfirst(lc_mem);

            if(IsA(em->em_expr, Var))
            {
                var = (Var*) em->em_expr;

                if (var->varno == var1->varno && var->varattno == var1->varattno)
                {
                    var1_found = true;
                }
                
                if (var->varno == var2->varno && var->varattno == var2->varattno)
                {
                    var2_found = true;
                }

                if (var1_found && var2_found)
                {
                    return true;
                }
            }

        }

    }
    return false;
}

/**
 * Generates all joins that are
 * possible to join to
 * current_intermediate.
 * 
 * To do so, we iterate over all
 * candidate_keys and joined_keys
 * and check if they have a eclass 
 * joinclause with our 
 * current_intermediate. If they 
 * have, we iterate over.
 * 
 * When found to JoinKeys that 
 * are in same eclass we also
 * have to check of both Var's
 * have a join clause. This is
 * necessary as a consequence
 * of multiple columns of one
 * relation.
 * 
 * This function expects that a 
 * UesState object is stored in 
 * root->join_search_private. 
 * The current_intermediate in 
 * the UesState object must not 
 * be NULL. 
 */
void
ues_get_possible_joins(PlannerInfo* root)
{
    UesState*       ues_state;
    ListCell*       lc_join;
    ListCell*       lc_parent;
    UesJoinKey*     join_key;
    UesJoinKey*     parent_key;
    UesJoinInfo*    join_info;
    UesJoinType     join_type;

    //elog(NOTICE, "\033[1;32m[updating]\033[0m joinrels");

    ues_state = (UesState*) root->join_search_private;

    list_free_deep(ues_state->expanding_joins);
    list_free_deep(ues_state->filter_joins);
    ues_state->expanding_joins = NIL;
    ues_state->filter_joins = NIL;

    /**
     * Interrupt the program if the
     * current_intermediate is NULL.
     * Without we would run into a 
     * lot of SegmentationFaults
     * and unpredictable behavior.
     */
    if(ues_state->current_intermediate == NULL)
    {
        //elog(ERROR, "ues_state->current_intermediate must not be NULL");
    }

    /**
     * This loop looks super complicated but
     * it is only so because of these very
     * descriptive comments.
     * 
     * Notice that we have this loop two
     * times. This is because we have to 
     * iterate over all candidate_keys
     * and joined_keys. Both loops are
     * working the same. The only 
     * difference is the keys list they 
     * are iterating over. 
     */
    foreach(lc_parent, ues_state->candidate_keys)
    {
        parent_key = (UesJoinKey*) lfirst(lc_parent);

        /**
         * Check if the key is part of our
         * current_intermediate. If so, we
         * can check for keys that can be
         * joined. But if this key is not
         * already part of 
         * current_intermediate we canjust
         * continue.
         */
        if(!bms_is_subset(parent_key->baserel->relids, ues_state->current_intermediate->relids))
        {
            continue;
        }

        /**
         * Our parent_key is part of our
         * current_intermediate. Now we can
         * check the candidate_keys if they
         * are joinable to our parent_key.
         * 
         * Notice that we generate multiple
         * UesJoinInfo elements if the 
         * parent_key hasmore than just one 
         * joinable parent_key. This is no
         * problem for our join order because
         * every key get joined only one time
         * anyways (if the key is not several
         * times in candidate_keys). After
         * every join we regenerate all the
         * possbile joins. Which extinguish
         * the other join options.
         */
        foreach(lc_join, ues_state->candidate_keys)
        {
            join_key = (UesJoinKey*) lfirst(lc_join);
            
            /**
             * Check if the join_key is joinable
             * to our current_intermediate by
             * checking if it has a eclass
             * joinclause with parent_key.
             */
            if(!have_relevant_eclass_joinclause(root, parent_key->baserel, join_key->baserel))
            {
                continue;
            }

            Oid rel1 = root->simple_rte_array[parent_key->baserel->relid]->relid;
            Oid rel2 = root->simple_rte_array[join_key->baserel->relid]->relid;
            char* rel1_name = get_rel_name(rel1);
            char* rel2_name = get_rel_name(rel2);
            char* rel1_var = get_attname(rel1, parent_key->join_key->varattno, false);
            char* rel2_var = get_attname(rel2, join_key->join_key->varattno, false);
            //elog(NOTICE, "check joinbarkeit von: \033[1;33m%s\033[0m.%s und \033[1;33m%s\033[0m.%s",\
                rel1_name, rel1_var, rel2_name, rel2_var);
            if(!have_vars_join_relation(root, parent_key->join_key, join_key->join_key))
            {
                //elog(NOTICE, "\033[1;31mnicht joinbar\033[1;0m");
                continue;
            }

            join_type = ues_get_jointype(parent_key, join_key);
            
            /**
             * Here we put together our join_info element. 
             * Notice that we are using the parent_key for 
             * determining the upperbound, but we use the
             * current_intermediates tuple size inside
             * the upper_bound function.
             */
            join_info = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
            join_info->join_type = join_type;
            join_info->rel1 = join_key;
            join_info->rel2 = parent_key;
            join_info->upper_bound = get_upper_bound_new(root, parent_key, join_key);
            
            /**
             * Depending on their join type
             * our UesJoinInfo elements get
             * inserted into a specialized
             * list. 
             */
            if(join_type == UES_JOIN_EXPANDING)
            {
                ues_state->expanding_joins = lappend(ues_state->expanding_joins, join_info);
            }else
            {
                ues_state->filter_joins = lappend(ues_state->filter_joins, join_info);
            }
        } /* end of join_key loop*/
    } /* end of parent_key loop */

    foreach(lc_parent, ues_state->joined_keys)
    {
        parent_key = (UesJoinKey*) lfirst(lc_parent);

        /**
         * Check if the key is part of our
         * current_intermediate. If so, we
         * can check for keys that can be
         * joined. But if this key is not
         * already part of 
         * current_intermediate we canjust
         * continue.
         */
        if(!bms_is_subset(parent_key->baserel->relids, ues_state->current_intermediate->relids))
        {
            continue;
        }

        /**
         * Our parent_key is part of our
         * current_intermediate. Now we can
         * check the candidate_keys if they
         * are joinable to our parent_key.
         * 
         * Notice that we generate multiple
         * UesJoinInfo elements if the 
         * parent_key hasmore than just one 
         * joinable parent_key. This is no
         * problem for our join order because
         * every key get joined only one time
         * anyways (if the key is not several
         * times in candidate_keys). After
         * every join we regenerate all the
         * possbile joins. Which extinguish
         * the other join options.
         */
        foreach(lc_join, ues_state->candidate_keys)
        {
            join_key = (UesJoinKey*) lfirst(lc_join);
            
            /**
             * Check if the join_key is joinable
             * to our current_intermediate by
             * checking if it has a eclass
             * joinclause with parent_key.
             */
            if(!have_relevant_eclass_joinclause(root, parent_key->baserel, join_key->baserel))
            {
                continue;
            }

            Oid rel1 = root->simple_rte_array[parent_key->baserel->relid]->relid;
            Oid rel2 = root->simple_rte_array[join_key->baserel->relid]->relid;
            char* rel1_name = get_rel_name(rel1);
            char* rel2_name = get_rel_name(rel2);
            char* rel1_var = get_attname(rel1, parent_key->join_key->varattno, false);
            char* rel2_var = get_attname(rel2, join_key->join_key->varattno, false);
            //elog(NOTICE, "check joinbarkeit von: \033[1;33m%s\033[0m.%s und \033[1;33m%s\033[0m.%s",\
                rel1_name, rel1_var, rel2_name, rel2_var);
            if(!have_vars_join_relation(root, parent_key->join_key, join_key->join_key))
            {
                //elog(NOTICE, "\033[1;31mnicht joinbar\033[1;0m");
                continue;
            }

            join_type = ues_get_jointype(parent_key, join_key);
            
            /**
             * Here we put together our join_info element. 
             * Notice that we are using the parent_key for 
             * determining the upperbound, but we use the
             * current_intermediates tuple size inside
             * the upper_bound function.
             */
            join_info = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
            join_info->join_type = join_type;
            join_info->rel1 = join_key;
            join_info->rel2 = parent_key;
            join_info->upper_bound = get_upper_bound_new(root, parent_key, join_key);
            
            /**
             * Depending on their join type
             * our UesJoinInfo elements get
             * inserted into a specialized
             * list. 
             */
            if(join_type == UES_JOIN_EXPANDING)
            {
                ues_state->expanding_joins = lappend(ues_state->expanding_joins, join_info);
            }else
            {
                ues_state->filter_joins = lappend(ues_state->filter_joins, join_info);
            }
        } /* end of join_key loop*/
    } /* end of parent_key loop */
    
    /**
     * At last we sort the elements of both 
     * lists based on their upperbounds. So
     * we can assue in all other functions
     * the lists as sorted. 
     */
    list_sort(ues_state->expanding_joins, compare_UesJoinInfo);
    list_sort(ues_state->filter_joins, compare_UesJoinInfo);
}

/*
 * default method of ues. Decides if to use postgres standard stuff
 * e.g. standard_join_search or geqo or to use our ues implementation.
 * This function is integrated through the join_search_hook. The real
 * implementation of ues is in ues_join_rels.
 */
RelOptInfo*
ues_join_search(PlannerInfo *root, int levels_needed, List *initial_rels)
{
    StringInfo      msg;
    bool            triggers_ues = ues_enabled && ues_supported_query(root);

    /*
     * debug print
     */
    msg = makeStringInfo();
    appendStringInfo(msg, "\n=========================\n");
    appendStringInfo(msg, "   UES: %s   \n", triggers_ues ? "enabled" : "disabled");
    appendStringInfo(msg, "=========================\n");
    //elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);

    if (!triggers_ues)
    {
        if (prev_join_search_hook)
            return prev_join_search_hook(root, levels_needed, initial_rels);
        else if (enable_geqo && levels_needed >= geqo_threshold)
            return geqo(root, levels_needed, initial_rels);
        else
            return standard_join_search(root, levels_needed, initial_rels);
    }

    /* use UES */
    return ues_join_rels(root, levels_needed, initial_rels);

}

RelOptInfo* 
ues_join_rels(PlannerInfo* root, int levels_neded, List* initial_rels)
{
    UesState*       ues_state;
    RelOptInfo*     joinrel;
    RelOptInfo*     next_join;
    UesJoinInfo*    filter;
    UesJoinInfo*    expanding;
    RelOptInfo*     filter_rel1;
    RelOptInfo*     filter_rel2;
    ListCell*       lcfj;
    int             loop_count;
    StringInfo      msg;

    /**
     * Before starting with the core
     * UES stuff we have to set up
     * our basic datastructures by
     * initialise a ues_state and 
     * read all keys from the query.
     */
    ues_state = ues_join_search_init(root);
    ues_init_baserels(root, &initial_rels);
    ues_print_state(root, ues_state);

    /* debug stuff */
    loop_count = 0;

    #ifdef DEBUG
        elog(NOTICE, "PENIS");
    #endif

    /**
     * Normally we have a big while loop
     * for joining everything together.
     * And we definitely have one but
     * when we are beginning with our
     * UES implementation there are some
     * things that have to be done only
     * one time. So instead of encapsulate
     * these things inside the loop we
     * are just doing them before:
     * 
     * 1. To find a relation to start
     * with, we have to generate all
     * possible joins across our 
     * candidate_keys and have to decide
     * if they are expanding or filter
     * joins. We prefer a expanding join
     * over a filter join but for
     * understanding how we decide for
     * the initial relation check the
     * comment about ues_get_start_rel.
     * 
     * 2. After we decided for a initial
     * relation we regenreate all possible
     * joins that can be joined to our
     * initial relation. Because of the
     * enumeration rules of UES we have
     * to join all filters before starting
     * with our first expanding join.
     *   Notice: In generall we want to
     * do as many filter joins as
     * possible before open our
     * current_intermediate for the next
     * next expanding join. 
     */

     /* 1. */
    //ues_get_all_joins(root);
    //ues_state->current_intermediate = ues_get_start_rel(root);
    ues_state->current_intermediate = ues_get_start_rel_alt(root);
    //ues_print_joins(root, ues_state);

    /* debug print */
    Oid start_rel = root->simple_rte_array[ues_state->current_intermediate->relid]->relid;
    //elog(NOTICE, "initial relation set: \033[1;31m%s\033[0m", get_rel_name(start_rel));

    /* 2. */
    ues_get_possible_joins(root);
    ues_state->current_intermediate = ues_join_filters(root, ues_state->current_intermediate);
    ues_print_state(root, ues_state);

    /* debug print */
    msg = makeStringInfo();
    appendStringInfo(msg, "\n=========================\n");
    appendStringInfo(msg, "   preperation finished   \n");
    appendStringInfo(msg, "==========================\n");
    //elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);

    /**
     * Here is our big while loop. It loop as long as
     * there are candidate keys in the corresponding
     * list. The procedure is as follows:
     * 
     * 1. We determine all possible joins that are 
     * joinable to out current_intermediate. We have
     * to check if any joins are available at all. If
     * not this is our sign to break the loop.
     *   Notice: We only talk about expanding joins
     * at this point, because we can assume that we
     * joined all possible filters at the end of the
     * last loop iteration. 
     * 
     * 2. The next step is to determine the next
     * expanding join and join him to our
     * current_intermediate.
     *   Notice: We don't have to check for a NULL
     * callback because we checked for available
     * joins before.
     * 
     * 3. At last we check for any available filters
     * and perfon them if possible. With joining the
     * filters after the expanding join we get a clear
     * left-aligned join tree.
     */
    while((ues_state->candidate_keys != NULL && 
            ues_state->candidate_keys != NIL) && 
            !ues_state->candidate_keys->length <= 0)
    {
        
        /* debug print*/
        msg = makeStringInfo();
        appendStringInfo(msg, "\n--------------------------\n");
        appendStringInfo(msg, " main loop, iteration: %d  \n", loop_count++);
        appendStringInfo(msg, "--------------------------\n");
        //elog(NOTICE, "%s", msg->data);
        destroyStringInfo(msg);
        
        /* 1. */
        ues_get_possible_joins(root);
        
        /**
         * If our relations build two distinct trees
         * the query is not feasible. When we are
         * running into such a situation we notice
         * this by having candidate keys over but
         * no possible joins. As a result of joining
         * all filters at the end of the loop we only
         * have to check for expanding joins. If none
         * are available we have such a situation and 
         * have to thow a error.
         */
        if(ues_state->expanding_joins == NULL)
        {
            //elog(ERROR, "There are no joins left but still candidate_keys. \\
                This means the join operation can not be performed");
        }

        /* 2. */
        next_join = ues_next_join(root, &expanding);
        ues_state->current_intermediate = ues_make_join_rel(root, ues_state->current_intermediate, next_join, expanding);

        /* debug print */
        Oid next_join_oid = root->simple_rte_array[next_join->relid]->relid;
        //elog(NOTICE, "expanding join performed: \033[1;31m%s\033[0m", get_rel_name(next_join_oid));

        /**
         * 3.
         * 
         * Before joinging the filters we check whether
         * any are available. If not we can continue
         * with the main loop.
         */
        if(ues_state->filter_joins == NULL)
        {
            //elog(NOTICE, "no filters left. Continue with next while loop iteration.");
            continue;
        }

        //elog(NOTICE, "AFTER CONTINUE");
        
        /**
         * If filters are available in general we
         * join them now.
         */        
        ues_state->current_intermediate = ues_join_filters(root, ues_state->current_intermediate);
        
        //elog(NOTICE, "AFTER FILTER JOIN");

        /* debug prints */
        //elog(NOTICE, "All possible filters joined. Continue with next while loop iteration.");
        
    }
    msg = makeStringInfo();
    appendStringInfo(msg, "\n==========================\n");
    appendStringInfo(msg, "    main loop finished    \n");
    appendStringInfo(msg, "==========================\n");
    //elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);

    /**
     * We do another check up here. Just to be
     * sure that everything went fine. 
     */
    if(ues_state->candidate_keys != NIL)
    {
        //elog(ERROR, "\033[1;31mThere are still candidate keys left. Something went wrong.\033[0m");
    }
    if(ues_state->expanding_joins != NIL)
    {
        //elog(ERROR, "\033[1;31mThere are still expanding joins left. Something went wrong.\033[0m");
    }
    if(ues_state->filter_joins != NIL)
    {
        //elog(ERROR, "\033[1;31mThere are still filter joins left. Something went wrong.\033[0m");
    }

    /**
     * return current_intermediate from ues_state and 
     * prepare everything for return into postgres code.
     */
    joinrel = ues_state->current_intermediate;
    set_cheapest(joinrel);

    /**
     * Clean up ues data in memory to avoid
     * memory overflow.
     */
    ues_join_search_cleanup(root);


    //elog(INFO, "ues finished. return into postgres code");
    return joinrel;
}

void _PG_init(void)
{
    prev_join_search_hook = join_search_hook;
    join_search_hook = ues_join_search;

    DefineCustomBoolVariable("ues.enable_ues", "Enable the UES query optimizer", NULL,
                             &ues_enabled, false,
                             PGC_USERSET, 0, NULL, NULL, NULL);

    //elog(INFO, "UES module loaded");
}

void _PG_fini(void)
{
    join_search_hook = prev_join_search_hook;
}
