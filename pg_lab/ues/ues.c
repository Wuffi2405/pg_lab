
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
    
    elog(INFO, "UES state: %s", msg->data);
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
        appendStringInfo(msg, "\n\tRel1: %s\n\tRel2: %s\n\tUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
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
        appendStringInfo(msg, "\n\tRel1: %s\n\tRel2: %s\n\tUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
    }
    appendStringInfo(msg, "\n===\n");
    elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);
}

/*
 * Separates all relations to be joined into expanding joins and filter joins.
 * 
 * Assumes that UesState->candidate_keys has been initialized and that UesState has been attached to PlanerInfo.
 */
static void
ues_init_joinrels(PlannerInfo *root)
{
    UesState    *ues_state = (UesState*) root->join_search_private;

    ListCell    *key1,  /* list cell for outer loop */
                *key2;  /* list cell for inner loop */

    UesJoinInfo *uinfo; /* join element to be added to lists */
    UesJoinType  type;  /* determined join type */

    foreach(key1, ues_state->candidate_keys)
    {
        UesJoinKey* elem_outer = (UesJoinKey*) lfirst(key1);
        
        // elog(NOTICE, "----------------");
        Oid         rel1 = root->simple_rte_array[elem_outer->baserel->relid]->relid;
        // char*       str1 = get_attname(rel1, elem_outer->join_key->varattno, false);
        // elog(NOTICE, "Key1: %d, %s", foreach_current_index(key1), str1);

        for_each_from(key2, ues_state->candidate_keys, foreach_current_index(key1)+1)
        {
            UesJoinKey* elem_inner = (UesJoinKey*) lfirst(key2);
            
            Oid         rel2 = root->simple_rte_array[elem_inner->baserel->relid]->relid;
            // char*       str2 = get_attname(rel2, elem_inner->join_key->varattno, false);
            // elog(NOTICE, "Key2: %d, %s", foreach_current_index(key2), str2);
            
            /* skip, if both keys haven't common join */
            if(!have_relevant_eclass_joinclause(root, elem_outer->baserel, elem_inner->baserel))
            {
                continue;
            }

            /* check if our join is certainly non expanding aka a filter */
            if(elem_outer->key_type == KT_PRIMARY)
            {
                if(elem_inner->key_type == KT_PRIMARY || elem_inner->key_type == KT_FOREIGN)
                {
                    type = UES_JOIN_FILTER;
                }
            }else if(elem_inner->key_type == KT_PRIMARY)
            {
                if(elem_outer->key_type == KT_PRIMARY || elem_outer->key_type == KT_FOREIGN)
                {
                    type = UES_JOIN_FILTER;
                }
            }else
            {
                type = UES_JOIN_EXPANDING;
            }
 if (elem_outer == NULL) {
                elog(ERROR, "------------------------fdfd543");
            }           
            /* put UesJoinInfo together */
            uinfo = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
            uinfo->join_type = type;
            uinfo->rel1 = elem_outer;
            uinfo->rel2 = elem_inner;
            uinfo->upper_bound = get_upper_bound(root, elem_outer, elem_inner);
            
            /* add UesJoinInfo to correct list */
            if(type == UES_JOIN_EXPANDING)
            {
                ues_state->expanding_joins = lappend(ues_state->expanding_joins, uinfo);
            }else
            {
                ues_state->filter_joins = lappend(ues_state->filter_joins, uinfo);
            }

            if (elem_outer == NULL) {
                elog(ERROR, "------------------------fdfd543");
            }
            if (uinfo->rel1 == NULL) {
                elog(ERROR, "------------------------fdfd543");
            }

        }
    }
}

void
ues_update_joinrels(PlannerInfo* root)
{
    UesState*       ues_state;
    ListCell*       lco;
    ListCell*       lci;
    UesJoinKey*     jk_outer;
    UesJoinKey*     jk_inner;
    UesJoinInfo*    uinfo;
    UesJoinType     type;

    ues_state = root->join_search_private;

    elog(NOTICE, "[called] ues_update_joinrels");

    list_free_deep(ues_state->expanding_joins);
    list_free_deep(ues_state->filter_joins);
    ues_state->expanding_joins = NIL;
    ues_state->filter_joins = NIL;


    ues_init_joinrels(root);

    foreach(lco, ues_state->candidate_keys)
    {
        jk_outer = lfirst(lco);

        foreach(lci, ues_state->joined_keys)
        {
            jk_inner = lfirst(lci);

            if(!have_relevant_eclass_joinclause(root, jk_outer->baserel, jk_inner->baserel))
            {
                continue;
            }

            if(jk_outer->key_type == KT_PRIMARY)
            {
                if(jk_inner->key_type == KT_PRIMARY || jk_inner->key_type == KT_FOREIGN)
                {
                    type = UES_JOIN_FILTER;
                }
            }else if(jk_inner->key_type == KT_PRIMARY)
            {
                if(jk_outer->key_type == KT_PRIMARY || jk_outer->key_type == KT_FOREIGN)
                {
                    type = UES_JOIN_FILTER;
                }
            }else{
                type = UES_JOIN_EXPANDING;
            }

            uinfo = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
            uinfo->join_type = type;
            uinfo->rel1 = jk_outer;
            uinfo->rel2 = jk_inner;
            
            elog(NOTICE, "BEFORE UPPER BOUND");
            uinfo->upper_bound = get_upper_bound(root, jk_outer, jk_inner);
            elog(NOTICE, "AFTER UPPER BOUND");

            if(type == UES_JOIN_EXPANDING)
            {
                ues_state->expanding_joins = lappend(ues_state->expanding_joins, uinfo);
            }else
            {
                ues_state->filter_joins = lappend(ues_state->filter_joins, uinfo);
            }
        }
    }

    elog(NOTICE, "[finished] ues_update_joinrels");
}

UpperBound get_upper_bound(PlannerInfo* info, UesJoinKey* left_key, UesJoinKey* right_key)
{
    // TODO: muss für Filter nicht berechnet werden.
    Freq            freq_left,
                    freq_right;
    Cardinality     card_left,
                    card_right;

    double maximal_pair_appearance;
    double most_common_values_prod;
    double max_apperance_left;
    double max_appearance_right;

    freq_left = left_key->max_freq;
    freq_right = right_key->max_freq;

    card_left = left_key->baserel->tuples;
    card_right = right_key->baserel->tuples;

    max_apperance_left = card_left / freq_left;
    max_appearance_right = card_right / freq_right;

    maximal_pair_appearance = Min(max_apperance_left, max_appearance_right);

    most_common_values_prod = freq_left * freq_right;
    
    return (UpperBound) maximal_pair_appearance * most_common_values_prod;
}

void ues_sort_expanding_joins(PlannerInfo* root)
{
    List*           output;
    UesState*       ues_state;
    ListCell*       lcej;
    ListCell*       curr_cell;
    UesJoinInfo*    curr_info;
    UesJoinInfo*    elem;
    int             curr_min;
    int             upper_bound;

    ues_state = root->join_search_private;
    curr_info = (UesJoinInfo*) palloc(sizeof(UesJoinInfo));
    output = NIL;
    
    if(ues_state->expanding_joins == NIL || 
        ues_state->expanding_joins->length == 0)
    {
        elog(INFO, "no expanding joins found");
        return;
    }

    UesJoinInfo* t = (UesJoinInfo*)linitial(ues_state->expanding_joins);
    if (t->rel1 == NULL) {
        elog(ERROR, "------------------------fdfd 1");
    }

    while(ues_state->expanding_joins->length != 0)
    {   
        curr_min = INTMAX_MAX;
        foreach(lcej, ues_state->expanding_joins)
        {   
            elem = (UesJoinInfo*) lfirst(lcej);
            upper_bound = elem->upper_bound;
            if(upper_bound > curr_min)
            {
                curr_cell = lcej;
                curr_info = elem;
                curr_min = upper_bound;
            }
        }
        output = lappend(output, curr_info);

        if(curr_info==NULL)
        {
            elog(NOTICE, "exist check: %s", curr_info==NULL);
        }
        // @todo: this is not how to use list_delete_cell. But with normal use it doesnt work lol
        list_delete_cell(ues_state->expanding_joins, curr_cell); // Hier lieber auf Kopie arbeiten?

        if(curr_info==NULL)
        {
            elog(NOTICE, "exist check: %s", curr_info==NULL);
        }
        
        //elog(NOTICE, "output length: %d", output->length);
        //elog(NOTICE, "expnd length: %d", ues_state->expanding_joins->length);
        
    }

    elog(NOTICE, "finished sorting. sorted list in output");
    ues_state->expanding_joins = output;

    UesJoinInfo* t2 = (UesJoinInfo*)linitial(ues_state->expanding_joins);
    if (t2->rel1 == NULL) {
        elog(ERROR, "------------------------fdfd 2");
    }
    //list_free(output);
}

/*
 * returns next join classified as expanding that needs to be joined
 *
 * Gets an UesState object from root->join_search_private. Then iterates over
 * List expandng_joins and compare upper bounds to decide which is next.
 */
UesJoinInfo*
ues_get_next_expanding_join(PlannerInfo* root)
{
    UesState*       ues_state;
    ListCell*       lcji;
    UesJoinInfo*    uji;
    UesJoinInfo*    uji_next;
    UpperBound      ub_next;

    ues_state = root->join_search_private;
    ub_next = 0;

    if(ues_state->expanding_joins == NIL)
    {
        return NULL;
    }

    /* iterate over all joins classified as expanding */
    foreach(lcji, ues_state->expanding_joins)
    {
        uji = (UesJoinInfo*) lfirst(lcji);

        /* check if current UpperBound is higher, than previous*/
        if(ub_next < uji->upper_bound)
        {
            ub_next = uji->upper_bound;
            uji_next = uji;
        }
    }

    Assert(uji_next != NULL);
    Assert(uji_next->join_type == UES_JOIN_EXPANDING);

    return uji_next;
}

/*
* sets up the enumeration part
*
* takes the first expanding join and put its two relations into 
* the currentrel in ues_state and returns the other one.
*
* If no expanding joins available this funktions takes a 
* filter relation.
*/
RelOptInfo* ues_init_enumeration(PlannerInfo* root, UesJoinInfo** ujinfo)
{
    UesState*       ues_state;
    UesJoinInfo*    join;
    UesJoinInfo*    filter;

    ues_state = root->join_search_private;

    elog(NOTICE, "[called] ues_init_enumeration");

    /*
    * Case 1: there are no expanding joins
    *
    * In this case we choose a filter join
    */
    if(ues_state->expanding_joins == NULL ||
        ues_state->expanding_joins->length == 0){
        elog(NOTICE, "ues_state->expanding_joins is NULL or empty. \
                        No expanding joins present. Consider filter as fallback."); 
        filter = (UesJoinInfo*) linitial(ues_state->filter_joins);
        *ujinfo = filter;
        //ues_state->current_intermediate = filter->rel1->baserel;
        return filter->rel1->baserel;
    }

    elog(NOTICE, "expanding joins are available");
    join = (UesJoinInfo*) linitial(ues_state->expanding_joins);
    // if (join->rel1 == NULL) {
    //     elog(ERROR, "No expanding join found (join is NULL)");
    //     return NULL;
    // }
    // elog(NOTICE, "got join");
    //ues_state->current_intermediate = join->rel1->baserel;
    // elog(NOTICE, "vor return");
    *ujinfo = join;

    elog(NOTICE, "[finished] ues_init_enumeration");
    return join->rel1->baserel;
}
/*
* returns the next join to do
*
* checks for: exactly one join key is already contained in curr_intermediate
*/
RelOptInfo* ues_next_join(PlannerInfo* root, UesJoinInfo** ujinfo)
{
    UesState*       ues_state;
    UesJoinInfo*    join;
    ListCell*       lc;
    RelOptInfo*     elem1;
    RelOptInfo*     elem2;
    RelOptInfo*     elem_curr;

    elog(NOTICE, "[called] ues_next_join");

    ues_state = root->join_search_private;
    elem_curr = ues_state->current_intermediate;

    if(ues_state->expanding_joins == NULL)
    {
        elog(NOTICE, "expanding joins is NULL");
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
ues_switch_key_in_list(PlannerInfo* root, UesJoinKey* jkey)
{
    UesState*   ues_state;
    UesJoinKey* key;
    UesJoinKey* dummy;
    ListCell*   lc;
    ListCell*   cell;
    Oid         rel;
    char*       name_rel;
    char*       name_att;

    ues_state = root->join_search_private;
    key = jkey;

    elog(NOTICE, "[called] ues_switch_key_in_list");

    if(list_member(ues_state->candidate_keys, key))
    {   
        foreach(lc, ues_state->candidate_keys)
        {   
            dummy = (UesJoinKey*) lfirst(lc);
            if(dummy == key)
            {
                cell = lc;
                break;
            }
        }
        ues_state->candidate_keys = list_delete_cell(ues_state->candidate_keys, cell);
        ues_state->joined_keys = lappend(ues_state->joined_keys, key);

        
        rel = root->simple_rte_array[key->baserel->relid]->relid;
        name_rel = get_rel_name(rel);
        name_att = get_attname(rel, key->join_key->varattno, false);
        elog(NOTICE, "\tswitched %s from rel %s", name_att, name_rel);
    }

    elog(NOTICE, "[finished] ues_switch_key_in_list");
}

/*
* Makes an relation for ues. Assumes that an UesState
* is stored in root->join_search_private. At the end
* this function calls the default make_join_rel from
* postgres. But before so, we have to work off the 
* following ToDo:
*
* a) delete the UesJoinInfo object from expanding_joins
*    or filter_joins list.
* b) update Keys after joining
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

    ues_state = root->join_search_private;
    info = jinfo;

    elog(NOTICE, "[called] ues_make_join_rel");

    /*
    * a) Delete UesJoinInfo Object from associated list.
    *    To do so, we distinguish according to join_type.
    *    When decided, we iterate over the associated list
    *    until we found our element. That helps us to
    *    determine the ListCell of the element in the list.
    *    At last we delete the element from the list.
    */
    if(info->join_type == UES_JOIN_EXPANDING)
    {
        foreach(lc, ues_state->expanding_joins)
        {
            dummy = (UesJoinInfo*) lfirst(lc);
            if(dummy == jinfo)
            {
                cell = lc;
                break;
            }
        }
        ues_state->expanding_joins = list_delete_cell(ues_state->expanding_joins, cell);

    /* part two for the filter case*/
    }else if(info->join_type == UES_JOIN_FILTER)
    {
        foreach(lc, ues_state->filter_joins)
        {
            dummy = (UesJoinInfo*) lfirst(lc);
            if(dummy == jinfo)
            {
                cell = lc;
                break;
            }
        }
        ues_state->filter_joins = list_delete_cell(ues_state->filter_joins, cell);

    /* the error case */
    }else
    {
        elog(ERROR, "Couldn't recognize join type");
    }
    
    /*
    * update upperbounds
    */
    
   
    /*
     * b) update the keys here
     * 
     * candidate key -> joined key
     * update upperbound
     */
    ues_switch_key_in_list(root, jinfo->rel1);
    ues_switch_key_in_list(root, jinfo->rel2);
    
    //now rebuild expnd/join lists
    ues_update_joinrels(root);
    
    /* perform actual join */
    join = make_join_rel(root, rel1, rel2);
    set_cheapest(join);

    elog(NOTICE, "[finished] ues_make_join_rel. Current UesState and detected joins following: (intermediate wrong)");
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

    rel_oid = root->simple_rte_array[jrel->relid]->relid;
    relname = get_rel_name(rel_oid);
    elog(NOTICE, "[called] ues_join_filters for rel %s. Deteced joins followed:", relname);
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
        elog(NOTICE, "while iteration over filters: %d", i++);
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
                elog(NOTICE, "no eclass join possible with this filter");
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
    
    elog(NOTICE, "Remaining joins:");
    ues_print_joins(root, ues_state);
    elog(NOTICE, "[finished] ues_join_filters");
    return rel;
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
    bool    triggers_ues = ues_enabled && ues_supported_query(root);

    elog(INFO, "UES join search: %s", triggers_ues ? "enabled" : "disabled");

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

    /*
     * Prepare anything for UES. 
     */
    ues_state = ues_join_search_init(root);
    ues_init_baserels(root, &initial_rels);
    ues_init_joinrels(root);
    ues_print_state(root, ues_state);
    ues_print_joins(root, ues_state);

    loop_count = 0;

    /*
     * ues algorithm starts here
     */
    ues_sort_expanding_joins(root);

    msg = makeStringInfo();
    appendStringInfo(msg, "\n=========================\n");
    appendStringInfo(msg, "   preperation finished   \n");
    appendStringInfo(msg, "==========================\n");
    elog(NOTICE, "%s", msg->data);
    destroyStringInfo(msg);

    while((ues_state->expanding_joins != NULL && 
            ues_state->expanding_joins != NIL) && 
            !ues_state->expanding_joins->length <= 0)
    {
        /*
        * Normally we join on ues_state->current_intermediate
        * but when we start joining relations it is NULL, NIL
        * or whatever. So we need a case differentiation. The
        * default method is ues_next_join which returns the 
        * next expanding join. 
        * 
        * When we are in the first enumeration of the while
        * loop, we call ues_init_enumeration, which also
        * returns the next expanding join. Additionally it
        * sets ues_state->current_intermediate to the other
        * relation of the expanding join which is not 
        * returned.
        */
        msg = makeStringInfo();
        appendStringInfo(msg, "\n--------------------------\n");
        appendStringInfo(msg, " main loop, iteration:%d   \n", loop_count++);
        appendStringInfo(msg, "--------------------------\n");
        elog(NOTICE, "%s", msg->data);
        destroyStringInfo(msg);


        if(ues_state->current_intermediate == NULL)
        {  
            ues_state->current_intermediate = ues_init_enumeration(root, &expanding);
            elog(NOTICE, "initial expanding join set");

            /*
             * To prevent inconsistent states we have to
             * join filters right here. In worst case it
             * could happen that we lose our expanding
             * join when joining all filters. This would
             * lead to inconsistent states and provoke
             * segmentation faults.
             * 
             * Afterwards we "restart" the main while
             * loop with an continue. If we lost our
             * expanding join we can skip the most
             * part of ues and can directly check for
             * remaining filters.
             */
            ues_state->current_intermediate = ues_join_filters(root, ues_state->current_intermediate);

            elog(NOTICE, "<<< End main while loop. It follows the current state:");
            ues_print_state(root, ues_state);

            continue;
        }
        
        /*
         * loading next expanding join. We 
         * can assume that there is a mini-
         * mim of one expanding join due to
         * the ues_state->expanding_joins
         * is not NULL, NIL or emtpy
         */
        next_join = ues_next_join(root, &expanding);
        elog(NOTICE, "next expanding join set");
        
        /*
         * defensive programming: Catch errors that
         * (actually) can't happen, just in case 
         * they appear.
         * 
         * We could have an expanding join that
         * isn't joinable due to no common eclasses.
         */
        if(next_join == NULL)
        {
            elog(ERROR, "Couldn't set next expanding join");
        }

        /* 
         * here we are at a state where its clear, that we
         * want to join next_join to current_intermediate.
         * 
         * the next step consists of determining which filters 
         * can be joined into them.
         */

        /*
         * Check if there are any filter joins left.
         * If not, we can skip this. 
         */
        if(ues_state->filter_joins == NULL)
        {
            elog(NOTICE, "no filters left. Join on current_intermediate now.");
            ues_state->current_intermediate = ues_make_join_rel(root, ues_state->current_intermediate, next_join, expanding);

            elog(NOTICE, "<<< End main while loop. It follows the current state:");
            ues_print_state(root, ues_state);
            ues_print_joins(root, ues_state);
            continue;
        }

        msg = makeStringInfo();
        appendStringInfo(msg, "\n==========================\n");
        appendStringInfo(msg, "    main loop finished    \n");
        appendStringInfo(msg, "==========================\n");
        elog(NOTICE, "%s", msg->data);
        destroyStringInfo(msg);

        ues_print_state(root, ues_state);

        /*
         * Join filters on next_join and 
         * current_intermediate.
         */        
        ues_state->current_intermediate = ues_join_filters(root, ues_state->current_intermediate); //delete?
        next_join = ues_join_filters(root, next_join);
        elog(NOTICE, "All possible filters joined");
        
        /*
        *   all possible filters were appiled. In the next step
        *   we have to join the next_join on the intermediate,
        *   before we chose the next expanding join to add.
        */
        ues_state->current_intermediate = ues_make_join_rel(root, ues_state->current_intermediate, next_join, expanding);

        //elog(NOTICE, "Expanding joins: %d", ues_state->expanding_joins->length);
        elog(NOTICE, "<<< End main while loop. It follows the current state:");
        ues_print_state(root, ues_state);
    }

    /*
    *   At this point we can assume that we joined all expanding 
    *   joins. At last we need to check if we joined all filters 
    *   due to the fact that they are not included in the big loops
    *   condition.
    * 
    *   If filter_joins is not NULL or NIL, there are joins left
    *   in the list. If this happend, the filters couldn't joined
    *   anywhere. This is an error, that should not occur.
    */
    if(ues_state->filter_joins != NULL && 
        ues_state->filter_joins != NIL)
    {
        if(ues_state->filter_joins->length > 0)
        {
            elog(ERROR, "Couldn't skedule all filter joins. Filters remaining: %d", ues_state->filter_joins->length);
        }
    }

    /*
    * return current_intermediate from ues_state and 
    * prepare everything for return into postgres code.
    */
    joinrel = ues_state->current_intermediate;
    set_cheapest(joinrel);

    /*
    * Clean up ues data in memory to avoid
    * memory overflow.
    */
    ues_join_search_cleanup(root);


    elog(NOTICE, "ues finished. return into postgres code");
    return joinrel;
}

void _PG_init(void)
{
    prev_join_search_hook = join_search_hook;
    join_search_hook = ues_join_search;

    DefineCustomBoolVariable("ues.enable_ues", "Enable the UES query optimizer", NULL,
                             &ues_enabled, false,
                             PGC_USERSET, 0, NULL, NULL, NULL);

    elog(INFO, "UES module loaded");
}

void _PG_fini(void)
{
    join_search_hook = prev_join_search_hook;
}
