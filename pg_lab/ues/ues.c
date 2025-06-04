
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
    state->filter_joins        = NIL;

    root->join_search_private = state;
    return state;
}

static void
ues_join_search_cleanup(PlannerInfo *root)
{
    UesState *state = root->join_search_private;
    list_free_deep(state->joined_keys);
    list_free_deep(state->candidate_keys);
    list_free_deep(state->expanding_joins);
    list_free_deep(state->filter_joins);
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

    appendStringInfo(msg, "\nJOINS CURRENTLY KLASSIFIED AS EXPANDING");
    foreach(ejlc, ues_state->expanding_joins){
        uji = lfirst(ejlc);
        rel1 = root->simple_rte_array[uji->rel1->baserel->relid]->relid;
        rel2 = root->simple_rte_array[uji->rel2->baserel->relid]->relid;
        appendStringInfo(msg, "\nRel1: %s\nRel2: %s\nUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
    }
    appendStringInfo(msg, "\n\nJOINS CURRENTLY KLASSIFIED AS FILTER");
    foreach(ejlc, ues_state->filter_joins){
        uji = lfirst(ejlc);
        rel1 = root->simple_rte_array[uji->rel1->baserel->relid]->relid;
        rel2 = root->simple_rte_array[uji->rel2->baserel->relid]->relid;
        appendStringInfo(msg, "\nRel1: %s\nRel2: %s\nUB: %f\n---", get_rel_name(rel1), get_rel_name(rel2), uji->upper_bound);
    }

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
            
        }
    }
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

RelOptInfo*
ues_join_search(PlannerInfo *root, int levels_needed, List *initial_rels)
{
    int          lev;
    RelOptInfo  *rel;
    UesState    *ues_state;
    bool         triggers_ues = ues_enabled && ues_supported_query(root);

    elog(INFO, "UES join search: %s", triggers_ues ? "enabled" : "disabled");

    RelOptInfo* test;
    if (!triggers_ues)
    {
        if (prev_join_search_hook)
            return prev_join_search_hook(root, levels_needed, initial_rels);
        else if (enable_geqo && levels_needed >= geqo_threshold)
            return geqo(root, levels_needed, initial_rels);
        else
            test = standard_join_search(root, levels_needed, initial_rels);
            return test;
    }

    ues_state = ues_join_search_init(root);
    ues_init_baserels(root, &initial_rels);
    ues_init_joinrels(root);
    ues_print_state(root, ues_state);
    ues_print_joins(root, ues_state);

    /*
     * XXX
     * Do magic UES stuff
     *
     */
    rel = ues_state->current_intermediate;
    
    //ListCell *key1;
    //ListCell *key2;

    //have_relevant_join_clause

    // while(ues_state->candidate_keys->length > 0)
    // {
    //     UesJoinInfo*    next_exp_join;

    //     /* select next expanding join */
    //     next_exp_join = ues_get_next_expanding_join(root);

    //     /* alle Filter iterieren und ggfs. anfügen */
    //     ListCell* lcfilter;
    //     foreach(lcfilter, ues_state->filter_joins)
    //     {
    //         UesJoinInfo* uinfo = (UesJoinInfo*) lfirst(lcfilter);

    //         /* check if rel1 from UesJoinInfo is already in current_intermediate */
    //         if(have_relevant_eclass_joinclause(root, rel, uinfo->rel1->baserel) &&
    //             bms_overlap(rel->relids, uinfo->rel1->baserel->relids))
    //         {
    //             /* if it is in current_intermediate, we can add the other baserel, if not also already included */
    //         }
    //     }

    //     //rel = 
    // }

    elog(NOTICE, "GANZ WILDER VERSUCH");

    UesJoinInfo*        next_exp_join;
    SpecialJoinInfo*    sjinfo;
    List*               pushed_down_joins;
    List*               restrictlist;
    RelOptInfo*         rel1;
    RelOptInfo*         rel2;
    bool                reversed;
    Bitmapset*          joinrelids;
    SpecialJoinInfo     sjinfo_data;
    JoinPathExtraData   extra;

    /* select next expanding join */
    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.0 ues_get_next_expanding_join");
    next_exp_join = ues_get_next_expanding_join(root);
    if(next_exp_join == NULL)
    {
        next_exp_join = linitial(ues_state->filter_joins);
    }

    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.1 set rels");
    rel1 = next_exp_join->rel1->baserel;
    rel2 = next_exp_join->rel2->baserel;
    
    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.2 union generieren");

    joinrelids = bms_union(rel1->relids, rel2->relids);
    
    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.3 legal check");

    join_is_legal(root, rel1, rel2, joinrelids, &sjinfo, &reversed);

    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.4 init_dummy_info");

    sjinfo = &sjinfo_data;
    init_dummy_sjinfo(sjinfo, rel1->relids, rel2->relids);

    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 1.5 add_outer_joins_to_relids");

    // macht effektiv nichts, aber verhindert compiler warning
    joinrelids = add_outer_joins_to_relids(root, joinrelids, sjinfo,
                                            &pushed_down_joins);

    //rel = build_ues_rel(root, bms_union(next_exp_join->rel1->baserel->relids, next_exp_join->rel2->baserel->relids), 
    //    next_exp_join->rel1->baserel, next_exp_join->rel2->baserel);
    
    
    elog(NOTICE, "GANZ WILDER VERSUCH    -----------2");

    RelOptInfo *joinrel = build_join_rel(root, joinrelids,
                                        rel1, rel2, sjinfo, pushed_down_joins, &restrictlist);

    //rel = ues_join_rels(root, next_exp_join->rel1->baserel, next_exp_join->rel2->baserel);
    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 3 gen paths");

    
    // extra.restrictlist = restrictlist;
	// extra.mergeclause_list = NIL;
	// extra.sjinfo = sjinfo;
	// extra.param_source_rels = NULL;

    // extra.param_source_rels = bms_add_members(extra.param_source_rels,
    //     joinrel->lateral_relids);

    //hash_inner_and_outer(root, joinrel, rel1, rel2, JOIN_INNER, &extra);

    if(is_dummy_rel(rel1))
    {
        elog(ERROR, "rel1 ist leer");
    }
    if(is_dummy_rel(rel2))
    {
        elog(ERROR, "rel2 ist leer");
    }

    populate_joinrel_with_paths(root, rel1, rel2, joinrel, sjinfo, restrictlist);
    set_cheapest(joinrel);

    /*
    * struct expndJoin{
    *    RelOptInfo *rel1;
    *    RelOptInfo *rel2;
    *    UpperBound upper_bound;
    * }
    *
    * 
    * 1. Liste mit expanding-Joins erstellen
    *      List<expnd_joins> expnding_joins = GetExpandingJoins(ues_state->candidate_keys); //pk oder unique
    * 2. Liste mit upper bounds zwischen baserels mit expanding Operatoren berechnen
    *      foreach join in expnding_joins:
    *        GetUpperBound(*join);
    * 3. Liste nach |upper bound| sortieren
    *      SortList(expnding_joins);
    * 
    * loop: length(ues_state->candidate_keys) != 0      // Pool, aus dem rels gezogen werden
    *   select expnding_joins[0]                        // join mit kleinster upper bound auswählen
    *   foreach element in ues_state->candidate_keys:           // Ziel: alle rels die Filter auf expnding_joins rels sind, auswählen
    *     if (HasRelevantExpr(expnding_joins[0], element)):     // überprüfen, ob element ein Filter ist
    *       ues_state->current_intermediate += element;         // ganz viele Variablen updaten
    *       ues_state->joined_keys += element;
    *       ues_state->candidate_keys -= element;
    *       ues_state->current_bound += element.upper_bound;    // PROBLEM: Filter Überprüfung müsste nach jedem join neu beginnen
    * 
    *       // NOTE: Key Eigentschaften verändern sich, bei expanding joins
    */

    elog(NOTICE, "GANZ WILDER VERSUCH    ----------- 4 fertig");
    
    rel = joinrel;

    //rel = standard_join_search(root, levels_needed, initial_rels); /* Remove this */

    ues_join_search_cleanup(root);
    return rel;
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
