
typedef double Freq;

typedef double UpperBound;

typedef enum KeyType
{
    KT_NONE = 0,
    KT_PRIMARY = 1, /* Primary key or UNIQUE */
    KT_FOREIGN = 2  /* Foreign key referencing some other column */
} KeyType;

typedef struct UesState
{
    /*
    * This is the intermediate that we have already built.
    * It should contain exactly one path corresponding to the hash join/sequential scan path that we are going to use.
    */
   RelOptInfo  *current_intermediate;
   
   /*
   * The upper bound cardinality of our current intermediate.
   *
   * We don't store this in the cost of the RelOptInfo path or the rows of the RelOptInfo to prevent unwanted side effects
   * with other parts of the planner (e.g. when determining the number of parallel workers).
   */
    UpperBound   current_bound;

    /* All columns that have already been joined and are part of our current intermediate  */
    List        *joined_keys;       /* UesJoinKey entries. */
    
    /* All columns that still need to be joined with the current intermediate */
    List        *candidate_keys;    /* UesJoinKey entries */
    
    /* All joins that will expand the tuples in the join tree */
    List        *expanding_joins; /* UESJoinInfo entries */
    
    /* All joins that solely filter the tuples in the join tree */
    List        *filter_joins;   /* UESJoinInfo entries */
} UesState;


typedef struct UesJoinKey
{
    /*
    * The intermediate that this column belongs to.
     * We use the RelOptInfo rather than the Relid because on most code paths we need to access the RelOptInfo anyway.
     *
     * This is just a non-owning reference to the planner's data.
     */
    RelOptInfo  *baserel;
    
    /*
    * The column being joined. It belongs to the Relid of the RelOptInfo.
     *
     * This is just a non-owning reference to the planner's data.
     */
    Var         *join_key;

    /* The maximum frequency of any value in the column. */
    Freq         max_freq;
    
    /* Constraints that are specified on the column. */
    KeyType      key_type;
} UesJoinKey;

typedef enum UesJoinType
{
    UES_JOIN_EXPANDING = 0,
    UES_JOIN_FILTER = 1,
} UesJoinType;

typedef struct UesJoinInfo
{
    UesJoinKey* rel1;
    UesJoinKey* rel2;
    UesJoinType join_type;
    UpperBound upper_bound;
}UesJoinInfo;

static UpperBound get_upper_bound(PlannerInfo* info, UesJoinKey* key1, UesJoinKey* key2);








static bool
join_is_legal(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2,
			  Relids joinrelids,
			  SpecialJoinInfo **sjinfo_p, bool *reversed_p)
{
	SpecialJoinInfo *match_sjinfo;
	bool		reversed;
	bool		unique_ified;
	bool		must_be_leftjoin;
	ListCell   *l;

	/*
	 * Ensure output params are set on failure return.  This is just to
	 * suppress uninitialized-variable warnings from overly anal compilers.
	 */
	*sjinfo_p = NULL;
	*reversed_p = false;

	/*
	 * If we have any special joins, the proposed join might be illegal; and
	 * in any case we have to determine its join type.  Scan the join info
	 * list for matches and conflicts.
	 */
	match_sjinfo = NULL;
	reversed = false;
	unique_ified = false;
	must_be_leftjoin = false;

	foreach(l, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

		/*
		 * This special join is not relevant unless its RHS overlaps the
		 * proposed join.  (Check this first as a fast path for dismissing
		 * most irrelevant SJs quickly.)
		 */
		if (!bms_overlap(sjinfo->min_righthand, joinrelids))
			continue;

		/*
		 * Also, not relevant if proposed join is fully contained within RHS
		 * (ie, we're still building up the RHS).
		 */
		if (bms_is_subset(joinrelids, sjinfo->min_righthand))
			continue;

		/*
		 * Also, not relevant if SJ is already done within either input.
		 */
		if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel1->relids))
			continue;
		if (bms_is_subset(sjinfo->min_lefthand, rel2->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel2->relids))
			continue;

		/*
		 * If it's a semijoin and we already joined the RHS to any other rels
		 * within either input, then we must have unique-ified the RHS at that
		 * point (see below).  Therefore the semijoin is no longer relevant in
		 * this join path.
		 */
		if (sjinfo->jointype == JOIN_SEMI)
		{
			if (bms_is_subset(sjinfo->syn_righthand, rel1->relids) &&
				!bms_equal(sjinfo->syn_righthand, rel1->relids))
				continue;
			if (bms_is_subset(sjinfo->syn_righthand, rel2->relids) &&
				!bms_equal(sjinfo->syn_righthand, rel2->relids))
				continue;
		}

		/*
		 * If one input contains min_lefthand and the other contains
		 * min_righthand, then we can perform the SJ at this join.
		 *
		 * Reject if we get matches to more than one SJ; that implies we're
		 * considering something that's not really valid.
		 */
		if (bms_is_subset(sjinfo->min_lefthand, rel1->relids) &&
			bms_is_subset(sjinfo->min_righthand, rel2->relids))
		{
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = false;
		}
		else if (bms_is_subset(sjinfo->min_lefthand, rel2->relids) &&
				 bms_is_subset(sjinfo->min_righthand, rel1->relids))
		{
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = true;
		}
		else if (sjinfo->jointype == JOIN_SEMI &&
				 bms_equal(sjinfo->syn_righthand, rel2->relids) &&
				 create_unique_path(root, rel2, rel2->cheapest_total_path,
									sjinfo) != NULL)
		{
			/*----------
			 * For a semijoin, we can join the RHS to anything else by
			 * unique-ifying the RHS (if the RHS can be unique-ified).
			 * We will only get here if we have the full RHS but less
			 * than min_lefthand on the LHS.
			 *
			 * The reason to consider such a join path is exemplified by
			 *	SELECT ... FROM a,b WHERE (a.x,b.y) IN (SELECT c1,c2 FROM c)
			 * If we insist on doing this as a semijoin we will first have
			 * to form the cartesian product of A*B.  But if we unique-ify
			 * C then the semijoin becomes a plain innerjoin and we can join
			 * in any order, eg C to A and then to B.  When C is much smaller
			 * than A and B this can be a huge win.  So we allow C to be
			 * joined to just A or just B here, and then make_join_rel has
			 * to handle the case properly.
			 *
			 * Note that actually we'll allow unique-ified C to be joined to
			 * some other relation D here, too.  That is legal, if usually not
			 * very sane, and this routine is only concerned with legality not
			 * with whether the join is good strategy.
			 *----------
			 */
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = false;
			unique_ified = true;
		}
		else if (sjinfo->jointype == JOIN_SEMI &&
				 bms_equal(sjinfo->syn_righthand, rel1->relids) &&
				 create_unique_path(root, rel1, rel1->cheapest_total_path,
									sjinfo) != NULL)
		{
			/* Reversed semijoin case */
			if (match_sjinfo)
				return false;	/* invalid join path */
			match_sjinfo = sjinfo;
			reversed = true;
			unique_ified = true;
		}
		else
		{
			/*
			 * Otherwise, the proposed join overlaps the RHS but isn't a valid
			 * implementation of this SJ.  But don't panic quite yet: the RHS
			 * violation might have occurred previously, in one or both input
			 * relations, in which case we must have previously decided that
			 * it was OK to commute some other SJ with this one.  If we need
			 * to perform this join to finish building up the RHS, rejecting
			 * it could lead to not finding any plan at all.  (This can occur
			 * because of the heuristics elsewhere in this file that postpone
			 * clauseless joins: we might not consider doing a clauseless join
			 * within the RHS until after we've performed other, validly
			 * commutable SJs with one or both sides of the clauseless join.)
			 * This consideration boils down to the rule that if both inputs
			 * overlap the RHS, we can allow the join --- they are either
			 * fully within the RHS, or represent previously-allowed joins to
			 * rels outside it.
			 */
			if (bms_overlap(rel1->relids, sjinfo->min_righthand) &&
				bms_overlap(rel2->relids, sjinfo->min_righthand))
				continue;		/* assume valid previous violation of RHS */

			/*
			 * The proposed join could still be legal, but only if we're
			 * allowed to associate it into the RHS of this SJ.  That means
			 * this SJ must be a LEFT join (not SEMI or ANTI, and certainly
			 * not FULL) and the proposed join must not overlap the LHS.
			 */
			if (sjinfo->jointype != JOIN_LEFT ||
				bms_overlap(joinrelids, sjinfo->min_lefthand))
				return false;	/* invalid join path */

			/*
			 * To be valid, the proposed join must be a LEFT join; otherwise
			 * it can't associate into this SJ's RHS.  But we may not yet have
			 * found the SpecialJoinInfo matching the proposed join, so we
			 * can't test that yet.  Remember the requirement for later.
			 */
			must_be_leftjoin = true;
		}
	}

	/*
	 * Fail if violated any SJ's RHS and didn't match to a LEFT SJ: the
	 * proposed join can't associate into an SJ's RHS.
	 *
	 * Also, fail if the proposed join's predicate isn't strict; we're
	 * essentially checking to see if we can apply outer-join identity 3, and
	 * that's a requirement.  (This check may be redundant with checks in
	 * make_outerjoininfo, but I'm not quite sure, and it's cheap to test.)
	 */
	if (must_be_leftjoin &&
		(match_sjinfo == NULL ||
		 match_sjinfo->jointype != JOIN_LEFT ||
		 !match_sjinfo->lhs_strict))
		return false;			/* invalid join path */

	/*
	 * We also have to check for constraints imposed by LATERAL references.
	 */
	if (root->hasLateralRTEs)
	{
		bool		lateral_fwd;
		bool		lateral_rev;
		Relids		join_lateral_rels;

		/*
		 * The proposed rels could each contain lateral references to the
		 * other, in which case the join is impossible.  If there are lateral
		 * references in just one direction, then the join has to be done with
		 * a nestloop with the lateral referencer on the inside.  If the join
		 * matches an SJ that cannot be implemented by such a nestloop, the
		 * join is impossible.
		 *
		 * Also, if the lateral reference is only indirect, we should reject
		 * the join; whatever rel(s) the reference chain goes through must be
		 * joined to first.
		 *
		 * Another case that might keep us from building a valid plan is the
		 * implementation restriction described by have_dangerous_phv().
		 */
		lateral_fwd = bms_overlap(rel1->relids, rel2->lateral_relids);
		lateral_rev = bms_overlap(rel2->relids, rel1->lateral_relids);
		if (lateral_fwd && lateral_rev)
			return false;		/* have lateral refs in both directions */
		if (lateral_fwd)
		{
			/* has to be implemented as nestloop with rel1 on left */
			if (match_sjinfo &&
				(reversed ||
				 unique_ified ||
				 match_sjinfo->jointype == JOIN_FULL))
				return false;	/* not implementable as nestloop */
			/* check there is a direct reference from rel2 to rel1 */
			if (!bms_overlap(rel1->relids, rel2->direct_lateral_relids))
				return false;	/* only indirect refs, so reject */
			/* check we won't have a dangerous PHV */
			if (have_dangerous_phv(root, rel1->relids, rel2->lateral_relids))
				return false;	/* might be unable to handle required PHV */
		}
		else if (lateral_rev)
		{
			/* has to be implemented as nestloop with rel2 on left */
			if (match_sjinfo &&
				(!reversed ||
				 unique_ified ||
				 match_sjinfo->jointype == JOIN_FULL))
				return false;	/* not implementable as nestloop */
			/* check there is a direct reference from rel1 to rel2 */
			if (!bms_overlap(rel2->relids, rel1->direct_lateral_relids))
				return false;	/* only indirect refs, so reject */
			/* check we won't have a dangerous PHV */
			if (have_dangerous_phv(root, rel2->relids, rel1->lateral_relids))
				return false;	/* might be unable to handle required PHV */
		}

		/*
		 * LATERAL references could also cause problems later on if we accept
		 * this join: if the join's minimum parameterization includes any rels
		 * that would have to be on the inside of an outer join with this join
		 * rel, then it's never going to be possible to build the complete
		 * query using this join.  We should reject this join not only because
		 * it'll save work, but because if we don't, the clauseless-join
		 * heuristics might think that legality of this join means that some
		 * other join rel need not be formed, and that could lead to failure
		 * to find any plan at all.  We have to consider not only rels that
		 * are directly on the inner side of an OJ with the joinrel, but also
		 * ones that are indirectly so, so search to find all such rels.
		 */
		join_lateral_rels = min_join_parameterization(root, joinrelids,
													  rel1, rel2);
		if (join_lateral_rels)
		{
			Relids		join_plus_rhs = bms_copy(joinrelids);
			bool		more;

			do
			{
				more = false;
				foreach(l, root->join_info_list)
				{
					SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(l);

					/* ignore full joins --- their ordering is predetermined */
					if (sjinfo->jointype == JOIN_FULL)
						continue;

					if (bms_overlap(sjinfo->min_lefthand, join_plus_rhs) &&
						!bms_is_subset(sjinfo->min_righthand, join_plus_rhs))
					{
						join_plus_rhs = bms_add_members(join_plus_rhs,
														sjinfo->min_righthand);
						more = true;
					}
				}
			} while (more);
			if (bms_overlap(join_plus_rhs, join_lateral_rels))
				return false;	/* will not be able to join to some RHS rel */
		}
	}

	/* Otherwise, it's a valid join */
	*sjinfo_p = match_sjinfo;
	*reversed_p = reversed;
	return true;
}

static void
populate_joinrel_with_paths(PlannerInfo *root, RelOptInfo *rel1,
							RelOptInfo *rel2, RelOptInfo *joinrel,
							SpecialJoinInfo *sjinfo, List *restrictlist)
{
	/*
	 * Consider paths using each rel as both outer and inner.  Depending on
	 * the join type, a provably empty outer or inner rel might mean the join
	 * is provably empty too; in which case throw away any previously computed
	 * paths and mark the join as dummy.  (We do it this way since it's
	 * conceivable that dummy-ness of a multi-element join might only be
	 * noticeable for certain construction paths.)
	 *
	 * Also, a provably constant-false join restriction typically means that
	 * we can skip evaluating one or both sides of the join.  We do this by
	 * marking the appropriate rel as dummy.  For outer joins, a
	 * constant-false restriction that is pushed down still means the whole
	 * join is dummy, while a non-pushed-down one means that no inner rows
	 * will join so we can treat the inner rel as dummy.
	 *
	 * We need only consider the jointypes that appear in join_info_list, plus
	 * JOIN_INNER.
	 */
    elog(INFO, "JoinType: %d", sjinfo->jointype);
	switch (sjinfo->jointype)
	{
		case JOIN_INNER:
			add_paths_to_joinrel(root, joinrel, rel1, rel2,
								 JOIN_INNER, sjinfo,
								 restrictlist);
			add_paths_to_joinrel(root, joinrel, rel2, rel1,
								 JOIN_INNER, sjinfo,
								 restrictlist);
			break;
		default:
			/* other values not expected here */
			elog(ERROR, "unrecognized join type: %d", (int) sjinfo->jointype);
			break;
	}
}