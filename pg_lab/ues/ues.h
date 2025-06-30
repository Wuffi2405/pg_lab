
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

//RelOptInfo* ues_next_join(PlannerInfo* root);

RelOptInfo* 
ues_join_rels(PlannerInfo* root, int levels_neded, List* initial_rels);