#ifndef DEBUG
    #define UNUSED __attribute__((unused))
#else
    #define UNUSED
#endif

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

/**
 * central functions in control flow
 */
/* PostgreSQL Hook */
RelOptInfo* 
ues_join_search(PlannerInfo *root, int levels_needed, List *initial_rels);

/* control flow management */
RelOptInfo* 
ues_join_rels(PlannerInfo* root, List* initial_rels);

/**
 * init and main join functions
 */
RelOptInfo*
ues_make_join_rel(PlannerInfo* root, RelOptInfo* rel1, RelOptInfo* rel2, UesJoinInfo* jinfo);

RelOptInfo*
ues_join_filters(PlannerInfo* root, RelOptInfo* jrel);

RelOptInfo* 
ues_get_start_rel_alt(PlannerInfo* root);

void
ues_get_possible_joins(PlannerInfo* root);

RelOptInfo* 
ues_next_join(PlannerInfo* root, UesJoinInfo** ujinfo);

/**
 * downstream functions for ues
 */
void
ues_switch_key_in_list(PlannerInfo* root, UesJoinKey* jkey);

void
ues_get_affected_joinkeys(PlannerInfo* root, List** keys, RelOptInfo* rel);

static UpperBound 
get_upper_bound_new(PlannerInfo* root, UesJoinKey* left_key, UesJoinKey* right_key);

/**
 * helper functions
 */
/* compare two UesJoinKey elments with list_sort() */
static int
compare_UesJoinInfo(const ListCell *a, const ListCell *b);

UesJoinType
ues_get_jointype(UesJoinKey* key1, UesJoinKey* key2);

bool
have_vars_join_relation(PlannerInfo* root, Var* var1, Var* var2);

/**
 * debug prints
 */
static void
ues_print_state(PlannerInfo *root, UesState *ues_state) UNUSED;

static void
ues_print_joins(PlannerInfo *root, UesState *ues_state) UNUSED;

