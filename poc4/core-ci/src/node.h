#ifndef NODE_H
#define NODE_H

#include "gc.h"
#include <stdint.h>

enum {
  /* shared */
  N_INT, N_STR,
  /* AST */
  N_LIST, N_REF, N_FN, N_CALL, N_IF, N_BLOCK, N_BIND, N_IMPORT,
  /* runtime */
  N_ARR, N_ENV, N_CLOSURE, N_TRUE, N_FALSE, N_NONE, N_BUILTIN, N_PROOF
};

typedef struct Intern Intern;
typedef struct Node Node;

struct Node {
  int tag;
  union {
    uint64_t integer;
    char *str;
    GCList *list;
    char *ref;
    struct { GCList *params; Node *body; } fn;
    struct { Node *callee; GCList *args; } call;
    struct { Node *cond; Node *then; Node *else_; } if_;
    struct { GCList *binds; Node *expr; } block;
    struct { char *name; Node *expr; } bind;
    struct { char *filepath; GCList *names; } import;
    /* runtime */
    struct { void *data; uint64_t len; } arr;
    GCMap *env;
    struct { GCList *params; Node *body; Node *env; GCNMap *cache; int ncache; } closure;
    struct { void (*fn)(GC *gc, GCStack *stack, const char **tags, Intern *it); int nparams; GCNMap *cache; int ncache; void *ctx; } builtin;
    struct { Node *left; Node *right; } proof; /* sequent: left=N_ARR, right=N_ARR */
  };
};

void node_trace(void *data);
void node_new(GC *gc, void **slot, int tag);
Node **env_get(GC *gc, Node *env, const char *name);
Node **env_find(Node *env, const char *name);
void env_snapshot(GC *gc, void **slot, Node *env);

#endif
