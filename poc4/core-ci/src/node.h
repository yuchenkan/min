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
  N_ARR, N_CLOSURE, N_TRUE, N_FALSE, N_NONE, N_BUILTIN, N_PROOF
};

typedef struct Intern Intern;
typedef struct Env Env;
typedef struct Node Node;

/* Env: a small environment frame. Most frames (call args, captures) hold only
   a few bindings, so the first ENV_INLINE are stored inline — no GCMap alloc.
   Bindings beyond that spill into `overflow` (e.g. large proof blocks). Keys
   are interned strings, compared by pointer. */
#define ENV_INLINE 4
struct Env {
  Env *parent;
  GCMap *overflow;            /* NULL until > ENV_INLINE bindings */
  int n;                      /* # inline bindings used (0..ENV_INLINE) */
  const char *keys[ENV_INLINE];
  Node *vals[ENV_INLINE];
};

struct Node {
  int tag;
  const char *file;
  int line, col;
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
    struct { GCList *params; Node *body; Env *env; GCCallCache *cache; } closure;
    struct { int (*fn)(GC *gc, GCStack *stack, const char **tags, Intern *it); int nparams; GCCallCache *cache; void *ctx; } builtin;
    struct { Node *left; Node *right; } proof; /* sequent: left=N_ARR, right=N_ARR */
  };
};

typedef struct Module {
  Env *env;
  int64_t mtime;
  GCList *imports;
} Module;

static inline const char *type_name(int tag) {
  static const char *names[] = {
    [N_INT]="int", [N_STR]="str", [N_LIST]="list", [N_REF]="ref",
    [N_FN]="fn", [N_CALL]="call", [N_IF]="if", [N_BLOCK]="block",
    [N_BIND]="bind", [N_IMPORT]="import", [N_ARR]="arr",
    [N_CLOSURE]="fn", [N_TRUE]="true", [N_FALSE]="false",
    [N_NONE]="none", [N_BUILTIN]="fn", [N_PROOF]="proof"
  };
  if (tag >= 0 && tag <= N_PROOF) return names[tag];
  return "unknown";
}

void node_trace(void *data);
void module_trace(void *data);
void node_new(GC *gc, void **slot, int tag);
void env_new(GC *gc, void **slot);
Node **env_get(GC *gc, Env *e, const char *name);
Node **env_find(Env *e, const char *name);
int env_each(Env *e, GCMapFn fn, void *ctx);

#endif
