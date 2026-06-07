#ifndef NODE_H
#define NODE_H

#include "gc.h"
#include <stdint.h>

enum {
  N_INT, N_STR, N_LIST,
  N_REF, N_FN, N_CALL, N_IF, N_BLOCK, N_BIND, N_IMPORT,
};

typedef struct Node Node;

struct Node {
  int tag;
  union {
    struct { void *limbs; int len; } integer;
    char *str;
    GCList *list;
    char *ref;
    struct { GCList *params; Node *body; } fn;
    struct { Node *callee; GCList *args; } call;
    struct { Node *cond; Node *then; Node *else_; } if_;
    struct { GCList *binds; Node *expr; } block;
    struct { char *name; Node *expr; } bind;
    struct { char *filepath; GCList *names; } import;
  };
};

Node *node_new(GC *gc, int tag);

#endif
