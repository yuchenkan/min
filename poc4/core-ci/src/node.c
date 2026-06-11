#include "node.h"
#include <assert.h>
#include <string.h>

void node_trace(void *data) {
  Node *n = data;
  switch (n->tag) {
  case N_INT: break;
  case N_STR: gc_mark(n->str); break;
  case N_LIST: gc_mark(n->list); break;
  case N_REF: gc_mark(n->ref); break;
  case N_FN:
    gc_mark(n->fn.params);
    gc_mark(n->fn.body);
    break;
  case N_CALL:
    gc_mark(n->call.callee);
    gc_mark(n->call.args);
    break;
  case N_IF:
    gc_mark(n->if_.cond);
    gc_mark(n->if_.then);
    gc_mark(n->if_.else_);
    break;
  case N_BLOCK:
    gc_mark(n->block.binds);
    gc_mark(n->block.expr);
    break;
  case N_BIND:
    gc_mark(n->bind.name);
    gc_mark(n->bind.expr);
    break;
  case N_IMPORT:
    gc_mark(n->import.filepath);
    gc_mark(n->import.names);
    break;
  case N_ARR:
    gc_mark(n->arr.data);
    for (uint64_t i = 0; i < n->arr.len; i++)
      gc_mark(((Node **)n->arr.data)[i]);
    break;
  case N_ENV:
    gc_mark(n->env);
    break;
  case N_CLOSURE:
    gc_mark(n->closure.params);
    gc_mark(n->closure.body);
    gc_mark(n->closure.env);
    gc_mark(n->closure.cache);
    break;
  case N_BUILTIN:
    gc_mark(n->builtin.cache);
    gc_mark(n->builtin.ctx);
    break;
  case N_PROOF:
    gc_mark(n->proof.left);
    gc_mark(n->proof.right);
    break;
  }
}

void node_new(GC *gc, void **slot, int tag) {
  assert(tag != N_INT && tag != N_STR && tag != N_ARR && tag != N_TRUE && tag != N_FALSE && tag != N_NONE);
  Node *n = gc_alloc(gc, sizeof(Node), node_trace, NULL, NULL);
  memset(n, 0, sizeof(Node));
  n->tag = tag;
  *slot = n;
  if (tag == N_ENV)
    n->env = gc_map_new(gc);
}

Node **env_get(GC *gc, Node *e, const char *name) {
  return (Node **)gc_map_get(gc, e->env, name);
}

Node **env_find(Node *e, const char *name) {
  return (Node **)gc_map_find(e->env, name);
}

void env_snapshot(GC *gc, void **slot, Node *e) {
  Node *n = gc_alloc(gc, sizeof(Node), node_trace, NULL, NULL);
  memset(n, 0, sizeof(Node));
  n->tag = N_ENV;
  *slot = n;
  gc_map_copy(gc, (void **)&n->env, e->env);
}
