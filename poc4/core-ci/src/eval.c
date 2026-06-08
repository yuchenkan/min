#include "node.h"
#include "parse.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void eval_expr(GC *gc, Node *env, GCStack *stack, Node *e);
static void do_bind(void *item, void *ctx);
Node *eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Node *global, GCStack *stack);

static void builtin_is_none(GC *gc, GCStack *stack) {
  int tag = ((Node *)*gc_stack_top(stack))->tag;
  gc_stack_pop(stack, 2); /* arg + callee */
  node_new(gc, gc_stack_push(gc, stack), tag == N_NONE ? N_TRUE : N_FALSE);
}

static void builtin_add(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  int alen = a->integer.len, blen = b->integer.len;
  int rlen = (alen > blen ? alen : blen) + 1;

  /* compute into malloc'd buffer — no gc_alloc yet */
  uint32_t *tmp = malloc(sizeof(uint32_t) * rlen);
  uint32_t *al = a->integer.limbs, *bl = b->integer.limbs;
  uint64_t carry = 0;
  for (int i = 0; i < rlen; i++) {
    uint64_t sum = carry;
    if (i < alen) sum += al[i];
    if (i < blen) sum += bl[i];
    tmp[i] = (uint32_t)sum;
    carry = sum >> 32;
  }
  while (rlen > 0 && tmp[rlen - 1] == 0) rlen--;

  /* now allocate gc node + limbs */
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  Node *r = *slot;
  if (rlen > 0) {
    r->integer.limbs = gc_alloc(gc, sizeof(uint32_t) * rlen, NULL);
    memcpy(r->integer.limbs, tmp, sizeof(uint32_t) * rlen);
  }
  r->integer.len = rlen;
  free(tmp);

  /* overwrite callee slot (top - nparams - 1), pop args + callee */
  *gc_stack_nth(stack, top - 3) = r;
  gc_stack_pop(stack, 3);
}

static void builtin_sub(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  int alen = a->integer.len, blen = b->integer.len;
  int rlen = alen > blen ? alen : blen;
  if (rlen == 0) rlen = 1;

  uint32_t *tmp = malloc(sizeof(uint32_t) * rlen);
  uint32_t *al = a->integer.limbs, *bl = b->integer.limbs;
  int64_t borrow = 0;
  for (int i = 0; i < rlen; i++) {
    int64_t diff = borrow;
    if (i < alen) diff += al[i];
    if (i < blen) diff -= bl[i];
    if (diff < 0) { tmp[i] = (uint32_t)(diff + ((int64_t)1 << 32)); borrow = -1; }
    else { tmp[i] = (uint32_t)diff; borrow = 0; }
  }
  while (rlen > 0 && tmp[rlen - 1] == 0) rlen--;

  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  Node *r = *slot;
  if (rlen > 0) {
    r->integer.limbs = gc_alloc(gc, sizeof(uint32_t) * rlen, NULL);
    memcpy(r->integer.limbs, tmp, sizeof(uint32_t) * rlen);
  }
  r->integer.len = rlen;
  free(tmp);
  *gc_stack_nth(stack, top - 3) = r;
  gc_stack_pop(stack, 3);
}

static void builtin_mul(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  int alen = a->integer.len, blen = b->integer.len;
  if (alen == 0 || blen == 0) {
    void **slot = gc_stack_push(gc, stack);
    node_new(gc, slot, N_INT);
    *gc_stack_nth(stack, top - 3) = *slot;
    gc_stack_pop(stack, 3);
    return;
  }
  int rlen = alen + blen;
  uint32_t *tmp = calloc(rlen, sizeof(uint32_t));
  uint32_t *al = a->integer.limbs, *bl = b->integer.limbs;
  for (int i = 0; i < alen; i++) {
    uint64_t carry = 0;
    for (int j = 0; j < blen; j++) {
      uint64_t prod = (uint64_t)al[i] * bl[j] + tmp[i + j] + carry;
      tmp[i + j] = (uint32_t)prod;
      carry = prod >> 32;
    }
    tmp[i + blen] += (uint32_t)carry;
  }
  while (rlen > 0 && tmp[rlen - 1] == 0) rlen--;

  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  Node *r = *slot;
  if (rlen > 0) {
    r->integer.limbs = gc_alloc(gc, sizeof(uint32_t) * rlen, NULL);
    memcpy(r->integer.limbs, tmp, sizeof(uint32_t) * rlen);
  }
  r->integer.len = rlen;
  free(tmp);
  *gc_stack_nth(stack, top - 3) = r;
  gc_stack_pop(stack, 3);
}

static void builtin_eq(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  int equal = 0;
  if (a->tag == b->tag) {
    if (a->tag == N_INT) {
      equal = a->integer.len == b->integer.len &&
        (a->integer.len == 0 ||
         memcmp(a->integer.limbs, b->integer.limbs, a->integer.len * sizeof(uint32_t)) == 0);
    } else if (a->tag == N_STR) {
      equal = strcmp(a->str, b->str) == 0;
    } else if (a->tag == N_TRUE || a->tag == N_FALSE || a->tag == N_NONE) {
      equal = 1;
    }
  }
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, equal ? N_TRUE : N_FALSE);
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void set_builtin(GC *gc, Node *env, const char *name, void (*fn)(GC *, GCStack *), int nparams) {
  Node **slot = env_get(gc, env, name);
  node_new(gc, (void **)slot, N_BUILTIN);
  (*slot)->builtin.fn = fn;
  (*slot)->builtin.nparams = nparams;
}

void init_global(GC *gc, Node *global, void **s) {
  *s = gc_strdup(gc, "true");  node_new(gc, (void **)env_get(gc, global, *s), N_TRUE);
  *s = gc_strdup(gc, "false"); node_new(gc, (void **)env_get(gc, global, *s), N_FALSE);
  *s = gc_strdup(gc, "none");  node_new(gc, (void **)env_get(gc, global, *s), N_NONE);
  *s = gc_strdup(gc, "is_none"); set_builtin(gc, global, *s, builtin_is_none, 1);
  *s = gc_strdup(gc, "add");    set_builtin(gc, global, *s, builtin_add, 2);
  *s = gc_strdup(gc, "sub");    set_builtin(gc, global, *s, builtin_sub, 2);
  *s = gc_strdup(gc, "mul");    set_builtin(gc, global, *s, builtin_mul, 2);
  *s = gc_strdup(gc, "eq");     set_builtin(gc, global, *s, builtin_eq, 2);
  *s = NULL;
}

static void eval_each(void *item, void *ctx) {
  void **p = ctx;
  GC *gc = p[0]; Node *env = p[1]; GCStack *stack = p[2];
  eval_expr(gc, env, stack, item);
}

static void eval_list(GC *gc, Node *env, GCStack *stack, Node *e) {
  node_new(gc, gc_stack_push(gc, stack), N_ARR);
  Node *a = *gc_stack_top(stack);

  int t = gc_stack_len(stack);
  void *p[3] = { gc, env, stack };
  gc_list_each(e->list, eval_each, p);
  int l = gc_stack_len(stack) - t;

  a->arr.data = gc_alloc(gc, sizeof(Node *) * l, NULL);
  for (int i = 0; i < l; i++)
    ((Node **)a->arr.data)[i] = *gc_stack_nth(stack, t + i);
  a->arr.len = l;
  gc_stack_pop(stack, l);
}

static void eval_fn(GC *gc, Node *env, GCStack *stack, Node *e) {
  node_new(gc, gc_stack_push(gc, stack), N_CLOSURE);
  Node *c = *gc_stack_top(stack);

  c->closure.params = e->fn.params;
  c->closure.body = e->fn.body;

  env_snapshot(gc, (void **)&c->closure.env, env);
}

typedef struct BindParamContext {
  GC *gc;
  Node *env;
  GCStack *stack;
  int base;
  int nargs;
  int i;
} BindParamContext;

static void bind_param(void *item, void *ctx) {
  BindParamContext *bp = ctx;
  if (bp->i >= bp->nargs) {
    fprintf(stderr, "too few arguments\n");
    exit(1);
  }
  *env_get(bp->gc, bp->env, item) = *gc_stack_nth(bp->stack, bp->base + bp->i);
  bp->i++;
}

static void eval_call(GC *gc, Node *env, GCStack *stack, Node *e) {
  /* eval callee */
  eval_expr(gc, env, stack, e->call.callee);

  /* eval args */
  int base = gc_stack_len(stack);
  void *p[3] = { gc, env, stack };
  gc_list_each(e->call.args, eval_each, p);
  int nargs = gc_stack_len(stack) - base;

  Node *callee = *gc_stack_nth(stack, base - 1);

  if (callee->tag == N_CLOSURE) {
    /* snapshot closure env, bind params */
    env_snapshot(gc, gc_stack_push(gc, stack), callee->closure.env);
    Node *call_env = *gc_stack_top(stack);

    BindParamContext bp = { gc, call_env, stack, base, nargs, 0 };
    gc_list_each(callee->closure.params, bind_param, &bp);
    if (bp.i != nargs) {
      fprintf(stderr, "too many arguments\n");
      exit(1);
    }

    /* eval body in closure env */
    eval_expr(gc, call_env, stack, callee->closure.body);

    /* result is on top; move it to callee's slot */
    *gc_stack_nth(stack, base - 1) = *gc_stack_top(stack);
    gc_stack_pop(stack, gc_stack_len(stack) - base);
  } else if (callee->tag == N_BUILTIN) {
    if (nargs != callee->builtin.nparams) {
      fprintf(stderr, "builtin: expected %d args, got %d\n", callee->builtin.nparams, nargs);
      exit(1);
    }
    callee->builtin.fn(gc, stack);
  } else {
    fprintf(stderr, "not callable: tag=%d\n", callee->tag);
    exit(1);
  }
}

static void eval_expr(GC *gc, Node *env, GCStack *stack, Node *e) {
  if (e->tag == N_INT || e->tag == N_STR) {
    *gc_stack_push(gc, stack) = e;
  }
  else if (e->tag == N_LIST)
    eval_list(gc, env, stack, e);
  else if (e->tag == N_REF) {
    Node **n = env_find(env, e->ref);
    if (!n) {
      fprintf(stderr, "undefined: %s\n", e->ref);
      exit(1);
    }
    *gc_stack_push(gc, stack) = *n;
  }
  else if (e->tag == N_FN)
    eval_fn(gc, env, stack, e);
  else if (e->tag == N_CALL)
    eval_call(gc, env, stack, e);
  else if (e->tag == N_BLOCK) {
    int base = gc_stack_len(stack);
    env_snapshot(gc, gc_stack_push(gc, stack), env);
    Node *block_env = *gc_stack_top(stack);

    void *bc[3] = { gc, block_env, stack };
    gc_list_each(e->block.binds, do_bind, bc);

    eval_expr(gc, block_env, stack, e->block.expr);

    *gc_stack_nth(stack, base) = *gc_stack_top(stack);
    gc_stack_pop(stack, gc_stack_len(stack) - base - 1);
  }
  else if (e->tag == N_IF) {
    eval_expr(gc, env, stack, e->if_.cond);
    Node *cond = *gc_stack_top(stack);
    int tag = cond->tag;
    gc_stack_pop(stack, 1);
    if (tag == N_TRUE)
      eval_expr(gc, env, stack, e->if_.then);
    else if (tag == N_FALSE)
      eval_expr(gc, env, stack, e->if_.else_);
    else {
      fprintf(stderr, "if: condition must be true or false\n");
      exit(1);
    }
  }
}

static void import_bind(void *item, void *ctx) {
  char **names = item;
  void **p = ctx;
  GC *gc = p[0]; Node *env = p[1]; Node *from = p[2];

  Node **v = env_find(from, names[0]);
  if (!v) {
    fprintf(stderr, "import: undefined: %s\n", names[0]);
    exit(1);
  }

  const char *alias = names[1] ? names[1] : names[0];
  *env_get(gc, env, alias) = *v;
}

static void do_import(void *item, void *ctx) {
  Node *n = item;
  void **p = ctx;
  GC *gc = p[0]; GCMap *modules = p[1]; GCMap *sources = p[2]; Node *env = p[3]; GCStack *stack = p[4];

  Node *from = eval(gc, modules, sources, n->import.filepath, env, stack);

  void *ibc[3] = { gc, env, from };
  gc_list_each(n->import.names, import_bind, ibc);
}

static void do_bind(void *item, void *ctx) {
  Node *n = item;
  void **p = ctx;
  GC *gc = p[0]; Node *env = p[1]; GCStack *stack = p[2];

  eval_expr(gc, env, stack, n->bind.expr);
  *env_get(gc, env, n->bind.name) = *gc_stack_top(stack);
  gc_stack_pop(stack, 1);
}

Node *eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Node *global, GCStack *stack) {
  void **slot = gc_map_get(gc, modules, filepath);
  if (*slot) return *slot;

  env_snapshot(gc, slot, global);

  Source *s = *gc_map_find(sources, filepath);

  void *ic[5] = { gc, modules, sources, *slot, stack };
  gc_list_each(s->imports, do_import, ic);

  void *bc[3] = { gc, *slot, stack };
  gc_list_each(s->binds, do_bind, bc);

  gc_map_delete(sources, filepath);
  return *slot;
}
