#include "node.h"
#include "parse.h"
#include "kernel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

static void eval_expr(GC *gc, Node *env, GCStack *stack, Node *e);
static void do_bind(void *item, void *ctx);
Node *eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Node *global, GCStack *stack);

static void builtin_is_none(GC *gc, GCStack *stack) {
  int tag = ((Node *)*gc_stack_top(stack))->tag;
  gc_stack_pop(stack, 2); /* arg + callee */
  node_new(gc, gc_stack_push(gc, stack), tag == N_NONE ? N_TRUE : N_FALSE);
}

static void builtin_add_int(GC *gc, GCStack *stack, int top, Node *a, Node *b) {
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  ((Node *)*slot)->integer = a->integer + b->integer;
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void builtin_add_str(GC *gc, GCStack *stack, int top, Node *a, Node *b) {
  int alen = strlen(a->str), blen = strlen(b->str);
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_STR);
  ((Node *)*slot)->str = gc_alloc(gc, alen + blen + 1, NULL, NULL);
  a = *gc_stack_nth(stack, top - 2);
  b = *gc_stack_nth(stack, top - 1);
  memcpy(((Node *)*slot)->str, a->str, alen);
  memcpy(((Node *)*slot)->str + alen, b->str, blen + 1);
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void builtin_add_arr(GC *gc, GCStack *stack, int top, Node *a, Node *b) {
  int alen = a->arr.len, blen = b->arr.len;
  int rlen = alen + blen;
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_ARR);
  Node *r = *slot;
  if (rlen > 0) {
    r->arr.data = gc_alloc(gc, sizeof(Node *) * rlen, NULL, NULL);
    a = *gc_stack_nth(stack, top - 2);
    b = *gc_stack_nth(stack, top - 1);
    memcpy(r->arr.data, a->arr.data, sizeof(Node *) * alen);
    memcpy((char *)r->arr.data + sizeof(Node *) * alen, b->arr.data, sizeof(Node *) * blen);
  }
  r->arr.len = rlen;
  *gc_stack_nth(stack, top - 3) = r;
  gc_stack_pop(stack, 3);
}

static void builtin_add(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != b->tag) { fprintf(stderr, "add: type mismatch %d vs %d\n", a->tag, b->tag); exit(1); }
  if (a->tag == N_INT)       builtin_add_int(gc, stack, top, a, b);
  else if (a->tag == N_STR)  builtin_add_str(gc, stack, top, a, b);
  else if (a->tag == N_ARR)  builtin_add_arr(gc, stack, top, a, b);
  else { fprintf(stderr, "add: unsupported type %d\n", a->tag); exit(1); }
}

static void builtin_sub(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT || b->tag != N_INT) { fprintf(stderr, "sub: expected int\n"); exit(1); }
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  ((Node *)*slot)->integer = a->integer - b->integer;
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void builtin_mul(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT || b->tag != N_INT) { fprintf(stderr, "mul: expected int\n"); exit(1); }

  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  ((Node *)*slot)->integer = a->integer * b->integer;
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void builtin_eq(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT && a->tag != N_STR && a->tag != N_TRUE && a->tag != N_FALSE) {
    fprintf(stderr, "eq: unsupported type %d\n", a->tag); exit(1);
  }
  if (a->tag != b->tag) {
    fprintf(stderr, "eq: type mismatch %d vs %d\n", a->tag, b->tag); exit(1);
  }
  int equal = 0;
  if (a->tag == N_INT) equal = a->integer == b->integer;
  else if (a->tag == N_STR) equal = strcmp(a->str, b->str) == 0;
  else equal = 1;
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, equal ? N_TRUE : N_FALSE);
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
}

static void builtin_str(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT) { fprintf(stderr, "str: expected int\n"); exit(1); }

  char buf[21]; /* max uint64 is 20 digits */
  snprintf(buf, sizeof(buf), "%lu", (unsigned long)a->integer);
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_STR);
  ((Node *)*slot)->str = gc_strdup(gc, buf);
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
}

static void builtin_not(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  int tag = ((Node *)*gc_stack_top(stack))->tag;
  if (tag != N_TRUE && tag != N_FALSE) { fprintf(stderr, "not: expected bool\n"); exit(1); }
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, tag == N_TRUE ? N_FALSE : N_TRUE);
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
}

static void builtin_head(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR || a->arr.len == 0) { fprintf(stderr, "head: expected non-empty arr\n"); exit(1); }
  *gc_stack_nth(stack, top - 2) = ((Node **)a->arr.data)[0];
  gc_stack_pop(stack, 1);
  (void)gc;
}

static void builtin_tail(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR || a->arr.len == 0) { fprintf(stderr, "tail: expected non-empty arr\n"); exit(1); }
  int rlen = a->arr.len - 1;
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_ARR);
  Node *r = *slot;
  if (rlen > 0) {
    r->arr.data = gc_alloc(gc, sizeof(Node *) * rlen, NULL, NULL);
    a = *gc_stack_nth(stack, top - 1);
    memcpy(r->arr.data, (char *)a->arr.data + sizeof(Node *), sizeof(Node *) * rlen);
  }
  r->arr.len = rlen;
  *gc_stack_nth(stack, top - 2) = r;
  gc_stack_pop(stack, 2);
}

static void builtin_nth(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *n = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR) { fprintf(stderr, "nth: expected arr\n"); exit(1); }
  if (n->tag != N_INT) { fprintf(stderr, "nth: expected int index\n"); exit(1); }
  if (n->integer >= a->arr.len) { fprintf(stderr, "nth: index out of bounds\n"); exit(1); }
  uint64_t idx = n->integer;
  *gc_stack_nth(stack, top - 3) = ((Node **)a->arr.data)[idx];
  gc_stack_pop(stack, 2);
  (void)gc;
}

static void builtin_len(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR) { fprintf(stderr, "len: expected arr\n"); exit(1); }
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_INT);
  ((Node *)*slot)->integer = a->arr.len;
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
}

static void print_node(Node *n) {
  switch (n->tag) {
  case N_TRUE:  printf("true"); break;
  case N_FALSE: printf("false"); break;
  case N_NONE:  printf("none"); break;
  case N_STR:   printf("%s", n->str); break;
  case N_INT: printf("%lu", (unsigned long)n->integer); break;
  case N_ARR:
    printf("[");
    for (uint64_t i = 0; i < n->arr.len; i++) {
      if (i) printf(", ");
      Node *item = ((Node **)n->arr.data)[i];
      switch (item->tag) {
      case N_TRUE:  printf("true"); break;
      case N_FALSE: printf("false"); break;
      case N_NONE:  printf("none"); break;
      case N_STR:
        putchar('"');
        for (char *p = item->str; *p; p++) {
          if (*p == '\n') printf("\\n");
          else if (*p == '\t') printf("\\t");
          else if (*p == '\\') printf("\\\\");
          else if (*p == '"') printf("\\\"");
          else putchar(*p);
        }
        putchar('"');
        break;
      case N_INT:   print_node(item); break;
      case N_CLOSURE: printf("<closure>"); break;
      case N_BUILTIN: printf("<builtin>"); break;
      case N_PROOF:   printf("<proof>"); break;
      case N_ARR:     printf("<arr>"); break;
      default: assert(0 && "unreachable");
      }
    }
    printf("]");
    break;
  case N_CLOSURE: printf("<closure>"); break;
  case N_BUILTIN: printf("<builtin>"); break;
  case N_PROOF:   printf("<proof>"); break;
  default: assert(0 && "unreachable");
  }
}

static void builtin_tap(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  print_node(a);
  printf("\n");
  *gc_stack_nth(stack, top - 2) = a;
  gc_stack_pop(stack, 1);
  (void)gc;
}

/* _do_proof(left, right, rule, premises, principal, term)
   returns [true, proof] or [false, error_msg] */
static void builtin_do_proof(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *left      = *gc_stack_nth(stack, top - 6);
  Node *right     = *gc_stack_nth(stack, top - 5);
  Node *rule      = *gc_stack_nth(stack, top - 4);
  Node *premises  = *gc_stack_nth(stack, top - 3);
  Node *principal = *gc_stack_nth(stack, top - 2);
  Node *term      = *gc_stack_nth(stack, top - 1);

  Node *term_or_null = (term->tag == N_NONE) ? NULL : term;
  const char *err = kernel_check(gc, stack, left, right, rule->str, premises, principal, term_or_null);

  /* build result array [ok, value] */
  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_ARR);
  Node *result = *slot;
  result->arr.data = gc_alloc(gc, sizeof(Node *) * 2, NULL, NULL);
  result->arr.len = 2;
  Node **rd = result->arr.data;
  rd[0] = NULL; rd[1] = NULL;

  if (err) {
    node_new(gc, (void **)&rd[0], N_FALSE);
    node_new(gc, (void **)&rd[1], N_STR);
    rd[1]->str = gc_strdup(gc, err);
  } else {
    node_new(gc, (void **)&rd[0], N_TRUE);
    node_new(gc, (void **)&rd[1], N_PROOF);
    rd[1]->proof.left = left;
    rd[1]->proof.right = right;
  }

  *gc_stack_nth(stack, top - 7) = result;
  gc_stack_pop(stack, 7);
}

/* _do_qed(proof, expected, system)
   returns [true, none] or [false, error_msg] */
static void builtin_do_qed(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *proof    = *gc_stack_nth(stack, top - 3);
  Node *expected = *gc_stack_nth(stack, top - 2);
  Node *system   = *gc_stack_nth(stack, top - 1);

  const char *err = kernel_qed(gc, stack, proof, expected, system->str);

  void **slot = gc_stack_push(gc, stack);
  node_new(gc, slot, N_ARR);
  Node *result = *slot;
  result->arr.data = gc_alloc(gc, sizeof(Node *) * 2, NULL, NULL);
  result->arr.len = 2;
  Node **rd = result->arr.data;
  rd[0] = NULL; rd[1] = NULL;

  if (err) {
    node_new(gc, (void **)&rd[0], N_FALSE);
    node_new(gc, (void **)&rd[1], N_STR);
    rd[1]->str = gc_strdup(gc, err);
  } else {
    node_new(gc, (void **)&rd[0], N_TRUE);
    node_new(gc, (void **)&rd[1], N_NONE);
  }

  *gc_stack_nth(stack, top - 4) = result;
  gc_stack_pop(stack, 4);
}

static void builtin_fail(GC *gc, GCStack *stack) {
  int top = gc_stack_len(stack);
  Node *msg = *gc_stack_nth(stack, top - 1);
  fprintf(stderr, "%s\n", msg->str);
  exit(1);
  (void)gc;
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
  *s = gc_strdup(gc, "str");    set_builtin(gc, global, *s, builtin_str, 1);
  *s = gc_strdup(gc, "not");    set_builtin(gc, global, *s, builtin_not, 1);
  *s = gc_strdup(gc, "head");   set_builtin(gc, global, *s, builtin_head, 1);
  *s = gc_strdup(gc, "tail");   set_builtin(gc, global, *s, builtin_tail, 1);
  *s = gc_strdup(gc, "nth");    set_builtin(gc, global, *s, builtin_nth, 2);
  *s = gc_strdup(gc, "len");    set_builtin(gc, global, *s, builtin_len, 1);
  *s = gc_strdup(gc, "tap");        set_builtin(gc, global, *s, builtin_tap, 1);
  *s = gc_strdup(gc, "_do_proof");  set_builtin(gc, global, *s, builtin_do_proof, 6);
  *s = gc_strdup(gc, "_do_qed");    set_builtin(gc, global, *s, builtin_do_qed, 3);
  *s = gc_strdup(gc, "_fail");      set_builtin(gc, global, *s, builtin_fail, 1);
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

  a->arr.data = gc_alloc(gc, sizeof(Node *) * l, NULL, NULL);
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
