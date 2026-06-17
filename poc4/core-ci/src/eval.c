#include "node.h"
#include "parse.h"
#include "kernel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

static int eval_expr(GC *gc, Env *env, GCStack *stack, const char **tags, Intern *it, Node *e);
static int do_bind(void *item, void *ctx);
int eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Env *global, GCStack *stack, const char **tags, Intern *it, Env **out);

static void frame(Node *e, const char *kind) {
  if (e->file)
    fprintf(stderr, "  at %s:%d:%d (%s)\n", e->file, e->line, e->col, kind);
}

static int builtin_is_none(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int tag = ((Node *)*gc_stack_top(stack))->tag;
  gc_stack_pop(stack, 2);
  *gc_stack_push(gc, stack) = tag == N_NONE ? intern_true(it) : intern_false(it);
  return 0;
}

/* value-type predicates: \x -> bool */
#define DEF_IS(name, cond) \
  static int builtin_##name(GC *gc, GCStack *stack, const char **tags, Intern *it) { \
    (void)tags; \
    int tag = ((Node *)*gc_stack_top(stack))->tag; \
    gc_stack_pop(stack, 2); \
    *gc_stack_push(gc, stack) = (cond) ? intern_true(it) : intern_false(it); \
    return 0; \
  }
DEF_IS(is_bool, tag == N_TRUE || tag == N_FALSE)
DEF_IS(is_int, tag == N_INT)
DEF_IS(is_str, tag == N_STR)
DEF_IS(is_arr, tag == N_ARR)
DEF_IS(is_fn, tag == N_CLOSURE || tag == N_BUILTIN)
DEF_IS(is_proof, tag == N_PROOF)
#undef DEF_IS

static int builtin_add(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != b->tag) { fprintf(stderr, "add: type mismatch %s vs %s\n", type_name(a->tag), type_name(b->tag)); return 1; }
  if (a->tag == N_INT) {
    void **slot = gc_stack_push(gc, stack);
    *slot = intern_int(it, a->integer + b->integer);
    *gc_stack_nth(stack, top - 3) = *slot;
    gc_stack_pop(stack, 3);
  } else if (a->tag == N_STR) {
    int alen = strlen(a->str), blen = strlen(b->str);
    char *buf = malloc(alen + blen + 1);
    memcpy(buf, a->str, alen);
    memcpy(buf + alen, b->str, blen + 1);
    void **slot = gc_stack_push(gc, stack);
    *slot = (void *)intern(it, buf);
    free(buf);
    *slot = intern_str(it, (const char *)*slot);
    *gc_stack_nth(stack, top - 3) = *slot;
    gc_stack_pop(stack, 3);
  } else if (a->tag == N_ARR) {
    int alen = a->arr.len, blen = b->arr.len;
    int rlen = alen + blen;
    Node **tmp = rlen ? malloc(sizeof(Node *) * rlen) : NULL;
    if (alen) memcpy(tmp, a->arr.data, sizeof(Node *) * alen);
    if (blen) memcpy(tmp + alen, b->arr.data, sizeof(Node *) * blen);
    void **slot = gc_stack_push(gc, stack);
    intern_arr(it, tmp, rlen, slot);
    free(tmp);
    *gc_stack_nth(stack, top - 3) = *slot;
    gc_stack_pop(stack, 3);
  } else {
    fprintf(stderr, "add: unsupported type %s\n", type_name(a->tag)); return 1;
  }
  return 0;
}

static int builtin_sub(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT || b->tag != N_INT) { fprintf(stderr, "sub: expected int\n"); return 1; }
  void **slot = gc_stack_push(gc, stack);
  *slot = intern_int(it, a->integer - b->integer);
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
  return 0;
}

static int builtin_mul(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT || b->tag != N_INT) { fprintf(stderr, "mul: expected int\n"); return 1; }
  void **slot = gc_stack_push(gc, stack);
  *slot = intern_int(it, a->integer * b->integer);
  *gc_stack_nth(stack, top - 3) = *slot;
  gc_stack_pop(stack, 3);
  return 0;
}

static int builtin_eqv(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags; (void)it;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *b = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_INT && a->tag != N_STR && a->tag != N_TRUE && a->tag != N_FALSE) {
    fprintf(stderr, "eqv: unsupported type %s\n", type_name(a->tag)); return 1;
  }
  if (a->tag != b->tag) {
    fprintf(stderr, "eqv: type mismatch %s vs %s\n", type_name(a->tag), type_name(b->tag)); return 1;
  }
  int equal = 0;
  if (a->tag == N_INT) equal = a->integer == b->integer;
  else if (a->tag == N_STR) equal = a->str == b->str;
  else equal = 1;
  *gc_stack_nth(stack, top - 3) = equal ? intern_true(it) : intern_false(it);
  gc_stack_pop(stack, 2);
  return 0;
  (void)gc;
}

typedef struct { char *buf; size_t len, cap; } Sbuf;

static void sb_putc(Sbuf *s, char c) {
  if (s->len + 1 > s->cap) {
    s->cap = s->cap ? s->cap * 2 : 64;
    s->buf = realloc(s->buf, s->cap);
  }
  s->buf[s->len++] = c;
}

static void sb_puts(Sbuf *s, const char *str) {
  for (; *str; str++) sb_putc(s, *str);
}

static void node_str(Sbuf *s, Node *n) {
  switch (n->tag) {
  case N_TRUE:  sb_puts(s, "true"); break;
  case N_FALSE: sb_puts(s, "false"); break;
  case N_NONE:  sb_puts(s, "none"); break;
  case N_STR:
    sb_putc(s, '"');
    for (char *p = n->str; *p; p++) {
      if (*p == '\\') sb_puts(s, "\\\\");
      else if (*p == '"') sb_puts(s, "\\\"");
      else sb_putc(s, *p);
    }
    sb_putc(s, '"');
    break;
  case N_INT: {
    char b[21];
    snprintf(b, sizeof(b), "%lu", (unsigned long)n->integer);
    sb_puts(s, b);
    break;
  }
  case N_ARR:
    sb_putc(s, '[');
    for (uint64_t i = 0; i < n->arr.len; i++) {
      if (i) sb_puts(s, ", ");
      Node *item = ((Node **)n->arr.data)[i];
      switch (item->tag) {
      case N_TRUE:  sb_puts(s, "true"); break;
      case N_FALSE: sb_puts(s, "false"); break;
      case N_NONE:  sb_puts(s, "none"); break;
      case N_STR:   case N_INT: node_str(s, item); break;
      case N_CLOSURE: sb_puts(s, "<closure>"); break;
      case N_BUILTIN: sb_puts(s, "<builtin>"); break;
      case N_PROOF:   sb_puts(s, "<proof>"); break;
      case N_ARR:     sb_puts(s, "<arr>"); break;
      default: assert(0 && "unreachable");
      }
    }
    sb_putc(s, ']');
    break;
  case N_CLOSURE: sb_puts(s, "<closure>"); break;
  case N_BUILTIN: sb_puts(s, "<builtin>"); break;
  case N_PROOF:   sb_puts(s, "<proof>"); break;
  default: assert(0 && "unreachable");
  }
}

static int builtin_str(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  Sbuf s = {0};
  node_str(&s, a);
  sb_putc(&s, '\0');
  void **slot = gc_stack_push(gc, stack);
  *slot = (void *)intern(it, s.buf);
  free(s.buf);
  *slot = intern_str(it, (const char *)*slot);
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
  return 0;
}

static int builtin_not(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags; (void)gc;
  int top = gc_stack_len(stack);
  int tag = ((Node *)*gc_stack_top(stack))->tag;
  if (tag != N_TRUE && tag != N_FALSE) { fprintf(stderr, "not: expected bool\n"); return 1; }
  *gc_stack_nth(stack, top - 2) = tag == N_TRUE ? intern_false(it) : intern_true(it);
  gc_stack_pop(stack, 1);
  return 0;
}

static int builtin_head(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags; (void)it; (void)gc;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR || a->arr.len == 0) { fprintf(stderr, "head: expected non-empty arr\n"); return 1; }
  *gc_stack_nth(stack, top - 2) = ((Node **)a->arr.data)[0];
  gc_stack_pop(stack, 1);
  return 0;
}

static int builtin_tail(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  if (a->tag != N_ARR || a->arr.len == 0) { fprintf(stderr, "tail: expected non-empty arr\n"); return 1; }
  int rlen = a->arr.len - 1;
  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, (Node **)a->arr.data + 1, rlen, slot);
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
  return 0;
}

static int builtin_nth(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 2);
  Node *n = *gc_stack_nth(stack, top - 1);
  if (n->tag != N_INT) { fprintf(stderr, "nth: expected int index\n"); return 1; }
  if (a->tag == N_ARR) {
    if (n->integer >= a->arr.len) { fprintf(stderr, "nth: index out of bounds\n"); return 1; }
    *gc_stack_nth(stack, top - 3) = ((Node **)a->arr.data)[n->integer];
    gc_stack_pop(stack, 2);
    return 0;
  } else if (a->tag == N_STR) {
    uint64_t slen = strlen(a->str);
    if (n->integer >= slen) { fprintf(stderr, "nth: string index out of bounds\n"); return 1; }
    char buf[2] = { a->str[n->integer], '\0' };
    void **slot = gc_stack_push(gc, stack);
    *slot = (void *)intern(it, buf);
    *slot = intern_str(it, (const char *)*slot);
    *gc_stack_nth(stack, top - 3) = *slot;
    gc_stack_pop(stack, 3);
    return 0;
  }
  fprintf(stderr, "nth: expected arr or str\n"); return 1;
}

static int builtin_len(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  uint64_t result;
  if (a->tag == N_ARR) result = a->arr.len;
  else if (a->tag == N_STR) result = strlen(a->str);
  else { fprintf(stderr, "len: expected arr or str\n"); return 1; }
  void **slot = gc_stack_push(gc, stack);
  *slot = intern_int(it, result);
  *gc_stack_nth(stack, top - 2) = *slot;
  gc_stack_pop(stack, 2);
  return 0;
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
          if (*p == '\\') printf("\\\\");
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

static int builtin_tap(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags; (void)it; (void)gc;
  int top = gc_stack_len(stack);
  Node *a = *gc_stack_nth(stack, top - 1);
  print_node(a);
  printf("\n");
  *gc_stack_nth(stack, top - 2) = a;
  gc_stack_pop(stack, 1);
  return 0;
}

static int builtin_do_proof(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  int top = gc_stack_len(stack);
  Node *left      = *gc_stack_nth(stack, top - 6);
  Node *right     = *gc_stack_nth(stack, top - 5);
  Node *rule      = *gc_stack_nth(stack, top - 4);
  Node *premises  = *gc_stack_nth(stack, top - 3);
  Node *principal = *gc_stack_nth(stack, top - 2);
  Node *term      = *gc_stack_nth(stack, top - 1);

  Node *term_or_null = (term->tag == N_NONE) ? NULL : term;
  const char *err = kernel_check(gc, stack, tags, it, left, right, rule->str, premises, principal, term_or_null);

  void **slot = gc_stack_push(gc, stack);
  if (err) {
    void **sslot = gc_stack_push(gc, stack);
    *sslot = (void *)intern(it, err);
    void **nslot = gc_stack_push(gc, stack);
    *nslot = intern_str(it, (const char *)*sslot);
    Node *elems[2] = { intern_false(it), *nslot };
    intern_arr(it, elems, 2, slot);
    gc_stack_pop(stack, 2);
  } else {
    void **pslot = gc_stack_push(gc, stack);
    node_new(gc, pslot, N_PROOF);
    ((Node *)*pslot)->proof.left = left;
    ((Node *)*pslot)->proof.right = right;
    Node *elems[2] = { intern_true(it), *pslot };
    intern_arr(it, elems, 2, slot);
    gc_stack_pop(stack, 1);
  }

  *gc_stack_nth(stack, top - 7) = *slot;
  gc_stack_pop(stack, 7);
  return 0;
}

static int builtin_do_qed(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  int top = gc_stack_len(stack);
  Node *proof    = *gc_stack_nth(stack, top - 3);
  Node *expected = *gc_stack_nth(stack, top - 2);
  Node *system   = *gc_stack_nth(stack, top - 1);

  Node *self = *gc_stack_nth(stack, top - 4);
  KernelData *kd = self->builtin.ctx;
  const char *err = kernel_qed(gc, stack, tags, it, kd, proof, expected, system->str);

  void **slot = gc_stack_push(gc, stack);
  if (err) {
    void **sslot = gc_stack_push(gc, stack);
    *sslot = (void *)intern(it, err);
    void **nslot = gc_stack_push(gc, stack);
    *nslot = intern_str(it, (const char *)*sslot);
    Node *elems[2] = { intern_false(it), *nslot };
    intern_arr(it, elems, 2, slot);
    gc_stack_pop(stack, 2);
  } else {
    Node *elems[2] = { intern_true(it), intern_none(it) };
    intern_arr(it, elems, 2, slot);
  }

  *gc_stack_nth(stack, top - 4) = *slot;
  gc_stack_pop(stack, 4);
  return 0;
}

static int builtin_fail(GC *gc, GCStack *stack, const char **tags, Intern *it) {
  (void)tags; (void)it; (void)gc;
  int top = gc_stack_len(stack);
  Node *msg = *gc_stack_nth(stack, top - 1);
  fprintf(stderr, "%s\n", msg->str);
  return 1;
}

static void set_builtin(GC *gc, Env *env, const char *name, int (*fn)(GC *, GCStack *, const char **, Intern *), int nparams) {
  Node **slot = env_get(gc, env, name);
  node_new(gc, (void **)slot, N_BUILTIN);
  (*slot)->builtin.fn = fn;
  (*slot)->builtin.nparams = nparams;
}

void init_global(GC *gc, GCStack *stack, const char **tags, Intern *it, Env *global, void **s) {
  *s = (void *)intern(it, "true");  *env_get(gc, global, *s) = intern_true(it);
  *s = (void *)intern(it, "false"); *env_get(gc, global, *s) = intern_false(it);
  *s = (void *)intern(it, "none");  *env_get(gc, global, *s) = intern_none(it);
  *s = (void *)intern(it, "is_none"); set_builtin(gc, global, *s, builtin_is_none, 1);
  *s = (void *)intern(it, "is_bool"); set_builtin(gc, global, *s, builtin_is_bool, 1);
  *s = (void *)intern(it, "is_int");  set_builtin(gc, global, *s, builtin_is_int, 1);
  *s = (void *)intern(it, "is_str");  set_builtin(gc, global, *s, builtin_is_str, 1);
  *s = (void *)intern(it, "is_arr");  set_builtin(gc, global, *s, builtin_is_arr, 1);
  *s = (void *)intern(it, "is_fn");   set_builtin(gc, global, *s, builtin_is_fn, 1);
  *s = (void *)intern(it, "is_proof"); set_builtin(gc, global, *s, builtin_is_proof, 1);
  *s = (void *)intern(it, "add");    set_builtin(gc, global, *s, builtin_add, 2);
  *s = (void *)intern(it, "sub");    set_builtin(gc, global, *s, builtin_sub, 2);
  *s = (void *)intern(it, "mul");    set_builtin(gc, global, *s, builtin_mul, 2);
  *s = (void *)intern(it, "eqv");    set_builtin(gc, global, *s, builtin_eqv, 2);
  *s = (void *)intern(it, "str");    set_builtin(gc, global, *s, builtin_str, 1);
  *s = (void *)intern(it, "not");    set_builtin(gc, global, *s, builtin_not, 1);
  *s = (void *)intern(it, "head");   set_builtin(gc, global, *s, builtin_head, 1);
  *s = (void *)intern(it, "tail");   set_builtin(gc, global, *s, builtin_tail, 1);
  *s = (void *)intern(it, "nth");    set_builtin(gc, global, *s, builtin_nth, 2);
  *s = (void *)intern(it, "len");    set_builtin(gc, global, *s, builtin_len, 1);
  *s = (void *)intern(it, "tap");        set_builtin(gc, global, *s, builtin_tap, 1);
  *s = (void *)intern(it, "_do_proof");  set_builtin(gc, global, *s, builtin_do_proof, 6);
  *s = (void *)intern(it, "_do_qed");    set_builtin(gc, global, *s, builtin_do_qed, 3);
  Node *qed_node = *env_find(global, *s);
  kernel_precompute(gc, stack, tags, it, &qed_node->builtin.ctx);
  *s = (void *)intern(it, "_fail");      set_builtin(gc, global, *s, builtin_fail, 1);
  *s = NULL;
}

/* ---- free variable capture ---- */

static void capture_free(GC *gc, Env *src, Env *dst, GCStack *stack, Node *e);

typedef struct { GC *gc; Env *src; Env *dst; GCStack *stack; } CaptureCtx;

static int capture_list_cb(void *item, void *ctx) {
  CaptureCtx *c = ctx;
  capture_free(c->gc, c->src, c->dst, c->stack, item);
  return 0;
}

static int shadow_param_cb(void *item, void *ctx) {
  void **p = ctx;
  *env_get(p[0], p[1], item) = NULL;
  return 0;
}

static int capture_block_cb(void *item, void *ctx) {
  CaptureCtx *c = ctx;
  Node *bind = item;
  capture_free(c->gc, c->src, c->dst, c->stack, bind->bind.expr);
  *env_get(c->gc, c->src, bind->bind.name) = NULL;
  return 0;
}

static void capture_free(GC *gc, Env *src, Env *dst, GCStack *stack, Node *e) {
  switch (e->tag) {
  case N_INT: case N_STR: break;
  case N_REF: {
    if (env_find(dst, e->ref)) break;
    Node **v = env_find(src, e->ref);
    if (v && *v)
      *env_get(gc, dst, e->ref) = *v;
    break;
  }
  case N_LIST: {
    CaptureCtx ctx = { gc, src, dst, stack };
    gc_list_each(e->list, capture_list_cb, &ctx);
    break;
  }
  case N_FN: {
    env_new(gc, gc_stack_push(gc, stack));
    Env *shadow = *gc_stack_top(stack);
    shadow->parent = src;
    void *sp[2] = { gc, shadow };
    gc_list_each(e->fn.params, shadow_param_cb, sp);
    capture_free(gc, shadow, dst, stack, e->fn.body);
    gc_stack_pop(stack, 1);
    break;
  }
  case N_CALL: {
    capture_free(gc, src, dst, stack, e->call.callee);
    CaptureCtx ctx = { gc, src, dst, stack };
    gc_list_each(e->call.args, capture_list_cb, &ctx);
    break;
  }
  case N_IF:
    capture_free(gc, src, dst, stack, e->if_.cond);
    capture_free(gc, src, dst, stack, e->if_.then);
    capture_free(gc, src, dst, stack, e->if_.else_);
    break;
  case N_BLOCK: {
    env_new(gc, gc_stack_push(gc, stack));
    Env *shadow = *gc_stack_top(stack);
    shadow->parent = src;
    CaptureCtx ctx = { gc, shadow, dst, stack };
    gc_list_each(e->block.binds, capture_block_cb, &ctx);
    capture_free(gc, shadow, dst, stack, e->block.expr);
    gc_stack_pop(stack, 1);
    break;
  }
  default: break;
  }
}

/* ---- evaluation ---- */

static int eval_each(void *item, void *ctx) {
  void **p = ctx;
  GC *gc = p[0]; Env *env = p[1]; GCStack *stack = p[2]; const char **tags = p[3]; Intern *it = p[4];
  return eval_expr(gc, env, stack, tags, it, item);
}

static int eval_list(GC *gc, Env *env, GCStack *stack, const char **tags, Intern *it, Node *e) {
  int base = gc_stack_len(stack);
  void *p[5] = { gc, env, stack, (void *)tags, it };
  int err = gc_list_each(e->list, eval_each, p);
  if (err) return err;
  int l = gc_stack_len(stack) - base;

  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, (Node **)gc_stack_nth(stack, base), l, slot);
  *gc_stack_nth(stack, base) = *slot;
  gc_stack_pop(stack, l);
  return 0;
}

static void eval_fn(GC *gc, Env *env, GCStack *stack, Node *e) {
  node_new(gc, gc_stack_push(gc, stack), N_CLOSURE);
  Node *c = *gc_stack_top(stack);
  c->closure.params = e->fn.params;
  c->closure.body = e->fn.body;

  env_new(gc, (void **)&c->closure.env);
  env_new(gc, gc_stack_push(gc, stack));
  Env *shadow = *gc_stack_top(stack);
  shadow->parent = env;
  void *sp[2] = { gc, shadow };
  gc_list_each(e->fn.params, shadow_param_cb, sp);
  capture_free(gc, shadow, c->closure.env, stack, e->fn.body);
  gc_stack_pop(stack, 1);
}

typedef struct BindParamContext {
  GC *gc;
  Env *env;
  GCStack *stack;
  int base;
  int nargs;
  int i;
} BindParamContext;

static int bind_param(void *item, void *ctx) {
  BindParamContext *bp = ctx;
  if (bp->i >= bp->nargs) {
    fprintf(stderr, "too few arguments\n");
    return 1;
  }
  *env_get(bp->gc, bp->env, item) = *gc_stack_nth(bp->stack, bp->base + bp->i);
  bp->i++;
  return 0;
}

static int eval_call(GC *gc, Env *env, GCStack *stack, const char **tags, Intern *it, Node *e) {
  int err = eval_expr(gc, env, stack, tags, it, e->call.callee);
  if (err) return err;

  int base = gc_stack_len(stack);
  void *p[5] = { gc, env, stack, (void *)tags, it };
  err = gc_list_each(e->call.args, eval_each, p);
  if (err) return err;
  int nargs = gc_stack_len(stack) - base;

  Node *callee = *gc_stack_nth(stack, base - 1);

  if (callee->tag == N_CLOSURE) {
    if (!callee->closure.cache)
      callee->closure.cache = gc_cc_new(gc, nargs);

    void **hit = gc_cc_find(callee->closure.cache, gc_stack_nth(stack, base));
    if (hit) {
      *gc_stack_nth(stack, base - 1) = *hit;
      gc_stack_pop(stack, nargs);
      return 0;
    }

    env_new(gc, gc_stack_push(gc, stack));
    Env *call_env = *gc_stack_top(stack);
    call_env->parent = callee->closure.env;

    BindParamContext bp = { gc, call_env, stack, base, nargs, 0 };
    err = gc_list_each(callee->closure.params, bind_param, &bp);
    if (err) { frame(e, "call"); return err; }
    if (bp.i != nargs) {
      fprintf(stderr, "too many arguments\n");
      frame(e, "call");
      return 1;
    }

    err = eval_expr(gc, call_env, stack, tags, it, callee->closure.body);
    if (err) { frame(e, "call"); return err; }

    Node *result = *gc_stack_top(stack);
    callee = *gc_stack_nth(stack, base - 1);
    if (gc_cc_count(callee->closure.cache) > 1024) {
      gc_cc_clear(callee->closure.cache);
    }
    *gc_cc_get(gc, callee->closure.cache, gc_stack_nth(stack, base)) = result;

    *gc_stack_nth(stack, base - 1) = result;
    gc_stack_pop(stack, gc_stack_len(stack) - base);
  } else if (callee->tag == N_BUILTIN) {
    if (nargs != callee->builtin.nparams) {
      fprintf(stderr, "builtin: expected %d args, got %d\n", callee->builtin.nparams, nargs);
      frame(e, "call");
      return 1;
    }
    err = callee->builtin.fn(gc, stack, tags, it);
    if (err) { frame(e, "call"); return err; }
  } else {
    fprintf(stderr, "not callable: got %s (expected function)\n", type_name(callee->tag));
    frame(e, "call");
    return 1;
  }
  return 0;
}

static int eval_expr(GC *gc, Env *env, GCStack *stack, const char **tags, Intern *it, Node *e) {
  if (e->tag == N_INT || e->tag == N_STR) {
    *gc_stack_push(gc, stack) = e;
  }
  else if (e->tag == N_LIST) {
    int err = eval_list(gc, env, stack, tags, it, e);
    if (err) return err;
  }
  else if (e->tag == N_REF) {
    Node **n = env_find(env, e->ref);
    if (!n) {
      fprintf(stderr, "undefined: %s\n", e->ref);
      frame(e, "ref");
      return 1;
    }
    *gc_stack_push(gc, stack) = *n;
  }
  else if (e->tag == N_FN)
    eval_fn(gc, env, stack, e);
  else if (e->tag == N_CALL) {
    int err = eval_call(gc, env, stack, tags, it, e);
    if (err) return err;
  }
  else if (e->tag == N_BLOCK) {
    int base = gc_stack_len(stack);
    env_new(gc, gc_stack_push(gc, stack));
    Env *block_env = *gc_stack_top(stack);
    block_env->parent = env;

    void *bc[5] = { gc, block_env, stack, (void *)tags, it };
    int err = gc_list_each(e->block.binds, do_bind, bc);
    if (err) return err;

    err = eval_expr(gc, block_env, stack, tags, it, e->block.expr);
    if (err) return err;

    *gc_stack_nth(stack, base) = *gc_stack_top(stack);
    gc_stack_pop(stack, gc_stack_len(stack) - base - 1);
  }
  else if (e->tag == N_IF) {
    int err = eval_expr(gc, env, stack, tags, it, e->if_.cond);
    if (err) return err;
    Node *cond = *gc_stack_top(stack);
    int tag = cond->tag;
    gc_stack_pop(stack, 1);
    if (tag == N_TRUE) {
      err = eval_expr(gc, env, stack, tags, it, e->if_.then);
      if (err) return err;
    } else if (tag == N_FALSE) {
      err = eval_expr(gc, env, stack, tags, it, e->if_.else_);
      if (err) return err;
    } else {
      fprintf(stderr, "if: condition must be true or false\n");
      return 1;
    }
  }
  return 0;
}

static int import_bind(void *item, void *ctx) {
  char **names = item;
  void **p = ctx;
  GC *gc = p[0]; Env *env = p[1]; Env *from = p[2];

  if (names[0][0] == '_') {
    fprintf(stderr, "import: private name: %s\n", names[0]);
    return 1;
  }

  Node **v = env_find(from, names[0]);
  if (!v) {
    fprintf(stderr, "import: undefined: %s\n", names[0]);
    return 1;
  }

  const char *alias = names[1] ? names[1] : names[0];
  *env_get(gc, env, alias) = *v;
  return 0;
}

static int do_import(void *item, void *ctx) {
  Node *n = item;
  void **p = ctx;
  GC *gc = p[0]; GCMap *modules = p[1]; GCMap *sources = p[2]; Env *env = p[3]; GCStack *stack = p[4]; const char **tags = p[5]; Intern *it = p[6];

  Env *from;
  int err = eval(gc, modules, sources, n->import.filepath, env, stack, tags, it, &from);
  if (err) { frame(n, "import"); return err; }

  void *ibc[3] = { gc, env, from };
  err = gc_list_each(n->import.names, import_bind, ibc);
  if (err) { frame(n, "import"); return err; }
  return 0;
}

static int do_bind(void *item, void *ctx) {
  Node *n = item;
  void **p = ctx;
  GC *gc = p[0]; Env *env = p[1]; GCStack *stack = p[2]; const char **tags = p[3]; Intern *it = p[4];

  int err = eval_expr(gc, env, stack, tags, it, n->bind.expr);
  if (err) { frame(n, "bind"); return err; }
  *env_get(gc, env, n->bind.name) = *gc_stack_top(stack);
  gc_stack_pop(stack, 1);
  return 0;
}


static int collect_import_path(void *item, void *ctx) {
  Node *n = item;
  void **p = ctx;
  *gc_list_append(p[0], p[1]) = n->import.filepath;
  return 0;
}

int eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Env *global, GCStack *stack, const char **tags, Intern *it, Env **out) {
  void **slot = gc_map_get(gc, modules, filepath);
  if (*slot) { *out = ((Module *)*slot)->env; return 0; }

  Module *mod = gc_alloc(gc, sizeof(Module), module_trace, NULL, NULL);
  mod->env = NULL;
  mod->mtime = 0;
  mod->imports = NULL;
  *slot = mod;

  env_new(gc, (void **)&mod->env);
  mod->env->parent = global;

  Source *s = *gc_map_find(sources, filepath);
  mod->mtime = s->mtime;

  void *ic[7] = { gc, modules, sources, mod->env, stack, (void *)tags, it };
  int err = gc_list_each(s->imports, do_import, ic);
  if (err) { fprintf(stderr, "  in %s\n", filepath); return err; }

  slot = gc_map_find(modules, filepath);
  *out = ((Module *)*slot)->env;

  void *bc[5] = { gc, *out, stack, (void *)tags, it };
  err = gc_list_each(s->binds, do_bind, bc);
  if (err) { fprintf(stderr, "  in %s\n", filepath); return err; }

  mod->imports = gc_list_new(gc);
  void *cp[2] = { gc, mod->imports };
  gc_list_each(s->imports, collect_import_path, cp);

  gc_map_delete(sources, filepath);
  *out = ((Module *)*slot)->env;
  return 0;
}
