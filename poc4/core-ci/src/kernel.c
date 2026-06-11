#include "kernel.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdarg.h>

/* ============================================================
 * Formula helpers
 *
 * variable:     N_STR "x"
 * mem(a,b):     N_ARR ["mem", a, b]
 * neg(a):       N_ARR ["neg", a]
 * implies(a,b): N_ARR ["implies", a, b]
 * forall(x,b):  N_ARR ["forall", N_STR x, body]
 * ============================================================ */

static const char *ftag(Node *f) {
  if (f->tag != N_ARR || f->arr.len == 0) return NULL;
  Node *first = ((Node **)f->arr.data)[0];
  return first->tag == N_STR ? first->str : NULL;
}

static Node *farg(Node *f, int i) {
  return ((Node **)f->arr.data)[i + 1];
}

static int is_mem(Node *f) { const char *t = ftag(f); return t && strcmp(t, "mem") == 0; }
static int is_neg(Node *f) { const char *t = ftag(f); return t && strcmp(t, "neg") == 0; }
static int is_implies(Node *f) { const char *t = ftag(f); return t && strcmp(t, "implies") == 0; }
static int is_forall(Node *f) { const char *t = ftag(f); return t && strcmp(t, "forall") == 0; }

/* ============================================================
 * Alpha-equivalence (read-only, no allocation)
 * ============================================================ */

typedef struct Binding { const char *a; const char *b; struct Binding *next; } Binding;

static int alpha_eq(Node *a, Node *b, Binding *env) {
  if (a->tag == N_STR && b->tag == N_STR) {
    for (Binding *e = env; e; e = e->next) {
      if (strcmp(a->str, e->a) == 0) return strcmp(b->str, e->b) == 0;
      if (strcmp(b->str, e->b) == 0) return 0;
    }
    return strcmp(a->str, b->str) == 0;
  }
  if (a->tag != N_ARR || b->tag != N_ARR) return 0;
  const char *ta = ftag(a), *tb = ftag(b);
  if (!ta || !tb || strcmp(ta, tb) != 0) return 0;
  if (is_mem(a))     return alpha_eq(farg(a,0), farg(b,0), env) && alpha_eq(farg(a,1), farg(b,1), env);
  if (is_neg(a))     return alpha_eq(farg(a,0), farg(b,0), env);
  if (is_implies(a)) return alpha_eq(farg(a,0), farg(b,0), env) && alpha_eq(farg(a,1), farg(b,1), env);
  if (is_forall(a)) {
    Binding bind = { farg(a,0)->str, farg(b,0)->str, env };
    return alpha_eq(farg(a,1), farg(b,1), &bind);
  }
  return 0;
}

static int same(Node *a, Node *b) { return alpha_eq(a, b, NULL); }

/* ============================================================
 * String sets (malloc'd, for free/bound vars)
 * ============================================================ */

typedef struct { const char **items; int len; int cap; } StrSet;
static StrSet ss_new(void) { return (StrSet){ malloc(sizeof(char*) * 8), 0, 8 }; }
static void ss_free(StrSet *s) { free(s->items); }
static int ss_has(StrSet *s, const char *v) {
  for (int i = 0; i < s->len; i++) if (strcmp(s->items[i], v) == 0) return 1;
  return 0;
}
static void ss_add(StrSet *s, const char *v) {
  if (ss_has(s, v)) return;
  if (s->len >= s->cap) { s->cap *= 2; s->items = realloc(s->items, sizeof(char*) * s->cap); }
  s->items[s->len++] = v;
}

static void freeVars_(Node *f, StrSet *bound, StrSet *out) {
  if (f->tag == N_STR) { if (!ss_has(bound, f->str)) ss_add(out, f->str); return; }
  if (is_mem(f) || is_implies(f)) { freeVars_(farg(f,0), bound, out); freeVars_(farg(f,1), bound, out); return; }
  if (is_neg(f)) { freeVars_(farg(f,0), bound, out); return; }
  if (is_forall(f)) { ss_add(bound, farg(f,0)->str); freeVars_(farg(f,1), bound, out); return; }
}

static StrSet freeVars(Node *f) {
  StrSet bound = ss_new(), out = ss_new();
  freeVars_(f, &bound, &out);
  ss_free(&bound);
  return out;
}

static void boundVars_(Node *f, StrSet *out) {
  if (f->tag == N_STR) return;
  if (is_mem(f) || is_implies(f)) { boundVars_(farg(f,0), out); boundVars_(farg(f,1), out); return; }
  if (is_neg(f)) { boundVars_(farg(f,0), out); return; }
  if (is_forall(f)) { ss_add(out, farg(f,0)->str); boundVars_(farg(f,1), out); return; }
}

static StrSet boundVars(Node *f) {
  StrSet out = ss_new();
  boundVars_(f, &out);
  return out;
}

/* ============================================================
 * Substitution (gc_alloc'd, pushed onto stack)
 * ============================================================ */

static Node *make_arr(GC *gc, GCStack *stack, int len, ...) {
  node_new(gc, gc_stack_push(gc, stack), N_ARR);
  Node *n = *gc_stack_top(stack);
  n->arr.data = gc_alloc(gc, sizeof(Node *) * len, NULL, NULL);
  n->arr.len = len;
  va_list ap;
  va_start(ap, len);
  for (int i = 0; i < len; i++) ((Node **)n->arr.data)[i] = va_arg(ap, Node *);
  va_end(ap);
  return n;
}

static Node *subst(GC *gc, GCStack *stack, Node *f, const char *old, const char *new_str) {
  if (f->tag == N_STR) {
    if (strcmp(f->str, old) == 0) {
      node_new(gc, gc_stack_push(gc, stack), N_STR);
      Node *n = *gc_stack_top(stack);
      n->str = gc_strdup(gc, new_str);
      return n;
    }
    return f;
  }
  if (is_forall(f) && strcmp(farg(f,0)->str, old) == 0) return f;

  Node *tag_node = ((Node **)f->arr.data)[0];
  if (is_mem(f)) {
    Node *l = subst(gc, stack, farg(f,0), old, new_str);
    Node *r = subst(gc, stack, farg(f,1), old, new_str);
    if (l == farg(f,0) && r == farg(f,1)) return f;
    return make_arr(gc, stack, 3, tag_node, l, r);
  }
  if (is_neg(f)) {
    Node *a = subst(gc, stack, farg(f,0), old, new_str);
    if (a == farg(f,0)) return f;
    return make_arr(gc, stack, 2, tag_node, a);
  }
  if (is_implies(f)) {
    Node *l = subst(gc, stack, farg(f,0), old, new_str);
    Node *r = subst(gc, stack, farg(f,1), old, new_str);
    if (l == farg(f,0) && r == farg(f,1)) return f;
    return make_arr(gc, stack, 3, tag_node, l, r);
  }
  if (is_forall(f)) {
    Node *body = subst(gc, stack, farg(f,1), old, new_str);
    if (body == farg(f,1)) return f;
    return make_arr(gc, stack, 3, tag_node, farg(f,0), body);
  }
  return f;
}

/* ============================================================
 * Sequent helpers (gc_alloc'd arrays on stack)
 * ============================================================ */

#define ALEN(n) ((int)(n)->arr.len)
#define AGET(n, i) (((Node **)(n)->arr.data)[i])

static int fin(Node *f, Node *lst) {
  for (int i = 0; i < ALEN(lst); i++)
    if (same(f, AGET(lst, i))) return 1;
  return 0;
}

static Node *seq_remove(GC *gc, GCStack *stack, Node *lst, Node *f) {
  int len = ALEN(lst);
  node_new(gc, gc_stack_push(gc, stack), N_ARR);
  Node *r = *gc_stack_top(stack);
  r->arr.data = gc_alloc(gc, sizeof(Node *) * len, NULL, NULL);
  int j = 0, removed = 0;
  for (int i = 0; i < len; i++) {
    if (!removed && same(f, AGET(lst, i))) { removed = 1; continue; }
    ((Node **)r->arr.data)[j++] = AGET(lst, i);
  }
  r->arr.len = j;
  return r;
}

static Node *seq_add(GC *gc, GCStack *stack, Node *lst, Node *f) {
  if (fin(f, lst)) return lst;
  int len = ALEN(lst);
  node_new(gc, gc_stack_push(gc, stack), N_ARR);
  Node *r = *gc_stack_top(stack);
  r->arr.data = gc_alloc(gc, sizeof(Node *) * (len + 1), NULL, NULL);
  for (int i = 0; i < len; i++) ((Node **)r->arr.data)[i] = AGET(lst, i);
  ((Node **)r->arr.data)[len] = f;
  r->arr.len = len + 1;
  return r;
}

static int isPermutation(Node *a, Node *b) {
  int len = ALEN(a);
  if (len != ALEN(b)) return 0;
  int *used = calloc(len, sizeof(int));
  int ok = 1;
  for (int i = 0; i < len && ok; i++) {
    int found = 0;
    for (int j = 0; j < len; j++) {
      if (!used[j] && same(AGET(a, i), AGET(b, j))) { used[j] = 1; found = 1; break; }
    }
    if (!found) ok = 0;
  }
  free(used);
  return ok;
}

static int eqSeq(Node *al, Node *ar, Node *bl, Node *br) {
  return isPermutation(al, bl) && isPermutation(ar, br);
}

static const char *checkSet(Node *lst) {
  for (int i = 0; i < ALEN(lst); i++)
    for (int j = i + 1; j < ALEN(lst); j++)
      if (same(AGET(lst, i), AGET(lst, j)))
        return "sequent: duplicate formula";
  return NULL;
}

/* ============================================================
 * Proof rules
 * ============================================================ */

#define PL(i) (AGET(premises, i))->proof.left
#define PR(i) (AGET(premises, i))->proof.right

static const char *checkRule(GC *gc, GCStack *stack,
                             Node *sl, Node *sr, const char *rule,
                             Node *premises, Node *principal, Node *term) {
  int np = ALEN(premises);
  int save = gc_stack_len(stack);

  const char *err = NULL;

  if (strcmp(rule, "axiom") == 0) {
    if (np != 0) { err = "axiom: premises not empty"; goto done; }
    if (!fin(principal, sl)) { err = "axiom: principal not in left"; goto done; }
    if (!fin(principal, sr)) { err = "axiom: principal not in right"; goto done; }
  }
  else if (strcmp(rule, "neg_left") == 0) {
    if (np != 1 || !is_neg(principal)) { err = "neg_left: bad principal/premises"; goto done; }
    if (!fin(principal, sl)) { err = "neg_left: principal not in left"; goto done; }
    Node *G = seq_remove(gc, stack, sl, principal);
    Node *D = seq_add(gc, stack, sr, farg(principal, 0));
    if (!eqSeq(PL(0), PR(0), G, D)) err = "neg_left: premise mismatch";
  }
  else if (strcmp(rule, "neg_right") == 0) {
    if (np != 1 || !is_neg(principal)) { err = "neg_right: bad principal/premises"; goto done; }
    if (!fin(principal, sr)) { err = "neg_right: principal not in right"; goto done; }
    Node *G = seq_add(gc, stack, sl, farg(principal, 0));
    Node *D = seq_remove(gc, stack, sr, principal);
    if (!eqSeq(PL(0), PR(0), G, D)) err = "neg_right: premise mismatch";
  }
  else if (strcmp(rule, "implies_left") == 0) {
    if (np != 2 || !is_implies(principal)) { err = "implies_left: bad principal/premises"; goto done; }
    if (!fin(principal, sl)) { err = "implies_left: principal not in left"; goto done; }
    Node *G = seq_remove(gc, stack, sl, principal);
    Node *D0 = seq_add(gc, stack, sr, farg(principal, 0));
    Node *G1 = seq_add(gc, stack, G, farg(principal, 1));
    if (!eqSeq(PL(0), PR(0), G, D0)) { err = "implies_left: premise 0 mismatch"; goto done; }
    if (!eqSeq(PL(1), PR(1), G1, sr)) err = "implies_left: premise 1 mismatch";
  }
  else if (strcmp(rule, "implies_right") == 0) {
    if (np != 1 || !is_implies(principal)) { err = "implies_right: bad principal/premises"; goto done; }
    if (!fin(principal, sr)) { err = "implies_right: principal not in right"; goto done; }
    Node *D = seq_remove(gc, stack, sr, principal);
    Node *G = seq_add(gc, stack, sl, farg(principal, 0));
    Node *D2 = seq_add(gc, stack, D, farg(principal, 1));
    if (!eqSeq(PL(0), PR(0), G, D2)) err = "implies_right: premise mismatch";
  }
  else if (strcmp(rule, "forall_left") == 0) {
    if (np != 1 || !term || term->tag != N_STR || !is_forall(principal))
      { err = "forall_left: bad principal/premises/term"; goto done; }
    if (!fin(principal, sl)) { err = "forall_left: principal not in left"; goto done; }
    StrSet bv = boundVars(farg(principal, 1));
    if (ss_has(&bv, term->str)) { ss_free(&bv); err = "forall_left: term clashes with bound vars"; goto done; }
    ss_free(&bv);
    Node *G = seq_remove(gc, stack, sl, principal);
    Node *substituted = subst(gc, stack, farg(principal, 1), farg(principal, 0)->str, term->str);
    Node *G2 = seq_add(gc, stack, G, substituted);
    if (!eqSeq(PL(0), PR(0), G2, sr)) err = "forall_left: premise mismatch";
  }
  else if (strcmp(rule, "forall_right") == 0) {
    if (np != 1 || !term || term->tag != N_STR || !is_forall(principal))
      { err = "forall_right: bad principal/premises/term"; goto done; }
    if (!fin(principal, sr)) { err = "forall_right: principal not in right"; goto done; }
    StrSet bv = boundVars(farg(principal, 1));
    if (ss_has(&bv, term->str)) { ss_free(&bv); err = "forall_right: term clashes with bound vars"; goto done; }
    ss_free(&bv);
    Node *D = seq_remove(gc, stack, sr, principal);
    for (int i = 0; i < ALEN(sl); i++) {
      StrSet fv = freeVars(AGET(sl, i));
      int has = ss_has(&fv, term->str); ss_free(&fv);
      if (has) { err = "forall_right: term free in context"; goto done; }
    }
    for (int i = 0; i < ALEN(D); i++) {
      StrSet fv = freeVars(AGET(D, i));
      int has = ss_has(&fv, term->str); ss_free(&fv);
      if (has) { err = "forall_right: term free in context"; goto done; }
    }
    Node *substituted = subst(gc, stack, farg(principal, 1), farg(principal, 0)->str, term->str);
    Node *D2 = seq_add(gc, stack, D, substituted);
    if (!eqSeq(PL(0), PR(0), sl, D2)) err = "forall_right: premise mismatch";
  }
  else if (strcmp(rule, "cut") == 0) {
    if (np != 2) { err = "cut: need 2 premises"; goto done; }
    Node *D0 = seq_add(gc, stack, sr, principal);
    Node *G1 = seq_add(gc, stack, sl, principal);
    if (!eqSeq(PL(0), PR(0), sl, D0)) { err = "cut: premise 0 mismatch"; goto done; }
    if (!eqSeq(PL(1), PR(1), G1, sr)) err = "cut: premise 1 mismatch";
  }
  else if (strcmp(rule, "weakening_left") == 0) {
    if (np != 1) { err = "weakening_left: need 1 premise"; goto done; }
    if (!fin(principal, sl)) { err = "weakening_left: principal not in left"; goto done; }
    if (fin(principal, PL(0))) {
      if (!eqSeq(PL(0), PR(0), sl, sr)) err = "weakening_left: premise mismatch (already present)";
      goto done;
    }
    Node *G = seq_remove(gc, stack, sl, principal);
    if (!eqSeq(PL(0), PR(0), G, sr)) err = "weakening_left: premise mismatch";
  }
  else if (strcmp(rule, "weakening_right") == 0) {
    if (np != 1) { err = "weakening_right: need 1 premise"; goto done; }
    if (!fin(principal, sr)) { err = "weakening_right: principal not in right"; goto done; }
    if (fin(principal, PR(0))) {
      if (!eqSeq(PL(0), PR(0), sl, sr)) err = "weakening_right: premise mismatch (already present)";
      goto done;
    }
    Node *D = seq_remove(gc, stack, sr, principal);
    if (!eqSeq(PL(0), PR(0), sl, D)) err = "weakening_right: premise mismatch";
  }
  else {
    err = "unknown rule";
  }

done:
  gc_stack_pop(stack, gc_stack_len(stack) - save);
  return err;
}

/* ============================================================
 * ZFC pattern matching
 * ============================================================ */

typedef struct { const char *key; Node *val; } PBind;
typedef struct { PBind items[64]; int n; } PBindings;

static Node *pbind_get(PBindings *b, const char *key) {
  for (int i = 0; i < b->n; i++)
    if (strcmp(b->items[i].key, key) == 0) return b->items[i].val;
  return NULL;
}
static void pbind_set(PBindings *b, const char *key, Node *val) {
  b->items[b->n++] = (PBind){ key, val };
}

/* Pattern nodes: gc_alloc'd, pushed onto stack.
   N_NONE = capture (matches any formula).
   N_STR = pattern var (binds on first occurrence). */

static Node *p_str(GC *gc, GCStack *stack, const char *s) {
  node_new(gc, gc_stack_push(gc, stack), N_STR);
  Node *n = *gc_stack_top(stack);
  n->str = gc_strdup(gc, s);
  return n;
}

static Node *p_cap(GC *gc, GCStack *stack) {
  node_new(gc, gc_stack_push(gc, stack), N_NONE);
  return *gc_stack_top(stack);
}

static Node *p_arr(GC *gc, GCStack *stack, int len, ...) {
  /* collect args from va_list first (they're already on stack) */
  va_list ap; va_start(ap, len);
  Node *args[8];
  for (int i = 0; i < len; i++) args[i] = va_arg(ap, Node*);
  va_end(ap);
  node_new(gc, gc_stack_push(gc, stack), N_ARR);
  Node *n = *gc_stack_top(stack);
  n->arr.data = gc_alloc(gc, sizeof(Node*) * len, NULL, NULL);
  n->arr.len = len;
  for (int i = 0; i < len; i++) ((Node**)n->arr.data)[i] = args[i];
  return n;
}

#define PS(s) p_str(gc, stack, s)
#define PC    p_cap(gc, stack)
#define PA(...) p_arr(gc, stack, __VA_ARGS__)

static Node *p_mem(GC *gc, GCStack *stack, Node *a, Node *b) { return PA(3, PS("mem"), a, b); }
static Node *p_neg(GC *gc, GCStack *stack, Node *a) { return PA(2, PS("neg"), a); }
static Node *p_imp(GC *gc, GCStack *stack, Node *a, Node *b) { return PA(3, PS("implies"), a, b); }
static Node *p_fa(GC *gc, GCStack *stack, Node *v, Node *body) { return PA(3, PS("forall"), v, body); }
static Node *p_and(GC *gc, GCStack *stack, Node *a, Node *b) { return p_neg(gc,stack, p_imp(gc,stack, a, p_neg(gc,stack, b))); }
static Node *p_or(GC *gc, GCStack *stack, Node *a, Node *b) { return p_imp(gc,stack, p_neg(gc,stack, a), b); }
static Node *p_iff(GC *gc, GCStack *stack, Node *a, Node *b) {
  return p_neg(gc,stack, p_imp(gc,stack, p_imp(gc,stack,a,b), p_neg(gc,stack, p_imp(gc,stack,b,a))));
}
static Node *p_exists(GC *gc, GCStack *stack, Node *v, Node *body) { return p_neg(gc,stack, p_fa(gc,stack, v, p_neg(gc,stack, body))); }
static Node *p_eqv(GC *gc, GCStack *stack, Node *a, Node *b, Node *z) {
  return p_fa(gc,stack, z, p_iff(gc,stack, p_mem(gc,stack,z,a), p_mem(gc,stack,z,b)));
}

static int pmatch(Node *pat, Node *f, PBindings *b) {
  if (pat->tag == N_NONE) { pbind_set(b, "_", f); return 1; }
  if (pat->tag == N_STR && f->tag == N_STR) {
    Node *prev = pbind_get(b, pat->str);
    if (prev) return strcmp(prev->str, f->str) == 0;
    pbind_set(b, pat->str, f); return 1;
  }
  if (pat->tag != N_ARR || f->tag != N_ARR) return 0;
  const char *pt = ftag(pat), *ft = ftag(f);
  if (!pt || !ft || strcmp(pt, ft) != 0) return 0;
  if (strcmp(pt,"mem")==0)     return pmatch(farg(pat,0),farg(f,0),b) && pmatch(farg(pat,1),farg(f,1),b);
  if (strcmp(pt,"neg")==0)     return pmatch(farg(pat,0),farg(f,0),b);
  if (strcmp(pt,"implies")==0) return pmatch(farg(pat,0),farg(f,0),b) && pmatch(farg(pat,1),farg(f,1),b);
  if (strcmp(pt,"forall")==0)  return pmatch(farg(pat,0),farg(f,0),b) && pmatch(farg(pat,1),farg(f,1),b);
  return 0;
}

static int matchAxiom(GC *gc, GCStack *stack, Node *f, int idx) {
  int save = gc_stack_len(stack);
  PBindings b = { .n = 0 };
  #define S(s) PS(s)
  #define M(a,b) p_mem(gc,stack,a,b)
  #define N(a) p_neg(gc,stack,a)
  #define I(a,b) p_imp(gc,stack,a,b)
  #define F(v,body) p_fa(gc,stack,v,body)
  #define A(a,b) p_and(gc,stack,a,b)
  #define O(a,b) p_or(gc,stack,a,b)
  #define IF(a,b) p_iff(gc,stack,a,b)
  #define E(v,body) p_exists(gc,stack,v,body)
  #define EQ(a,b,z) p_eqv(gc,stack,a,b,z)

  Node *x=S("x"),*y=S("y"),*z=S("z"),*a=S("a"),*w=S("w");
  Node *_b=S("b"),*e=S("e"),*s=S("s"),*_z=S("_z"),*c=S("c");
  Node *pat = NULL;
  switch (idx) {
  case 0: pat=F(x,F(y,I(F(z,IF(M(z,x),M(z,y))),F(z,IF(M(x,z),M(y,z)))))); break;
  case 1: pat=E(_b,F(x,N(M(x,_b)))); break;
  case 2: pat=F(x,F(y,E(_b,F(z,IF(M(z,_b),O(EQ(z,x,_z),EQ(z,y,_z))))))); break;
  case 3: pat=F(a,E(_b,F(x,IF(M(x,_b),E(y,A(M(y,a),M(x,y))))))); break;
  case 4: pat=F(a,E(_b,F(x,IF(M(x,_b),F(y,I(M(y,x),M(y,a))))))); break;
  case 5: pat=E(_b,A(E(e,A(M(e,_b),F(z,N(M(z,e))))),
    F(y,I(M(y,_b),E(s,A(M(s,_b),F(w,IF(M(w,s),O(M(w,y),EQ(w,y,_z)))))))))); break;
  case 6: pat=F(a,I(E(y,M(y,a)),E(y,A(M(y,a),N(E(z,A(M(z,a),M(z,y)))))))); break;
  case 7: pat=F(x,I(F(y,I(M(y,x),E(z,M(z,y)))),
    E(c,F(y,I(M(y,x),E(z,A(A(M(z,y),M(z,c)),F(w,I(A(M(w,y),M(w,c)),EQ(w,z,_z)))))))))); break;
  }
  int result = pat ? pmatch(pat, f, &b) : 0;
  gc_stack_pop(stack, gc_stack_len(stack) - save);

  #undef S
  #undef M
  #undef N
  #undef I
  #undef F
  #undef A
  #undef O
  #undef IF
  #undef E
  #undef EQ
  return result;
}

static int isSeparation(GC *gc, GCStack *stack, Node *f) {
  const char **stripped = malloc(sizeof(char*) * 8);
  int nstripped = 0, cap = 8;
  Node *cur = f;
  int found = 0;
  while (!found) {
    int save = gc_stack_len(stack);
    Node *phi=PC, *a=PS("a"), *_b=PS("b"), *x=PS("x");
    Node *pat = p_fa(gc,stack, a, p_exists(gc,stack, _b, p_fa(gc,stack, x,
      p_iff(gc,stack, p_mem(gc,stack,x,_b), p_and(gc,stack, p_mem(gc,stack,x,a), phi)))));
    PBindings b = { .n = 0 };
    if (pmatch(pat, cur, &b)) {
      Node *mp = pbind_get(&b, "_");
      if (mp) {
        StrSet fv = freeVars(mp);
        int ok = 1;
        for (int i = 0; i < fv.len && ok; i++) {
          int f2 = 0;
          Node *ba = pbind_get(&b,"a"), *bx = pbind_get(&b,"x");
          if (ba && strcmp(fv.items[i], ba->str)==0) f2=1;
          if (bx && strcmp(fv.items[i], bx->str)==0) f2=1;
          for (int j = 0; j < nstripped && !f2; j++) if (strcmp(fv.items[i], stripped[j])==0) f2=1;
          if (!f2) ok = 0;
        }
        ss_free(&fv);
        if (ok) found = 1;
      }
    }
    gc_stack_pop(stack, gc_stack_len(stack) - save);
    if (found || !is_forall(cur)) break;
    if (nstripped >= cap) { cap *= 2; stripped = realloc(stripped, sizeof(char*) * cap); }
    stripped[nstripped++] = farg(cur,0)->str;
    cur = farg(cur,1);
  }
  free(stripped);
  return found;
}

static int isReplacement(GC *gc, GCStack *stack, Node *f) {
  const char **stripped = malloc(sizeof(char*) * 8);
  int nstripped = 0, cap = 8;
  Node *cur = f;
  int found = 0;
  while (!found) {
    int save = gc_stack_len(stack);
    Node *phi=PC, *uniq=PC, *a=PS("a"), *_b=PS("b"), *x=PS("x"), *y=PS("y");
    Node *pat = p_fa(gc,stack, a, p_imp(gc,stack, uniq, p_exists(gc,stack, _b, p_fa(gc,stack, y,
      p_iff(gc,stack, p_mem(gc,stack,y,_b), p_exists(gc,stack, x, p_and(gc,stack, p_mem(gc,stack,x,a), phi)))))));
    PBindings b = { .n = 0 };
    if (pmatch(pat, cur, &b)) {
      Node *mp = NULL;
      for (int i = b.n-1; i >= 0; i--) if (strcmp(b.items[i].key,"_")==0) { mp = b.items[i].val; break; }
      if (mp) {
        StrSet fv = freeVars(mp);
        int ok = 1;
        for (int i = 0; i < fv.len && ok; i++) {
          int f2 = 0;
          Node *ba=pbind_get(&b,"a"), *bx=pbind_get(&b,"x"), *by=pbind_get(&b,"y");
          if (ba && strcmp(fv.items[i], ba->str)==0) f2=1;
          if (bx && strcmp(fv.items[i], bx->str)==0) f2=1;
          if (by && strcmp(fv.items[i], by->str)==0) f2=1;
          for (int j = 0; j < nstripped && !f2; j++) if (strcmp(fv.items[i], stripped[j])==0) f2=1;
          if (!f2) ok = 0;
        }
        ss_free(&fv);
        if (ok) found = 1;
      }
    }
    gc_stack_pop(stack, gc_stack_len(stack) - save);
    if (found || !is_forall(cur)) break;
    if (nstripped >= cap) { cap *= 2; stripped = realloc(stripped, sizeof(char*) * cap); }
    stripped[nstripped++] = farg(cur,0)->str;
    cur = farg(cur,1);
  }
  free(stripped);
  return found;
}

static int isAxiom(GC *gc, GCStack *stack, Node *f, const char *system) {
  int limit = (strcmp(system,"z")==0 || strcmp(system,"zf")==0) ? 7 : 8;
  for (int i = 0; i < limit; i++) if (matchAxiom(gc, stack, f, i)) return 1;
  if (isSeparation(gc, stack, f)) return 1;
  if ((strcmp(system,"zf")==0 || strcmp(system,"zfc")==0) && isReplacement(gc, stack, f)) return 1;
  return 0;
}

/* ============================================================
 * Public API
 * ============================================================ */

const char *kernel_check(GC *gc, GCStack *stack,
                         Node *left, Node *right, const char *rule,
                         Node *premises, Node *principal, Node *term) {
  const char *err;
  err = checkSet(left);  if (err) return err;
  err = checkSet(right); if (err) return err;
  return checkRule(gc, stack, left, right, rule, premises, principal, term);
}

const char *kernel_qed(GC *gc, GCStack *stack,
                       Node *proof, Node *expected, const char *system) {
  Node *sl = proof->proof.left, *sr = proof->proof.right;
  if (ALEN(sr) != 1) return "qed: expected 1 formula on right";
  StrSet fv = freeVars(AGET(sr, 0));
  int has_fv = fv.len > 0; ss_free(&fv);
  if (has_fv) return "qed: theorem has free variables";
  for (int i = 0; i < ALEN(sl); i++)
    if (!isAxiom(gc, stack, AGET(sl, i), system)) return "qed: non-axiom on left";
  if (!same(AGET(sr, 0), expected)) return "qed: theorem does not match expected";
  return NULL;
}
