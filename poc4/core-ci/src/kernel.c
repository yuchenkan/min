#include "kernel.h"
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

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

static int is_mem(Node *f, const char **tags) { return ftag(f) == tags[K_MEM]; }
static int is_neg(Node *f, const char **tags) { return ftag(f) == tags[K_NEG]; }
static int is_implies(Node *f, const char **tags) { return ftag(f) == tags[K_IMPLIES]; }
static int is_forall(Node *f, const char **tags) { return ftag(f) == tags[K_FORALL]; }

/* ============================================================
 * Alpha-equivalence (read-only, no allocation)
 * ============================================================ */

typedef struct Binding { const char *a; const char *b; struct Binding *next; } Binding;

static int alpha_eq(Node *a, Node *b, Binding *env, const char **tags) {
  if (a->tag == N_STR && b->tag == N_STR) {
    for (Binding *e = env; e; e = e->next) {
      if (a->str == e->a) return b->str == e->b;
      if (b->str == e->b) return 0;
    }
    return a->str == b->str;
  }
  if (a->tag != N_ARR || b->tag != N_ARR) return 0;
  const char *ta = ftag(a), *tb = ftag(b);
  if (!ta || !tb || ta != tb) return 0;
  if (is_mem(a, tags))     return alpha_eq(farg(a,0), farg(b,0), env, tags) && alpha_eq(farg(a,1), farg(b,1), env, tags);
  if (is_neg(a, tags))     return alpha_eq(farg(a,0), farg(b,0), env, tags);
  if (is_implies(a, tags)) return alpha_eq(farg(a,0), farg(b,0), env, tags) && alpha_eq(farg(a,1), farg(b,1), env, tags);
  if (is_forall(a, tags)) {
    Binding bind = { farg(a,0)->str, farg(b,0)->str, env };
    return alpha_eq(farg(a,1), farg(b,1), &bind, tags);
  }
  return 0;
}

static int same(Node *a, Node *b, const char **tags) { return alpha_eq(a, b, NULL, tags); }

/* ============================================================
 * String sets (malloc'd, for free/bound vars)
 * ============================================================ */

typedef struct { const char **items; int len; int cap; } StrSet;
static StrSet ss_new(void) { return (StrSet){ malloc(sizeof(char*) * 8), 0, 8 }; }
static void ss_free(StrSet *s) { free(s->items); }
static int ss_has(StrSet *s, const char *v) {
  for (int i = 0; i < s->len; i++) if (s->items[i] == v) return 1;
  return 0;
}
static void ss_add(StrSet *s, const char *v) {
  if (ss_has(s, v)) return;
  if (s->len >= s->cap) { s->cap *= 2; s->items = realloc(s->items, sizeof(char*) * s->cap); }
  s->items[s->len++] = v;
}

static void freeVars_(Node *f, StrSet *bound, StrSet *out, const char **tags) {
  if (f->tag == N_STR) { if (!ss_has(bound, f->str)) ss_add(out, f->str); return; }
  if (is_mem(f, tags) || is_implies(f, tags)) { freeVars_(farg(f,0), bound, out, tags); freeVars_(farg(f,1), bound, out, tags); return; }
  if (is_neg(f, tags)) { freeVars_(farg(f,0), bound, out, tags); return; }
  if (is_forall(f, tags)) { ss_add(bound, farg(f,0)->str); freeVars_(farg(f,1), bound, out, tags); return; }
}

static StrSet freeVars(Node *f, const char **tags) {
  StrSet bound = ss_new(), out = ss_new();
  freeVars_(f, &bound, &out, tags);
  ss_free(&bound);
  return out;
}

static void boundVars_(Node *f, StrSet *out, const char **tags) {
  if (f->tag == N_STR) return;
  if (is_mem(f, tags) || is_implies(f, tags)) { boundVars_(farg(f,0), out, tags); boundVars_(farg(f,1), out, tags); return; }
  if (is_neg(f, tags)) { boundVars_(farg(f,0), out, tags); return; }
  if (is_forall(f, tags)) { ss_add(out, farg(f,0)->str); boundVars_(farg(f,1), out, tags); return; }
}

static StrSet boundVars(Node *f, const char **tags) {
  StrSet out = ss_new();
  boundVars_(f, &out, tags);
  return out;
}

/* ============================================================
 * Substitution (gc_alloc'd, pushed onto stack)
 * ============================================================ */

static Node *make_arr(GC *gc, GCStack *stack, Intern *it, int len, ...) {
  Node *args[8];
  va_list ap;
  va_start(ap, len);
  for (int i = 0; i < len; i++) args[i] = va_arg(ap, Node *);
  va_end(ap);
  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, args, len, slot);
  return *slot;
}

static Node *subst(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *f, const char *old, const char *new_str) {
  if (f->tag == N_STR) {
    if (f->str == old) {
      *gc_stack_push(gc, stack) = intern_str(it, new_str);
      return *gc_stack_top(stack);
    }
    return f;
  }
  if (is_forall(f, tags) && farg(f,0)->str == old) return f;

  Node *tag_node = ((Node **)f->arr.data)[0];
  if (is_mem(f, tags)) {
    Node *l = subst(gc, stack, tags, it, farg(f,0), old, new_str);
    Node *r = subst(gc, stack, tags, it, farg(f,1), old, new_str);
    if (l == farg(f,0) && r == farg(f,1)) return f;
    return make_arr(gc, stack, it, 3, tag_node, l, r);
  }
  if (is_neg(f, tags)) {
    Node *a = subst(gc, stack, tags, it, farg(f,0), old, new_str);
    if (a == farg(f,0)) return f;
    return make_arr(gc, stack, it, 2, tag_node, a);
  }
  if (is_implies(f, tags)) {
    Node *l = subst(gc, stack, tags, it, farg(f,0), old, new_str);
    Node *r = subst(gc, stack, tags, it, farg(f,1), old, new_str);
    if (l == farg(f,0) && r == farg(f,1)) return f;
    return make_arr(gc, stack, it, 3, tag_node, l, r);
  }
  if (is_forall(f, tags)) {
    Node *body = subst(gc, stack, tags, it, farg(f,1), old, new_str);
    if (body == farg(f,1)) return f;
    return make_arr(gc, stack, it, 3, tag_node, farg(f,0), body);
  }
  return f;
}

/* ============================================================
 * Sequent helpers (gc_alloc'd arrays on stack)
 * ============================================================ */

#define ALEN(n) ((int)(n)->arr.len)
#define AGET(n, i) (((Node **)(n)->arr.data)[i])

static int fin(Node *f, Node *lst, const char **tags) {
  for (int i = 0; i < ALEN(lst); i++)
    if (same(f, AGET(lst, i), tags)) return 1;
  return 0;
}

static Node *seq_remove(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *lst, Node *f) {
  int len = ALEN(lst);
  Node **tmp = malloc(sizeof(Node *) * len);
  int j = 0, removed = 0;
  for (int i = 0; i < len; i++) {
    if (!removed && same(f, AGET(lst, i), tags)) { removed = 1; continue; }
    tmp[j++] = AGET(lst, i);
  }
  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, tmp, j, slot);
  free(tmp);
  return *slot;
}

static Node *seq_add(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *lst, Node *f) {
  if (fin(f, lst, tags)) return lst;
  int len = ALEN(lst);
  Node **tmp = malloc(sizeof(Node *) * (len + 1));
  for (int i = 0; i < len; i++) tmp[i] = AGET(lst, i);
  tmp[len] = f;
  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, tmp, len + 1, slot);
  free(tmp);
  return *slot;
}

static int isPermutation(Node *a, Node *b, const char **tags) {
  int len = ALEN(a);
  if (len != ALEN(b)) return 0;
  int *used = calloc(len, sizeof(int));
  int ok = 1;
  for (int i = 0; i < len && ok; i++) {
    int found = 0;
    for (int j = 0; j < len; j++) {
      if (!used[j] && same(AGET(a, i), AGET(b, j), tags)) { used[j] = 1; found = 1; break; }
    }
    if (!found) ok = 0;
  }
  free(used);
  return ok;
}

static int eqSeq(Node *al, Node *ar, Node *bl, Node *br, const char **tags) {
  return isPermutation(al, bl, tags) && isPermutation(ar, br, tags);
}

static const char *checkSet(Node *lst, const char **tags) {
  for (int i = 0; i < ALEN(lst); i++)
    for (int j = i + 1; j < ALEN(lst); j++)
      if (same(AGET(lst, i), AGET(lst, j), tags))
        return "sequent: duplicate formula";
  return NULL;
}

/* ============================================================
 * Proof rules
 * ============================================================ */

#define PL(i) (AGET(premises, i))->proof.left
#define PR(i) (AGET(premises, i))->proof.right

static const char *checkRule(GC *gc, GCStack *stack, const char **tags, Intern *it,
                             Node *sl, Node *sr, const char *rule,
                             Node *premises, Node *principal, Node *term) {
  int np = ALEN(premises);
  int save = gc_stack_len(stack);

  const char *err = NULL;

  if (rule == tags[K_AXIOM]) {
    if (np != 0) { err = "axiom: premises not empty"; goto done; }
    if (!fin(principal, sl, tags)) { err = "axiom: principal not in left"; goto done; }
    if (!fin(principal, sr, tags)) { err = "axiom: principal not in right"; goto done; }
  }
  else if (rule == tags[K_NEG_LEFT]) {
    if (np != 1 || !is_neg(principal, tags)) { err = "neg_left: bad principal/premises"; goto done; }
    if (!fin(principal, sl, tags)) { err = "neg_left: principal not in left"; goto done; }
    Node *G = seq_remove(gc, stack, tags, it, sl, principal);
    Node *D = seq_add(gc, stack, tags, it, sr, farg(principal, 0));
    if (!eqSeq(PL(0), PR(0), G, D, tags)) err = "neg_left: premise mismatch";
  }
  else if (rule == tags[K_NEG_RIGHT]) {
    if (np != 1 || !is_neg(principal, tags)) { err = "neg_right: bad principal/premises"; goto done; }
    if (!fin(principal, sr, tags)) { err = "neg_right: principal not in right"; goto done; }
    Node *G = seq_add(gc, stack, tags, it, sl, farg(principal, 0));
    Node *D = seq_remove(gc, stack, tags, it, sr, principal);
    if (!eqSeq(PL(0), PR(0), G, D, tags)) err = "neg_right: premise mismatch";
  }
  else if (rule == tags[K_IMPLIES_LEFT]) {
    if (np != 2 || !is_implies(principal, tags)) { err = "implies_left: bad principal/premises"; goto done; }
    if (!fin(principal, sl, tags)) { err = "implies_left: principal not in left"; goto done; }
    Node *G = seq_remove(gc, stack, tags, it, sl, principal);
    Node *D0 = seq_add(gc, stack, tags, it, sr, farg(principal, 0));
    Node *G1 = seq_add(gc, stack, tags, it, G, farg(principal, 1));
    if (!eqSeq(PL(0), PR(0), G, D0, tags)) { err = "implies_left: premise 0 mismatch"; goto done; }
    if (!eqSeq(PL(1), PR(1), G1, sr, tags)) err = "implies_left: premise 1 mismatch";
  }
  else if (rule == tags[K_IMPLIES_RIGHT]) {
    if (np != 1 || !is_implies(principal, tags)) { err = "implies_right: bad principal/premises"; goto done; }
    if (!fin(principal, sr, tags)) { err = "implies_right: principal not in right"; goto done; }
    Node *D = seq_remove(gc, stack, tags, it, sr, principal);
    Node *G = seq_add(gc, stack, tags, it, sl, farg(principal, 0));
    Node *D2 = seq_add(gc, stack, tags, it, D, farg(principal, 1));
    if (!eqSeq(PL(0), PR(0), G, D2, tags)) err = "implies_right: premise mismatch";
  }
  else if (rule == tags[K_FORALL_LEFT]) {
    if (np != 1 || !term || term->tag != N_STR || !is_forall(principal, tags))
      { err = "forall_left: bad principal/premises/term"; goto done; }
    if (!fin(principal, sl, tags)) { err = "forall_left: principal not in left"; goto done; }
    StrSet bv = boundVars(farg(principal, 1), tags);
    if (ss_has(&bv, term->str)) { ss_free(&bv); err = "forall_left: term clashes with bound vars"; goto done; }
    ss_free(&bv);
    Node *G = seq_remove(gc, stack, tags, it, sl, principal);
    Node *substituted = subst(gc, stack, tags, it, farg(principal, 1), farg(principal, 0)->str, term->str);
    Node *G2 = seq_add(gc, stack, tags, it, G, substituted);
    if (!eqSeq(PL(0), PR(0), G2, sr, tags)) err = "forall_left: premise mismatch";
  }
  else if (rule == tags[K_FORALL_RIGHT]) {
    if (np != 1 || !term || term->tag != N_STR || !is_forall(principal, tags))
      { err = "forall_right: bad principal/premises/term"; goto done; }
    if (!fin(principal, sr, tags)) { err = "forall_right: principal not in right"; goto done; }
    StrSet bv = boundVars(farg(principal, 1), tags);
    if (ss_has(&bv, term->str)) { ss_free(&bv); err = "forall_right: term clashes with bound vars"; goto done; }
    ss_free(&bv);
    Node *D = seq_remove(gc, stack, tags, it, sr, principal);
    for (int i = 0; i < ALEN(sl); i++) {
      StrSet fv = freeVars(AGET(sl, i), tags);
      int has = ss_has(&fv, term->str); ss_free(&fv);
      if (has) { err = "forall_right: term free in context"; goto done; }
    }
    for (int i = 0; i < ALEN(D); i++) {
      StrSet fv = freeVars(AGET(D, i), tags);
      int has = ss_has(&fv, term->str); ss_free(&fv);
      if (has) { err = "forall_right: term free in context"; goto done; }
    }
    Node *substituted = subst(gc, stack, tags, it, farg(principal, 1), farg(principal, 0)->str, term->str);
    Node *D2 = seq_add(gc, stack, tags, it, D, substituted);
    if (!eqSeq(PL(0), PR(0), sl, D2, tags)) err = "forall_right: premise mismatch";
  }
  else if (rule == tags[K_CUT]) {
    if (np != 2) { err = "cut: need 2 premises"; goto done; }
    Node *D0 = seq_add(gc, stack, tags, it, sr, principal);
    Node *G1 = seq_add(gc, stack, tags, it, sl, principal);
    if (!eqSeq(PL(0), PR(0), sl, D0, tags)) { err = "cut: premise 0 mismatch"; goto done; }
    if (!eqSeq(PL(1), PR(1), G1, sr, tags)) err = "cut: premise 1 mismatch";
  }
  else if (rule == tags[K_WEAKENING_LEFT]) {
    if (np != 1) { err = "weakening_left: need 1 premise"; goto done; }
    if (!fin(principal, sl, tags)) { err = "weakening_left: principal not in left"; goto done; }
    if (fin(principal, PL(0), tags)) {
      if (!eqSeq(PL(0), PR(0), sl, sr, tags)) err = "weakening_left: premise mismatch (already present)";
      goto done;
    }
    Node *G = seq_remove(gc, stack, tags, it, sl, principal);
    if (!eqSeq(PL(0), PR(0), G, sr, tags)) err = "weakening_left: premise mismatch";
  }
  else if (rule == tags[K_WEAKENING_RIGHT]) {
    if (np != 1) { err = "weakening_right: need 1 premise"; goto done; }
    if (!fin(principal, sr, tags)) { err = "weakening_right: principal not in right"; goto done; }
    if (fin(principal, PR(0), tags)) {
      if (!eqSeq(PL(0), PR(0), sl, sr, tags)) err = "weakening_right: premise mismatch (already present)";
      goto done;
    }
    Node *D = seq_remove(gc, stack, tags, it, sr, principal);
    if (!eqSeq(PL(0), PR(0), sl, D, tags)) err = "weakening_right: premise mismatch";
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
    if (b->items[i].key == key) return b->items[i].val;
  return NULL;
}
static void pbind_set(PBindings *b, const char *key, Node *val) {
  b->items[b->n++] = (PBind){ key, val };
}

static Node *p_tag(GC *gc, GCStack *stack, Intern *it, const char *s) {
  *gc_stack_push(gc, stack) = intern_str(it, s);
  return *gc_stack_top(stack);
}

static Node *p_cap(GC *gc, GCStack *stack, Intern *it) {
  *gc_stack_push(gc, stack) = intern_none(it);
  return *gc_stack_top(stack);
}

static Node *p_arr(GC *gc, GCStack *stack, Intern *it, int len, ...) {
  va_list ap; va_start(ap, len);
  Node *args[8];
  for (int i = 0; i < len; i++) args[i] = va_arg(ap, Node*);
  va_end(ap);
  void **slot = gc_stack_push(gc, stack);
  intern_arr(it, args, len, slot);
  return *slot;
}

#define PT(k) p_tag(gc, stack, it, tags[k])
#define PC    p_cap(gc, stack, it)
#define PA(...) p_arr(gc, stack, it, __VA_ARGS__)

static Node *p_mem(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b) { return PA(3, PT(K_MEM), a, b); }
static Node *p_neg(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a) { return PA(2, PT(K_NEG), a); }
static Node *p_imp(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b) { return PA(3, PT(K_IMPLIES), a, b); }
static Node *p_fa(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *v, Node *body) { return PA(3, PT(K_FORALL), v, body); }
static Node *p_and(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b) { return p_neg(gc,stack,tags,it, p_imp(gc,stack,tags,it, a, p_neg(gc,stack,tags,it, b))); }
static Node *p_or(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b) { return p_imp(gc,stack,tags,it, p_neg(gc,stack,tags,it, a), b); }
static Node *p_iff(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b) {
  return p_neg(gc,stack,tags,it, p_imp(gc,stack,tags,it, p_imp(gc,stack,tags,it,a,b), p_neg(gc,stack,tags,it, p_imp(gc,stack,tags,it,b,a))));
}
static Node *p_exists(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *v, Node *body) { return p_neg(gc,stack,tags,it, p_fa(gc,stack,tags,it, v, p_neg(gc,stack,tags,it, body))); }
static Node *p_eqv(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *a, Node *b, Node *z) {
  return p_fa(gc,stack,tags,it, z, p_iff(gc,stack,tags,it, p_mem(gc,stack,tags,it,z,a), p_mem(gc,stack,tags,it,z,b)));
}

static int pmatch(Node *pat, Node *f, PBindings *b, const char **tags) {
  if (pat->tag == N_NONE) { pbind_set(b, tags[K_UNDERSCORE], f); return 1; }
  if (pat->tag == N_STR && f->tag == N_STR) {
    Node *prev = pbind_get(b, pat->str);
    if (prev) return prev->str == f->str;
    pbind_set(b, pat->str, f); return 1;
  }
  if (pat->tag != N_ARR || f->tag != N_ARR) return 0;
  const char *pt = ftag(pat), *ft = ftag(f);
  if (!pt || !ft || pt != ft) return 0;
  if (pt == tags[K_MEM])     return pmatch(farg(pat,0),farg(f,0),b,tags) && pmatch(farg(pat,1),farg(f,1),b,tags);
  if (pt == tags[K_NEG])     return pmatch(farg(pat,0),farg(f,0),b,tags);
  if (pt == tags[K_IMPLIES]) return pmatch(farg(pat,0),farg(f,0),b,tags) && pmatch(farg(pat,1),farg(f,1),b,tags);
  if (pt == tags[K_FORALL])  return pmatch(farg(pat,0),farg(f,0),b,tags) && pmatch(farg(pat,1),farg(f,1),b,tags);
  return 0;
}

struct KernelData {
  Node *axiom_pat[8];
  Node *sep_pat;
  Node *rep_pat;
};

static void kd_trace(void *data) {
  KernelData *kd = data;
  for (int i = 0; i < 8; i++) gc_mark(kd->axiom_pat[i]);
  gc_mark(kd->sep_pat);
  gc_mark(kd->rep_pat);
}

void kernel_precompute(GC *gc, GCStack *stack, const char **tags, Intern *it, void **slot) {
  int save = gc_stack_len(stack);

  KernelData *kd = gc_alloc(gc, sizeof(KernelData), kd_trace, NULL, NULL);
  memset(kd, 0, sizeof(KernelData));
  *slot = kd;

  #define M(a,b) p_mem(gc,stack,tags,it,a,b)
  #define N(a) p_neg(gc,stack,tags,it,a)
  #define I(a,b) p_imp(gc,stack,tags,it,a,b)
  #define F(v,body) p_fa(gc,stack,tags,it,v,body)
  #define A(a,b) p_and(gc,stack,tags,it,a,b)
  #define O(a,b) p_or(gc,stack,tags,it,a,b)
  #define IF(a,b) p_iff(gc,stack,tags,it,a,b)
  #define E(v,body) p_exists(gc,stack,tags,it,v,body)
  #define EQ(a,b,z) p_eqv(gc,stack,tags,it,a,b,z)

  Node *x=PT(K_X),*y=PT(K_Y),*z=PT(K_Z),*a=PT(K_A),*w=PT(K_W);
  Node *_b=PT(K_B),*e=PT(K_E),*s=PT(K_S),*_z=PT(K_UZ),*c=PT(K_C);
  Node *phi=PC, *uniq=PC;
  kd->axiom_pat[0] = F(x,F(y,I(F(z,IF(M(z,x),M(z,y))),F(z,IF(M(x,z),M(y,z))))));
  kd->axiom_pat[1] = E(_b,F(x,N(M(x,_b))));
  kd->axiom_pat[2] = F(x,F(y,E(_b,F(z,IF(M(z,_b),O(EQ(z,x,_z),EQ(z,y,_z)))))));
  kd->axiom_pat[3] = F(a,E(_b,F(x,IF(M(x,_b),E(y,A(M(y,a),M(x,y)))))));
  kd->axiom_pat[4] = F(a,E(_b,F(x,IF(M(x,_b),F(y,I(M(y,x),M(y,a)))))));
  kd->axiom_pat[5] = E(_b,A(E(e,A(M(e,_b),F(z,N(M(z,e))))),
    F(y,I(M(y,_b),E(s,A(M(s,_b),F(w,IF(M(w,s),O(M(w,y),EQ(w,y,_z))))))))));
  kd->axiom_pat[6] = F(a,I(E(y,M(y,a)),E(y,A(M(y,a),N(E(z,A(M(z,a),M(z,y))))))));
  kd->axiom_pat[7] = F(x,I(F(y,I(M(y,x),E(z,M(z,y)))),
    E(c,F(y,I(M(y,x),E(z,A(A(M(z,y),M(z,c)),F(w,I(A(M(w,y),M(w,c)),EQ(w,z,_z))))))))));

  kd->sep_pat = F(a, E(_b, F(x,
    IF(M(x,_b), A(M(x,a), phi)))));

  kd->rep_pat = F(a, I(uniq, E(_b, F(y,
    IF(M(y,_b), E(x, A(M(x,a), phi)))))));

  #undef M
  #undef N
  #undef I
  #undef F
  #undef A
  #undef O
  #undef IF
  #undef E
  #undef EQ

  gc_stack_pop(stack, gc_stack_len(stack) - save);
}

static int matchAxiom(KernelData *kd, Node *f, int idx, const char **tags) {
  PBindings b = { .n = 0 };
  return pmatch(kd->axiom_pat[idx], f, &b, tags);
}

static int isSeparation(KernelData *kd, Node *f, const char **tags) {
  const char **stripped = malloc(sizeof(char*) * 8);
  int nstripped = 0, cap = 8;
  Node *cur = f;
  int found = 0;
  while (!found) {
    PBindings b = { .n = 0 };
    if (pmatch(kd->sep_pat, cur, &b, tags)) {
      Node *mp = pbind_get(&b, tags[K_UNDERSCORE]);
      if (mp) {
        StrSet fv = freeVars(mp, tags);
        int ok = 1;
        for (int i = 0; i < fv.len && ok; i++) {
          int f2 = 0;
          Node *ba = pbind_get(&b, tags[K_A]), *bx = pbind_get(&b, tags[K_X]);
          if (ba && fv.items[i] == ba->str) f2=1;
          if (bx && fv.items[i] == bx->str) f2=1;
          for (int j = 0; j < nstripped && !f2; j++) if (fv.items[i] == stripped[j]) f2=1;
          if (!f2) ok = 0;
        }
        ss_free(&fv);
        if (ok) found = 1;
      }
    }
    if (found || !is_forall(cur, tags)) break;
    if (nstripped >= cap) { cap *= 2; stripped = realloc(stripped, sizeof(char*) * cap); }
    stripped[nstripped++] = farg(cur,0)->str;
    cur = farg(cur,1);
  }
  free(stripped);
  return found;
}

static int isReplacement(KernelData *kd, Node *f, const char **tags) {
  const char **stripped = malloc(sizeof(char*) * 8);
  int nstripped = 0, cap = 8;
  Node *cur = f;
  int found = 0;
  while (!found) {
    PBindings b = { .n = 0 };
    if (pmatch(kd->rep_pat, cur, &b, tags)) {
      Node *mp = NULL;
      for (int i = b.n-1; i >= 0; i--) if (b.items[i].key == tags[K_UNDERSCORE]) { mp = b.items[i].val; break; }
      if (mp) {
        StrSet fv = freeVars(mp, tags);
        int ok = 1;
        for (int i = 0; i < fv.len && ok; i++) {
          int f2 = 0;
          Node *ba=pbind_get(&b, tags[K_A]), *bx=pbind_get(&b, tags[K_X]), *by=pbind_get(&b, tags[K_Y]);
          if (ba && fv.items[i] == ba->str) f2=1;
          if (bx && fv.items[i] == bx->str) f2=1;
          if (by && fv.items[i] == by->str) f2=1;
          for (int j = 0; j < nstripped && !f2; j++) if (fv.items[i] == stripped[j]) f2=1;
          if (!f2) ok = 0;
        }
        ss_free(&fv);
        if (ok) found = 1;
      }
    }
    if (found || !is_forall(cur, tags)) break;
    if (nstripped >= cap) { cap *= 2; stripped = realloc(stripped, sizeof(char*) * cap); }
    stripped[nstripped++] = farg(cur,0)->str;
    cur = farg(cur,1);
  }
  free(stripped);
  return found;
}

static int isAxiom(KernelData *kd, Node *f, const char **tags, const char *system) {
  int limit = (system == tags[K_Z] || system == tags[K_ZF]) ? 7 : 8;
  for (int i = 0; i < limit; i++) if (matchAxiom(kd, f, i, tags)) return 1;
  if (isSeparation(kd, f, tags)) return 1;
  if ((system == tags[K_ZF] || system == tags[K_ZFC]) && isReplacement(kd, f, tags)) return 1;
  return 0;
}

/* ============================================================
 * Public API
 * ============================================================ */

const char *kernel_check(GC *gc, GCStack *stack, const char **tags, Intern *it,
                         Node *left, Node *right, const char *rule,
                         Node *premises, Node *principal, Node *term) {
  const char *err;
  err = checkSet(left, tags);  if (err) return err;
  err = checkSet(right, tags); if (err) return err;
  return checkRule(gc, stack, tags, it, left, right, rule, premises, principal, term);
}

const char *kernel_qed(GC *gc, GCStack *stack, const char **tags, Intern *it,
                       KernelData *kd,
                       Node *proof, Node *expected, const char *system) {
  (void)gc; (void)stack; (void)it;
  Node *sl = proof->proof.left, *sr = proof->proof.right;
  if (ALEN(sr) != 1) return "qed: expected 1 formula on right";
  StrSet fv = freeVars(AGET(sr, 0), tags);
  int has_fv = fv.len > 0; ss_free(&fv);
  if (has_fv) return "qed: theorem has free variables";
  for (int i = 0; i < ALEN(sl); i++)
    if (!isAxiom(kd, AGET(sl, i), tags, system)) return "qed: non-axiom on left";
  if (!same(AGET(sr, 0), expected, tags)) return "qed: theorem does not match expected";
  return NULL;
}
