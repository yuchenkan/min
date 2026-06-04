#ifndef KERNEL_H
#define KERNEL_H

#include "val.h"

/* ============================================================
 * Kernel: formula equality, substitution, helpers
 * ============================================================ */

bool formula_eq(Val *a, Val *b, void *env);  /* env is VarPair* internally */
bool same(Val *a, Val *b);
Val *subst(Val *f, const char *old, Val *new_);

/* VarSet */
typedef struct VarSet { const char **vars; int len; int cap; } VarSet;
VarSet *varset_new(void);
bool varset_has(VarSet *s, const char *v);
void varset_add(VarSet *s, const char *v);
void collect_bound_vars(Val *f, VarSet *s);
void collect_free_vars(Val *f, VarSet *bound, VarSet *free);

/* List helpers */
bool fin(Val *f, Val **lst, int len);
Val **list_remove(Val **lst, int len, Val *f, int *newlen);
Val **list_add(Val **lst, int len, Val *f, int *newlen);
bool is_permutation(Val **a, int alen, Val **b, int blen);
bool seq_eq(Val **l1, int nl1, Val **r1, int nr1, Val **l2, int nl2, Val **r2, int nr2);

/* Proof checking */
const char *check_rule(
    Val **left, int nleft, Val **right, int nright,
    const char *rule, Val **premises, int npremises,
    Val *principal, const char *term);

/* Formula builder */
Val *build_formula(Val *f);

/* ZFC axiom checking */
bool is_axiom(Val *f, const char *system);

/* ZFC axioms array (used by gc_mark_roots) */
extern Val *zfc_axioms[8];

#endif
