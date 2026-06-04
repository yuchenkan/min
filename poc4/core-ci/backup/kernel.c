#include "kernel.h"
#include "parse.h"

/* ============================================================
 * Kernel: formula equality (alpha-equiv)
 * ============================================================ */

typedef struct VarPair { const char *a; const char *b; struct VarPair *next; } VarPair;

bool formula_eq(Val *a, Val *b, void *env) {
    VarPair *venv = (VarPair*)env;
    if (a == b) return true;
    if (a->tag == V_STR && b->tag == V_STR) {
        /* check bound var mapping */
        for (VarPair *p = venv; p; p = p->next) {
            if (strcmp(a->s, p->a) == 0) return strcmp(b->s, p->b) == 0;
            if (strcmp(b->s, p->b) == 0) return false;
        }
        return strcmp(a->s, b->s) == 0;
    }
    if (a->tag != b->tag) return false;
    if (a->tag == V_MEM)
        return formula_eq(a->mem.left, b->mem.left, venv) &&
               formula_eq(a->mem.right, b->mem.right, venv);
    if (a->tag == V_NEG)
        return formula_eq(a->neg.operand, b->neg.operand, venv);
    if (a->tag == V_IMPLIES)
        return formula_eq(a->implies.left, b->implies.left, venv) &&
               formula_eq(a->implies.right, b->implies.right, venv);
    if (a->tag == V_FORALL) {
        VarPair pair = { a->forall.var, b->forall.var, venv };
        return formula_eq(a->forall.body, b->forall.body, &pair);
    }
    return false;
}

bool same(Val *a, Val *b) {
    return formula_eq(a, b, NULL);
}

/* ============================================================
 * Kernel: substitution, free/bound vars, helpers
 * ============================================================ */

Val *subst(Val *f, const char *old, Val *new_) {
    if (f->tag == V_STR)
        return strcmp(f->s, old) == 0 ? new_ : f;
    if (f->tag == V_MEM)
        return val_mem(subst(f->mem.left, old, new_), subst(f->mem.right, old, new_));
    if (f->tag == V_NEG)
        return val_neg(subst(f->neg.operand, old, new_));
    if (f->tag == V_IMPLIES)
        return val_implies(subst(f->implies.left, old, new_), subst(f->implies.right, old, new_));
    if (f->tag == V_FORALL) {
        if (strcmp(f->forall.var, old) == 0) return f;
        return val_forall(f->forall.var, subst(f->forall.body, old, new_));
    }
    die("subst: unknown formula tag %d", f->tag);
    return NULL;
}

VarSet *varset_new(void) {
    VarSet *s = gc_alloc(sizeof(VarSet), GC_KIND_RAW);
    s->cap = 16;
    s->vars = gc_alloc(sizeof(const char*) * s->cap, GC_KIND_RAW);
    s->len = 0;
    return s;
}

bool varset_has(VarSet *s, const char *v) {
    for (int i = 0; i < s->len; i++)
        if (strcmp(s->vars[i], v) == 0) return true;
    return false;
}

void varset_add(VarSet *s, const char *v) {
    if (varset_has(s, v)) return;
    if (s->len >= s->cap) {
        s->cap *= 2;
        const char **n = gc_alloc(sizeof(const char*) * s->cap, GC_KIND_RAW);
        memcpy(n, s->vars, sizeof(const char*) * s->len);
        s->vars = n;
    }
    s->vars[s->len++] = v;
}

void collect_bound_vars(Val *f, VarSet *s) {
    if (f->tag == V_STR) return;
    if (f->tag == V_MEM) { collect_bound_vars(f->mem.left, s); collect_bound_vars(f->mem.right, s); return; }
    if (f->tag == V_NEG) { collect_bound_vars(f->neg.operand, s); return; }
    if (f->tag == V_IMPLIES) { collect_bound_vars(f->implies.left, s); collect_bound_vars(f->implies.right, s); return; }
    if (f->tag == V_FORALL) { varset_add(s, f->forall.var); collect_bound_vars(f->forall.body, s); return; }
}

void collect_free_vars(Val *f, VarSet *bound, VarSet *free) {
    if (f->tag == V_STR) {
        if (!varset_has(bound, f->s)) varset_add(free, f->s);
        return;
    }
    if (f->tag == V_MEM) { collect_free_vars(f->mem.left, bound, free); collect_free_vars(f->mem.right, bound, free); return; }
    if (f->tag == V_NEG) { collect_free_vars(f->neg.operand, bound, free); return; }
    if (f->tag == V_IMPLIES) { collect_free_vars(f->implies.left, bound, free); collect_free_vars(f->implies.right, bound, free); return; }
    if (f->tag == V_FORALL) {
        VarSet *nb = varset_new();
        for (int i = 0; i < bound->len; i++) varset_add(nb, bound->vars[i]);
        varset_add(nb, f->forall.var);
        collect_free_vars(f->forall.body, nb, free);
        return;
    }
}

/* list helpers */
bool fin(Val *f, Val **lst, int len) {
    for (int i = 0; i < len; i++) if (same(f, lst[i])) return true;
    return false;
}

Val **list_remove(Val **lst, int len, Val *f, int *newlen) {
    Val **r = gc_alloc(sizeof(Val*) * (len > 0 ? len : 1), GC_KIND_RAW);
    int ri = 0;
    bool removed = false;
    for (int i = 0; i < len; i++) {
        if (!removed && same(f, lst[i])) { removed = true; continue; }
        r[ri++] = lst[i];
    }
    *newlen = ri;
    return r;
}

Val **list_add(Val **lst, int len, Val *f, int *newlen) {
    if (fin(f, lst, len)) {
        Val **r = gc_alloc(sizeof(Val*) * (len > 0 ? len : 1), GC_KIND_RAW);
        memcpy(r, lst, sizeof(Val*) * len);
        *newlen = len;
        return r;
    }
    Val **r = gc_alloc(sizeof(Val*) * (len + 1), GC_KIND_RAW);
    memcpy(r, lst, sizeof(Val*) * len);
    r[len] = f;
    *newlen = len + 1;
    return r;
}

bool is_permutation(Val **a, int alen, Val **b, int blen) {
    if (alen != blen) return false;
    bool *used = gc_alloc(sizeof(bool) * (blen > 0 ? blen : 1), GC_KIND_RAW);
    memset(used, 0, sizeof(bool) * blen);
    for (int i = 0; i < alen; i++) {
        bool found = false;
        for (int j = 0; j < blen; j++) {
            if (!used[j] && same(a[i], b[j])) { used[j] = true; found = true; break; }
        }
        if (!found) return false;
    }
    return true;
}

bool seq_eq(Val **l1, int nl1, Val **r1, int nr1, Val **l2, int nl2, Val **r2, int nr2) {
    return is_permutation(l1, nl1, l2, nl2) && is_permutation(r1, nr1, r2, nr2);
}

/* ============================================================
 * Kernel: proof checking
 * ============================================================ */

const char *check_rule(
    Val **left, int nleft, Val **right, int nright,
    const char *rule, Val **premises, int npremises,
    Val *principal, const char *term)
{
    if (strcmp(rule, "axiom") == 0) {
        if (npremises != 0) return "axiom: premises not empty";
        if (!fin(principal, left, nleft)) return "axiom: principal not in left";
        if (!fin(principal, right, nright)) return "axiom: principal not in right";
        return NULL;
    }

    if (strcmp(rule, "neg_left") == 0) {
        if (npremises != 1 || principal->tag != V_NEG) return "neg_left: bad";
        if (!fin(principal, left, nleft)) return "neg_left: principal not in left";
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        int gnr; Val **gr = list_add(right, nright, principal->neg.operand, &gnr);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gnl, gr, gnr))
            return "neg_left: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "neg_right") == 0) {
        if (npremises != 1 || principal->tag != V_NEG) return "neg_right: bad";
        if (!fin(principal, right, nright)) return "neg_right: principal not in right";
        int gnl; Val **gl = list_add(left, nleft, principal->neg.operand, &gnl);
        int gnr; Val **gr = list_remove(right, nright, principal, &gnr);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gnl, gr, gnr))
            return "neg_right: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "implies_left") == 0) {
        if (npremises != 2 || principal->tag != V_IMPLIES) return "implies_left: bad";
        if (!fin(principal, left, nleft)) return "implies_left: principal not in left";
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        int gr0n; Val **gr0 = list_add(right, nright, principal->implies.left, &gr0n);
        int gl1n; Val **gl1 = list_add(gl, gnl, principal->implies.right, &gl1n);
        Val *p0 = premises[0], *p1 = premises[1];
        if (!seq_eq(p0->proof.left, p0->proof.nleft, p0->proof.right, p0->proof.nright, gl, gnl, gr0, gr0n))
            return "implies_left: premise 0 mismatch";
        if (!seq_eq(p1->proof.left, p1->proof.nleft, p1->proof.right, p1->proof.nright, gl1, gl1n, right, nright))
            return "implies_left: premise 1 mismatch";
        return NULL;
    }

    if (strcmp(rule, "implies_right") == 0) {
        if (npremises != 1 || principal->tag != V_IMPLIES) return "implies_right: bad";
        if (!fin(principal, right, nright)) return "implies_right: principal not in right";
        int gdn; Val **gd = list_remove(right, nright, principal, &gdn);
        int gln; Val **gl = list_add(left, nleft, principal->implies.left, &gln);
        int grn; Val **gr = list_add(gd, gdn, principal->implies.right, &grn);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gln, gr, grn))
            return "implies_right: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "forall_left") == 0) {
        if (npremises != 1 || !term || principal->tag != V_FORALL) return "forall_left: bad";
        if (!fin(principal, left, nleft)) return "forall_left: principal not in left";
        VarSet *bv = varset_new();
        collect_bound_vars(principal->forall.body, bv);
        if (varset_has(bv, term)) return "forall_left: term clashes with boundVars";
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        Val *substituted = subst(principal->forall.body, principal->forall.var, val_str(term));
        int gln; Val **gl2 = list_add(gl, gnl, substituted, &gln);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl2, gln, right, nright))
            return "forall_left: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "forall_right") == 0) {
        if (npremises != 1 || !term || principal->tag != V_FORALL) return "forall_right: bad";
        if (!fin(principal, right, nright)) return "forall_right: principal not in right";
        VarSet *bv = varset_new();
        collect_bound_vars(principal->forall.body, bv);
        if (varset_has(bv, term)) return "forall_right: term clashes with boundVars";
        int gdn; Val **gd = list_remove(right, nright, principal, &gdn);
        /* eigenvariable check */
        const char *ti = term;
        for (int i = 0; i < nleft; i++) {
            VarSet *fv = varset_new();
            collect_free_vars(left[i], varset_new(), fv);
            if (varset_has(fv, ti)) return "forall_right: term free in context";
        }
        for (int i = 0; i < gdn; i++) {
            VarSet *fv = varset_new();
            collect_free_vars(gd[i], varset_new(), fv);
            if (varset_has(fv, ti)) return "forall_right: term free in context";
        }
        Val *substituted = subst(principal->forall.body, principal->forall.var, val_str(term));
        int grn; Val **gr = list_add(gd, gdn, substituted, &grn);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, left, nleft, gr, grn))
            return "forall_right: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "cut") == 0) {
        if (npremises != 2) return "cut: need 2 premises";
        int gr0n; Val **gr0 = list_add(right, nright, principal, &gr0n);
        int gl1n; Val **gl1 = list_add(left, nleft, principal, &gl1n);
        Val *p0 = premises[0], *p1 = premises[1];
        if (!seq_eq(p0->proof.left, p0->proof.nleft, p0->proof.right, p0->proof.nright, left, nleft, gr0, gr0n))
            return "cut: premise 0 mismatch";
        if (!seq_eq(p1->proof.left, p1->proof.nleft, p1->proof.right, p1->proof.nright, gl1, gl1n, right, nright))
            return "cut: premise 1 mismatch";
        return NULL;
    }

    if (strcmp(rule, "weakening_left") == 0) {
        if (npremises != 1) return "weakening_left: need 1 premise";
        if (!fin(principal, left, nleft)) return "weakening_left: principal not in left";
        Val *p = premises[0];
        if (fin(principal, p->proof.left, p->proof.nleft)) {
            if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, left, nleft, right, nright))
                return "weakening_left: premise mismatch (already present)";
            return NULL;
        }
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gnl, right, nright))
            return "weakening_left: premise mismatch";
        return NULL;
    }

    if (strcmp(rule, "weakening_right") == 0) {
        if (npremises != 1) return "weakening_right: need 1 premise";
        if (!fin(principal, right, nright)) return "weakening_right: principal not in right";
        Val *p = premises[0];
        if (fin(principal, p->proof.right, p->proof.nright)) {
            if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, left, nleft, right, nright))
                return "weakening_right: premise mismatch (already present)";
            return NULL;
        }
        int gnr; Val **gr = list_remove(right, nright, principal, &gnr);
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, left, nleft, gr, gnr))
            return "weakening_right: premise mismatch";
        return NULL;
    }

    return "unknown rule";
}

/* ============================================================
 * Formula builder
 * ============================================================ */

Val *build_formula(Val *f) {
    if (f->tag == V_STR) return f;
    if (f->tag != V_LIST || f->list.len < 1) die("build_formula: bad input");
    const char *tag = f->list.items[0]->s;
    if (strcmp(tag, "mem") == 0) return val_mem(build_formula(f->list.items[1]), build_formula(f->list.items[2]));
    if (strcmp(tag, "neg") == 0) return val_neg(build_formula(f->list.items[1]));
    if (strcmp(tag, "implies") == 0) return val_implies(build_formula(f->list.items[1]), build_formula(f->list.items[2]));
    if (strcmp(tag, "forall") == 0) return val_forall(f->list.items[1]->s, build_formula(f->list.items[2]));
    die("build_formula: unknown tag %s", tag);
    return NULL;
}

/* ============================================================
 * ZFC axiom checking
 * ============================================================ */

Val *zfc_axioms[8];

static bool is_separation(Val *f) {
    /* Strip leading foralls */
    while (f->tag == V_FORALL) f = f->forall.body;
    if (f->tag != V_FORALL) return false;
    Val *body = f->forall.body;
    if (body->tag != V_NEG) return false;
    Val *inner = body->neg.operand;
    if (inner->tag != V_FORALL) return false;
    Val *inner2 = inner->forall.body;
    if (inner2->tag != V_NEG) return false;
    Val *fax = inner2->neg.operand;
    if (fax->tag != V_FORALL) return false;
    Val *iff_body = fax->forall.body;
    if (iff_body->tag != V_NEG) return false;
    Val *imp1 = iff_body->neg.operand;
    if (imp1->tag != V_IMPLIES) return false;
    return true;
}

static bool is_replacement(Val *f) {
    (void)f;
    return false;
}

/* Helper constructors for ZFC patterns */
static Val *p_and(Val *a, Val *b) { return val_neg(val_implies(a, val_neg(b))); }
static Val *p_or(Val *a, Val *b) { return val_implies(val_neg(a), b); }
static Val *p_iff(Val *a, Val *b) { return val_neg(val_implies(val_implies(a,b), val_neg(val_implies(b,a)))); }
static Val *p_exists(const char *v, Val *body) { return val_neg(val_forall(v, val_neg(body))); }
static Val *p_eqv(const char *a, const char *b) {
    return val_forall("_z", p_iff(val_mem(val_str("_z"), val_str(a)), val_mem(val_str("_z"), val_str(b))));
}

static bool zfc_built = false;

static void build_zfc(void) {
    if (zfc_built) return;
    /* Extensionality */
    zfc_axioms[0] = val_forall("x", val_forall("y", val_implies(
        val_forall("z", p_iff(val_mem(val_str("z"),val_str("x")), val_mem(val_str("z"),val_str("y")))),
        val_forall("z", p_iff(val_mem(val_str("x"),val_str("z")), val_mem(val_str("y"),val_str("z")))))));
    /* EmptySet */
    zfc_axioms[1] = p_exists("b", val_forall("x", val_neg(val_mem(val_str("x"),val_str("b")))));
    /* Pairing */
    zfc_axioms[2] = val_forall("x", val_forall("y", p_exists("b", val_forall("z",
        p_iff(val_mem(val_str("z"),val_str("b")), p_or(p_eqv("z","x"), p_eqv("z","y")))))));
    /* Union */
    zfc_axioms[3] = val_forall("a", p_exists("b", val_forall("x",
        p_iff(val_mem(val_str("x"),val_str("b")), p_exists("y", p_and(val_mem(val_str("y"),val_str("a")), val_mem(val_str("x"),val_str("y"))))))));
    /* PowerSet */
    zfc_axioms[4] = val_forall("a", p_exists("b", val_forall("x",
        p_iff(val_mem(val_str("x"),val_str("b")), val_forall("y", val_implies(val_mem(val_str("y"),val_str("x")), val_mem(val_str("y"),val_str("a"))))))));
    /* Infinity */
    zfc_axioms[5] = p_exists("b", p_and(
        p_exists("e", p_and(val_mem(val_str("e"),val_str("b")), val_forall("z", val_neg(val_mem(val_str("z"),val_str("e")))))),
        val_forall("y", val_implies(val_mem(val_str("y"),val_str("b")),
            p_exists("s", p_and(val_mem(val_str("s"),val_str("b")),
                val_forall("w", p_iff(val_mem(val_str("w"),val_str("s")), p_or(val_mem(val_str("w"),val_str("y")), p_eqv("w","y"))))))))));
    /* Regularity */
    zfc_axioms[6] = val_forall("a", val_implies(
        p_exists("y", val_mem(val_str("y"),val_str("a"))),
        p_exists("y", p_and(val_mem(val_str("y"),val_str("a")), val_neg(p_exists("z", p_and(val_mem(val_str("z"),val_str("a")), val_mem(val_str("z"),val_str("y")))))))));
    /* Choice */
    zfc_axioms[7] = val_forall("x", val_implies(
        val_forall("y", val_implies(val_mem(val_str("y"),val_str("x")), p_exists("z", val_mem(val_str("z"),val_str("y"))))),
        p_exists("c", val_forall("y", val_implies(val_mem(val_str("y"),val_str("x")),
            p_exists("z", p_and(p_and(val_mem(val_str("z"),val_str("y")), val_mem(val_str("z"),val_str("c"))),
                val_forall("w", val_implies(p_and(val_mem(val_str("w"),val_str("y")), val_mem(val_str("w"),val_str("c"))), p_eqv("w","z"))))))))));
    zfc_built = true;
}

static bool match_zfc(Val *f, int idx) {
    build_zfc();
    return same(f, zfc_axioms[idx]);
}

bool is_axiom(Val *f, const char *system) {
    int limit = 7;
    if (strcmp(system, "zfc") == 0) limit = 8;

    for (int i = 0; i < limit; i++)
        if (match_zfc(f, i)) return true;

    if (is_separation(f)) return true;
    if ((strcmp(system, "zf") == 0 || strcmp(system, "zfc") == 0) && is_replacement(f))
        return true;
    return false;
}
