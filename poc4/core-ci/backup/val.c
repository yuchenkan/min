#include "val.h"
#include "parse.h"

/* ============================================================
 * Error handling
 * ============================================================ */

void die(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    exit(1);
}

/* ============================================================
 * Value singletons
 * ============================================================ */

Val val_nil_v = { .tag = V_NIL };
Val val_true_v = { .tag = V_BOOL, .b = true };
Val val_false_v = { .tag = V_BOOL, .b = false };

/* ============================================================
 * Value constructors
 * ============================================================ */

Val *val_int(int i) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_INT; v->i = i;
    return v;
}

Val *val_str(const char *s) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_STR; v->s = strdup(s);
    return v;
}

Val *val_list(Val **items, int len) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_LIST;
    v->list.items = gc_alloc(sizeof(Val*) * (len > 0 ? len : 1), GC_KIND_RAW);
    memcpy(v->list.items, items, sizeof(Val*) * len);
    v->list.len = len;
    return v;
}

Val *val_builtin(BuiltinFn fn, const char *name, bool nocache) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_BUILTIN;
    v->builtin.fn = fn;
    v->builtin.name = name;
    v->builtin.nocache = nocache;
    return v;
}

Val *val_mem(Val *left, Val *right) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_MEM; v->mem.left = left; v->mem.right = right;
    return v;
}

Val *val_neg(Val *operand) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_NEG; v->neg.operand = operand;
    return v;
}

Val *val_implies(Val *left, Val *right) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_IMPLIES; v->implies.left = left; v->implies.right = right;
    return v;
}

Val *val_forall(const char *var, Val *body) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_FORALL; v->forall.var = strdup(var); v->forall.body = body;
    return v;
}

Val *val_proof(Val **left, int nleft, Val **right, int nright) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_PROOF;
    v->proof.left = gc_alloc(sizeof(Val*) * (nleft > 0 ? nleft : 1), GC_KIND_RAW);
    memcpy(v->proof.left, left, sizeof(Val*) * nleft);
    v->proof.nleft = nleft;
    v->proof.right = gc_alloc(sizeof(Val*) * (nright > 0 ? nright : 1), GC_KIND_RAW);
    memcpy(v->proof.right, right, sizeof(Val*) * nright);
    v->proof.nright = nright;
    return v;
}

/* ============================================================
 * Environment
 * ============================================================ */

Env *env_new(void) {
    Env *e = gc_alloc(sizeof(Env), GC_KIND_ENV);
    e->cap = 16;
    e->entries = gc_alloc(sizeof(EnvEntry) * e->cap, GC_KIND_RAW);
    e->len = 0;
    return e;
}

Env *env_snapshot(Env *e) {
    Env *n = gc_alloc(sizeof(Env), GC_KIND_ENV);
    n->cap = e->len > 8 ? e->len * 2 : 16;
    n->entries = gc_alloc(sizeof(EnvEntry) * n->cap, GC_KIND_RAW);
    memcpy(n->entries, e->entries, sizeof(EnvEntry) * e->len);
    n->len = e->len;
    return n;
}

void env_set(Env *e, const char *name, Val *val) {
    /* overwrite if exists */
    for (int i = e->len - 1; i >= 0; i--)
        if (strcmp(e->entries[i].name, name) == 0) { e->entries[i].val = val; return; }
    if (e->len >= e->cap) {
        e->cap *= 2;
        EnvEntry *ne = gc_alloc(sizeof(EnvEntry) * e->cap, GC_KIND_RAW);
        memcpy(ne, e->entries, sizeof(EnvEntry) * e->len);
        e->entries = ne;
    }
    e->entries[e->len].name = name;
    e->entries[e->len].val = val;
    e->len++;
}

Val *env_get(Env *e, const char *name) {
    for (int i = e->len - 1; i >= 0; i--)
        if (strcmp(e->entries[i].name, name) == 0) return e->entries[i].val;
    return NULL;
}
