#include "val.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

/* ============================================================
 * Internal types
 * ============================================================ */

enum { TAG_NIL, TAG_BOOL, TAG_INT, TAG_STR, TAG_LIST, TAG_FN, TAG_BUILTIN };

struct Val {
    GCObject *gc;
    int tag;
    union {
        bool b;
        struct { GCObject *data; int len; } integer;  /* uint32_t[] via gc_data */
        struct { GCObject *data; } str;                /* char[] via gc_data */
        struct { GCObject *data; int len; } list;      /* Val*[] via gc_data */
        struct { GCObject *data; int nparams;          /* const char*[] via gc_data */
                 Val *body; Env *env; } fn;
        struct { BuiltinFn fn; const char *name; bool nocache; } builtin;
    };
};

typedef struct { const char *name; Val *val; } EnvEntry;

struct Env {
    GCObject *gc;
    GCObject *data;     /* EnvEntry[] via gc_data */
    int len;
    int cap;
};

/* ============================================================
 * Singletons
 * ============================================================ */

Val *val_nil;
Val *val_true;
Val *val_false;

static Val *make_singleton(int tag, bool b) {
    GCObject *obj = gc_alloc(sizeof(Val), NULL);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = tag;
    v->b = b;
    gc_retain(obj);  /* prevent collection */
    return v;
}

void val_init(void) {
    val_nil   = make_singleton(TAG_NIL, false);
    val_true  = make_singleton(TAG_BOOL, true);
    val_false = make_singleton(TAG_BOOL, false);
}

/* ============================================================
 * Trace functions
 * ============================================================ */

static void mark_val(Val *v) {
    gc_mark(v->gc);
}

static void trace_int(GCObject *obj) {
    Val *v = gc_data(obj);
    gc_mark(v->integer.data);
}

static void trace_str(GCObject *obj) {
    Val *v = gc_data(obj);
    gc_mark(v->str.data);
}

static void trace_list(GCObject *obj) {
    Val *v = gc_data(obj);
    gc_mark(v->list.data);
    Val **items = gc_data(v->list.data);
    for (int i = 0; i < v->list.len; i++)
        mark_val(items[i]);
}

static void trace_fn(GCObject *obj) {
    Val *v = gc_data(obj);
    gc_mark(v->fn.data);
    mark_val(v->fn.body);
    gc_mark(v->fn.env->gc);
}

static void trace_env(GCObject *obj) {
    Env *e = gc_data(obj);
    gc_mark(e->data);
    EnvEntry *entries = gc_data(e->data);
    for (int i = 0; i < e->len; i++)
        mark_val(entries[i].val);
}

/* ============================================================
 * Constructors
 * ============================================================ */

Val *val_int(const uint32_t *limbs, int len) {
    GCObject *data = gc_alloc(sizeof(uint32_t) * len, NULL);
    memcpy(gc_data(data), limbs, sizeof(uint32_t) * len);

    GCObject *obj = gc_alloc(sizeof(Val), trace_int);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = TAG_INT;
    v->integer.data = data;
    v->integer.len = len;
    return v;
}

Val *val_str(const char *s) {
    size_t slen = strlen(s) + 1;
    GCObject *data = gc_alloc(slen, NULL);
    memcpy(gc_data(data), s, slen);

    GCObject *obj = gc_alloc(sizeof(Val), trace_str);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = TAG_STR;
    v->str.data = data;
    return v;
}

Val *val_list(Val **items, int len) {
    GCObject *data = gc_alloc(sizeof(Val *) * len, NULL);
    memcpy(gc_data(data), items, sizeof(Val *) * len);

    GCObject *obj = gc_alloc(sizeof(Val), trace_list);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = TAG_LIST;
    v->list.data = data;
    v->list.len = len;
    return v;
}

Val *val_fn(const char **params, int nparams, Val *body, Env *env) {
    GCObject *data = gc_alloc(sizeof(const char *) * nparams, NULL);
    memcpy(gc_data(data), params, sizeof(const char *) * nparams);

    GCObject *obj = gc_alloc(sizeof(Val), trace_fn);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = TAG_FN;
    v->fn.data = data;
    v->fn.nparams = nparams;
    v->fn.body = body;
    v->fn.env = env;
    return v;
}

Val *val_builtin(BuiltinFn fn, const char *name, bool nocache) {
    GCObject *obj = gc_alloc(sizeof(Val), NULL);
    Val *v = gc_data(obj);
    v->gc = obj;
    v->tag = TAG_BUILTIN;
    v->builtin.fn = fn;
    v->builtin.name = name;
    v->builtin.nocache = nocache;
    return v;
}

/* ============================================================
 * Environment
 * ============================================================ */

Env *env_new(void) {
    GCObject *data = gc_alloc(sizeof(EnvEntry) * 16, NULL);

    GCObject *obj = gc_alloc(sizeof(Env), trace_env);
    Env *e = gc_data(obj);
    e->gc = obj;
    e->data = data;
    e->len = 0;
    e->cap = 16;
    return e;
}

Env *env_snapshot(Env *e) {
    int cap = e->len * 2;
    GCObject *data = gc_alloc(sizeof(EnvEntry) * cap, NULL);
    memcpy(gc_data(data), gc_data(e->data), sizeof(EnvEntry) * e->len);

    GCObject *obj = gc_alloc(sizeof(Env), trace_env);
    Env *n = gc_data(obj);
    n->gc = obj;
    n->data = data;
    n->len = e->len;
    n->cap = cap;
    return n;
}

void env_set(Env *e, const char *name, Val *val) {
    EnvEntry *entries = gc_data(e->data);
    for (int i = e->len - 1; i >= 0; i--)
        if (strcmp(entries[i].name, name) == 0) {
            entries[i].val = val;
            return;
        }
    if (e->len >= e->cap) {
        e->cap *= 2;
        GCObject *data = gc_alloc(sizeof(EnvEntry) * e->cap, NULL);
        memcpy(gc_data(data), gc_data(e->data), sizeof(EnvEntry) * e->len);
        e->data = data;
        entries = gc_data(data);
    }
    entries[e->len].name = name;
    entries[e->len].val = val;
    e->len++;
}

Val *env_get(Env *e, const char *name) {
    EnvEntry *entries = gc_data(e->data);
    for (int i = e->len - 1; i >= 0; i--)
        if (strcmp(entries[i].name, name) == 0)
            return entries[i].val;
    return NULL;
}
