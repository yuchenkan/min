#ifndef VAL_H
#define VAL_H

#include <stdbool.h>
#include <stdarg.h>
#include "gc.h"

/* ============================================================
 * Error handling
 * ============================================================ */

void die(const char *fmt, ...);

/* ============================================================
 * Values
 * ============================================================ */

typedef enum {
    V_NIL, V_BOOL, V_INT, V_STR,
    V_LIST, V_FN, V_BUILTIN,
    /* kernel formula types */
    V_MEM, V_NEG, V_IMPLIES, V_FORALL,
    /* kernel proof types */
    V_PROOF,
} ValTag;

typedef Val *(*BuiltinFn)(Val **args, int nargs);

struct Val {
    ValTag tag;
    union {
        bool b;
        int i;
        const char *s;                  struct { Val **items; int len; } list;
        struct { const char **params; int nparams; int body; Env *env; } fn;
        /* body is index into global AST node array */
        struct { BuiltinFn fn; const char *name; bool nocache; } builtin;
        /* kernel formulas */
        struct { Val *left; Val *right; } mem;
        struct { Val *operand; } neg;
        struct { Val *left; Val *right; } implies;
        struct { const char *var; Val *body; } forall;
        /* kernel proof */
        struct { Val **left; int nleft; Val **right; int nright; } proof;
    };
};

/* ============================================================
 * Environment
 * ============================================================ */

typedef struct EnvEntry {
    const char *name;       Val *val;
} EnvEntry;

struct Env {
    EnvEntry *entries;
    int len;
    int cap;
};

/* Singletons */
extern Val val_nil_v;
extern Val val_true_v;
extern Val val_false_v;

#define VAL_NIL (&val_nil_v)
#define VAL_TRUE (&val_true_v)
#define VAL_FALSE (&val_false_v)

/* Constructors */
Val *val_int(int i);
Val *val_str(const char *s);
Val *val_list(Val **items, int len);
Val *val_builtin(BuiltinFn fn, const char *name, bool nocache);
Val *val_mem(Val *left, Val *right);
Val *val_neg(Val *operand);
Val *val_implies(Val *left, Val *right);
Val *val_forall(const char *var, Val *body);
Val *val_proof(Val **left, int nleft, Val **right, int nright);

/* Environment */
Env *env_new(void);
Env *env_snapshot(Env *e);
void env_set(Env *e, const char *name, Val *val);
Val *env_get(Env *e, const char *name);

#endif
