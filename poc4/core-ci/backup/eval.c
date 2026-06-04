#include "eval.h"

/* ============================================================
 * File loading state
 * ============================================================ */

LoadedFile loaded_files[MAX_LOADED];
int nloaded = 0;
const char *root_dir = NULL;

/* ============================================================
 * Evaluator
 * ============================================================ */

Val *eval(int nid, Env *env) {
    ASTNode *n = &nodes[nid];

    switch (n->tag) {
    case N_LIT_INT: return val_int(n->lit_int);
    case N_LIT_STR: return val_str(n->lit_str);
    case N_REF: {
        Val *v = env_get(env, n->ref_name);
        if (!v) die("%s:%d:%d: undefined: %s", n->file, n->line, n->col, n->ref_name);
        return v;
    }
    case N_FN: {
        Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
        v->tag = V_FN;
        v->fn.params = n->fn.params;
        v->fn.nparams = n->fn.nparams;
        v->fn.body = n->fn.body;
        v->fn.env = env_snapshot(env);
        return v;
    }
    case N_CALL: {
        Val *callee = eval(n->call.callee, env);
        Val *args[64];
        for (int i = 0; i < n->call.nargs; i++)
            args[i] = eval(n->call.args[i], env);
        return do_call(callee, args, n->call.nargs, nid);
    }
    case N_LIST: {
        Val *items[256];
        for (int i = 0; i < n->list.nelems; i++)
            items[i] = eval(n->list.elems[i], env);
        return val_list(items, n->list.nelems);
    }
    case N_IF: {
        Val *c = eval(n->if_.cond, env);
        if (c->tag != V_BOOL) die("%s:%d:%d: condition must be bool", n->file, n->line, n->col);
        return c->b ? eval(n->if_.then_, env) : eval(n->if_.else_, env);
    }
    case N_BLOCK: {
        Env *be = env_snapshot(env);
        for (int i = 0; i < n->block.nbinds; i++) {
            ASTNode *b = &nodes[n->block.binds[i]];
            Val *v = eval(b->bind.expr, be);
            env_set(be, b->bind.name, v);
        }
        return eval(n->block.expr, be);
    }
    default:
        die("eval: unknown node tag %d", n->tag);
        return NULL;
    }
}

Val *do_call(Val *callee, Val **args, int nargs, int call_node) {
    if (callee->tag == V_BUILTIN) {
        return callee->builtin.fn(args, nargs);
    }
    if (callee->tag == V_FN) {
        Env *e = env_snapshot(callee->fn.env);
        gc_push_root(e);
        for (int i = 0; i < callee->fn.nparams; i++)
            env_set(e, callee->fn.params[i], i < nargs ? args[i] : VAL_NIL);
        Val *result = eval(callee->fn.body, e);
        gc_pop_root();
        return result;
    }
    die("%s:%d:%d: cannot call non-function",
        nodes[call_node].file, nodes[call_node].line, nodes[call_node].col);
    return NULL;
}

/* ============================================================
 * Builtins
 * ============================================================ */

static Val *builtin_add(Val **args, int n) {
    Val *a = args[0], *b = args[1];
    if (a->tag == V_STR && b->tag == V_STR) {
        char buf[8192];
        snprintf(buf, sizeof(buf), "%s%s", a->s, b->s);
        return val_str(buf);
    }
    if (a->tag == V_LIST && b->tag == V_LIST) {
        int len = a->list.len + b->list.len;
        Val **items = gc_alloc(sizeof(Val*) * (len > 0 ? len : 1), GC_KIND_RAW);
        memcpy(items, a->list.items, sizeof(Val*) * a->list.len);
        memcpy(items + a->list.len, b->list.items, sizeof(Val*) * b->list.len);
        return val_list(items, len);
    }
    if (a->tag == V_INT && b->tag == V_INT) return val_int(a->i + b->i);
    die("add: type mismatch");
    return NULL;
}

static Val *builtin_sub(Val **args, int n) { return val_int(args[0]->i - args[1]->i); }
static Val *builtin_mul(Val **args, int n) { return val_int(args[0]->i * args[1]->i); }
static Val *builtin_gt(Val **args, int n) { return args[0]->i > args[1]->i ? VAL_TRUE : VAL_FALSE; }

static Val *builtin_str(Val **args, int n) {
    char buf[64];
    snprintf(buf, sizeof(buf), "%d", args[0]->i);
    return val_str(buf);
}

static Val *builtin_eq(Val **args, int n) {
    Val *a = args[0], *b = args[1];
    if (a->tag == V_STR && b->tag == V_STR) return a->s == b->s ? VAL_TRUE : VAL_FALSE;
    if (a->tag == V_INT && b->tag == V_INT) return a->i == b->i ? VAL_TRUE : VAL_FALSE;
    if (a->tag == V_BOOL && b->tag == V_BOOL) return a->b == b->b ? VAL_TRUE : VAL_FALSE;
    if (a == b) return VAL_TRUE;
    return VAL_FALSE;
}

static Val *builtin_not(Val **args, int n) { return args[0]->b ? VAL_FALSE : VAL_TRUE; }
static Val *builtin_head(Val **args, int n) { return args[0]->list.items[0]; }
static Val *builtin_tail(Val **args, int n) {
    Val *l = args[0];
    return val_list(l->list.items + 1, l->list.len - 1);
}
static Val *builtin_nth(Val **args, int n) { return args[0]->list.items[args[1]->i]; }
static Val *builtin_len(Val **args, int n) { return val_int(args[0]->list.len); }

static Val *builtin_print(Val **args, int n) {
    Val *v = args[0];
    if (v->tag == V_STR) printf("%s\n", v->s);
    else if (v->tag == V_INT) printf("%d\n", v->i);
    else if (v->tag == V_BOOL) printf("%s\n", v->b ? "true" : "false");
    else printf("<val:%d>\n", v->tag);
    return v;
}

static Val *builtin_fail(Val **args, int n) {
    die("%s", args[0]->tag == V_STR ? args[0]->s : "fail");
    return NULL;
}

static Val *builtin_do_proof(Val **args, int n) {
    Val *left_list = args[0], *right_list = args[1];
    const char *rule = args[2]->s;
    Val *premises_list = args[3];
    Val *principal_raw = args[4];
    Val *term_val = args[5];

    /* build formulas */
    int nleft = left_list->list.len;
    Val **left = gc_alloc(sizeof(Val*) * (nleft > 0 ? nleft : 1), GC_KIND_RAW);
    for (int i = 0; i < nleft; i++) left[i] = build_formula(left_list->list.items[i]);

    int nright = right_list->list.len;
    Val **right = gc_alloc(sizeof(Val*) * (nright > 0 ? nright : 1), GC_KIND_RAW);
    for (int i = 0; i < nright; i++) right[i] = build_formula(right_list->list.items[i]);

    Val *principal = build_formula(principal_raw);

    int nprem = premises_list->list.len;
    Val **premises = gc_alloc(sizeof(Val*) * (nprem > 0 ? nprem : 1), GC_KIND_RAW);
    for (int i = 0; i < nprem; i++) premises[i] = premises_list->list.items[i];

    const char *term = (term_val && term_val->tag == V_STR) ? term_val->s : NULL;

    /* check duplicates in left/right */
    for (int i = 0; i < nleft; i++)
        for (int j = i+1; j < nleft; j++)
            if (same(left[i], left[j])) {
                Val *items[2] = { VAL_FALSE, val_str("sequent: duplicate formula in left") };
                return val_list(items, 2);
            }
    for (int i = 0; i < nright; i++)
        for (int j = i+1; j < nright; j++)
            if (same(right[i], right[j])) {
                Val *items[2] = { VAL_FALSE, val_str("sequent: duplicate formula in right") };
                return val_list(items, 2);
            }

    const char *err = check_rule(left, nleft, right, nright, rule, premises, nprem, principal, term);
    if (err) {
        Val *items[2] = { VAL_FALSE, val_str(err) };
        return val_list(items, 2);
    }

    Val *proof = val_proof(left, nleft, right, nright);
    Val *items[2] = { VAL_TRUE, proof };
    return val_list(items, 2);
}

static Val *builtin_do_qed(Val **args, int n) {
    Val *proof = args[0];
    Val *expected_raw = args[1];
    const char *system = args[2]->tag == V_STR ? args[2]->s : "z";

    Val *expected = build_formula(expected_raw);

    if (proof->tag != V_PROOF) {
        Val *items[2] = { VAL_FALSE, val_str("qed: not a proof") };
        return val_list(items, 2);
    }
    if (proof->proof.nright != 1) {
        Val *items[2] = { VAL_FALSE, val_str("qed: expected 1 formula on right") };
        return val_list(items, 2);
    }
    VarSet *fv = varset_new();
    collect_free_vars(proof->proof.right[0], varset_new(), fv);
    if (fv->len > 0) {
        Val *items[2] = { VAL_FALSE, val_str("qed: theorem has free variables") };
        return val_list(items, 2);
    }
    for (int i = 0; i < proof->proof.nleft; i++) {
        if (!is_axiom(proof->proof.left[i], system)) {
            Val *items[2] = { VAL_FALSE, val_str("qed: non-axiom on left") };
            return val_list(items, 2);
        }
    }
    if (!same(proof->proof.right[0], expected)) {
        Val *items[2] = { VAL_FALSE, val_str("qed: theorem does not match expected") };
        return val_list(items, 2);
    }
    Val *items[2] = { VAL_TRUE, VAL_NIL };
    return val_list(items, 2);
}

/* ============================================================
 * Global environment
 * ============================================================ */

Env *make_global(void) {
    Env *e = env_new();
    env_set(e, "true", VAL_TRUE);
    env_set(e, "false", VAL_FALSE);
    env_set(e, "none", VAL_NIL);
    env_set(e, "add", val_builtin(builtin_add, "add", false));
    env_set(e, "sub", val_builtin(builtin_sub, "sub", false));
    env_set(e, "mul", val_builtin(builtin_mul, "mul", false));
    env_set(e, "gt", val_builtin(builtin_gt, "gt", false));
    env_set(e, "str", val_builtin(builtin_str, "str", false));
    env_set(e, "eq", val_builtin(builtin_eq, "eq", false));
    env_set(e, "not", val_builtin(builtin_not, "not", false));
    env_set(e, "head", val_builtin(builtin_head, "head", false));
    env_set(e, "tail", val_builtin(builtin_tail, "tail", false));
    env_set(e, "nth", val_builtin(builtin_nth, "nth", false));
    env_set(e, "len", val_builtin(builtin_len, "len", false));
    env_set(e, "print", val_builtin(builtin_print, "print", true));
    env_set(e, "_do_proof", val_builtin(builtin_do_proof, "_do_proof", false));
    env_set(e, "_do_qed", val_builtin(builtin_do_qed, "_do_qed", false));
    env_set(e, "_fail", val_builtin(builtin_fail, "_fail", true));
    return e;
}

/* ============================================================
 * File loading
 * ============================================================ */

char *read_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open: %s", path);
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = gc_alloc(len + 1, GC_KIND_RAW);
    fread(buf, 1, len, f);
    buf[len] = 0;
    fclose(f);
    return buf;
}

void load_import(ASTNode *n, Env *env) {
    /* build filepath from module name */
    char filepath[1024];
    snprintf(filepath, sizeof(filepath), "%s/", root_dir);
    const char *m = n->import.module;
    for (const char *c = m; *c; c++) {
        int len = strlen(filepath);
        if (*c == '.') filepath[len] = '/';
        else filepath[len] = *c;
        filepath[len+1] = 0;
    }
    strcat(filepath, ".min");

    Env *imported = load_file(filepath);
    if (!imported) return;

    for (int i = 0; i < n->import.nnames; i++) {
        const char *name = n->import.names[i];
        const char *alias = n->import.aliases[i];
        if (name[0] == '_') die("cannot import private name \"%s\"", name);
        Val *v = env_get(imported, name);
        if (v) env_set(env, alias, v);
    }
}

Env *load_file(const char *filepath) {
    /* check cache */
    for (int i = 0; i < nloaded; i++)
        if (strcmp(loaded_files[i].filepath, filepath) == 0) return loaded_files[i].exports;

    /* mark as loading */
    Env *exports = env_new();
    loaded_files[nloaded].filepath = strdup(filepath);
    loaded_files[nloaded].exports = exports;
    nloaded++;

    char *source = read_file(filepath);
    TokenList tl = tokenize(source, filepath);
    Parser p = { tl, 0, filepath };
    Program prog = parse_program(&p);

    Env *env = make_global();

    for (int i = 0; i < prog.nitems; i++) {
        ASTNode *n = &nodes[prog.items[i]];
        if (n->tag == N_IMPORT) {
            load_import(n, env);
        } else if (n->tag == N_BIND) {
            Val *v = eval(n->bind.expr, env);
            env_set(env, n->bind.name, v);
            env_set(exports, n->bind.name, v);
        }
    }

    return exports;
}
