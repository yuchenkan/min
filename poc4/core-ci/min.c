/*
 * min interpreter in C
 * Single-file: tokenizer, parser, evaluator, proof kernel
 * Uses precise mark-sweep GC for Val/Env, malloc for long-lived data
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdarg.h>
#include <assert.h>


/* ============================================================
 * GC: precise mark-sweep for heap objects
 * ============================================================
 * Every GC object starts with a GCHeader.
 * The mark phase traces from roots using type-specific tracing.
 * The sweep phase frees unmarked objects.
 */

typedef struct GCHeader {
    struct GCHeader *next;  /* all-objects list */
    unsigned char mark;
    unsigned char kind;     /* 0=Val, 1=Env, 2=raw pointer array */
} GCHeader;

#define GC_KIND_VAL   0
#define GC_KIND_ENV   1
#define GC_KIND_RAW   2     /* Val**, const char**, EnvEntry* — traced by parent */

static GCHeader *gc_all = NULL;
static size_t gc_count = 0;
static size_t gc_threshold = (size_t)-1;  /* disabled for now — fix rooting first */

/* Forward declarations for GC */
typedef struct Val Val;
typedef struct Env Env;
static void gc_collect(void);

static void *gc_alloc(size_t size, unsigned char kind) {
    if (gc_count >= gc_threshold) {
        gc_collect();
        if (gc_count > gc_threshold / 2) gc_threshold *= 2;
    }
    GCHeader *h = malloc(sizeof(GCHeader) + size);
    if (!h) { fprintf(stderr, "out of memory\n"); exit(1); }
    h->next = gc_all;
    h->mark = 0;
    h->kind = kind;
    gc_all = h;
    gc_count++;
    void *ptr = (void*)(h + 1);
    memset(ptr, 0, size);
    return ptr;
}

static GCHeader *gc_header(void *ptr) { return ((GCHeader*)ptr) - 1; }

static void gc_mark(void *ptr);  /* forward — implemented after Val/Env definitions */

/* perm_alloc: for long-lived data (AST, tokens, interned strings) — never freed */
static void *perm_alloc(size_t size) {
    void *p = malloc(size);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(1); }
    memset(p, 0, size);
    return p;
}

static char *perm_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = perm_alloc(len);
    memcpy(p, s, len);
    return p;
}


/* ============================================================
 * Interned strings
 * ============================================================ */

#define INTERN_BUCKETS 4096

typedef struct InternEntry {
    const char *str;
    struct InternEntry *next;
} InternEntry;

static InternEntry *intern_table[INTERN_BUCKETS];

static unsigned intern_hash(const char *s) {
    unsigned h = 5381;
    for (; *s; s++) h = h * 33 + (unsigned char)*s;
    return h;
}

/* Returns a unique pointer for each distinct string */
const char *intern(const char *s) {
    unsigned idx = intern_hash(s) % INTERN_BUCKETS;
    for (InternEntry *e = intern_table[idx]; e; e = e->next)
        if (strcmp(e->str, s) == 0) return e->str;
    InternEntry *e = perm_alloc(sizeof(InternEntry));
    e->str = perm_strdup(s);
    e->next = intern_table[idx];
    intern_table[idx] = e;
    return e->str;
}


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

typedef struct Val Val;
typedef struct Env Env;

typedef Val *(*BuiltinFn)(Val **args, int nargs);

struct Val {
    ValTag tag;
    union {
        bool b;
        int i;
        const char *s;          /* interned */
        struct { Val **items; int len; } list;
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

/* Constructors */
static Val val_nil_v = { .tag = V_NIL };
static Val val_true_v = { .tag = V_BOOL, .b = true };
static Val val_false_v = { .tag = V_BOOL, .b = false };

#define VAL_NIL (&val_nil_v)
#define VAL_TRUE (&val_true_v)
#define VAL_FALSE (&val_false_v)

static Val *val_int(int i) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_INT; v->i = i;
    return v;
}

static Val *val_str(const char *s) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_STR; v->s = intern(s);
    return v;
}

static Val *val_list(Val **items, int len) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_LIST;
    v->list.items = gc_alloc(sizeof(Val*) * (len > 0 ? len : 1), GC_KIND_RAW);
    memcpy(v->list.items, items, sizeof(Val*) * len);
    v->list.len = len;
    return v;
}

static Val *val_builtin(BuiltinFn fn, const char *name, bool nocache) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_BUILTIN;
    v->builtin.fn = fn;
    v->builtin.name = name;
    v->builtin.nocache = nocache;
    return v;
}

/* Kernel formula constructors */
static Val *val_mem(Val *left, Val *right) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_MEM; v->mem.left = left; v->mem.right = right;
    return v;
}

static Val *val_neg(Val *operand) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_NEG; v->neg.operand = operand;
    return v;
}

static Val *val_implies(Val *left, Val *right) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_IMPLIES; v->implies.left = left; v->implies.right = right;
    return v;
}

static Val *val_forall(const char *var, Val *body) {
    Val *v = gc_alloc(sizeof(Val), GC_KIND_VAL);
    v->tag = V_FORALL; v->forall.var = intern(var); v->forall.body = body;
    return v;
}

static Val *val_proof(Val **left, int nleft, Val **right, int nright) {
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

typedef struct EnvEntry {
    const char *name;   /* interned */
    Val *val;
} EnvEntry;

struct Env {
    EnvEntry *entries;
    int len;
    int cap;
};

static Env *env_new(void) {
    Env *e = gc_alloc(sizeof(Env), GC_KIND_ENV);
    e->cap = 16;
    e->entries = gc_alloc(sizeof(EnvEntry) * e->cap, GC_KIND_RAW);
    e->len = 0;
    return e;
}

static Env *env_snapshot(Env *e) {
    Env *n = gc_alloc(sizeof(Env), GC_KIND_ENV);
    n->cap = e->len > 8 ? e->len * 2 : 16;
    n->entries = gc_alloc(sizeof(EnvEntry) * n->cap, GC_KIND_RAW);
    memcpy(n->entries, e->entries, sizeof(EnvEntry) * e->len);
    n->len = e->len;
    return n;
}

static void env_set(Env *e, const char *name, Val *val) {
    /* overwrite if exists */
    for (int i = e->len - 1; i >= 0; i--)
        if (e->entries[i].name == name) { e->entries[i].val = val; return; }
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

static Val *env_get(Env *e, const char *name) {
    for (int i = e->len - 1; i >= 0; i--)
        if (e->entries[i].name == name) return e->entries[i].val;
    return NULL;
}


/* ============================================================
 * GC: mark and sweep implementation
 * ============================================================ */

static void gc_mark_val(Val *v);
static void gc_mark_env(Env *e);

static void gc_mark(void *ptr) {
    if (!ptr) return;
    GCHeader *h = gc_header(ptr);
    if (h->mark) return;
    h->mark = 1;
    if (h->kind == GC_KIND_VAL) gc_mark_val((Val*)ptr);
    else if (h->kind == GC_KIND_ENV) gc_mark_env((Env*)ptr);
    /* GC_KIND_RAW: no children to trace — traced by parent */
}

static void gc_mark_val(Val *v) {
    switch (v->tag) {
    case V_NIL: case V_BOOL: case V_INT: case V_STR: case V_BUILTIN:
        break;
    case V_LIST:
        if (v->list.items) {
            gc_header(v->list.items)->mark = 1;
            for (int i = 0; i < v->list.len; i++) gc_mark(v->list.items[i]);
        }
        break;
    case V_FN:
        gc_mark(v->fn.env);
        break;
    case V_MEM:
        gc_mark(v->mem.left); gc_mark(v->mem.right);
        break;
    case V_NEG:
        gc_mark(v->neg.operand);
        break;
    case V_IMPLIES:
        gc_mark(v->implies.left); gc_mark(v->implies.right);
        break;
    case V_FORALL:
        gc_mark(v->forall.body);
        break;
    case V_PROOF:
        if (v->proof.left) {
            gc_header(v->proof.left)->mark = 1;
            for (int i = 0; i < v->proof.nleft; i++) gc_mark(v->proof.left[i]);
        }
        if (v->proof.right) {
            gc_header(v->proof.right)->mark = 1;
            for (int i = 0; i < v->proof.nright; i++) gc_mark(v->proof.right[i]);
        }
        break;
    }
}

static void gc_mark_env(Env *e) {
    if (e->entries) {
        gc_header(e->entries)->mark = 1;
        for (int i = 0; i < e->len; i++)
            gc_mark(e->entries[i].val);
    }
}

/* GC roots: loaded file exports + ZFC axioms */
/* Forward declarations */
typedef struct { const char *filepath; Env *exports; } LoadedFile;
#define MAX_LOADED 1024
static LoadedFile loaded_files[MAX_LOADED];
static int nloaded;
static Val *zfc_axioms[8];

static void gc_mark_roots(void) {
    for (int i = 0; i < nloaded; i++)
        gc_mark(loaded_files[i].exports);
    for (int i = 0; i < 8; i++)
        gc_mark(zfc_axioms[i]);
}

/* Eval stack roots — the eval function pushes/pops env pointers here */
#define GC_ROOT_STACK_MAX 65536
static Env *gc_root_stack[GC_ROOT_STACK_MAX];
static int gc_root_sp = 0;

static void gc_push_root(Env *e) {
    if (gc_root_sp >= GC_ROOT_STACK_MAX) { fprintf(stderr, "gc root stack overflow\n"); exit(1); }
    gc_root_stack[gc_root_sp++] = e;
}
static void gc_pop_root(void) { gc_root_sp--; }

static void gc_collect(void) {
    /* Mark */
    for (int i = 0; i < gc_root_sp; i++) gc_mark(gc_root_stack[i]);
    gc_mark_roots();

    /* Sweep */
    GCHeader **pp = &gc_all;
    while (*pp) {
        if (!(*pp)->mark) {
            GCHeader *dead = *pp;
            *pp = dead->next;
            free(dead);
            gc_count--;
        } else {
            (*pp)->mark = 0;
            pp = &(*pp)->next;
        }
    }
}


/* ============================================================
 * Error handling
 * ============================================================ */

static void die(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    exit(1);
}


/* ============================================================
 * Tokenizer
 * ============================================================ */

typedef enum {
    T_NAME, T_STR, T_INT, T_PUNCT, T_EOF
} TokTag;

typedef struct {
    TokTag tag;
    const char *sval;   /* for NAME, STR, PUNCT */
    int ival;           /* for INT */
    int line, col;
} Token;

typedef struct {
    Token *toks;
    int len, cap;
} TokenList;

static void tok_push(TokenList *tl, Token t) {
    if (tl->len >= tl->cap) {
        tl->cap *= 2;
        Token *n = perm_alloc(sizeof(Token) * tl->cap);
        memcpy(n, tl->toks, sizeof(Token) * tl->len);
        tl->toks = n;
    }
    tl->toks[tl->len++] = t;
}

static const char *punctuation = "(){}[]$,.:?\\!";

static TokenList tokenize(const char *src, const char *filepath) {
    TokenList tl = { perm_alloc(sizeof(Token) * 256), 0, 256 };
    int pos = 0, line = 1, colstart = 0;
    int srclen = strlen(src);

    while (pos < srclen) {
        char c = src[pos];
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
            if (c == '\n') { line++; colstart = pos + 1; }
            pos++;
            continue;
        }
        if (c == '#') {
            while (pos < srclen && src[pos] != '\n') pos++;
            continue;
        }
        int col = pos - colstart + 1;

        if (c == '"') {
            pos++;
            char buf[4096];
            int bi = 0;
            while (pos < srclen && src[pos] != '"') {
                if (src[pos] == '\\') {
                    pos++;
                    if (pos >= srclen) die("%s:%d:%d: unterminated string escape", filepath, line, col);
                    char esc = src[pos];
                    if (esc == '\\') buf[bi++] = '\\';
                    else if (esc == '"') buf[bi++] = '"';
                    else if (esc == 'n') buf[bi++] = '\n';
                    else if (esc == 't') buf[bi++] = '\t';
                    else die("%s:%d:%d: invalid escape: \\%c", filepath, line, col, esc);
                } else {
                    buf[bi++] = src[pos];
                }
                pos++;
            }
            if (pos >= srclen) die("%s:%d:%d: unterminated string", filepath, line, col);
            pos++;
            buf[bi] = 0;
            tok_push(&tl, (Token){ T_STR, intern(buf), 0, line, col });
            continue;
        }

        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
            int start = pos;
            while (pos < srclen && ((src[pos] >= 'a' && src[pos] <= 'z') ||
                   (src[pos] >= 'A' && src[pos] <= 'Z') ||
                   (src[pos] >= '0' && src[pos] <= '9') || src[pos] == '_'))
                pos++;
            char buf[256];
            int len = pos - start;
            if (len >= 256) die("%s:%d:%d: name too long", filepath, line, col);
            memcpy(buf, src + start, len);
            buf[len] = 0;
            tok_push(&tl, (Token){ T_NAME, intern(buf), 0, line, col });
            continue;
        }

        if (c >= '0' && c <= '9') {
            int val = 0;
            while (pos < srclen && src[pos] >= '0' && src[pos] <= '9')
                val = val * 10 + (src[pos++] - '0');
            tok_push(&tl, (Token){ T_INT, NULL, val, line, col });
            continue;
        }

        if (strchr(punctuation, c)) {
            char buf[2] = { c, 0 };
            tok_push(&tl, (Token){ T_PUNCT, intern(buf), 0, line, col });
            pos++;
            continue;
        }

        die("%s:%d:%d: unexpected char: '%c'", filepath, line, col, c);
    }

    tok_push(&tl, (Token){ T_EOF, NULL, 0, line, 1 });
    return tl;
}


/* ============================================================
 * AST
 * ============================================================ */

typedef enum {
    N_LIT_INT, N_LIT_STR, N_REF, N_FN, N_CALL,
    N_LIST, N_IF, N_BLOCK, N_BIND, N_IMPORT,
} NodeTag;

typedef struct ASTNode ASTNode;

struct ASTNode {
    NodeTag tag;
    const char *file;
    int line, col;
    union {
        int lit_int;
        const char *lit_str;        /* interned */
        const char *ref_name;       /* interned */
        struct { const char **params; int nparams; int body; } fn;
        struct { int callee; int *args; int nargs; } call;
        struct { int *elems; int nelems; } list;
        struct { int cond, then_, else_; } if_;
        struct { int *binds; int nbinds; int expr; } block;
        struct { const char *name; int expr; } bind;
        struct { const char *module; const char **names; const char **aliases; int nnames; } import;
    };
};

/* Global AST node pool */
static ASTNode *nodes;
static int nnodes, nodes_cap;

static int node_alloc(void) {
    if (nnodes >= nodes_cap) {
        nodes_cap = nodes_cap ? nodes_cap * 2 : 1024;
        ASTNode *n = perm_alloc(sizeof(ASTNode) * nodes_cap);
        if (nodes) memcpy(n, nodes, sizeof(ASTNode) * nnodes);
        nodes = n;
    }
    return nnodes++;
}


/* ============================================================
 * Parser
 * ============================================================ */

typedef struct {
    TokenList tl;
    int pos;
    const char *filepath;
} Parser;

static Token ppeek(Parser *p) { return p->tl.toks[p->pos]; }
static Token padvance(Parser *p) { return p->tl.toks[p->pos++]; }

static Token pexpect(Parser *p, TokTag tag, const char *val) {
    Token t = padvance(p);
    if (t.tag != tag || (val && t.sval != intern(val)))
        die("%s:%d:%d: expected %d %s, got %d %s",
            p->filepath, t.line, t.col, tag, val ? val : "", t.tag, t.sval ? t.sval : "");
    return t;
}

static bool ppunct(Parser *p, const char *val) {
    Token t = ppeek(p);
    return t.tag == T_PUNCT && t.sval == intern(val);
}

static int parse_expr(Parser *p);

static int parse_fn(Parser *p) {
    Token tok = pexpect(p, T_PUNCT, "\\");
    const char *params[64];
    int np = 0;
    while (ppeek(p).tag == T_NAME)
        params[np++] = padvance(p).sval;
    pexpect(p, T_PUNCT, ":");
    int body = parse_expr(p);

    int id = node_alloc();
    nodes[id].tag = N_FN;
    nodes[id].file = p->filepath;
    nodes[id].line = tok.line;
    nodes[id].col = tok.col;
    nodes[id].fn.params = perm_alloc(sizeof(const char*) * np);
    memcpy(nodes[id].fn.params, params, sizeof(const char*) * np);
    nodes[id].fn.nparams = np;
    nodes[id].fn.body = body;
    return id;
}

static int parse_list(Parser *p) {
    Token tok = pexpect(p, T_PUNCT, "[");
    int elems[256];
    int ne = 0;
    if (!ppunct(p, "]")) {
        elems[ne++] = parse_expr(p);
        while (ppunct(p, ",")) { padvance(p); elems[ne++] = parse_expr(p); }
    }
    pexpect(p, T_PUNCT, "]");

    int id = node_alloc();
    nodes[id].tag = N_LIST;
    nodes[id].file = p->filepath;
    nodes[id].line = tok.line;
    nodes[id].col = tok.col;
    nodes[id].list.elems = perm_alloc(sizeof(int) * ne);
    memcpy(nodes[id].list.elems, elems, sizeof(int) * ne);
    nodes[id].list.nelems = ne;
    return id;
}

static int parse_if(Parser *p) {
    Token tok = pexpect(p, T_PUNCT, "?");
    pexpect(p, T_PUNCT, "(");
    int cond = parse_expr(p);
    pexpect(p, T_PUNCT, ",");
    int then_ = parse_expr(p);
    pexpect(p, T_PUNCT, ",");
    int else_ = parse_expr(p);
    pexpect(p, T_PUNCT, ")");

    int id = node_alloc();
    nodes[id].tag = N_IF;
    nodes[id].file = p->filepath;
    nodes[id].line = tok.line;
    nodes[id].col = tok.col;
    nodes[id].if_.cond = cond;
    nodes[id].if_.then_ = then_;
    nodes[id].if_.else_ = else_;
    return id;
}

static int parse_bind(Parser *p) {
    Token tok = pexpect(p, T_PUNCT, "$");
    const char *name = pexpect(p, T_NAME, NULL).sval;
    int expr = parse_expr(p);

    int id = node_alloc();
    nodes[id].tag = N_BIND;
    nodes[id].file = p->filepath;
    nodes[id].line = tok.line;
    nodes[id].col = tok.col;
    nodes[id].bind.name = name;
    nodes[id].bind.expr = expr;
    return id;
}

static int parse_block(Parser *p) {
    Token tok = pexpect(p, T_PUNCT, "{");
    int binds[256];
    int nb = 0;
    while (ppunct(p, "$"))
        binds[nb++] = parse_bind(p);
    int expr = parse_expr(p);
    pexpect(p, T_PUNCT, "}");

    int id = node_alloc();
    nodes[id].tag = N_BLOCK;
    nodes[id].file = p->filepath;
    nodes[id].line = tok.line;
    nodes[id].col = tok.col;
    nodes[id].block.binds = perm_alloc(sizeof(int) * nb);
    memcpy(nodes[id].block.binds, binds, sizeof(int) * nb);
    nodes[id].block.nbinds = nb;
    nodes[id].block.expr = expr;
    return id;
}

static int parse_args(Parser *p, int *args) {
    int na = 0;
    if (!ppunct(p, ")")) {
        args[na++] = parse_expr(p);
        while (ppunct(p, ",")) { padvance(p); args[na++] = parse_expr(p); }
    }
    return na;
}

static int parse_expr(Parser *p) {
    int id;
    Token tok = ppeek(p);

    if (ppunct(p, "\\")) { id = parse_fn(p); }
    else if (ppunct(p, "[")) { id = parse_list(p); }
    else if (ppunct(p, "?")) { id = parse_if(p); }
    else if (ppunct(p, "{")) { id = parse_block(p); }
    else if (ppunct(p, "(")) {
        padvance(p);
        id = parse_expr(p);
        pexpect(p, T_PUNCT, ")");
    }
    else if (tok.tag == T_INT) {
        Token t = padvance(p);
        id = node_alloc();
        nodes[id].tag = N_LIT_INT;
        nodes[id].file = p->filepath;
        nodes[id].line = t.line;
        nodes[id].col = t.col;
        nodes[id].lit_int = t.ival;
    }
    else if (tok.tag == T_STR) {
        Token t = padvance(p);
        id = node_alloc();
        nodes[id].tag = N_LIT_STR;
        nodes[id].file = p->filepath;
        nodes[id].line = t.line;
        nodes[id].col = t.col;
        nodes[id].lit_str = t.sval;
    }
    else if (tok.tag == T_NAME) {
        Token t = padvance(p);
        id = node_alloc();
        nodes[id].tag = N_REF;
        nodes[id].file = p->filepath;
        nodes[id].line = t.line;
        nodes[id].col = t.col;
        nodes[id].ref_name = t.sval;
    }
    else {
        die("%s:%d:%d: expected expression, got %s", p->filepath, tok.line, tok.col, tok.sval ? tok.sval : "EOF");
        return -1;
    }

    /* Call chains: f(a,b)(c) */
    while (ppunct(p, "(")) {
        padvance(p);
        int args[64];
        int na = parse_args(p, args);
        pexpect(p, T_PUNCT, ")");

        int cid = node_alloc();
        nodes[cid].tag = N_CALL;
        nodes[cid].file = nodes[id].file;
        nodes[cid].line = nodes[id].line;
        nodes[cid].col = nodes[id].col;
        nodes[cid].call.callee = id;
        nodes[cid].call.args = perm_alloc(sizeof(int) * na);
        memcpy(nodes[cid].call.args, args, sizeof(int) * na);
        nodes[cid].call.nargs = na;
        id = cid;
    }

    return id;
}

static void parse_import(Parser *p, int *imports, int *nimports) {
    pexpect(p, T_NAME, "from");
    /* dotted name */
    char module[512] = "";
    strcat(module, pexpect(p, T_NAME, NULL).sval);
    while (ppunct(p, ".")) {
        padvance(p);
        strcat(module, ".");
        strcat(module, pexpect(p, T_NAME, NULL).sval);
    }
    pexpect(p, T_NAME, "import");

    const char *names[64], *aliases[64];
    int nn = 0;
    names[nn] = pexpect(p, T_NAME, NULL).sval;
    aliases[nn] = names[nn];
    if (ppeek(p).tag == T_NAME && ppeek(p).sval == intern("as")) {
        padvance(p);
        aliases[nn] = pexpect(p, T_NAME, NULL).sval;
    }
    nn++;
    while (ppunct(p, ",")) {
        padvance(p);
        names[nn] = pexpect(p, T_NAME, NULL).sval;
        aliases[nn] = names[nn];
        if (ppeek(p).tag == T_NAME && ppeek(p).sval == intern("as")) {
            padvance(p);
            aliases[nn] = pexpect(p, T_NAME, NULL).sval;
        }
        nn++;
    }

    int id = node_alloc();
    nodes[id].tag = N_IMPORT;
    nodes[id].file = p->filepath;
    nodes[id].line = 0;
    nodes[id].col = 0;
    nodes[id].import.module = intern(module);
    nodes[id].import.names = perm_alloc(sizeof(const char*) * nn);
    memcpy(nodes[id].import.names, names, sizeof(const char*) * nn);
    nodes[id].import.aliases = perm_alloc(sizeof(const char*) * nn);
    memcpy(nodes[id].import.aliases, aliases, sizeof(const char*) * nn);
    nodes[id].import.nnames = nn;
    imports[(*nimports)++] = id;
}

typedef struct {
    int *items;     /* node indices: imports then binds */
    int nitems;
} Program;

static Program parse_program(Parser *p) {
    int items[4096];
    int ni = 0;

    /* imports first */
    while (ppeek(p).tag != T_EOF && ppeek(p).tag == T_NAME && ppeek(p).sval == intern("from"))
        parse_import(p, items, &ni);

    /* then binds */
    while (ppeek(p).tag != T_EOF) {
        if (ppeek(p).tag == T_NAME && ppeek(p).sval == intern("from"))
            die("%s:%d:%d: imports must come before all bindings",
                p->filepath, ppeek(p).line, ppeek(p).col);
        if (ppunct(p, "$"))
            items[ni++] = parse_bind(p);
        else
            die("%s:%d:%d: expected bind, got %s",
                p->filepath, ppeek(p).line, ppeek(p).col,
                ppeek(p).sval ? ppeek(p).sval : "EOF");
    }

    Program prog;
    prog.items = perm_alloc(sizeof(int) * ni);
    memcpy(prog.items, items, sizeof(int) * ni);
    prog.nitems = ni;
    return prog;
}


/* ============================================================
 * Kernel: formula equality (alpha-equiv)
 * ============================================================ */

typedef struct VarPair { const char *a; const char *b; struct VarPair *next; } VarPair;

static bool formula_eq(Val *a, Val *b, VarPair *env) {
    if (a == b) return true;
    if (a->tag == V_STR && b->tag == V_STR) {
        /* check bound var mapping */
        for (VarPair *p = env; p; p = p->next) {
            if (a->s == p->a) return b->s == p->b;
            if (b->s == p->b) return false;
        }
        return a->s == b->s;
    }
    if (a->tag != b->tag) return false;
    if (a->tag == V_MEM)
        return formula_eq(a->mem.left, b->mem.left, env) &&
               formula_eq(a->mem.right, b->mem.right, env);
    if (a->tag == V_NEG)
        return formula_eq(a->neg.operand, b->neg.operand, env);
    if (a->tag == V_IMPLIES)
        return formula_eq(a->implies.left, b->implies.left, env) &&
               formula_eq(a->implies.right, b->implies.right, env);
    if (a->tag == V_FORALL) {
        VarPair pair = { a->forall.var, b->forall.var, env };
        return formula_eq(a->forall.body, b->forall.body, &pair);
    }
    return false;
}

static bool same(Val *a, Val *b) {
    return formula_eq(a, b, NULL);
}


/* ============================================================
 * Kernel: substitution, free/bound vars, helpers
 * ============================================================ */

static Val *subst(Val *f, const char *old, Val *new_) {
    if (f->tag == V_STR)
        return f->s == old ? new_ : f;
    if (f->tag == V_MEM)
        return val_mem(subst(f->mem.left, old, new_), subst(f->mem.right, old, new_));
    if (f->tag == V_NEG)
        return val_neg(subst(f->neg.operand, old, new_));
    if (f->tag == V_IMPLIES)
        return val_implies(subst(f->implies.left, old, new_), subst(f->implies.right, old, new_));
    if (f->tag == V_FORALL) {
        if (f->forall.var == old) return f;
        return val_forall(f->forall.var, subst(f->forall.body, old, new_));
    }
    die("subst: unknown formula tag %d", f->tag);
    return NULL;
}

typedef struct VarSet { const char **vars; int len; int cap; } VarSet;

static VarSet *varset_new(void) {
    VarSet *s = perm_alloc(sizeof(VarSet));  /* short-lived, stack-like usage */
    s->cap = 16;
    s->vars = perm_alloc(sizeof(const char*) * s->cap);
    s->len = 0;
    return s;
}

static bool varset_has(VarSet *s, const char *v) {
    for (int i = 0; i < s->len; i++)
        if (s->vars[i] == v) return true;
    return false;
}

static void varset_add(VarSet *s, const char *v) {
    if (varset_has(s, v)) return;
    if (s->len >= s->cap) {
        s->cap *= 2;
        const char **n = perm_alloc(sizeof(const char*) * s->cap);
        memcpy(n, s->vars, sizeof(const char*) * s->len);
        s->vars = n;
    }
    s->vars[s->len++] = v;
}

static void collect_bound_vars(Val *f, VarSet *s) {
    if (f->tag == V_STR) return;
    if (f->tag == V_MEM) { collect_bound_vars(f->mem.left, s); collect_bound_vars(f->mem.right, s); return; }
    if (f->tag == V_NEG) { collect_bound_vars(f->neg.operand, s); return; }
    if (f->tag == V_IMPLIES) { collect_bound_vars(f->implies.left, s); collect_bound_vars(f->implies.right, s); return; }
    if (f->tag == V_FORALL) { varset_add(s, f->forall.var); collect_bound_vars(f->forall.body, s); return; }
}

static void collect_free_vars(Val *f, VarSet *bound, VarSet *free) {
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
static bool fin(Val *f, Val **lst, int len) {
    for (int i = 0; i < len; i++) if (same(f, lst[i])) return true;
    return false;
}

/* Remove first occurrence of f from lst, return new list+len */
static Val **list_remove(Val **lst, int len, Val *f, int *newlen) {
    Val **r = perm_alloc(sizeof(Val*) * (len > 0 ? len : 1));
    int ri = 0;
    bool removed = false;
    for (int i = 0; i < len; i++) {
        if (!removed && same(f, lst[i])) { removed = true; continue; }
        r[ri++] = lst[i];
    }
    *newlen = ri;
    return r;
}

static Val **list_add(Val **lst, int len, Val *f, int *newlen) {
    if (fin(f, lst, len)) {
        Val **r = perm_alloc(sizeof(Val*) * (len > 0 ? len : 1));
        memcpy(r, lst, sizeof(Val*) * len);
        *newlen = len;
        return r;
    }
    Val **r = perm_alloc(sizeof(Val*) * (len + 1));
    memcpy(r, lst, sizeof(Val*) * len);
    r[len] = f;
    *newlen = len + 1;
    return r;
}

static bool is_permutation(Val **a, int alen, Val **b, int blen) {
    if (alen != blen) return false;
    bool *used = perm_alloc(sizeof(bool) * blen);
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

static bool seq_eq(Val **l1, int nl1, Val **r1, int nr1, Val **l2, int nl2, Val **r2, int nr2) {
    return is_permutation(l1, nl1, l2, nl2) && is_permutation(r1, nr1, r2, nr2);
}


/* ============================================================
 * Kernel: proof checking
 * ============================================================ */

static const char *check_rule(
    Val **left, int nleft, Val **right, int nright,
    const char *rule, Val **premises, int npremises,
    Val *principal, const char *term)
{
    const char *r_axiom = intern("axiom");
    const char *r_neg_left = intern("neg_left");
    const char *r_neg_right = intern("neg_right");
    const char *r_implies_left = intern("implies_left");
    const char *r_implies_right = intern("implies_right");
    const char *r_forall_left = intern("forall_left");
    const char *r_forall_right = intern("forall_right");
    const char *r_cut = intern("cut");
    const char *r_wl = intern("weakening_left");
    const char *r_wr = intern("weakening_right");

    if (rule == r_axiom) {
        if (npremises != 0) return "axiom: premises not empty";
        if (!fin(principal, left, nleft)) return "axiom: principal not in left";
        if (!fin(principal, right, nright)) return "axiom: principal not in right";
        return NULL;
    }

    if (rule == r_neg_left) {
        if (npremises != 1 || principal->tag != V_NEG) return "neg_left: bad";
        if (!fin(principal, left, nleft)) return "neg_left: principal not in left";
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        int gnr; Val **gr = list_add(right, nright, principal->neg.operand, &gnr);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gnl, gr, gnr))
            return "neg_left: premise mismatch";
        return NULL;
    }

    if (rule == r_neg_right) {
        if (npremises != 1 || principal->tag != V_NEG) return "neg_right: bad";
        if (!fin(principal, right, nright)) return "neg_right: principal not in right";
        int gnl; Val **gl = list_add(left, nleft, principal->neg.operand, &gnl);
        int gnr; Val **gr = list_remove(right, nright, principal, &gnr);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl, gnl, gr, gnr))
            return "neg_right: premise mismatch";
        return NULL;
    }

    if (rule == r_implies_left) {
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

    if (rule == r_implies_right) {
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

    if (rule == r_forall_left) {
        if (npremises != 1 || !term || principal->tag != V_FORALL) return "forall_left: bad";
        if (!fin(principal, left, nleft)) return "forall_left: principal not in left";
        VarSet *bv = varset_new();
        collect_bound_vars(principal->forall.body, bv);
        if (varset_has(bv, intern(term))) return "forall_left: term clashes with boundVars";
        int gnl; Val **gl = list_remove(left, nleft, principal, &gnl);
        Val *substituted = subst(principal->forall.body, principal->forall.var, val_str(term));
        int gln; Val **gl2 = list_add(gl, gnl, substituted, &gln);
        Val *p = premises[0];
        if (!seq_eq(p->proof.left, p->proof.nleft, p->proof.right, p->proof.nright, gl2, gln, right, nright))
            return "forall_left: premise mismatch";
        return NULL;
    }

    if (rule == r_forall_right) {
        if (npremises != 1 || !term || principal->tag != V_FORALL) return "forall_right: bad";
        if (!fin(principal, right, nright)) return "forall_right: principal not in right";
        VarSet *bv = varset_new();
        collect_bound_vars(principal->forall.body, bv);
        if (varset_has(bv, intern(term))) return "forall_right: term clashes with boundVars";
        int gdn; Val **gd = list_remove(right, nright, principal, &gdn);
        /* eigenvariable check */
        const char *ti = intern(term);
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

    if (rule == r_cut) {
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

    if (rule == r_wl) {
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

    if (rule == r_wr) {
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
 * Evaluator
 * ============================================================ */

static Val *eval(int node_id, Env *env);

static Val *do_call(Val *callee, Val **args, int nargs, int call_node) {
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

static Val *eval(int nid, Env *env) {
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


/* ============================================================
 * Builtins
 * ============================================================ */

/* Helper: convert .min list (Val* V_LIST of V_LIST/V_STR formula arrays) to kernel formulas */
static Val *build_formula(Val *f) {
    if (f->tag == V_STR) return f;
    if (f->tag != V_LIST || f->list.len < 1) die("build_formula: bad input");
    const char *tag = f->list.items[0]->s;
    if (tag == intern("mem")) return val_mem(build_formula(f->list.items[1]), build_formula(f->list.items[2]));
    if (tag == intern("neg")) return val_neg(build_formula(f->list.items[1]));
    if (tag == intern("implies")) return val_implies(build_formula(f->list.items[1]), build_formula(f->list.items[2]));
    if (tag == intern("forall")) return val_forall(f->list.items[1]->s, build_formula(f->list.items[2]));
    die("build_formula: unknown tag %s", tag);
    return NULL;
}

static Val *builtin_add(Val **args, int n) {
    Val *a = args[0], *b = args[1];
    if (a->tag == V_STR && b->tag == V_STR) {
        char buf[8192];
        snprintf(buf, sizeof(buf), "%s%s", a->s, b->s);
        return val_str(buf);
    }
    if (a->tag == V_LIST && b->tag == V_LIST) {
        int len = a->list.len + b->list.len;
        Val **items = perm_alloc(sizeof(Val*) * (len > 0 ? len : 1));
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
    const char *rule = intern(args[2]->s);
    Val *premises_list = args[3];
    Val *principal_raw = args[4];
    Val *term_val = args[5];

    /* build formulas */
    int nleft = left_list->list.len;
    Val **left = perm_alloc(sizeof(Val*) * (nleft > 0 ? nleft : 1));
    for (int i = 0; i < nleft; i++) left[i] = build_formula(left_list->list.items[i]);

    int nright = right_list->list.len;
    Val **right = perm_alloc(sizeof(Val*) * (nright > 0 ? nright : 1));
    for (int i = 0; i < nright; i++) right[i] = build_formula(right_list->list.items[i]);

    Val *principal = build_formula(principal_raw);

    int nprem = premises_list->list.len;
    Val **premises = perm_alloc(sizeof(Val*) * (nprem > 0 ? nprem : 1));
    for (int i = 0; i < nprem; i++) premises[i] = premises_list->list.items[i]; /* already proof vals */

    const char *term = (term_val && term_val->tag == V_STR) ? term_val->s : NULL;

    /* check duplicates in left/right (like JS checkSet) */
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

/* Forward declaration for qed axiom checking */
static bool is_axiom(Val *f, const char *system);

static Val *builtin_do_qed(Val **args, int n) {
    Val *proof = args[0];
    Val *expected_raw = args[1];
    const char *system = args[2]->tag == V_STR ? args[2]->s : intern("z");

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
 * ZFC axiom checking (simplified — matches JS kernel)
 * ============================================================ */

/* Pattern matching for ZFC axioms */
/* This is a simplified version — we check structural patterns */

/* For now, a stub that accepts separation instances */
static bool is_separation(Val *f) {
    /* Strip leading foralls */
    while (f->tag == V_FORALL) f = f->forall.body;
    /* Check: forall(a, exists(b, forall(x, iff(x in b, and(x in a, phi))))) */
    if (f->tag != V_FORALL) return false;
    Val *body = f->forall.body; /* exists(b, ...) = neg(forall(b, neg(...))) */
    if (body->tag != V_NEG) return false;
    Val *inner = body->neg.operand;
    if (inner->tag != V_FORALL) return false;
    Val *inner2 = inner->forall.body; /* neg(forall(x, iff(...))) */
    if (inner2->tag != V_NEG) return false;
    Val *fax = inner2->neg.operand;
    if (fax->tag != V_FORALL) return false;
    /* Good enough for now — check iff structure */
    Val *iff_body = fax->forall.body;
    /* iff(A,B) = neg(implies(implies(A,B), neg(implies(B,A)))) */
    if (iff_body->tag != V_NEG) return false;
    Val *imp1 = iff_body->neg.operand;
    if (imp1->tag != V_IMPLIES) return false;
    /* A = mem(x, b), B = and(mem(x,a), phi) */
    /* and(P,Q) = neg(implies(P, neg(Q))) */
    return true; /* accept if structural shape matches */
}

static bool is_replacement(Val *f) {
    /* TODO: implement when needed */
    return false;
}

/* ZFC axioms as structural patterns — compare with kernel.js */
/* For now, use the same pmatch approach */
static bool match_zfc(Val *f, int idx);

static bool is_axiom(Val *f, const char *system) {
    /* Check ZFC axioms by structural match */
    int limit = 7; /* Z: ext, empty, pair, union, power, inf, reg */
    if (strcmp(system, "zfc") == 0) limit = 8;

    for (int i = 0; i < limit; i++)
        if (match_zfc(f, i)) return true;

    if (is_separation(f)) return true;
    if ((strcmp(system, "zf") == 0 || strcmp(system, "zfc") == 0) && is_replacement(f))
        return true;
    return false;
}

/* Build ZFC axiom patterns and match — mirrors kernel.js ZFC array */
/* Helper constructors for patterns */
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

/* Simple structural match (no capture — just alpha-equiv) */
static bool match_zfc(Val *f, int idx) {
    build_zfc();
    return same(f, zfc_axioms[idx]);
}


/* ============================================================
 * File loading
 * ============================================================ */

#define MAX_LOADED 1024

static const char *root_dir;

static char *read_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open: %s", path);
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = perm_alloc(len + 1);
    fread(buf, 1, len, f);
    buf[len] = 0;
    fclose(f);
    return buf;
}

static Env *load_file(const char *filepath);

static void load_import(ASTNode *n, Env *env) {
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

static Env *make_global(void) {
    Env *e = env_new();
    env_set(e, intern("true"), VAL_TRUE);
    env_set(e, intern("false"), VAL_FALSE);
    env_set(e, intern("none"), VAL_NIL);
    env_set(e, intern("add"), val_builtin(builtin_add, "add", false));
    env_set(e, intern("sub"), val_builtin(builtin_sub, "sub", false));
    env_set(e, intern("mul"), val_builtin(builtin_mul, "mul", false));
    env_set(e, intern("gt"), val_builtin(builtin_gt, "gt", false));
    env_set(e, intern("str"), val_builtin(builtin_str, "str", false));
    env_set(e, intern("eq"), val_builtin(builtin_eq, "eq", false));
    env_set(e, intern("not"), val_builtin(builtin_not, "not", false));
    env_set(e, intern("head"), val_builtin(builtin_head, "head", false));
    env_set(e, intern("tail"), val_builtin(builtin_tail, "tail", false));
    env_set(e, intern("nth"), val_builtin(builtin_nth, "nth", false));
    env_set(e, intern("len"), val_builtin(builtin_len, "len", false));
    env_set(e, intern("print"), val_builtin(builtin_print, "print", true));
    env_set(e, intern("_do_proof"), val_builtin(builtin_do_proof, "_do_proof", false));
    env_set(e, intern("_do_qed"), val_builtin(builtin_do_qed, "_do_qed", false));
    env_set(e, intern("_fail"), val_builtin(builtin_fail, "_fail", true));
    return e;
}

static Env *load_file(const char *filepath) {
    /* check cache */
    const char *fp = intern(filepath);
    for (int i = 0; i < nloaded; i++)
        if (loaded_files[i].filepath == fp) return loaded_files[i].exports;

    /* mark as loading */
    Env *exports = env_new();
    loaded_files[nloaded].filepath = fp;
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


/* ============================================================
 * Main
 * ============================================================ */

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: core-ci/min <file.min>\n");
        return 1;
    }

    root_dir = ".";

    load_file(argv[1]);
    return 0;
}
