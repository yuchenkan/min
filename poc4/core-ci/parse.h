#ifndef PARSE_H
#define PARSE_H

#include "val.h"

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

TokenList tokenize(const char *src, const char *filepath);

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
        const char *lit_str;                const char *ref_name;               struct { const char **params; int nparams; int body; } fn;
        struct { int callee; int *args; int nargs; } call;
        struct { int *elems; int nelems; } list;
        struct { int cond, then_, else_; } if_;
        struct { int *binds; int nbinds; int expr; } block;
        struct { const char *name; int expr; } bind;
        struct { const char *module; const char **names; const char **aliases; int nnames; } import;
    };
};

/* Global AST node pool */
extern ASTNode *nodes;
extern int nnodes;

typedef struct {
    TokenList tl;
    int pos;
    const char *filepath;
} Parser;

typedef struct {
    int *items;     /* node indices: imports then binds */
    int nitems;
} Program;

int parse_expr(Parser *p);
Program parse_program(Parser *p);

#endif
