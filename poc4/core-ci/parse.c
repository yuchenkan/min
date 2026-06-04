#include "parse.h"

/* ============================================================
 * Tokenizer
 * ============================================================ */

static void tok_push(TokenList *tl, Token t) {
    if (tl->len >= tl->cap) {
        tl->cap *= 2;
        Token *n = gc_alloc(sizeof(Token) * tl->cap, GC_KIND_RAW);
        memcpy(n, tl->toks, sizeof(Token) * tl->len);
        tl->toks = n;
    }
    tl->toks[tl->len++] = t;
}

static const char *punctuation = "(){}[]$,.:?\\!";

TokenList tokenize(const char *src, const char *filepath) {
    TokenList tl = { gc_alloc(sizeof(Token) * 256, GC_KIND_RAW), 0, 256 };
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
            tok_push(&tl, (Token){ T_STR, strdup(buf), 0, line, col });
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
            tok_push(&tl, (Token){ T_NAME, strdup(buf), 0, line, col });
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
            tok_push(&tl, (Token){ T_PUNCT, strdup(buf), 0, line, col });
            pos++;
            continue;
        }

        die("%s:%d:%d: unexpected char: '%c'", filepath, line, col, c);
    }

    tok_push(&tl, (Token){ T_EOF, NULL, 0, line, 1 });
    return tl;
}

/* ============================================================
 * AST node pool
 * ============================================================ */

ASTNode *nodes = NULL;
int nnodes = 0;
static int nodes_cap = 0;

static int node_alloc(void) {
    if (nnodes >= nodes_cap) {
        nodes_cap = nodes_cap ? nodes_cap * 2 : 1024;
        ASTNode *n = gc_alloc(sizeof(ASTNode) * nodes_cap, GC_KIND_RAW);
        if (nodes) memcpy(n, nodes, sizeof(ASTNode) * nnodes);
        nodes = n;
    }
    return nnodes++;
}

/* ============================================================
 * Parser
 * ============================================================ */

static Token ppeek(Parser *p) { return p->tl.toks[p->pos]; }
static Token padvance(Parser *p) { return p->tl.toks[p->pos++]; }

static Token pexpect(Parser *p, TokTag tag, const char *val) {
    Token t = padvance(p);
    if (t.tag != tag || (val && strcmp(t.sval, val) != 0))
        die("%s:%d:%d: expected %d %s, got %d %s",
            p->filepath, t.line, t.col, tag, val ? val : "", t.tag, t.sval ? t.sval : "");
    return t;
}

static bool ppunct(Parser *p, const char *val) {
    Token t = ppeek(p);
    return t.tag == T_PUNCT && strcmp(t.sval, val) == 0;
}

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
    nodes[id].fn.params = gc_alloc(sizeof(const char*) * np, GC_KIND_RAW);
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
    nodes[id].list.elems = gc_alloc(sizeof(int) * ne, GC_KIND_RAW);
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
    nodes[id].block.binds = gc_alloc(sizeof(int) * nb, GC_KIND_RAW);
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

int parse_expr(Parser *p) {
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
        nodes[cid].call.args = gc_alloc(sizeof(int) * na, GC_KIND_RAW);
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
    if (ppeek(p).tag == T_NAME && strcmp(ppeek(p).sval, "as") == 0) {
        padvance(p);
        aliases[nn] = pexpect(p, T_NAME, NULL).sval;
    }
    nn++;
    while (ppunct(p, ",")) {
        padvance(p);
        names[nn] = pexpect(p, T_NAME, NULL).sval;
        aliases[nn] = names[nn];
        if (ppeek(p).tag == T_NAME && strcmp(ppeek(p).sval, "as") == 0) {
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
    nodes[id].import.module = strdup(module);
    nodes[id].import.names = gc_alloc(sizeof(const char*) * nn, GC_KIND_RAW);
    memcpy(nodes[id].import.names, names, sizeof(const char*) * nn);
    nodes[id].import.aliases = gc_alloc(sizeof(const char*) * nn, GC_KIND_RAW);
    memcpy(nodes[id].import.aliases, aliases, sizeof(const char*) * nn);
    nodes[id].import.nnames = nn;
    imports[(*nimports)++] = id;
}

Program parse_program(Parser *p) {
    int items[4096];
    int ni = 0;

    /* imports first */
    while (ppeek(p).tag != T_EOF && ppeek(p).tag == T_NAME && strcmp(ppeek(p).sval, "from") == 0)
        parse_import(p, items, &ni);

    /* then binds */
    while (ppeek(p).tag != T_EOF) {
        if (ppeek(p).tag == T_NAME && strcmp(ppeek(p).sval, "from") == 0)
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
    prog.items = gc_alloc(sizeof(int) * ni, GC_KIND_RAW);
    memcpy(prog.items, items, sizeof(int) * ni);
    prog.nitems = ni;
    return prog;
}
