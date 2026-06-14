#include "parse.h"
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

/* ============================================================
 * Tokenizer (malloc, freed after parse)
 * ============================================================ */

enum { T_NAME, T_INT, T_STR, T_PUNCT, T_EOF };

typedef struct Token {
  int type;
  char *val;
  int line, col;
} Token;

typedef struct Tokenizer {
  Token *tokens;
  int len, cap;
  int pos;
  const char *filepath;
} Tokenizer;

static char *strndup_(const char *s, int n) {
  char *p = malloc(n + 1);
  memcpy(p, s, n);
  p[n] = '\0';
  return p;
}

static void tok_push(Tokenizer *t, int type, char *s, int line, int col) {
  if (t->len >= t->cap) {
    t->cap *= 2;
    t->tokens = realloc(t->tokens, sizeof(Token) * t->cap);
  }
  Token *tok = &t->tokens[t->len++];
  tok->type = type;
  tok->val = s;
  tok->line = line;
  tok->col = col;
}

static const char *PUNCTUATION = "(){}[]$,.:?\\!";

static int tokenize(Tokenizer *t, const char *src) {
  int pos = 0, line = 1, colStart = 0;
  int slen = strlen(src);

  while (pos < slen) {
    char c = src[pos];

    if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
      if (c == '\n') { line++; colStart = pos + 1; }
      pos++;
      continue;
    }

    if (c == '#') {
      while (pos < slen && src[pos] != '\n') pos++;
      continue;
    }

    int col = pos - colStart + 1;

    if (c == '"') {
      pos++;
      int cap = 32;
      char *buf = malloc(cap);
      int blen = 0;
      while (pos < slen && src[pos] != '"') {
        if (src[pos] == '\\') {
          pos++;
          if (pos >= slen) {
            fprintf(stderr, "%s:%d:%d: unterminated escape\n", t->filepath, line, col);
            free(buf);
            return 1;
          }
          char e = src[pos];
          if (e == '\\') buf[blen++] = '\\';
          else if (e == '"') buf[blen++] = '"';
          else {
            fprintf(stderr, "%s:%d:%d: invalid escape: \\%c\n", t->filepath, line, col, e);
            free(buf);
            return 1;
          }
        } else {
          buf[blen++] = src[pos];
        }
        if (blen >= cap) { cap *= 2; buf = realloc(buf, cap); }
        pos++;
      }
      if (pos >= slen) {
        fprintf(stderr, "%s:%d:%d: unterminated string\n", t->filepath, line, col);
        free(buf);
        return 1;
      }
      pos++;
      buf[blen] = '\0';
      tok_push(t, T_STR, buf, line, col);
      continue;
    }

    if (isalpha(c) || c == '_') {
      int start = pos;
      while (pos < slen && (isalnum(src[pos]) || src[pos] == '_')) pos++;
      tok_push(t, T_NAME, strndup_(src + start, pos - start), line, col);
      continue;
    }

    if (isdigit(c)) {
      int start = pos;
      while (pos < slen && isdigit(src[pos])) pos++;
      tok_push(t, T_INT, strndup_(src + start, pos - start), line, col);
      continue;
    }

    if (strchr(PUNCTUATION, c)) {
      tok_push(t, T_PUNCT, strndup_(src + pos, 1), line, col);
      pos++;
      continue;
    }

    fprintf(stderr, "%s:%d:%d: unexpected char: '%c'\n", t->filepath, line, col, c);
    return 1;
  }

  tok_push(t, T_EOF, NULL, line, 1);
  return 0;
}

static void tokenizer_free(Tokenizer *t) {
  for (int i = 0; i < t->len; i++)
    free(t->tokens[i].val);
  free(t->tokens);
}

/* ============================================================
 * Parser helpers
 * ============================================================ */

static Token *peek(Tokenizer *t) { return &t->tokens[t->pos]; }
static Token *advance(Tokenizer *t) { return &t->tokens[t->pos++]; }

static int is_punct(Tokenizer *t, char c) {
  Token *tok = peek(t);
  return tok->type == T_PUNCT && tok->val[0] == c;
}

static int is_name(Tokenizer *t, const char *s) {
  Token *tok = peek(t);
  return tok->type == T_NAME && strcmp(tok->val, s) == 0;
}

static int expect_punct(Tokenizer *t, char c) {
  Token *tok = advance(t);
  if (tok->type != T_PUNCT || tok->val[0] != c) {
    fprintf(stderr, "%s:%d:%d: expected '%c'\n", t->filepath, tok->line, tok->col, c);
    return 1;
  }
  return 0;
}

static int expect_name(Tokenizer *t, const char **out) {
  Token *tok = advance(t);
  if (tok->type != T_NAME) {
    fprintf(stderr, "%s:%d:%d: expected name\n", t->filepath, tok->line, tok->col);
    return 1;
  }
  *out = tok->val;
  return 0;
}

static void set_loc(Node *n, Token *tok, const char *file) {
  n->file = file;
  n->line = tok->line;
  n->col = tok->col;
}

static int parse_expr(GC *gc, Intern *it, Node **slot, Tokenizer *t);

static int parse_bind(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '$')) return 1;
  n->tag = N_BIND;
  n->bind.name = NULL;
  n->bind.expr = NULL;
  const char *name;
  if (expect_name(t, &name)) return 1;
  n->bind.name = (char *)intern(it, name);
  return parse_expr(gc, it, &n->bind.expr, t);
}

static int parse_fn(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '\\')) return 1;
  n->fn.params = gc_list_new(gc);

  while (peek(t)->type == T_NAME) {
    void **slot = gc_list_append(gc, n->fn.params);
    const char *name;
    if (expect_name(t, &name)) return 1;
    *slot = (char *)intern(it, name);
  }

  if (expect_punct(t, ':')) return 1;
  return parse_expr(gc, it, &n->fn.body, t);
}

static int parse_list(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '[')) return 1;
  n->list = gc_list_new(gc);

  if (!is_punct(t, ']')) {
    void **slot = gc_list_append(gc, n->list);
    if (parse_expr(gc, it, (Node **)slot, t)) return 1;
    while (is_punct(t, ',')) {
      advance(t);
      slot = gc_list_append(gc, n->list);
      if (parse_expr(gc, it, (Node **)slot, t)) return 1;
    }
  }
  return expect_punct(t, ']');
}

static int parse_if(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '?')) return 1;
  if (expect_punct(t, '(')) return 1;
  if (parse_expr(gc, it, &n->if_.cond, t)) return 1;
  if (expect_punct(t, ',')) return 1;
  if (parse_expr(gc, it, &n->if_.then, t)) return 1;
  if (expect_punct(t, ',')) return 1;
  if (parse_expr(gc, it, &n->if_.else_, t)) return 1;
  return expect_punct(t, ')');
}

static int parse_block(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '{')) return 1;
  n->block.binds = gc_list_new(gc);

  while (is_punct(t, '$')) {
    void **slot = gc_list_append(gc, n->block.binds);
    node_new(gc, (void **)slot, N_BIND);
    set_loc(*slot, peek(t), t->filepath);
    if (parse_bind(gc, it, *slot, t)) return 1;
  }

  if (parse_expr(gc, it, &n->block.expr, t)) return 1;
  return expect_punct(t, '}');
}

static int parse_args(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  if (expect_punct(t, '(')) return 1;
  n->call.args = gc_list_new(gc);

  if (!is_punct(t, ')')) {
    void **slot = gc_list_append(gc, n->call.args);
    if (parse_expr(gc, it, (Node **)slot, t)) return 1;
    while (is_punct(t, ',')) {
      advance(t);
      slot = gc_list_append(gc, n->call.args);
      if (parse_expr(gc, it, (Node **)slot, t)) return 1;
    }
  }
  return expect_punct(t, ')');
}

static int parse_expr(GC *gc, Intern *it, Node **slot, Tokenizer *t) {

  Token *tok = peek(t);

  if (is_punct(t, '\\')) {
    node_new(gc, (void **)slot, N_FN);
    set_loc(*slot, tok, t->filepath);
    if (parse_fn(gc, it, *slot, t)) return 1;
  }
  else if (is_punct(t, '[')) {
    node_new(gc, (void **)slot, N_LIST);
    set_loc(*slot, tok, t->filepath);
    if (parse_list(gc, it, *slot, t)) return 1;
  }
  else if (is_punct(t, '?')) {
    node_new(gc, (void **)slot, N_IF);
    set_loc(*slot, tok, t->filepath);
    if (parse_if(gc, it, *slot, t)) return 1;
  }
  else if (is_punct(t, '{')) {
    node_new(gc, (void **)slot, N_BLOCK);
    set_loc(*slot, tok, t->filepath);
    if (parse_block(gc, it, *slot, t)) return 1;
  }
  else if (is_punct(t, '(')) {
    advance(t);
    if (parse_expr(gc, it, slot, t)) return 1;
    if (expect_punct(t, ')')) return 1;
  }
  else if (tok->type == T_INT) {
    advance(t);
    uint64_t v = 0;
    for (const char *s = tok->val; *s; s++)
      v = v * 10 + (*s - '0');
    *slot = intern_int(it, v);
  }
  else if (tok->type == T_STR) {
    advance(t);
    *slot = (Node *)intern(it, tok->val);
    *slot = intern_str(it, (const char *)*slot);
  }
  else if (tok->type == T_NAME) {
    advance(t);
    node_new(gc, (void **)slot, N_REF);
    set_loc(*slot, tok, t->filepath);
    (*slot)->ref = (char *)intern(it, tok->val);
  }
  else {
    fprintf(stderr, "%s:%d:%d: expected expression\n", t->filepath, tok->line, tok->col);
    return 1;
  }

  /* trailing calls: f(args)(args)... */
  while (is_punct(t, '(')) {
    Token *call_tok = peek(t);
    Node *callee = *slot;
    node_new(gc, (void **)slot, N_CALL);
    set_loc(*slot, call_tok, t->filepath);
    (*slot)->call.callee = callee;
    if (parse_args(gc, it, *slot, t)) return 1;
  }
  return 0;
}

static void import_name_trace(void *data) {
  char **n = data;
  gc_mark(n[0]);
  gc_mark(n[1]);
}

static int import_names_append(GC *gc, Intern *it, Node *n, Tokenizer *t) {

  void **slot = gc_list_append(gc, n->import.names);
  *slot = gc_alloc(gc, 2 * sizeof(char *), import_name_trace, NULL, NULL);
  char **name = *slot;
  name[0] = NULL;
  name[1] = NULL;

  const char *nm;
  if (expect_name(t, &nm)) return 1;
  name[0] = (char *)intern(it, nm);
  if (is_name(t, "as")) {
    advance(t);
    if (expect_name(t, &nm)) return 1;
    name[1] = (char *)intern(it, nm);
  }
  return 0;
}

static int parse_import(GC *gc, Intern *it, Node *n, Tokenizer *t) {
  advance(t); /* skip "from" */
  int from = t->pos;
  const char *nm;
  if (expect_name(t, &nm)) return 1;
  int len = strlen(nm);
  int nf = 0;
  while (is_punct(t, '.')) {
    advance(t);
    if (expect_name(t, &nm)) return 1;
    len += 1 + strlen(nm);
    nf++;
  }

  char *filepath = malloc(len + 5);
  char *fp = filepath;
  const char *f = t->tokens[from].val;
  strcpy(fp, f);
  fp += strlen(f);
  for (int i = 0; i < nf; i++) {
    *(fp++) = '/';
    f = t->tokens[from += 2].val;
    strcpy(fp, f);
    fp += strlen(f);
  }
  strcpy(fp, ".min");
  n->import.filepath = (char *)intern(it, filepath);
  free(filepath);

  if (!is_name(t, "import")) {
    fprintf(stderr, "%s:%d:%d: expected 'import'\n", t->filepath, peek(t)->line, peek(t)->col);
    return 1;
  }
  advance(t);

  n->import.names = gc_list_new(gc);
  if (import_names_append(gc, it, n, t)) return 1;
  while (is_punct(t, ',')) {
    advance(t);
    if (import_names_append(gc, it, n, t)) return 1;
  }
  return 0;
}

/* ============================================================
 * Source
 * ============================================================ */

static void source_trace(void *data) {
  Source *s = data;
  gc_mark(s->imports);
  gc_mark(s->binds);
}

int parse(GC *gc, Intern *intern_t, GCMap *sources, GCMap *modules, const char *filepath, ReadFileFn read_file) {
  if (gc_map_find(modules, filepath)) return 0;

  void **slot = gc_map_get(gc, sources, filepath);
  if (*slot) {
    Source *s = *slot;
    if (s->loading) {
      fprintf(stderr, "cycle import: %s\n", filepath);
      return 1;
    }
    return 0;
  }

  Source *s = gc_alloc(gc, sizeof(Source), source_trace, NULL, NULL);
  s->imports = NULL;
  s->binds = NULL;
  s->loading = 1;
  s->mtime = 0;
  *slot = s;
  s->imports = gc_list_new(gc);
  s->binds = gc_list_new(gc);

  int64_t mtime = 0;
  char *src = read_file(filepath, &mtime);
  s->mtime = mtime;
  if (!src) return 1;
  Tokenizer t = { malloc(sizeof(Token) * 64), 0, 64, 0, filepath };
  if (tokenize(&t, src)) { free(src); tokenizer_free(&t); return 1; }
  free(src);

  while (peek(&t)->type != T_EOF && is_name(&t, "from")) {
    void **islot = gc_list_append(gc, s->imports);
    node_new(gc, islot, N_IMPORT);
    set_loc(*islot, peek(&t), t.filepath);
    if (parse_import(gc, intern_t, *islot, &t)) { tokenizer_free(&t); return 1; }
    int err = parse(gc, intern_t, sources, modules, ((Node *)*islot)->import.filepath, read_file);
    if (err) { tokenizer_free(&t); return err; }
  }

  while (peek(&t)->type != T_EOF) {
    void **bslot = gc_list_append(gc, s->binds);
    node_new(gc, bslot, N_BIND);
    set_loc(*bslot, peek(&t), t.filepath);
    if (parse_bind(gc, intern_t, *bslot, &t)) { tokenizer_free(&t); return 1; }
  }

  tokenizer_free(&t);
  s->loading = 0;
  return 0;
}
