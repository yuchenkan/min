"use strict";

// === Tokens ===

// No keywords — from/import/as are contextual, not reserved
const PUNCTUATION = new Set("(){}[]$,.:?\\!".split(""));
const ESCAPES = { "\\": "\\", '"': '"', n: "\n", t: "\t" };

function tokenize(source, filepath) {
    filepath = filepath || "<input>";
    const tokens = [];
    let pos = 0, line = 1, colStart = 0;

    function err(msg) {
        throw new SyntaxError(`${filepath}:${line}:${pos - colStart + 1}: ${msg}`);
    }

    while (pos < source.length) {
        const c = source[pos];

        if (c === " " || c === "\t" || c === "\r" || c === "\n") {
            if (c === "\n") { line++; colStart = pos + 1; }
            pos++;
            continue;
        }

        if (c === "#") {
            while (pos < source.length && source[pos] !== "\n") pos++;
            continue;
        }

        const col = pos - colStart + 1;

        if (c === '"') {
            pos++;
            const s = [];
            while (pos < source.length && source[pos] !== '"') {
                if (source[pos] === "\\") {
                    pos++;
                    if (pos >= source.length) err("unterminated string escape");
                    const esc = ESCAPES[source[pos]];
                    if (esc === undefined) err(`invalid escape: \\${source[pos]}`);
                    s.push(esc);
                } else {
                    s.push(source[pos]);
                }
                pos++;
            }
            if (pos >= source.length) err("unterminated string");
            pos++;
            tokens.push(["STR", s.join(""), line, col]);
            continue;
        }

        if (/[a-zA-Z_]/.test(c)) {
            const start = pos;
            while (pos < source.length && /[a-zA-Z0-9_]/.test(source[pos])) pos++;
            const word = source.slice(start, pos);
            tokens.push(["NAME", word, line, col]);
            continue;
        }

        if (/[0-9]/.test(c)) {
            const start = pos;
            while (pos < source.length && /[0-9]/.test(source[pos])) pos++;
            tokens.push(["INT", parseInt(source.slice(start, pos), 10), line, col]);
            continue;
        }

        if (PUNCTUATION.has(c)) {
            tokens.push(["PUNCT", c, line, col]);
            pos++;
            continue;
        }

        err(`unexpected char: ${JSON.stringify(c)}`);
    }

    tokens.push(["EOF", null, line, 1]);
    return tokens;
}


// === AST ===

class Node {
    constructor(file, line, col) { this.file = file; this.line = line; this.col = col; }
}
class Import extends Node {
    constructor(module, names, file, line, col) {
        super(file, line, col); this.module = module; this.names = names;
    }
}
class Bind extends Node {
    constructor(name, expr, file, line, col) {
        super(file, line, col); this.name = name; this.expr = expr;
    }
}
class Fn extends Node {
    constructor(params, body, file, line, col) {
        super(file, line, col); this.params = params; this.body = body;
    }
}
class Call extends Node {
    constructor(callee, args, file, line, col) {
        super(file, line, col); this.callee = callee; this.args = args;
    }
}
class Ref extends Node {
    constructor(name, file, line, col) {
        super(file, line, col); this.name = name;
    }
}
class Lit extends Node {
    constructor(value, file, line, col) {
        super(file, line, col); this.value = value;
    }
}
class List extends Node {
    constructor(elems, file, line, col) {
        super(file, line, col); this.elems = elems;
    }
}
class Block extends Node {
    constructor(bindings, expr, file, line, col) {
        super(file, line, col); this.bindings = bindings; this.expr = expr;
    }
}
class If extends Node {
    constructor(cond, then, else_, file, line, col) {
        super(file, line, col); this.cond = cond; this.then = then; this.else_ = else_;
    }
}


// === Parser ===

class Parser {
    constructor(tokens, filepath) {
        this.tokens = tokens;
        this.pos = 0;
        this.filepath = filepath || "<input>";
    }

    peek() { return this.tokens[this.pos]; }
    advance() { return this.tokens[this.pos++]; }

    expect(typ, val) {
        const tok = this.advance();
        if (tok[0] !== typ || (val !== undefined && tok[1] !== val))
            throw new SyntaxError(
                `${this.filepath}:${tok[2]}:${tok[3]}: expected ${typ} ${JSON.stringify(val)}, got ${tok[0]} ${JSON.stringify(tok[1])}`);
        return tok;
    }

    error(msg) {
        const tok = this.peek();
        throw new SyntaxError(`${this.filepath}:${tok[2]}:${tok[3]}: ${msg}`);
    }

    parseProgram() {
        const items = [];
        while (this.peek()[0] !== "EOF" && this.peek()[1] === "from")
            items.push(this.parseImport());
        if (items.length === 0 && this.peek()[1] !== "$" && this.peek()[0] !== "EOF")
            this.error(`expected import or bind, got ${JSON.stringify(this.peek()[1])}`);
        while (this.peek()[0] !== "EOF") {
            if (this.peek()[1] === "from") this.error("imports must come before all bindings");
            else if (this.peek()[1] === "$") items.push(this.parseBind());
            else this.error(`expected bind, got ${JSON.stringify(this.peek()[1])}`);
        }
        return items;
    }

    parseImport() {
        const tok = this.expect("NAME", "from");
        const module = this.parseDottedName();
        this.expect("NAME", "import");
        const names = [this.parseImportName()];
        while (this.peek()[1] === ",") {
            this.advance();
            names.push(this.parseImportName());
        }
        return new Import(module, names, this.filepath, tok[2], tok[3]);
    }

    parseImportName() {
        const name = this.expect("NAME")[1];
        if (this.peek()[1] === "as") {
            this.advance();
            const alias = this.expect("NAME")[1];
            return { name, alias };
        }
        return { name, alias: name };
    }

    parseDottedName() {
        const parts = [this.expect("NAME")[1]];
        while (this.peek()[1] === ".") {
            this.advance();
            parts.push(this.expect("NAME")[1]);
        }
        return parts.join(".");
    }

    parseBind() {
        const tok = this.expect("PUNCT", "$");
        const name = this.expect("NAME")[1];
        const expr = this.parseExpr();
        return new Bind(name, expr, this.filepath, tok[2], tok[3]);
    }

    _punct(val) {
        const tok = this.peek();
        return tok[0] === "PUNCT" && tok[1] === val;
    }

    parseExpr() {
        let node;
        const tok = this.peek();

        if (this._punct("\\")) node = this.parseFn();
        else if (this._punct("[")) node = this.parseList();
        else if (this._punct("?")) node = this.parseIf();
        else if (this._punct("{")) node = this.parseBlock();
        else if (this._punct("(")) {
            this.advance();
            node = this.parseExpr();
            this.expect("PUNCT", ")");
        }
        else if (tok[0] === "INT") { const t = this.advance(); node = new Lit(t[1], this.filepath, t[2], t[3]); }
        else if (tok[0] === "STR") { const t = this.advance(); node = new Lit(t[1], this.filepath, t[2], t[3]); }
        else if (tok[0] === "NAME") { const t = this.advance(); node = new Ref(t[1], this.filepath, t[2], t[3]); }
        else this.error(`expected expression, got ${JSON.stringify(tok[1])}`);

        while (this._punct("(")) {
            this.advance();
            const args = this.parseArgs();
            this.expect("PUNCT", ")");
            node = new Call(node, args, node.file, node.line, node.col);
        }

        return node;
    }

    parseFn() {
        const tok = this.expect("PUNCT", "\\");
        const params = this.parseParams();
        this.expect("PUNCT", ":");
        const body = this.parseExpr();
        return new Fn(params, body, this.filepath, tok[2], tok[3]);
    }

    parseParams() {
        const params = [];
        while (this.peek()[0] === "NAME") params.push(this.advance()[1]);
        return params;
    }

    parseList() {
        const tok = this.expect("PUNCT", "[");
        const elems = [];
        if (this.peek()[1] !== "]") {
            elems.push(this.parseExpr());
            while (this.peek()[1] === ",") { this.advance(); elems.push(this.parseExpr()); }
        }
        this.expect("PUNCT", "]");
        return new List(elems, this.filepath, tok[2], tok[3]);
    }

    parseIf() {
        const tok = this.expect("PUNCT", "?");
        this.expect("PUNCT", "(");
        const cond = this.parseExpr();
        this.expect("PUNCT", ",");
        const then = this.parseExpr();
        this.expect("PUNCT", ",");
        const else_ = this.parseExpr();
        this.expect("PUNCT", ")");
        return new If(cond, then, else_, this.filepath, tok[2], tok[3]);
    }

    parseBlock() {
        const tok = this.expect("PUNCT", "{");
        const bindings = [];
        while (this.peek()[1] === "$") bindings.push(this.parseBind());
        const expr = this.parseExpr();
        this.expect("PUNCT", "}");
        return new Block(bindings, expr, this.filepath, tok[2], tok[3]);
    }

    parseArgs() {
        const args = [];
        if (this.peek()[1] === ")") return args;
        args.push(this.parseExpr());
        while (this.peek()[1] === ",") { this.advance(); args.push(this.parseExpr()); }
        return args;
    }
}


function parse(source, filepath) {
    const tokens = tokenize(source, filepath);
    const p = new Parser(tokens, filepath);
    return p.parseProgram();
}


module.exports = {
    tokenize, parse,
    Node, Import, Bind, Fn, Call, Ref, Lit, List, Block, If,
};
