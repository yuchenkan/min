"use strict";

const fs = require("fs");
const path = require("path");
const parser = require("./parser");
const kernel = require("./kernel");

const ROOT = path.dirname(path.dirname(path.resolve(__filename)));


// === Env ===

class Env {
    constructor(d) { this.d = d || {}; }
    get(name) {
        if (!(name in this.d)) throw new Error(`undefined: ${name}`);
        return this.d[name];
    }
    snapshot() { return new Env({ ...this.d }); }
}


// === Values ===

class Fn {
    constructor(params, bodyFn, env) {
        this.params = params;
        this.bodyFn = bodyFn;
        this.env = env;
    }
    toString() { return `\\${this.params.join(" ")}: ...`; }
}


// === Errors ===

class EvalError extends Error {
    constructor(msg, node) {
        super(msg);
        this.msg = msg;
        this.node = node;
        this.trace = [];
    }
    addFrame(node) { this.trace.push(node); }
    toString() {
        const lines = [];
        if (this.node)
            lines.push(`${this.node.file}:${this.node.line}:${this.node.col}: ${this.msg}`);
        else
            lines.push(this.msg);
        for (const n of this.trace)
            lines.push(`  at ${n.file}:${n.line}:${n.col}`);
        return lines.join("\n");
    }
}


// === Compiler: AST -> (env) => value ===

function compile(node) {
    if (node instanceof parser.Lit) {
        const v = node.value;
        return (_env) => v;
    }
    if (node instanceof parser.Ref) {
        const name = node.name;
        return (env) => {
            if (!(name in env.d)) throw new EvalError(`undefined: ${name}`, node);
            return env.d[name];
        };
    }
    if (node instanceof parser.Fn) {
        const params = node.params;
        const bodyFn = compile(node.body);
        return (env) => new Fn(params, bodyFn, env.snapshot());
    }
    if (node instanceof parser.Block) {
        const binds = node.bindings.map(b => ({ name: b.name, fn: compile(b.expr) }));
        const exprFn = compile(node.expr);
        return (env) => {
            env = env.snapshot();
            for (const b of binds) env.d[b.name] = b.fn(env);
            return exprFn(env);
        };
    }
    if (node instanceof parser.If) {
        const condFn = compile(node.cond);
        const thenFn = compile(node.then);
        const elseFn = compile(node.else_);
        return (env) => {
            const c = condFn(env);
            if (c === true) return thenFn(env);
            if (c === false) return elseFn(env);
            throw new EvalError("condition must be True or False", node);
        };
    }
    if (node instanceof parser.Call) {
        const calleeFn = compile(node.callee);
        const argFns = node.args.map(a => compile(a));
        return (env) => {
            const callee = calleeFn(env);
            const args = argFns.map(fn => fn(env));
            try { return call(callee, args, node); }
            catch (e) {
                if (e instanceof EvalError) { e.addFrame(node); throw e; }
                throw new EvalError(e.message, node);
            }
        };
    }
    if (node instanceof parser.List) {
        const fns = node.elems.map(e => compile(e));
        return (env) => fns.map(f => f(env));
    }
    throw new EvalError(`unknown: ${node.constructor.name}`, node);
}


function exec(callee, args) {
    if (callee instanceof Fn) {
        const env = callee.env.snapshot();
        for (let i = 0; i < callee.params.length; i++)
            env.d[callee.params[i]] = i < args.length ? args[i] : null;
        return callee.bodyFn(env);
    }
    return callee(...args);
}

const _R = Symbol();

function cacheGet(m, args) {
    for (const a of args) { m = m.get(a); if (!m) return undefined; }
    return m.get(_R);
}

function cacheSet(m, args, val) {
    for (const a of args) { let n = m.get(a); if (!n) { n = new Map(); m.set(a, n); } m = n; }
    m.set(_R, val);
}

function call(callee, args, node) {
    if (callee._nocache) return exec(callee, args);
    if (!callee._c) { callee._c = new Map(); callee._n = 0; }
    const hit = cacheGet(callee._c, args);
    if (hit !== undefined) return hit;
    if (callee._n > 1024) { callee._c.clear(); callee._n = 0; }
    const result = exec(callee, args);
    cacheSet(callee._c, args, result);
    callee._n++;
    return result;
}


// === Formula bridge ===

function build(f) {
    if (typeof f === "string") return f;
    const tag = f[0];
    if (tag === "mem") return new kernel.Mem(build(f[1]), build(f[2]));
    if (tag === "neg") return new kernel.Neg(build(f[1]));
    if (tag === "implies") return new kernel.Implies(build(f[1]), build(f[2]));
    if (tag === "forall") return new kernel.Forall(f[1], build(f[2]));
    throw new Error(`build: unknown tag ${tag}`);
}

function doProof(left, right, rule, premises, principal, term) {
    try {
        const seq = new kernel.Sequent(left.map(build), right.map(build));
        return [true, kernel.proof(seq, rule, premises, build(principal), term)];
    } catch (e) {
        return [false, e.message];
    }
}

function doQed(p, expected, system) {
    try {
        kernel.qed(p, build(expected), system);
        return [true, null];
    } catch (e) {
        return [false, e.message];
    }
}

function fail(msg) { throw new EvalError(msg); }

// === Builtins ===

function makeGlobal() {
    return new Env({
        True: true, False: false, None: null,
        add: (a, b) => {
            if (a === null || b === null) throw new EvalError("add: null argument");
            return Array.isArray(a) ? [...a, ...b] : a + b;
        },
        sub: (a, b) => a - b,
        gt: (a, b) => a > b,
        mul: (a, b) => a * b,
        eq: (a, b) => a === b,
        not: (a) => !a,
        head: (a) => a[0],
        tail: (a) => a.slice(1),
        nth: (a, n) => a[n],
        len: (a) => a.length,
        print: Object.assign((a) => { console.log(a); return a; }, { _nocache: true }),
        _do_proof: doProof,
        _do_qed: doQed,
        _fail: Object.assign(fail, { _nocache: true }),
    });
}


// === File loading ===

const loaded = {};

function loadFile(filepath) {
    filepath = path.resolve(filepath);
    if (filepath in loaded) return loaded[filepath];
    loaded[filepath] = {};

    const source = fs.readFileSync(filepath, "utf-8");
    const nodes = parser.parse(source, filepath);
    const env = makeGlobal();

    for (const node of nodes) {
        if (node instanceof parser.Import) {
            loadImport(node, env);
        } else if (node instanceof parser.Bind) {
            const fn = compile(node.expr);
            const val = fn(env);
            env.d[node.name] = val;
            loaded[filepath][node.name] = val;
        }
    }

    return loaded[filepath];
}

function loadImport(node, env) {
    const parts = node.module.split(".");
    const filepath = path.join(ROOT, ...parts) + ".min";
    if (!fs.existsSync(filepath)) return;
    const imported = loadFile(filepath);
    for (const { name, alias } of node.names) {
        if (name.startsWith("_"))
            throw new EvalError(`cannot import private name "${name}" from ${node.module}`);
        if (name in imported) env.d[alias] = imported[name];
    }
}

function run(filepath) {
    try {
        loadFile(filepath);
        return true;
    } catch (e) {
        if (e instanceof EvalError) {
            process.stderr.write(e.toString() + "\n");
            return false;
        }
        throw e;
    }
}


// === CLI ===

if (require.main === module) {
    if (process.argv.length > 2) {
        const ok = run(process.argv[2]);
        process.exit(ok ? 0 : 1);
    }

    const src = `
$double \\n: add(n, n)
$r1 print(double(3))
$r2 print(double(add(1, 2)))

$id \\x: x
$r3 print(id(42))

$pair \\a b: [a, b]
$r4 print(pair(1, 2))

$compose \\f g: \\x: f(g(x))
$quadruple compose(double, double)
$r5 print(quadruple(3))

$fact \\self n: ?(eq(n, 0), 1, mul(n, self(self, sub(n, 1))))
$r6 print(fact(fact, 5))
`;
    const env = makeGlobal();
    const nodes = parser.parse(src, "<test>");
    for (const node of nodes) {
        if (node instanceof parser.Bind) {
            const fn = compile(node.expr);
            env.d[node.name] = fn(env);
        }
    }
}

module.exports = { Env, Fn, EvalError, compile, call, loadFile, run };
