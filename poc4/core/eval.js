"use strict";

const fs = require("fs");
const path = require("path");
const parser = require("./parser");
const kernel = require("./kernel");

const ROOT = path.dirname(path.dirname(path.resolve(__filename)));


// === Env (immutable extend) ===

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
    constructor(params, body, env) {
        this.params = params;
        this.body = body;
        this.env = env;
    }
    toString() { return `\\${this.params.join(" ")}: ...`; }
}


// === Eval ===

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


function evaluate(node, env) {
    if (node instanceof parser.Lit) return node.value;
    if (node instanceof parser.Ref) {
        try { return env.get(node.name); }
        catch (_) { throw new EvalError(`undefined: ${node.name}`, node); }
    }
    if (node instanceof parser.Fn) return new Fn(node.params, node.body, env.snapshot());
    if (node instanceof parser.Block) {
        env = env.snapshot();
        for (const binding of node.bindings) {
            env.d[binding.name] = evaluate(binding.expr, env);
        }
        return evaluate(node.expr, env);
    }
    if (node instanceof parser.If) {
        const cond = evaluate(node.cond, env);
        if (cond === true) return evaluate(node.then, env);
        if (cond === false) return evaluate(node.else_, env);
        throw new EvalError("condition must be True or False", node);
    }
    if (node instanceof parser.Call) {
        const callee = evaluate(node.callee, env);
        const args = node.args.map(a => evaluate(a, env));
        try { return call(callee, args, node); }
        catch (e) { if (e instanceof EvalError) e.addFrame(node); throw e; }
    }
    if (node instanceof parser.List) return node.elems.map(e => evaluate(e, env));
    throw new EvalError(`unknown: ${node.constructor.name}`, node);
}


function call(callee, args, node) {
    if (callee instanceof Fn) {
        const env = callee.env.snapshot();
        for (let i = 0; i < callee.params.length; i++)
            env.d[callee.params[i]] = i < args.length ? args[i] : null;
        return evaluate(callee.body, env);
    }
    if (typeof callee === "function") return callee(...args);
    throw new EvalError(`not callable: ${callee}`, node);
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
        const seq = new kernel.Sequent(
            left.map(build),
            right.map(build));
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

function deepEqual(a, b) {
    if (a === b) return true;
    if (Array.isArray(a) && Array.isArray(b)) {
        if (a.length !== b.length) return false;
        for (let i = 0; i < a.length; i++)
            if (!deepEqual(a[i], b[i])) return false;
        return true;
    }
    return false;
}


// === Builtins ===

function makeGlobal() {
    return new Env({
        True: true, False: false, None: null,
        add: (a, b) => Array.isArray(a) ? [...a, ...b] : a + b,
        sub: (a, b) => a - b,
        mul: (a, b) => a * b,
        eq: deepEqual,
        not: (a) => !a,
        head: (a) => a[0],
        tail: (a) => a.slice(1),
        len: (a) => a.length,
        print: (a) => { console.log(a); return a; },
        _do_proof: doProof,
        _do_qed: doQed,
        _fail: fail,
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
            const val = evaluate(node.expr, env);
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
    for (const name of node.names) {
        if (name in imported) env.d[name] = imported[name];
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


// === Self-test / CLI ===

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
            const val = evaluate(node.expr, env);
            env.d[node.name] = val;
        }
    }
}


module.exports = { Env, Fn, EvalError, evaluate, call, loadFile, run };
