"use strict";

// === Types ===

class Mem {
    constructor(left, right) { this.left = left; this.right = right; }
}
class Neg {
    constructor(operand) { this.operand = operand; }
}
class Implies {
    constructor(left, right) { this.left = left; this.right = right; }
}
class Forall {
    constructor(var_, body) { this.var = var_; this.body = body; }
}
class Sequent {
    constructor(left, right) {
        checkSet(left);
        checkSet(right);
        this.left = left;
        this.right = right;
    }
}
class Proof {
    constructor(sequent) { this.sequent = sequent; }
}

function checkSet(lst) {
    for (let i = 0; i < lst.length; i++)
        for (let j = i + 1; j < lst.length; j++)
            if (same(lst[i], lst[j]))
                throw new Error("sequent: duplicate formula");
}


// === Substitution ===

function subst(formula, old, new_) {
    if (typeof formula === "string")
        return formula === old ? new_ : formula;
    if (formula instanceof Mem)
        return new Mem(subst(formula.left, old, new_), subst(formula.right, old, new_));
    if (formula instanceof Neg)
        return new Neg(subst(formula.operand, old, new_));
    if (formula instanceof Implies)
        return new Implies(subst(formula.left, old, new_), subst(formula.right, old, new_));
    if (formula instanceof Forall) {
        if (formula.var === old) return formula;
        return new Forall(formula.var, subst(formula.body, old, new_));
    }
    throw new Error(`cannot subst: ${formula.constructor.name}`);
}


// === Alpha-equivalence ===

function same(a, b) { return eq(a, b, []); }

function eq(a, b, env) {
    if (typeof a === "string" && typeof b === "string") {
        for (const [v1, v2] of env) {
            if (a === v1) return b === v2;
            if (b === v2) return false;
        }
        return a === b;
    }
    if (a.constructor !== b.constructor) return false;
    if (a instanceof Mem)
        return eq(a.left, b.left, env) && eq(a.right, b.right, env);
    if (a instanceof Neg)
        return eq(a.operand, b.operand, env);
    if (a instanceof Implies)
        return eq(a.left, b.left, env) && eq(a.right, b.right, env);
    if (a instanceof Forall)
        return eq(a.body, b.body, [[a.var, b.var], ...env]);
    return false;
}


// === Free variables ===

function freeVars(formula, bound) {
    if (!bound) bound = new Set();
    if (typeof formula === "string")
        return bound.has(formula) ? new Set() : new Set([formula]);
    if (formula instanceof Mem)
        return setUnion(freeVars(formula.left, bound), freeVars(formula.right, bound));
    if (formula instanceof Neg)
        return freeVars(formula.operand, bound);
    if (formula instanceof Implies)
        return setUnion(freeVars(formula.left, bound), freeVars(formula.right, bound));
    if (formula instanceof Forall)
        return freeVars(formula.body, new Set([...bound, formula.var]));
    return new Set();
}

function boundVars(formula) {
    if (typeof formula === "string") return new Set();
    if (formula instanceof Mem)
        return setUnion(boundVars(formula.left), boundVars(formula.right));
    if (formula instanceof Neg) return boundVars(formula.operand);
    if (formula instanceof Implies)
        return setUnion(boundVars(formula.left), boundVars(formula.right));
    if (formula instanceof Forall)
        return new Set([formula.var, ...boundVars(formula.body)]);
    return new Set();
}

function setUnion(a, b) {
    const r = new Set(a);
    for (const x of b) r.add(x);
    return r;
}


// === Helpers ===

function fin(f, lst) { return lst.some(g => same(f, g)); }

function remove(lst, f) {
    let removed = false;
    const result = [];
    for (const g of lst) {
        if (!removed && same(f, g)) { removed = true; }
        else result.push(g);
    }
    return result;
}

function setAdd(lst, f) {
    return fin(f, lst) ? [...lst] : [...lst, f];
}

function eqSequent(a, b) {
    return isPermutation(a.left, b.left) && isPermutation(a.right, b.right);
}

function isPermutation(a, b) {
    if (a.length !== b.length) return false;
    const used = new Array(b.length).fill(false);
    for (const f of a) {
        let found = false;
        for (let j = 0; j < b.length; j++) {
            if (!used[j] && same(f, b[j])) {
                used[j] = true;
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}


// === Proof rules ===

function proof(seq, rule, premises, principal, term) {
    if (!checkRule(seq, rule, premises, principal, term))
        throw new Error(`invalid proof step: ${rule}`);
    return new Proof(seq);
}

function checkRule(s, rule, premises, principal, term) {
    const ps = premises.map(p => p.sequent);

    switch (rule) {
        case "axiom":
            return ps.length === 0
                && fin(principal, s.left) && fin(principal, s.right);

        case "neg_left":
            return ps.length === 1 && principal instanceof Neg
                && fin(principal, s.left)
                && eqSequent(ps[0], new Sequent(
                    remove(s.left, principal),
                    setAdd(s.right, principal.operand)));

        case "neg_right":
            return ps.length === 1 && principal instanceof Neg
                && fin(principal, s.right)
                && eqSequent(ps[0], new Sequent(
                    setAdd(s.left, principal.operand),
                    remove(s.right, principal)));

        case "implies_left": {
            if (ps.length !== 2 || !(principal instanceof Implies)) return false;
            if (!fin(principal, s.left)) return false;
            const G = remove(s.left, principal);
            return eqSequent(ps[0], new Sequent(G, setAdd(s.right, principal.left)))
                && eqSequent(ps[1], new Sequent(setAdd(G, principal.right), s.right));
        }

        case "implies_right": {
            if (ps.length !== 1 || !(principal instanceof Implies)) return false;
            if (!fin(principal, s.right)) return false;
            const D = remove(s.right, principal);
            return eqSequent(ps[0], new Sequent(
                setAdd(s.left, principal.left), setAdd(D, principal.right)));
        }

        case "forall_left": {
            if (ps.length !== 1 || typeof term !== "string" || !(principal instanceof Forall))
                return false;
            if (!fin(principal, s.left)) return false;
            if (boundVars(principal.body).has(term)) return false;
            const G = remove(s.left, principal);
            const substituted = subst(principal.body, principal.var, term);
            return eqSequent(ps[0], new Sequent(setAdd(G, substituted), s.right));
        }

        case "forall_right": {
            if (ps.length !== 1 || typeof term !== "string" || !(principal instanceof Forall))
                return false;
            if (!fin(principal, s.right)) return false;
            if (boundVars(principal.body).has(term)) return false;
            const D = remove(s.right, principal);
            const all = [...s.left, ...D];
            if (all.some(f => freeVars(f).has(term))) return false;
            const substituted = subst(principal.body, principal.var, term);
            return eqSequent(ps[0], new Sequent(s.left, setAdd(D, substituted)));
        }

        case "cut":
            return ps.length === 2
                && eqSequent(ps[0], new Sequent(s.left, setAdd(s.right, principal)))
                && eqSequent(ps[1], new Sequent(setAdd(s.left, principal), s.right));

        case "weakening_left": {
            if (ps.length !== 1) return false;
            if (!fin(principal, s.left)) return false;
            if (fin(principal, ps[0].left)) return eqSequent(ps[0], s);
            return eqSequent(ps[0], new Sequent(remove(s.left, principal), s.right));
        }

        case "weakening_right": {
            if (ps.length !== 1) return false;
            if (!fin(principal, s.right)) return false;
            if (fin(principal, ps[0].right)) return eqSequent(ps[0], s);
            return eqSequent(ps[0], new Sequent(s.left, remove(s.right, principal)));
        }
    }
    return false;
}


// === ZFC pattern matching ===

class Capture {
    constructor(name) { this.name = name; }
}

const ANY = new Capture("_");

function pmatch(pattern, formula, bindings) {
    if (!bindings) bindings = {};
    if (pattern instanceof Capture) {
        bindings[pattern.name] = formula;
        return true;
    }
    if (typeof pattern === "string" && typeof formula === "string") {
        if (pattern in bindings) return bindings[pattern] === formula;
        bindings[pattern] = formula;
        return true;
    }
    if (pattern.constructor !== formula.constructor) return false;
    if (pattern instanceof Mem)
        return pmatch(pattern.left, formula.left, bindings) && pmatch(pattern.right, formula.right, bindings);
    if (pattern instanceof Neg)
        return pmatch(pattern.operand, formula.operand, bindings);
    if (pattern instanceof Implies)
        return pmatch(pattern.left, formula.left, bindings) && pmatch(pattern.right, formula.right, bindings);
    if (pattern instanceof Forall)
        return pmatch(pattern.var, formula.var, bindings) && pmatch(pattern.body, formula.body, bindings);
    return false;
}

// Derived helpers for building patterns
function PAnd(a, b) { return new Neg(new Implies(a, new Neg(b))); }
function POr(a, b) { return new Implies(new Neg(a), b); }
function PIff(a, b) { return new Neg(new Implies(new Implies(a, b), new Neg(new Implies(b, a)))); }
function PExists(v, body) { return new Neg(new Forall(v, new Neg(body))); }
function PEqv(a, b, z) { z = z || "_z"; return new Forall(z, PIff(new Mem(z, a), new Mem(z, b))); }

const ZFC = [
    // Extensionality
    new Forall("x", new Forall("y", new Implies(
        new Forall("z", PIff(new Mem("z", "x"), new Mem("z", "y"))),
        new Forall("z", PIff(new Mem("x", "z"), new Mem("y", "z")))))),
    // EmptySet
    PExists("b", new Forall("x", new Neg(new Mem("x", "b")))),
    // Pairing
    new Forall("x", new Forall("y", PExists("b", new Forall("z",
        PIff(new Mem("z", "b"), POr(PEqv("z", "x"), PEqv("z", "y"))))))),
    // Union
    new Forall("a", PExists("b", new Forall("x",
        PIff(new Mem("x", "b"), PExists("y", PAnd(new Mem("y", "a"), new Mem("x", "y"))))))),
    // PowerSet
    new Forall("a", PExists("b", new Forall("x",
        PIff(new Mem("x", "b"), new Forall("y", new Implies(new Mem("y", "x"), new Mem("y", "a"))))))),
    // Infinity
    PExists("b", PAnd(
        PExists("e", PAnd(new Mem("e", "b"), new Forall("z", new Neg(new Mem("z", "e"))))),
        new Forall("y", new Implies(new Mem("y", "b"),
            PExists("s", PAnd(new Mem("s", "b"),
                new Forall("w", PIff(new Mem("w", "s"), POr(new Mem("w", "y"), PEqv("w", "y")))))))))),
    // Regularity
    new Forall("a", new Implies(
        PExists("y", new Mem("y", "a")),
        PExists("y", PAnd(new Mem("y", "a"), new Neg(PExists("z", PAnd(new Mem("z", "a"), new Mem("z", "y")))))))),
    // Choice
    new Forall("x", new Implies(
        new Forall("y", new Implies(new Mem("y", "x"), PExists("z", new Mem("z", "y")))),
        PExists("c", new Forall("y", new Implies(new Mem("y", "x"),
            PExists("z", PAnd(PAnd(new Mem("z", "y"), new Mem("z", "c")),
                new Forall("w", new Implies(PAnd(new Mem("w", "y"), new Mem("w", "c")), PEqv("w", "z")))))))))),
];

function* stripForalls(f) {
    let stripped = [];
    yield [stripped, f];
    while (f instanceof Forall) {
        stripped = [...stripped, f.var];
        f = f.body;
        yield [stripped, f];
    }
}

function isSeparation(f) {
    const phi = new Capture("phi");
    const pat = new Forall("a", PExists("b", new Forall("x",
        PIff(new Mem("x", "b"), PAnd(new Mem("x", "a"), phi)))));
    for (const [stripped, g] of stripForalls(f)) {
        const b = {};
        if (pmatch(pat, g, b)) {
            const allowed = new Set([...stripped, b["a"], b["x"]]);
            if (isSubset(freeVars(b["phi"]), allowed)) return true;
        }
    }
    return false;
}

function isReplacement(f) {
    const phi = new Capture("phi");
    const uniq = new Capture("uniq");
    const pat = new Forall("a", new Implies(uniq, PExists("b", new Forall("y",
        PIff(new Mem("y", "b"), PExists("x", PAnd(new Mem("x", "a"), phi)))))));
    for (const [stripped, g] of stripForalls(f)) {
        const b = {};
        if (pmatch(pat, g, b)) {
            const allowed = new Set([...stripped, b["a"], b["x"], b["y"]]);
            if (isSubset(freeVars(b["phi"]), allowed)) return true;
        }
    }
    return false;
}

function isSubset(a, b) {
    for (const x of a) if (!b.has(x)) return false;
    return true;
}

function isAxiom(f, system) {
    const limit = (system === "z" || system === "zf") ? 7 : 8;
    for (let i = 0; i < limit; i++)
        if (pmatch(ZFC[i], f, {})) return true;
    if (isSeparation(f)) return true;
    if ((system === "zf" || system === "zfc") && isReplacement(f)) return true;
    return false;
}


// === qed ===

function qed(p, expected, system) {
    const s = p.sequent;
    if (s.right.length !== 1)
        throw new Error(`qed: expected 1 formula on right, got ${s.right.length}`);
    if (freeVars(s.right[0]).size > 0)
        throw new Error("qed: theorem has free variables");
    for (const f of s.left)
        if (!isAxiom(f, system))
            throw new Error(`qed: non-axiom on left (system=${system})`);
    if (!same(s.right[0], expected))
        throw new Error("qed: theorem does not match expected");
}


module.exports = {
    Mem, Neg, Implies, Forall, Sequent, Proof, Capture, ANY,
    subst, same, freeVars, boundVars, fin, remove, setAdd,
    proof, qed, pmatch, PAnd, POr, PIff, PExists, PEqv,
    isAxiom, isSeparation, isReplacement,
};
