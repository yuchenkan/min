"""Proof kernel: sequent calculus with 10 rules."""


# === Types ===

class Mem:
    def __init__(self, left, right):
        self.left = left
        self.right = right

class Neg:
    def __init__(self, operand):
        self.operand = operand

class Implies:
    def __init__(self, left, right):
        self.left = left
        self.right = right

class Forall:
    def __init__(self, var, body):
        self.var = var
        self.body = body

class Sequent:
    def __init__(self, left, right):
        _check_set(left)
        _check_set(right)
        self.left = left
        self.right = right

def _check_set(lst):
    for i, a in enumerate(lst):
        for j in range(i + 1, len(lst)):
            if same(a, lst[j]):
                raise ValueError(f'sequent: duplicate formula')

class Proof:
    def __init__(self, sequent):
        self.sequent = sequent


# === Substitution ===

def subst(formula, old, new):
    if isinstance(formula, str):
        return new if formula == old else formula
    if isinstance(formula, Mem):
        return Mem(subst(formula.left, old, new), subst(formula.right, old, new))
    if isinstance(formula, Neg):
        return Neg(subst(formula.operand, old, new))
    if isinstance(formula, Implies):
        return Implies(subst(formula.left, old, new), subst(formula.right, old, new))
    if isinstance(formula, Forall):
        if formula.var == old:
            return formula
        return Forall(formula.var, subst(formula.body, old, new))
    raise ValueError(f'cannot subst: {type(formula).__name__}')


# === Alpha-equivalence ===

def same(a, b):
    return eq(a, b, [])

def eq(a, b, env):
    if isinstance(a, str) and isinstance(b, str):
        for v1, v2 in env:
            if a == v1: return b == v2
            if b == v2: return False
        return a == b
    if type(a) is not type(b):
        return False
    if isinstance(a, Mem):
        return eq(a.left, b.left, env) and eq(a.right, b.right, env)
    if isinstance(a, Neg):
        return eq(a.operand, b.operand, env)
    if isinstance(a, Implies):
        return eq(a.left, b.left, env) and eq(a.right, b.right, env)
    if isinstance(a, Forall):
        return eq(a.body, b.body, [(a.var, b.var)] + env)
    return False


# === Free variables ===

def free_vars(formula, bound=None):
    if bound is None:
        bound = set()
    if isinstance(formula, str):
        return {formula} - bound
    if isinstance(formula, Mem):
        return free_vars(formula.left, bound) | free_vars(formula.right, bound)
    if isinstance(formula, Neg):
        return free_vars(formula.operand, bound)
    if isinstance(formula, Implies):
        return free_vars(formula.left, bound) | free_vars(formula.right, bound)
    if isinstance(formula, Forall):
        return free_vars(formula.body, bound | {formula.var})
    return set()


def bound_vars(formula):
    if isinstance(formula, str):
        return set()
    if isinstance(formula, Mem):
        return bound_vars(formula.left) | bound_vars(formula.right)
    if isinstance(formula, Neg):
        return bound_vars(formula.operand)
    if isinstance(formula, Implies):
        return bound_vars(formula.left) | bound_vars(formula.right)
    if isinstance(formula, Forall):
        return {formula.var} | bound_vars(formula.body)
    return set()


# === Helpers ===

def fin(f, lst):
    return any(same(f, g) for g in lst)

def remove(lst, f):
    result = []
    removed = False
    for g in lst:
        if not removed and same(f, g):
            removed = True
        else:
            result.append(g)
    return result

def set_add(lst, f):
    if fin(f, lst):
        return list(lst)
    return list(lst) + [f]

def eq_sequent(a, b):
    return is_permutation(a.left, b.left) and is_permutation(a.right, b.right)

def is_permutation(a, b):
    if len(a) != len(b):
        return False
    used = [False] * len(b)
    for f in a:
        found = False
        for j, g in enumerate(b):
            if not used[j] and same(f, g):
                used[j] = True
                found = True
                break
        if not found:
            return False
    return True


# === Proof rules ===

def proof(seq, rule, premises, principal, term=None):
    if not check_rule(seq, rule, premises, principal, term):
        raise ValueError(f'invalid proof step: {rule}')
    return Proof(seq)


def check_rule(s, rule, premises, principal, term):
    ps = [p.sequent for p in premises]

    match rule:
        # A in G, A in D  =>  G |- D
        case "axiom":
            return (len(ps) == 0
                    and fin(principal, s.left) and fin(principal, s.right))
        # G |- D, A  =>  G, ~A |- D
        case "neg_left":
            return (len(ps) == 1 and isinstance(principal, Neg)
                    and fin(principal, s.left)
                    and eq_sequent(ps[0], Sequent(
                        remove(s.left, principal),
                        set_add(s.right, principal.operand))))
        # A, G |- D  =>  G |- D, ~A
        case "neg_right":
            return (len(ps) == 1 and isinstance(principal, Neg)
                    and fin(principal, s.right)
                    and eq_sequent(ps[0], Sequent(
                        set_add(s.left, principal.operand),
                        remove(s.right, principal))))
        # G |- D, A    B, G |- D  =>  G, A->B |- D
        case "implies_left":
            if len(ps) != 2 or not isinstance(principal, Implies):
                return False
            if not fin(principal, s.left):
                return False
            G = remove(s.left, principal)
            return (eq_sequent(ps[0], Sequent(G, set_add(s.right, principal.left)))
                    and eq_sequent(ps[1], Sequent(set_add(G, principal.right), s.right)))
        # A, G |- D, B  =>  G |- D, A->B
        case "implies_right":
            if len(ps) != 1 or not isinstance(principal, Implies):
                return False
            if not fin(principal, s.right):
                return False
            D = remove(s.right, principal)
            return eq_sequent(ps[0], Sequent(
                set_add(s.left, principal.left), set_add(D, principal.right)))
        # p[t/x], G |- D  =>  G, Ax.p |- D   (t is var, no capture)
        case "forall_left":
            if len(ps) != 1 or not isinstance(term, str) or not isinstance(principal, Forall):
                return False
            if not fin(principal, s.left):
                return False
            if term in bound_vars(principal.body):
                return False
            G = remove(s.left, principal)
            substituted = subst(principal.body, principal.var, term)
            return eq_sequent(ps[0], Sequent(set_add(G, substituted), s.right))
        # G |- D, p[t/x]  =>  G |- D, Ax.p   (t eigenvariable: not free in G,D, no capture)
        case "forall_right":
            if len(ps) != 1 or not isinstance(term, str) or not isinstance(principal, Forall):
                return False
            if not fin(principal, s.right):
                return False
            if term in bound_vars(principal.body):
                return False
            D = remove(s.right, principal)
            if any(term in free_vars(f) for f in s.left + D):
                return False
            substituted = subst(principal.body, principal.var, term)
            return eq_sequent(ps[0], Sequent(s.left, set_add(D, substituted)))
        # G |- D, A    A, G |- D  =>  G |- D
        case "cut":
            return (len(ps) == 2
                    and eq_sequent(ps[0], Sequent(s.left, set_add(s.right, principal)))
                    and eq_sequent(ps[1], Sequent(set_add(s.left, principal), s.right)))
        # G |- D  =>  G, A |- D
        case "weakening_left":
            if len(ps) != 1:
                return False
            if not fin(principal, s.left):
                return False
            if fin(principal, ps[0].left):
                return eq_sequent(ps[0], s)
            return eq_sequent(ps[0], Sequent(remove(s.left, principal), s.right))
        # G |- D  =>  G |- D, A
        case "weakening_right":
            if len(ps) != 1:
                return False
            if not fin(principal, s.right):
                return False
            if fin(principal, ps[0].right):
                return eq_sequent(ps[0], s)
            return eq_sequent(ps[0], Sequent(s.left, remove(s.right, principal)))
    return False


# === ZFC pattern matching ===

class Capture:
    def __init__(self, name):
        self.name = name

ANY = Capture('_')

def pmatch(pattern, formula, bindings=None):
    if bindings is None:
        bindings = {}
    if isinstance(pattern, Capture):
        bindings[pattern.name] = formula
        return True
    if isinstance(pattern, str) and isinstance(formula, str):
        if pattern in bindings:
            return bindings[pattern] == formula
        bindings[pattern] = formula
        return True
    if type(pattern) is not type(formula):
        return False
    if isinstance(pattern, Mem):
        return pmatch(pattern.left, formula.left, bindings) and pmatch(pattern.right, formula.right, bindings)
    if isinstance(pattern, Neg):
        return pmatch(pattern.operand, formula.operand, bindings)
    if isinstance(pattern, Implies):
        return pmatch(pattern.left, formula.left, bindings) and pmatch(pattern.right, formula.right, bindings)
    if isinstance(pattern, Forall):
        return pmatch(pattern.var, formula.var, bindings) and pmatch(pattern.body, formula.body, bindings)
    return False

# Derived helpers for building patterns
def PAnd(a, b): return Neg(Implies(a, Neg(b)))
def POr(a, b): return Implies(Neg(a), b)
def PIff(a, b): return Neg(Implies(Implies(a, b), Neg(Implies(b, a))))
def PExists(v, body): return Neg(Forall(v, Neg(body)))
def PEqv(a, b, z="_z"): return Forall(z, PIff(Mem(z, a), Mem(z, b)))

ZFC = [
    # Extensionality
    Forall("x", Forall("y", Implies(
        Forall("z", PIff(Mem("z", "x"), Mem("z", "y"))),
        Forall("z", PIff(Mem("x", "z"), Mem("y", "z")))))),
    # EmptySet
    PExists("b", Forall("x", Neg(Mem("x", "b")))),
    # Pairing
    Forall("x", Forall("y", PExists("b", Forall("z",
        PIff(Mem("z", "b"), POr(PEqv("z", "x"), PEqv("z", "y"))))))),
    # Union
    Forall("a", PExists("b", Forall("x",
        PIff(Mem("x", "b"), PExists("y", PAnd(Mem("y", "a"), Mem("x", "y"))))))),
    # PowerSet
    Forall("a", PExists("b", Forall("x",
        PIff(Mem("x", "b"), Forall("y", Implies(Mem("y", "x"), Mem("y", "a"))))))),
    # Infinity
    PExists("b", PAnd(
        PExists("e", PAnd(Mem("e", "b"), Forall("z", Neg(Mem("z", "e"))))),
        Forall("y", Implies(Mem("y", "b"),
            PExists("s", PAnd(Mem("s", "b"),
                Forall("w", PIff(Mem("w", "s"), POr(Mem("w", "y"), PEqv("w", "y")))))))))),
    # Regularity
    Forall("a", Implies(
        PExists("y", Mem("y", "a")),
        PExists("y", PAnd(Mem("y", "a"), Neg(PExists("z", PAnd(Mem("z", "a"), Mem("z", "y")))))))),
    # Choice
    Forall("x", Implies(
        Forall("y", Implies(Mem("y", "x"), PExists("z", Mem("z", "y")))),
        PExists("c", Forall("y", Implies(Mem("y", "x"),
            PExists("z", PAnd(PAnd(Mem("z", "y"), Mem("z", "c")),
                Forall("w", Implies(PAnd(Mem("w", "y"), Mem("w", "c")), PEqv("w", "z")))))))))),
]

def _strip_foralls(f):
    """Yield (stripped_vars, body) with 0, 1, 2, ... outer foralls stripped."""
    stripped = []
    yield stripped, f
    while isinstance(f, Forall):
        stripped = stripped + [f.var]
        f = f.body
        yield stripped, f

def is_separation(f):
    phi = Capture('phi')
    pat = Forall("a", PExists("b", Forall("x",
        PIff(Mem("x", "b"), PAnd(Mem("x", "a"), phi)))))
    for stripped, g in _strip_foralls(f):
        b = {}
        if pmatch(pat, g, b):
            allowed = set(stripped) | {b["a"], b["x"]}
            if free_vars(b["phi"]) <= allowed:
                return True
    return False

def is_replacement(f):
    phi = Capture('phi')
    uniq = Capture('uniq')
    pat = Forall("a", Implies(uniq, PExists("b", Forall("y",
        PIff(Mem("y", "b"), PExists("x", PAnd(Mem("x", "a"), phi)))))))
    for stripped, g in _strip_foralls(f):
        b = {}
        if pmatch(pat, g, b):
            allowed = set(stripped) | {b["a"], b["x"], b["y"]}
            if free_vars(b["phi"]) <= allowed:
                return True
    return False

# ZFC[0..6] = Ext, Empty, Pair, Union, Power, Inf, Reg
# ZFC[7] = Choice

def is_axiom(f, system):
    # z: no Choice, no Replacement
    # zf: no Choice
    # zfc: all
    limit = 7 if system in ("z", "zf") else 8
    for pattern in ZFC[:limit]:
        if pmatch(pattern, f, {}):
            return True
    if is_separation(f):
        return True
    if system in ("zf", "zfc") and is_replacement(f):
        return True
    return False


# === qed ===

def qed(p, expected, system):
    s = p.sequent
    if len(s.right) != 1:
        raise ValueError(f'qed: expected 1 formula on right, got {len(s.right)}')
    if free_vars(s.right[0]):
        raise ValueError('qed: theorem has free variables')
    for f in s.left:
        if not is_axiom(f, system):
            raise ValueError(f'qed: non-axiom on left (system={system})')
    if not same(s.right[0], expected):
        raise ValueError('qed: theorem does not match expected')
