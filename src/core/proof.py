"""Sequent calculus for first-order logic with set theory language."""

from core.lang import Var, In, Not, Implies, Forall, Formula


def _expand(f):
    while hasattr(f, 'expand'):
        if not hasattr(f, '_cache'):
            f._cache = f.expand()
        f = f._cache
    return f


def same(a, b):
    """Alpha-equivalence after expanding definitions."""
    return _eq(a, b)


class Sequent:
    def __init__(self, left: list[Formula], right: list[Formula]):
        self.left = list(left)
        self.right = list(right)


class Proof:
    def __init__(self, sequent: Sequent, rule: str, premises: list['Proof'] = None,
                 name: str = None, term: Var = None, principal: Formula = None,
                 trusted: bool = False):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []
        self.name = name
        self.term = term
        self.principal = principal
        self.trusted = trusted

    def theorem(self) -> Formula:
        s = self.sequent
        result = s.right[0] if len(s.right) == 1 else None
        for f in reversed(s.left):
            result = Implies(f, result)
        return result


def verify(proof: Proof, axiom_checker, trust=False) -> bool:
    """Verify a proof. axiom_checker(formula) -> bool validates left-side assumptions.
    trust: if True, skip subtrees marked with trusted=True."""
    s = proof.sequent
    if len(s.right) != 1 or _free_vars(s.right[0]):
        return False
    for f in s.left:
        if not axiom_checker(f):
            return False
    return _verify(proof, trust)


def _verify(proof: Proof, trust: bool) -> bool:
    if trust and proof.trusted:
        return True
    for p in proof.premises:
        if not _verify(p, trust):
            return False
    return _check_rule(proof)


def _check_rule(proof: Proof) -> bool:
    s = proof.sequent
    ps = [p.sequent for p in proof.premises]
    principal = _expand(proof.principal) if proof.principal else None

    match proof.rule:
        case "axiom":
            return _check_axiom(s, ps, principal)
        case "not_left":
            return _check_not_left(s, ps, principal)
        case "not_right":
            return _check_not_right(s, ps, principal)
        case "implies_left":
            return _check_implies_left(s, ps, principal)
        case "implies_right":
            return _check_implies_right(s, ps, principal)
        case "forall_left":
            return _check_forall_left(s, ps, principal, proof.term)
        case "forall_right":
            return _check_forall_right(s, ps, principal, proof.term)
        case "cut":
            return _check_cut(s, ps, principal)
        case "weakening_left":
            return _check_weakening_left(s, ps, principal)
        case "weakening_right":
            return _check_weakening_right(s, ps, principal)
    return False


# --- Identity ---

def _check_axiom(s, ps, principal):
    if len(ps) != 0 or principal is None:
        return False
    return _in(principal, s.left) and _in(principal, s.right)


# --- Not ---

def _check_not_left(s, ps, principal):
    if len(ps) != 1 or not isinstance(principal, Not):
        return False
    if not _in(principal, s.left):
        return False
    return _eq_sequent(ps[0], Sequent(
        _remove(s.left, principal), [principal.operand] + s.right))


def _check_not_right(s, ps, principal):
    if len(ps) != 1 or not isinstance(principal, Not):
        return False
    if not _in(principal, s.right):
        return False
    return _eq_sequent(ps[0], Sequent(
        s.left + [principal.operand], _remove(s.right, principal)))


# --- Implies ---

def _check_implies_left(s, ps, principal):
    if len(ps) != 2 or not isinstance(principal, Implies):
        return False
    if not _in(principal, s.left):
        return False
    G = _remove(s.left, principal)
    return (_eq_sequent(ps[0], Sequent(G, [principal.left] + s.right)) and
            _eq_sequent(ps[1], Sequent(G + [principal.right], s.right)))


def _check_implies_right(s, ps, principal):
    if len(ps) != 1 or not isinstance(principal, Implies):
        return False
    if not _in(principal, s.right):
        return False
    D = _remove(s.right, principal)
    return _eq_sequent(ps[0], Sequent(
        s.left + [principal.left], [principal.right] + D))


# --- Forall ---

def _check_forall_left(s, ps, principal, t):
    if len(ps) != 1 or t is None or not isinstance(principal, Forall):
        return False
    if not _in(principal, s.left):
        return False
    G = _remove(s.left, principal)
    substituted = _subst(principal.body, principal.var, t)
    return _eq_sequent(ps[0], Sequent(G + [substituted], s.right))


def _check_forall_right(s, ps, principal, y):
    if len(ps) != 1 or y is None or not isinstance(principal, Forall):
        return False
    if not _in(principal, s.right):
        return False
    D = _remove(s.right, principal)
    if _var_free_in_sequent(y, Sequent(s.left, D)):
        return False
    substituted = _subst(principal.body, principal.var, y)
    return _eq_sequent(ps[0], Sequent(s.left, [substituted] + D))


# --- Cut ---

def _check_cut(s, ps, principal):
    if len(ps) != 2 or principal is None:
        return False
    return (_eq_sequent(ps[0], Sequent(s.left, [principal] + s.right)) and
            _eq_sequent(ps[1], Sequent(s.left + [principal], s.right)))


# --- Structural ---

def _check_weakening_left(s, ps, principal):
    if len(ps) != 1 or principal is None:
        return False
    if not _in(principal, s.left):
        return False
    return _eq_sequent(ps[0], Sequent(_remove(s.left, principal), s.right))


def _check_weakening_right(s, ps, principal):
    if len(ps) != 1 or principal is None:
        return False
    if not _in(principal, s.right):
        return False
    return _eq_sequent(ps[0], Sequent(s.left, _remove(s.right, principal)))


# --- Formula equality (alpha-equivalence, expands definitions) ---

def _eq(a, b, env=None):
    if a is b:
        return True
    if env is None:
        env = []
    a = _expand(a)
    b = _expand(b)
    if type(a) is not type(b):
        return False
    match a:
        case Var():
            return _eq_var(a, b, env)
        case In(l1, r1):
            return _eq(l1, b.left, env) and _eq(r1, b.right, env)
        case Not(o1):
            return _eq(o1, b.operand, env)
        case Implies(l1, r1):
            return _eq(l1, b.left, env) and _eq(r1, b.right, env)
        case Forall(v1, b1):
            return _eq(b1, b.body, env + [(v1, b.var)])
    return False


def _eq_var(v1, v2, env):
    for left, right in reversed(env):
        if v1 is left and v2 is right:
            return True
        if v1 is left or v2 is right:
            return False
    return v1 is v2


def _in(f, lst):
    return any(same(f, g) for g in lst)


def _remove(lst, f):
    result = []
    removed = False
    for g in lst:
        if not removed and same(f, g):
            removed = True
        else:
            result.append(g)
    return result


def _eq_sequent(a, b):
    return _is_permutation(a.left, b.left) and _is_permutation(a.right, b.right)


def _is_permutation(a, b):
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


# --- Substitution (works on expanded formulas) ---

def _subst(formula, old, new):
    formula = _expand(formula)
    match formula:
        case In(left, right):
            return In(new if left is old else left,
                      new if right is old else right)
        case Not(operand):
            return Not(_subst(operand, old, new))
        case Implies(left, right):
            return Implies(_subst(left, old, new), _subst(right, old, new))
        case Forall(var, body):
            if var is old:
                return formula
            return Forall(var, _subst(body, old, new))


def _free_vars(formula, bound=None):
    if bound is None:
        bound = set()
    formula = _expand(formula)
    match formula:
        case In(left, right):
            result = set()
            if left not in bound:
                result.add(left)
            if right not in bound:
                result.add(right)
            return result
        case Not(operand):
            return _free_vars(operand, bound)
        case Implies(left, right):
            return _free_vars(left, bound) | _free_vars(right, bound)
        case Forall(var, body):
            return _free_vars(body, bound | {var})
    return set()


def _var_free_in_sequent(var, s):
    return any(var in _free_vars(f) for f in s.left + s.right)
