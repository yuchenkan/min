"""Sequent calculus for first-order logic with set theory language."""

from core.lang import Var, In, Not, Implies, Forall, Formula


def expand_all(formula):
    while hasattr(formula, 'expand'):
        formula = formula.expand()
    match formula:
        case Not(operand):
            return Not(expand_all(operand))
        case Implies(left, right):
            return Implies(expand_all(left), expand_all(right))
        case Forall(var, body):
            return Forall(var, expand_all(body))
        case _:
            return formula


class Sequent:
    def __init__(self, left: list[Formula], right: list[Formula]):
        self.left = list(left)
        self.right = list(right)


class Proof:
    def __init__(self, sequent: Sequent, rule: str, premises: list['Proof'] = None,
                 name: str = None, term: Var = None, principal: Formula = None):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []
        self.name = name
        self.term = term
        self.principal = principal

    def theorem(self) -> Formula:
        s = self.sequent
        result = s.right[0] if len(s.right) == 1 else None
        for f in reversed(s.left):
            result = Implies(f, result)
        return result


def _expand_sequent(s: Sequent) -> Sequent:
    return Sequent([expand_all(f) for f in s.left], [expand_all(f) for f in s.right])


def _expand_proof(proof: Proof) -> Proof:
    return Proof(
        _expand_sequent(proof.sequent),
        proof.rule,
        [_expand_proof(p) for p in proof.premises],
        term=proof.term,
        principal=expand_all(proof.principal) if proof.principal else None)


def verify(proof: Proof) -> bool:
    return _verify(_expand_proof(proof))


def _verify(proof: Proof) -> bool:
    for p in proof.premises:
        if not _verify(p):
            return False
    return _check_rule(proof)


def _check_rule(proof: Proof) -> bool:
    s = proof.sequent
    ps = [p.sequent for p in proof.premises]
    A = proof.principal

    match proof.rule:
        case "axiom":
            return _check_axiom(s, ps, A)
        case "not_left":
            return _check_not_left(s, ps, A)
        case "not_right":
            return _check_not_right(s, ps, A)
        case "implies_left":
            return _check_implies_left(s, ps, A)
        case "implies_right":
            return _check_implies_right(s, ps, A)
        case "forall_left":
            return _check_forall_left(s, ps, A, proof.term)
        case "forall_right":
            return _check_forall_right(s, ps, A, proof.term)
        case "cut":
            return _check_cut(s, ps, A)
        case "weakening_left":
            return _check_weakening_left(s, ps, A)
        case "weakening_right":
            return _check_weakening_right(s, ps, A)
    return False


# --- Identity ---

# G, A |- A, D
def _check_axiom(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 0 or A is None:
        return False
    return _in(A, s.left) and _in(A, s.right)


# --- Not ---

# from G |- A, D  derive  G, ~A |- D
def _check_not_left(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 1 or not isinstance(A, Not):
        return False
    if not _in(A, s.left):
        return False
    return _eq_sequent(ps[0], Sequent(_remove(s.left, A), [A.operand] + s.right))


# from G, A |- D  derive  G |- ~A, D
def _check_not_right(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 1 or not isinstance(A, Not):
        return False
    if not _in(A, s.right):
        return False
    return _eq_sequent(ps[0], Sequent(s.left + [A.operand], _remove(s.right, A)))


# --- Implies ---

# from G |- A, D  and  G, B |- D  derive  G, A->B |- D
def _check_implies_left(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 2 or not isinstance(A, Implies):
        return False
    if not _in(A, s.left):
        return False
    G = _remove(s.left, A)
    return (_eq_sequent(ps[0], Sequent(G, [A.left] + s.right)) and
            _eq_sequent(ps[1], Sequent(G + [A.right], s.right)))


# from G, A |- B, D  derive  G |- A->B, D
def _check_implies_right(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 1 or not isinstance(A, Implies):
        return False
    if not _in(A, s.right):
        return False
    D = _remove(s.right, A)
    return _eq_sequent(ps[0], Sequent(s.left + [A.left], [A.right] + D))


# --- Forall ---

# from G, A[t/x] |- D  derive  G, Ax.A |- D
def _check_forall_left(s: Sequent, ps: list[Sequent], A: Formula, t: Var) -> bool:
    if len(ps) != 1 or t is None or not isinstance(A, Forall):
        return False
    if not _in(A, s.left):
        return False
    G = _remove(s.left, A)
    substituted = _subst(A.body, A.var, t)
    return _eq_sequent(ps[0], Sequent(G + [substituted], s.right))


# from G |- A[y/x], D  where y not in G, D  derive  G |- Ax.A, D
def _check_forall_right(s: Sequent, ps: list[Sequent], A: Formula, y: Var) -> bool:
    if len(ps) != 1 or y is None or not isinstance(A, Forall):
        return False
    if not _in(A, s.right):
        return False
    D = _remove(s.right, A)
    if _var_free_in_sequent(y, Sequent(s.left, D)):
        return False
    substituted = _subst(A.body, A.var, y)
    return _eq_sequent(ps[0], Sequent(s.left, [substituted] + D))


# --- Cut ---

# from G |- A, D  and  G, A |- D  derive  G |- D
def _check_cut(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 2 or A is None:
        return False
    return (_eq_sequent(ps[0], Sequent(s.left, [A] + s.right)) and
            _eq_sequent(ps[1], Sequent(s.left + [A], s.right)))


# --- Structural ---

# from G |- D  derive  G, A |- D
def _check_weakening_left(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 1 or A is None:
        return False
    if not _in(A, s.left):
        return False
    return _eq_sequent(ps[0], Sequent(_remove(s.left, A), s.right))


# from G |- D  derive  G |- A, D
def _check_weakening_right(s: Sequent, ps: list[Sequent], A: Formula) -> bool:
    if len(ps) != 1 or A is None:
        return False
    if not _in(A, s.right):
        return False
    return _eq_sequent(ps[0], Sequent(s.left, _remove(s.right, A)))


# --- Formula equality (alpha-equivalence) ---

def formula_eq(a, b, env=None):
    if env is None:
        env = []
    if type(a) is not type(b):
        return False
    match a:
        case In(l1, r1):
            return _eq_var(l1, b.left, env) and _eq_var(r1, b.right, env)
        case Not(o1):
            return formula_eq(o1, b.operand, env)
        case Implies(l1, r1):
            return formula_eq(l1, b.left, env) and formula_eq(r1, b.right, env)
        case Forall(v1, b1):
            return formula_eq(b1, b.body, env + [(v1, b.var)])
    return False


def _eq_var(v1, v2, env):
    for left, right in reversed(env):
        if v1 is left and v2 is right:
            return True
        if v1 is left or v2 is right:
            return False
    return v1 is v2


def _in(f, lst):
    """Check if f is in lst by alpha-equiv."""
    return any(formula_eq(expand_all(f), expand_all(g)) for g in lst)


def _remove(lst, f):
    """Remove first occurrence of f from lst by alpha-equiv."""
    ef = expand_all(f)
    result = []
    removed = False
    for g in lst:
        if not removed and formula_eq(ef, expand_all(g)):
            removed = True
        else:
            result.append(g)
    return result


def _eq_sequent(a, b):
    """Sequents are equal as sets (multisets with alpha-equiv)."""
    return _is_permutation(a.left, b.left) and _is_permutation(a.right, b.right)


def _is_permutation(a, b):
    if len(a) != len(b):
        return False
    used = [False] * len(b)
    for f in a:
        ef = expand_all(f)
        found = False
        for j, g in enumerate(b):
            if not used[j] and formula_eq(ef, expand_all(g)):
                used[j] = True
                found = True
                break
        if not found:
            return False
    return True


# --- Substitution helpers ---

def _subst(formula, old, new):
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


def _var_free_in(var, formula):
    match formula:
        case In(left, right):
            return left is var or right is var
        case Not(operand):
            return _var_free_in(var, operand)
        case Implies(left, right):
            return _var_free_in(var, left) or _var_free_in(var, right)
        case Forall(v, body):
            if v is var:
                return False
            return _var_free_in(var, body)
    return False


def _var_free_in_sequent(var, s):
    return any(_var_free_in(var, f) for f in s.left + s.right)
