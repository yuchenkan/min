"""Sequent calculus for first-order logic with set theory language."""

from core.lang import Var, In, Not, Implies, Forall, Formula


def expand_all(formula):
    while hasattr(formula, 'expand'):
        formula = formula.expand_all()
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
        self.left = left
        self.right = right


class Proof:
    def __init__(self, sequent: Sequent, rule: str, premises: list['Proof'] = None):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []

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
        [_expand_proof(p) for p in proof.premises])


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

    match proof.rule:
        case "axiom":
            return _check_axiom(s)
        case "not_left":
            return _check_not_left(s, ps)
        case "not_right":
            return _check_not_right(s, ps)
        case "implies_left":
            return _check_implies_left(s, ps)
        case "implies_right":
            return _check_implies_right(s, ps)
        case "forall_left":
            return _check_forall_left(s, ps)
        case "forall_right":
            return _check_forall_right(s, ps)
        case "cut":
            return _check_cut(s, ps)
        case "weakening_left":
            return _check_weakening_left(s, ps)
        case "weakening_right":
            return _check_weakening_right(s, ps)
        case "contraction_left":
            return _check_contraction_left(s, ps)
        case "contraction_right":
            return _check_contraction_right(s, ps)
    return False


# --- Identity ---

# G, A |- A, D
def _check_axiom(s: Sequent) -> bool:
    for a in s.left:
        for b in s.right:
            if _eq(a, b):
                return True
    return False


# --- Not ---

# from G |- A, D  derive  G, ~A |- D
def _check_not_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    for i, f in enumerate(s.left):
        if isinstance(f, Not):
            expected_right = [f.operand] + s.right
            expected_left = s.left[:i] + s.left[i+1:]
            if _eq_sequent(ps[0], Sequent(expected_left, expected_right)):
                return True
    return False


# from G, A |- D  derive  G |- ~A, D
def _check_not_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    for i, f in enumerate(s.right):
        if isinstance(f, Not):
            expected_left = s.left + [f.operand]
            expected_right = s.right[:i] + s.right[i+1:]
            if _eq_sequent(ps[0], Sequent(expected_left, expected_right)):
                return True
    return False


# --- Implies ---

# from G |- A, D  and  G, B |- D  derive  G, A->B |- D
def _check_implies_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 2:
        return False
    for i, f in enumerate(s.left):
        if isinstance(f, Implies):
            rest_left = s.left[:i] + s.left[i+1:]
            p0 = Sequent(rest_left, [f.left] + s.right)
            p1 = Sequent(rest_left + [f.right], s.right)
            if _eq_sequent(ps[0], p0) and _eq_sequent(ps[1], p1):
                return True
    return False


# from G, A |- B, D  derive  G |- A->B, D
def _check_implies_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    for i, f in enumerate(s.right):
        if isinstance(f, Implies):
            expected_left = s.left + [f.left]
            expected_right = s.right[:i] + [f.right] + s.right[i+1:]
            if _eq_sequent(ps[0], Sequent(expected_left, expected_right)):
                return True
    return False


# --- Forall ---

# from G, A[t/x] |- D  derive  G, Ax.A |- D
def _check_forall_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    for i, f in enumerate(s.left):
        if isinstance(f, Forall):
            rest_left = s.left[:i] + s.left[i+1:]
            # find what term was substituted
            for g in ps[0].left:
                if g not in rest_left:
                    t = _find_subst_term(f.body, f.var, g)
                    if t is not None:
                        expected = Sequent(rest_left + [g], s.right)
                        if _eq_sequent(ps[0], expected):
                            return True
    return False


# from G |- A[y/x], D  where y not in G, D  derive  G |- Ax.A, D
def _check_forall_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    for i, f in enumerate(s.right):
        if isinstance(f, Forall):
            rest_right = s.right[:i] + s.right[i+1:]
            for g in ps[0].right:
                if g not in rest_right:
                    y = _find_subst_term(f.body, f.var, g)
                    if y is not None and isinstance(y, Var):
                        if not _var_free_in_sequent(y, Sequent(s.left, rest_right)):
                            expected = Sequent(s.left, rest_right + [g])
                            if _eq_sequent(ps[0], expected):
                                return True
    return False


# --- Cut ---

# from G |- A, D  and  G, A |- D  derive  G |- D
def _check_cut(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 2:
        return False
    # try every formula as cut formula
    for a in _all_subformulas(ps[0], ps[1]):
        p0 = Sequent(s.left, [a] + s.right)
        p1 = Sequent(s.left + [a], s.right)
        if _eq_sequent(ps[0], p0) and _eq_sequent(ps[1], p1):
            return True
    return False


# --- Structural ---

# from G |- D  derive  G, A |- D
def _check_weakening_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    p = ps[0]
    return _is_sublist(p.left, s.left) and _eq_list(p.right, s.right)


# from G |- D  derive  G |- A, D
def _check_weakening_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    p = ps[0]
    return _eq_list(p.left, s.left) and _is_sublist(p.right, s.right)


# from G, A, A |- D  derive  G, A |- D
def _check_contraction_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    p = ps[0]
    # p.left should have one extra duplicate compared to s.left
    for i, f in enumerate(s.left):
        expanded = s.left[:i] + [f] + s.left[i:]
        if _eq_list(expanded, p.left) and _eq_list(s.right, p.right):
            return True
    return False


# from G |- A, A, D  derive  G |- A, D
def _check_contraction_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    p = ps[0]
    for i, f in enumerate(s.right):
        expanded = s.right[:i] + [f] + s.right[i:]
        if _eq_list(s.left, p.left) and _eq_list(expanded, p.right):
            return True
    return False


# --- Formula equality (structural, by identity for Var) ---

def _eq(a: Formula, b: Formula) -> bool:
    if type(a) is not type(b):
        return False
    match a:
        case In(l1, r1):
            return l1 is b.left and r1 is b.right
        case Not(o1):
            return _eq(o1, b.operand)
        case Implies(l1, r1):
            return _eq(l1, b.left) and _eq(r1, b.right)
        case Forall(v1, b1):
            return v1 is b.var and _eq(b1, b.body)
    return False


def _eq_list(a: list[Formula], b: list[Formula]) -> bool:
    if len(a) != len(b):
        return False
    return all(_eq(x, y) for x, y in zip(a, b))


def _eq_sequent(a: Sequent, b: Sequent) -> bool:
    return _eq_list(a.left, b.left) and _eq_list(a.right, b.right)


def _is_sublist(small: list[Formula], big: list[Formula]) -> bool:
    j = 0
    for f in big:
        if j < len(small) and _eq(f, small[j]):
            j += 1
    return j == len(small)


# --- Substitution helpers ---

def _subst(formula: Formula, old: Var, new: Var) -> Formula:
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


def _find_subst_term(body: Formula, var: Var, result: Formula):
    """Given body, var, result: find t such that body[t/var] = result."""
    if type(body) is not type(result):
        return None
    match body:
        case In(l, r):
            tl = _match_var(l, var, result.left)
            tr = _match_var(r, var, result.right)
            if tl is None and tr is None:
                if l is result.left and r is result.right:
                    return Var()  # dummy, var not used
                return None
            if tl is not None and tr is not None:
                if tl is not tr:
                    return None
            return tl or tr
        case Not(o):
            return _find_subst_term(o, var, result.operand)
        case Implies(l, r):
            tl = _find_subst_term(l, var, result.left)
            tr = _find_subst_term(r, var, result.right)
            if tl is not None and tr is not None and tl is not tr:
                return None
            return tl or tr
        case Forall(v, b):
            if v is var:
                if _eq(body, result):
                    return Var()  # shadowed, any term works
                return None
            if v is not result.var:
                return None
            return _find_subst_term(b, var, result.body)
    return None


def _match_var(orig: Var, var: Var, target: Var):
    if orig is var:
        return target
    if orig is target:
        return None  # no substitution needed
    return None


def _var_free_in(var: Var, formula: Formula) -> bool:
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


def _var_free_in_sequent(var: Var, s: Sequent) -> bool:
    return any(_var_free_in(var, f) for f in s.left + s.right)


def _all_subformulas(p0: Sequent, p1: Sequent):
    formulas = []
    for f in p0.right + p1.left:
        formulas.append(f)
    return formulas
