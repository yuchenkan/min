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
        self.left = left
        self.right = right


class Proof:
    def __init__(self, sequent: Sequent, rule: str, premises: list['Proof'] = None, name: str = None, term: Var = None):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []
        self.name = name
        self.term = term

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
        term=proof.term)


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
            return _check_axiom(s, ps)
        case "not_left":
            return _check_not_left(s, ps)
        case "not_right":
            return _check_not_right(s, ps)
        case "implies_left":
            return _check_implies_left(s, ps)
        case "implies_right":
            return _check_implies_right(s, ps)
        case "forall_left":
            return _check_forall_left(s, ps, proof.term)
        case "forall_right":
            return _check_forall_right(s, ps, proof.term)
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
        case "exchange_left":
            return _check_exchange_left(s, ps)
        case "exchange_right":
            return _check_exchange_right(s, ps)
    return False


# --- Identity ---

# G, A |- A, D
def _check_axiom(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 0 or not s.left or not s.right:
        return False
    return _eq(s.left[-1], s.right[0])


# --- Not ---

# from G |- A, D  derive  G, ~A |- D
def _check_not_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.left or not isinstance(s.left[-1], Not):
        return False
    f = s.left[-1]
    return _eq_sequent(ps[0], Sequent(s.left[:-1], [f.operand] + s.right))


# from G, A |- D  derive  G |- ~A, D
def _check_not_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.right or not isinstance(s.right[0], Not):
        return False
    f = s.right[0]
    return _eq_sequent(ps[0], Sequent(s.left + [f.operand], s.right[1:]))


# --- Implies ---

# from G |- A, D  and  G, B |- D  derive  G, A->B |- D
def _check_implies_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 2 or not s.left or not isinstance(s.left[-1], Implies):
        return False
    f = s.left[-1]
    G = s.left[:-1]
    return (_eq_sequent(ps[0], Sequent(G, [f.left] + s.right)) and
            _eq_sequent(ps[1], Sequent(G + [f.right], s.right)))


# from G, A |- B, D  derive  G |- A->B, D
def _check_implies_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.right or not isinstance(s.right[0], Implies):
        return False
    f = s.right[0]
    return _eq_sequent(ps[0], Sequent(s.left + [f.left], [f.right] + s.right[1:]))


# --- Forall ---

# from G, A[t/x] |- D  derive  G, Ax.A |- D
def _check_forall_left(s: Sequent, ps: list[Sequent], t: Var) -> bool:
    if len(ps) != 1 or t is None:
        return False
    if not s.left or not isinstance(s.left[-1], Forall):
        return False
    f = s.left[-1]
    expected = Sequent(s.left[:-1] + [_subst(f.body, f.var, t)], s.right)
    return _eq_sequent(ps[0], expected)


# from G |- A[y/x], D  where y not in G, D  derive  G |- Ax.A, D
def _check_forall_right(s: Sequent, ps: list[Sequent], y: Var) -> bool:
    if len(ps) != 1 or y is None:
        return False
    if not s.right or not isinstance(s.right[0], Forall):
        return False
    f = s.right[0]
    D = s.right[1:]
    if _var_free_in_sequent(y, Sequent(s.left, D)):
        return False
    expected = Sequent(s.left, [_subst(f.body, f.var, y)] + D)
    return _eq_sequent(ps[0], expected)


# --- Cut ---

# from G |- A, D  and  G, A |- D  derive  G |- D
def _check_cut(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 2:
        return False
    if not ps[0].right or not ps[1].left:
        return False
    a = ps[0].right[0]
    return (_eq_list(ps[0].left, s.left) and
            _eq_list(ps[0].right[1:], s.right) and
            _eq_list(ps[1].left[:-1], s.left) and
            _eq_list(ps[1].right, s.right) and
            _eq(a, ps[1].left[-1]))


# --- Structural ---

# from G |- D  derive  G, A |- D
def _check_weakening_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.left:
        return False
    return _eq_sequent(ps[0], Sequent(s.left[:-1], s.right))


# from G |- D  derive  G |- A, D
def _check_weakening_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.right:
        return False
    return _eq_sequent(ps[0], Sequent(s.left, s.right[1:]))


# from G, A, A |- D  derive  G, A |- D
def _check_contraction_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.left:
        return False
    return _eq_sequent(ps[0], Sequent(s.left + [s.left[-1]], s.right))


# from G |- A, A, D  derive  G |- A, D
def _check_contraction_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1 or not s.right:
        return False
    return _eq_sequent(ps[0], Sequent(s.left, [s.right[0]] + s.right))


# --- Exchange ---

# from G |- D  derive  G' |- D  where G' is a permutation of G
def _check_exchange_left(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    if not _eq_list(s.right, ps[0].right):
        return False
    return _is_permutation(s.left, ps[0].left)


# from G |- D  derive  G |- D'  where D' is a permutation of D
def _check_exchange_right(s: Sequent, ps: list[Sequent]) -> bool:
    if len(ps) != 1:
        return False
    if not _eq_list(s.left, ps[0].left):
        return False
    return _is_permutation(s.right, ps[0].right)


def _is_permutation(a: list[Formula], b: list[Formula]) -> bool:
    if len(a) != len(b):
        return False
    used = [False] * len(b)
    for f in a:
        found = False
        for j, g in enumerate(b):
            if not used[j] and _eq(f, g):
                used[j] = True
                found = True
                break
        if not found:
            return False
    return True


# --- Formula equality (alpha-equivalence) ---

def _eq(a: Formula, b: Formula, env=None) -> bool:
    if env is None:
        env = []
    if type(a) is not type(b):
        return False
    match a:
        case In(l1, r1):
            return _eq_var(l1, b.left, env) and _eq_var(r1, b.right, env)
        case Not(o1):
            return _eq(o1, b.operand, env)
        case Implies(l1, r1):
            return _eq(l1, b.left, env) and _eq(r1, b.right, env)
        case Forall(v1, b1):
            return _eq(b1, b.body, env + [(v1, b.var)])
    return False


def _eq_var(v1: Var, v2: Var, env: list) -> bool:
    for left, right in reversed(env):
        if v1 is left and v2 is right:
            return True
        if v1 is left or v2 is right:
            return False
    return v1 is v2


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


def _find_subst_term(body: Formula, var: Var, result: Formula, env=None):
    """Given body, var, result: find t such that body[t/var] = result.
    env tracks bound variable pairs for alpha-equivalence."""
    if env is None:
        env = []
    if type(body) is not type(result):
        return None
    match body:
        case In(l, r):
            tl = _match_var(l, var, result.left, env)
            tr = _match_var(r, var, result.right, env)
            if tl is None and tr is None:
                if _eq_var(l, result.left, env) and _eq_var(r, result.right, env):
                    return Var()  # dummy, var not used
                return None
            if tl is not None and tr is not None:
                if tl is not tr:
                    return None
            return tl or tr
        case Not(o):
            return _find_subst_term(o, var, result.operand, env)
        case Implies(l, r):
            tl = _find_subst_term(l, var, result.left, env)
            tr = _find_subst_term(r, var, result.right, env)
            if tl is not None and tr is not None and tl is not tr:
                return None
            return tl or tr
        case Forall(v, b):
            if v is var:
                if _eq(body, result, env):
                    return Var()  # shadowed, any term works
                return None
            return _find_subst_term(b, var, result.body, env + [(v, result.var)])
    return None


def _match_var(orig: Var, var: Var, target: Var, env: list):
    if orig is var:
        return target
    if _eq_var(orig, target, env):
        return None  # no substitution needed
    return None


def _free_vars(formula: Formula, bound=None) -> set:
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
