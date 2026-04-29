"""Sequent calculus for first-order logic with set theory language."""

from ring0.lang import Var, In, Not, Implies, Forall, Formula


def _expand(f):
    while hasattr(f, 'expand'):
        if not hasattr(f, '_cache'):
            f._cache = f.expand()
        f = f._cache
    return f



class Sequent:
    def __init__(self, left, right):
        self.left = set(left)
        self.right = set(right)
        assert len(self.left) == len(list(left))
        assert len(self.right) == len(list(right))


class Proof:
    def __init__(self, sequent: Sequent, rule: str, premises: list['Proof'] = None,
                 name: str = None, term: Var = None, principal: Formula = None,
                 trusted: bool = False, substituted: Formula = None):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []
        self.name = name
        self.term = term
        self.principal = principal
        self.trusted = trusted
        self.substituted = substituted

    def theorem(self) -> Formula:
        s = self.sequent
        result = s.right[0] if len(s.right) == 1 else None
        for f in reversed(s.left):
            result = Implies(f, result)
        return result


def verify(proof: Proof, axiom_checker, trust=False, cache=True) -> bool:
    """Verify a proof. axiom_checker(formula) -> bool validates left-side assumptions.
    trust: if True, skip subtrees marked with trusted=True.
    cache: if True, mark verified nodes and skip them on re-encounter."""
    s = proof.sequent
    if len(s.right) != 1 or _free_vars(next(iter(s.right))):
        return False
    for f in s.left:
        if not axiom_checker(f):
            return False
    return _verify(proof, trust, cache)


def _verify(proof: Proof, trust: bool, cache: bool) -> bool:
    if cache and getattr(proof, '_verified', False):
        return True
    if trust and proof.trusted:
        return True
    for p in proof.premises:
        if not _verify(p, trust, cache):
            return False
    if not _check_rule(proof):
        return False
    proof._verified = True
    return True


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
            return _check_forall_left(s, ps, principal, proof.term, proof.substituted)
        case "forall_right":
            return _check_forall_right(s, ps, principal, proof.term, proof.substituted)
        case "cut":
            return _check_cut(s, ps, principal)
        case "weakening_left":
            return _check_weakening_left(s, ps, principal)
        case "weakening_right":
            return _check_weakening_right(s, ps, principal)
    return False


# --- Identity ---

def _check_axiom(s, ps, principal):
    """A |- A. Principal must be in both left and right."""
    if len(ps) != 0 or principal is None:
        return False
    return _in(principal, s.left) and _in(principal, s.right)


# --- Not ---

def _check_not_left(s, ps, principal):
    """G, Not(A) |- D  from  G |- D, A.
    Principal Not(A) on left; premise moves A to right."""
    if len(ps) != 1 or not isinstance(principal, Not):
        return False
    if not _in(principal, s.left):
        return False
    return _eq_sequent(ps[0], Sequent(
        _remove(s.left, principal), _set_add(s.right, principal.operand)))


def _check_not_right(s, ps, principal):
    """G |- D, Not(A)  from  G, A |- D.
    Principal Not(A) on right; premise moves A to left."""
    if len(ps) != 1 or not isinstance(principal, Not):
        return False
    if not _in(principal, s.right):
        return False
    return _eq_sequent(ps[0], Sequent(
        _set_add(s.left, principal.operand), _remove(s.right, principal)))


# --- Implies ---

def _check_implies_left(s, ps, principal):
    """G, A->B |- D  from  G |- D, A  and  G, B |- D.
    Principal A->B on left; prem0 proves A, prem1 uses B."""
    if len(ps) != 2 or not isinstance(principal, Implies):
        return False
    if not _in(principal, s.left):
        return False
    G = _remove(s.left, principal)
    return (_eq_sequent(ps[0], Sequent(G, _set_add(s.right, principal.left))) and
            _eq_sequent(ps[1], Sequent(_set_add(G, principal.right), s.right)))


def _check_implies_right(s, ps, principal):
    """G |- D, A->B  from  G, A |- D, B.
    Principal A->B on right; premise assumes A and proves B."""
    if len(ps) != 1 or not isinstance(principal, Implies):
        return False
    if not _in(principal, s.right):
        return False
    D = _remove(s.right, principal)
    return _eq_sequent(ps[0], Sequent(
        _set_add(s.left, principal.left), _set_add(D, principal.right)))


# --- Forall ---

def _check_forall_left(s, ps, principal, t, substituted):
    """G, Forall(x,A) |- D  from  G, A[x:=t] |- D.
    Principal Forall(x,A) on left; premise instantiates x with term t."""
    if len(ps) != 1 or t is None or substituted is None or not isinstance(principal, Forall):
        return False
    if not _in(principal, s.left):
        return False
    G = _remove(s.left, principal)
    return _eq_sequent(ps[0], Sequent(_set_add(G, substituted), s.right))


def _check_forall_right(s, ps, principal, y, substituted):
    """G |- D, Forall(x,A)  from  G |- D, A[x:=y].
    Principal Forall(x,A) on right; y is eigenvariable (fresh, not free in G or D)."""
    if len(ps) != 1 or y is None or substituted is None or not isinstance(principal, Forall):
        return False
    if not _in(principal, s.right):
        return False
    D = _remove(s.right, principal)
    if _var_free_in_sequent(y, Sequent(s.left, D)):
        return False
    if _var_bound_in(y, principal.body):
        return False
    return _eq_sequent(ps[0], Sequent(s.left, _set_add(D, substituted)))


# --- Cut ---

def _check_cut(s, ps, principal):
    """G |- D  from  G |- D, C  and  G, C |- D.
    Principal C is the cut formula; appears on prem0 right and prem1 left."""
    if len(ps) != 2 or principal is None:
        return False
    return (_eq_sequent(ps[0], Sequent(s.left, _set_add(s.right, principal))) and
            _eq_sequent(ps[1], Sequent(_set_add(s.left, principal), s.right)))


# --- Structural ---

def _check_weakening_left(s, ps, principal):
    """G, A |- D  from  G |- D.
    Principal A added to left. No-op if A already in premise."""
    if len(ps) != 1 or principal is None:
        return False
    if not _in(principal, s.left):
        return False
    if _in(principal, ps[0].left):
        return _eq_sequent(ps[0], s)
    return _eq_sequent(ps[0], Sequent(_remove(s.left, principal), s.right))


def _check_weakening_right(s, ps, principal):
    """G |- D, A  from  G |- D.
    Principal A added to right. No-op if A already in premise."""
    if len(ps) != 1 or principal is None:
        return False
    if not _in(principal, s.right):
        return False
    if _in(principal, ps[0].right):
        return _eq_sequent(ps[0], s)
    return _eq_sequent(ps[0], Sequent(s.left, _remove(s.right, principal)))


# --- Formula equality (alpha-equivalence, expands definitions) ---

def _in(f, s):
    return f in s


def _remove(s, f):
    return s - {f}


def _set_add(s, f):
    return s | {f}


def _eq_sequent(a, b):
    return a.left == b.left and a.right == b.right


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


def _var_bound_in(var, formula):
    """Check if var appears as a binding variable in any Forall inside formula."""
    formula = _expand(formula)
    match formula:
        case In():
            return False
        case Not(operand):
            return _var_bound_in(var, operand)
        case Implies(left, right):
            return _var_bound_in(var, left) or _var_bound_in(var, right)
        case Forall(v, body):
            if v is var:
                return True
            return _var_bound_in(var, body)
    return False


def _var_free_in_sequent(var, s):
    return any(var in _free_vars(f) for f in s.left | s.right)
