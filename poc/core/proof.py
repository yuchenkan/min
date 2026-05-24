"""Proof kernel: formula types, sequent calculus, proof rules.

Public API: var, mem, neg, implies, forall, sequent, proof, same
All are factory functions. Internal classes are private."""


# === Internal classes (not exported) ===

class _Var:
    pass


class _Formula:
    pass


class _Mem(_Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class _Neg(_Formula):
    def __init__(self, operand):
        self.operand = operand


class _Implies(_Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class _Forall(_Formula):
    def __init__(self, var, body):
        self.var = var
        self.body = body


class _Sequent:
    def __init__(self, left, right):
        self.left = left
        self.right = right


class _Proof:
    def __init__(self, sequent):
        self.sequent = sequent

    def theorem(self):
        s = self.sequent
        result = s.right[0] if len(s.right) == 1 else None
        for f in reversed(s.left):
            result = _Implies(f, result)
        return result


# === Substitution (internal, uses raw constructors) ===

def _subst(formula, old, new):
    if isinstance(formula, _Mem):
        return _Mem(new if formula.left is old else formula.left,
                    new if formula.right is old else formula.right)
    if isinstance(formula, _Neg):
        return _Neg(_subst(formula.operand, old, new))
    if isinstance(formula, _Implies):
        return _Implies(_subst(formula.left, old, new), _subst(formula.right, old, new))
    if isinstance(formula, _Forall):
        if formula.var is old:
            return formula
        return _Forall(formula.var, _subst(formula.body, old, new))
    raise ValueError(f'cannot subst: {type(formula).__name__}')


# === Alpha-equivalence ===

def same(a, b):
    return _eq(a, b, [])


def _eq(a, b, env):
    if a is b and not env:
        return True
    if type(a) is not type(b):
        return False
    if isinstance(a, _Var):
        for v1, v2 in env:
            if a is v1: return b is v2
            if b is v2: return False
        return a is b
    if isinstance(a, _Mem):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, _Neg):
        return _eq(a.operand, b.operand, env)
    if isinstance(a, _Implies):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, _Forall):
        return _eq(a.body, b.body, [(a.var, b.var)] + env)
    return False


# === Public factories ===

def var():
    return _Var()


def mem(left, right):
    if not isinstance(left, _Var):
        raise TypeError(f'mem: left must be var, got {type(left).__name__}')
    if not isinstance(right, _Var):
        raise TypeError(f'mem: right must be var, got {type(right).__name__}')
    return _Mem(left, right)


def neg(operand):
    if not isinstance(operand, _Formula):
        raise TypeError(f'neg: operand must be formula, got {type(operand).__name__}')
    return _Neg(operand)


def implies(left, right):
    if not isinstance(left, _Formula):
        raise TypeError(f'implies: left must be formula, got {type(left).__name__}')
    if not isinstance(right, _Formula):
        raise TypeError(f'implies: right must be formula, got {type(right).__name__}')
    return _Implies(left, right)


def forall(v, body):
    """Creates forall with a fresh bound var. The user's var is substituted out."""
    if not isinstance(v, _Var):
        raise TypeError(f'forall: var must be var, got {type(v).__name__}')
    if not isinstance(body, _Formula):
        raise TypeError(f'forall: body must be formula, got {type(body).__name__}')
    fresh = _Var()
    return _Forall(fresh, _subst(body, v, fresh))


def sequent(left, right):
    left = list(left)
    right = list(right)
    for f in left:
        if not isinstance(f, _Formula):
            raise TypeError(f'sequent: left must contain formula, got {type(f).__name__}')
    for f in right:
        if not isinstance(f, _Formula):
            raise TypeError(f'sequent: right must contain formula, got {type(f).__name__}')
    for i in range(len(left)):
        for j in range(i + 1, len(left)):
            if _eq(left[i], left[j], []):
                raise ValueError('duplicate on left')
    for i in range(len(right)):
        for j in range(i + 1, len(right)):
            if _eq(right[i], right[j], []):
                raise ValueError('duplicate on right')
    return _Sequent(left, right)


def proof(seq, rule, premises=None, principal=None, term=None):
    """Validate and create a proof step.

    Rules (G = left context, D = right context, A/B = formulas):

    axiom:           A |- A
    neg_left:        G, neg(A) |- D          from  G |- D, A
    neg_right:       G |- D, neg(A)          from  G, A |- D
    implies_left:    G, A->B |- D            from  G |- D, A  and  G, B |- D
    implies_right:   G |- D, A->B            from  G, A |- D, B
    forall_left:     G, forall(x,A) |- D     from  G, A[x:=t] |- D
    forall_right:    G |- D, forall(x,A)     from  G |- D, A[x:=y]  (y fresh)
    cut:             G |- D                  from  G |- D, C  and  G, C |- D
    weakening_left:  G, A |- D               from  G |- D
    weakening_right: G |- D, A               from  G |- D
    """
    if not isinstance(seq, _Sequent):
        raise TypeError(f'proof: sequent required, got {type(seq).__name__}')
    if not isinstance(rule, str):
        raise TypeError(f'proof: rule must be str, got {type(rule).__name__}')
    premises = premises or []
    for p in premises:
        if not isinstance(p, _Proof):
            raise TypeError(f'proof: premises must contain proof, got {type(p).__name__}')
    if term is not None and not isinstance(term, _Var):
        raise TypeError(f'proof: term must be var, got {type(term).__name__}')
    if principal is not None and not isinstance(principal, _Formula):
        raise TypeError(f'proof: principal must be formula, got {type(principal).__name__}')
    if not _check_rule(seq, rule, premises, principal, term):
        raise ValueError(f'invalid proof step: {rule}')
    return _Proof(seq)


# === Proof rules ===

def _check_rule(sequent, rule, premises, principal, term):
    s = sequent
    ps = [p.sequent for p in premises]

    match rule:
        case "axiom":
            return (len(ps) == 0 and principal is not None
                    and _fin(principal, s.left) and _fin(principal, s.right))
        case "neg_left":
            return (len(ps) == 1 and isinstance(principal, _Neg)
                    and _fin(principal, s.left)
                    and _eq_sequent(ps[0], _Sequent(
                        _remove(s.left, principal), _set_add(s.right, principal.operand))))
        case "neg_right":
            return (len(ps) == 1 and isinstance(principal, _Neg)
                    and _fin(principal, s.right)
                    and _eq_sequent(ps[0], _Sequent(
                        _set_add(s.left, principal.operand), _remove(s.right, principal))))
        case "implies_left":
            if len(ps) != 2 or not isinstance(principal, _Implies):
                return False
            if not _fin(principal, s.left):
                return False
            G = _remove(s.left, principal)
            return (_eq_sequent(ps[0], _Sequent(G, _set_add(s.right, principal.left)))
                    and _eq_sequent(ps[1], _Sequent(_set_add(G, principal.right), s.right)))
        case "implies_right":
            if len(ps) != 1 or not isinstance(principal, _Implies):
                return False
            if not _fin(principal, s.right):
                return False
            D = _remove(s.right, principal)
            return _eq_sequent(ps[0], _Sequent(
                _set_add(s.left, principal.left), _set_add(D, principal.right)))
        case "forall_left":
            if len(ps) != 1 or term is None or not isinstance(principal, _Forall):
                return False
            if not _fin(principal, s.left):
                return False
            G = _remove(s.left, principal)
            substituted = _subst(principal.body, principal.var, term)
            return _eq_sequent(ps[0], _Sequent(_set_add(G, substituted), s.right))
        case "forall_right":
            if len(ps) != 1 or term is None or not isinstance(principal, _Forall):
                return False
            if not _fin(principal, s.right):
                return False
            D = _remove(s.right, principal)
            if _var_free_in_sequent(term, _Sequent(s.left, D)):
                return False
            substituted = _subst(principal.body, principal.var, term)
            return _eq_sequent(ps[0], _Sequent(s.left, _set_add(D, substituted)))
        case "cut":
            return (len(ps) == 2 and principal is not None
                    and _eq_sequent(ps[0], _Sequent(s.left, _set_add(s.right, principal)))
                    and _eq_sequent(ps[1], _Sequent(_set_add(s.left, principal), s.right)))
        case "weakening_left":
            if len(ps) != 1 or principal is None:
                return False
            if not _fin(principal, s.left):
                return False
            if _fin(principal, ps[0].left):
                return _eq_sequent(ps[0], s)
            return _eq_sequent(ps[0], _Sequent(_remove(s.left, principal), s.right))
        case "weakening_right":
            if len(ps) != 1 or principal is None:
                return False
            if not _fin(principal, s.right):
                return False
            if _fin(principal, ps[0].right):
                return _eq_sequent(ps[0], s)
            return _eq_sequent(ps[0], _Sequent(s.left, _remove(s.right, principal)))
    return False


# === Helpers ===

def _fin(f, lst):
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

def _set_add(lst, f):
    if _fin(f, lst):
        return list(lst)
    return list(lst) + [f]

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

def _free_vars(formula, bound=None):
    if bound is None:
        bound = set()
    if isinstance(formula, _Mem):
        result = set()
        if formula.left not in bound:
            result.add(formula.left)
        if formula.right not in bound:
            result.add(formula.right)
        return result
    if isinstance(formula, _Neg):
        return _free_vars(formula.operand, bound)
    if isinstance(formula, _Implies):
        return _free_vars(formula.left, bound) | _free_vars(formula.right, bound)
    if isinstance(formula, _Forall):
        return _free_vars(formula.body, bound | {formula.var})
    return set()

def _var_free_in_sequent(var, s):
    return any(var in _free_vars(f) for f in s.left + s.right)
