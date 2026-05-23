"""Sequent calculus proof kernel.

All formula comparison by identity (is) with alpha-eq env for bound vars.
No expand(). No vocab. Pure functions on 5 types.
"""

from poc.core.lang import Var, In, Not, Implies, Forall


def _eq(a, b, env=None):
    """Alpha-equivalence. Var compared by is, bound vars via env."""
    if a is b and not env:
        return True
    if env is None:
        env = []
    if isinstance(a, Var) and isinstance(b, Var):
        for v1, v2 in env:
            if a is v1: return b is v2
            if b is v2: return False
        return a is b
    if type(a) is not type(b):
        return False
    if isinstance(a, In):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, Not):
        return _eq(a.operand, b.operand, env)
    if isinstance(a, Implies):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, Forall):
        return _eq(a.body, b.body, env + [(a.var, b.var)])
    return False


def _subst(formula, var, term):
    """Substitute bound var with term. var must be Var(bound=True)."""
    if isinstance(formula, Var):
        return term if formula is var else formula
    if isinstance(formula, In):
        return In(_subst(formula.left, var, term),
                  _subst(formula.right, var, term))
    if isinstance(formula, Not):
        return Not(_subst(formula.operand, var, term))
    if isinstance(formula, Implies):
        return Implies(_subst(formula.left, var, term),
                       _subst(formula.right, var, term))
    if isinstance(formula, Forall):
        if formula.var is var:
            return formula  # shadowed
        return Forall(formula.var, _subst(formula.body, var, term))
    return formula


def _free_vars(formula):
    """Collect free Vars. Returns list, no duplicates (by is)."""
    result = []
    _collect_free(formula, [], result)
    return result

def _collect_free(formula, bound, result):
    if isinstance(formula, Var):
        if formula not in bound and formula not in result:
            result.append(formula)
    elif isinstance(formula, In):
        _collect_free(formula.left, bound, result)
        _collect_free(formula.right, bound, result)
    elif isinstance(formula, Not):
        _collect_free(formula.operand, bound, result)
    elif isinstance(formula, Implies):
        _collect_free(formula.left, bound, result)
        _collect_free(formula.right, bound, result)
    elif isinstance(formula, Forall):
        _collect_free(formula.body, bound + [formula.var], result)


def _in(f, lst):
    return any(_eq(f, g) for g in lst)

def _remove(lst, f):
    result = []
    removed = False
    for g in lst:
        if not removed and _eq(f, g):
            removed = True
        else:
            result.append(g)
    return result

def _set_add(lst, f):
    if _in(f, lst):
        return list(lst)
    return list(lst) + [f]

def _eq_sequent(a, b):
    return _perm(a.left, b.left) and _perm(a.right, b.right)

def _perm(a, b):
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


class Sequent:
    def __init__(self, left, right):
        self.left = list(left)
        self.right = list(right)
        for i in range(len(self.left)):
            for j in range(i + 1, len(self.left)):
                if _eq(self.left[i], self.left[j]):
                    raise ValueError('duplicate on left')
        for i in range(len(self.right)):
            for j in range(i + 1, len(self.right)):
                if _eq(self.right[i], self.right[j]):
                    raise ValueError('duplicate on right')


class Proof:
    def __init__(self, sequent, rule, premises=None, principal=None, term=None):
        premises = premises or []
        if not _check(sequent, rule, premises, principal, term):
            raise ValueError(f'invalid proof step: {rule}')
        self.sequent = sequent


def _check(seq, rule, premises, principal, term):
    s = seq
    ps = [p.sequent for p in premises]

    if rule == 'axiom':
        return principal is not None and _in(principal, s.left) and _in(principal, s.right)

    elif rule == 'not_left':
        if len(ps) != 1 or not isinstance(principal, Not):
            return False
        if not _in(principal, s.left):
            return False
        return _eq_sequent(ps[0], Sequent(
            _remove(s.left, principal), _set_add(s.right, principal.operand)))

    elif rule == 'not_right':
        if len(ps) != 1 or not isinstance(principal, Not):
            return False
        if not _in(principal, s.right):
            return False
        return _eq_sequent(ps[0], Sequent(
            _set_add(s.left, principal.operand), _remove(s.right, principal)))

    elif rule == 'implies_left':
        if len(ps) != 2 or not isinstance(principal, Implies):
            return False
        if not _in(principal, s.left):
            return False
        G = _remove(s.left, principal)
        return (_eq_sequent(ps[0], Sequent(G, _set_add(s.right, principal.left))) and
                _eq_sequent(ps[1], Sequent(_set_add(G, principal.right), s.right)))

    elif rule == 'implies_right':
        if len(ps) != 1 or not isinstance(principal, Implies):
            return False
        if not _in(principal, s.right):
            return False
        D = _remove(s.right, principal)
        return _eq_sequent(ps[0], Sequent(
            _set_add(s.left, principal.left), _set_add(D, principal.right)))

    elif rule == 'forall_left':
        if len(ps) != 1 or not isinstance(principal, Forall) or term is None:
            return False
        if not _in(principal, s.left):
            return False
        G = _remove(s.left, principal)
        substituted = _subst(principal.body, principal.var, term)
        return _eq_sequent(ps[0], Sequent(_set_add(G, substituted), s.right))

    elif rule == 'forall_right':
        if len(ps) != 1 or not isinstance(principal, Forall) or term is None:
            return False
        if not _in(principal, s.right):
            return False
        D = _remove(s.right, principal)
        if _var_free_in_sequent(term, Sequent(s.left, D)):
            return False
        substituted = _subst(principal.body, principal.var, term)
        return _eq_sequent(ps[0], Sequent(s.left, _set_add(D, substituted)))

    elif rule == 'cut':
        if len(ps) != 2 or principal is None:
            return False
        return (_eq_sequent(ps[0], Sequent(s.left, _set_add(s.right, principal))) and
                _eq_sequent(ps[1], Sequent(_set_add(s.left, principal), s.right)))

    elif rule == 'weakening_left':
        if len(ps) != 1 or principal is None:
            return False
        if not _in(principal, s.left):
            return False
        if _in(principal, ps[0].left):
            return _eq_sequent(ps[0], s)
        return _eq_sequent(ps[0], Sequent(_remove(s.left, principal), s.right))

    elif rule == 'weakening_right':
        if len(ps) != 1 or principal is None:
            return False
        if not _in(principal, s.right):
            return False
        if _in(principal, ps[0].right):
            return _eq_sequent(ps[0], s)
        return _eq_sequent(ps[0], Sequent(s.left, _remove(s.right, principal)))

    return False


def _var_free_in_sequent(var, s):
    for f in s.left + s.right:
        if var in _free_vars(f):
            return True
    return False


def qed(proof, axiom_checker=None):
    s = proof.sequent
    if len(s.right) != 1:
        return False
    if len(_free_vars(s.right[0])) > 0:
        return False
    for f in s.left:
        if axiom_checker and not axiom_checker(f):
            return False
    return True
