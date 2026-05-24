"""Proof kernel: formula types, sequent calculus, proof rules.

No dependency on eval. Pure logic."""


class Var:
    pass


class Formula:
    pass


class In(Formula):
    def __init__(self, left, right):
        if not isinstance(left, Var):
            raise TypeError(f'In.left must be Var, got {type(left).__name__}')
        if not isinstance(right, Var):
            raise TypeError(f'In.right must be Var, got {type(right).__name__}')
        self.left = left
        self.right = right


class Not(Formula):
    def __init__(self, operand):
        if not isinstance(operand, Formula):
            raise TypeError(f'Not.operand must be Formula, got {type(operand).__name__}')
        self.operand = operand


class Implies(Formula):
    def __init__(self, left, right):
        if not isinstance(left, Formula):
            raise TypeError(f'Implies.left must be Formula, got {type(left).__name__}')
        if not isinstance(right, Formula):
            raise TypeError(f'Implies.right must be Formula, got {type(right).__name__}')
        self.left = left
        self.right = right


class Forall(Formula):
    def __init__(self, var, body):
        if not isinstance(var, Var):
            raise TypeError(f'Forall.var must be Var, got {type(var).__name__}')
        if not isinstance(body, Formula):
            raise TypeError(f'Forall.body must be Formula, got {type(body).__name__}')
        self.var = var
        self.body = body


# === Substitution ===

def _subst(formula, old, new):
    if isinstance(formula, In):
        return In(new if formula.left is old else formula.left,
                  new if formula.right is old else formula.right)
    if isinstance(formula, Not):
        return Not(_subst(formula.operand, old, new))
    if isinstance(formula, Implies):
        return Implies(_subst(formula.left, old, new), _subst(formula.right, old, new))
    if isinstance(formula, Forall):
        if formula.var is old:
            return formula
        return Forall(formula.var, _subst(formula.body, old, new))
    raise ValueError(f'cannot subst: {type(formula).__name__}')



# === Alpha-equivalence ===

def same(a, b):
    return _eq(a, b, [])


def _eq(a, b, env):
    if a is b and not env:
        return True
    if type(a) is not type(b):
        return False
    if isinstance(a, Var):
        for v1, v2 in env:
            if a is v1: return b is v2
            if b is v2: return False
        return a is b
    if isinstance(a, In):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, Not):
        return _eq(a.operand, b.operand, env)
    if isinstance(a, Implies):
        return _eq(a.left, b.left, env) and _eq(a.right, b.right, env)
    if isinstance(a, Forall):
        return _eq(a.body, b.body, env + [(a.var, b.var)])
    return False


# === Sequent ===

class Sequent:
    def __init__(self, left, right):
        self.left = list(left)
        self.right = list(right)
        for f in self.left:
            if not isinstance(f, Formula):
                raise TypeError(f'Sequent.left must contain Formula, got {type(f).__name__}')
        for f in self.right:
            if not isinstance(f, Formula):
                raise TypeError(f'Sequent.right must contain Formula, got {type(f).__name__}')
        for i in range(len(self.left)):
            for j in range(i + 1, len(self.left)):
                if _eq(self.left[i], self.left[j], []):
                    raise ValueError('duplicate on left')
        for i in range(len(self.right)):
            for j in range(i + 1, len(self.right)):
                if _eq(self.right[i], self.right[j], []):
                    raise ValueError('duplicate on right')


# === Proof ===

class Proof:
    def __init__(self, sequent, rule, premises=None, term=None, principal=None):
        if not isinstance(sequent, Sequent):
            raise TypeError(f'Proof.sequent must be Sequent, got {type(sequent).__name__}')
        if not isinstance(rule, str):
            raise TypeError(f'Proof.rule must be str, got {type(rule).__name__}')
        premises = premises or []
        for p in premises:
            if not isinstance(p, Proof):
                raise TypeError(f'Proof.premises must contain Proof, got {type(p).__name__}')
        if term is not None and not isinstance(term, Var):
            raise TypeError(f'Proof.term must be Var, got {type(term).__name__}')
        if principal is not None and not isinstance(principal, Formula):
            raise TypeError(f'Proof.principal must be Formula, got {type(principal).__name__}')
        if not _check_rule(sequent, rule, premises, principal, term):
            raise ValueError(f'invalid proof step: {rule}')
        self.sequent = sequent

    def theorem(self):
        s = self.sequent
        result = s.right[0] if len(s.right) == 1 else None
        for f in reversed(s.left):
            result = Implies(f, result)
        return result


# === Proof rules ===

def _check_rule(sequent, rule, premises, principal, term):
    s = sequent
    ps = [p.sequent for p in premises]

    match rule:
        case "axiom":
            return (len(ps) == 0 and principal is not None
                    and _fin(principal, s.left) and _fin(principal, s.right))
        case "not_left":
            return (len(ps) == 1 and isinstance(principal, Not)
                    and _fin(principal, s.left)
                    and _eq_sequent(ps[0], Sequent(
                        _remove(s.left, principal), _set_add(s.right, principal.operand))))
        case "not_right":
            return (len(ps) == 1 and isinstance(principal, Not)
                    and _fin(principal, s.right)
                    and _eq_sequent(ps[0], Sequent(
                        _set_add(s.left, principal.operand), _remove(s.right, principal))))
        case "implies_left":
            if len(ps) != 2 or not isinstance(principal, Implies):
                return False
            if not _fin(principal, s.left):
                return False
            G = _remove(s.left, principal)
            return (_eq_sequent(ps[0], Sequent(G, _set_add(s.right, principal.left)))
                    and _eq_sequent(ps[1], Sequent(_set_add(G, principal.right), s.right)))
        case "implies_right":
            if len(ps) != 1 or not isinstance(principal, Implies):
                return False
            if not _fin(principal, s.right):
                return False
            D = _remove(s.right, principal)
            return _eq_sequent(ps[0], Sequent(
                _set_add(s.left, principal.left), _set_add(D, principal.right)))
        case "forall_left":
            if len(ps) != 1 or term is None or not isinstance(principal, Forall):
                return False
            if not _fin(principal, s.left):
                return False
            if _var_bound_in(term, principal.body):
                return False
            G = _remove(s.left, principal)
            substituted = _subst(principal.body, principal.var, term)
            return _eq_sequent(ps[0], Sequent(_set_add(G, substituted), s.right))
        case "forall_right":
            if len(ps) != 1 or term is None or not isinstance(principal, Forall):
                return False
            if not _fin(principal, s.right):
                return False
            D = _remove(s.right, principal)
            if _var_free_in_sequent(term, Sequent(s.left, D)):
                return False
            if _var_bound_in(term, principal.body):
                return False
            substituted = _subst(principal.body, principal.var, term)
            return _eq_sequent(ps[0], Sequent(s.left, _set_add(D, substituted)))
        case "cut":
            return (len(ps) == 2 and principal is not None
                    and _eq_sequent(ps[0], Sequent(s.left, _set_add(s.right, principal)))
                    and _eq_sequent(ps[1], Sequent(_set_add(s.left, principal), s.right)))
        case "weakening_left":
            if len(ps) != 1 or principal is None:
                return False
            if not _fin(principal, s.left):
                return False
            if _fin(principal, ps[0].left):
                return _eq_sequent(ps[0], s)
            return _eq_sequent(ps[0], Sequent(_remove(s.left, principal), s.right))
        case "weakening_right":
            if len(ps) != 1 or principal is None:
                return False
            if not _fin(principal, s.right):
                return False
            if _fin(principal, ps[0].right):
                return _eq_sequent(ps[0], s)
            return _eq_sequent(ps[0], Sequent(s.left, _remove(s.right, principal)))
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
    if isinstance(formula, In):
        result = set()
        if formula.left not in bound:
            result.add(formula.left)
        if formula.right not in bound:
            result.add(formula.right)
        return result
    if isinstance(formula, Not):
        return _free_vars(formula.operand, bound)
    if isinstance(formula, Implies):
        return _free_vars(formula.left, bound) | _free_vars(formula.right, bound)
    if isinstance(formula, Forall):
        return _free_vars(formula.body, bound | {formula.var})
    return set()


def _var_bound_in(var, formula):
    if isinstance(formula, In):
        return False
    if isinstance(formula, Not):
        return _var_bound_in(var, formula.operand)
    if isinstance(formula, Implies):
        return _var_bound_in(var, formula.left) or _var_bound_in(var, formula.right)
    if isinstance(formula, Forall):
        if formula.var is var:
            return True
        return _var_bound_in(var, formula.body)
    return False

def _var_free_in_sequent(var, s):
    return any(var in _free_vars(f) for f in s.left + s.right)
