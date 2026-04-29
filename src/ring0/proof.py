"""Ring 0 sequent calculus verifier. Identity-based, no alpha-equivalence."""

from ring0.lang import Var, In, Not, Implies, Forall, Formula


class Sequent:
    def __init__(self, left, right):
        self.left = set(left)
        self.right = set(right)
        assert len(self.left) == len(list(left))
        assert len(self.right) == len(list(right))


class Proof:
    def __init__(self, sequent, rule, premises=None, name=None,
                 term=None, principal=None, substituted=None):
        self.sequent = sequent
        self.rule = rule
        self.premises = premises or []
        self.name = name
        self.term = term
        self.principal = principal
        self.substituted = substituted


def verify(proof, axiom_checker):
    s = proof.sequent
    if len(s.right) != 1 or _free_vars(next(iter(s.right))):
        return False
    for f in s.left:
        if not axiom_checker(f):
            return False
    return _verify(proof)


def _verify(proof):
    if getattr(proof, '_verified', False):
        return True
    for p in proof.premises:
        if not _verify(p):
            return False
    if not _check_rule(proof):
        return False
    proof._verified = True
    return True


def _check_rule(proof):
    s = proof.sequent
    ps = [p.sequent for p in proof.premises]
    p = proof.principal

    match proof.rule:
        case "axiom":
            return len(ps) == 0 and p is not None and p in s.left and p in s.right

        case "not_left":
            if len(ps) != 1 or not isinstance(p, Not) or p not in s.left:
                return False
            return ps[0].left == s.left - {p} and ps[0].right == s.right | {p.operand}

        case "not_right":
            if len(ps) != 1 or not isinstance(p, Not) or p not in s.right:
                return False
            return ps[0].left == s.left | {p.operand} and ps[0].right == s.right - {p}

        case "implies_left":
            if len(ps) != 2 or not isinstance(p, Implies) or p not in s.left:
                return False
            G = s.left - {p}
            return (ps[0].left == G and ps[0].right == s.right | {p.left} and
                    ps[1].left == G | {p.right} and ps[1].right == s.right)

        case "implies_right":
            if len(ps) != 1 or not isinstance(p, Implies) or p not in s.right:
                return False
            D = s.right - {p}
            return ps[0].left == s.left | {p.left} and ps[0].right == D | {p.right}

        case "forall_left":
            sub = proof.substituted
            if len(ps) != 1 or proof.term is None or sub is None or not isinstance(p, Forall):
                return False
            if p not in s.left:
                return False
            return ps[0].left == (s.left - {p}) | {sub} and ps[0].right == s.right

        case "forall_right":
            sub = proof.substituted
            y = proof.term
            if len(ps) != 1 or y is None or sub is None or not isinstance(p, Forall):
                return False
            if p not in s.right:
                return False
            D = s.right - {p}
            if _var_free_in_sequent(y, s.left, D):
                return False
            if _var_bound_in(y, p.body):
                return False
            return ps[0].left == s.left and ps[0].right == D | {sub}

        case "cut":
            if len(ps) != 2 or p is None:
                return False
            return (ps[0].left == s.left and ps[0].right == s.right | {p} and
                    ps[1].left == s.left | {p} and ps[1].right == s.right)

        case "weakening_left":
            if len(ps) != 1 or p is None or p not in s.left:
                return False
            if p in ps[0].left:
                return ps[0].left == s.left and ps[0].right == s.right
            return ps[0].left == s.left - {p} and ps[0].right == s.right

        case "weakening_right":
            if len(ps) != 1 or p is None or p not in s.right:
                return False
            if p in ps[0].right:
                return ps[0].left == s.left and ps[0].right == s.right
            return ps[0].left == s.left and ps[0].right == s.right - {p}

    return False


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


def _var_bound_in(var, formula):
    match formula:
        case In():
            return False
        case Not(operand):
            return _var_bound_in(var, operand)
        case Implies(left, right):
            return _var_bound_in(var, left) or _var_bound_in(var, right)
        case Forall(v, body):
            return v is var or _var_bound_in(var, body)
    return False


def _var_free_in_sequent(var, left, right):
    return any(var in _free_vars(f) for f in left | right)
