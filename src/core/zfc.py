"""ZFC axioms as formula-level objects with expand()."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class ZFCAxiom:
    """Base class for ZFC axioms."""
    def expand(self):
        raise NotImplementedError

    def __str__(self):
        return type(self).__name__


class Extensionality(ZFCAxiom):
    def expand(self):
        x, y, z = Var(), Var(), Var()
        return Forall(x, Forall(y,
            Implies(
                Forall(z, Iff(In(z, x), In(z, y))),
                Forall(z, Iff(In(x, z), In(y, z))))))


class EmptySet(ZFCAxiom):
    def expand(self):
        b, x = Var(), Var()
        return Exists(b, Forall(x, Not(In(x, b))))


class Pairing(ZFCAxiom):
    def expand(self):
        x, y, z, b = Var(), Var(), Var(), Var()
        return Forall(x, Forall(y,
            Exists(b, Forall(z,
                Iff(In(z, b), Or(Eq(z, x), Eq(z, y)))))))


class Union(ZFCAxiom):
    def expand(self):
        a, b, x, y = Var(), Var(), Var(), Var()
        return Forall(a,
            Exists(b, Forall(x,
                Iff(In(x, b), Exists(y, And(In(y, a), In(x, y)))))))


class PowerSet(ZFCAxiom):
    def expand(self):
        a, b, x, y = Var(), Var(), Var(), Var()
        return Forall(a,
            Exists(b, Forall(x,
                Iff(In(x, b), Forall(y, Implies(In(y, x), In(y, a)))))))


class Separation(ZFCAxiom):
    def __init__(self, phi, x, vars: list):
        """phi: formula with x free (the separation predicate).
        x: the separation variable.
        vars: other free variables in phi."""
        self.phi = phi
        self.x = x
        self.vars = vars
        from core.proof import _free_vars
        for v in _free_vars(phi) - {x}:
            assert v in vars, f'Separation: free var {v} in phi not in vars'

    def expand(self):
        a, b = Var(), Var()
        body = Forall(a, Exists(b, Forall(self.x,
            Iff(In(self.x, b), And(In(self.x, a), self.phi)))))
        for v in self.vars:
            body = Forall(v, body)
        return body

    def __str__(self):
        return f'Separation({self.x} => {self.phi})'


class Infinity(ZFCAxiom):
    def expand(self):
        b, e, y, z, s, w = Var(), Var(), Var(), Var(), Var(), Var()
        return Exists(b, And(
            Exists(e, And(In(e, b), Forall(z, Not(In(z, e))))),
            Forall(y, Implies(In(y, b),
                Exists(s, And(In(s, b),
                    Forall(w, Iff(In(w, s), Or(In(w, y), Eq(w, y))))))))))


class Choice(ZFCAxiom):
    def expand(self):
        x, y, z, c, w = Var(), Var(), Var(), Var(), Var()
        return Forall(x,
            Implies(
                Forall(y, Implies(In(y, x), Exists(z, In(z, y)))),
                Exists(c, Forall(y, Implies(In(y, x),
                    Exists(z, And(And(In(z, y), In(z, c)),
                        Forall(w, Implies(And(In(w, y), In(w, c)), Eq(w, z))))))))))


class Replacement(ZFCAxiom):
    def __init__(self, phi, x, y, vars: list):
        """phi: formula with x,y free (the functional relation).
        x: domain variable. y: range variable.
        vars: other free variables in phi."""
        self.phi = phi
        self.x = x
        self.y = y
        self.vars = vars
        from core.proof import _free_vars
        for v in _free_vars(phi) - {x, y}:
            assert v in vars, f'Replacement: free var {v} in phi not in vars'

    def expand(self):
        from core.proof import _subst
        a, b, y1, y2 = Var(), Var(), Var(), Var()
        phi_xy1 = _subst(self.phi, self.y, y1)
        phi_xy2 = _subst(self.phi, self.y, y2)
        functional = Forall(self.x, Implies(In(self.x, a),
            Forall(y1, Forall(y2, Implies(
                And(phi_xy1, phi_xy2),
                Eq(y1, y2))))))
        image = Exists(b, Forall(self.y,
            Iff(In(self.y, b), Exists(self.x, And(In(self.x, a), self.phi)))))
        body = Forall(a, Implies(functional, image))
        for v in self.vars:
            body = Forall(v, body)
        return body

    def __str__(self):
        return f'Replacement({self.x},{self.y} => {self.phi})'


class Regularity(ZFCAxiom):
    def expand(self):
        a, y, z = Var(), Var(), Var()
        return Forall(a,
            Implies(
                Exists(y, In(y, a)),
                Exists(y, And(In(y, a), Not(Exists(z, And(In(z, a), In(z, y))))))))


def is_axiom(formula) -> bool:
    """Check if formula is a ZFC axiom."""
    return isinstance(formula, ZFCAxiom)
