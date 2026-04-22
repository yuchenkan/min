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
    def __init__(self, phi, vars: list):
        self.phi = phi
        self.vars = vars

    def expand(self):
        a, b, x = Var(), Var(), Var()
        body = Forall(a, Exists(b, Forall(x,
            Iff(In(x, b), And(In(x, a), self.phi(x))))))
        for v in self.vars:
            body = Forall(v, body)
        return body

    def __str__(self):
        return 'Separation(...)'


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
    def __init__(self, phi, vars: list):
        self.phi = phi
        self.vars = vars

    def expand(self):
        a, b, x, y, y1, y2 = Var(), Var(), Var(), Var(), Var(), Var()
        functional = Forall(x, Implies(In(x, a),
            Forall(y1, Forall(y2, Implies(
                And(self.phi(x, y1), self.phi(x, y2)),
                Eq(y1, y2))))))
        image = Exists(b, Forall(y,
            Iff(In(y, b), Exists(x, And(In(x, a), self.phi(x, y))))))
        body = Forall(a, Implies(functional, image))
        for v in self.vars:
            body = Forall(v, body)
        return body

    def __str__(self):
        return 'Replacement(...)'


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
