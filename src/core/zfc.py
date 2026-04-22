"""ZFC axioms in the first-order language of set theory."""

from core.lang import Var, In, Not, Implies, Forall, Formula
from core.proof import Sequent, Proof
from core.derived import Exists, And, Or, Iff, Eq


def _axiom(name: str, formula: Formula) -> Proof:
    from core.proof import _free_vars
    # Close over any free variables
    for v in sorted(_free_vars(formula), key=lambda v: v._id):
        formula = Forall(v, formula)
    return Proof(Sequent([formula], [formula]), 'axiom', name=name, principal=formula)


# --- Axioms ---

# 1. Extensionality
x, y, z = Var(), Var(), Var()
extensionality = _axiom('extensionality', Forall(x, Forall(y,
    Implies(
        Forall(z, Iff(In(z, x), In(z, y))),
        Forall(z, Iff(In(x, z), In(y, z)))))))

# 2. Empty set
b, x = Var(), Var()
empty_set = _axiom('empty_set', Exists(b, Forall(x, Not(In(x, b)))))

# 3. Pairing
x, y, z, b = Var(), Var(), Var(), Var()
pairing = _axiom('pairing', Forall(x, Forall(y,
    Exists(b, Forall(z,
        Iff(In(z, b), Or(Eq(z, x), Eq(z, y))))))))

# 4. Union
a, b, x, y = Var(), Var(), Var(), Var()
union = _axiom('union', Forall(a,
    Exists(b, Forall(x,
        Iff(In(x, b), Exists(y, And(In(y, a), In(x, y))))))))

# 5. Power set
a, b, x, y = Var(), Var(), Var(), Var()
power_set = _axiom('power_set', Forall(a,
    Exists(b, Forall(x,
        Iff(In(x, b), Forall(y, Implies(In(y, x), In(y, a))))))))

# 6. Separation (schema)
def separation(phi) -> Proof:
    a, b, x = Var(), Var(), Var()
    return _axiom('separation', Forall(a, Exists(b, Forall(x,
        Iff(In(x, b), And(In(x, a), phi(x)))))))

# 7. Infinity
b, e, y, z, s, w = Var(), Var(), Var(), Var(), Var(), Var()
infinity = _axiom('infinity', Exists(b, And(
    Exists(e, And(In(e, b), Forall(z, Not(In(z, e))))),
    Forall(y, Implies(In(y, b),
        Exists(s, And(In(s, b),
            Forall(w, Iff(In(w, s), Or(In(w, y), Eq(w, y)))))))))))

# 8. Choice
x, y, z, c, w = Var(), Var(), Var(), Var(), Var()
choice = _axiom('choice', Forall(x,
    Implies(
        Forall(y, Implies(In(y, x), Exists(z, In(z, y)))),
        Exists(c, Forall(y, Implies(In(y, x),
            Exists(z, And(And(In(z, y), In(z, c)),
                Forall(w, Implies(And(In(w, y), In(w, c)), Eq(w, z)))))))))))

# 9. Replacement (schema)
def replacement(phi) -> Proof:
    a, b, x, y, y1, y2 = Var(), Var(), Var(), Var(), Var(), Var()
    functional = Forall(x, Implies(In(x, a),
        Forall(y1, Forall(y2, Implies(
            And(phi(x, y1), phi(x, y2)),
            Eq(y1, y2))))))
    image = Exists(b, Forall(y,
        Iff(In(y, b), Exists(x, And(In(x, a), phi(x, y))))))
    return _axiom('replacement', Forall(a, Implies(functional, image)))

# 10. Regularity
a, y, z = Var(), Var(), Var()
regularity = _axiom('regularity', Forall(a,
    Implies(
        Exists(y, In(y, a)),
        Exists(y, And(In(y, a), Not(Exists(z, And(In(z, a), In(z, y)))))))))
