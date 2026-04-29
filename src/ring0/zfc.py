"""ZFC axioms for ring 0. Pure functions, no classes. Returns core formulas."""

from ring0.lang import Var, In, Not, Implies, Forall
from ring0.proof import _subst


# --- Derived connectives (expand immediately) ---

def exists(v, body):
    return Not(Forall(v, Not(body)))

def and_(left, right):
    return Not(Implies(left, Not(right)))

def or_(left, right):
    return Implies(Not(left), right)

def iff(left, right):
    return Not(Implies(Implies(left, right), Not(Implies(right, left))))

def eq(left, right):
    z = Var()
    return Forall(z, Not(Implies(Implies(In(z, left), In(z, right)),
                                 Not(Implies(In(z, right), In(z, left))))))


# --- ZFC axiom formulas ---

def extensionality():
    x, y, z = Var(), Var(), Var()
    return Forall(x, Forall(y, Implies(
        Forall(z, iff(In(z, x), In(z, y))),
        Forall(z, iff(In(x, z), In(y, z))))))

def empty_set():
    b, x = Var(), Var()
    return exists(b, Forall(x, Not(In(x, b))))

def pairing():
    x, y, z, b = Var(), Var(), Var(), Var()
    return Forall(x, Forall(y, exists(b, Forall(z,
        iff(In(z, b), or_(eq(z, x), eq(z, y)))))))

def union():
    a, b, x, y = Var(), Var(), Var(), Var()
    return Forall(a, exists(b, Forall(x,
        iff(In(x, b), exists(y, and_(In(y, a), In(x, y)))))))

def power_set():
    a, b, x, y = Var(), Var(), Var(), Var()
    return Forall(a, exists(b, Forall(x,
        iff(In(x, b), Forall(y, Implies(In(y, x), In(y, a)))))))

def separation(x, phi, vars):
    a, b = Var(), Var()
    body = Forall(a, exists(b, Forall(x,
        iff(In(x, b), and_(In(x, a), phi)))))
    for v in vars:
        body = Forall(v, body)
    return body

def infinity():
    b, e, y, z, s, w = Var(), Var(), Var(), Var(), Var(), Var()
    return exists(b, and_(
        exists(e, and_(In(e, b), Forall(z, Not(In(z, e))))),
        Forall(y, Implies(In(y, b),
            exists(s, and_(In(s, b), Forall(w, iff(In(w, s), or_(In(w, y), eq(w, y))))))))))

def choice():
    x, y, z, c, w = Var(), Var(), Var(), Var(), Var()
    return Forall(x, Implies(
        Forall(y, Implies(In(y, x), exists(z, In(z, y)))),
        exists(c, Forall(y, Implies(In(y, x),
            exists(z, and_(and_(In(z, y), In(z, c)),
                Forall(w, Implies(and_(In(w, y), In(w, c)), eq(w, z))))))))))

def replacement(x, y, phi, vars):
    a, b, y1, y2 = Var(), Var(), Var(), Var()
    functional = Forall(x, Implies(In(x, a),
        Forall(y1, Forall(y2, Implies(and_(_subst(phi, y, y1), _subst(phi, y, y2)), eq(y1, y2))))))
    image = exists(b, Forall(y,
        iff(In(y, b), exists(x, and_(In(x, a), phi)))))
    body = Forall(a, Implies(functional, image))
    for v in vars:
        body = Forall(v, body)
    return body

def regularity():
    a, y, z = Var(), Var(), Var()
    return Forall(a, Implies(
        exists(y, In(y, a)),
        exists(y, and_(In(y, a), Not(exists(z, and_(In(z, a), In(z, y))))))))
