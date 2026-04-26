"""Database of formal definitions built on core.

Naming convention:
- Predicates (Empty, Singleton, PairSet, Successor, Inductive, Subset):
  formula-level objects describing a property of sets.
- Compound definitions (OrdPair, Omega):
  build formulas using predicates + Forall/Implies.
- SetSpec: generic definite description for unnamed set constructions
  (Union, Intersect, PowerSet, Diff, BigUnion, BigIntersect).
"""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq


class ExistsUnique:
    """ExistsUnique(var, body): exists unique var satisfying body.
    exists var. body and forall var'. body[var:=var'] -> Eq(var, var')"""
    __match_args__ = ('var', 'body')
    def __init__(self, var, body, postfix=None):
        self.var = var
        self.body = body
        self._postfix = postfix

    def expand(self):
        p = self._postfix
        v2 = Var(postfix=f'{p}.v2' if p else None)
        body_v2 = self.body.subst(self.var, v2)
        unique = Forall(v2, Implies(body_v2, Eq(self.var, v2),
                                    postfix=f'{p}.imp' if p else None),
                        postfix=f'{p}.fa' if p else None)
        return Exists(self.var, And(self.body, unique, postfix=f'{p}.and' if p else None),
                      postfix=f'{p}.ex' if p else None)

    def subst(self, old, new):
        if self.var is old:
            return self
        return ExistsUnique(self.var, self.body.subst(old, new))

    def __str__(self):
        s = f'exists! {self.var}. ({self.body})'
        return f'{s}/*{self._postfix}*/' if self._postfix else s


# --- Generic set characterization predicate ---

class SetSpec:
    """SetSpec(s, cond) = forall x. Iff(In(x, s), cond(x)). s has membership cond."""
    def __init__(self, s, cond):
        self.set = s
        self.cond = cond
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), self.cond(x)))
    def subst(self, old, new):
        return SetSpec(new if self.set is old else self.set,
                       lambda x: self.cond(x).subst(old, new))
    def __str__(self):
        x = Var()
        return f'{self.set} = {{ {x} | {self.cond(x)} }}'


# --- Predicates ---

class Empty:
    """Empty(s) = forall x. not(x in s)"""
    __match_args__ = ('set',)
    def __init__(self, s):
        self.set = s
    def expand(self):
        x = Var()
        return Forall(x, Not(In(x, self.set)))
    def subst(self, old, new):
        return Empty(new if self.set is old else self.set)
    def __str__(self):
        return f'{self.set} = {{}}'


class Singleton:
    """Singleton(s, a) = forall x. Iff(In(x, s), Eq(x, a)). s is {a}."""
    __match_args__ = ('set', 'elem')
    def __init__(self, s, a):
        self.set = s
        self.elem = a
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), Eq(x, self.elem)))
    def subst(self, old, new):
        return Singleton(new if self.set is old else self.set,
                         new if self.elem is old else self.elem)
    def __str__(self):
        return f'{self.set} = {{{self.elem}}}'


class PairSet:
    """PairSet(s, a, b) = forall x. Iff(In(x, s), Or(Eq(x, a), Eq(x, b))). s is {a,b}."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s
        self.left = a
        self.right = b
    def expand(self):
        x = Var()
        return Forall(x, Iff(In(x, self.set), Or(Eq(x, self.left), Eq(x, self.right))))
    def subst(self, old, new):
        return PairSet(new if self.set is old else self.set,
                       new if self.left is old else self.left,
                       new if self.right is old else self.right)
    def __str__(self):
        return f'{self.set} = {{{self.left},{self.right}}}'


class Successor:
    """Successor(s, x) = forall z. Iff(In(z, s), Or(In(z, x), Eq(z, x))). s is S(x) = x union {x}."""
    __match_args__ = ('set', 'of')
    def __init__(self, s, x):
        self.set = s
        self.of = x
    def expand(self):
        z = Var()
        return Forall(z, Iff(In(z, self.set), Or(In(z, self.of), Eq(z, self.of))))
    def subst(self, old, new):
        return Successor(new if self.set is old else self.set,
                         new if self.of is old else self.of)
    def __str__(self):
        return f'{self.set} = S({self.of})'


class Subset:
    """Subset(a, b) = forall x. In(x, a) implies In(x, b). a sub b."""
    __match_args__ = ('left', 'right')
    def __init__(self, a, b):
        self.left = a
        self.right = b
    def expand(self):
        x = Var()
        return Forall(x, Implies(In(x, self.left), In(x, self.right)))
    def subst(self, old, new):
        return Subset(new if self.left is old else self.left,
                      new if self.right is old else self.right)
    def __str__(self):
        return f'{self.left} sub {self.right}'


class Inductive:
    """isInductive(a) = (forall e. Empty(e) implies e in a)
                      and (forall x in a. forall s. Successor(s, x) implies s in a)"""
    __match_args__ = ('set',)
    def __init__(self, a):
        self.set = a
    def expand(self):
        e, x, s = Var(), Var(), Var()
        return And(
            Forall(e, Implies(Empty(e), In(e, self.set))),
            Forall(x, Implies(In(x, self.set),
                Forall(s, Implies(Successor(s, x), In(s, self.set))))))
    def subst(self, old, new):
        return Inductive(new if self.set is old else self.set)
    def __str__(self):
        return f'Inductive({self.set})'


# --- Compound definitions ---

class OrdPair:
    """OrdPair(t, a, b): t = (a, b) = {{a}, {a, b}}.
    Exists sa. Singleton(sa,a) and Exists pab. PairSet(pab,a,b) and PairSet(t,sa,pab)."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, t, a, b):
        self.set = t; self.left = a; self.right = b
    def expand(self):
        sa = Var()
        pab = Var()
        return Exists(sa, And(Singleton(sa, self.left),
            Exists(pab, And(PairSet(pab, self.left, self.right),
                PairSet(self.set, sa, pab)))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return OrdPair(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = <{self.left},{self.right}>'


class Omega:
    """Omega(w): w is the smallest inductive set.
    forall b. isInductive(b) implies forall x. x in w iff (x in b and forall c. isInductive(c) implies x in c)"""
    __match_args__ = ('set',)
    def __init__(self, w):
        self.set = w
    def expand(self):
        b, x, c = Var(), Var(), Var()
        cond = And(In(x, b), Forall(c, Implies(Inductive(c), In(x, c))))
        return Forall(b, Implies(Inductive(b),
            Forall(x, Iff(In(x, self.set), cond))))
    def subst(self, old, new):
        return Omega(new if self.set is old else self.set)
    def __str__(self):
        return f'{self.set} = omega'


# --- Relations and functions (Section 4.1.6) ---

class Apply:
    """Apply(f, x, y): f(x) = y, i.e. <x,y> in f."""
    __match_args__ = ('func', 'arg', 'val')
    def __init__(self, f, x, y):
        self.func = f; self.arg = x; self.val = y
    def expand(self):
        p = Var()
        return Exists(p, And(OrdPair(p, self.arg, self.val), In(p, self.func)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Apply(r(self.func), r(self.arg), r(self.val))
    def __str__(self):
        return f'{self.func}({self.arg}) = {self.val}'



class Domain:
    """Domain(f, d): d = dom(f). forall x. x in d iff exists y. Apply(f, x, y)."""
    __match_args__ = ('func', 'set')
    def __init__(self, f, d):
        self.func = f; self.set = d
    def expand(self):
        x, y = Var(), Var()
        return Forall(x, Iff(In(x, self.set), Exists(y, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Domain(r(self.func), r(self.set))
    def __str__(self):
        return f'{self.set} = dom({self.func})'


class Range:
    """Range(f, r): r = ran(f). forall y. y in r iff exists x. Apply(f, x, y)."""
    __match_args__ = ('func', 'set')
    def __init__(self, f, r):
        self.func = f; self.set = r
    def expand(self):
        x, y = Var(), Var()
        return Forall(y, Iff(In(y, self.set), Exists(x, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Range(r(self.func), r(self.set))
    def __str__(self):
        return f'{self.set} = ran({self.func})'


class Relation:
    """Relation(r): all elements of r are ordered pairs.
    forall z. z in r -> exists x, y. OrdPair(z, x, y)."""
    __match_args__ = ('set',)
    def __init__(self, r):
        self.set = r
    def expand(self):
        z, x, y = Var(), Var(), Var()
        return Forall(z, Implies(In(z, self.set),
            Exists(x, Exists(y, OrdPair(z, x, y)))))
    def subst(self, old, new):
        return Relation(new if self.set is old else self.set)
    def __str__(self):
        return f'Relation({self.set})'


class Function:
    """Function(f): f is a relation and single-valued.
    Relation(f) and forall x, y1, y2. Apply(f,x,y1) and Apply(f,x,y2) -> y1 = y2."""
    __match_args__ = ('set',)
    def __init__(self, f):
        self.set = f
    def expand(self):
        x, y1, y2 = Var(), Var(), Var()
        single_valued = Forall(x, Forall(y1, Forall(y2,
            Implies(And(Apply(self.set, x, y1), Apply(self.set, x, y2)),
                    Eq(y1, y2)))))
        return And(Relation(self.set), single_valued)
    def subst(self, old, new):
        return Function(new if self.set is old else self.set)
    def __str__(self):
        return f'Function({self.set})'


class Total:
    """Total(f, a): f is total on a. forall x. x in a -> exists y. Apply(f, x, y)."""
    __match_args__ = ('func', 'domain')
    def __init__(self, f, a):
        self.func = f; self.domain = a
    def expand(self):
        x, y = Var(), Var()
        return Forall(x, Implies(In(x, self.domain), Exists(y, Apply(self.func, x, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Total(r(self.func), r(self.domain))
    def __str__(self):
        return f'Total({self.func}, {self.domain})'


class Recursive:
    """Recursive(h, a, f, w): isRecursive per book Thm 4.2.14.
    isFunction(h) and h(0) = a and forall n in w. h(n+) = f(h(n)).
    w is omega."""
    __match_args__ = ('func', 'init', 'step', 'omega')
    def __init__(self, h, a, f, w):
        self.func = h; self.init = a; self.step = f; self.omega = w
    def expand(self):
        e, n, val, sn, fval = Var(), Var(), Var(), Var(), Var()
        return And(Function(self.func),
               And(Forall(e, Implies(Empty(e), Apply(self.func, e, self.init))),
                   Forall(n, Implies(In(n, self.omega),
                       Forall(val, Implies(Apply(self.func, n, val),
                           Forall(sn, Implies(Successor(sn, n),
                               Forall(fval, Implies(Apply(self.step, val, fval),
                                   Apply(self.func, sn, fval)))))))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Recursive(r(self.func), r(self.init), r(self.step), r(self.omega))
    def __str__(self):
        return f'Recursive({self.func}, {self.init}, {self.step})'


class Plus:
    """Plus(m, n, p): m + n = p.
    Exists w, h, sf. Omega(w) and succ_char(sf) and Recursive(h, m, sf, w) and Apply(h, n, p)."""
    __match_args__ = ('left', 'right', 'result')
    def __init__(self, m, n, p):
        self.left = m; self.right = n; self.result = p
    def expand(self):
        w, h, sf, x, y = Var(), Var(), Var(), Var(), Var()
        succ_char = Forall(x, Forall(y, Iff(Apply(sf, x, y), Successor(y, x))))
        return Exists(w, And(Omega(w),
            Exists(h, Exists(sf,
                And(succ_char,
                And(Recursive(h, self.left, sf, w),
                    Apply(h, self.right, self.result)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Plus(r(self.left), r(self.right), r(self.result))
    def __str__(self):
        return f'{self.left} + {self.right} = {self.result}'


# InitialSegment: DEPRECATED, replaced by RecApprox (book Thm 4.2.14)
# Old theorems using it (init_seg_total, init_seg_agree, etc.) need rewriting.


class RecApprox:
    """RecApprox(v, a, f, w): v is a recursive approximation (book P(v), Thm 4.2.14).
    Function(v)
    and Subset(dom v, w)                       -- dom v sub omega
    and (forall y. Apply(v,_,y) -> Total(f,y)) -- ran v sub dom f (pointwise)
    and (forall e. Empty(e) -> e in dom v -> Apply(v, e, a))
    and forall n in w. Succ(sn, n) -> sn in dom v -> n in dom v and Apply(v, sn, f(v(n)))"""
    __match_args__ = ('func', 'init', 'step', 'omega')
    def __init__(self, v, a, f, w):
        self.func = v; self.init = a; self.step = f; self.omega = w
    def expand(self):
        e, n, sn, val, fval, y, x = Var(), Var(), Var(), Var(), Var(), Var(), Var()
        # Following book page 142 exactly:
        # isFunction(v)
        func_v = Function(self.func)
        # dom v sub omega: forall x. (exists y. Apply(v,x,y)) -> x in w
        dom_sub_w = Forall(x, Implies(Exists(y, Apply(self.func, x, y)),
                                       In(x, self.omega)))
        # ran v sub dom f: forall x,y. Apply(v,x,y) -> exists z. Apply(f,y,z)
        z = Var()
        ran_sub_dom = Forall(x, Forall(y, Implies(Apply(self.func, x, y),
                                                    Exists(z, Apply(self.step, y, z)))))
        # base: forall e. Empty(e) -> (exists y. Apply(v,e,y)) -> Apply(v, e, a)
        # (if 0 in dom v then v(0) = a)
        base = Forall(e, Implies(Empty(e),
                   Implies(Exists(y, Apply(self.func, e, y)),
                           Apply(self.func, e, self.init))))
        # step: forall n. n in w -> forall sn. Succ(sn,n) ->
        #   (exists y. Apply(v,sn,y)) -> (exists y. Apply(v,n,y))
        #   and forall val. Apply(v,n,val) -> forall fval. Apply(f,val,fval) -> Apply(v,sn,fval)
        # Simplified: if sn in dom v, then n in dom v and v(sn) = f(v(n))
        step = Forall(n, Implies(In(n, self.omega),
                   Forall(sn, Implies(Successor(sn, n),
                       Implies(Exists(y, Apply(self.func, sn, y)),
                           And(Exists(y, Apply(self.func, n, y)),
                               Forall(val, Implies(Apply(self.func, n, val),
                                   Forall(fval, Implies(Apply(self.step, val, fval),
                                       Apply(self.func, sn, fval)))))))))))
        return And(func_v, And(dom_sub_w, And(ran_sub_dom, And(base, step))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return RecApprox(r(self.func), r(self.init), r(self.step), r(self.omega))
    def __str__(self):
        return f'RecApprox({self.func}, {self.init}, {self.step}, {self.omega})'


class Product:
    """Product(s, a, b): s = a x b (cartesian product).
    forall z. z in s iff exists x, y. x in a and y in b and OrdPair(z, x, y)."""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        z, x, y = Var(), Var(), Var()
        return Forall(z, Iff(In(z, self.set),
            Exists(x, Exists(y, And(In(x, self.left),
                And(In(y, self.right), OrdPair(z, x, y)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Product(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} x {self.right}'


# --- Set operation predicates ---

class Union:
    """s = a | b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: Or(In(z, self.left), In(z, self.right)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Union(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} | {self.right}'

class BigUnion:
    """s = U(a)"""
    __match_args__ = ('set', 'family')
    def __init__(self, s, a):
        self.set = s; self.family = a
    def expand(self):
        y = Var()
        return SetSpec(self.set, lambda z: Exists(y, And(In(y, self.family), In(z, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return BigUnion(r(self.set), r(self.family))
    def __str__(self):
        return f'{self.set} = U({self.family})'

class Intersect:
    """s = a & b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: And(In(z, self.left), In(z, self.right)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Intersect(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} & {self.right}'

class BigIntersect:
    """s = I(a)"""
    __match_args__ = ('set', 'family')
    def __init__(self, s, a):
        self.set = s; self.family = a
    def expand(self):
        y = Var()
        return SetSpec(self.set, lambda z: Forall(y, Implies(In(y, self.family), In(z, y))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return BigIntersect(r(self.set), r(self.family))
    def __str__(self):
        return f'{self.set} = I({self.family})'

class PowerSet:
    """s = P(a)"""
    __match_args__ = ('set', 'of')
    def __init__(self, s, a):
        self.set = s; self.of = a
    def expand(self):
        return SetSpec(self.set, lambda z: Subset(z, self.of))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return PowerSet(r(self.set), r(self.of))
    def __str__(self):
        return f'{self.set} = P({self.of})'

class Diff:
    """s = a \\ b"""
    __match_args__ = ('set', 'left', 'right')
    def __init__(self, s, a, b):
        self.set = s; self.left = a; self.right = b
    def expand(self):
        return SetSpec(self.set, lambda z: And(In(z, self.left), Not(In(z, self.right))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Diff(r(self.set), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.set} = {self.left} \\ {self.right}'


