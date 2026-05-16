"""Turing machine vocabulary.

Models tm.py in ZFC. All predicates use Forall form (no existential witnesses).

Symbols: 0 = empty set, 1 = S(0).
States: natural numbers.
Directions: 0 = left, 1 = right.
"""

from core.lang import Var, Not, In, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from vocab.sets import Empty
from vocab.ordpair import OrdPair, Successor
from vocab.functions import Apply, Function
from vocab.omega import Num


class TM:
    """TM(tm, delta, q0, qhalt): tm = (delta, (q0, qhalt)).
    Forall inner. OrdPair(inner, q0, qhalt) -> OrdPair(tm, delta, inner)."""
    __match_args__ = ('set', 'delta', 'start', 'halt')
    def __init__(self, tm, delta, q0, qhalt):
        self.set = tm; self.delta = delta; self.start = q0; self.halt = qhalt
    def expand(self):
        inner = Var()
        return Forall(inner, Implies(OrdPair(inner, self.start, self.halt),
                                     OrdPair(self.set, self.delta, inner)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TM(r(self.set), r(self.delta), r(self.start), r(self.halt))
    def __str__(self):
        return f'TM({self.set}, {self.delta}, {self.start}, {self.halt})'


class TMConfig:
    """TMConfig(c, q, h, tape): c = (q, (h, tape)).
    Forall inner. OrdPair(inner, h, tape) -> OrdPair(c, q, inner)."""
    __match_args__ = ('config', 'state', 'head', 'tape')
    def __init__(self, c, q, h, tape):
        self.config = c; self.state = q; self.head = h; self.tape = tape
    def expand(self):
        inner = Var()
        return Forall(inner, Implies(OrdPair(inner, self.head, self.tape),
                                     OrdPair(self.config, self.state, inner)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TMConfig(r(self.config), r(self.state), r(self.head), r(self.tape))
    def __str__(self):
        return f'{self.config} = Config({self.state}, {self.head}, {self.tape})'


class TMTransition:
    """TMTransition(delta, q, r, w, d, q'): delta maps (q,r) to (w,(d,q')).
    Forall inp. OrdPair(inp, q, r) ->
        Forall dp. OrdPair(dp, d, q') ->
            Forall out. OrdPair(out, w, dp) ->
                Apply(delta, inp, out)."""
    __match_args__ = ('delta', 'state', 'read', 'write', 'move', 'next')
    def __init__(self, delta, q, r, w, d, qn):
        self.delta = delta; self.state = q; self.read = r
        self.write = w; self.move = d; self.next = qn
    def expand(self):
        inp, out, dp = Var(), Var(), Var()
        return Forall(inp, Implies(OrdPair(inp, self.state, self.read),
            Forall(dp, Implies(OrdPair(dp, self.move, self.next),
                Forall(out, Implies(OrdPair(out, self.write, dp),
                    Apply(self.delta, inp, out)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TMTransition(r(self.delta), r(self.state), r(self.read),
                            r(self.write), r(self.move), r(self.next))
    def __str__(self):
        return f'delta({self.state},{self.read}) = ({self.write},{self.move},{self.next})'


class TapeUpdate:
    """TapeUpdate(tape', tape, h, w): tape' is tape with position h set to w.
    Forall p. Iff(In(p, tape'),
        Or(OrdPair(p, h, w),
           And(In(p, tape), Not(Exists(y, OrdPair(p, h, y))))))
    Fully characterizes tape' as a set: contains exactly the pair (h,w)
    plus all elements of tape that aren't pairs with first component h."""
    __match_args__ = ('new_tape', 'old_tape', 'pos', 'sym')
    def __init__(self, tapen, tape, h, w):
        self.new_tape = tapen; self.old_tape = tape; self.pos = h; self.sym = w
    def expand(self):
        p, y = Var(), Var()
        return Forall(p, Iff(In(p, self.new_tape),
            Or(OrdPair(p, self.pos, self.sym),
               And(In(p, self.old_tape),
                   Not(Exists(y, OrdPair(p, self.pos, y)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TapeUpdate(r(self.new_tape), r(self.old_tape), r(self.pos), r(self.sym))
    def __str__(self):
        return f'{self.new_tape} = {self.old_tape}[{self.pos} := {self.sym}]'


class HeadMove:
    """HeadMove(h, h', d): h' is h moved by d. d=1 (right): Successor(h',h). d=0 (left): Successor(h,h').
    Or(And(Num(d,1), Successor(h',h)), And(Num(d,0), Successor(h,h')))."""
    __match_args__ = ('head', 'new_head', 'direction')
    def __init__(self, h, hn, d):
        self.head = h; self.new_head = hn; self.direction = d
    def expand(self):
        return Or(And(Num(self.direction, 1), Successor(self.new_head, self.head)),
                  And(Num(self.direction, 0), Successor(self.head, self.new_head)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return HeadMove(r(self.head), r(self.new_head), r(self.direction))
    def __str__(self):
        return f'Move({self.head}, {self.new_head}, {self.direction})'


class TMStep:
    """TMStep(delta, c1, c2): c2 is one step from c1 under delta.
    Forall q,h,tape,sym,w,d,q',h',tape'.
        TMConfig(c1,q,h,tape) -> Apply(tape,h,sym) ->
        TMTransition(delta,q,sym,w,d,q') ->
        TapeUpdate(tape',tape,h,w) -> HeadMove(h,h',d) ->
        TMConfig(c2,q',h',tape')."""
    __match_args__ = ('delta', 'before', 'after')
    def __init__(self, delta, c1, c2):
        self.delta = delta; self.before = c1; self.after = c2
    def expand(self):
        q, h, tape, sym = Var(), Var(), Var(), Var()
        w, d, qn, hn, tapen = Var(), Var(), Var(), Var(), Var()
        return Forall(q, Forall(h, Forall(tape, Forall(sym,
            Forall(w, Forall(d, Forall(qn, Forall(hn, Forall(tapen,
                Implies(TMConfig(self.before, q, h, tape),
                Implies(Apply(tape, h, sym),
                Implies(TMTransition(self.delta, q, sym, w, d, qn),
                Implies(TapeUpdate(tapen, tape, h, w),
                Implies(HeadMove(h, hn, d),
                    TMConfig(self.after, qn, hn, tapen)))))))))))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TMStep(r(self.delta), r(self.before), r(self.after))
    def __str__(self):
        return f'Step({self.before} -> {self.after})'


class TMRun:
    """TMRun(run, delta, c0, n): run is an n-step execution from c0.
    Forall zero. Empty(zero) -> Apply(run, zero, c0)
    and Forall k. In(k, n) -> Forall sk. Successor(sk, k) ->
            Forall ck. Apply(run, k, ck) ->
                Forall ck1. Apply(run, sk, ck1) ->
                    TMStep(delta, ck, ck1)."""
    __match_args__ = ('run', 'delta', 'init', 'steps')
    def __init__(self, run, delta, c0, n):
        self.run = run; self.delta = delta; self.init = c0; self.steps = n
    def expand(self):
        zero, k, sk, ck, ck1 = Var(), Var(), Var(), Var(), Var()
        base = Forall(zero, Implies(Empty(zero), Apply(self.run, zero, self.init)))
        step = Forall(k, Implies(In(k, self.steps),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(self.run, k, ck),
                    Forall(ck1, Implies(Apply(self.run, sk, ck1),
                        TMStep(self.delta, ck, ck1)))))))))
        return And(base, step)
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TMRun(r(self.run), r(self.delta), r(self.init), r(self.steps))
    def __str__(self):
        return f'Run({self.run}, {self.delta}, {self.init}, {self.steps})'


class TMReaches:
    """TMReaches(delta, c0, n, cf): TM reaches config cf in n steps from c0.
    Exists trace. And(
      Forall zero. Empty(zero) -> Apply(trace, zero, c0),          -- base
      And(
        Forall k. In(k,n) -> Forall sk. Succ(sk,k) ->             -- step valid
          Forall ck. Apply(trace,k,ck) ->
            Exists ck1. And(Apply(trace,sk,ck1), TMStep(delta,ck,ck1)),
        Apply(trace, n, cf)))                                       -- reached"""
    __match_args__ = ('delta', 'init', 'steps', 'config')
    def __init__(self, delta, c0, n, cf):
        self.delta = delta; self.init = c0
        self.steps = n; self.config = cf
    def expand(self):
        trace = Var()
        zero, k, sk, ck, ck1 = Var(), Var(), Var(), Var(), Var()
        base = Forall(zero, Implies(Empty(zero), Apply(trace, zero, self.init)))
        step = Forall(k, Implies(In(k, self.steps),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(trace, k, ck),
                    Exists(ck1, And(Apply(trace, sk, ck1),
                        TMStep(self.delta, ck, ck1)))))))))
        reached = Apply(trace, self.steps, self.config)
        func = Function(trace)
        xd, yd = Var(), Var()
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(trace, xd, yd),
            Or(In(xd, self.steps), Eq(xd, self.steps)))))
        return Exists(trace, And(func, And(dom_bound, And(base, And(step, reached)))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return TMReaches(r(self.delta), r(self.init), r(self.steps), r(self.config))
    def __str__(self):
        return f'(TM({self.delta}) reaches {self.config} from {self.init} in {self.steps} steps)'
