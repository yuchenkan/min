"""Phase1P proof — using proper vocab for induction predicate."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty, Singleton, TransitiveSet
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists,
    omega_transitive_set as ots_fn, singleton_exists)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
import core.zfc as zfc


class Phase1Ind:
    """Strong induction predicate for Phase1 trace construction.
    Phase1Ind(n, d, q0, tape, c0) =
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c0) ∧
                 TMConfig(cn,q0,n,tape) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n', 'd', 'q0', 'tape', 'c0')
    def __init__(self, n, d, q0, tape, c0):
        self.n = n; self.d = d; self.q0 = q0; self.tape = tape; self.c0 = c0
    def expand(self):
        tra = Var(postfix='_tra'); cn = Var(postfix='_cn')
        k = Var(postfix='_k'); sk = Var(postfix='_sk')
        ck = Var(postfix='_ck'); ck1 = Var(postfix='_ck1')
        zp = Var(postfix='_zp')
        xd = Var(postfix='_xd'); yd = Var(postfix='_yd')
        base_cond = Forall(zp, Implies(Empty(zp), Apply(tra, zp, self.c0)))
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.n), Eq(xd, self.n)))))
        step_valid = Forall(k, Implies(In(k, self.n),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tra, k, ck),
                    Exists(ck1, And(Apply(tra, sk, ck1), TMStep(self.d, ck, ck1)))))))))
        return Exists(tra, Exists(cn, And(FuncDef(tra),
            And(dom_bound,
            And(base_cond,
            And(TMConfig(cn, self.q0, self.n, self.tape),
            And(Apply(tra, self.n, cn),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Ind(r(self.n), r(self.d), r(self.q0), r(self.tape), r(self.c0))
    def __str__(self):
        return f'P1Ind({self.n},{self.d},{self.q0},{self.tape},{self.c0})'


if __name__ == '__main__':
    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    tape=Var(postfix='tape');c0=Var(postfix='c0');a=Var(postfix='a')
    n=Var(postfix='n')
    p = Phase1Ind(z, d, q0, tape, c0)
    print(f'Phase1Ind(z,...): {p}')
    print(f'  expand: {str(p.expand())[:120]}')
    p2 = Phase1Ind(n, d, q0, tape, c0)
    print(f'Phase1Ind(n,...): {p2}')
    print(f'  same(P(z),P(z))? {same(p, p)}')
    print(f'  same(P(z),P(n))? {same(p, p2)}')
    # Test subst
    p3 = p.subst(z, a)
    print(f'  subst(z→a): {p3}')
    print(f'  same(P(a),P(a))? {same(p3, Phase1Ind(a,d,q0,tape,c0))}')
