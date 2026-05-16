"""Phase2P proof — single TM step: (q0,a,tape)→(q1,sa,tape2).

Transition: q0,zero→one,one(right),q1. Reads tape(a)=zero (separator),
writes one, moves right to sa=S(a), changes state to q1.

TMReaches for 1 step = TMStep wrapped via tmstep_to_reaches pattern.
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to


def tape_read_sep():
    """|- ∀tape,a,b,zero. UnaryTape(tape,a,b) → Num(zero,0) → Apply(tape,a,zero)"""
    from theorems.logic import and_elim_left, and_elim_right

    tape, a, b, zero = Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    num_zero = Num(zero, 0)
    app = Apply(tape, a, zero)

    exp = ut.expand()
    func_f = exp.left
    rest0 = exp.right
    low_f = rest0.left
    rest1 = rest0.right
    sep_f = rest1.left

    aer0 = and_elim_right(func_f, rest0, [])
    got_rest0 = apply_thm(aer0, [], ut, rest0, ax(ut))
    aer1 = and_elim_right(low_f, rest1, [])
    got_rest1 = apply_thm(aer1, [], rest0, rest1, got_rest0)
    ael1 = and_elim_left(sep_f, rest1.right, [])
    got_sep = apply_thm(ael1, [], rest1, sep_f, got_rest1)

    got = apply_thm(got_sep, [zero], num_zero, app, ax(num_zero))

    for premise in [num_zero, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [zero, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_sep'
    return proof


if __name__ == '__main__':
    p = tape_read_sep()
    print(f'tape_read_sep: OK, left={[type(f).__name__ for f in p.sequent.left]}')
