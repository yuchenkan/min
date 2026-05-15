"""TM addition correctness proof.

Goal: TMReaches(delta, c0, n, cf)
  - delta: transition function for the addition TM
  - c0: initial config (q0, 0, tape_in)
  - n: total step count = S(S(S(a+b)))
  - cf: final config (qH, hf, tf)

Chain:
  Phase1: TMReaches(delta, c0,  a,   c1)   scan a ones
  Phase2: TMReaches(delta, c1,  one, c2)   write 1, move R, change state
  Phase3: TMReaches(delta, c2,  b,   c3)   scan b ones
  Phase4: TMReaches(delta, c3,  one, c4)   read 0, transition
  Phase5: TMReaches(delta, c4,  one, cf)   halt

  Compose via TMReaches_compose + Plus arithmetic:
    a + one = sa, sa + b = hf, hf + one = ssc, ssc + one = n
"""

from core.lang import Var, In, Implies, Forall, Not
from core.derived import Exists, And, Or, Iff, Eq
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.sets import Empty
from vocab.recursion import Plus as PlusDef


def tm_add_correct():
    """TM addition correctness: the unary addition machine halts with correct output.
    |- forall delta,q0,qH,tape_in,z,c0,w,a,b,c,hf,ssc,n,tf,cf.
         Omega(w) -> In(a,w) -> In(b,w) ->
         Function(delta) -> Function(tape_in) ->
         delta_char -> Num(q0,0) -> Num(qH,1) -> Num(z,0) ->
         UnaryTape(tape_in,a,b) -> TMConfig(c0,q0,z,tape_in) ->
         Plus(a,b,c) ->
         Successor(hf,c) -> Successor(ssc,hf) -> Successor(n,ssc) ->
         UnaryOutput(tf,c) -> TMConfig(cf,qH,hf,tf) ->
         TMReaches(delta,c0,n,cf)
    """
    pass
