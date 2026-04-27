"""Theorems: arithmetic module."""

from core.lang import Var, In, Not, Implies, Forall
from definitions import Empty, Omega

def plus_zero_right():
    """m + 0 = m: the base case of addition.
    |- forall w, m, e.
         Omega(w) -> In(m, w) -> Empty(e) -> Plus(m, e, m)
    Construct sf via succ_func_exists, apply recursion_theorem,
    extract Recursive base h(0) = m, package into Plus."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive,
        Successor as SuccDef, Plus as PlusDef)

    w = Var(postfix='w')
    m = Var(postfix='m')
    ev = Var(postfix='e')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    empty_ev = Empty(ev)
    plus_goal = PlusDef(m, ev, m)

    goal = Forall(w, Forall(m, Forall(ev,
        Implies(omega_w, Implies(in_m_w, Implies(empty_ev, plus_goal))))))

    # TODO: use sf_props + recursion_theorem + Recursive base → Plus packaging
    raise NotImplementedError('plus_zero_right: awaiting sf_props')



def plus_comm():
    """Commutativity of addition: m + n = n + m.
    |- forall w, m, n, p.
         Omega(w) -> In(m, w) -> In(n, w) ->
         Plus(m, n, p) -> Plus(n, m, p)
    where Plus(m, n, p) = exists w. Omega(w) /\\ exists h, sf.
         succ_char(sf, w) /\\ Recursive(h, m, sf, w) /\\ Apply(h, n, p)
    Requires sub-theorems:
      plus_zero_right:  m + 0 = m   (Recursive base)
      plus_succ_right:  m + S(n) = S(m + n)  (Recursive step)
      plus_zero_left:   0 + m = m   (induction on m)
      plus_succ_left:   S(m) + n = S(m + n)  (induction on n)
    Then commutativity by induction on n."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive,
        Successor as SuccDef, Plus as PlusDef)

    w = Var(postfix='w')
    m, n, p = Var(postfix='m'), Var(postfix='n'), Var(postfix='p')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    in_n_w = In(n, w)
    plus_mn = PlusDef(m, n, p)
    plus_nm = PlusDef(n, m, p)

    goal = Forall(w, Forall(m, Forall(n, Forall(p,
        Implies(omega_w, Implies(in_m_w, Implies(in_n_w,
            Implies(plus_mn, plus_nm))))))))

    # TODO: proof
    raise NotImplementedError('plus_comm proof not yet built')


