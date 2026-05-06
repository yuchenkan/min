"""Theorems: omega module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from core import zfc
from definitions import Empty, OrdPair, Subset, Inductive, Omega
from theorems.logic import and_elim_left, and_elim_right, char_transfer, eq_substitution, iff_sym, or_iff_compat, unique_empty
from theorems.sets import eq_in_eq, unique_successor

def infinity_gives_inductive():
    """Infinity, Extensionality |- exists b. Inductive(b)
    The Infinity axiom provides an inductive set."""
    from tactics import apply_thm, wl, wr, mp, eel
    from definitions import Inductive, Empty, Successor

    # Infinity gives: exists b. (exists e.e in b  and  Empty(e))  and  (forall y in b.exists s.s in b  and  Successor(s,y))
    # Need: exists b. Inductive(b) = exists b. (forall e.Empty(e)->e in b)  and  (forall x in b.forall s.Succ(s,x)->s in b)
    #
    # The conversion exists ->forall  uses:
    # - unique_empty: Empty(e1)  and  Empty(e2) -> Eq(e1,e2)
    # - unique_successor: Succ(s1,x)  and  Succ(s2,x) -> Eq(s1,s2)
    # - Extensionality: Eq(a,b) -> (a in c <-> b in c)
    #
    # From exists e.e in b  and  Empty(e): exists e0 with e0 in b, Empty(e0).
    # For any e with Empty(e): Eq(e,e0) (unique_empty). Ext: e in b. Hence forall e.Empty(e)->e in b.
    # Similarly for successors.
    #
    from tactics import wl, wr
    b, e0, e, x, s0, s = Var(), Var(), Var(), Var(), Var(), Var()
    inf_ax = zfc.Infinity()
    ext_ax = zfc.Extensionality()

    # Prove: Ext, Inf |- exists b. Inductive(b)
    # Using unique_empty + unique_successor + eq_substitution via raw forall_left + implies_left.

    # Step 1: unique_empty gives Eq(e0,e) from Empty(e0), Empty(e)
    # ue structure: Forall(v1, Implies(Empty(v1), Forall(v2, Implies(Empty(v2), Eq(v1,v2)))))
    ue = unique_empty()
    ue_f = ue.sequent.right[0]  # the actual formula
    eq_e0_e = Eq(e0, e)
    # Peel: forall_left(e0) -> Implies(Empty(e0), Forall(e, Implies(Empty(e), Eq(e0,e))))
    # But we use the ACTUAL body from ue_f to avoid structure mismatch.
    ue_body = ue_f.body  # Implies(Empty(v1), Forall(v2, Implies(Empty(v2), Eq(v1,v2))))
    imp_e_eq = Implies(Empty(e), eq_e0_e)
    fa_e_imp = Forall(e, imp_e_eq)
    imp_e0_rest = Implies(Empty(e0), fa_e_imp)
    # Now peel from inside out, matching ue's actual structure:
    # innermost: Eq(e0,e) |- Eq(e0,e)
    ax_eq = Proof(Sequent([eq_e0_e], [eq_e0_e]), 'axiom', principal=eq_e0_e)
    # implies_left on Empty(e): need Empty(e) on both sides
    ax_ee = wr(Proof(Sequent([Empty(e)], [Empty(e)]), 'axiom', principal=Empty(e)), eq_e0_e)
    il_e = Proof(Sequent([imp_e_eq, Empty(e)], [eq_e0_e]),
                 'implies_left', [ax_ee, wl(ax_eq, Empty(e))], principal=imp_e_eq)
    # forall_left(e): Forall(e, imp_e_eq), Empty(e) |- Eq(e0,e)
    fl_e = Proof(Sequent([fa_e_imp, Empty(e)], [eq_e0_e]),
                 'forall_left', [il_e], principal=fa_e_imp, term=e)
    # implies_left on Empty(e0): need Empty(e0) on both sides
    ax_e0 = wr(Proof(Sequent([Empty(e0), Empty(e)], [Empty(e0)]),
                     'weakening_left',
                     [Proof(Sequent([Empty(e0)], [Empty(e0)]), 'axiom', principal=Empty(e0))],
                     principal=Empty(e)), eq_e0_e)
    il_e0 = Proof(Sequent([imp_e0_rest, Empty(e0), Empty(e)], [eq_e0_e]),
                  'implies_left', [ax_e0, wl(fl_e, Empty(e0))], principal=imp_e0_rest)
    # forall_left(e0): ue_f, Empty(e0), Empty(e) |- Eq(e0,e)
    fl_e0 = Proof(Sequent([ue_f, Empty(e0), Empty(e)], [eq_e0_e]),
                  'forall_left', [il_e0], principal=ue_f, term=e0)
    # Cut with ue: Empty(e0), Empty(e) |- Eq(e0,e)
    got_eq = Proof(Sequent([Empty(e0), Empty(e)], [eq_e0_e]), 'cut',
        [wr(wl(ue, Empty(e0), Empty(e)), eq_e0_e), fl_e0],
        principal=ue_f)

    # Step 2: eq_substitution gives Iff(In(e0,b), In(e,b)) from Eq(e0,e)
    es = eq_substitution()
    iff_eb = Iff(In(e0, b), In(e, b))
    imp_eq_iff = Implies(eq_e0_e, iff_eb)
    fa_z = Forall(b, imp_eq_iff)
    fa_ez = Forall(e, fa_z)
    fa_e0ez = Forall(e0, fa_ez)
    ax_iff = Proof(Sequent([iff_eb], [iff_eb]), 'axiom', principal=iff_eb)
    ax_eq2 = wr(Proof(Sequent([eq_e0_e], [eq_e0_e]), 'axiom', principal=eq_e0_e), iff_eb)
    il_eq = Proof(Sequent([imp_eq_iff, eq_e0_e], [iff_eb]),
                  'implies_left', [ax_eq2, wl(ax_iff, eq_e0_e)], principal=imp_eq_iff)
    fl_z = Proof(Sequent([fa_z, eq_e0_e], [iff_eb]), 'forall_left', [il_eq], principal=fa_z, term=b)
    fl_ez = Proof(Sequent([fa_ez, eq_e0_e], [iff_eb]), 'forall_left', [fl_z], principal=fa_ez, term=e)
    fl_e0ez = Proof(Sequent([fa_e0ez, eq_e0_e], [iff_eb]), 'forall_left', [fl_ez], principal=fa_e0ez, term=e0)
    got_iff = Proof(Sequent([ext_ax, eq_e0_e], [iff_eb]), 'cut',
        [wr(wl(es, eq_e0_e), iff_eb), wl(fl_e0ez, ext_ax)], principal=fa_e0ez)

    # Step 3: extract forward In(e0,b)->In(e,b) from Iff
    fwd_eb = Implies(In(e0, b), In(e, b))
    bwd_eb = Implies(In(e, b), In(e0, b))
    H_iff = Implies(fwd_eb, Not(bwd_eb))
    ef1 = Proof(Sequent([iff_eb, fwd_eb], [fwd_eb]), 'axiom', principal=fwd_eb)
    ef2 = Proof(Sequent([iff_eb, fwd_eb], [Not(bwd_eb), fwd_eb]), 'weakening_right', [ef1], principal=Not(bwd_eb))
    ef3 = Proof(Sequent([iff_eb], [H_iff, fwd_eb]), 'implies_right', [ef2], principal=H_iff)
    ef4 = wr(Proof(Sequent([H_iff], [H_iff]), 'axiom', principal=H_iff), fwd_eb)
    ef5 = Proof(Sequent([H_iff, iff_eb], [fwd_eb]), 'not_left', [ef4], principal=iff_eb)
    got_fwd_iff = Proof(Sequent([iff_eb], [fwd_eb]), 'cut', [ef3, ef5], principal=H_iff)
    got_fwd = Proof(Sequent([ext_ax, eq_e0_e], [fwd_eb]), 'cut',
        [wr(got_iff, fwd_eb), wl(got_fwd_iff, ext_ax, eq_e0_e)], principal=iff_eb)
    got_fwd2 = Proof(Sequent([ext_ax, Empty(e0), Empty(e)], [fwd_eb]), 'cut',
        [wr(wl(got_eq, ext_ax), fwd_eb), wl(got_fwd, Empty(e0), Empty(e))], principal=eq_e0_e)

    # MP: ext_ax, Empty(e0), Empty(e), In(e0,b) |- In(e,b)
    got_in_e = mp(got_fwd2, Proof(Sequent([In(e0, b)], [In(e0, b)]), 'axiom', principal=In(e0, b)),
                  In(e0, b), In(e, b))

    # Part 1: forall e. Empty(e) -> In(e, b)
    imp_e_in = Implies(Empty(e), In(e, b))
    d1 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b)], [imp_e_in]), 'implies_right', [got_in_e], principal=imp_e_in)
    fa_e_part1 = Forall(e, imp_e_in)
    d2 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b)], [fa_e_part1]), 'forall_right', [d1], principal=fa_e_part1, term=e)

    # === Part 2: successor closure (same pattern with unique_successor) ===
    us = unique_successor()
    succ_s0 = Successor(s0, x); succ_s = Successor(s, x)
    eq_s0_s = Eq(s0, s)
    imp_s_eqs = Implies(succ_s, eq_s0_s)
    imp_s0_rest_s = Implies(succ_s0, imp_s_eqs)
    fa_s2 = Forall(s, imp_s0_rest_s)
    fa_s1s2 = Forall(s0, fa_s2)
    fa_xs1s2 = Forall(x, fa_s1s2)
    ax_eqs = Proof(Sequent([eq_s0_s], [eq_s0_s]), 'axiom', principal=eq_s0_s)
    ax_ss = wr(Proof(Sequent([succ_s, succ_s0], [succ_s]),
                     'weakening_left',
                     [Proof(Sequent([succ_s], [succ_s]), 'axiom', principal=succ_s)], principal=succ_s0),
               eq_s0_s)
    il_ss = Proof(Sequent([imp_s_eqs, succ_s, succ_s0], [eq_s0_s]),
                  'implies_left', [ax_ss, wl(ax_eqs, succ_s, succ_s0)], principal=imp_s_eqs)
    ax_s0s = wr(Proof(Sequent([succ_s0, succ_s], [succ_s0]),
                      'weakening_left',
                      [Proof(Sequent([succ_s0], [succ_s0]), 'axiom', principal=succ_s0)], principal=succ_s),
                eq_s0_s)
    il_s0s = Proof(Sequent([imp_s0_rest_s, succ_s0, succ_s], [eq_s0_s]),
                   'implies_left', [ax_s0s, il_ss], principal=imp_s0_rest_s)
    fl_ss = Proof(Sequent([fa_s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [il_s0s], principal=fa_s2, term=s)
    fl_s1s = Proof(Sequent([fa_s1s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [fl_ss], principal=fa_s1s2, term=s0)
    fl_xs = Proof(Sequent([fa_xs1s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [fl_s1s], principal=fa_xs1s2, term=x)
    got_eq_s = Proof(Sequent([succ_s0, succ_s], [eq_s0_s]), 'cut',
        [wr(wl(us, succ_s0, succ_s), eq_s0_s), fl_xs], principal=fa_xs1s2)

    iff_sb = Iff(In(s0, b), In(s, b))
    imp_eq_iffs = Implies(eq_s0_s, iff_sb)
    fa_zs = Forall(b, imp_eq_iffs); fa_szs = Forall(s, fa_zs); fa_s0szs = Forall(s0, fa_szs)
    ax_iffs = Proof(Sequent([iff_sb], [iff_sb]), 'axiom', principal=iff_sb)
    ax_eqs2 = wr(Proof(Sequent([eq_s0_s], [eq_s0_s]), 'axiom', principal=eq_s0_s), iff_sb)
    il_eqs = Proof(Sequent([imp_eq_iffs, eq_s0_s], [iff_sb]), 'implies_left', [ax_eqs2, wl(ax_iffs, eq_s0_s)], principal=imp_eq_iffs)
    fl_zs = Proof(Sequent([fa_zs, eq_s0_s], [iff_sb]), 'forall_left', [il_eqs], principal=fa_zs, term=b)
    fl_szs = Proof(Sequent([fa_szs, eq_s0_s], [iff_sb]), 'forall_left', [fl_zs], principal=fa_szs, term=s)
    fl_s0szs = Proof(Sequent([fa_s0szs, eq_s0_s], [iff_sb]), 'forall_left', [fl_szs], principal=fa_s0szs, term=s0)
    got_iff_s = Proof(Sequent([ext_ax, eq_s0_s], [iff_sb]), 'cut',
        [wr(wl(es, eq_s0_s), iff_sb), wl(fl_s0szs, ext_ax)], principal=fa_s0szs)
    fwd_sb = Implies(In(s0, b), In(s, b)); bwd_sb = Implies(In(s, b), In(s0, b))
    H_s = Implies(fwd_sb, Not(bwd_sb))
    sf1 = Proof(Sequent([iff_sb, fwd_sb], [fwd_sb]), 'axiom', principal=fwd_sb)
    sf2 = Proof(Sequent([iff_sb, fwd_sb], [Not(bwd_sb), fwd_sb]), 'weakening_right', [sf1], principal=Not(bwd_sb))
    sf3 = Proof(Sequent([iff_sb], [H_s, fwd_sb]), 'implies_right', [sf2], principal=H_s)
    sf4 = wr(Proof(Sequent([H_s], [H_s]), 'axiom', principal=H_s), fwd_sb)
    sf5 = Proof(Sequent([H_s, iff_sb], [fwd_sb]), 'not_left', [sf4], principal=iff_sb)
    got_fwd_s = Proof(Sequent([iff_sb], [fwd_sb]), 'cut', [sf3, sf5], principal=H_s)
    got_fwd_s2 = Proof(Sequent([ext_ax, eq_s0_s], [fwd_sb]), 'cut',
        [wr(got_iff_s, fwd_sb), wl(got_fwd_s, ext_ax, eq_s0_s)], principal=iff_sb)
    got_fwd_s3 = Proof(Sequent([ext_ax, succ_s0, succ_s], [fwd_sb]), 'cut',
        [wr(wl(got_eq_s, ext_ax), fwd_sb), wl(got_fwd_s2, succ_s0, succ_s)], principal=eq_s0_s)
    got_in_s = mp(got_fwd_s3, Proof(Sequent([In(s0, b)], [In(s0, b)]), 'axiom', principal=In(s0, b)),
                  In(s0, b), In(s, b))
    imp_s_in = Implies(succ_s, In(s, b))
    d3 = Proof(Sequent([ext_ax, succ_s0, In(s0, b)], [imp_s_in]), 'implies_right', [got_in_s], principal=imp_s_in)
    fa_s_part2 = Forall(s, imp_s_in)
    d4 = Proof(Sequent([ext_ax, succ_s0, In(s0, b)], [fa_s_part2]), 'forall_right', [d3], principal=fa_s_part2, term=s)

    # Package And(In(s0,b), succ_s0) -> existential elim
    and_s0 = And(In(s0, b), succ_s0)
    ax_as = Proof(Sequent([and_s0], [and_s0]), 'axiom', principal=and_s0)
    got_ins0 = apply_thm(and_elim_left(In(s0, b), succ_s0, []), [], and_s0, In(s0, b), ax_as)
    got_succ0 = apply_thm(and_elim_right(In(s0, b), succ_s0, []), [], and_s0, succ_s0,
                           Proof(Sequent([and_s0], [and_s0]), 'axiom', principal=and_s0))
    d4a = Proof(Sequent([ext_ax, and_s0], [fa_s_part2]), 'cut',
        [wr(wl(got_succ0, ext_ax), fa_s_part2),
         Proof(Sequent([ext_ax, and_s0, succ_s0], [fa_s_part2]), 'cut',
             [wr(wl(got_ins0, ext_ax, succ_s0), fa_s_part2), wl(d4, and_s0)], principal=In(s0, b))],
        principal=succ_s0)
    d5 = eel(d4a, and_s0, s0)
    ex_s0 = Exists(s0, and_s0)

    # Closure from Infinity
    inf_closure = Forall(x, Implies(In(x, b), ex_s0))
    imp_x_ex = Implies(In(x, b), ex_s0)
    fl_cl = Proof(Sequent([inf_closure], [imp_x_ex]), 'forall_left',
        [Proof(Sequent([imp_x_ex], [imp_x_ex]), 'axiom', principal=imp_x_ex)], principal=inf_closure, term=x)
    got_ex_s0 = mp(fl_cl, Proof(Sequent([In(x, b)], [In(x, b)]), 'axiom', principal=In(x, b)), In(x, b), ex_s0)
    got_cl = Proof(Sequent([ext_ax, inf_closure, In(x, b)], [fa_s_part2]), 'cut',
        [wr(wl(got_ex_s0, ext_ax), fa_s_part2), wl(d5, inf_closure, In(x, b))], principal=ex_s0)
    imp_x_fa = Implies(In(x, b), fa_s_part2)
    dc1 = Proof(Sequent([ext_ax, inf_closure], [imp_x_fa]), 'implies_right', [got_cl], principal=imp_x_fa)
    fa_x_part2 = Forall(x, imp_x_fa)
    dc2 = Proof(Sequent([ext_ax, inf_closure], [fa_x_part2]), 'forall_right', [dc1], principal=fa_x_part2, term=x)

    # Build Inductive(b) from parts
    ind_b = Inductive(b)
    ncl = Not(fa_x_part2)
    a1 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure, ncl], []), 'not_left', [wl(dc2, Empty(e0), In(e0, b))], principal=ncl)
    a2 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure, Implies(fa_e_part1, ncl)], []),
               'implies_left', [wl(d2, inf_closure), a1], principal=Implies(fa_e_part1, ncl))
    got_ind = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure], [ind_b]), 'not_right', [a2], principal=ind_b)

    # Package from inf_empty
    inf_empty = Exists(e0, And(In(e0, b), Empty(e0)))
    and_e0 = And(In(e0, b), Empty(e0))
    ax_ae = Proof(Sequent([and_e0], [and_e0]), 'axiom', principal=and_e0)
    got_ine0 = apply_thm(and_elim_left(In(e0, b), Empty(e0), []), [], and_e0, In(e0, b), ax_ae)
    got_empe0 = apply_thm(and_elim_right(In(e0, b), Empty(e0), []), [], and_e0, Empty(e0),
                           Proof(Sequent([and_e0], [and_e0]), 'axiom', principal=and_e0))
    gi2 = Proof(Sequent([ext_ax, and_e0, inf_closure], [ind_b]), 'cut',
        [wr(wl(got_empe0, ext_ax, inf_closure), ind_b),
         Proof(Sequent([ext_ax, and_e0, Empty(e0), inf_closure], [ind_b]), 'cut',
             [wr(wl(got_ine0, ext_ax, Empty(e0), inf_closure), ind_b), wl(got_ind, and_e0)], principal=In(e0, b))],
        principal=Empty(e0))
    gi3 = eel(gi2, and_e0, e0)

    # Package inf_and
    inf_and = And(inf_empty, inf_closure)
    ax_ia = Proof(Sequent([inf_and], [inf_and]), 'axiom', principal=inf_and)
    got_ie = apply_thm(and_elim_left(inf_empty, inf_closure, []), [], inf_and, inf_empty, ax_ia)
    got_ic = apply_thm(and_elim_right(inf_empty, inf_closure, []), [], inf_and, inf_closure,
                        Proof(Sequent([inf_and], [inf_and]), 'axiom', principal=inf_and))
    gi4 = Proof(Sequent([ext_ax, inf_and], [ind_b]), 'cut',
        [wr(wl(got_ie, ext_ax), ind_b),
         Proof(Sequent([ext_ax, inf_and, inf_empty], [ind_b]), 'cut',
             [wr(wl(got_ic, ext_ax, inf_empty), ind_b), wl(gi3, inf_and)], principal=inf_closure)],
        principal=inf_empty)

    # Exist intro + elim
    ex_ind = Exists(b, ind_b)
    nl = Proof(Sequent(gi4.sequent.left + [Not(ind_b)], []), 'not_left', [gi4], principal=Not(ind_b))
    fl = Proof(Sequent(gi4.sequent.left + [Forall(b, Not(ind_b))], []), 'forall_left', [nl], principal=Forall(b, Not(ind_b)), term=b)
    gex = Proof(Sequent(gi4.sequent.left, [ex_ind]), 'not_right', [fl], principal=ex_ind)
    gfex = eel(gex, inf_and, b)
    gfex.name = 'infinity_gives_inductive'
    return gfex



def omega_is_inductive():
    """Infinity, Extensionality |- forall w. Omega(w) -> Inductive(w)
    omega is itself an inductive set."""
    from tactics import apply_thm, wl, wr, mp, eel, fl
    from definitions import Inductive, Omega, Empty, Successor

    w, b0, xv, cv, ev, sv = Var(), Var(), Var(), Var(), Var(), Var()
    inf_ax = zfc.Infinity()
    ext_ax = zfc.Extensionality()
    omega_w = Omega(w)
    ind_w = Inductive(w)

    # Step 1: From infinity_gives_inductive: exists b. Inductive(b)
    igi = infinity_gives_inductive()  # [ext, inf] |- [exists b. Inductive(b)]
    ind_b0 = Inductive(b0)
    ex_ind = Exists(b0, ind_b0)

    # Step 2: From Omega(w) with b=b0: Inductive(b0) -> forall x. x in w <-> cond(x)
    cond_xv = And(In(xv, b0), Forall(cv, Implies(Inductive(cv), In(xv, cv))))
    iff_w = Iff(In(xv, w), cond_xv)
    fa_iff = Forall(xv, iff_w)
    imp_ind_fa = Implies(ind_b0, fa_iff)


    # omega_w |- Implies(Inductive(b0), fa_iff)
    got_imp = fl(omega_w, imp_ind_fa, b0)
    # MP with Inductive(b0): omega_w, Inductive(b0) |- fa_iff
    got_fa = mp(got_imp,
                Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0),
                ind_b0, fa_iff)

    # Instantiate fa_iff with xv=ev (for empty part) and xv (for closure part)
    # via cut on fa_iff
    fl_iff = fl(fa_iff, iff_w, xv)  # fa_iff |- iff_w
    def _get_iff(xvar):
        """From got_fa, instantiate and get: omega_w, ind_b0 |- Iff(In(xvar,w), cond(xvar))"""
        c_xvar = And(In(xvar, b0), Forall(cv, Implies(Inductive(cv), In(xvar, cv))))
        iff_xvar = Iff(In(xvar, w), c_xvar)
        fl_x = fl(fa_iff, iff_xvar, xvar)
        return Proof(Sequent(got_fa.sequent.left, [iff_xvar]), 'cut',
            [wr(got_fa, iff_xvar), wl(fl_x, *got_fa.sequent.left)], principal=fa_iff)

    # === Extract Iff backward: cond -> In(xvar, w) ===
    def _ext_bwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = wr(Proof(Sequent([H], [H]), 'axiom', principal=H), RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    def _ext_fwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = wr(Proof(Sequent([H], [H]), 'axiom', principal=H), LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    # === Part 1: forall e. Empty(e) -> e in w ===
    # For ev with Empty(ev):
    # Need cond(ev) = In(ev, b0)  and  forall c. Ind(c) -> In(ev, c)
    # From Ind(b0): Empty(ev) -> In(ev, b0) [first part of Inductive]
    # From Ind(c) for any c: Empty(ev) -> In(ev, c) [first part of Inductive(c)]
    # So forall c. Ind(c) -> In(ev, c) follows from Empty(ev).

    # Unpack Ind(b0): And(forall e.Empty(e)->In(e,b0), forall x.In(x,b0)->forall s.Succ(s,x)->In(s,b0))
    ind_empty = Forall(ev, Implies(Empty(ev), In(ev, b0)))  # first part
    ind_closure_b0 = Forall(xv, Implies(In(xv, b0), Forall(sv, Implies(Successor(sv, xv), In(sv, b0)))))

    ax_ind = Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0)
    got_empty_b0 = apply_thm(and_elim_left(ind_empty, ind_closure_b0, []), [],
                              ind_b0, ind_empty, ax_ind)
    # got_empty_b0: [ind_b0] |- [forall e. Empty(e) -> In(e, b0)]

    # For In(ev, b0): ind_b0, Empty(ev) |- In(ev, b0)
    imp_emp_in = Implies(Empty(ev), In(ev, b0))
    fl_emp = fl(ind_empty, imp_emp_in, ev)
    got_ev_b0 = mp(Proof(Sequent([ind_b0], [imp_emp_in]), 'cut',
                    [wr(got_empty_b0, imp_emp_in), wl(fl_emp, ind_b0)], principal=ind_empty),
                   Proof(Sequent([Empty(ev)], [Empty(ev)]), 'axiom', principal=Empty(ev)),
                   Empty(ev), In(ev, b0))
    # got_ev_b0: [ind_b0, Empty(ev)] |- [In(ev, b0)]

    # For forall c. Ind(c) -> In(ev, c):
    # From Ind(c): forall e. Empty(e) -> In(e, c). Instantiate e=ev: Empty(ev) -> In(ev, c).
    ind_c = Inductive(cv)
    ind_empty_c = Forall(ev, Implies(Empty(ev), In(ev, cv)))
    ind_closure_c = Forall(xv, Implies(In(xv, cv), Forall(sv, Implies(Successor(sv, xv), In(sv, cv)))))
    ax_ind_c = Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c)
    got_empty_c = apply_thm(and_elim_left(ind_empty_c, ind_closure_c, []), [],
                             ind_c, ind_empty_c, ax_ind_c)
    fl_emp_c = fl(ind_empty_c, Implies(Empty(ev), In(ev, cv)), ev)
    got_ev_c = mp(Proof(Sequent([ind_c], [Implies(Empty(ev), In(ev, cv))]), 'cut',
                   [wr(got_empty_c, Implies(Empty(ev), In(ev, cv))),
                    wl(fl_emp_c, ind_c)], principal=ind_empty_c),
                  Proof(Sequent([Empty(ev)], [Empty(ev)]), 'axiom', principal=Empty(ev)),
                  Empty(ev), In(ev, cv))
    # got_ev_c: [ind_c, Empty(ev)] |- [In(ev, cv)]

    # forall c. Ind(c) -> In(ev, c): discharge Ind(c), forall c
    imp_ind_in = Implies(ind_c, In(ev, cv))
    d_c = Proof(Sequent([Empty(ev)], [imp_ind_in]), 'implies_right', [got_ev_c], principal=imp_ind_in)
    fa_c = Forall(cv, imp_ind_in)
    d_c2 = Proof(Sequent([Empty(ev)], [fa_c]), 'forall_right', [d_c], principal=fa_c, term=cv)
    # d_c2: [Empty(ev)] |- [forall c. Ind(c) -> In(ev, c)]

    # Build cond(ev) = And(In(ev, b0), forall c. Ind(c) -> In(ev, c))
    cond_ev = And(In(ev, b0), fa_c)
    n_fc = Not(fa_c)
    and_c1 = Proof(Sequent([ind_b0, Empty(ev), n_fc], []),
                   'not_left', [wl(d_c2, ind_b0)], principal=n_fc)
    and_c2 = Proof(Sequent([ind_b0, Empty(ev), Implies(In(ev, b0), n_fc)], []),
                   'implies_left', [got_ev_b0, and_c1], principal=Implies(In(ev, b0), n_fc))
    got_cond_ev = Proof(Sequent([ind_b0, Empty(ev)], [cond_ev]),
                        'not_right', [and_c2], principal=cond_ev)
    # got_cond_ev: [ind_b0, Empty(ev)] |- [cond_ev]

    # Apply Iff backward: cond_ev -> In(ev, w)
    iff_ev = Iff(In(ev, w), cond_ev)
    got_iff_ev = _get_iff(ev)  # omega_w, ind_b0 |- iff_ev
    bwd_ev = _ext_bwd(iff_ev)  # iff_ev |- cond_ev -> In(ev, w)
    got_bwd_ev = Proof(Sequent(got_iff_ev.sequent.left, [Implies(cond_ev, In(ev, w))]), 'cut',
        [wr(got_iff_ev, Implies(cond_ev, In(ev, w))),
         wl(bwd_ev, *got_iff_ev.sequent.left)], principal=iff_ev)
    # MP: omega_w, ind_b0, cond_ev |- In(ev, w)
    got_ev_w = mp(got_bwd_ev, got_cond_ev, cond_ev, In(ev, w))
    # got_ev_w: [omega_w, ind_b0, Empty(ev)] |- [In(ev, w)]

    # Part 1 done: discharge Empty(ev), forall ev
    imp_emp_w = Implies(Empty(ev), In(ev, w))
    p1 = Proof(Sequent([omega_w, ind_b0], [imp_emp_w]),
               'implies_right', [got_ev_w], principal=imp_emp_w)
    fa_ev = Forall(ev, imp_emp_w)
    p1f = Proof(Sequent([omega_w, ind_b0], [fa_ev]),
                'forall_right', [p1], principal=fa_ev, term=ev)

    # === Part 2: forall x in w. forall s. Succ(s,x) -> s in w ===
    # For xv in w with Succ(sv, xv):
    # Iff forward at xv: In(xv,w) -> cond(xv). Extract In(xv,b0) and forall c.Ind(c)->In(xv,c).
    # From Ind(b0) closure + In(xv,b0) + Succ(sv,xv): In(sv,b0).
    # From Ind(c) closure + In(xv,c) + Succ(sv,xv): In(sv,c). So forall c.Ind(c)->In(sv,c).
    # Build cond(sv). Iff backward: In(sv,w). (ok)

    got_iff_xv = _get_iff(xv)  # omega_w, ind_b0 |- Iff(In(xv,w), cond(xv))
    cond_xv_full = And(In(xv, b0), Forall(cv, Implies(Inductive(cv), In(xv, cv))))
    iff_xv = Iff(In(xv, w), cond_xv_full)
    fwd_xv = _ext_fwd(iff_xv)  # iff_xv |- In(xv,w) -> cond(xv)
    got_fwd_xv = Proof(Sequent(got_iff_xv.sequent.left, [Implies(In(xv, w), cond_xv_full)]), 'cut',
        [wr(got_iff_xv, Implies(In(xv, w), cond_xv_full)),
         wl(fwd_xv, *got_iff_xv.sequent.left)], principal=iff_xv)
    # MP with In(xv, w):
    got_cond_xv = mp(got_fwd_xv,
                     Proof(Sequent([In(xv, w)], [In(xv, w)]), 'axiom', principal=In(xv, w)),
                     In(xv, w), cond_xv_full)
    # got_cond_xv: [omega_w, ind_b0, In(xv,w)] |- [cond_xv_full]

    # Extract In(xv, b0) and forall c.Ind(c)->In(xv,c) from cond
    fa_c_xv = Forall(cv, Implies(Inductive(cv), In(xv, cv)))
    ax_cond = Proof(Sequent([cond_xv_full], [cond_xv_full]), 'axiom', principal=cond_xv_full)
    got_xv_b0 = apply_thm(and_elim_left(In(xv, b0), fa_c_xv, []), [],
                            cond_xv_full, In(xv, b0), ax_cond)
    got_fa_c_xv = apply_thm(and_elim_right(In(xv, b0), fa_c_xv, []), [],
                              cond_xv_full, fa_c_xv,
                              Proof(Sequent([cond_xv_full], [cond_xv_full]), 'axiom', principal=cond_xv_full))

    # From Ind(b0) closure + In(xv,b0) + Succ(sv,xv): In(sv,b0)
    got_closure_b0 = apply_thm(and_elim_right(ind_empty, ind_closure_b0, []), [],
                                ind_b0, ind_closure_b0,
                                Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0))
    # got_closure_b0: [ind_b0] |- [forall x.In(x,b0)->forall s.Succ(s,x)->In(s,b0)]
    imp_xv_cl = Implies(In(xv, b0), Forall(sv, Implies(Successor(sv, xv), In(sv, b0))))
    fl_cl = fl(ind_closure_b0, imp_xv_cl, xv)
    fa_sv_imp = Forall(sv, Implies(Successor(sv, xv), In(sv, b0)))
    got_fa_sv = mp(Proof(Sequent([ind_b0], [imp_xv_cl]), 'cut',
                    [wr(got_closure_b0, imp_xv_cl), wl(fl_cl, ind_b0)], principal=ind_closure_b0),
                   got_xv_b0, In(xv, b0), fa_sv_imp)
    # got_fa_sv: [ind_b0, cond_xv_full] |- [forall s.Succ(s,xv)->In(s,b0)]
    imp_sv_in = Implies(Successor(sv, xv), In(sv, b0))
    fl_sv = fl(fa_sv_imp, imp_sv_in, sv)
    got_sv_b0 = mp(Proof(Sequent(got_fa_sv.sequent.left, [imp_sv_in]), 'cut',
                    [wr(got_fa_sv, imp_sv_in), wl(fl_sv, *got_fa_sv.sequent.left)], principal=fa_sv_imp),
                   Proof(Sequent([Successor(sv, xv)], [Successor(sv, xv)]), 'axiom', principal=Successor(sv, xv)),
                   Successor(sv, xv), In(sv, b0))
    # got_sv_b0: [ind_b0, cond_xv_full, Succ(sv,xv)] |- [In(sv,b0)]

    # For forall c. Ind(c) -> In(sv, c): from Ind(c), In(xv,c), Succ(sv,xv) -> In(sv,c)
    got_closure_c = apply_thm(and_elim_right(ind_empty_c, ind_closure_c, []), [],
                               ind_c, ind_closure_c,
                               Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c))
    imp_xv_cl_c = Implies(In(xv, cv), Forall(sv, Implies(Successor(sv, xv), In(sv, cv))))
    fl_cl_c = fl(ind_closure_c, imp_xv_cl_c, xv)
    # From forall c.Ind(c)->In(xv,c), instantiate c=cv: Ind(cv) -> In(xv, cv)
    imp_ind_xv = Implies(Inductive(cv), In(xv, cv))
    fl_c_xv = fl(fa_c_xv, imp_ind_xv, cv)
    got_xv_cv = mp(wl(fl_c_xv, ind_c),
                   Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c),
                   ind_c, In(xv, cv))
    # got_xv_cv: [fa_c_xv, ind_c] |- [In(xv, cv)]

    fa_sv_imp_c = Forall(sv, Implies(Successor(sv, xv), In(sv, cv)))
    got_fa_sv_c = mp(Proof(Sequent([ind_c], [imp_xv_cl_c]), 'cut',
                      [wr(got_closure_c, imp_xv_cl_c), wl(fl_cl_c, ind_c)], principal=ind_closure_c),
                     got_xv_cv, In(xv, cv), fa_sv_imp_c)
    imp_sv_in_c = Implies(Successor(sv, xv), In(sv, cv))
    fl_sv_c = fl(fa_sv_imp_c, imp_sv_in_c, sv)
    got_sv_cv = mp(Proof(Sequent(got_fa_sv_c.sequent.left, [imp_sv_in_c]), 'cut',
                    [wr(got_fa_sv_c, imp_sv_in_c), wl(fl_sv_c, *got_fa_sv_c.sequent.left)], principal=fa_sv_imp_c),
                   Proof(Sequent([Successor(sv, xv)], [Successor(sv, xv)]), 'axiom', principal=Successor(sv, xv)),
                   Successor(sv, xv), In(sv, cv))
    # got_sv_cv: [fa_c_xv, ind_c, Succ(sv,xv)] |- [In(sv, cv)]

    # forall c. Ind(c) -> In(sv, c): discharge ind_c, forall cv
    imp_ind_sv = Implies(ind_c, In(sv, cv))
    d_sv_c = Proof(Sequent([fa_c_xv, Successor(sv, xv)], [imp_ind_sv]),
                   'implies_right', [got_sv_cv], principal=imp_ind_sv)
    fa_c_sv = Forall(cv, imp_ind_sv)
    d_sv_c2 = Proof(Sequent([fa_c_xv, Successor(sv, xv)], [fa_c_sv]),
                    'forall_right', [d_sv_c], principal=fa_c_sv, term=cv)
    # d_sv_c2: [fa_c_xv, Succ(sv,xv)] |- [forall c. Ind(c) -> In(sv, c)]

    # Build cond(sv): And(In(sv,b0), fa_c_sv)
    cond_sv = And(In(sv, b0), fa_c_sv)
    n_fcsv = Not(fa_c_sv)
    and_sv1 = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), fa_c_xv, n_fcsv], []),
                    'not_left', [wl(d_sv_c2, ind_b0, cond_xv_full)], principal=n_fcsv)
    # Hmm, got_sv_b0 has [ind_b0, cond_xv_full, Succ] and d_sv_c2 has [fa_c_xv, Succ].
    # Need to merge: [ind_b0, cond_xv_full, fa_c_xv, Succ(sv,xv)]
    # But fa_c_xv comes from cond_xv_full (it's the second component of And).
    # So we need to extract fa_c_xv from cond_xv_full via and_elim_right, then cut.

    # Actually, got_fa_c_xv: [cond_xv_full] |- [fa_c_xv]
    # Cut fa_c_xv: replace fa_c_xv with cond_xv_full
    d_sv_c2_from_cond = Proof(Sequent([cond_xv_full, Successor(sv, xv)], [fa_c_sv]), 'cut',
        [wr(wl(got_fa_c_xv, Successor(sv, xv)), fa_c_sv),
         wl(d_sv_c2, cond_xv_full)], principal=fa_c_xv)

    and_sv1b = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), n_fcsv], []),
                     'not_left', [wl(d_sv_c2_from_cond, ind_b0)], principal=n_fcsv)
    and_sv2 = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), Implies(In(sv, b0), n_fcsv)], []),
                    'implies_left', [got_sv_b0, and_sv1b], principal=Implies(In(sv, b0), n_fcsv))
    got_cond_sv = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv)], [cond_sv]),
                        'not_right', [and_sv2], principal=cond_sv)

    # Cut cond_xv_full from In(xv, w):
    got_cond_sv2 = Proof(Sequent([omega_w, ind_b0, In(xv, w), Successor(sv, xv)], [cond_sv]), 'cut',
        [wr(wl(got_cond_xv, Successor(sv, xv)), cond_sv),
         wl(got_cond_sv, omega_w, In(xv, w))], principal=cond_xv_full)

    # Apply Iff backward for sv:
    cond_sv_full = cond_sv  # And(In(sv, b0), forall c. Ind(c) -> In(sv, c))
    iff_sv = Iff(In(sv, w), cond_sv_full)
    got_iff_sv = _get_iff(sv)
    bwd_sv = _ext_bwd(iff_sv)
    got_bwd_sv = Proof(Sequent(got_iff_sv.sequent.left, [Implies(cond_sv_full, In(sv, w))]), 'cut',
        [wr(got_iff_sv, Implies(cond_sv_full, In(sv, w))),
         wl(bwd_sv, *got_iff_sv.sequent.left)], principal=iff_sv)
    got_sv_w = mp(got_bwd_sv, got_cond_sv2, cond_sv_full, In(sv, w))
    # got_sv_w: [omega_w, ind_b0, In(xv,w), Succ(sv,xv)] |- [In(sv,w)]

    # Part 2: discharge Succ, forall sv, discharge In(xv,w), forall xv
    imp_succ_w = Implies(Successor(sv, xv), In(sv, w))
    p2a = Proof(Sequent([omega_w, ind_b0, In(xv, w)], [imp_succ_w]),
                'implies_right', [got_sv_w], principal=imp_succ_w)
    fa_sv_w = Forall(sv, imp_succ_w)
    p2b = Proof(Sequent([omega_w, ind_b0, In(xv, w)], [fa_sv_w]),
                'forall_right', [p2a], principal=fa_sv_w, term=sv)
    imp_xv_w = Implies(In(xv, w), fa_sv_w)
    p2c = Proof(Sequent([omega_w, ind_b0], [imp_xv_w]),
                'implies_right', [p2b], principal=imp_xv_w)
    fa_xv_w = Forall(xv, imp_xv_w)
    p2f = Proof(Sequent([omega_w, ind_b0], [fa_xv_w]),
                'forall_right', [p2c], principal=fa_xv_w, term=xv)

    # === Build Inductive(w) = And(fa_ev, fa_xv_w) ===
    n_p2 = Not(fa_xv_w)
    a1 = Proof(Sequent([omega_w, ind_b0, n_p2], []), 'not_left', [p2f], principal=n_p2)
    a2 = Proof(Sequent([omega_w, ind_b0, Implies(fa_ev, n_p2)], []),
               'implies_left', [p1f, a1], principal=Implies(fa_ev, n_p2))
    got_ind_w = Proof(Sequent([omega_w, ind_b0], [ind_w]), 'not_right', [a2], principal=ind_w)

    # === Existential elimination on b0 ===

    got_ind_w2 = eel(got_ind_w, ind_b0, b0)
    # got_ind_w2: [omega_w, Exists(b0, Inductive(b0))] |- [Inductive(w)]

    # Cut with infinity_gives_inductive:
    got_ind_w3 = Proof(Sequent([omega_w, ext_ax, inf_ax], [ind_w]), 'cut',
        [wr(wl(igi, omega_w), ind_w), wl(got_ind_w2, ext_ax, inf_ax)], principal=ex_ind)

    # Close: discharge omega_w, forall w
    imp_omega = Implies(omega_w, ind_w)
    s1 = Proof(Sequent([ext_ax, inf_ax], [imp_omega]), 'implies_right', [got_ind_w3], principal=imp_omega)
    fa_w = Forall(w, imp_omega)
    s2 = Proof(Sequent([ext_ax, inf_ax], [fa_w]), 'forall_right', [s1], principal=fa_w, term=w)
    s2.name = 'omega_is_inductive'
    return s2



def omega_contains_empty():
    """Ext, Inf |- forall w. Omega(w) -> forall e. Empty(e) -> In(e, w)
    Every empty set is in omega."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor

    w, ev = Var(), Var()
    omega_w = Omega(w)
    ind_w = Inductive(w)
    empty_e = Empty(ev)
    in_e_w = In(ev, w)

    # Inductive(w) = And(forall e. Empty(e) -> In(e,w), forall x. In(x,w) -> forall s. Succ(s,x) -> In(s,w))
    sv, xv = Var(), Var()
    base_w = Forall(ev, Implies(empty_e, in_e_w))
    step_w = Forall(xv, Implies(In(xv, w), Forall(sv, Implies(Successor(sv, xv), In(sv, w)))))

    # omega_is_inductive: Ext, Inf |- Omega(w) -> Inductive(w)
    oii = omega_is_inductive()
    ext_ax = zfc.Extensionality()
    inf_ax = zfc.Infinity()
    got_ind = apply_thm(oii, [w], omega_w, ind_w,
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w))
    # got_ind: [ext_ax, inf_ax, omega_w] |- [Inductive(w)]

    # and_elim_left to get base_w
    got_base_w = apply_thm(and_elim_left(base_w, step_w, []), [], ind_w, base_w,
        Proof(Sequent([ind_w], [ind_w]), 'axiom', principal=ind_w))
    # Chain: ext, inf, omega |- base_w
    got = Proof(Sequent(got_ind.sequent.left, [base_w]), 'cut',
        [wr(got_ind, base_w), wl(got_base_w, *got_ind.sequent.left)], principal=ind_w)

    # Close: discharge omega, forall w
    proof = Proof(Sequent(got_ind.sequent.left[:2], [Implies(omega_w, base_w)]),
                  'implies_right', [got], principal=Implies(omega_w, base_w))
    fa = Forall(w, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=w, principal=fa)
    proof.name = 'omega_contains_empty'
    return proof



def omega_succ_closed():
    """Ext, Inf |- forall w. Omega(w) -> forall x. In(x,w) -> forall s. Succ(s,x) -> In(s,w)
    Omega is closed under successor."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor

    w, xv, sv, ev = Var(), Var(), Var(), Var()
    omega_w = Omega(w)
    ind_w = Inductive(w)

    base_w = Forall(ev, Implies(Empty(ev), In(ev, w)))
    step_w = Forall(xv, Implies(In(xv, w), Forall(sv, Implies(Successor(sv, xv), In(sv, w)))))

    oii = omega_is_inductive()
    got_ind = apply_thm(oii, [w], omega_w, ind_w,
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w))

    got_step_w = apply_thm(and_elim_right(base_w, step_w, []), [], ind_w, step_w,
        Proof(Sequent([ind_w], [ind_w]), 'axiom', principal=ind_w))
    got = Proof(Sequent(got_ind.sequent.left, [step_w]), 'cut',
        [wr(got_ind, step_w), wl(got_step_w, *got_ind.sequent.left)], principal=ind_w)

    proof = Proof(Sequent(got_ind.sequent.left[:2], [Implies(omega_w, step_w)]),
                  'implies_right', [got], principal=Implies(omega_w, step_w))
    fa = Forall(w, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=w, principal=fa)
    proof.name = 'omega_succ_closed'
    return proof



def omega_smallest_inductive():
    """Theorem 4.2.1: p sub omega and isInductive(p) implies p = omega.
    |- forall p, w. Omega(w) -> Subset(p,w) and Inductive(p) -> Eq(p,w)"""
    from tactics import apply_thm, wl, wr, mp

    p, w, zv, cv = Var(), Var(), Var(), Var()

    omega_w = Omega(w)
    sub_pw = Subset(p, w)
    ind_p = Inductive(p)
    hyps = [omega_w, sub_pw, ind_p]
    eq_pw = Eq(p, w)

    # === Forward: In(zv, p) -> In(zv, w) from Subset ===
    fwd_imp = Implies(In(zv, p), In(zv, w))
    fwd = Proof(Sequent([sub_pw], [fwd_imp]), 'forall_left',
                [Proof(Sequent([fwd_imp], [fwd_imp]), 'axiom', principal=fwd_imp)],
                principal=sub_pw, term=zv)

    # === Backward: In(zv, w) -> In(zv, p) ===
    # From Omega(w) with b=p: Inductive(p) -> forall x. x in w iff (x in p and ...)
    and_cond = And(In(zv, p), Forall(cv, Implies(Inductive(cv), In(zv, cv))))
    iff_zw = Iff(In(zv, w), and_cond)
    fa_iff = Forall(zv, iff_zw)
    imp_ind_fa = Implies(ind_p, fa_iff)

    # Instantiate Omega(w) with b=p
    ax_imp = Proof(Sequent([imp_ind_fa], [imp_ind_fa]), 'axiom', principal=imp_ind_fa)
    got_imp = Proof(Sequent([omega_w], [imp_ind_fa]), 'forall_left',
                    [ax_imp], principal=omega_w, term=p)
    # MP with ind_p: omega_w, ind_p |- fa_iff
    got_fa = mp(got_imp,
                Proof(Sequent([ind_p], [ind_p]), 'axiom', principal=ind_p),
                ind_p, fa_iff)
    # got_fa has fa_iff on right. Cut to instantiate with zv.
    fl_iff = Proof(Sequent([fa_iff], [iff_zw]), 'forall_left',
                   [Proof(Sequent([iff_zw], [iff_zw]), 'axiom', principal=iff_zw)],
                   principal=fa_iff, term=zv)
    got_iff = Proof(Sequent(got_fa.sequent.left, [iff_zw]), 'cut',
        [wr(got_fa, iff_zw), wl(fl_iff, *got_fa.sequent.left)], principal=fa_iff)
    # got_iff: [omega_w, ind_p] |- [iff_zw]

    # Extract forward of iff_zw: In(zv,w) -> and_cond
    iff_fwd = Implies(In(zv, w), and_cond)
    iff_bwd = Implies(and_cond, In(zv, w))
    H_iff = Implies(iff_fwd, Not(iff_bwd))
    e1 = Proof(Sequent([iff_zw, iff_fwd], [iff_fwd]), 'axiom', principal=iff_fwd)
    e2 = Proof(Sequent([iff_zw, iff_fwd], [Not(iff_bwd), iff_fwd]),
               'weakening_right', [e1], principal=Not(iff_bwd))
    e3 = Proof(Sequent([iff_zw], [H_iff, iff_fwd]), 'implies_right', [e2], principal=H_iff)
    e4 = Proof(Sequent([H_iff], [H_iff, iff_fwd]), 'weakening_right',
               [Proof(Sequent([H_iff], [H_iff]), 'axiom', principal=H_iff)], principal=iff_fwd)
    e5 = Proof(Sequent([H_iff, iff_zw], [iff_fwd]), 'not_left', [e4], principal=iff_zw)
    ext_fwd = Proof(Sequent([iff_zw], [iff_fwd]), 'cut', [e3, e5], principal=H_iff)

    # Chain: omega_w, ind_p |- In(zv,w) -> and_cond
    got_fwd = Proof(Sequent(got_iff.sequent.left, [iff_fwd]), 'cut',
        [wr(got_iff, iff_fwd), wl(ext_fwd, *got_iff.sequent.left)], principal=iff_zw)

    # From and_cond extract In(zv, p) (and_elim_left)
    ael = and_elim_left(In(zv, p), Forall(cv, Implies(Inductive(cv), In(zv, cv))), [])
    ax_and = Proof(Sequent([and_cond], [and_cond]), 'axiom', principal=and_cond)
    got_in_p = apply_thm(ael, [], and_cond, In(zv, p), ax_and)
    # got_in_p: [and_cond] |- [In(zv, p)]

    # Chain: omega_w, ind_p, In(zv,w) |- In(zv, p)
    got_and = mp(got_fwd,
                 Proof(Sequent([In(zv, w)], [In(zv, w)]), 'axiom', principal=In(zv, w)),
                 In(zv, w), and_cond)
    # got_and: [omega_w, ind_p, In(zv,w)] |- [and_cond]
    bwd_core = Proof(Sequent(got_and.sequent.left, [In(zv, p)]), 'cut',
        [wr(got_and, In(zv, p)), wl(got_in_p, *got_and.sequent.left)], principal=and_cond)
    # bwd_core: [omega_w, ind_p, In(zv,w)] |- [In(zv,p)]
    bwd = Proof(Sequent([omega_w, ind_p], [Implies(In(zv, w), In(zv, p))]),
                'implies_right', [bwd_core], principal=Implies(In(zv, w), In(zv, p)))

    # === Build Iff(In(zv, p), In(zv, w)) ===
    fwd_w = wl(fwd, omega_w, ind_p)
    bwd_w = wl(bwd, sub_pw)
    PA = Implies(In(zv, p), In(zv, w))
    AP = Implies(In(zv, w), In(zv, p))
    iff_pw = Iff(In(zv, p), In(zv, w))
    H_pw = Implies(PA, Not(AP))

    nr = Proof(Sequent(hyps + [Not(AP)], []), 'not_left', [bwd_w], principal=Not(AP))
    il = Proof(Sequent(hyps + [H_pw], []), 'implies_left', [fwd_w, nr], principal=H_pw)
    core = Proof(Sequent(hyps, [iff_pw]), 'not_right', [il], principal=iff_pw)

    # forall_right zv
    eq_body = Forall(zv, iff_pw)
    core_fa = Proof(Sequent(hyps, [eq_body]), 'forall_right', [core], principal=eq_body, term=zv)

    # === Close ===
    hyp_and = And(sub_pw, ind_p)
    ael2 = and_elim_left(sub_pw, ind_p, [])
    aer2 = and_elim_right(sub_pw, ind_p, [])
    ax_ha = Proof(Sequent([hyp_and], [hyp_and]), 'axiom', principal=hyp_and)
    got_sub = apply_thm(ael2, [], hyp_and, sub_pw, ax_ha)
    got_ind = apply_thm(aer2, [], hyp_and, ind_p,
                        Proof(Sequent([hyp_and], [hyp_and]), 'axiom', principal=hyp_and))

    core_w = wl(core_fa, hyp_and)
    cut_sub = Proof(Sequent([omega_w, ind_p, hyp_and], [eq_body]), 'cut',
        [wr(wl(got_sub, omega_w, ind_p), eq_body), core_w], principal=sub_pw)
    cut_ind = Proof(Sequent([omega_w, hyp_and], [eq_body]), 'cut',
        [wr(wl(got_ind, omega_w), eq_body), cut_sub], principal=ind_p)

    imp_and = Implies(hyp_and, eq_pw)
    s1 = Proof(Sequent([omega_w], [imp_and]), 'implies_right', [cut_ind], principal=imp_and)
    imp_omega = Implies(omega_w, imp_and)
    s2 = Proof(Sequent([], [imp_omega]), 'implies_right', [s1], principal=imp_omega)
    fw = Forall(w, imp_omega)
    s3 = Proof(Sequent([], [fw]), 'forall_right', [s2], principal=fw, term=w)
    fp = Forall(p, fw)
    s4 = Proof(Sequent([], [fp]), 'forall_right', [s3], principal=fp, term=p)
    s4.name = 'omega_smallest_inductive'
    return s4



def func_preserves_eq():
    """Extensionality |- forall f,x1,x2,y1,y2.
       Function(f) -> Eq(x1,x2) -> Apply(f,x1,y1) -> Apply(f,x2,y2) -> Eq(y1,y2)
    Functions map equal inputs to equal outputs."""
    from tactics import apply_thm, wl, wr, mp, eel, eir, fl, ax
    from definitions import Function as FuncDef, Apply, Singleton, PairSet, OrdPair
    from theorems.logic import eq_reflexive, eq_symmetric, and_intro
    from theorems.sets import ordpair_eq_transfer

    f, x1, x2, y1, y2 = Var(), Var(), Var(), Var(), Var()
    func_f = FuncDef(f)
    eq_x = Eq(x1, x2)
    app1 = Apply(f, x1, y1)
    app2 = Apply(f, x2, y2)
    goal = Eq(y1, y2)

    # Strategy: from Eq(x1,x2) + Apply(f,x2,y2), derive Apply(f,x1,y2)
    # using ordpair_eq_transfer to transform OrdPair(p,x2,y2) to OrdPair(p,x1,y2).
    # Then Function(f) + Apply(f,x1,y1) + Apply(f,x1,y2) -> Eq(y1,y2).

    p, qv = Var(), Var()

    # === Step 1: Eq(x2,x1) from eq_symmetric ===
    es = eq_symmetric()
    got_eq_sym = apply_thm(es, [x1, x2], eq_x, Eq(x2, x1), ax(eq_x))
    # got_eq_sym: [eq_x] |- Eq(x2, x1)

    # === Step 2: Eq(y2,y2) from eq_reflexive ===
    er = eq_reflexive()
    got_eq_refl = apply_thm(er, [y2], concl=Eq(y2, y2))
    # got_eq_refl: [] |- Eq(y2, y2)

    # === Step 3: Unpack Apply(f,x2,y2) -> OrdPair(p,x2,y2) + In(p,f) ===
    ordp_x2 = OrdPair(p, x2, y2)
    in_pf = In(p, f)
    and_ordp_in = And(ordp_x2, in_pf)

    got_ordp = apply_thm(and_elim_left(ordp_x2, in_pf, []), [], and_ordp_in, ordp_x2, ax(and_ordp_in))
    got_inf = apply_thm(and_elim_right(ordp_x2, in_pf, []), [], and_ordp_in, in_pf,
        Proof(Sequent([and_ordp_in], [and_ordp_in]), 'axiom', principal=and_ordp_in))

    # === Step 4: ordpair_eq_transfer: Eq(x2,x1) -> Eq(y2,y2) -> OrdPair(p,x2,y2) -> OrdPair(p,x1,y2) ===
    oet = ordpair_eq_transfer()
    ordp_x1 = OrdPair(p, x1, y2)
    got_ordp_x1 = apply_thm(oet, [x2, y2, x1, y2, p], Eq(x2, x1),
        Implies(Eq(y2, y2), Implies(ordp_x2, ordp_x1)), got_eq_sym)
    got_ordp_x1 = mp(got_ordp_x1, got_eq_refl, Eq(y2, y2), Implies(ordp_x2, ordp_x1))
    got_ordp_x1 = mp(got_ordp_x1, got_ordp, ordp_x2, ordp_x1)
    # got_ordp_x1: [eq_x, and_ordp_in] |- OrdPair(p, x1, y2)

    # === Step 5: Build And(OrdPair(p,x1,y2), In(p,f)) -> eir -> Apply(f,x1,y2) ===
    and_ordp_x1_in = And(ordp_x1, in_pf)
    ai = and_intro(ordp_x1, in_pf, [])
    got_and_x1 = mp(apply_thm(ai, [], ordp_x1, Implies(in_pf, and_ordp_x1_in), got_ordp_x1),
        got_inf, in_pf, and_ordp_x1_in)
    # got_and_x1: [eq_x, and_ordp_in] |- And(OrdPair(p,x1,y2), In(p,f))

    app_x1_y2 = Apply(f, x1, y2)
    got_app_x1 = eir(got_and_x1, And(OrdPair(qv, x1, y2), In(qv, f)), qv, p)
    # got_app_x1: [eq_x, and_ordp_in] |- Apply(f, x1, y2)

    # === Step 6: eel p from and_ordp_in, connect to Apply(f,x2,y2) ===
    got_app_from_and = eel(got_app_x1, and_ordp_in, p)
    # got_app_from_and: [eq_x, Exists(p, and_ordp_in)] |- Apply(f, x1, y2)
    # Exists(p, and_ordp_in) = Apply(f, x2, y2) (alpha-equiv)

    # === Step 7: func_unique_thm: Function(f) + Apply(f,x1,y1) + Apply(f,x1,y2) -> Eq(y1,y2) ===
    fu = func_unique_thm()
    got_eq = apply_thm(fu, [f, x1, y1, y2], func_f,
        Implies(app1, Implies(app_x1_y2, goal)), ax(func_f))
    got_eq = mp(got_eq, ax(app1), app1, Implies(app_x1_y2, goal))
    got_eq = mp(got_eq, got_app_from_and, app_x1_y2, goal)
    # got_eq: [func_f, app1, eq_x, Apply(f,x2,y2)] |- Eq(y1, y2)

    # === Close: discharge all, forall all ===
    proof = got_eq
    for h in [app2, app1, eq_x, func_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [f, y2, y1, x2, x1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'func_preserves_eq'
    return proof



def func_unique_thm():
    """|- forall f, x, y1, y2. Function(f) -> Apply(f,x,y1) -> Apply(f,x,y2) -> Eq(y1,y2)
    Basic function uniqueness: same input implies same output."""
    from tactics import apply_thm, wl, wr, mp, fl
    from definitions import Function as FuncDef, Apply

    f, x, y1, y2 = Var(), Var(), Var(), Var()
    func_f = FuncDef(f)
    app1 = Apply(f, x, y1)
    app2 = Apply(f, x, y2)
    eq_y = Eq(y1, y2)

    # Function(f) = And(Relation(f), single_valued). Extract single_valued.
    from definitions import Relation
    xv, ya, yb = Var(), Var(), Var()
    and_apps = And(app1, app2)
    imp = Implies(and_apps, eq_y)
    sv = Forall(xv, Forall(ya, Forall(yb,
        Implies(And(Apply(f, xv, ya), Apply(f, xv, yb)), Eq(ya, yb)))))
    rel_f = Relation(f)
    got_sv = apply_thm(and_elim_right(rel_f, sv, []), [], func_f, sv,
        Proof(Sequent([func_f], [func_f]), 'axiom', principal=func_f))
    # got_sv: [func_f] |- sv

    fa3 = Forall(yb, Implies(And(Apply(f, x, y1), Apply(f, x, yb)), Eq(y1, yb)))
    fa2 = Forall(ya, Forall(yb, Implies(And(Apply(f, x, ya), Apply(f, x, yb)), Eq(ya, yb))))


    # Peel 3 foralls from sv
    fl1 = fl(sv, fa2, x)
    fl2 = Proof(Sequent([sv], [fa3]), 'cut',
        [wr(fl1, fa3), wl(fl(fa2, fa3, y1), sv)], principal=fa2)
    fl3 = Proof(Sequent([sv], [imp]), 'cut',
        [wr(fl2, imp), wl(fl(fa3, imp, y2), sv)], principal=fa3)
    # Chain: func_f |- sv |- imp
    fl3 = Proof(Sequent([func_f], [imp]), 'cut',
        [wr(got_sv, imp), wl(fl3, func_f)], principal=sv)
    # fl3: [func_f] |- [And(app1,app2) -> Eq(y1,y2)]

    # Build And(app1, app2)
    n_app2 = Not(app2)
    br1 = wr(Proof(Sequent([app1], [app1]), 'axiom', principal=app1), eq_y)
    br2 = Proof(Sequent([app2, n_app2], []), 'not_left',
               [Proof(Sequent([app2], [app2]), 'axiom', principal=app2)], principal=n_app2)

    # br1 needs right = [app1] not [app1, eq_y]. For implies_left:
    # Branch 1: G |- app1, D (D = conclusion.right = [])
    # So branch 1 should be: [app1, app2] |- [app1]
    br1_fix = wl(Proof(Sequent([app1], [app1]), 'axiom', principal=app1), app2)
    il = Proof(Sequent([app1, app2, Implies(app1, n_app2)], []),
               'implies_left', [br1_fix, wl(br2, app1)], principal=Implies(app1, n_app2))
    got_and = Proof(Sequent([app1, app2], [and_apps]), 'not_right', [il], principal=and_apps)

    # MP: imp, and_apps |- eq_y
    ax_eq = Proof(Sequent([eq_y], [eq_y]), 'axiom', principal=eq_y)
    ax_and = wr(got_and, eq_y)
    il_mp = Proof(Sequent([app1, app2, imp], [eq_y]),
                  'implies_left', [ax_and, wl(ax_eq, app1, app2)], principal=imp)
    # Cut on imp: fl3 gives [fa1] |- [imp], il_mp gives [app1, app2, imp] |- [eq_y]
    got_eq = Proof(Sequent([func_f, app1, app2], [eq_y]), 'cut',
        [wr(wl(fl3, app1, app2), eq_y), wl(il_mp, func_f)], principal=imp)

    # Discharge and close
    proof = got_eq
    for h in [app2, app1, func_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [y2, y1, x, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'func_unique'
    return proof




def omega_exists():
    """Omega exists: construct the smallest inductive set from Infinity + Separation.
    Ext, Inf, Sep |- exists w. Omega(w)
    From infinity_gives_inductive: exists b. Inductive(b).
    Separation on b with phi(x) = forall c. Inductive(c) -> x in c.
    The result satisfies Omega."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import iff_intro, iff_mp, iff_mp_rev, and_intro, and_elim_left, and_elim_right
    from theorems.axioms import separation

    bv = Var()   # the inductive set from Infinity
    wv = Var()   # omega (the separation result)
    xv = Var()   # element variable
    cv = Var()   # inductive set variable (in Omega's forall)

    ind_b = Inductive(bv)
    omega_wv = Omega(wv)

    # phi(x) = forall c. Inductive(c) -> x in c
    def phi(x):
        return Forall(cv, Implies(Inductive(cv), In(x, cv)))

    # Separation: forall bv. exists wv. forall xv. xv in wv iff (xv in bv and phi(xv))
    sep = separation(phi, [])
    from core.proof import _expand
    # Peel forall a_set = bv:
    got_sep = sep
    actual = got_sep.sequent.right[0]
    char_wv_body = Iff(In(xv, wv), And(In(xv, bv), phi(xv)))
    char_wv = Forall(xv, char_wv_body)
    ex_wv = Exists(wv, char_wv)
    got_sep = Proof(Sequent(got_sep.sequent.left, [ex_wv]), 'cut',
        [wr(got_sep, ex_wv), wl(fl(actual, ex_wv, bv), *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(wv, char_wv)

    # === Verify Omega(wv) from char_wv and Inductive(bv) ===
    # Omega(wv) = forall b'. Inductive(b') -> forall x. x in wv iff (x in b' and forall c. Ind(c) -> x in c)
    # From char_wv: x in wv iff (x in bv and phi(x)) where phi(x) = forall c. Ind(c) -> x in c.
    # For any Inductive(b'):
    #   Forward: x in wv -> (x in bv and phi(x)) -> phi(x) -> Ind(b') -> x in b'. So x in b'.
    #            And phi(x) is already there. So x in b' and phi(x). ✓
    #   Backward: x in b' and phi(x) -> phi(x) -> Ind(bv) -> x in bv. And phi(x). So x in bv and phi(x) -> x in wv. ✓

    bpv = Var()  # b' in Omega's forall
    ind_bp = Inductive(bpv)

    # char_wv at xv: In(xv,wv) iff And(In(xv,bv), phi(xv))
    got_char = fl(char_wv, char_wv_body, xv)
    and_in_phi = And(In(xv, bv), phi(xv))

    # --- Forward: In(xv, wv) -> And(In(xv, bpv), phi(xv)) ---
    # In(xv,wv) -> And(In(xv,bv), phi(xv)) from char_wv
    got_fwd_char = mp(iff_mp(In(xv, wv), and_in_phi, []),
        got_char, char_wv_body, Implies(In(xv, wv), and_in_phi))
    got_and = mp(got_fwd_char, ax(In(xv, wv)), In(xv, wv), and_in_phi)
    # [char_wv, In(xv,wv)] |- And(In(xv,bv), phi(xv))
    got_phi = apply_thm(and_elim_right(In(xv, bv), phi(xv), []), [],
        and_in_phi, phi(xv), got_and)
    # [char_wv, In(xv,wv)] |- phi(xv) = forall c. Ind(c) -> x in c
    # Instantiate at bpv: Ind(bpv) -> In(xv, bpv)
    got_in_bp = apply_thm(got_phi, [bpv], ind_bp, In(xv, bpv), ax(ind_bp))
    # [char_wv, In(xv,wv), Ind(bpv)] |- In(xv, bpv)
    # And(In(xv, bpv), phi(xv)):
    all_fwd = list(got_in_bp.sequent.left)
    for f_ in got_phi.sequent.left:
        if not any(same(f_, g) for g in all_fwd):
            all_fwd.append(f_)
    omega_and = And(In(xv, bpv), phi(xv))
    got_fwd = mp(apply_thm(and_intro(In(xv, bpv), phi(xv), []), [], In(xv, bpv),
        Implies(phi(xv), omega_and), weaken_to(got_in_bp, all_fwd)),
        weaken_to(got_phi, all_fwd), phi(xv), omega_and)
    # [char_wv, In(xv,wv), Ind(bpv)] |- And(In(xv,bpv), phi(xv))

    # --- Backward: And(In(xv, bpv), phi(xv)) -> In(xv, wv) ---
    # From phi(xv) and Inductive(bv): In(xv, bv).
    # From In(xv, bv) and phi(xv): And(...) -> In(xv, wv) via char_wv backward.
    got_phi_bwd = apply_thm(and_elim_right(In(xv, bpv), phi(xv), []), [],
        omega_and, phi(xv), ax(omega_and))
    got_in_bv_from_phi = apply_thm(got_phi_bwd, [bv], ind_b, In(xv, bv), ax(ind_b))
    # [omega_and, Ind(bv)] |- In(xv, bv)
    and_bv_phi = And(In(xv, bv), phi(xv))
    all_bwd = list(got_in_bv_from_phi.sequent.left)
    for f_ in got_phi_bwd.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_and_bv = mp(apply_thm(and_intro(In(xv, bv), phi(xv), []), [], In(xv, bv),
        Implies(phi(xv), and_bv_phi), weaken_to(got_in_bv_from_phi, all_bwd)),
        weaken_to(got_phi_bwd, all_bwd), phi(xv), and_bv_phi)
    # [omega_and, Ind(bv)] |- And(In(xv,bv), phi(xv))
    got_bwd_char = mp(iff_mp_rev(In(xv, wv), and_bv_phi, []),
        got_char, char_wv_body, Implies(and_bv_phi, In(xv, wv)))
    all_bwd2 = list(got_and_bv.sequent.left)
    for f_ in got_bwd_char.sequent.left:
        if not any(same(f_, g) for g in all_bwd2):
            all_bwd2.append(f_)
    got_bwd = mp(weaken_to(got_bwd_char, all_bwd2), got_and_bv, and_bv_phi, In(xv, wv))
    # [omega_and, Ind(bv), char_wv] |- In(xv, wv)

    # --- Build Iff(In(xv, wv), omega_and) ---
    imp_fwd = Implies(In(xv, wv), omega_and)
    imp_bwd = Implies(omega_and, In(xv, wv))
    rem_fwd = [f_ for f_ in got_fwd.sequent.left if not same(f_, In(xv, wv))]
    got_imp_fwd = Proof(Sequent(rem_fwd, [imp_fwd]), 'implies_right', [got_fwd], principal=imp_fwd)
    rem_bwd = [f_ for f_ in got_bwd.sequent.left if not same(f_, omega_and)]
    got_imp_bwd = Proof(Sequent(rem_bwd, [imp_bwd]), 'implies_right', [got_bwd], principal=imp_bwd)

    iff_omega = Iff(In(xv, wv), omega_and)
    ii = iff_intro(In(xv, wv), omega_and, [])
    all_iff = list(got_imp_fwd.sequent.left)
    for f_ in got_imp_bwd.sequent.left:
        if not any(same(f_, g) for g in all_iff):
            all_iff.append(f_)
    got_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_bwd, iff_omega),
        weaken_to(got_imp_fwd, all_iff)),
        weaken_to(got_imp_bwd, all_iff), imp_bwd, iff_omega)

    # forall xv, implies_right Ind(bpv), forall bpv -> Omega(wv)
    fa_x = Forall(xv, iff_omega)
    got_fa_x = Proof(Sequent(got_iff.sequent.left, [fa_x]), 'forall_right',
        [got_iff], principal=fa_x, term=xv)
    imp_ind = Implies(ind_bp, fa_x)
    rem_ind = [f_ for f_ in got_fa_x.sequent.left if not same(f_, ind_bp)]
    got_imp_ind = Proof(Sequent(rem_ind, [imp_ind]), 'implies_right',
        [got_fa_x], principal=imp_ind)
    got_omega = Proof(Sequent(rem_ind, [omega_wv]), 'forall_right',
        [got_imp_ind], principal=omega_wv, term=bpv)
    # got_omega: [char_wv, Ind(bv), Sep] |- Omega(wv)

    # === Package: eir wv, eel wv from char_wv, cut with got_sep ===
    got_ex_omega = eir(got_omega, Omega(wv), wv, wv)
    # eel wv from char_wv:
    got_ex_omega = eel(got_ex_omega, char_wv, wv)
    # cut Exists(wv, char_wv) with got_sep:
    got_ex_omega = cut(got_ex_omega, got_ex_omega.sequent.left[-1], got_sep)

    # === eel bv from Ind(bv), cut with infinity_gives_inductive ===
    got_ex_omega = eel(got_ex_omega, ind_b, bv)
    # Exists(bv, Ind(bv)) on left. Cut with infinity_gives_inductive:
    igi = infinity_gives_inductive()
    got_ex_omega = cut(got_ex_omega, got_ex_omega.sequent.left[-1], igi)

    # Replace expanded Infinity (Exists form) with the Infinity() axiom object
    inf_ax = zfc.Infinity()
    expanded_inf = None
    for f in got_ex_omega.sequent.left:
        if not isinstance(f, zfc.ZFCAxiom) and same(f, inf_ax):
            expanded_inf = f
            break
    if expanded_inf is not None:
        inf_proof = Proof(Sequent([inf_ax], [expanded_inf]), 'axiom', principal=inf_ax)
        got_ex_omega = cut(got_ex_omega, expanded_inf, inf_proof)

    got_ex_omega.name = 'omega_exists'
    return got_ex_omega
