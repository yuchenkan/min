"""Theorems: arithmetic module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from definitions import Empty, OrdPair, Omega, Num

from theorems.logic import (iff_mp, iff_mp_rev, iff_intro, and_intro,
    and_elim_left, and_elim_right, eq_reflexive, eq_substitution)
from theorems.sets import (kuratowski, ordpair_exists, unique_successor,
    eq_successor_transfer)
from theorems.recursion import succ_func_exists


def _tuple_inject(ku, er, a, b, c, d, q, ordp_q, ordp_q_cd, q2):
    """Kuratowski pair injection: from OrdPair(q,a,b) and OrdPair(q,c,d), derive And(Eq(a,c), Eq(b,d)).
    Uses fl+cut to avoid leaving Forall(q2,...) on any premise right side."""
    from tactics import apply_thm, fl, wl, mp, ax, cut
    fa_inner = Forall(q2, Implies(OrdPair(q2, c, d), Implies(Eq(q, q2),
        And(Eq(a, c), Eq(b, d)))))
    got_ti = apply_thm(ku, [a, b, c, d, q], ordp_q, fa_inner, ax(ordp_q))
    imp_inst = Implies(ordp_q_cd, Implies(Eq(q, q), And(Eq(a, c), Eq(b, d))))
    got_fl = fl(fa_inner, imp_inst, q)
    got_fl = wl(got_fl, *[f for f in got_ti.sequent.left if not same(f, fa_inner)])
    got_ti = cut(got_fl, fa_inner, got_ti)
    got_ti = mp(got_ti, ax(ordp_q_cd), ordp_q_cd, Implies(Eq(q, q), And(Eq(a, c), Eq(b, d))))
    got_eq_qq = apply_thm(er, [q], concl=Eq(q, q))
    return mp(got_ti, got_eq_qq, Eq(q, q), And(Eq(a, c), Eq(b, d)))


def sf_props():
    """Successor function exists with succ_char, Function, and dom_sub.
    Rep, Ext, Pairing |- forall w.
      exists sf. succ_char(sf, w) /\\ Function(sf) /\\ dom_sub(sf, w)
    where succ_char(sf, w) = forall x. In(x,w) -> forall y. Iff(Apply(sf,x,y), Successor(y,x))
    and dom_sub(sf, w) = forall x. (exists y. Apply(sf,x,y)) -> In(x,w)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Relation as RelDef,
        Successor as SuccDef)

    w = Var(postfix='w')
    sfv = Var(postfix='sf')

    # === sf_char from succ_func_exists ===
    sfe = succ_func_exists()
    pv = Var()
    xsf, ssf = Var(), Var()
    sf_body = Iff(In(pv, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(pv, xsf, ssf))))))
    sf_char = Forall(pv, sf_body)
    got_sfe = apply_thm(sfe, [w], concl=Exists(sfv, sf_char))

    # === succ_char from sf_char ===
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    app_sf = Apply(sfv, xsc, ysc)
    succ_yx = SuccDef(ysc, xsc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf, succ_yx))))

    # -- Forward: [sf_char, Apply(sf,x,y)] |- Succ(y,x) --
    qv = Var(postfix='qf')
    ordp_q = OrdPair(qv, xsc, ysc)
    in_q_sf = In(qv, sfv)
    and_oq_iq = And(ordp_q, in_q_sf)
    ex_xsf = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qv, xsf, ssf)))))
    sf_inst = Iff(In(qv, sfv), ex_xsf)
    got_sf_fwd = mp(iff_mp(In(qv, sfv), ex_xsf, []),
        fl(sf_char, sf_inst, qv), sf_inst, Implies(In(qv, sfv), ex_xsf))
    got_ex_xsf = mp(got_sf_fwd, ax(in_q_sf), in_q_sf, ex_xsf)

    ordp_q_xs = OrdPair(qv, xsf, ssf)
    succ_sx = SuccDef(ssf, xsf)
    qv2 = Var(postfix='q2')
    ku = kuratowski()
    er = eq_reflexive()
    got_ti = _tuple_inject(ku, er, xsc, ysc, xsf, ssf, qv, ordp_q, ordp_q_xs, qv2)

    got_eq_ys = apply_thm(and_elim_right(Eq(xsc, xsf), Eq(ysc, ssf), []), [],
        And(Eq(xsc, xsf), Eq(ysc, ssf)), Eq(ysc, ssf), got_ti)
    got_eq_xs = apply_thm(and_elim_left(Eq(xsc, xsf), Eq(ysc, ssf), []), [],
        And(Eq(xsc, xsf), Eq(ysc, ssf)), Eq(xsc, xsf), got_ti)

    est = eq_successor_transfer()
    got_succ = apply_thm(est, [ysc, xsc, ssf, xsf], Eq(ysc, ssf),
        Implies(Eq(xsc, xsf), Implies(succ_sx, succ_yx)), got_eq_ys)
    got_succ = mp(got_succ, got_eq_xs, Eq(xsc, xsf), Implies(succ_sx, succ_yx))
    got_succ = mp(got_succ, ax(succ_sx), succ_sx, succ_yx)

    # Close existentials back to Apply on left:
    and_succ_ordp = And(succ_sx, ordp_q_xs)
    cur_fwd = got_succ
    for (pred, gp) in [
        (succ_sx, apply_thm(and_elim_left(succ_sx, ordp_q_xs, []), [], and_succ_ordp, succ_sx, ax(and_succ_ordp))),
        (ordp_q_xs, apply_thm(and_elim_right(succ_sx, ordp_q_xs, []), [], and_succ_ordp, ordp_q_xs, ax(and_succ_ordp)))]:
        if any(same(pred, g) for g in cur_fwd.sequent.left):
            cur_fwd = cut(cur_fwd, pred, gp)
    cur_fwd = eel(cur_fwd, and_succ_ordp, ssf)
    in_xsf_w = In(xsf, w)
    and_in_ex = And(in_xsf_w, Exists(ssf, and_succ_ordp))
    cur_fwd = cut(cur_fwd, cur_fwd.sequent.left[-1],
        apply_thm(and_elim_right(in_xsf_w, Exists(ssf, and_succ_ordp), []), [],
            and_in_ex, Exists(ssf, and_succ_ordp), ax(and_in_ex)))
    cur_fwd = eel(cur_fwd, and_in_ex, xsf)
    cur_fwd = cut(cur_fwd, cur_fwd.sequent.left[-1], got_ex_xsf)
    for (pred, gp) in [
        (ordp_q, apply_thm(and_elim_left(ordp_q, in_q_sf, []), [], and_oq_iq, ordp_q, ax(and_oq_iq))),
        (in_q_sf, apply_thm(and_elim_right(ordp_q, in_q_sf, []), [], and_oq_iq, in_q_sf, ax(and_oq_iq)))]:
        if any(same(pred, g) for g in cur_fwd.sequent.left):
            cur_fwd = cut(cur_fwd, pred, gp)
    cur_fwd = eel(cur_fwd, and_oq_iq, qv)
    # cur_fwd: [sf_char, Apply(sf,xsc,ysc)] |- Succ(ysc,xsc)

    # -- Backward: [sf_char, In(xsc,w), Succ(ysc,xsc), Pairing] |- Apply(sf,xsc,ysc) --
    oe = ordpair_exists()
    qb = Var(postfix='qb')
    ordp_qb = OrdPair(qb, xsc, ysc)
    got_qb = apply_thm(oe, [xsc, ysc], concl=Exists(qb, ordp_qb))

    sf_inst_qb = Iff(In(qb, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf))))))
    ex_xsf_qb = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf)))))
    got_sf_bwd = mp(iff_mp_rev(In(qb, sfv), ex_xsf_qb, []),
        fl(sf_char, sf_inst_qb, qb), sf_inst_qb, Implies(ex_xsf_qb, In(qb, sfv)))

    in_xsc_w = In(xsc, w)
    and_so_b = And(succ_yx, ordp_qb)
    got_so_b = mp(apply_thm(and_intro(succ_yx, ordp_qb, []), [], succ_yx,
        Implies(ordp_qb, and_so_b), ax(succ_yx)), ax(ordp_qb), ordp_qb, and_so_b)
    got_ex_ssf_b = eir(got_so_b, And(SuccDef(ssf, xsc), OrdPair(qb, xsc, ssf)), ssf, ysc)
    ex_ssf_b_right = got_ex_ssf_b.sequent.right[0]
    and_in_ex_b = And(in_xsc_w, ex_ssf_b_right)
    got_ie_b = mp(apply_thm(and_intro(in_xsc_w, ex_ssf_b_right, []), [],
        in_xsc_w, Implies(ex_ssf_b_right, and_in_ex_b), ax(in_xsc_w)),
        got_ex_ssf_b, ex_ssf_b_right, and_in_ex_b)
    got_ex_xsf_b = eir(got_ie_b,
        And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf)))), xsf, xsc)

    all_bwd = list(got_ex_xsf_b.sequent.left)
    for f_ in got_sf_bwd.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_qb = mp(weaken_to(got_sf_bwd, all_bwd),
        weaken_to(got_ex_xsf_b, all_bwd), ex_xsf_qb, In(qb, sfv))

    pv_app = Var()
    got_and_bwd = mp(apply_thm(and_intro(ordp_qb, In(qb, sfv), []), [], ordp_qb,
        Implies(In(qb, sfv), And(ordp_qb, In(qb, sfv))), ax(ordp_qb)),
        got_in_qb, In(qb, sfv), And(ordp_qb, In(qb, sfv)))
    got_app_bwd = eir(got_and_bwd, And(OrdPair(pv_app, xsc, ysc), In(pv_app, sfv)), pv_app, qb)
    cur_bwd = eel(got_app_bwd, ordp_qb, qb)
    cur_bwd = cut(cur_bwd, cur_bwd.sequent.left[-1], got_qb)
    # cur_bwd: [sf_char, In(xsc,w), Succ(ysc,xsc), Pairing] |- Apply(sf,xsc,ysc)

    # -- Build Iff, close into succ_char --
    imp_fwd = Implies(app_sf, succ_yx)
    rem_f = [f_ for f_ in cur_fwd.sequent.left if not same(f_, app_sf)]
    got_if = Proof(Sequent(rem_f, [imp_fwd]), 'implies_right', [cur_fwd], principal=imp_fwd)
    imp_bwd = Implies(succ_yx, app_sf)
    rem_b = [f_ for f_ in cur_bwd.sequent.left if not same(f_, succ_yx)]
    got_ib = Proof(Sequent(rem_b, [imp_bwd]), 'implies_right', [cur_bwd], principal=imp_bwd)

    iff_sc = Iff(app_sf, succ_yx)
    ii = iff_intro(app_sf, succ_yx, [])
    all_sc = list(got_if.sequent.left)
    for f_ in got_ib.sequent.left:
        if not any(same(f_, g) for g in all_sc):
            all_sc.append(f_)
    got_iff_sc = mp(apply_thm(ii, [], imp_fwd, Implies(imp_bwd, iff_sc),
        weaken_to(got_if, all_sc)), weaken_to(got_ib, all_sc), imp_bwd, iff_sc)

    fa_y = Forall(ysc, iff_sc)
    got_fa = Proof(Sequent(got_iff_sc.sequent.left, [fa_y]), 'forall_right',
        [got_iff_sc], principal=fa_y, term=ysc)
    imp_in = Implies(In(xsc, w), fa_y)
    rem_in = [f_ for f_ in got_fa.sequent.left if not same(f_, In(xsc, w))]
    got_imp_in = Proof(Sequent(rem_in, [imp_in]), 'implies_right', [got_fa], principal=imp_in)
    got_succ_char = Proof(Sequent(rem_in, [succ_char]), 'forall_right',
        [got_imp_in], principal=succ_char, term=xsc)

    # === Relation(sf) from sf_char ===
    rel_sf = RelDef(sfv)
    zrel = Var()
    xrel, yrel = Var(), Var()
    sf_inst_z = Iff(In(zrel, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(zrel, xsf, ssf))))))
    ex_z = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(zrel, xsf, ssf)))))
    got_z_fwd = mp(iff_mp(In(zrel, sfv), ex_z, []),
        fl(sf_char, sf_inst_z, zrel), sf_inst_z, Implies(In(zrel, sfv), ex_z))
    got_z_ex = mp(got_z_fwd, ax(In(zrel, sfv)), In(zrel, sfv), ex_z)

    ordp_z_xs = OrdPair(zrel, xsf, ssf)
    ex_xy_ordp = Exists(xrel, Exists(yrel, OrdPair(zrel, xrel, yrel)))
    got_exy = eir(eir(ax(ordp_z_xs), OrdPair(zrel, xsf, yrel), yrel, ssf),
        Exists(yrel, OrdPair(zrel, xrel, yrel)), xrel, xsf)

    and_s_o_z = And(SuccDef(ssf, xsf), ordp_z_xs)
    cur_rel = cut(got_exy, ordp_z_xs,
        apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_z_xs, []), [], and_s_o_z, ordp_z_xs, ax(and_s_o_z)))
    cur_rel = eel(cur_rel, and_s_o_z, ssf)
    and_in_ex_z = And(In(xsf, w), Exists(ssf, and_s_o_z))
    cur_rel = cut(cur_rel, cur_rel.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_z), []), [],
            and_in_ex_z, Exists(ssf, and_s_o_z), ax(and_in_ex_z)))
    cur_rel = eel(cur_rel, and_in_ex_z, xsf)
    cur_rel = cut(cur_rel, cur_rel.sequent.left[-1], got_z_ex)

    imp_rel = Implies(In(zrel, sfv), ex_xy_ordp)
    rem_r = [f_ for f_ in cur_rel.sequent.left if not same(f_, In(zrel, sfv))]
    got_rel = Proof(Sequent(rem_r, [rel_sf]), 'forall_right',
        [Proof(Sequent(rem_r, [imp_rel]), 'implies_right', [cur_rel], principal=imp_rel)],
        principal=rel_sf, term=zrel)

    # === Single-valued from succ_char + unique_successor ===
    xsv, y1sv, y2sv = Var(), Var(), Var()
    app1 = Apply(sfv, xsv, y1sv)
    app2 = Apply(sfv, xsv, y2sv)
    and_apps = And(app1, app2)

    # In(xsv,w) from app1 via sf_char + pair_injection + eq_substitution:
    q_dm = Var(postfix='qdm')
    ordp_dm = OrdPair(q_dm, xsv, y1sv)
    in_dm_sf = In(q_dm, sfv)
    sf_inst_dm = Iff(In(q_dm, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_dm, xsf, ssf))))))
    ex_dm = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_dm, xsf, ssf)))))
    got_dm_fwd = mp(iff_mp(In(q_dm, sfv), ex_dm, []),
        fl(sf_char, sf_inst_dm, q_dm), sf_inst_dm, Implies(In(q_dm, sfv), ex_dm))
    got_dm_ex = mp(got_dm_fwd, ax(in_dm_sf), in_dm_sf, ex_dm)

    ordp_dm_xs = OrdPair(q_dm, xsf, ssf)
    got_ti_dm = _tuple_inject(ku, er, xsv, y1sv, xsf, ssf, q_dm, ordp_dm, ordp_dm_xs, qv2)
    got_eq_xv = apply_thm(and_elim_left(Eq(xsv, xsf), Eq(y1sv, ssf), []), [],
        And(Eq(xsv, xsf), Eq(y1sv, ssf)), Eq(xsv, xsf), got_ti_dm)

    esub = eq_substitution()
    got_iff_xw = apply_thm(esub, [xsv, xsf, w], Eq(xsv, xsf),
        Iff(In(xsv, w), In(xsf, w)), got_eq_xv)
    got_in_xsv = mp(mp(iff_mp_rev(In(xsv, w), In(xsf, w), []),
        got_iff_xw, Iff(In(xsv, w), In(xsf, w)), Implies(In(xsf, w), In(xsv, w))),
        ax(In(xsf, w)), In(xsf, w), In(xsv, w))

    # Fold back existentials:
    cur_dm = got_in_xsv
    and_s_o_dm = And(SuccDef(ssf, xsf), ordp_dm_xs)
    and_in_ex_dm = And(In(xsf, w), Exists(ssf, and_s_o_dm))
    for (pred, gp) in [
        (ordp_dm_xs, apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_dm_xs, []), [], and_s_o_dm, ordp_dm_xs, ax(and_s_o_dm))),
        (In(xsf, w), apply_thm(and_elim_left(In(xsf, w), Exists(ssf, and_s_o_dm), []), [], and_in_ex_dm, In(xsf, w), ax(and_in_ex_dm)))]:
        if any(same(pred, g) for g in cur_dm.sequent.left):
            cur_dm = cut(cur_dm, pred, gp)
    cur_dm = eel(cur_dm, and_s_o_dm, ssf)
    cur_dm = cut(cur_dm, cur_dm.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_dm), []), [],
            and_in_ex_dm, Exists(ssf, and_s_o_dm), ax(and_in_ex_dm)))
    cur_dm = eel(cur_dm, and_in_ex_dm, xsf)
    cur_dm = cut(cur_dm, cur_dm.sequent.left[-1], got_dm_ex)
    and_dm = And(ordp_dm, in_dm_sf)
    for (pred, gp) in [
        (ordp_dm, apply_thm(and_elim_left(ordp_dm, in_dm_sf, []), [], and_dm, ordp_dm, ax(and_dm))),
        (in_dm_sf, apply_thm(and_elim_right(ordp_dm, in_dm_sf, []), [], and_dm, in_dm_sf, ax(and_dm)))]:
        if any(same(pred, g) for g in cur_dm.sequent.left):
            cur_dm = cut(cur_dm, pred, gp)
    cur_dm = eel(cur_dm, and_dm, q_dm)
    cur_dm = cut(cur_dm, app1, apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)))
    # cur_dm: [sf_char, And(app1,app2), Ext] |- In(xsv,w)

    # === dom_sub_sf: forall x. (exists y. Apply(sf,x,y)) -> In(x,w) ===
    # Build from cur_dm by replacing And(app1,app2) with app1, then eel y1sv, close forall xsv
    yd_sf = Var()
    cur_dom = cut(cur_dm, and_apps,
        apply_thm(and_intro(app1, app2, []), [], app1, Implies(app2, and_apps), ax(app1)))
    # cur_dom has [sf_char, app1, app2, Ext] on left, but we added app2 unnecessarily
    # Simpler: go back to got_in_xsv before the And(app1,app2) cut:
    # Actually cur_dm was built from got_in_xsv with existential folding + cut with And.
    # The And is there because the single-valued section needed both apps.
    # For dom_sub, I just need one Apply. Let me rebuild from got_in_xsv:
    # got_in_xsv at line 236 has [ordp_dm, ordp_dm_xs, In(xsf,w), Ext] |- In(xsv,w)
    # After folding: [sf_char, app1, Ext] |- In(xsv,w)
    # (the folding removes ordp_dm, ordp_dm_xs, In(xsf,w) and replaces with sf_char + app1)
    # I already did this folding in cur_dm, but then also cut with And(app1,app2).
    # The cut at line 260 replaced app1 with And(app1,app2) via and_elim_left.
    # For dom_sub, I need the version BEFORE that cut. That's cur_dm before line 260.
    # But cur_dm was already modified. I need to redo the folding without the And cut.
    # Or: just derive app1 back from And(app1,app2) and rebuild.
    # Simplest: from cur_dm [sf_char, And(app1,app2), Ext] |- In(xsv,w),
    # weaken with app1 and cut And(app1,app2) using and_intro:
    # Actually this is circular. Let me just eel y1sv from app1 to get dom_sub directly.
    # cur_dm has And(app1,app2) on left. I want app1 instead.
    # From [app1] |- And(app1,app2) requires app2 which I don't have.
    # Better: go back to before cut at line 260 and save a copy.
    # This is getting messy. Let me just build dom_sub from scratch using the same pattern.
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    app_ds = Apply(sfv, xds, yds)
    q_ds = Var(postfix='qds')
    ordp_ds = OrdPair(q_ds, xds, yds)
    in_ds_sf = In(q_ds, sfv)
    sf_inst_ds = Iff(In(q_ds, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_ds, xsf, ssf))))))
    ex_ds = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_ds, xsf, ssf)))))
    got_ds_fwd = mp(iff_mp(In(q_ds, sfv), ex_ds, []),
        fl(sf_char, sf_inst_ds, q_ds), sf_inst_ds, Implies(In(q_ds, sfv), ex_ds))
    got_ds_ex = mp(got_ds_fwd, ax(in_ds_sf), in_ds_sf, ex_ds)
    ordp_ds_xs = OrdPair(q_ds, xsf, ssf)
    got_ti_ds = _tuple_inject(ku, er, xds, yds, xsf, ssf, q_ds, ordp_ds, ordp_ds_xs, qv2)
    got_eq_xds = apply_thm(and_elim_left(Eq(xds, xsf), Eq(yds, ssf), []), [],
        And(Eq(xds, xsf), Eq(yds, ssf)), Eq(xds, xsf), got_ti_ds)
    got_iff_xds = apply_thm(esub, [xds, xsf, w], Eq(xds, xsf),
        Iff(In(xds, w), In(xsf, w)), got_eq_xds)
    got_in_xds = mp(mp(iff_mp_rev(In(xds, w), In(xsf, w), []),
        got_iff_xds, Iff(In(xds, w), In(xsf, w)), Implies(In(xsf, w), In(xds, w))),
        ax(In(xsf, w)), In(xsf, w), In(xds, w))
    # Fold existentials:
    cur_ds = got_in_xds
    and_s_o_ds = And(SuccDef(ssf, xsf), ordp_ds_xs)
    and_in_ex_ds = And(In(xsf, w), Exists(ssf, and_s_o_ds))
    for (pred, gp) in [
        (ordp_ds_xs, apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_ds_xs, []), [], and_s_o_ds, ordp_ds_xs, ax(and_s_o_ds))),
        (In(xsf, w), apply_thm(and_elim_left(In(xsf, w), Exists(ssf, and_s_o_ds), []), [], and_in_ex_ds, In(xsf, w), ax(and_in_ex_ds)))]:
        if any(same(pred, g) for g in cur_ds.sequent.left):
            cur_ds = cut(cur_ds, pred, gp)
    cur_ds = eel(cur_ds, and_s_o_ds, ssf)
    cur_ds = cut(cur_ds, cur_ds.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_ds), []), [],
            and_in_ex_ds, Exists(ssf, and_s_o_ds), ax(and_in_ex_ds)))
    cur_ds = eel(cur_ds, and_in_ex_ds, xsf)
    cur_ds = cut(cur_ds, cur_ds.sequent.left[-1], got_ds_ex)
    and_ds = And(ordp_ds, in_ds_sf)
    for (pred, gp) in [
        (ordp_ds, apply_thm(and_elim_left(ordp_ds, in_ds_sf, []), [], and_ds, ordp_ds, ax(and_ds))),
        (in_ds_sf, apply_thm(and_elim_right(ordp_ds, in_ds_sf, []), [], and_ds, in_ds_sf, ax(and_ds)))]:
        if any(same(pred, g) for g in cur_ds.sequent.left):
            cur_ds = cut(cur_ds, pred, gp)
    cur_ds = eel(cur_ds, and_ds, q_ds)
    # cur_ds: [sf_char, Apply(sf,xds,yds), Ext] |- In(xds,w)
    # eel yds, close:
    cur_ds = eel(cur_ds, app_ds, yds)
    ex_y_app_ds = cur_ds.sequent.left[-1]  # Exists(yds, Apply(sf,xds,yds))
    imp_ds = Implies(ex_y_app_ds, In(xds, w))
    rem_ds = [f_ for f_ in cur_ds.sequent.left if not same(f_, ex_y_app_ds)]
    got_dom_sub_body = Proof(Sequent(rem_ds, [imp_ds]), 'implies_right', [cur_ds], principal=imp_ds)
    dom_sub_sf = Forall(xds, imp_ds)
    got_dom_sub = Proof(Sequent(rem_ds, [dom_sub_sf]), 'forall_right',
        [got_dom_sub_body], principal=dom_sub_sf, term=xds)
    # got_dom_sub: [sf_char, Ext] |- dom_sub_sf

    # succ_char -> Succ(y1,x) and Succ(y2,x):
    sc_inst_y1 = Iff(app1, SuccDef(y1sv, xsv))
    fa_y1 = Forall(y1sv, sc_inst_y1)
    got_sc_x = apply_thm(got_succ_char, [xsv], In(xsv, w), fa_y1, cur_dm)
    got_sc_y1 = apply_thm(got_sc_x, [y1sv], concl=sc_inst_y1)
    got_s1 = mp(mp(iff_mp(app1, SuccDef(y1sv, xsv), []),
        got_sc_y1, sc_inst_y1, Implies(app1, SuccDef(y1sv, xsv))),
        apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)),
        app1, SuccDef(y1sv, xsv))

    got_sc_y2 = apply_thm(got_sc_x, [y2sv], concl=Iff(app2, SuccDef(y2sv, xsv)))
    got_s2 = mp(mp(iff_mp(app2, SuccDef(y2sv, xsv), []),
        got_sc_y2, Iff(app2, SuccDef(y2sv, xsv)), Implies(app2, SuccDef(y2sv, xsv))),
        apply_thm(and_elim_right(app1, app2, []), [], and_apps, app2, ax(and_apps)),
        app2, SuccDef(y2sv, xsv))

    # unique_successor: Succ(y1,x) -> Succ(y2,x) -> Eq(y1,y2)
    us = unique_successor()
    all_us = list(got_s1.sequent.left)
    for f_ in got_s2.sequent.left:
        if not any(same(f_, g) for g in all_us):
            all_us.append(f_)
    got_eq_y12 = mp(apply_thm(us, [xsv, y1sv, y2sv], SuccDef(y1sv, xsv),
        Implies(SuccDef(y2sv, xsv), Eq(y1sv, y2sv)), weaken_to(got_s1, all_us)),
        weaken_to(got_s2, all_us), SuccDef(y2sv, xsv), Eq(y1sv, y2sv))

    # Close single-valued:
    imp_sv = Implies(and_apps, Eq(y1sv, y2sv))
    rem_sv = [f_ for f_ in got_eq_y12.sequent.left if not same(f_, and_apps)]
    cur_sv = Proof(Sequent(rem_sv, [imp_sv]), 'implies_right', [got_eq_y12], principal=imp_sv)
    for var in [y2sv, y1sv, xsv]:
        body = cur_sv.sequent.right[0]
        fa = Forall(var, body)
        cur_sv = Proof(Sequent(cur_sv.sequent.left, [fa]), 'forall_right', [cur_sv], principal=fa, term=var)
    sv_formula = cur_sv.sequent.right[0]

    # === Function(sf) = And(Relation, single_valued) ===
    func_sf = FuncDef(sfv)
    all_func = list(got_rel.sequent.left)
    for f_ in cur_sv.sequent.left:
        if not any(same(f_, g) for g in all_func):
            all_func.append(f_)
    got_func = mp(apply_thm(and_intro(rel_sf, sv_formula, []), [], rel_sf,
        Implies(sv_formula, func_sf), weaken_to(got_rel, all_func)),
        weaken_to(cur_sv, all_func), sv_formula, func_sf)

    # === Package: And(succ_char, And(Function(sf), dom_sub_sf)), exists sf ===
    and_func_dom = And(func_sf, dom_sub_sf)
    result = And(succ_char, and_func_dom)
    # And(func_sf, dom_sub_sf):
    all_fd = list(got_func.sequent.left)
    for f_ in got_dom_sub.sequent.left:
        if not any(same(f_, g) for g in all_fd):
            all_fd.append(f_)
    got_fd = mp(apply_thm(and_intro(func_sf, dom_sub_sf, []), [], func_sf,
        Implies(dom_sub_sf, and_func_dom), weaken_to(got_func, all_fd)),
        weaken_to(got_dom_sub, all_fd), dom_sub_sf, and_func_dom)
    # And(succ_char, And(func, dom_sub)):
    all_res = list(got_succ_char.sequent.left)
    for f_ in got_fd.sequent.left:
        if not any(same(f_, g) for g in all_res):
            all_res.append(f_)
    got_res = mp(apply_thm(and_intro(succ_char, and_func_dom, []), [], succ_char,
        Implies(and_func_dom, result), weaken_to(got_succ_char, all_res)),
        weaken_to(got_fd, all_res), and_func_dom, result)

    # Exists-intro sfv, eel from sf_char, cut with got_sfe:
    got_ex = eir(got_res, And(succ_char, And(FuncDef(sfv), dom_sub_sf)), sfv, sfv)
    got_ex = eel(got_ex, sf_char, sfv)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], got_sfe)

    # forall w:
    proof = got_ex
    body = proof.sequent.right[0]
    fa_w = Forall(w, body)
    proof = Proof(Sequent(proof.sequent.left, [fa_w]), 'forall_right', [proof], principal=fa_w, term=w)

    proof.name = 'sf_props'
    return proof


def plus_zero_right():
    """m + 0 = m: the base case of addition.
    |- forall w, m, e.
         Omega(w) -> In(m, w) -> Empty(e) -> Plus(m, e, m)
    Uses sf_props + recursion_theorem + Recursive base."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive,
        Successor as SuccDef, Plus as PlusDef)

    w = Var(postfix='w')
    m = Var(postfix='m')
    ev = Var(postfix='e')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    empty_ev = Empty(ev)
    zero_ev = Num(ev, 0)
    plus_goal = PlusDef(m, ev, m)

    goal = Forall(w, Forall(m, Forall(ev,
        Implies(omega_w, Implies(in_m_w, Implies(zero_ev, plus_goal))))))

    from theorems.recursion import recursion_theorem
    from theorems.sets import successor_exists
    from theorems.omega import omega_succ_closed
    from definitions import ExistsUnique, Recursive as RecDef

    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    # === Step 1: sf from sf_props ===
    sp = sf_props()
    app_sf = Apply(sfv, xsc, ysc)
    succ_yx = SuccDef(ysc, xsc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf, succ_yx))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    and_func_dom = And(func_sf, dom_sub_sf)
    and_sc_fd = And(succ_char, and_func_dom)
    ex_sf = Exists(sfv, and_sc_fd)
    got_sp = apply_thm(sp, [w], concl=ex_sf)

    got_sc_from = apply_thm(and_elim_left(succ_char, and_func_dom, []), [],
        and_sc_fd, succ_char, ax(and_sc_fd))
    got_fd_from = apply_thm(and_elim_right(succ_char, and_func_dom, []), [],
        and_sc_fd, and_func_dom, ax(and_sc_fd))
    got_func_from = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        and_func_dom, func_sf, got_fd_from)
    got_dom_from = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        and_func_dom, dom_sub_sf, got_fd_from)

    # === Step 2: Build dom_closed(sf, m) ===
    # dom_closed = And(f_at_a, ran_f_closed) where f=sf, a=m
    # -- f_at_a: exists z. Apply(sf, m, z) --
    sm = Var(postfix='sm')
    se = successor_exists()
    got_se = apply_thm(se, [m], concl=Exists(sm, SuccDef(sm, m)))
    sc_at_m = Implies(In(m, w), Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m))))
    got_sc_m = fl(succ_char, sc_at_m, m)
    fa_y_at_m = Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m)))
    got_fa_y_m = mp(got_sc_m, ax(In(m, w)), In(m, w), fa_y_at_m)
    iff_m_sm = Iff(Apply(sfv, m, sm), SuccDef(sm, m))
    got_iff_m = apply_thm(got_fa_y_m, [sm], concl=iff_m_sm)
    got_app_m = mp(mp(iff_mp_rev(Apply(sfv, m, sm), SuccDef(sm, m), []),
        got_iff_m, iff_m_sm, Implies(SuccDef(sm, m), Apply(sfv, m, sm))),
        ax(SuccDef(sm, m)), SuccDef(sm, m), Apply(sfv, m, sm))
    zfa2 = Var()
    got_ex_app_m = eir(got_app_m, Apply(sfv, m, zfa2), zfa2, sm)
    got_ex_app_m = eel(got_ex_app_m, SuccDef(sm, m), sm)
    got_ex_app_m = cut(got_ex_app_m, got_ex_app_m.sequent.left[-1], got_se)
    f_at_a = Exists(zfa2, Apply(sfv, m, zfa2))
    # got_ex_app_m: [succ_char, In(m,w), Pairing] |- f_at_a

    # -- ran_f_closed: forall y,z. Apply(sf,y,z) -> exists q. Apply(sf,z,q) --
    # dom_sub -> In(y,w). succ_char fwd -> Succ(z,y). omega_succ -> In(z,w).
    # successor_exists -> Succ(q,z). succ_char bwd -> Apply(sf,z,q).
    yr, zr, qr = Var(postfix='yr'), Var(postfix='zr'), Var(postfix='qr')
    app_yz = Apply(sfv, yr, zr)
    succ_zr_yr = SuccDef(zr, yr)

    # dom_sub at yr: Apply(sf,yr,zr) -> In(yr,w)
    got_in_yr = apply_thm(got_dom_from, [yr],
        Exists(yds, Apply(sfv, yr, yds)), In(yr, w),
        eir(ax(app_yz), Apply(sfv, yr, yds), yds, zr))
    # [and_sc_fd, Apply(sf,yr,zr)] |- In(yr,w)

    # succ_char fwd: In(yr,w) -> Apply(sf,yr,zr) -> Succ(zr,yr)
    sc_at_yr = Implies(In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    got_sc_yr = fl(succ_char, sc_at_yr, yr)
    got_fa_yr = mp(got_sc_yr, got_in_yr, In(yr, w),
        Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    iff_yr_zr = Iff(app_yz, succ_zr_yr)
    got_iff_yr = apply_thm(got_fa_yr, [zr], concl=iff_yr_zr)
    got_succ_zr = mp(mp(iff_mp(app_yz, succ_zr_yr, []),
        got_iff_yr, iff_yr_zr, Implies(app_yz, succ_zr_yr)),
        ax(app_yz), app_yz, succ_zr_yr)

    # omega_succ_closed: In(yr,w) -> Succ(zr,yr) -> In(zr,w)
    osc = omega_succ_closed()
    got_in_zr = apply_thm(osc, [w], omega_w,
        Forall(yr, Implies(In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))))),
        ax(omega_w))
    got_in_zr = apply_thm(got_in_zr, [yr], In(yr, w),
        Forall(zr, Implies(succ_zr_yr, In(zr, w))), got_in_yr)
    got_in_zr = apply_thm(got_in_zr, [zr], succ_zr_yr, In(zr, w), got_succ_zr)

    # succ_char bwd at (zr, qr): In(zr,w) -> Succ(qr,zr) -> Apply(sf,zr,qr)
    succ_qr_zr = SuccDef(qr, zr)
    sc_at_zr = Implies(In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr))))
    got_sc_zr = fl(succ_char, sc_at_zr, zr)
    got_fa_zr = mp(got_sc_zr, got_in_zr, In(zr, w),
        Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr))))
    iff_zr_qr = Iff(Apply(sfv, zr, qr), succ_qr_zr)
    got_iff_zr = apply_thm(got_fa_zr, [qr], concl=iff_zr_qr)
    got_app_zr = mp(mp(iff_mp_rev(Apply(sfv, zr, qr), succ_qr_zr, []),
        got_iff_zr, iff_zr_qr, Implies(succ_qr_zr, Apply(sfv, zr, qr))),
        ax(succ_qr_zr), succ_qr_zr, Apply(sfv, zr, qr))

    # successor_exists -> eir -> eel -> exists q. Apply(sf,zr,q)
    got_se_zr = apply_thm(se, [zr], concl=Exists(qr, succ_qr_zr))
    qr2 = Var()
    got_ex_app_zr = eir(got_app_zr, Apply(sfv, zr, qr2), qr2, qr)
    got_ex_app_zr = eel(got_ex_app_zr, succ_qr_zr, qr)
    got_ex_app_zr = cut(got_ex_app_zr, got_ex_app_zr.sequent.left[-1], got_se_zr)

    # Close ran_f_closed:
    ex_q_app = got_ex_app_zr.sequent.right[0]
    imp_rfc = Implies(app_yz, ex_q_app)
    rem_rfc = [f_ for f_ in got_ex_app_zr.sequent.left if not same(f_, app_yz)]
    got_rfc_body = Proof(Sequent(rem_rfc, [imp_rfc]), 'implies_right',
        [got_ex_app_zr], principal=imp_rfc)
    ran_f_closed = Forall(yr, Forall(zr, imp_rfc))
    cur_rfc = got_rfc_body
    for var in [zr, yr]:
        body = cur_rfc.sequent.right[0]
        fa = Forall(var, body)
        cur_rfc = Proof(Sequent(cur_rfc.sequent.left, [fa]), 'forall_right',
            [cur_rfc], principal=fa, term=var)

    # dom_closed = And(f_at_a, ran_f_closed):
    dom_closed = And(f_at_a, ran_f_closed)
    all_dc = list(got_ex_app_m.sequent.left)
    for f_ in cur_rfc.sequent.left:
        if not any(same(f_, g) for g in all_dc):
            all_dc.append(f_)
    got_dc = mp(apply_thm(and_intro(f_at_a, ran_f_closed, []), [], f_at_a,
        Implies(ran_f_closed, dom_closed), weaken_to(got_ex_app_m, all_dc)),
        weaken_to(cur_rfc, all_dc), ran_f_closed, dom_closed)
    got_dc = cut(got_dc, succ_char, got_sc_from)

    # === Step 3: Apply recursion theorem ===
    rt = recursion_theorem()
    rec_h = RecDef(hv, m, sfv, w)
    exu_h = ExistsUnique(hv, rec_h)
    got_rt = apply_thm(rt, [m, sfv, w], func_sf,
        Implies(dom_closed, Implies(omega_w, exu_h)), got_func_from)
    got_rt = mp(got_rt, got_dc, dom_closed, Implies(omega_w, exu_h))
    got_rt = mp(got_rt, ax(omega_w), omega_w, exu_h)
    # got_rt: [and_sc_fd, In(m,w), omega_w, axioms] |- ExistsUnique(hv, Recursive)

    # === Step 4: Extract base from Recursive, build Plus ===
    # ExistsUnique = Exists(hv, And(rec_h, uniq)). Open to get rec_h.
    h2v = Var()
    uniq_part = Forall(h2v, Implies(RecDef(h2v, m, sfv, w), Eq(hv, h2v)))
    and_rec_uniq = And(rec_h, uniq_part)
    got_rec_from = apply_thm(and_elim_left(rec_h, uniq_part, []), [],
        and_rec_uniq, rec_h, ax(and_rec_uniq))

    # Extract base: forall e. Empty(e) -> Apply(hv, e, m)
    ev2 = Var()
    base_h = Forall(ev2, Implies(Empty(ev2), Apply(hv, ev2, m)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_bs)
    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs, []), [],
        rec_h, and_dom_bs, got_rec_from)
    got_bs = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [],
        and_dom_bs, and_bs, got_dom_bs)
    got_base = apply_thm(and_elim_left(base_h, step_h, []), [],
        and_bs, base_h, got_bs)
    # [and_rec_uniq] |- base_h

    app_h_em = Apply(hv, ev, m)
    got_app_em = apply_thm(got_base, [ev], empty_ev, app_h_em, ax(empty_ev))
    # [and_rec_uniq, Empty(ev)] |- Apply(hv, ev, m)

    # === Step 5: Package into Plus(m, ev, m) ===
    # Plus = Exists(w', And(Omega(w'), Exists(h, Exists(sf, And(sf_all, And(Rec, Apply))))))
    # sf_all = And(succ_char, And(Function(sf), dom_sub))
    # Build And(Recursive, Apply):
    and_rec_app = And(rec_h, app_h_em)
    got_ra = mp(apply_thm(and_intro(rec_h, app_h_em, []), [], rec_h,
        Implies(app_h_em, and_rec_app), got_rec_from),
        got_app_em, app_h_em, and_rec_app)
    # And(sf_all, And(Rec, Apply)):  sf_all = and_sc_fd from sf_props
    and_sf_ra = And(and_sc_fd, and_rec_app)
    all_pkg = list(got_ra.sequent.left)
    for f_ in ax(and_sc_fd).sequent.left:
        if not any(same(f_, g) for g in all_pkg):
            all_pkg.append(f_)
    got_sfra = mp(apply_thm(and_intro(and_sc_fd, and_rec_app, []), [], and_sc_fd,
        Implies(and_rec_app, and_sf_ra), ax(and_sc_fd)),
        got_ra, and_rec_app, and_sf_ra)
    # Exists sf, h, w:
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc3, ysc3, xds3, yds3 = Var(), Var(), Var(), Var()
    sc_pat = Forall(xsc3, Implies(In(xsc3, w), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3)))))
    sf_all_pat = And(sc_pat, And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w)))))
    inner_sf = And(sf_all_pat, And(RecDef(hv, m, sf_var, w), Apply(hv, ev, m)))
    got_ex_sf = eir(got_sfra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sf_all_pat, And(RecDef(h_var, m, sf_var, w), Apply(h_var, ev, m))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    sf_all_w = And(Forall(xsc3, Implies(In(xsc3, w_var), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3))))),
        And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w_var)))))
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(sf_all_w, And(RecDef(h_var, m, sf_var, w_var), Apply(h_var, ev, m))))))
    got_plus = eir(got_omega_ex, inner_w, w_var, w)
    # got_plus: [and_sc_fd, and_rec_uniq, Empty(ev), omega_w, axioms] |- Plus(m, ev, m)

    # === Step 6: Close existentials from sf_props and recursion theorem ===
    cur = got_plus
    # eel hv from and_rec_uniq, then cut with ExistsUnique from got_rt:
    cur = eel(cur, and_rec_uniq, hv)
    cur = cut(cur, cur.sequent.left[-1], got_rt)
    # eel sfv from and_sc_fd:
    cur = eel(cur, and_sc_fd, sfv)
    cur = cut(cur, cur.sequent.left[-1], got_sp)

    # === Step 7: Discharge and close ===
    proof = cur
    g_ev = goal.body.body  # Forall(ev, Implies(omega, ...))
    g_omega = g_ev.body    # Implies(omega, Implies(in_m, Implies(empty, plus)))
    g_in_m = g_omega.right
    g_empty = g_in_m.right
    for hh, imp in [(empty_ev, g_empty), (In(m, w), g_in_m), (omega_w, g_omega)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var, fa in [(ev, g_ev), (m, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'plus_zero_right'
    return proof


def rec_step_succ():
    """Recursive step gives h(S(n)) = S(h(n)).
    |- forall w, m, sf, h, n, p, sn, sp.
         Omega(w) -> In(n, w) -> In(p, w) ->
         succ_char(sf, w) -> Recursive(h, m, sf, w) ->
         Apply(h, n, p) -> Succ(sn, n) -> Succ(sp, p) -> Apply(h, sn, sp)
    From Recursive step + succ_char backward."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)

    w = Var(postfix='w')
    m = Var(postfix='m')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    n, p = Var(postfix='n'), Var(postfix='p')
    sn, sp = Var(postfix='sn'), Var(postfix='sp')
    omega_w = Omega(w)
    in_n_w, in_p_w = In(n, w), In(p, w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    app_sf_xy = Apply(sfv, xsc, ysc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf_xy, SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, m, sfv, w)
    app_h_np = Apply(hv, n, p)
    succ_sn_n = SuccDef(sn, n)
    succ_sp_p = SuccDef(sp, p)
    app_h_sn_sp = Apply(hv, sn, sp)

    goal = Forall(w, Forall(m, Forall(sfv, Forall(hv, Forall(n, Forall(p, Forall(sn, Forall(sp,
        Implies(omega_w, Implies(in_n_w, Implies(in_p_w,
            Implies(succ_char, Implies(rec_h, Implies(app_h_np,
                Implies(succ_sn_n, Implies(succ_sp_p, app_h_sn_sp))))))))))))))))

    # === Extract Recursive step ===
    ev_r = Var()
    base_h = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, m)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_bs)

    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs, []), [],
        rec_h, and_dom_bs, ax(rec_h))
    got_bs = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [],
        and_dom_bs, and_bs, got_dom_bs)
    got_step = apply_thm(and_elim_right(base_h, step_h, []), [],
        and_bs, step_h, got_bs)
    # [rec_h] |- step_h

    # Peel step at (n, p, sn, sp):
    step_at_n = Implies(in_n_w, Forall(valst, Implies(Apply(hv, n, valst),
        Forall(snst, Implies(SuccDef(snst, n),
            Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                Apply(hv, snst, fvalst))))))))
    got_s = cut(fl(step_h, step_at_n, n), step_h, got_step)
    got_s = mp(got_s, ax(in_n_w), in_n_w, step_at_n.right)
    step_at_p = Implies(app_h_np, Forall(snst, Implies(SuccDef(snst, n),
        Forall(fvalst, Implies(Apply(sfv, p, fvalst), Apply(hv, snst, fvalst))))))
    fl_p = fl(got_s.sequent.right[0], step_at_p, p)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_p]), 'cut',
        [wr(got_s, step_at_p), weaken_to(fl_p, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    got_s = mp(got_s, ax(app_h_np), app_h_np, step_at_p.right)
    step_at_sn = Implies(succ_sn_n, Forall(fvalst, Implies(Apply(sfv, p, fvalst), Apply(hv, sn, fvalst))))
    fl_sn = fl(got_s.sequent.right[0], step_at_sn, sn)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_sn]), 'cut',
        [wr(got_s, step_at_sn), weaken_to(fl_sn, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    got_s = mp(got_s, ax(succ_sn_n), succ_sn_n, step_at_sn.right)
    app_sf_p_sp = Apply(sfv, p, sp)
    step_at_sp = Implies(app_sf_p_sp, app_h_sn_sp)
    fl_sp = fl(got_s.sequent.right[0], step_at_sp, sp)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_sp]), 'cut',
        [wr(got_s, step_at_sp), weaken_to(fl_sp, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    # got_s: [rec_h, In(n,w), Apply(h,n,p), Succ(sn,n)] |- Apply(sf,p,sp) -> Apply(h,sn,sp)

    # === succ_char backward: Succ(sp,p) -> Apply(sf,p,sp) given In(p,w) ===
    sc_at_p = Implies(in_p_w, Forall(ysc, Iff(Apply(sfv, p, ysc), SuccDef(ysc, p))))
    got_sc_p = fl(succ_char, sc_at_p, p)
    got_fa_p = mp(got_sc_p, ax(in_p_w), in_p_w, Forall(ysc, Iff(Apply(sfv, p, ysc), SuccDef(ysc, p))))
    iff_p_sp = Iff(app_sf_p_sp, succ_sp_p)
    got_iff_p = apply_thm(got_fa_p, [sp], concl=iff_p_sp)
    got_app_sf = mp(mp(iff_mp_rev(app_sf_p_sp, succ_sp_p, []),
        got_iff_p, iff_p_sp, Implies(succ_sp_p, app_sf_p_sp)),
        ax(succ_sp_p), succ_sp_p, app_sf_p_sp)
    # [succ_char, In(p,w), Succ(sp,p)] |- Apply(sf,p,sp)

    # === Combine ===
    all_left = list(got_s.sequent.left)
    for f_ in got_app_sf.sequent.left:
        if not any(same(f_, g) for g in all_left):
            all_left.append(f_)
    got_result = mp(weaken_to(got_s, all_left),
        weaken_to(got_app_sf, all_left), app_sf_p_sp, app_h_sn_sp)
    # [rec_h, In(n,w), Apply(h,n,p), Succ(sn,n), succ_char, In(p,w), Succ(sp,p)] |- Apply(h,sn,sp)

    # === Discharge and close using goal ===
    proof = wl(got_result, omega_w)  # omega_w not used but part of goal
    # Unpack goal's implies chain:
    g8 = goal.body.body.body.body.body.body.body  # Forall(sp, Implies(omega, ...))
    cur_imp = g8.body  # Implies(omega_w, Implies(in_n, ...))
    imps = []
    while hasattr(cur_imp, 'right') and isinstance(cur_imp, Implies):
        imps.append(cur_imp)
        cur_imp = cur_imp.right
    # imps[0]=Implies(omega,...), imps[1]=Implies(in_n,...), ..., imps[7]=Implies(succ_sp,app)
    hyps_imps = list(zip([succ_sp_p, succ_sn_n, app_h_np, rec_h, succ_char, in_p_w, in_n_w, omega_w],
                         reversed(imps)))
    for hh, imp in hyps_imps:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    # Forall chain:
    fas = [g8, goal.body.body.body.body.body.body, goal.body.body.body.body.body,
           goal.body.body.body.body, goal.body.body.body, goal.body.body, goal.body, goal]
    for var, fa in zip([sp, sn, p, n, hv, sfv, m, w], fas):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'rec_step_succ'
    return proof


def rec_h_zero_identity():
    """When initial value is 0 (empty set), h(m) = m for all m in omega.
    Ext, Inf, Sep |- forall w, sf, h, e.
      Omega(w) -> succ_char(sf, w) -> Recursive(h, e, sf, w) -> Empty(e) ->
      forall m. In(m, w) -> Apply(h, m, m)
    Induction on m with P(m) = Apply(h, m, m).
    Base: Apply(h, 0, 0) from Recursive base (h(0) = e = 0, and 0 = e).
    Step: Apply(h, m, m) -> Apply(h, S(m), S(m)) from rec_step_succ."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from core.proof import _expand

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    ev = Var(postfix='e')
    mv = Var(postfix='m')
    omega_w = Omega(w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, ev, sfv, w)
    empty_ev = Empty(ev)
    zero_ev = Num(ev, 0)
    app_h_mm = Apply(hv, mv, mv)

    goal = Forall(w, Forall(sfv, Forall(hv, Forall(ev,
        Implies(omega_w, Implies(succ_char, Implies(rec_h, Implies(zero_ev,
            Forall(mv, Implies(In(mv, w), app_h_mm))))))))))

    # === Induction setup ===
    # P(x) = Apply(h, x, x)
    from theorems.axioms import separation
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed

    pv = Var(postfix='p')
    xv = Var(postfix='xv')
    def P(x):
        return Apply(hv, x, x)
    char_p_body = Iff(In(xv, pv), And(In(xv, w), P(xv)))
    char_p = Forall(xv, char_p_body)

    sep = separation(P, [hv])
    got_sep = sep
    for term in [hv]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        # wl (not weaken_to): actual may same() match sep axiom, need both copies for cut
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)],
            principal=actual)
    # Peel forall a_set = w:
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, Exists(pv, char_p), w)
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)), wl(fl_w, *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    # char_p helpers:
    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base: Empty(ev) -> In(ev, pv) ===
    # From Recursive base: Apply(h, ev, ev) (h(0)=e, and P(e) = Apply(h,e,e))
    # Wait: Recursive base is Apply(h, ev, ev)? No: h(0)=e means Apply(h, 0, e).
    # But e IS 0 (the empty set). So Apply(h, e, e) = Apply(h, 0, 0). P(0) = Apply(h, 0, 0). Yes!
    ev_r = Var()
    base_h = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, ev)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h_body = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h_body)
    and_dom_bs = And(dom_sub_h, and_bs)

    got_dom_bs_r = apply_thm(and_elim_right(func_h, and_dom_bs, []), [],
        rec_h, and_dom_bs, ax(rec_h))
    got_bs_r = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [],
        and_dom_bs, and_bs, got_dom_bs_r)
    got_base_h = apply_thm(and_elim_left(base_h, step_h_body, []), [],
        and_bs, base_h, got_bs_r)
    # [rec_h] |- forall ev_r. Empty(ev_r) -> Apply(hv, ev_r, ev)

    # Base case uses fresh ev_base (ev is free in rec_h, can't be eigenvariable).
    # h(ev_base) = ev from Recursive. Eq(ev, ev_base) from unique_empty. Transfer: Apply(h,eb,eb).
    ev_base = Var(postfix='eb')
    empty_eb = Empty(ev_base)
    from theorems.logic import and_intro, eq_symmetric
    from theorems.recursion import eq_apply_val_transfer

    got_app_eb_ev = apply_thm(got_base_h, [ev_base], empty_eb, Apply(hv, ev_base, ev), ax(empty_eb))
    # [rec_h, Empty(ev_base)] |- Apply(hv, ev_base, ev)

    # unique_empty: forall e1. Empty(e1) -> forall e2. Empty(e2) -> Eq(e1,e2)
    # Interleaved forall/implies — peel manually
    from theorems.logic import unique_empty
    ue = unique_empty()
    got_eq_eeb = apply_thm(ue, [ev], empty_ev,
        Forall(ev_base, Implies(empty_eb, Eq(ev, ev_base))), ax(empty_ev))
    got_eq_eeb = apply_thm(got_eq_eeb, [ev_base], empty_eb,
        Eq(ev, ev_base), ax(empty_eb))
    # [Empty(ev), Empty(ev_base)] |- Eq(ev, ev_base)

    # eq_apply_val_transfer: peel 3 foralls (f,x,y), then fl z=ev_base manually
    # (can't use apply_thm with 4 terms because x=ev_base and z=ev_base clash)
    eavt = eq_apply_val_transfer()
    zz = Var()  # eavt's internal z var
    fa_z = Forall(zz, Implies(Eq(ev, zz), Implies(Apply(hv, ev_base, ev), Apply(hv, ev_base, zz))))
    got_eavt = apply_thm(eavt, [hv, ev_base, ev], Eq(ev, ev_base),
        Implies(Apply(hv, ev_base, ev), Apply(hv, ev_base, ev_base)), ax(Eq(ev, ev_base)))
    # Hmm, this still has concl with ev_base for z. But the 3-term peel gives fa_z on the right.
    # Let me use apply_thm with 3 terms and hyp=None:
    got_eavt3 = apply_thm(eavt, [hv, ev_base, ev], concl=fa_z)
    # got_eavt3: [eavt axioms] |- Forall(zz, Implies(Eq(ev,zz), Implies(App(h,eb,ev), App(h,eb,zz))))
    # fl z=ev_base:
    inst_z = Implies(Eq(ev, ev_base), Implies(Apply(hv, ev_base, ev), Apply(hv, ev_base, ev_base)))
    got_eavt_inst = fl(fa_z, inst_z, ev_base)
    got_eavt_inst = Proof(Sequent(got_eavt3.sequent.left, [inst_z]), 'cut',
        [wr(got_eavt3, inst_z), weaken_to(got_eavt_inst, got_eavt3.sequent.left)],
        principal=fa_z)
    # MP with Eq and Apply:
    all_base_eq = list(got_eq_eeb.sequent.left)
    for f_ in got_app_eb_ev.sequent.left:
        if not any(same(f_, g) for g in all_base_eq):
            all_base_eq.append(f_)
    for f_ in got_eavt_inst.sequent.left:
        if not any(same(f_, g) for g in all_base_eq):
            all_base_eq.append(f_)
    got_app_eb_eb = mp(weaken_to(got_eavt_inst, all_base_eq),
        weaken_to(got_eq_eeb, all_base_eq), Eq(ev, ev_base),
        Implies(Apply(hv, ev_base, ev), P(ev_base)))
    got_app_eb_eb = mp(got_app_eb_eb, weaken_to(got_app_eb_ev, all_base_eq),
        Apply(hv, ev_base, ev), P(ev_base))
    # [rec_h, Empty(ev), Empty(ev_base)] |- P(ev_base)

    # In(ev_base, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(ev_base, Implies(empty_eb, In(ev_base, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [ev_base], empty_eb, In(ev_base, w), ax(empty_eb))
    # [omega_w, Empty(ev_base), Inf] |- In(ev_base, w)

    # And(In(eb,w), P(eb)) -> In(eb, pv):
    and_w_p_eb = And(In(ev_base, w), P(ev_base))
    all_base = list(got_eb_w.sequent.left)
    for f_ in got_app_eb_eb.sequent.left:
        if not any(same(f_, g) for g in all_base):
            all_base.append(f_)
    got_and_base = mp(apply_thm(and_intro(In(ev_base, w), P(ev_base), []), [], In(ev_base, w),
        Implies(P(ev_base), and_w_p_eb), weaken_to(got_eb_w, all_base)),
        weaken_to(got_app_eb_eb, all_base), P(ev_base), and_w_p_eb)
    got_bwd_eb = char_p_bwd(ev_base)
    all_bwd = list(got_and_base.sequent.left)
    for f_ in got_bwd_eb.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_eb, all_bwd), got_and_base, and_w_p_eb, In(ev_base, pv))

    # Close base: implies_right Empty(ev_base), forall_right ev_base
    imp_base = Implies(empty_eb, In(ev_base, pv))
    rem = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    base_ind = Forall(ev_base, imp_base)
    proof_base = Proof(Sequent(rem, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=ev_base)

    # === Step: In(m, pv) -> Succ(sm, m) -> In(sm, pv) ===
    smv = Var(postfix='sm')
    succ_sm_m = SuccDef(smv, mv)
    in_mv_p = In(mv, pv)

    # From char_p fwd: In(mv, pv) -> And(In(mv,w), P(mv))
    got_fwd_m = char_p_fwd(mv)
    got_and_m = mp(weaken_to(got_fwd_m, [in_mv_p]), ax(in_mv_p), in_mv_p, And(In(mv, w), P(mv)))
    got_in_mw = apply_thm(and_elim_left(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), In(mv, w), got_and_m)
    got_p_m = apply_thm(and_elim_right(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), P(mv), got_and_m)
    # [char_p, In(mv,pv)] |- In(mv,w) and P(mv) = Apply(h,mv,mv)

    # rec_step_succ: Apply(h,mv,mv) + Succ(smv,mv) + Succ(S(mv),mv) -> Apply(h,smv,S(mv))
    # But we want Apply(h,smv,smv), i.e., P(smv). We need S(mv) = smv, i.e., Succ(smv,mv).
    # So: rec_step_succ with n=mv, p=mv, sn=smv, sp=smv.
    # Succ(smv,mv) = succ_sm_m (given). Succ(smv,mv) = Succ(sp,p) with sp=smv, p=mv. ✓
    # Apply(h,smv,smv) = rec_step_succ result. ✓
    rst = rec_step_succ()
    # rst: |- forall w,m,sf,h,n,p,sn,sp. Omega->In(n,w)->In(p,w)->sc->Rec->App(h,n,p)->Succ(sn,n)->Succ(sp,p)->App(h,sn,sp)
    # rec_step_succ: 8 foralls (w,m,sf,h,n,p,sn,sp) then 8 implies.
    # n=mv, p=mv (same) and sn=smv, sp=smv (same) cause shadow in apply_thm.
    # Peel first 4 (w,m,sf,h) with apply_thm, then fl the rest manually.
    app_h_sm_sm = Apply(hv, smv, smv)
    # After peeling w,ev,sfv,hv: forall n. forall p. forall sn. forall sp. Omega(w) -> ...
    # But rec_step_succ has all implies AFTER all foralls. So the body after 4 foralls is:
    # forall n. forall p. forall sn. forall sp. Omega -> In(n,w) -> In(p,w) -> sc -> rec -> app -> succ_sn -> succ_sp -> app_result
    nv2, pv2, snv2, spv2 = Var(), Var(), Var(), Var()
    inner_after4 = Forall(nv2, Forall(pv2, Forall(snv2, Forall(spv2,
        Implies(omega_w, Implies(In(nv2, w), Implies(In(pv2, w), Implies(succ_char,
            Implies(RecDef(hv, ev, sfv, w), Implies(Apply(hv, nv2, pv2),
                Implies(SuccDef(snv2, nv2), Implies(SuccDef(spv2, pv2),
                    Apply(hv, snv2, spv2)))))))))))))
    got_rst = apply_thm(rst, [w, ev, sfv, hv], concl=inner_after4)
    # Peel n=mv, p=mv, sn=smv, sp=smv manually:
    from core.proof import _expand
    cur_f = inner_after4
    for term in [mv, mv, smv, smv]:
        exp = _expand(cur_f)
        next_f = exp.body
        # forall_left substitutes exp.var with term:
        from core.proof import _subst
        next_f = _subst(exp.body, exp.var, term)
        fl_t = fl(cur_f, next_f, term)
        got_rst = Proof(Sequent(got_rst.sequent.left, [next_f]), 'cut',
            [wr(got_rst, next_f), wl(fl_t, *got_rst.sequent.left)], principal=cur_f)
        cur_f = next_f
    # Now got_rst.right[0] = Omega -> In(mv,w) -> In(mv,w) -> sc -> rec -> Apply(h,mv,mv) -> Succ(smv,mv) -> Succ(smv,mv) -> Apply(h,smv,smv)
    got_rst = mp(got_rst, ax(omega_w), omega_w, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_in_mw, In(mv, w), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_in_mw, In(mv, w), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_char), succ_char, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(rec_h), rec_h, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_p_m, P(mv), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_sm_m), succ_sm_m, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_sm_m), succ_sm_m, app_h_sm_sm)
    # got_rst: [char_p, In(mv,pv), omega_w, succ_char, rec_h, succ_sm_m] |- Apply(h,smv,smv) = P(smv)

    # omega_succ_closed: In(smv, w)
    osc = omega_succ_closed()
    got_sm_w = apply_thm(osc, [w], omega_w,
        Forall(mv, Implies(In(mv, w), Forall(smv, Implies(succ_sm_m, In(smv, w))))),
        ax(omega_w))
    got_sm_w = apply_thm(got_sm_w, [mv], In(mv, w),
        Forall(smv, Implies(succ_sm_m, In(smv, w))), got_in_mw)
    got_sm_w = apply_thm(got_sm_w, [smv], succ_sm_m, In(smv, w), ax(succ_sm_m))
    # [char_p, In(mv,pv), omega_w, succ_sm_m, Inf] |- In(smv, w)

    # And(In(smv,w), P(smv)) -> In(smv, pv)
    and_w_p_sm = And(In(smv, w), P(smv))
    all_step = list(got_rst.sequent.left)
    for f_ in got_sm_w.sequent.left:
        if not any(same(f_, g) for g in all_step):
            all_step.append(f_)
    got_and_step = mp(apply_thm(and_intro(In(smv, w), P(smv), []), [], In(smv, w),
        Implies(P(smv), and_w_p_sm), weaken_to(got_sm_w, all_step)),
        weaken_to(got_rst, all_step), P(smv), and_w_p_sm)
    got_bwd_sm = char_p_bwd(smv)
    all_bwd_sm = list(got_and_step.sequent.left)
    for f_ in got_bwd_sm.sequent.left:
        if not any(same(f_, g) for g in all_bwd_sm):
            all_bwd_sm.append(f_)
    got_in_sp = mp(weaken_to(got_bwd_sm, all_bwd_sm), got_and_step, and_w_p_sm, In(smv, pv))

    # Close step: implies_right succ_sm_m, forall smv, implies_right In(mv,pv), forall mv
    imp_succ = Implies(succ_sm_m, In(smv, pv))
    rem_s = [f_ for f_ in got_in_sp.sequent.left if not same(f_, succ_sm_m)]
    cur_step = Proof(Sequent(rem_s, [imp_succ]), 'implies_right', [got_in_sp], principal=imp_succ)
    fa_sm = Forall(smv, imp_succ)
    cur_step = Proof(Sequent(rem_s, [fa_sm]), 'forall_right', [cur_step], principal=fa_sm, term=smv)
    imp_inp = Implies(in_mv_p, fa_sm)
    rem_n = [f_ for f_ in cur_step.sequent.left if not same(f_, in_mv_p)]
    cur_step = Proof(Sequent(rem_n, [imp_inp]), 'implies_right', [cur_step], principal=imp_inp)
    step_ind = Forall(mv, imp_inp)
    proof_step = Proof(Sequent(rem_n, [step_ind]), 'forall_right', [cur_step], principal=step_ind, term=mv)

    # === Build Inductive(pv), Subset(pv,w), apply omega_smallest_inductive ===
    from definitions import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

    # Inductive = And(base_ind, step_ind):
    all_ind = list(proof_base.sequent.left)
    for f_ in proof_step.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind, step_ind, []), [], base_ind,
        Implies(step_ind, ind_p), weaken_to(proof_base, all_ind)),
        weaken_to(proof_step, all_ind), step_ind, ind_p)

    # Subset(pv,w): from char_p fwd, In(xv,pv) -> In(xv,w)
    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv), And(In(xsub, w), P(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P(xsub), []), [],
        And(In(xsub, w), P(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    # omega_smallest_inductive: Omega(w) -> And(Subset,Inductive) -> Eq(pv,w)
    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w, Implies(hyp_and, eq_pw), ax(omega_w))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # === Extract: In(mv, w) -> P(mv) ===
    # From Eq(pv,w): In(mv,w) -> In(mv,pv). From char_p: In(mv,pv) -> P(mv).
    zz = Var()
    iff_mv = Iff(In(mv, pv), In(mv, w))
    got_iff_mv = Proof(Sequent(got_eq.sequent.left, [iff_mv]), 'cut',
        [wr(got_eq, iff_mv), weaken_to(fl(eq_pw, iff_mv, mv), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_mp = mp(mp(iff_mp_rev(In(mv, pv), In(mv, w), []),
        got_iff_mv, iff_mv, Implies(In(mv, w), In(mv, pv))),
        ax(In(mv, w)), In(mv, w), In(mv, pv))
    got_fwd_mv = char_p_fwd(mv)
    all_ext = list(got_in_mp.sequent.left)
    for f_ in got_fwd_mv.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_ext = mp(weaken_to(got_fwd_mv, all_ext),
        weaken_to(got_in_mp, all_ext), In(mv, pv), And(In(mv, w), P(mv)))
    got_p_mv = apply_thm(and_elim_right(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), P(mv), got_and_ext)
    # [..., In(mv,w)] |- Apply(hv, mv, mv)

    # eel pv from char_p, cut with got_sep:
    proof = got_p_mv
    proof = eel(proof, char_p, pv)
    proof = cut(proof, proof.sequent.left[-1], got_sep)

    # === Discharge and close using goal ===
    g_ev = goal.body.body.body  # Forall(ev, Implies(omega, ...))
    g_omega = g_ev.body
    g_sc = g_omega.right
    g_rec = g_sc.right
    g_empty = g_rec.right  # Implies(empty, Forall(mv, ...))
    g_fa_mv = g_empty.right  # Forall(mv, Implies(In(mv,w), app))
    g_in_mv = g_fa_mv.body  # Implies(In(mv,w), app)

    rem_mv = [f_ for f_ in proof.sequent.left if not same(f_, In(mv, w))]
    proof = Proof(Sequent(rem_mv, [g_in_mv]), 'implies_right', [proof], principal=g_in_mv)
    proof = Proof(Sequent(rem_mv, [g_fa_mv]), 'forall_right', [proof], principal=g_fa_mv, term=mv)
    for hh, imp in [(empty_ev, g_empty), (rec_h, g_rec), (succ_char, g_sc), (omega_w, g_omega)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var, fa in [(ev, g_ev), (hv, goal.body.body), (sfv, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'rec_h_zero_identity'
    return proof


def plus_zero_left():
    """0 + m = m: addition with zero on the left.
    |- forall w, m, e.
         Omega(w) -> In(m, w) -> Empty(e) -> Plus(e, m, m)
    Uses sf_props + recursion_theorem + rec_h_zero_identity."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, ExistsUnique)
    from theorems.recursion import recursion_theorem
    from theorems.sets import successor_exists
    from theorems.omega import omega_succ_closed, omega_contains_empty

    w = Var(postfix='w')
    mv = Var(postfix='m')
    ev = Var(postfix='e')
    omega_w = Omega(w)
    in_m_w = In(mv, w)
    empty_ev = Empty(ev)
    zero_ev = Num(ev, 0)
    plus_goal = PlusDef(ev, mv, mv)

    goal = Forall(w, Forall(mv, Forall(ev,
        Implies(omega_w, Implies(in_m_w, Implies(zero_ev, plus_goal))))))

    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    # === sf_props → succ_char, Function(sf), dom_sub ===
    sp = sf_props()
    app_sf = Apply(sfv, xsc, ysc)
    succ_yx = SuccDef(ysc, xsc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf, succ_yx))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    and_func_dom = And(func_sf, dom_sub_sf)
    and_sc_fd = And(succ_char, and_func_dom)
    got_sp = apply_thm(sp, [w], concl=Exists(sfv, and_sc_fd))

    got_sc_from = apply_thm(and_elim_left(succ_char, and_func_dom, []), [],
        and_sc_fd, succ_char, ax(and_sc_fd))
    got_fd_from = apply_thm(and_elim_right(succ_char, and_func_dom, []), [],
        and_sc_fd, and_func_dom, ax(and_sc_fd))
    got_func_from = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        and_func_dom, func_sf, got_fd_from)
    got_dom_from = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        and_func_dom, dom_sub_sf, got_fd_from)

    # === dom_closed(sf, e) ===
    # f_at_a: ∃z. Apply(sf, e, z). From In(e,w) + succ_char backward + successor_exists.
    sm = Var(postfix='sm')
    se = successor_exists()
    got_se = apply_thm(se, [ev], concl=Exists(sm, SuccDef(sm, ev)))

    # In(e,w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_ev_w = apply_thm(oce, [w], omega_w,
        Forall(ev, Implies(empty_ev, In(ev, w))), ax(omega_w))
    got_ev_w = apply_thm(got_ev_w, [ev], empty_ev, In(ev, w), ax(empty_ev))

    sc_at_e = Implies(In(ev, w), Forall(ysc, Iff(Apply(sfv, ev, ysc), SuccDef(ysc, ev))))
    got_fa_e = mp(fl(succ_char, sc_at_e, ev), got_ev_w, In(ev, w),
        Forall(ysc, Iff(Apply(sfv, ev, ysc), SuccDef(ysc, ev))))
    iff_e_sm = Iff(Apply(sfv, ev, sm), SuccDef(sm, ev))
    got_app_e = mp(mp(iff_mp_rev(Apply(sfv, ev, sm), SuccDef(sm, ev), []),
        apply_thm(got_fa_e, [sm], concl=iff_e_sm), iff_e_sm,
        Implies(SuccDef(sm, ev), Apply(sfv, ev, sm))),
        ax(SuccDef(sm, ev)), SuccDef(sm, ev), Apply(sfv, ev, sm))
    zfa2 = Var()
    got_fat = eir(got_app_e, Apply(sfv, ev, zfa2), zfa2, sm)
    got_fat = eel(got_fat, SuccDef(sm, ev), sm)
    got_fat = cut(got_fat, got_fat.sequent.left[-1], got_se)
    f_at_a = Exists(zfa2, Apply(sfv, ev, zfa2))

    # ran_f_closed: same as plus_zero_right (doesn't depend on initial value)
    yr, zr, qr = Var(postfix='yr'), Var(postfix='zr'), Var(postfix='qr')
    app_yz = Apply(sfv, yr, zr)
    succ_zr_yr = SuccDef(zr, yr)
    got_in_yr = apply_thm(got_dom_from, [yr],
        Exists(yds, Apply(sfv, yr, yds)), In(yr, w),
        eir(ax(app_yz), Apply(sfv, yr, yds), yds, zr))
    got_sc_yr = fl(succ_char, Implies(In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr)))), yr)
    got_fa_yr = mp(got_sc_yr, got_in_yr, In(yr, w),
        Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    got_succ_zr = mp(mp(iff_mp(app_yz, succ_zr_yr, []),
        apply_thm(got_fa_yr, [zr], concl=Iff(app_yz, succ_zr_yr)),
        Iff(app_yz, succ_zr_yr), Implies(app_yz, succ_zr_yr)),
        ax(app_yz), app_yz, succ_zr_yr)
    osc = omega_succ_closed()
    got_in_zr = apply_thm(osc, [w], omega_w,
        Forall(yr, Implies(In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))))),
        ax(omega_w))
    got_in_zr = apply_thm(got_in_zr, [yr], In(yr, w),
        Forall(zr, Implies(succ_zr_yr, In(zr, w))), got_in_yr)
    got_in_zr = apply_thm(got_in_zr, [zr], succ_zr_yr, In(zr, w), got_succ_zr)
    succ_qr_zr = SuccDef(qr, zr)
    got_app_zr = mp(mp(iff_mp_rev(Apply(sfv, zr, qr), succ_qr_zr, []),
        apply_thm(mp(fl(succ_char, Implies(In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))), zr),
            got_in_zr, In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))),
            [qr], concl=Iff(Apply(sfv, zr, qr), succ_qr_zr)),
        Iff(Apply(sfv, zr, qr), succ_qr_zr), Implies(succ_qr_zr, Apply(sfv, zr, qr))),
        ax(succ_qr_zr), succ_qr_zr, Apply(sfv, zr, qr))
    got_se_zr = apply_thm(se, [zr], concl=Exists(qr, succ_qr_zr))
    qr2 = Var()
    got_ex_zr = eir(got_app_zr, Apply(sfv, zr, qr2), qr2, qr)
    got_ex_zr = eel(got_ex_zr, succ_qr_zr, qr)
    got_ex_zr = cut(got_ex_zr, got_ex_zr.sequent.left[-1], got_se_zr)
    ex_q_app = got_ex_zr.sequent.right[0]
    imp_rfc = Implies(app_yz, ex_q_app)
    rem_rfc = [f_ for f_ in got_ex_zr.sequent.left if not same(f_, app_yz)]
    cur_rfc = Proof(Sequent(rem_rfc, [imp_rfc]), 'implies_right', [got_ex_zr], principal=imp_rfc)
    ran_f_closed = Forall(yr, Forall(zr, imp_rfc))
    for var in [zr, yr]:
        body = cur_rfc.sequent.right[0]
        fa = Forall(var, body)
        cur_rfc = Proof(Sequent(cur_rfc.sequent.left, [fa]), 'forall_right', [cur_rfc], principal=fa, term=var)

    dom_closed = And(f_at_a, ran_f_closed)
    all_dc = list(got_fat.sequent.left)
    for f_ in cur_rfc.sequent.left:
        if not any(same(f_, g) for g in all_dc):
            all_dc.append(f_)
    got_dc = mp(apply_thm(and_intro(f_at_a, ran_f_closed, []), [], f_at_a,
        Implies(ran_f_closed, dom_closed), weaken_to(got_fat, all_dc)),
        weaken_to(cur_rfc, all_dc), ran_f_closed, dom_closed)
    got_dc = cut(got_dc, succ_char, got_sc_from)

    # === recursion_theorem → ∃!h. Recursive(h, e, sf, w) ===
    rt = recursion_theorem()
    rec_h = RecDef(hv, ev, sfv, w)
    exu_h = ExistsUnique(hv, rec_h)
    got_rt = apply_thm(rt, [ev, sfv, w], func_sf,
        Implies(dom_closed, Implies(omega_w, exu_h)), got_func_from)
    got_rt = mp(got_rt, got_dc, dom_closed, Implies(omega_w, exu_h))
    got_rt = mp(got_rt, ax(omega_w), omega_w, exu_h)

    # === rec_h_zero_identity: Apply(h, m, m) ===
    rhi = rec_h_zero_identity()
    app_h_mm = Apply(hv, mv, mv)
    got_hmm = apply_thm(rhi, [w, sfv, hv, ev], omega_w,
        Implies(succ_char, Implies(rec_h, Implies(empty_ev,
            Forall(mv, Implies(in_m_w, app_h_mm))))), ax(omega_w))
    got_hmm = mp(got_hmm, ax(succ_char), succ_char,
        Implies(rec_h, Implies(empty_ev, Forall(mv, Implies(in_m_w, app_h_mm)))))
    got_hmm = mp(got_hmm, ax(rec_h), rec_h,
        Implies(empty_ev, Forall(mv, Implies(in_m_w, app_h_mm))))
    got_hmm = mp(got_hmm, ax(empty_ev), empty_ev, Forall(mv, Implies(in_m_w, app_h_mm)))
    got_hmm = apply_thm(got_hmm, [mv], in_m_w, app_h_mm, ax(in_m_w))
    # [succ_char, rec_h, empty_ev, In(m,w), omega_w, axioms] |- Apply(h,m,m)

    # === Package into Plus(e, m, m) with new Plus structure ===
    # sf_all = And(succ_char, And(Function(sf), dom_sub))
    and_rec_app = And(rec_h, app_h_mm)
    got_ra = mp(apply_thm(and_intro(rec_h, app_h_mm, []), [], rec_h,
        Implies(app_h_mm, and_rec_app), ax(rec_h)),
        got_hmm, app_h_mm, and_rec_app)
    and_sf_ra = And(and_sc_fd, and_rec_app)
    got_sfra = mp(apply_thm(and_intro(and_sc_fd, and_rec_app, []), [], and_sc_fd,
        Implies(and_rec_app, and_sf_ra), ax(and_sc_fd)),
        got_ra, and_rec_app, and_sf_ra)
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc2, ysc2, xds2, yds2 = Var(), Var(), Var(), Var()
    sc_pat = Forall(xsc2, Implies(In(xsc2, w), Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2)))))
    sf_all_pat = And(sc_pat, And(FuncDef(sf_var), Forall(xds2, Implies(Exists(yds2, Apply(sf_var, xds2, yds2)), In(xds2, w)))))
    inner_sf = And(sf_all_pat, And(RecDef(hv, ev, sf_var, w), Apply(hv, mv, mv)))
    got_ex_sf = eir(got_sfra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sf_all_pat, And(RecDef(h_var, ev, sf_var, w), Apply(h_var, mv, mv))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    sf_all_w = And(Forall(xsc2, Implies(In(xsc2, w_var), Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2))))),
        And(FuncDef(sf_var), Forall(xds2, Implies(Exists(yds2, Apply(sf_var, xds2, yds2)), In(xds2, w_var)))))
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(sf_all_w, And(RecDef(h_var, ev, sf_var, w_var), Apply(h_var, mv, mv))))))
    got_plus = eir(got_omega_ex, inner_w, w_var, w)

    # === Close existentials ===
    # From ExistsUnique: extract Recursive
    h2v = Var()
    uniq_part = Forall(h2v, Implies(RecDef(h2v, ev, sfv, w), Eq(hv, h2v)))
    and_rec_uniq = And(rec_h, uniq_part)
    got_rec_from = apply_thm(and_elim_left(rec_h, uniq_part, []), [],
        and_rec_uniq, rec_h, ax(and_rec_uniq))

    cur = got_plus
    # Cut rec_h and succ_char with derivations from and_rec_uniq and and_sc_fd:
    cur = cut(cur, rec_h, got_rec_from)
    cur = cut(cur, succ_char, got_sc_from)
    cur = eel(cur, and_rec_uniq, hv)
    cur = cut(cur, cur.sequent.left[-1], got_rt)
    cur = eel(cur, and_sc_fd, sfv)
    cur = cut(cur, cur.sequent.left[-1], got_sp)

    # Discharge and close using goal:
    proof = cur
    g_ev = goal.body.body  # Forall(ev, Implies(omega, ...))
    g_omega = g_ev.body
    g_in_m = g_omega.right
    g_empty = g_in_m.right
    for hh, imp in [(empty_ev, g_empty), (in_m_w, g_in_m), (omega_w, g_omega)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var, fa in [(ev, g_ev), (mv, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'plus_zero_left'
    return proof


def rec_succ_shift():
    """If h1 starts at S(m) and h2 starts at m, then h1(n) = S(h2(n)) for all n in omega.
    Ext, Inf, Sep |- forall w, sf, h1, h2, m, sm.
      Omega(w) -> succ_char(sf,w) -> Recursive(h1,sm,sf,w) -> Recursive(h2,m,sf,w) ->
      Successor(sm,m) -> In(m,w) ->
      forall n. In(n,w) -> forall y,s. Apply(h2,n,y) -> Successor(s,y) -> Apply(h1,n,s)
    Induction on n with P(n) = forall y,s. Apply(h2,n,y) -> Succ(s,y) -> Apply(h1,n,s)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from core.proof import _expand, _subst
    from theorems.axioms import separation
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp, iff_mp_rev, unique_empty, eq_symmetric
    from theorems.sets import unique_successor, successor_exists, eq_successor_transfer
    from theorems.recursion import eq_apply_val_transfer, func_unique_thm

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    h1 = Var(postfix='h1')
    h2 = Var(postfix='h2')
    mv = Var(postfix='m')
    smv = Var(postfix='sm')
    nv = Var(postfix='n')
    yv = Var(postfix='y')
    sv = Var(postfix='s')
    omega_w = Omega(w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h1 = RecDef(h1, smv, sfv, w)
    rec_h2 = RecDef(h2, mv, sfv, w)
    succ_sm_m = SuccDef(smv, mv)
    in_m_w = In(mv, w)

    app_h2_ny = Apply(h2, nv, yv)
    succ_sy = SuccDef(sv, yv)
    app_h1_ns = Apply(h1, nv, sv)
    P_body = Implies(app_h2_ny, Implies(succ_sy, app_h1_ns))
    P_n = Forall(yv, Forall(sv, P_body))

    goal_inner = Forall(nv, Implies(In(nv, w), P_n))

    # === Separation: p = {n in w : P(n)} ===
    pv = Var(postfix='p')
    xv = Var(postfix='xv')
    def P(x):
        return Forall(yv, Forall(sv, Implies(Apply(h2, x, yv), Implies(SuccDef(sv, yv), Apply(h1, x, sv)))))
    char_p_body = Iff(In(xv, pv), And(In(xv, w), P(xv)))
    char_p = Forall(xv, char_p_body)

    sep = separation(P, [h1, h2])
    got_sep = sep
    for term in [h2, h1]:  # reversed order: sep wraps h1 outermost
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)], principal=actual)
    actual = got_sep.sequent.right[0]
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)),
         wl(fl(actual, Exists(pv, char_p), w), *got_sep.sequent.left)],
        principal=actual)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst, Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))
    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst, Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Extract base/step from Recursive ===
    ev_r = Var()
    base_h1 = Forall(ev_r, Implies(Empty(ev_r), Apply(h1, ev_r, smv)))
    base_h2 = Forall(ev_r, Implies(Empty(ev_r), Apply(h2, ev_r, mv)))
    func_h2_f = FuncDef(h2)
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h_tmpl = lambda hh, init: Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hh, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hh, snst, fvalst)))))))))
    xd, yd = Var(), Var()
    dom_sub_tmpl = lambda hh: Forall(xd, Implies(Exists(yd, Apply(hh, xd, yd)), In(xd, w)))

    def extract_base(rec, base_f):
        func = FuncDef(rec.func)
        ds = dom_sub_tmpl(rec.func)
        bs = And(base_f, step_h_tmpl(rec.func, rec.init))
        dbs = And(ds, bs)
        r = apply_thm(and_elim_right(func, dbs, []), [], rec, dbs, ax(rec))
        r = apply_thm(and_elim_right(ds, bs, []), [], dbs, bs, r)
        return apply_thm(and_elim_left(base_f, step_h_tmpl(rec.func, rec.init), []), [], bs, base_f, r)

    got_base_h1 = extract_base(rec_h1, base_h1)  # [rec_h1] |- base_h1
    got_base_h2 = extract_base(rec_h2, base_h2)  # [rec_h2] |- base_h2

    # === Base case: forall e. Empty(e) -> In(e, p) ===
    # P(0) = forall y,s. Apply(h2,0,y) -> Succ(s,y) -> Apply(h1,0,s)
    # h2(0) = m, h1(0) = sm, Succ(sm,m). So Apply(h2,0,y) -> y=m (func_unique).
    # Succ(s,y) = Succ(s,m). unique_successor: s=sm. Apply(h1,0,sm) = Apply(h1,0,s).
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)

    # h2(eb) = m:
    got_h2_eb = apply_thm(got_base_h2, [eb], empty_eb, Apply(h2, eb, mv), ax(empty_eb))
    # h1(eb) = sm:
    got_h1_eb = apply_thm(got_base_h1, [eb], empty_eb, Apply(h1, eb, smv), ax(empty_eb))

    # func_unique on h2: Apply(h2,eb,mv) and Apply(h2,eb,yv) -> Eq(mv,yv)
    fut = func_unique_thm()
    got_func_h2 = apply_thm(and_elim_left(func_h2_f, And(dom_sub_tmpl(h2), And(base_h2, step_h_tmpl(h2, mv))), []),
        [], rec_h2, func_h2_f, ax(rec_h2))
    got_eq_my = apply_thm(fut, [h2, eb, mv, yv], func_h2_f,
        Implies(Apply(h2, eb, mv), Implies(Apply(h2, eb, yv), Eq(mv, yv))),
        got_func_h2)
    got_eq_my = mp(got_eq_my, got_h2_eb, Apply(h2, eb, mv), Implies(Apply(h2, eb, yv), Eq(mv, yv)))
    got_eq_my = mp(got_eq_my, ax(Apply(h2, eb, yv)), Apply(h2, eb, yv), Eq(mv, yv))
    # [rec_h2, Empty(eb), Apply(h2,eb,yv)] |- Eq(mv,yv)

    # unique_successor: Succ(sm,m) and Succ(sv,yv) and Eq(mv,yv) -> Eq(smv,sv)
    # From eq_successor_transfer: Eq(smv,sv') and Eq(mv,yv) and Succ(smv,mv) -> Succ(sv',yv)
    # Then unique_successor: Succ(sv',yv) and Succ(sv,yv) -> Eq(sv',sv). With sv'=smv.
    # Actually simpler: from Eq(mv,yv) + Succ(sm,m) -> Succ(sm,yv) via eq_successor_transfer.
    # Then unique_successor: Succ(sm,yv) + Succ(sv,yv) -> Eq(sm,sv).
    es = eq_symmetric()
    est = eq_successor_transfer()
    # Eq(smv, smv) (reflexive) and Eq(mv, yv) and Succ(smv, mv) -> Succ(smv, yv)
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    got_eq_ss = apply_thm(er, [smv], concl=Eq(smv, smv))
    got_succ_sy = apply_thm(est, [smv, yv, smv, mv], Eq(smv, smv),
        Implies(Eq(yv, mv), Implies(succ_sm_m, SuccDef(smv, yv))), got_eq_ss)
    # Need Eq(yv,mv) from Eq(mv,yv):
    got_eq_ym = apply_thm(es, [mv, yv], Eq(mv, yv), Eq(yv, mv), got_eq_my)
    got_succ_sy = mp(got_succ_sy, got_eq_ym, Eq(yv, mv), Implies(succ_sm_m, SuccDef(smv, yv)))
    got_succ_sy = mp(got_succ_sy, ax(succ_sm_m), succ_sm_m, SuccDef(smv, yv))
    # [..., Succ(sm,m), Apply(h2,eb,yv)] |- Succ(smv, yv)

    # unique_successor: Succ(smv,yv) and Succ(sv,yv) -> Eq(smv,sv)
    us = unique_successor()
    got_eq_smsv = apply_thm(us, [yv, smv, sv], SuccDef(smv, yv),
        Implies(SuccDef(sv, yv), Eq(smv, sv)), got_succ_sy)
    got_eq_smsv = mp(got_eq_smsv, ax(succ_sy), succ_sy, Eq(smv, sv))
    # [...] |- Eq(smv, sv)

    # eq_apply_val_transfer: Eq(smv,sv) -> Apply(h1,eb,smv) -> Apply(h1,eb,sv)
    eavt = eq_apply_val_transfer()
    got_h1_es = apply_thm(eavt, [h1, eb, smv, sv], Eq(smv, sv),
        Implies(Apply(h1, eb, smv), Apply(h1, eb, sv)), got_eq_smsv)
    all_base = list(got_h1_es.sequent.left)
    for f_ in got_h1_eb.sequent.left:
        if not any(same(f_, g) for g in all_base):
            all_base.append(f_)
    got_h1_es = mp(weaken_to(got_h1_es, all_base),
        weaken_to(got_h1_eb, all_base), Apply(h1, eb, smv), Apply(h1, eb, sv))
    # [..., Apply(h2,eb,yv), Succ(sv,yv)] |- Apply(h1,eb,sv)

    # Close: implies_right Succ(sv,yv), forall sv, implies_right Apply(h2,eb,yv), forall yv
    imp_s = Implies(succ_sy, Apply(h1, eb, sv))
    rem_s = [f_ for f_ in got_h1_es.sequent.left if not same(f_, succ_sy)]
    cur_base = Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_h1_es], principal=imp_s)
    imp_y = Implies(Apply(h2, eb, yv), imp_s)
    rem_y = [f_ for f_ in cur_base.sequent.left if not same(f_, Apply(h2, eb, yv))]
    cur_base = Proof(Sequent(rem_y, [imp_y]), 'implies_right', [cur_base], principal=imp_y)
    fa_s = Forall(sv, imp_y)
    # Wait, the P(n) structure is Forall(yv, Forall(sv, Implies(app_h2, Implies(succ, app_h1))))
    # So close: forall sv, forall yv
    p_eb = P(eb)
    cur_base = Proof(Sequent(rem_y, [Forall(sv, imp_s)]), 'forall_right',
        [Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_h1_es], principal=imp_s)],
        principal=Forall(sv, imp_s), term=sv)
    fa_sv_body = Forall(sv, imp_s)
    imp_app_fa = Implies(Apply(h2, eb, yv), fa_sv_body)
    rem_app = [f_ for f_ in cur_base.sequent.left if not same(f_, Apply(h2, eb, yv))]
    cur_base = Proof(Sequent(rem_app, [imp_app_fa]), 'implies_right', [cur_base], principal=imp_app_fa)
    p_eb_formula = Forall(yv, imp_app_fa)
    cur_base = Proof(Sequent(rem_app, [p_eb_formula]), 'forall_right', [cur_base], principal=p_eb_formula, term=yv)
    # cur_base: [...] |- P(eb)

    # In(eb, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(eb, Implies(empty_eb, In(eb, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [eb], empty_eb, In(eb, w), ax(empty_eb))

    # And(In(eb,w), P(eb)) -> In(eb,pv):
    and_wp_eb = And(In(eb, w), p_eb_formula)
    all_b = list(got_eb_w.sequent.left)
    for f_ in cur_base.sequent.left:
        if not any(same(f_, g) for g in all_b):
            all_b.append(f_)
    got_and_b = mp(apply_thm(and_intro(In(eb, w), p_eb_formula, []), [], In(eb, w),
        Implies(p_eb_formula, and_wp_eb), weaken_to(got_eb_w, all_b)),
        weaken_to(cur_base, all_b), p_eb_formula, and_wp_eb)
    got_bwd_eb = char_p_bwd(eb)
    all_bwd = list(got_and_b.sequent.left)
    for f_ in got_bwd_eb.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_eb, all_bwd), got_and_b, and_wp_eb, In(eb, pv))
    imp_base = Implies(empty_eb, In(eb, pv))
    rem_eb = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_eb, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    base_ind = Forall(eb, imp_base)
    proof_base = Proof(Sequent(rem_eb, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=eb)

    # === Step case: In(n, pv) -> Succ(sn, n) -> In(sn, pv) ===
    snv = Var(postfix='sn')
    succ_sn_n = SuccDef(snv, nv)
    in_nv_p = In(nv, pv)

    # From char_p fwd: In(nv,pv) -> And(In(nv,w), P(nv))
    got_fwd_n = char_p_fwd(nv)
    got_and_n = mp(weaken_to(got_fwd_n, [in_nv_p]), ax(in_nv_p), in_nv_p, And(In(nv, w), P(nv)))
    got_in_nw = apply_thm(and_elim_left(In(nv, w), P(nv), []), [],
        And(In(nv, w), P(nv)), In(nv, w), got_and_n)
    got_p_n = apply_thm(and_elim_right(In(nv, w), P(nv), []), [],
        And(In(nv, w), P(nv)), P(nv), got_and_n)
    # [char_p, In(nv,pv)] |- P(nv) = forall y,s. Apply(h2,nv,y) -> Succ(s,y) -> Apply(h1,nv,s)

    # P(S(n)): forall y',s'. Apply(h2,S(n),y') -> Succ(s',y') -> Apply(h1,S(n),s')
    # From rec_step_succ on h2: In(nv,w) -> Apply(h2,nv,y2) -> Succ(snv,nv) -> Succ(sy2,y2) -> Apply(h2,snv,sy2)
    # From rec_step_succ on h1: In(nv,w) -> Apply(h1,nv,s) -> Succ(snv,nv) -> Succ(ss,s) -> Apply(h1,snv,ss)
    # From P(n): Apply(h2,nv,y2) -> Succ(s,y2) -> Apply(h1,nv,s).
    # Need: Apply(h2,snv,y') -> Succ(s',y') -> Apply(h1,snv,s').
    # y' = sf(y2) = S(y2) (from rec_step_succ on h2, need y2 exists + in w)
    # s = S(y2) (from P(n)), so Apply(h1,nv,S(y2))
    # Apply(h1,snv,ss) where ss = sf(s) = sf(S(y2)) = S(S(y2))
    # y' = S(y2), so Succ(s', y') = Succ(s', S(y2)). s' = S(S(y2)) = ss.
    # Apply(h1,snv,ss) = Apply(h1,snv,s'). ✓

    # This is complex. Let me just use rec_step_succ directly for both h1 and h2.
    # Assume Apply(h2,snv,y') and Succ(s',y').
    y_step = Var(postfix='ys')
    s_step = Var(postfix='ss')

    # From Recursive dom_sub on h2: Apply(h2,snv,y') -> In(snv,w). Then snv has a predecessor nv.
    # Hmm, we're given Succ(snv,nv) from the Inductive step. So snv is S(nv). Good.

    # rec_step_succ on h2: needs In(nv,w), In(y2,w), Apply(h2,nv,y2), Succ(snv,nv), Succ(sy2,y2)
    # -> Apply(h2,snv,sy2). From Function(h2): y'=sy2.
    # But we have Apply(h2,snv,y') as hypothesis. Via func_unique: y'=sy2.

    # === Step case: In(nv, pv) -> Succ(snv, nv) -> In(snv, pv) ===
    # Strengthened P: P(n) = ∃y2. Apply(h2,n,y2) ∧ In(y2,w) ∧ ∃s. Succ(s,y2) ∧ Apply(h1,n,s)
    # This is what we need from the induction. But the GOAL theorem uses the simpler
    # ∀y,s. Apply(h2,n,y)->Succ(s,y)->Apply(h1,n,s). We'll derive it from the strengthened P + func_unique.
    # Actually, for the separation predicate, use the strengthened version.

    # REDEFINE P for separation:
    y2v = Var(postfix='y2')
    s2v = Var(postfix='s2')
    def P_strong(x):
        return Exists(y2v, And(Apply(h2, x, y2v), And(In(y2v, w),
            Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, x, s2v))))))

    # Rebuild separation with P_strong:
    char_p_body_s = Iff(In(xv, pv), And(In(xv, w), P_strong(xv)))
    char_p_s = Forall(xv, char_p_body_s)
    sep_s = separation(P_strong, [h1, h2, w])
    got_sep_s = sep_s
    for term in [w, h2, h1]:
        actual_s = got_sep_s.sequent.right[0]
        exp_s = _expand(actual_s)
        inst_s = exp_s.body
        got_sep_s = Proof(Sequent(got_sep_s.sequent.left, [inst_s]), 'cut',
            [wr(got_sep_s, inst_s), wl(fl(actual_s, inst_s, term), *got_sep_s.sequent.left)],
            principal=actual_s)
    actual_s = got_sep_s.sequent.right[0]
    got_sep_s = Proof(Sequent(got_sep_s.sequent.left, [Exists(pv, char_p_s)]), 'cut',
        [wr(got_sep_s, Exists(pv, char_p_s)),
         wl(fl(actual_s, Exists(pv, char_p_s), w), *got_sep_s.sequent.left)],
        principal=actual_s)

    def char_ps_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P_strong(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P_strong(term_x)), []),
            fl(char_p_s, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P_strong(term_x))))
    def char_ps_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P_strong(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P_strong(term_x)), []),
            fl(char_p_s, inst, term_x), inst,
            Implies(And(In(term_x, w), P_strong(term_x)), In(term_x, pv)))

    # -- Rebuild base with P_strong --
    # P_strong(0) = ∃y2. Apply(h2,0,y2) ∧ In(y2,w) ∧ ∃s. Succ(s,y2) ∧ Apply(h1,0,s)
    # y2=m, In(m,w), s=sm, Succ(sm,m), Apply(h1,0,sm)
    and_succ_app = And(succ_sm_m, Apply(h1, eb, smv))
    got_sa = mp(apply_thm(and_intro(succ_sm_m, Apply(h1, eb, smv), []), [],
        succ_sm_m, Implies(Apply(h1, eb, smv), and_succ_app), ax(succ_sm_m)),
        got_h1_eb, Apply(h1, eb, smv), and_succ_app)
    got_ex_s = eir(got_sa, And(SuccDef(s2v, mv), Apply(h1, eb, s2v)), s2v, smv)
    and_in_ex = And(In(mv, w), got_ex_s.sequent.right[0])
    all_ie = list(got_eb_w.sequent.left)
    for f_ in got_ex_s.sequent.left:
        if not any(same(f_, g) for g in all_ie):
            all_ie.append(f_)
    # Need In(mv,w)... but mv is the initial value param, In(mv,w) is a hypothesis.
    got_and_ie = mp(apply_thm(and_intro(In(mv, w), got_ex_s.sequent.right[0], []), [],
        In(mv, w), Implies(got_ex_s.sequent.right[0], and_in_ex), ax(In(mv, w))),
        weaken_to(got_ex_s, [In(mv, w)] + got_ex_s.sequent.left),
        got_ex_s.sequent.right[0], and_in_ex)
    and_app_ie = And(Apply(h2, eb, mv), and_in_ex)
    got_app_ie = mp(apply_thm(and_intro(Apply(h2, eb, mv), and_in_ex, []), [],
        Apply(h2, eb, mv), Implies(and_in_ex, and_app_ie), got_h2_eb),
        got_and_ie, and_in_ex, and_app_ie)
    p_strong_eb = P_strong(eb)
    got_ps_eb = eir(got_app_ie,
        And(Apply(h2, eb, y2v), And(In(y2v, w), Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, eb, s2v))))),
        y2v, mv)
    # got_ps_eb: [...] |- P_strong(eb)

    # In(eb,w) + P_strong(eb) -> In(eb, pv):
    and_wp_eb_s = And(In(eb, w), p_strong_eb)
    all_bs = list(got_eb_w.sequent.left)
    for f_ in got_ps_eb.sequent.left:
        if not any(same(f_, g) for g in all_bs):
            all_bs.append(f_)
    got_and_bs = mp(apply_thm(and_intro(In(eb, w), p_strong_eb, []), [], In(eb, w),
        Implies(p_strong_eb, and_wp_eb_s), weaken_to(got_eb_w, all_bs)),
        weaken_to(got_ps_eb, all_bs), p_strong_eb, and_wp_eb_s)
    got_bwd_ebs = char_ps_bwd(eb)
    all_bwds = list(got_and_bs.sequent.left)
    for f_ in got_bwd_ebs.sequent.left:
        if not any(same(f_, g) for g in all_bwds):
            all_bwds.append(f_)
    got_in_eps = mp(weaken_to(got_bwd_ebs, all_bwds), got_and_bs, and_wp_eb_s, In(eb, pv))
    imp_base_s = Implies(Empty(eb), In(eb, pv))
    rem_ebs = [f_ for f_ in got_in_eps.sequent.left if not same(f_, Empty(eb))]
    proof_base_s = Proof(Sequent(rem_ebs, [imp_base_s]), 'implies_right', [got_in_eps], principal=imp_base_s)
    base_ind_s = Forall(eb, imp_base_s)
    proof_base_s = Proof(Sequent(rem_ebs, [base_ind_s]), 'forall_right', [proof_base_s], principal=base_ind_s, term=eb)

    # -- Step with P_strong --
    # Given In(nv,pv), Succ(snv,nv):
    # From char_ps_fwd: In(nv,w) + P_strong(nv)
    # P_strong(nv) = ∃y2. Apply(h2,nv,y2) ∧ In(y2,w) ∧ ∃s2. Succ(s2,y2) ∧ Apply(h1,nv,s2)
    # Open y2, s2: have Apply(h2,nv,y2), In(y2,w), Succ(s2,y2), Apply(h1,nv,s2)
    # In(s2,w) from omega_succ_closed + In(y2,w) + Succ(s2,y2)
    # rec_step_succ on h2: In(nv,w) + In(y2,w) + Apply(h2,nv,y2) + Succ(snv,nv) + Succ(sy2,y2) -> Apply(h2,snv,sy2)
    #   where sy2 is S(y2). From successor_exists: ∃sy2. Succ(sy2,y2).
    # rec_step_succ on h1: In(nv,w) + In(s2,w) + Apply(h1,nv,s2) + Succ(snv,nv) + Succ(ss2,s2) -> Apply(h1,snv,ss2)
    #   where ss2 is S(s2). From successor_exists: ∃ss2. Succ(ss2,s2).
    # Succ(ss2, sy2): sy2 = S(y2) = s2 (since Succ(s2,y2)). So Succ(ss2, s2) = Succ(ss2, sy2). ✓
    # P_strong(snv) with y2'=sy2, s2'=ss2. In(sy2,w) from omega_succ_closed.

    got_fwd_ns = char_ps_fwd(nv)
    got_and_ns = mp(weaken_to(got_fwd_ns, [In(nv, pv)]), ax(In(nv, pv)),
        In(nv, pv), And(In(nv, w), P_strong(nv)))
    got_in_nws = apply_thm(and_elim_left(In(nv, w), P_strong(nv), []), [],
        And(In(nv, w), P_strong(nv)), In(nv, w), got_and_ns)
    got_ps_n = apply_thm(and_elim_right(In(nv, w), P_strong(nv), []), [],
        And(In(nv, w), P_strong(nv)), P_strong(nv), got_and_ns)
    # [char_p_s, In(nv,pv)] |- P_strong(nv)

    # Work from inside: assume Apply(h2,nv,y2), In(y2,w), Succ(s2,y2), Apply(h1,nv,s2)
    app_h2_ny2 = Apply(h2, nv, y2v)
    in_y2_w = In(y2v, w)
    succ_s2_y2 = SuccDef(s2v, y2v)
    app_h1_ns2 = Apply(h1, nv, s2v)

    # In(s2,w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_s2_w = apply_thm(osc, [w], omega_w,
        Forall(y2v, Implies(in_y2_w, Forall(s2v, Implies(succ_s2_y2, In(s2v, w))))),
        ax(omega_w))
    got_s2_w = apply_thm(got_s2_w, [y2v], in_y2_w,
        Forall(s2v, Implies(succ_s2_y2, In(s2v, w))), ax(in_y2_w))
    got_s2_w = apply_thm(got_s2_w, [s2v], succ_s2_y2, In(s2v, w), ax(succ_s2_y2))
    # [omega_w, In(y2,w), Succ(s2,y2), Inf] |- In(s2,w)

    # successor_exists at y2 and s2:
    sy2v = Var(postfix='sy2')
    ss2v = Var(postfix='ss2')
    se2 = successor_exists()
    got_se_y2 = apply_thm(se2, [y2v], concl=Exists(sy2v, SuccDef(sy2v, y2v)))
    got_se_s2 = apply_thm(se2, [s2v], concl=Exists(ss2v, SuccDef(ss2v, s2v)))

    # rec_step_succ on h2: Apply(h2,snv,sy2)
    rst = rec_step_succ()
    # Peel 4 non-repeating foralls, then fl the rest:
    nv3, pv3, snv3, spv3 = Var(), Var(), Var(), Var()
    inner_rst = Forall(nv3, Forall(pv3, Forall(snv3, Forall(spv3,
        Implies(omega_w, Implies(In(nv3, w), Implies(In(pv3, w), Implies(succ_char,
            Implies(rec_h2, Implies(Apply(h2, nv3, pv3),
                Implies(SuccDef(snv3, nv3), Implies(SuccDef(spv3, pv3),
                    Apply(h2, snv3, spv3)))))))))))))
    got_rst_h2 = apply_thm(rst, [w, mv, sfv, h2], concl=inner_rst)
    # Peel n=nv, p=y2v, sn=snv, sp=sy2v:
    cur_f = inner_rst
    for term in [nv, y2v, snv, sy2v]:
        exp_f = _expand(cur_f)
        next_f = _subst(exp_f.body, exp_f.var, term)
        got_rst_h2 = Proof(Sequent(got_rst_h2.sequent.left, [next_f]), 'cut',
            [wr(got_rst_h2, next_f), wl(fl(cur_f, next_f, term), *got_rst_h2.sequent.left)],
            principal=cur_f)
        cur_f = next_f
    # MP through: omega, In(nv,w), In(y2,w), succ_char, rec_h2, Apply(h2,nv,y2), Succ(snv,nv), Succ(sy2,y2)
    got_rst_h2 = mp(got_rst_h2, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, got_in_nws, In(nv, w), cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(in_y2_w), in_y2_w, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(succ_char), succ_char, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(rec_h2), rec_h2, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(app_h2_ny2), app_h2_ny2, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(succ_sn_n), succ_sn_n, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(SuccDef(sy2v, y2v)), SuccDef(sy2v, y2v), Apply(h2, snv, sy2v))
    # [..., Succ(sy2,y2)] |- Apply(h2,snv,sy2)

    # rec_step_succ on h1: Apply(h1,snv,ss2)
    inner_rst1 = Forall(nv3, Forall(pv3, Forall(snv3, Forall(spv3,
        Implies(omega_w, Implies(In(nv3, w), Implies(In(pv3, w), Implies(succ_char,
            Implies(rec_h1, Implies(Apply(h1, nv3, pv3),
                Implies(SuccDef(snv3, nv3), Implies(SuccDef(spv3, pv3),
                    Apply(h1, snv3, spv3)))))))))))))
    got_rst_h1 = apply_thm(rst, [w, smv, sfv, h1], concl=inner_rst1)
    cur_f = inner_rst1
    for term in [nv, s2v, snv, ss2v]:
        exp_f = _expand(cur_f)
        next_f = _subst(exp_f.body, exp_f.var, term)
        got_rst_h1 = Proof(Sequent(got_rst_h1.sequent.left, [next_f]), 'cut',
            [wr(got_rst_h1, next_f), wl(fl(cur_f, next_f, term), *got_rst_h1.sequent.left)],
            principal=cur_f)
        cur_f = next_f
    got_rst_h1 = mp(got_rst_h1, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, got_in_nws, In(nv, w), cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, got_s2_w, In(s2v, w), cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(succ_char), succ_char, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(rec_h1), rec_h1, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(app_h1_ns2), app_h1_ns2, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(succ_sn_n), succ_sn_n, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(SuccDef(ss2v, s2v)), SuccDef(ss2v, s2v), Apply(h1, snv, ss2v))
    # [..., Succ(ss2,s2)] |- Apply(h1,snv,ss2)

    # In(sy2,w) from omega_succ_closed + In(y2,w):
    got_sy2_w = apply_thm(osc, [w], omega_w,
        Forall(y2v, Implies(in_y2_w, Forall(sy2v, Implies(SuccDef(sy2v, y2v), In(sy2v, w))))),
        ax(omega_w))
    got_sy2_w = apply_thm(got_sy2_w, [y2v], in_y2_w,
        Forall(sy2v, Implies(SuccDef(sy2v, y2v), In(sy2v, w))), ax(in_y2_w))
    got_sy2_w = apply_thm(got_sy2_w, [sy2v], SuccDef(sy2v, y2v), In(sy2v, w), ax(SuccDef(sy2v, y2v)))

    # Succ(ss2, sy2): from Succ(s2,y2) -> s2 = S(y2) -> sy2 = S(y2) = s2
    # -> Succ(ss2, s2) = Succ(ss2, sy2) via eq_successor_transfer
    # From unique_successor: Succ(s2,y2) and Succ(sy2,y2) -> Eq(s2,sy2)
    got_eq_s2sy2 = apply_thm(us, [y2v, s2v, sy2v], succ_s2_y2,
        Implies(SuccDef(sy2v, y2v), Eq(s2v, sy2v)), ax(succ_s2_y2))
    got_eq_s2sy2 = mp(got_eq_s2sy2, ax(SuccDef(sy2v, y2v)), SuccDef(sy2v, y2v), Eq(s2v, sy2v))
    # eq_successor_transfer: Eq(ss2,ss2) + Eq(sy2,s2) + Succ(ss2,s2) -> Succ(ss2,sy2)
    # Peel only 2 (a=ss2v, b=sy2v), then fl c=ss2v and d=s2v manually.
    got_eq_ss = apply_thm(er, [ss2v], concl=Eq(ss2v, ss2v))
    cv, dv = Var(), Var()
    fa_cd = Forall(cv, Forall(dv,
        Implies(Eq(ss2v, cv), Implies(Eq(sy2v, dv), Implies(SuccDef(cv, dv), SuccDef(ss2v, sy2v))))))
    got_est2 = apply_thm(est, [ss2v, sy2v], concl=fa_cd)
    # fl c=ss2v:
    fa_d2 = Forall(dv, Implies(Eq(ss2v, ss2v), Implies(Eq(sy2v, dv), Implies(SuccDef(ss2v, dv), SuccDef(ss2v, sy2v)))))
    got_est_c = Proof(Sequent(got_est2.sequent.left, [fa_d2]), 'cut',
        [wr(got_est2, fa_d2), wl(fl(fa_cd, fa_d2, ss2v), *got_est2.sequent.left)], principal=fa_cd)
    # fl d=s2v:
    inst_d = Implies(Eq(ss2v, ss2v), Implies(Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))))
    got_est_inst = Proof(Sequent(got_est_c.sequent.left, [inst_d]), 'cut',
        [wr(got_est_c, inst_d), wl(fl(fa_d2, inst_d, s2v), *got_est_c.sequent.left)], principal=fa_d2)
    got_succ_ss_sy = mp(got_est_inst, got_eq_ss, Eq(ss2v, ss2v),
        Implies(Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))))
    got_eq_sy2_s2 = apply_thm(es, [s2v, sy2v], Eq(s2v, sy2v), Eq(sy2v, s2v), got_eq_s2sy2)
    got_succ_ss_sy = mp(got_succ_ss_sy, got_eq_sy2_s2, Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v)))
    got_succ_ss_sy = mp(got_succ_ss_sy, ax(SuccDef(ss2v, s2v)), SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))
    # [Succ(s2,y2), Succ(sy2,y2), Succ(ss2,s2)] |- Succ(ss2,sy2)

    # Build P_strong(snv): ∃y2'. Apply(h2,snv,y2') ∧ In(y2',w) ∧ ∃s2'. Succ(s2',y2') ∧ Apply(h1,snv,s2')
    # y2'=sy2, s2'=ss2
    and_succ_app_step = And(SuccDef(ss2v, sy2v), Apply(h1, snv, ss2v))
    all_step_left = []
    for pr in [got_rst_h2, got_rst_h1, got_sy2_w, got_succ_ss_sy]:
        for f_ in pr.sequent.left:
            if not any(same(f_, g) for g in all_step_left):
                all_step_left.append(f_)
    got_sa_step = mp(apply_thm(and_intro(SuccDef(ss2v, sy2v), Apply(h1, snv, ss2v), []), [],
        SuccDef(ss2v, sy2v), Implies(Apply(h1, snv, ss2v), and_succ_app_step),
        weaken_to(got_succ_ss_sy, all_step_left)),
        weaken_to(got_rst_h1, all_step_left), Apply(h1, snv, ss2v), and_succ_app_step)
    got_ex_s_step = eir(got_sa_step, And(SuccDef(s2v, sy2v), Apply(h1, snv, s2v)), s2v, ss2v)
    and_in_ex_step = And(In(sy2v, w), got_ex_s_step.sequent.right[0])
    got_ie_step = mp(apply_thm(and_intro(In(sy2v, w), got_ex_s_step.sequent.right[0], []), [],
        In(sy2v, w), Implies(got_ex_s_step.sequent.right[0], and_in_ex_step),
        weaken_to(got_sy2_w, all_step_left)),
        weaken_to(got_ex_s_step, all_step_left), got_ex_s_step.sequent.right[0], and_in_ex_step)
    and_app_ie_step = And(Apply(h2, snv, sy2v), and_in_ex_step)
    got_app_ie_step = mp(apply_thm(and_intro(Apply(h2, snv, sy2v), and_in_ex_step, []), [],
        Apply(h2, snv, sy2v), Implies(and_in_ex_step, and_app_ie_step),
        weaken_to(got_rst_h2, all_step_left)),
        weaken_to(got_ie_step, all_step_left), and_in_ex_step, and_app_ie_step)
    p_strong_snv = P_strong(snv)
    got_ps_snv = eir(got_app_ie_step,
        And(Apply(h2, snv, y2v), And(In(y2v, w), Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, snv, s2v))))),
        y2v, sy2v)
    # [...lots...] |- P_strong(snv)

    # Close: eel ss2v from Succ(ss2,s2), eel sy2v from Succ(sy2,y2),
    # fold back into P_strong(nv) components, eel y2v, s2v
    # Fold Succ(ss2,s2) + Succ(sy2,y2) back:
    cur_step = got_ps_snv
    cur_step = eel(cur_step, SuccDef(ss2v, s2v), ss2v)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_s2)
    cur_step = eel(cur_step, SuccDef(sy2v, y2v), sy2v)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_y2)

    # Fold app_h1_ns2, succ_s2_y2 into And, eel s2v:
    and_succ_app_n = And(succ_s2_y2, app_h1_ns2)
    for pred, gp in [
        (succ_s2_y2, apply_thm(and_elim_left(succ_s2_y2, app_h1_ns2, []), [], and_succ_app_n, succ_s2_y2, ax(and_succ_app_n))),
        (app_h1_ns2, apply_thm(and_elim_right(succ_s2_y2, app_h1_ns2, []), [], and_succ_app_n, app_h1_ns2, ax(and_succ_app_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_succ_app_n, s2v)
    ex_s2 = cur_step.sequent.left[-1]

    # Fold in_y2_w, ex_s2 into And, then with app_h2_ny2, eel y2v:
    and_in_ex_n = And(in_y2_w, ex_s2)
    for pred, gp in [
        (in_y2_w, apply_thm(and_elim_left(in_y2_w, ex_s2, []), [], and_in_ex_n, in_y2_w, ax(and_in_ex_n))),
        (ex_s2, apply_thm(and_elim_right(in_y2_w, ex_s2, []), [], and_in_ex_n, ex_s2, ax(and_in_ex_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    and_app_in_ex_n = And(app_h2_ny2, and_in_ex_n)
    for pred, gp in [
        (app_h2_ny2, apply_thm(and_elim_left(app_h2_ny2, and_in_ex_n, []), [], and_app_in_ex_n, app_h2_ny2, ax(and_app_in_ex_n))),
        (and_in_ex_n, apply_thm(and_elim_right(app_h2_ny2, and_in_ex_n, []), [], and_app_in_ex_n, and_in_ex_n, ax(and_app_in_ex_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_app_in_ex_n, y2v)
    # P_strong(nv) on left. Cut with got_ps_n:
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_ps_n)

    # In(snv,w) from omega_succ_closed:
    got_snv_w = apply_thm(osc, [w], omega_w,
        Forall(nv, Implies(In(nv, w), Forall(snv, Implies(succ_sn_n, In(snv, w))))),
        ax(omega_w))
    got_snv_w = apply_thm(got_snv_w, [nv], In(nv, w), Forall(snv, Implies(succ_sn_n, In(snv, w))), got_in_nws)
    got_snv_w = apply_thm(got_snv_w, [snv], succ_sn_n, In(snv, w), ax(succ_sn_n))

    # And(In(snv,w), P_strong(snv)) -> In(snv, pv):
    and_wp_snv = And(In(snv, w), p_strong_snv)
    all_sw = list(cur_step.sequent.left)
    for f_ in got_snv_w.sequent.left:
        if not any(same(f_, g) for g in all_sw):
            all_sw.append(f_)
    got_and_sw = mp(apply_thm(and_intro(In(snv, w), p_strong_snv, []), [], In(snv, w),
        Implies(p_strong_snv, and_wp_snv), weaken_to(got_snv_w, all_sw)),
        weaken_to(cur_step, all_sw), p_strong_snv, and_wp_snv)
    got_bwd_snv = char_ps_bwd(snv)
    all_bwd_snv = list(got_and_sw.sequent.left)
    for f_ in got_bwd_snv.sequent.left:
        if not any(same(f_, g) for g in all_bwd_snv):
            all_bwd_snv.append(f_)
    got_in_snp = mp(weaken_to(got_bwd_snv, all_bwd_snv), got_and_sw, and_wp_snv, In(snv, pv))

    # Close step: implies_right Succ(snv,nv), forall snv, implies_right In(nv,pv), forall nv
    imp_succ_s = Implies(succ_sn_n, In(snv, pv))
    rem_ss = [f_ for f_ in got_in_snp.sequent.left if not same(f_, succ_sn_n)]
    cur_s = Proof(Sequent(rem_ss, [imp_succ_s]), 'implies_right', [got_in_snp], principal=imp_succ_s)
    fa_snv = Forall(snv, imp_succ_s)
    cur_s = Proof(Sequent(rem_ss, [fa_snv]), 'forall_right', [cur_s], principal=fa_snv, term=snv)
    imp_inp_s = Implies(In(nv, pv), fa_snv)
    rem_inp = [f_ for f_ in cur_s.sequent.left if not same(f_, In(nv, pv))]
    cur_s = Proof(Sequent(rem_inp, [imp_inp_s]), 'implies_right', [cur_s], principal=imp_inp_s)
    step_ind_s = Forall(nv, imp_inp_s)
    proof_step_s = Proof(Sequent(rem_inp, [step_ind_s]), 'forall_right', [cur_s], principal=step_ind_s, term=nv)

    # === Build Inductive(pv), Subset(pv,w), omega_smallest_inductive ===
    from definitions import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

    all_ind = list(proof_base_s.sequent.left)
    for f_ in proof_step_s.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind_s, step_ind_s, []), [], base_ind_s,
        Implies(step_ind_s, ind_p), weaken_to(proof_base_s, all_ind)),
        weaken_to(proof_step_s, all_ind), step_ind_s, ind_p)

    xsub = Var()
    got_fwd_x = char_ps_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv), And(In(xsub, w), P_strong(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P_strong(xsub), []), [],
        And(In(xsub, w), P_strong(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p_s], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p_s], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w, Implies(hyp_and, eq_pw), ax(omega_w))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # === Extract: In(nv, w) -> P_strong(nv) -> (the goal's P_n) ===
    # From Eq(pv,w): In(nv,w) -> In(nv,pv) -> P_strong(nv)
    # From P_strong(nv): ∃y2. ... -> (∀y,s. Apply(h2,nv,y)->Succ(s,y)->Apply(h1,nv,s)) via func_unique
    # Actually for the extraction, we can derive the weaker P(n) from P_strong(n) + func_unique(h2).
    # But for simplicity, let's just keep P_strong in the goal.
    # The goal becomes: ∀n∈w. P_strong(n). The caller can extract what they need.

    nf = Var(postfix='nf')
    iff_nf = Iff(In(nf, pv), In(nf, w))
    got_iff_nf = Proof(Sequent(got_eq.sequent.left, [iff_nf]), 'cut',
        [wr(got_eq, iff_nf), weaken_to(fl(eq_pw, iff_nf, nf), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_nfp = mp(mp(iff_mp_rev(In(nf, pv), In(nf, w), []),
        got_iff_nf, iff_nf, Implies(In(nf, w), In(nf, pv))),
        ax(In(nf, w)), In(nf, w), In(nf, pv))
    got_fwd_nf = char_ps_fwd(nf)
    all_ext = list(got_in_nfp.sequent.left)
    for f_ in got_fwd_nf.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_ext = mp(weaken_to(got_fwd_nf, all_ext),
        weaken_to(got_in_nfp, all_ext), In(nf, pv), And(In(nf, w), P_strong(nf)))
    got_ps_nf = apply_thm(and_elim_right(In(nf, w), P_strong(nf), []), [],
        And(In(nf, w), P_strong(nf)), P_strong(nf), got_and_ext)
    # [..., In(nf,w)] |- P_strong(nf)

    # eel pv, cut with got_sep_s:
    proof = got_ps_nf
    proof = eel(proof, char_p_s, pv)
    proof = cut(proof, proof.sequent.left[-1], got_sep_s)

    # Discharge and close:
    imp_nf = Implies(In(nf, w), P_strong(nf))
    rem_nf = [f_ for f_ in proof.sequent.left if not same(f_, In(nf, w))]
    proof = Proof(Sequent(rem_nf, [imp_nf]), 'implies_right', [proof], principal=imp_nf)
    fa_nf = Forall(nf, imp_nf)
    proof = Proof(Sequent(rem_nf, [fa_nf]), 'forall_right', [proof], principal=fa_nf, term=nf)
    # Build goal with definition objects for compact display:
    g_imp_inm = Implies(in_m_w, fa_nf)
    g_imp_succ = Implies(succ_sm_m, g_imp_inm)
    g_imp_rech2 = Implies(rec_h2, g_imp_succ)
    g_imp_rech1 = Implies(rec_h1, g_imp_rech2)
    g_imp_sc = Implies(succ_char, g_imp_rech1)
    g_imp_omega = Implies(omega_w, g_imp_sc)
    g_fa_smv = Forall(smv, g_imp_omega)
    g_fa_mv = Forall(mv, g_fa_smv)
    g_fa_h2 = Forall(h2, g_fa_mv)
    g_fa_h1 = Forall(h1, g_fa_h2)
    g_fa_sfv = Forall(sfv, g_fa_h1)
    goal = Forall(w, g_fa_sfv)

    for hh, g_imp in zip([in_m_w, succ_sm_m, rec_h2, rec_h1, succ_char, omega_w],
                         [g_imp_inm, g_imp_succ, g_imp_rech2, g_imp_rech1, g_imp_sc, g_imp_omega]):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    for var, fa in zip([smv, mv, h2, h1, sfv, w],
                       [g_fa_smv, g_fa_mv, g_fa_h2, g_fa_h1, g_fa_sfv, goal]):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal

    proof.name = 'rec_succ_shift'
    return proof


def sf_apply_transfer():
    """Two sf's with succ_char+dom_sub at same w agree on Apply.
    |- forall w, sf1, sf2, x, y.
         succ_char(sf1,w) -> dom_sub(sf1,w) -> succ_char(sf2,w) ->
         Apply(sf1,x,y) -> Apply(sf2,x,y)
    From Apply(sf1,x,y): dom_sub -> In(x,w). succ_char1 fwd -> Succ(y,x). succ_char2 bwd -> Apply(sf2,x,y)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Apply, Successor as SuccDef)

    w = Var(postfix='w')
    sf1 = Var(postfix='sf1')
    sf2 = Var(postfix='sf2')
    xv = Var(postfix='x')
    yv = Var(postfix='y')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    succ_char1 = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sf1, xsc, ysc), SuccDef(ysc, xsc)))))
    succ_char2 = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sf2, xsc, ysc), SuccDef(ysc, xsc)))))
    dom_sub1 = Forall(xds, Implies(Exists(yds, Apply(sf1, xds, yds)), In(xds, w)))
    app1 = Apply(sf1, xv, yv)
    app2 = Apply(sf2, xv, yv)
    succ_yx = SuccDef(yv, xv)

    # dom_sub1: Apply(sf1,x,y) -> In(x,w)
    got_in_xw = apply_thm(ax(dom_sub1), [xv], Exists(yds, Apply(sf1, xv, yds)), In(xv, w),
        eir(ax(app1), Apply(sf1, xv, yds), yds, yv))

    # succ_char1 fwd at (x,y): In(x,w) -> Apply(sf1,x,y) -> Succ(y,x)
    got_fa1 = mp(fl(succ_char1, Implies(In(xv, w), Forall(ysc, Iff(Apply(sf1, xv, ysc), SuccDef(ysc, xv)))), xv),
        got_in_xw, In(xv, w), Forall(ysc, Iff(Apply(sf1, xv, ysc), SuccDef(ysc, xv))))
    iff1 = Iff(app1, succ_yx)
    got_succ = mp(mp(iff_mp(app1, succ_yx, []),
        apply_thm(got_fa1, [yv], concl=iff1), iff1, Implies(app1, succ_yx)),
        ax(app1), app1, succ_yx)

    # succ_char2 bwd at (x,y): In(x,w) -> Succ(y,x) -> Apply(sf2,x,y)
    got_fa2 = mp(fl(succ_char2, Implies(In(xv, w), Forall(ysc, Iff(Apply(sf2, xv, ysc), SuccDef(ysc, xv)))), xv),
        got_in_xw, In(xv, w), Forall(ysc, Iff(Apply(sf2, xv, ysc), SuccDef(ysc, xv))))
    iff2 = Iff(app2, succ_yx)
    got_app2 = mp(mp(iff_mp_rev(app2, succ_yx, []),
        apply_thm(got_fa2, [yv], concl=iff2), iff2, Implies(succ_yx, app2)),
        got_succ, succ_yx, app2)
    # [succ_char1, dom_sub1, succ_char2, Apply(sf1,x,y)] |- Apply(sf2,x,y)

    # Discharge and close:
    proof = got_app2
    for hh in [app1, succ_char2, dom_sub1, succ_char1]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [yv, xv, sf2, sf1, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'sf_apply_transfer'
    return proof


def prove_addition(m_val, n_val):
    """Construct a verified proof that m + n = m+n for specific Python ints.
    |- forall w, m, n. Omega(w) -> Num(m, m_val) -> Num(n, n_val) ->
         exists p. Num(p, p_val) /\ Plus(m, n, p)
    Uses sf_props + recursion_theorem + rec_step_succ chain.
    Right side uses Num/Plus definition objects for clean display."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, Num as NumDef, ExistsUnique)
    from theorems.recursion import recursion_theorem
    from theorems.sets import successor_exists
    from theorems.omega import omega_succ_closed, omega_contains_empty
    from core.proof import _expand, _subst
    from core.zfc import is_axiom as _is_ax

    p_val = m_val + n_val
    w = Var(postfix='w')
    omega_w = Omega(w)
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    # === sf_props ===
    sp = sf_props()
    succ_char = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    and_func_dom = And(func_sf, dom_sub_sf)
    and_sc_fd = And(succ_char, and_func_dom)
    got_sp = apply_thm(sp, [w], concl=Exists(sfv, and_sc_fd))
    got_sc = apply_thm(and_elim_left(succ_char, and_func_dom, []), [], and_sc_fd, succ_char, ax(and_sc_fd))
    got_fd = apply_thm(and_elim_right(succ_char, and_func_dom, []), [], and_sc_fd, and_func_dom, ax(and_sc_fd))
    got_func = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [], and_func_dom, func_sf, got_fd)
    got_dom = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [], and_func_dom, dom_sub_sf, got_fd)

    # === dom_closed for sf at mv (the m variable) ===
    mv = Var(postfix='m')
    sm = Var(postfix='sm')
    se = successor_exists()
    got_se_m = apply_thm(se, [mv], concl=Exists(sm, SuccDef(sm, mv)))
    sc_at_m = Implies(In(mv, w), Forall(ysc, Iff(Apply(sfv, mv, ysc), SuccDef(ysc, mv))))
    got_fa_m = mp(fl(succ_char, sc_at_m, mv), ax(In(mv, w)), In(mv, w),
        Forall(ysc, Iff(Apply(sfv, mv, ysc), SuccDef(ysc, mv))))
    iff_m = Iff(Apply(sfv, mv, sm), SuccDef(sm, mv))
    got_app_m = mp(mp(iff_mp_rev(Apply(sfv, mv, sm), SuccDef(sm, mv), []),
        apply_thm(got_fa_m, [sm], concl=iff_m), iff_m,
        Implies(SuccDef(sm, mv), Apply(sfv, mv, sm))),
        ax(SuccDef(sm, mv)), SuccDef(sm, mv), Apply(sfv, mv, sm))
    zfa = Var()
    got_fat = eir(got_app_m, Apply(sfv, mv, zfa), zfa, sm)
    got_fat = eel(got_fat, SuccDef(sm, mv), sm)
    got_fat = cut(got_fat, got_fat.sequent.left[-1], got_se_m)
    f_at_a = Exists(zfa, Apply(sfv, mv, zfa))

    # ran_f_closed (same as plus_zero_right):
    yr, zr, qr = Var(postfix='yr'), Var(postfix='zr'), Var(postfix='qr')
    app_yz = Apply(sfv, yr, zr)
    succ_zr_yr = SuccDef(zr, yr)
    got_in_yr = apply_thm(got_dom, [yr], Exists(yds, Apply(sfv, yr, yds)), In(yr, w),
        eir(ax(app_yz), Apply(sfv, yr, yds), yds, zr))
    got_fa_yr = mp(fl(succ_char, Implies(In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr)))), yr),
        got_in_yr, In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    got_succ_zr = mp(mp(iff_mp(app_yz, succ_zr_yr, []),
        apply_thm(got_fa_yr, [zr], concl=Iff(app_yz, succ_zr_yr)),
        Iff(app_yz, succ_zr_yr), Implies(app_yz, succ_zr_yr)),
        ax(app_yz), app_yz, succ_zr_yr)
    osc = omega_succ_closed()
    got_in_zr = apply_thm(osc, [w], omega_w,
        Forall(yr, Implies(In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))))), ax(omega_w))
    got_in_zr = apply_thm(got_in_zr, [yr], In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))), got_in_yr)
    got_in_zr = apply_thm(got_in_zr, [zr], succ_zr_yr, In(zr, w), got_succ_zr)
    succ_qr_zr = SuccDef(qr, zr)
    got_app_zr = mp(mp(iff_mp_rev(Apply(sfv, zr, qr), succ_qr_zr, []),
        apply_thm(mp(fl(succ_char, Implies(In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))), zr),
            got_in_zr, In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))),
            [qr], concl=Iff(Apply(sfv, zr, qr), succ_qr_zr)),
        Iff(Apply(sfv, zr, qr), succ_qr_zr), Implies(succ_qr_zr, Apply(sfv, zr, qr))),
        ax(succ_qr_zr), succ_qr_zr, Apply(sfv, zr, qr))
    got_se_zr = apply_thm(se, [zr], concl=Exists(qr, succ_qr_zr))
    qr2 = Var()
    got_ex_zr = eir(got_app_zr, Apply(sfv, zr, qr2), qr2, qr)
    got_ex_zr = eel(got_ex_zr, succ_qr_zr, qr)
    got_ex_zr = cut(got_ex_zr, got_ex_zr.sequent.left[-1], got_se_zr)
    ex_q_app = got_ex_zr.sequent.right[0]
    imp_rfc = Implies(app_yz, ex_q_app)
    rem_rfc = [f_ for f_ in got_ex_zr.sequent.left if not same(f_, app_yz)]
    cur_rfc = Proof(Sequent(rem_rfc, [imp_rfc]), 'implies_right', [got_ex_zr], principal=imp_rfc)
    ran_f_closed = Forall(yr, Forall(zr, imp_rfc))
    for var in [zr, yr]:
        body = cur_rfc.sequent.right[0]
        fa = Forall(var, body)
        cur_rfc = Proof(Sequent(cur_rfc.sequent.left, [fa]), 'forall_right', [cur_rfc], principal=fa, term=var)
    dom_closed = And(f_at_a, ran_f_closed)
    all_dc = list(got_fat.sequent.left)
    for f_ in cur_rfc.sequent.left:
        if not any(same(f_, g) for g in all_dc):
            all_dc.append(f_)
    got_dc = mp(apply_thm(and_intro(f_at_a, ran_f_closed, []), [], f_at_a,
        Implies(ran_f_closed, dom_closed), weaken_to(got_fat, all_dc)),
        weaken_to(cur_rfc, all_dc), ran_f_closed, dom_closed)
    got_dc = cut(got_dc, succ_char, got_sc)

    # === recursion_theorem -> h ===
    rt = recursion_theorem()
    rec_h = RecDef(hv, mv, sfv, w)
    exu_h = ExistsUnique(hv, rec_h)
    got_rt = apply_thm(rt, [mv, sfv, w], func_sf,
        Implies(dom_closed, Implies(omega_w, exu_h)), got_func)
    got_rt = mp(got_rt, got_dc, dom_closed, Implies(omega_w, exu_h))
    got_rt = mp(got_rt, ax(omega_w), omega_w, exu_h)

    # Extract Recursive from ExistsUnique:
    h2v = Var()
    uniq_part = Forall(h2v, Implies(RecDef(h2v, mv, sfv, w), Eq(hv, h2v)))
    and_rec_uniq = And(rec_h, uniq_part)
    got_rec = apply_thm(and_elim_left(rec_h, uniq_part, []), [], and_rec_uniq, rec_h, ax(and_rec_uniq))

    # Extract base: Apply(hv, 0, mv)
    ev_r = Var()
    base_h = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, mv)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_bs)
    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs, []), [], rec_h, and_dom_bs, got_rec)
    got_bs = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [], and_dom_bs, and_bs, got_dom_bs)
    got_step = apply_thm(and_elim_right(base_h, step_h, []), [], and_bs, step_h, got_bs)
    got_base = apply_thm(and_elim_left(base_h, step_h, []), [], and_bs, base_h, got_bs)

    # === Chain: compute h(0)=mv, h(1)=S(mv), ..., h(n_val)=mv+n_val ===
    vals = [Var(postfix=f'v{k}') for k in range(n_val + 1)]
    nums_n = [Var(postfix=f'k{k}') for k in range(n_val + 1)]

    # Base: Apply(hv, nums_n[0], mv) from Recursive base + Empty(nums_n[0])
    got_app_0 = apply_thm(got_base, [nums_n[0]], Empty(nums_n[0]), Apply(hv, nums_n[0], mv), ax(Empty(nums_n[0])))

    oce = omega_contains_empty()
    cur_app = got_app_0
    cur_n = nums_n[0]
    cur_val = mv

    # In(nums_n[0], w) from omega_contains_empty:
    got_in_0 = apply_thm(oce, [w], omega_w, Forall(nums_n[0], Implies(Empty(nums_n[0]), In(nums_n[0], w))), ax(omega_w))
    got_in_0 = apply_thm(got_in_0, [nums_n[0]], Empty(nums_n[0]), In(nums_n[0], w), ax(Empty(nums_n[0])))
    cur_in_n = got_in_0
    cur_in_val = ax(In(mv, w))

    rst = rec_step_succ()

    for k in range(n_val):
        next_n = nums_n[k + 1]
        next_val = vals[k + 1] if k + 1 < n_val else vals[n_val]
        succ_nn = SuccDef(next_n, cur_n)
        succ_vv = SuccDef(next_val, cur_val)

        nv2, pv2, snv2, spv2 = Var(), Var(), Var(), Var()
        inner_rst = Forall(nv2, Forall(pv2, Forall(snv2, Forall(spv2,
            Implies(omega_w, Implies(In(nv2, w), Implies(In(pv2, w), Implies(succ_char,
                Implies(rec_h, Implies(Apply(hv, nv2, pv2),
                    Implies(SuccDef(snv2, nv2), Implies(SuccDef(spv2, pv2),
                        Apply(hv, snv2, spv2)))))))))))))
        got_rst_k = apply_thm(rst, [w, mv, sfv, hv], concl=inner_rst)
        cur_f = inner_rst
        for term in [cur_n, cur_val, next_n, next_val]:
            exp_f = _expand(cur_f)
            next_f = _subst(exp_f.body, exp_f.var, term)
            got_rst_k = Proof(Sequent(got_rst_k.sequent.left, [next_f]), 'cut',
                [wr(got_rst_k, next_f), wl(fl(cur_f, next_f, term), *got_rst_k.sequent.left)],
                principal=cur_f)
            cur_f = next_f
        # MP through: omega, In(cur_n,w), In(cur_val,w), succ_char, rec_h, Apply, Succ_n, Succ_v
        got_rst_k = mp(got_rst_k, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
        all_k = list(got_rst_k.sequent.left)
        for f_ in cur_in_n.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        for f_ in cur_in_val.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        for f_ in cur_app.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        got_rst_k = mp(weaken_to(got_rst_k, all_k), weaken_to(cur_in_n, all_k), In(cur_n, w), cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(cur_in_val, all_k), In(cur_val, w), cur_f.right); cur_f = cur_f.right
        # Use got_sc (derived from and_sc_fd) instead of ax(succ_char):
        got_rst_k = mp(got_rst_k, weaken_to(got_sc, all_k), succ_char, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(got_rec, all_k), rec_h, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(cur_app, all_k), Apply(hv, cur_n, cur_val), cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, ax(succ_nn), succ_nn, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, ax(succ_vv), succ_vv, Apply(hv, next_n, next_val))

        got_in_next_n = apply_thm(osc, [w], omega_w,
            Forall(cur_n, Implies(In(cur_n, w), Forall(next_n, Implies(succ_nn, In(next_n, w))))), ax(omega_w))
        got_in_next_n = apply_thm(got_in_next_n, [cur_n], In(cur_n, w),
            Forall(next_n, Implies(succ_nn, In(next_n, w))), cur_in_n)
        got_in_next_n = apply_thm(got_in_next_n, [next_n], succ_nn, In(next_n, w), ax(succ_nn))

        got_in_next_val = apply_thm(osc, [w], omega_w,
            Forall(cur_val, Implies(In(cur_val, w), Forall(next_val, Implies(succ_vv, In(next_val, w))))), ax(omega_w))
        got_in_next_val = apply_thm(got_in_next_val, [cur_val], In(cur_val, w),
            Forall(next_val, Implies(succ_vv, In(next_val, w))), cur_in_val)
        got_in_next_val = apply_thm(got_in_next_val, [next_val], succ_vv, In(next_val, w), ax(succ_vv))

        cur_app = got_rst_k
        cur_n = next_n
        cur_val = next_val
        cur_in_n = got_in_next_n
        cur_in_val = got_in_next_val

    nv_final = cur_n
    pv_final = cur_val
    app_final = Apply(hv, nv_final, pv_final)

    # === Build Plus(mv, nv_final, pv_final) ===
    and_rec_app = And(rec_h, app_final)
    got_ra = mp(apply_thm(and_intro(rec_h, app_final, []), [], rec_h,
        Implies(app_final, and_rec_app), weaken_to(got_rec, cur_app.sequent.left)),
        cur_app, app_final, and_rec_app)
    and_sf_ra = And(and_sc_fd, and_rec_app)
    got_sfra = mp(apply_thm(and_intro(and_sc_fd, and_rec_app, []), [], and_sc_fd,
        Implies(and_rec_app, and_sf_ra), ax(and_sc_fd)),
        got_ra, and_rec_app, and_sf_ra)
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc3, ysc3, xds3, yds3 = Var(), Var(), Var(), Var()
    sc_pat = Forall(xsc3, Implies(In(xsc3, w), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3)))))
    sf_all_pat = And(sc_pat, And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w)))))
    inner_sf = And(sf_all_pat, And(RecDef(hv, mv, sf_var, w), Apply(hv, nv_final, pv_final)))
    got_ex_sf = eir(got_sfra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sf_all_pat, And(RecDef(h_var, mv, sf_var, w), Apply(h_var, nv_final, pv_final))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    sf_all_w = And(Forall(xsc3, Implies(In(xsc3, w_var), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3))))),
        And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w_var)))))
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(sf_all_w, And(RecDef(h_var, mv, sf_var, w_var), Apply(h_var, nv_final, pv_final))))))
    got_plus = eir(got_omega_ex, inner_w, w_var, w)
    # got_plus: [...] |- PlusDef(mv, nv_final, pv_final)

    # === Step A: Close existentials for structural hypotheses ===
    # Following plus_zero_right pattern: eel hv from and_rec_uniq, cut with got_rt;
    # eel sfv from and_sc_fd, cut with got_sp.
    cur = got_plus
    cur = eel(cur, and_rec_uniq, hv)
    cur = cut(cur, cur.sequent.left[-1], got_rt)
    cur = eel(cur, and_sc_fd, sfv)
    cur = cut(cur, cur.sequent.left[-1], got_sp)
    # Now structural hypotheses (and_rec_uniq, and_sc_fd) are eliminated.
    # Left has: [axioms, omega_w, Empty(nums_n[0]), Succ(nums_n[k+1],nums_n[k])...,
    #            In(mv,w), Succ(vals[k+1],vals[k])...]

    # === Step B: Close n-chain into Num(nv_final, n_val) ===
    # n-chain: Empty(nums_n[0]), Succ(nums_n[1],nums_n[0]), ..., Succ(nv_final,nums_n[n_val-1])
    # Close from bottom up: combine Empty+Succ into And, eel to get Num.
    if n_val == 0:
        # nv_final = nums_n[0], Num(nv_final, 0) = Empty(nv_final) already on left
        pass
    else:
        for j in range(1, n_val + 1):
            # At this point, Num(nums_n[j-1], j-1) and Succ(nums_n[j], nums_n[j-1]) are on left
            # (For j=1: Num(nums_n[0],0) = Empty(nums_n[0]) and Succ(nums_n[1],nums_n[0]))
            prev_var = nums_n[j - 1]
            cur_var = nums_n[j]
            num_prev = NumDef(prev_var, j - 1)
            succ_cur = SuccDef(cur_var, prev_var)
            and_np_sc = And(num_prev, succ_cur)

            # Replace num_prev on left with and_np_sc via cut:
            # Need: [and_np_sc] |- num_prev
            got_np = apply_thm(and_elim_left(num_prev, succ_cur, []), [],
                and_np_sc, num_prev, ax(and_np_sc))
            cur = cut(cur, num_prev, got_np)

            # Replace succ_cur on left with and_np_sc via cut:
            # Need: [and_np_sc] |- succ_cur
            got_sc_j = apply_thm(and_elim_right(num_prev, succ_cur, []), [],
                and_np_sc, succ_cur, ax(and_np_sc))
            cur = cut(cur, succ_cur, got_sc_j)

            # eel prev_var: And(num_prev, succ_cur) -> Exists(prev_var, And(...)) = Num(cur_var, j)
            cur = eel(cur, and_np_sc, prev_var)
    # Now the n-chain is closed: Num(nv_final, n_val) is on the left.

    # === Step C: Derive In(mv, w) from Num(mv, m_val) + Omega(w) ===
    # Build proof: [Num(mv, m_val), Omega(w), axioms] |- In(mv, w)
    # Then cut In(mv, w) on cur's left.
    def _num_in_omega(var, k):
        """Build proof: [Num(var, k), Omega(w), axioms] |- In(var, w)"""
        if k == 0:
            # Num(var, 0) = Empty(var)
            got = apply_thm(oce, [w], omega_w,
                Forall(var, Implies(Empty(var), In(var, w))), ax(omega_w))
            got = apply_thm(got, [var], Empty(var), In(var, w), ax(NumDef(var, 0)))
            return got
        else:
            prev = Var(postfix=f'np{k}')
            num_prev = NumDef(prev, k - 1)
            succ_v_prev = SuccDef(var, prev)
            and_form = And(num_prev, succ_v_prev)

            # Recursively get In(prev, w) from Num(prev, k-1)
            got_in_prev = _num_in_omega(prev, k - 1)
            # [Num(prev, k-1), Omega(w), axioms] |- In(prev, w)

            # Get Num(prev, k-1) from And(Num(prev,k-1), Succ(var,prev)):
            got_np = apply_thm(and_elim_left(num_prev, succ_v_prev, []), [],
                and_form, num_prev, ax(and_form))
            # Replace Num(prev, k-1) on left of got_in_prev with and_form:
            got_in_prev = cut(got_in_prev, num_prev, got_np)
            # [and_form, Omega(w), axioms] |- In(prev, w)

            # Get Succ(var, prev) from and_form:
            got_succ = apply_thm(and_elim_right(num_prev, succ_v_prev, []), [],
                and_form, succ_v_prev, ax(and_form))

            # omega_succ_closed: Omega(w) -> In(prev, w) -> Succ(var, prev) -> In(var, w)
            got_in_var = apply_thm(osc, [w], omega_w,
                Forall(prev, Implies(In(prev, w), Forall(var, Implies(succ_v_prev, In(var, w))))),
                ax(omega_w))
            got_in_var = apply_thm(got_in_var, [prev], In(prev, w),
                Forall(var, Implies(succ_v_prev, In(var, w))), got_in_prev)
            got_in_var = apply_thm(got_in_var, [var], succ_v_prev, In(var, w), got_succ)
            # [and_form, Omega(w), axioms] |- In(var, w)

            # eel prev to get Exists(prev, and_form) = Num(var, k) on left:
            got_in_var = eel(got_in_var, and_form, prev)
            # [Num(var, k), Omega(w), axioms] |- In(var, w)
            return got_in_var

    got_in_mv = _num_in_omega(mv, m_val)
    # [Num(mv, m_val), Omega(w), axioms] |- In(mv, w)
    num_m = NumDef(mv, m_val)
    cur = cut(cur, In(mv, w), got_in_mv)
    # In(mv, w) is replaced by Num(mv, m_val) + Omega(w) on the left.

    # === Step D: Eliminate val-chain Succ hypotheses ===
    # Val-chain: Succ(vals[1], mv), Succ(vals[2], vals[1]), ..., Succ(pv_final, vals[n_val-1])
    # These are on the left from ax(succ_vv) calls.
    # After building Num(pv_final, p_val) on the right and eir'ing pv_final,
    # we can eel each val var and cut with successor_exists.
    # But first we need to build Num(pv_final, p_val) on the right BEFORE eir'ing.

    # === Step E: Build Num(pv_final, p_val) on the right ===
    # Num(pv_final, p_val) is built from:
    #   Num(mv, m_val) (on left) + Succ(vals[1], mv), ..., Succ(pv_final, vals[n_val-1]) (on left)
    # Strategy: prove Num(pv_final, p_val) on the right using these left hypotheses.
    # Num(vals[0], m_val) = Num(mv, m_val) -- ax from left
    # Num(vals[1], m_val+1) = Exists(prev, And(Num(prev, m_val), Succ(vals[1], prev)))
    #   with prev=mv as witness: And(Num(mv, m_val), Succ(vals[1], mv))
    #   then eir mv -> Num(vals[1], m_val+1)
    # ... continue for each val

    # Build Num(pv_final, p_val) on the right side of cur.
    # We'll build a separate proof of Num(pv_final, p_val) and combine with Plus via and_intro.

    # Build right-side Num proof incrementally:
    if n_val == 0:
        # pv_final = mv (or vals[0]... but vals[0] is unused, pv_final = mv)
        # Num(pv_final, p_val) = Num(mv, m_val) = num_m, which is on the left
        got_num_p = ax(num_m)
        # [Num(mv, m_val)] |- Num(mv, m_val)
        got_num_p = weaken_to(got_num_p, cur.sequent.left)
    else:
        # Start with Num(mv, m_val) from left
        # For each k from 0 to n_val-1:
        #   have Num(vals[k] or mv, m_val+k) on right
        #   have Succ(vals[k+1], vals[k] or mv) on left
        #   build And(Num(..., m_val+k), Succ(vals[k+1], ...)) on right
        #   eir the previous var -> Num(vals[k+1], m_val+k+1) on right

        # Proof of Num(mv, m_val) on right (from left hypothesis):
        cur_num_proof = weaken_to(ax(num_m), cur.sequent.left)
        cur_num_var = mv
        cur_num_val = m_val

        for k in range(n_val):
            next_v = vals[k + 1] if k + 1 < n_val else pv_final
            succ_next = SuccDef(next_v, cur_num_var)
            num_cur = NumDef(cur_num_var, cur_num_val)
            and_num_succ = And(num_cur, succ_next)

            # Build And(Num(cur_num_var, cur_num_val), Succ(next_v, cur_num_var)) on right:
            got_succ_r = weaken_to(ax(succ_next), cur.sequent.left)
            got_and = mp(apply_thm(and_intro(num_cur, succ_next, []), [],
                num_cur, Implies(succ_next, and_num_succ), cur_num_proof),
                got_succ_r, succ_next, and_num_succ)

            # eir cur_num_var -> Exists(prev, And(Num(prev, cur_num_val), Succ(next_v, prev)))
            ex_var = Var()
            ex_body = And(NumDef(ex_var, cur_num_val), SuccDef(next_v, ex_var))
            got_ex = eir(got_and, ex_body, ex_var, cur_num_var)
            # got_ex: [...] |- Exists(ex_var, And(Num(ex_var, cur_num_val), Succ(next_v, ex_var)))
            # This is same as Num(next_v, cur_num_val + 1)

            cur_num_proof = got_ex
            cur_num_var = next_v
            cur_num_val = cur_num_val + 1

        got_num_p = cur_num_proof
    # got_num_p: [left hyps] |- Num(pv_final, p_val)

    # === Step F: Combine Num(pv_final, p_val) and Plus(mv, nv_final, pv_final) ===
    plus_result = PlusDef(mv, nv_final, pv_final)
    num_p = NumDef(pv_final, p_val)
    and_num_plus = And(num_p, plus_result)

    # cur has: [left] |- plus_result (same as Plus(mv, nv_final, pv_final))
    # got_num_p has: [left'] |- num_p
    # Merge and build And:
    all_left = list(cur.sequent.left)
    for f_ in got_num_p.sequent.left:
        if not any(same(f_, g) for g in all_left):
            all_left.append(f_)
    got_combined = mp(apply_thm(and_intro(num_p, plus_result, []), [],
        num_p, Implies(plus_result, and_num_plus), weaken_to(got_num_p, all_left)),
        weaken_to(cur, all_left), plus_result, and_num_plus)
    # got_combined: [all_left] |- And(Num(pv_final, p_val), Plus(mv, nv_final, pv_final))

    # === Step G: Exists intro for pv_final ===
    pv_result = Var(postfix='pv')
    ex_body = And(NumDef(pv_result, p_val), PlusDef(mv, nv_final, pv_result))
    got_ex_p = eir(got_combined, ex_body, pv_result, pv_final)
    # got_ex_p: [all_left] |- Exists(pv_result, And(Num(pv_result, p_val), Plus(mv, nv_final, pv_result)))

    # === Step H: Eliminate val-chain Succs via eel + cut with successor_exists ===
    # After eir'ing pv_final, it's no longer free in the right.
    # Val-chain Succs: Succ(vals[k+1], vals[k]) for k=0..n_val-1 where vals[0]=mv.
    # But vals[k+1] for k < n_val-1 are intermediate vars only in these Succ formulas.
    # pv_final = vals[n_val] was just eir'd.
    # We eel in reverse order: vals[n_val], vals[n_val-1], ..., vals[1]
    # (vals[0] = mv is in the goal, so we don't eel it.)
    proof = got_ex_p
    for k in range(n_val - 1, -1, -1):
        prev_v = vals[k] if k > 0 else mv
        next_v = vals[k + 1] if k + 1 < n_val else pv_final
        succ_form = SuccDef(next_v, prev_v)
        if any(same(succ_form, f_) for f_ in proof.sequent.left):
            # eel next_v from succ_form (if next_v not free in right or other left)
            proof = eel(proof, succ_form, next_v)
            # Now left has Exists(next_v, Succ(next_v, prev_v))
            # Cut with successor_exists:
            got_se_k = apply_thm(se, [prev_v], concl=Exists(next_v, SuccDef(next_v, prev_v)))
            proof = cut(proof, proof.sequent.left[-1], got_se_k)

    # === Step I: Eliminate n-chain Empty (for n_val=0, nums_n[0] Empty is still there) ===
    # After Step B, if n_val > 0, n-chain is closed into Num(nv_final, n_val).
    # If n_val = 0, nv_final = nums_n[0] and Empty(nv_final) = Num(nv_final, 0) is on left.
    # In either case, Num(nv_final, n_val) should be on the left.

    # === Step J: Discharge hypotheses and close with forall ===
    # Goal: forall m, n. Num(m, m_val) -> Num(n, n_val) -> exists p. Num(p, p_val) /\ Plus(m, n, p)
    # No w — use omega_exists to eliminate Omega(w) internally.
    num_n = NumDef(nv_final, n_val)
    ex_goal = Exists(pv_result, And(NumDef(pv_result, p_val), PlusDef(mv, nv_final, pv_result)))
    imp_num_n = Implies(num_n, ex_goal)
    imp_num_m = Implies(num_m, imp_num_n)
    fa_nv = Forall(nv_final, imp_num_m)
    fa_mv = Forall(mv, fa_nv)
    goal = fa_mv

    # Discharge Num hypotheses:
    for hh, imp in [(num_n, imp_num_n), (num_m, imp_num_m)]:
        if any(same(hh, f_) for f_ in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    # Eliminate Omega(w): eel w from Omega(w), cut with omega_exists
    from theorems.omega import omega_exists
    if any(same(omega_w, f_) for f_ in proof.sequent.left):
        proof = eel(proof, omega_w, w)
        oe = omega_exists()
        proof = cut(proof, proof.sequent.left[-1], oe)

    # Discharge any remaining non-axiom hypotheses:
    non_ax = [f_ for f_ in proof.sequent.left if not _is_ax(f_)]
    for hh in non_ax:
        imp = Implies(hh, proof.sequent.right[0])
        rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
        proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    # Close foralls using goal sub-formulas:
    for var, fa in [(nv_final, fa_nv), (mv, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal, \
        f"Goal mismatch: got {proof.sequent.right[0]}"
    proof.name = f'plus_{m_val}_{n_val}'
    return proof


def plus_comm():
    """Commutativity of addition: m + n = n + m.
    |- forall w, m, n, p.
         Omega(w) -> In(m, w) -> In(n, w) ->
         Plus(m, n, p) -> Plus(n, m, p)
    Induction on n with P(n) = forall q. Apply(h_m,n,q) ->
      exists h_n. Recursive(h_n,n,sf,w) /\\ Apply(h_n,m,q).
    Base: rec_h_zero_identity.  Step: rec_succ_shift + rec_step_succ."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, ExistsUnique)
    from core.proof import _expand, _subst
    from theorems.axioms import separation
    from theorems.recursion import recursion_theorem, eq_apply_val_transfer
    from theorems.sets import omega_unique, successor_exists, eq_successor_transfer
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.logic import (unique_empty, eq_symmetric, eq_reflexive)

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

    # ====================================================================
    # Section 1: Open Plus(m,n,p) to get wv, hv, sfv with properties
    # ====================================================================
    # Plus(m,n,p) expands to:
    # exists wv. And(Omega(wv),
    #   exists hv. exists sfv.
    #     And(succ_char(sfv,wv), And(Function(sfv), dom_sub(sfv,wv)))
    #     And(Recursive(hv,m,sfv,wv), Apply(hv,n,p)))
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    sfv = Var(postfix='sfv')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    omega_wv = Omega(wv)
    succ_char = Forall(xsc, Implies(In(xsc, wv),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, wv)))
    and_func_dom = And(func_sf, dom_sub_sf)
    sf_all = And(succ_char, and_func_dom)
    rec_hm = RecDef(hv, m, sfv, wv)
    app_hm_np = Apply(hv, n, p)
    and_rec_app = And(rec_hm, app_hm_np)
    and_sf_ra = And(sf_all, and_rec_app)
    ex_sfv = Exists(sfv, and_sf_ra)
    ex_hv = Exists(hv, ex_sfv)
    and_omega_ex = And(omega_wv, ex_hv)
    # plus_mn expands to Exists(wv, and_omega_ex)

    # We will work with all components on the left and Plus(n,m,p) on the right.
    # At the end, eel wv/hv/sfv and fold the existentials.

    # Extract components from opened Plus:
    got_sc_from = apply_thm(and_elim_left(succ_char, and_func_dom, []), [],
        sf_all, succ_char, ax(sf_all))
    got_fd_from = apply_thm(and_elim_right(succ_char, and_func_dom, []), [],
        sf_all, and_func_dom, ax(sf_all))
    got_func_sf = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        and_func_dom, func_sf, got_fd_from)
    got_dom_sf = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        and_func_dom, dom_sub_sf, got_fd_from)

    got_rec_from = apply_thm(and_elim_left(rec_hm, app_hm_np, []), [],
        and_rec_app, rec_hm, ax(and_rec_app))
    got_app_from = apply_thm(and_elim_right(rec_hm, app_hm_np, []), [],
        and_rec_app, app_hm_np, ax(and_rec_app))

    got_sf_from = apply_thm(and_elim_left(sf_all, and_rec_app, []), [],
        and_sf_ra, sf_all, ax(and_sf_ra))
    got_ra_from = apply_thm(and_elim_right(sf_all, and_rec_app, []), [],
        and_sf_ra, and_rec_app, ax(and_sf_ra))

    got_omega_from = apply_thm(and_elim_left(omega_wv, ex_hv, []), [],
        and_omega_ex, omega_wv, ax(and_omega_ex))
    got_exhv_from = apply_thm(and_elim_right(omega_wv, ex_hv, []), [],
        and_omega_ex, ex_hv, ax(and_omega_ex))

    # ====================================================================
    # Section 2: omega_unique -> Eq(w, wv), transfer In(m,wv), In(n,wv)
    # ====================================================================
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_w_wv = apply_thm(ou, [w, wv], omega_w,
        Implies(omega_wv, eq_w_wv), ax(omega_w))
    got_eq_w_wv = mp(got_eq_w_wv, ax(omega_wv), omega_wv, eq_w_wv)
    # [omega_w, omega_wv, Ext, Inf] |- Eq(w, wv)

    esub = eq_substitution()
    # eq_substitution: ∀a,b,z. Eq(a,b) → Iff(In(a,z), In(b,z))
    # For In(m, w) → In(m, wv):
    # We need Eq(w, wv) → Iff(In(m, w), In(m, wv))  -- but this is In(a,z) where a=w, b=wv, z=m? No.
    # eq_substitution: Eq(a,b) → Iff(In(a,z), In(b,z)). This moves a↔b INSIDE membership.
    # For x ∈ w → x ∈ wv, we need: Eq(w,wv) → Iff(In(x,w), In(x,wv))
    # which is In(x,a) ↔ In(x,b) given Eq(a,b).
    # But eq_substitution gives In(a,z) ↔ In(b,z), i.e., the set argument stays fixed.
    # We need the OTHER direction. From Eq(w,wv): ∀z. Iff(In(z,w), In(z,wv)).
    # This is directly from the definition of Eq (extensionality).
    # Eq(w,wv) = ∀z. Iff(In(z,w), In(z,wv)).
    zz = Var()
    iff_in_m = Iff(In(m, w), In(m, wv))
    got_iff_m = Proof(Sequent(got_eq_w_wv.sequent.left, [iff_in_m]), 'cut',
        [wr(got_eq_w_wv, iff_in_m),
         weaken_to(fl(eq_w_wv, iff_in_m, m), got_eq_w_wv.sequent.left)],
        principal=eq_w_wv)
    in_m_wv = In(m, wv)
    got_in_m_wv = mp(mp(iff_mp(In(m, w), in_m_wv, []),
        got_iff_m, iff_in_m, Implies(In(m, w), in_m_wv)),
        ax(in_m_w), in_m_w, in_m_wv)

    iff_in_n = Iff(In(n, w), In(n, wv))
    got_iff_n = Proof(Sequent(got_eq_w_wv.sequent.left, [iff_in_n]), 'cut',
        [wr(got_eq_w_wv, iff_in_n),
         weaken_to(fl(eq_w_wv, iff_in_n, n), got_eq_w_wv.sequent.left)],
        principal=eq_w_wv)
    in_n_wv = In(n, wv)
    got_in_n_wv = mp(mp(iff_mp(In(n, w), in_n_wv, []),
        got_iff_n, iff_in_n, Implies(In(n, w), in_n_wv)),
        ax(in_n_w), in_n_w, in_n_wv)

    # ====================================================================
    # Section 3: Extract Recursive components for h_m
    # ====================================================================
    func_hm = FuncDef(hv)
    ev_r = Var()
    base_hm = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, m)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_hm = Forall(nst, Implies(In(nst, wv),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_hm = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, wv)))
    and_base_step = And(base_hm, step_hm)
    and_dom_bs = And(dom_sub_hm, and_base_step)

    got_dom_bs = apply_thm(and_elim_right(func_hm, and_dom_bs, []), [],
        rec_hm, and_dom_bs, ax(rec_hm))
    got_base_hm = apply_thm(and_elim_left(base_hm, step_hm, []), [],
        and_base_step,  base_hm,
        apply_thm(and_elim_right(dom_sub_hm, and_base_step, []), [],
            and_dom_bs, and_base_step, got_dom_bs))

    # ====================================================================
    # Section 4: dom_closed for sf (needed by recursion_theorem)
    # ====================================================================
    # ran_f_closed for sf: ∀y,z. Apply(sf,y,z) → ∃q. Apply(sf,z,q)
    # Same as in plus_zero_left lines 1253-1293.
    yr, zr, qr = Var(postfix='yr'), Var(postfix='zr'), Var(postfix='qr')
    app_yz = Apply(sfv, yr, zr)
    succ_zr_yr = SuccDef(zr, yr)
    # dom_sub: Apply(sf,yr,zr) -> In(yr,wv)
    got_in_yr = apply_thm(got_dom_sf, [yr],
        Exists(yds, Apply(sfv, yr, yds)), In(yr, wv),
        eir(ax(app_yz), Apply(sfv, yr, yds), yds, zr))
    # succ_char at yr: In(yr,wv) -> Iff(Apply(sf,yr,zr), Succ(zr,yr))
    got_sc_yr = fl(succ_char, Implies(In(yr, wv),
        Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr)))), yr)
    got_fa_yr = mp(got_sc_yr, got_in_yr, In(yr, wv),
        Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    got_succ_zr = mp(mp(iff_mp(app_yz, succ_zr_yr, []),
        apply_thm(got_fa_yr, [zr], concl=Iff(app_yz, succ_zr_yr)),
        Iff(app_yz, succ_zr_yr), Implies(app_yz, succ_zr_yr)),
        ax(app_yz), app_yz, succ_zr_yr)
    # [succ_char, dom_sub_sf, Apply(sf,yr,zr)] |- Succ(zr, yr)
    osc = omega_succ_closed()
    got_in_zr = apply_thm(osc, [wv], omega_wv,
        Forall(yr, Implies(In(yr, wv), Forall(zr, Implies(succ_zr_yr, In(zr, wv))))),
        ax(omega_wv))
    got_in_zr = apply_thm(got_in_zr, [yr], In(yr, wv),
        Forall(zr, Implies(succ_zr_yr, In(zr, wv))), got_in_yr)
    got_in_zr = apply_thm(got_in_zr, [zr], succ_zr_yr, In(zr, wv), got_succ_zr)
    # In(zr, wv)
    succ_qr_zr = SuccDef(qr, zr)
    got_app_zr = mp(mp(iff_mp_rev(Apply(sfv, zr, qr), succ_qr_zr, []),
        apply_thm(mp(fl(succ_char, Implies(In(zr, wv),
            Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))), zr),
            got_in_zr, In(zr, wv),
            Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))),
            [qr], concl=Iff(Apply(sfv, zr, qr), succ_qr_zr)),
        Iff(Apply(sfv, zr, qr), succ_qr_zr), Implies(succ_qr_zr, Apply(sfv, zr, qr))),
        ax(succ_qr_zr), succ_qr_zr, Apply(sfv, zr, qr))
    se = successor_exists()
    got_se_zr = apply_thm(se, [zr], concl=Exists(qr, succ_qr_zr))
    qr2 = Var()
    got_ex_zr = eir(got_app_zr, Apply(sfv, zr, qr2), qr2, qr)
    got_ex_zr = eel(got_ex_zr, succ_qr_zr, qr)
    got_ex_zr = cut(got_ex_zr, got_ex_zr.sequent.left[-1], got_se_zr)
    ex_q_app = got_ex_zr.sequent.right[0]  # Exists(qr2, Apply(sfv, zr, qr2))
    imp_rfc = Implies(app_yz, ex_q_app)
    rem_rfc = [f_ for f_ in got_ex_zr.sequent.left if not same(f_, app_yz)]
    cur_rfc = Proof(Sequent(rem_rfc, [imp_rfc]), 'implies_right', [got_ex_zr], principal=imp_rfc)
    ran_f_closed = Forall(yr, Forall(zr, imp_rfc))
    for var in [zr, yr]:
        body = cur_rfc.sequent.right[0]
        fa = Forall(var, body)
        cur_rfc = Proof(Sequent(cur_rfc.sequent.left, [fa]), 'forall_right',
            [cur_rfc], principal=fa, term=var)
    # cur_rfc: [succ_char, dom_sub_sf, omega_wv, Inf, Pair] |- ran_f_closed

    # Helper: build dom_closed(sf, init) = And(∃z.Apply(sf,init,z), ran_f_closed) for any init in wv
    def build_dom_closed(init_var, got_in_init_wv):
        """Build dom_closed(sf, init_var) given got_in_init_wv proves In(init_var, wv)."""
        sm_var = Var()
        got_se_init = apply_thm(se, [init_var], concl=Exists(sm_var, SuccDef(sm_var, init_var)))
        sc_at_init = Implies(In(init_var, wv),
            Forall(ysc, Iff(Apply(sfv, init_var, ysc), SuccDef(ysc, init_var))))
        got_fa_init = mp(fl(succ_char, sc_at_init, init_var),
            got_in_init_wv, In(init_var, wv),
            Forall(ysc, Iff(Apply(sfv, init_var, ysc), SuccDef(ysc, init_var))))
        iff_init_sm = Iff(Apply(sfv, init_var, sm_var), SuccDef(sm_var, init_var))
        got_app_init = mp(mp(iff_mp_rev(Apply(sfv, init_var, sm_var),
            SuccDef(sm_var, init_var), []),
            apply_thm(got_fa_init, [sm_var], concl=iff_init_sm),
            iff_init_sm, Implies(SuccDef(sm_var, init_var), Apply(sfv, init_var, sm_var))),
            ax(SuccDef(sm_var, init_var)), SuccDef(sm_var, init_var),
            Apply(sfv, init_var, sm_var))
        zfa2 = Var()
        got_fat = eir(got_app_init, Apply(sfv, init_var, zfa2), zfa2, sm_var)
        got_fat = eel(got_fat, SuccDef(sm_var, init_var), sm_var)
        got_fat = cut(got_fat, got_fat.sequent.left[-1], got_se_init)
        f_at_init = got_fat.sequent.right[0]  # Exists(zfa2, Apply(sfv, init_var, zfa2))

        dc = And(f_at_init, ran_f_closed)
        all_dc = list(got_fat.sequent.left)
        for f_ in cur_rfc.sequent.left:
            if not any(same(f_, g) for g in all_dc):
                all_dc.append(f_)
        got_dc = mp(apply_thm(and_intro(f_at_init, ran_f_closed, []), [],
            f_at_init, Implies(ran_f_closed, dc), weaken_to(got_fat, all_dc)),
            weaken_to(cur_rfc, all_dc), ran_f_closed, dc)
        return got_dc, dc, f_at_init

    # ====================================================================
    # Section 5: Separation-based induction
    # ====================================================================
    # Induction on n over wv.
    # P(x) = ∃q. Apply(hv,x,q) ∧ In(q,wv) ∧
    #         ∃hn. Recursive(hn,x,sfv,wv) ∧ Apply(hn,m,q)
    # Free vars in P besides x: hv, m, sfv, wv.
    # Separation parameters: [hv, m, sfv, wv].

    hn = Var(postfix='hn')
    qv = Var(postfix='q')
    def P(x):
        return Exists(qv, And(Apply(hv, x, qv), And(In(qv, wv),
            Exists(hn, And(RecDef(hn, x, sfv, wv), Apply(hn, m, qv))))))

    pv = Var(postfix='pset')
    xv = Var(postfix='xv')
    char_p_body = Iff(In(xv, pv), And(In(xv, wv), P(xv)))
    char_p = Forall(xv, char_p_body)

    sep = separation(P, [hv, m, sfv, wv])
    got_sep = sep
    for term in [wv, sfv, m, hv]:  # reversed order (outermost peeled first)
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl(actual, inst, term), *got_sep.sequent.left)],
            principal=actual)
    actual = got_sep.sequent.right[0]
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)),
         wl(fl(actual, Exists(pv, char_p), wv), *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, wv), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, wv), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, wv), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, wv), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, wv), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, wv), P(term_x)), In(term_x, pv)))

    # ====================================================================
    # Section 6: Base case — P(0) => In(0, pv)
    # ====================================================================
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)

    # h_m(0) = m from Recursive base:
    got_hm_0 = apply_thm(got_base_hm, [eb], empty_eb, Apply(hv, eb, m), ax(empty_eb))
    # [rec_hm, Empty(eb)] |- Apply(hv, eb, m)

    # In(eb, wv) from omega_contains_empty:
    oce = omega_contains_empty()
    got_eb_wv = apply_thm(oce, [wv], omega_wv,
        Forall(eb, Implies(empty_eb, In(eb, wv))), ax(omega_wv))
    got_eb_wv = apply_thm(got_eb_wv, [eb], empty_eb, In(eb, wv), ax(empty_eb))

    # dom_closed(sf, eb) for recursion_theorem:
    got_dc_eb, dc_eb, f_at_eb = build_dom_closed(eb, got_eb_wv)

    # recursion_theorem: ∃!h0. Recursive(h0, eb, sf, wv)
    rt = recursion_theorem()
    h0 = Var(postfix='h0')
    rec_h0 = RecDef(h0, eb, sfv, wv)
    exu_h0 = ExistsUnique(h0, rec_h0)
    got_rt_eb = apply_thm(rt, [eb, sfv, wv], func_sf,
        Implies(dc_eb, Implies(omega_wv, exu_h0)), ax(func_sf))
    got_rt_eb = mp(got_rt_eb, got_dc_eb, dc_eb, Implies(omega_wv, exu_h0))
    got_rt_eb = mp(got_rt_eb, ax(omega_wv), omega_wv, exu_h0)
    # Extract Recursive(h0, eb, sfv, wv) from ExistsUnique:
    h0u = Var()
    uniq_part_h0 = Forall(h0u, Implies(RecDef(h0u, eb, sfv, wv), Eq(h0, h0u)))
    and_rec_uniq_h0 = And(rec_h0, uniq_part_h0)
    got_rec_h0 = apply_thm(and_elim_left(rec_h0, uniq_part_h0, []), [],
        and_rec_uniq_h0, rec_h0, ax(and_rec_uniq_h0))

    # rec_h_zero_identity: Recursive(h0,0,sf,wv) + Empty(eb) + sc + Omega(wv) -> Apply(h0,m,m)
    rhi = rec_h_zero_identity()
    app_h0_mm = Apply(h0, m, m)
    got_h0_mm = apply_thm(rhi, [wv, sfv, h0, eb], omega_wv,
        Implies(succ_char, Implies(rec_h0, Implies(empty_eb,
            Forall(m, Implies(in_m_wv, app_h0_mm))))), ax(omega_wv))
    got_h0_mm = mp(got_h0_mm, ax(succ_char), succ_char,
        Implies(rec_h0, Implies(empty_eb, Forall(m, Implies(in_m_wv, app_h0_mm)))))
    got_h0_mm = mp(got_h0_mm, ax(rec_h0), rec_h0,
        Implies(empty_eb, Forall(m, Implies(in_m_wv, app_h0_mm))))
    got_h0_mm = mp(got_h0_mm, ax(empty_eb), empty_eb,
        Forall(m, Implies(in_m_wv, app_h0_mm)))
    got_h0_mm = apply_thm(got_h0_mm, [m], in_m_wv, app_h0_mm, ax(in_m_wv))
    # [succ_char, rec_h0, empty_eb, in_m_wv, omega_wv, axioms] |- Apply(h0, m, m)

    # Build P(eb): ∃q. Apply(hv,eb,q) ∧ In(q,wv) ∧ ∃hn. Rec(hn,eb,sf,wv) ∧ Apply(hn,m,q)
    # With q=m: Apply(hv,eb,m) ∧ In(m,wv) ∧ ∃hn. Rec(hn,eb,sf,wv) ∧ Apply(hn,m,m)
    # Witness hn=h0.
    and_rec_app_h0 = And(rec_h0, app_h0_mm)
    all_base = list(got_h0_mm.sequent.left)
    for f_ in [rec_h0]:
        if not any(same(f_, g) for g in all_base):
            all_base.append(f_)
    got_ra_h0 = mp(apply_thm(and_intro(rec_h0, app_h0_mm, []), [],
        rec_h0, Implies(app_h0_mm, and_rec_app_h0), ax(rec_h0)),
        weaken_to(got_h0_mm, all_base + [rec_h0]), app_h0_mm, and_rec_app_h0)
    got_ex_hn_base = eir(got_ra_h0,
        And(RecDef(hn, eb, sfv, wv), Apply(hn, m, m)), hn, h0)
    ex_hn_base = got_ex_hn_base.sequent.right[0]

    and_in_ex_base = And(in_m_wv, ex_hn_base)
    all_b2 = list(got_ex_hn_base.sequent.left)
    for f_ in got_in_m_wv.sequent.left:
        if not any(same(f_, g) for g in all_b2):
            all_b2.append(f_)
    got_in_ex_base = mp(apply_thm(and_intro(in_m_wv, ex_hn_base, []), [],
        in_m_wv, Implies(ex_hn_base, and_in_ex_base),
        weaken_to(ax(in_m_wv), all_b2)),
        weaken_to(got_ex_hn_base, all_b2), ex_hn_base, and_in_ex_base)

    and_app_in_ex_base = And(Apply(hv, eb, m), and_in_ex_base)
    all_b3 = list(got_in_ex_base.sequent.left)
    for f_ in got_hm_0.sequent.left:
        if not any(same(f_, g) for g in all_b3):
            all_b3.append(f_)
    got_full_base = mp(apply_thm(and_intro(Apply(hv, eb, m), and_in_ex_base, []), [],
        Apply(hv, eb, m), Implies(and_in_ex_base, and_app_in_ex_base),
        weaken_to(got_hm_0, all_b3)),
        weaken_to(got_in_ex_base, all_b3), and_in_ex_base, and_app_in_ex_base)

    p_eb = P(eb)
    got_p_eb = eir(got_full_base,
        And(Apply(hv, eb, qv), And(In(qv, wv),
            Exists(hn, And(RecDef(hn, eb, sfv, wv), Apply(hn, m, qv))))),
        qv, m)
    # got_p_eb: [...] |- P(eb)

    # Cut rec_h0 with got_rec_h0 which depends on and_rec_uniq_h0:
    cur_base = got_p_eb
    if any(same(rec_h0, g) for g in cur_base.sequent.left):
        cur_base = cut(cur_base, rec_h0, got_rec_h0)
    # Now eel h0 from and_rec_uniq_h0:
    if any(same(and_rec_uniq_h0, g) for g in cur_base.sequent.left):
        cur_base = eel(cur_base, and_rec_uniq_h0, h0)
        cur_base = cut(cur_base, cur_base.sequent.left[-1], got_rt_eb)

    # And(In(eb,wv), P(eb)) -> In(eb, pv)
    and_wp_eb = And(In(eb, wv), p_eb)
    all_b4 = list(got_eb_wv.sequent.left)
    for f_ in cur_base.sequent.left:
        if not any(same(f_, g) for g in all_b4):
            all_b4.append(f_)
    got_and_b = mp(apply_thm(and_intro(In(eb, wv), p_eb, []), [], In(eb, wv),
        Implies(p_eb, and_wp_eb), weaken_to(got_eb_wv, all_b4)),
        weaken_to(cur_base, all_b4), p_eb, and_wp_eb)
    got_bwd_eb = char_p_bwd(eb)
    all_b5 = list(got_and_b.sequent.left)
    for f_ in got_bwd_eb.sequent.left:
        if not any(same(f_, g) for g in all_b5):
            all_b5.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_eb, all_b5), got_and_b, and_wp_eb, In(eb, pv))

    imp_base = Implies(empty_eb, In(eb, pv))
    rem_eb = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_eb, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    base_ind = Forall(eb, imp_base)
    proof_base = Proof(Sequent(rem_eb, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=eb)

    # ====================================================================
    # Section 7: Step case — In(nv, pv) ∧ Succ(snv,nv) → In(snv, pv)
    # ====================================================================
    nv = Var(postfix='nv')
    snv = Var(postfix='snv')
    succ_sn_n = SuccDef(snv, nv)
    in_nv_p = In(nv, pv)

    # Extract from char_p: In(nv,pv) -> In(nv,wv) ∧ P(nv)
    got_fwd_n = char_p_fwd(nv)
    got_and_n = mp(weaken_to(got_fwd_n, [in_nv_p]), ax(in_nv_p),
        in_nv_p, And(In(nv, wv), P(nv)))
    got_in_nwv = apply_thm(and_elim_left(In(nv, wv), P(nv), []), [],
        And(In(nv, wv), P(nv)), In(nv, wv), got_and_n)
    got_p_n = apply_thm(and_elim_right(In(nv, wv), P(nv), []), [],
        And(In(nv, wv), P(nv)), P(nv), got_and_n)
    # [char_p, In(nv,pv)] |- P(nv)

    # Open P(nv): ∃q. Apply(hv,nv,q) ∧ In(q,wv) ∧ ∃hn. Rec(hn,nv,sf,wv) ∧ Apply(hn,m,q)
    # Work with components: qv, hn open
    app_hm_nq = Apply(hv, nv, qv)
    in_q_wv = In(qv, wv)
    rec_hn_n = RecDef(hn, nv, sfv, wv)
    app_hn_mq = Apply(hn, m, qv)

    # --- Build Apply(hv, snv, sq) via rec_step_succ on hv at nv ---
    sqv = Var(postfix='sq')  # S(q)
    succ_sq_q = SuccDef(sqv, qv)
    got_se_q = apply_thm(se, [qv], concl=Exists(sqv, succ_sq_q))

    rst = rec_step_succ()
    nv3, pv3, snv3, spv3 = Var(), Var(), Var(), Var()
    inner_rst = Forall(nv3, Forall(pv3, Forall(snv3, Forall(spv3,
        Implies(omega_wv, Implies(In(nv3, wv), Implies(In(pv3, wv), Implies(succ_char,
            Implies(rec_hm, Implies(Apply(hv, nv3, pv3),
                Implies(SuccDef(snv3, nv3), Implies(SuccDef(spv3, pv3),
                    Apply(hv, snv3, spv3)))))))))))))
    got_rst_hm = apply_thm(rst, [wv, m, sfv, hv], concl=inner_rst)
    cur_f = inner_rst
    for term in [nv, qv, snv, sqv]:
        exp = _expand(cur_f)
        next_f = _subst(exp.body, exp.var, term)
        got_rst_hm = Proof(Sequent(got_rst_hm.sequent.left, [next_f]), 'cut',
            [wr(got_rst_hm, next_f), wl(fl(cur_f, next_f, term), *got_rst_hm.sequent.left)],
            principal=cur_f)
        cur_f = next_f
    # MP through all hypotheses:
    got_rst_hm = mp(got_rst_hm, ax(omega_wv), omega_wv, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, got_in_nwv, In(nv, wv), cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(in_q_wv), in_q_wv, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(succ_char), succ_char, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(rec_hm), rec_hm, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(app_hm_nq), app_hm_nq, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(succ_sn_n), succ_sn_n, cur_f.right); cur_f = cur_f.right
    got_rst_hm = mp(got_rst_hm, ax(succ_sq_q), succ_sq_q, Apply(hv, snv, sqv))
    # [..., succ_sq_q, succ_sn_n, app_hm_nq, in_q_wv, ...] |- Apply(hv, snv, sqv)

    # --- In(sqv, wv) from omega_succ_closed ---
    got_sq_wv = apply_thm(osc, [wv], omega_wv,
        Forall(qv, Implies(in_q_wv, Forall(sqv, Implies(succ_sq_q, In(sqv, wv))))),
        ax(omega_wv))
    got_sq_wv = apply_thm(got_sq_wv, [qv], in_q_wv,
        Forall(sqv, Implies(succ_sq_q, In(sqv, wv))), ax(in_q_wv))
    got_sq_wv = apply_thm(got_sq_wv, [sqv], succ_sq_q, In(sqv, wv), ax(succ_sq_q))

    # --- In(snv, wv) from omega_succ_closed ---
    got_snv_wv = apply_thm(osc, [wv], omega_wv,
        Forall(nv, Implies(In(nv, wv), Forall(snv, Implies(succ_sn_n, In(snv, wv))))),
        ax(omega_wv))
    got_snv_wv = apply_thm(got_snv_wv, [nv], In(nv, wv),
        Forall(snv, Implies(succ_sn_n, In(snv, wv))), got_in_nwv)
    got_snv_wv = apply_thm(got_snv_wv, [snv], succ_sn_n, In(snv, wv), ax(succ_sn_n))

    # --- dom_closed(sf, snv) for recursion_theorem to get h_sn ---
    got_dc_snv, dc_snv, f_at_snv = build_dom_closed(snv, got_snv_wv)

    # --- recursion_theorem: ∃!h_sn. Recursive(h_sn, snv, sf, wv) ---
    h_sn = Var(postfix='hsn')
    rec_hsn = RecDef(h_sn, snv, sfv, wv)
    exu_hsn = ExistsUnique(h_sn, rec_hsn)
    got_rt_snv = apply_thm(rt, [snv, sfv, wv], func_sf,
        Implies(dc_snv, Implies(omega_wv, exu_hsn)), ax(func_sf))
    got_rt_snv = mp(got_rt_snv, got_dc_snv, dc_snv, Implies(omega_wv, exu_hsn))
    got_rt_snv = mp(got_rt_snv, ax(omega_wv), omega_wv, exu_hsn)
    h_sn_u = Var()
    uniq_part_hsn = Forall(h_sn_u, Implies(RecDef(h_sn_u, snv, sfv, wv), Eq(h_sn, h_sn_u)))
    and_rec_uniq_hsn = And(rec_hsn, uniq_part_hsn)
    got_rec_hsn = apply_thm(and_elim_left(rec_hsn, uniq_part_hsn, []), [],
        and_rec_uniq_hsn, rec_hsn, ax(and_rec_uniq_hsn))

    # --- rec_succ_shift: h_sn and hn with Succ(snv,nv), In(nv,wv) ---
    # Result: ∀k∈wv. P_strong(k) where P_strong(k) = ∃y2. Apply(hn,k,y2) ∧ In(y2,wv)
    #   ∧ ∃s2. Succ(s2,y2) ∧ Apply(h_sn,k,s2)
    rss = rec_succ_shift()
    # rss: ∀w,sf,h1,h2,m,sm. Omega->sc->Rec(h1,sm,...)->Rec(h2,m,...)->Succ(sm,m)->In(m,w)->
    #   ∀nf. In(nf,w) -> P_strong(nf)
    # Instantiate: w=wv, sf=sfv, h1=h_sn, h2=hn, m=nv, sm=snv
    # Then at nf=m: P_strong(m) = ∃y2. Apply(hn,m,y2) ∧ In(y2,wv) ∧ ∃s2. Succ(s2,y2) ∧ Apply(h_sn,m,s2)
    y2v = Var(postfix='y2')
    s2v = Var(postfix='s2')
    def P_strong_rss(k):
        return Exists(y2v, And(Apply(hn, k, y2v), And(In(y2v, wv),
            Exists(s2v, And(SuccDef(s2v, y2v), Apply(h_sn, k, s2v))))))
    nf = Var(postfix='nf')
    imp_nf = Implies(In(nf, wv), P_strong_rss(nf))
    fa_nf = Forall(nf, imp_nf)

    got_rss = apply_thm(rss, [wv, sfv, h_sn, hn, nv, snv], omega_wv,
        Implies(succ_char, Implies(rec_hsn, Implies(rec_hn_n,
            Implies(succ_sn_n, Implies(In(nv, wv), fa_nf))))),
        ax(omega_wv))
    got_rss = mp(got_rss, ax(succ_char), succ_char,
        Implies(rec_hsn, Implies(rec_hn_n,
            Implies(succ_sn_n, Implies(In(nv, wv), fa_nf)))))
    got_rss = mp(got_rss, ax(rec_hsn), rec_hsn,
        Implies(rec_hn_n, Implies(succ_sn_n, Implies(In(nv, wv), fa_nf))))
    got_rss = mp(got_rss, ax(rec_hn_n), rec_hn_n,
        Implies(succ_sn_n, Implies(In(nv, wv), fa_nf)))
    got_rss = mp(got_rss, ax(succ_sn_n), succ_sn_n,
        Implies(In(nv, wv), fa_nf))
    got_rss = mp(got_rss, got_in_nwv, In(nv, wv), fa_nf)
    # Instantiate nf=m:
    ps_m = P_strong_rss(m)
    got_ps_m = apply_thm(got_rss, [m], in_m_wv, ps_m, ax(in_m_wv))
    # [omega_wv, succ_char, rec_hsn, rec_hn_n, succ_sn_n, In(nv,wv), in_m_wv, char_p, In(nv,pv), axioms]
    # |- P_strong_rss(m)

    # Open P_strong_rss(m): ∃y2. Apply(hn,m,y2) ∧ In(y2,wv) ∧ ∃s2. Succ(s2,y2) ∧ Apply(h_sn,m,s2)
    # y2 should equal qv (from func_unique on hn). Then s2 = S(qv) = sqv.
    # But we need to work with the opened existentials.

    # From IH (P(nv) opened): Apply(hn, m, qv) is available.
    # From P_strong_rss(m) opened: Apply(hn, m, y2v).
    # func_unique on hn: qv = y2v. Then s2v is the successor of y2v = qv.
    # Apply(h_sn, m, s2v). And succ_sq_q = Succ(sqv, qv).
    # From func_unique on successor: s2v = sqv.
    # So Apply(h_sn, m, sqv).

    # Actually, the approach is simpler: from func_unique on hn,
    # Apply(hn,m,qv) and Apply(hn,m,y2v) -> Eq(qv, y2v).
    # Then transfer: Succ(s2v, y2v) + Eq(qv,y2v) -> Succ(s2v, qv).
    # Then unique_successor: Succ(s2v, qv) + Succ(sqv, qv) -> Eq(s2v, sqv).
    # Then transfer: Apply(h_sn, m, s2v) + Eq(s2v, sqv) -> Apply(h_sn, m, sqv).

    # But this requires opening the existentials in P_strong_rss(m), which means
    # working inside existential scope. Let me just use the existential directly
    # and build P(snv) from the components.

    # Strategy: work with y2v, s2v as opened variables.
    # From Apply(hn,m,y2v) and Apply(hn,m,qv): Eq(qv,y2v) via func_unique.
    # Transfer Succ(s2v,y2v) to Succ(s2v,qv) via eq_successor_transfer.
    # Then unique_successor: Succ(s2v,qv) + Succ(sqv,qv) -> Eq(sqv,s2v).
    # Transfer Apply(h_sn,m,s2v) to Apply(h_sn,m,sqv) via eq_apply_val_transfer? No,
    # we want Apply(h_sn,m,sqv). Actually, we can just use Eq(s2v,sqv) to transfer.
    # Wait, we have Eq(sqv,s2v). We want Apply(h_sn,m,s2v) -> Apply(h_sn,m,sqv).
    # That needs Eq(s2v,sqv). Symmetric: Eq(s2v,sqv).

    # Actually, let me avoid opening P_strong_rss(m) at all. Instead, I'll build
    # P(snv) differently.
    # P(snv) = ∃q'. Apply(hv,snv,q') ∧ In(q',wv) ∧ ∃hsn'. Rec(hsn',snv,sf,wv) ∧ Apply(hsn',m,q')
    # With q'=sqv, hsn'=h_sn.
    # I have: Apply(hv,snv,sqv) from got_rst_hm.
    # I have: In(sqv,wv) from got_sq_wv.
    # I need: Apply(h_sn,m,sqv).

    # From P_strong_rss(m): ∃y2. Apply(hn,m,y2) ∧ In(y2,wv) ∧ ∃s2. Succ(s2,y2) ∧ Apply(h_sn,m,s2).
    # Open y2: Apply(hn,m,y2). By func_unique on hn: y2=qv (since Apply(hn,m,qv) from IH).
    # Open s2: Succ(s2,y2) and Apply(h_sn,m,s2).
    # From Eq(y2,qv) + Succ(s2,y2): Succ(s2,qv).
    # Succ(sqv,qv) from assumption.
    # unique_successor: Eq(s2,sqv). Transfer: Apply(h_sn,m,sqv).

    # This requires opening P_strong inside the existential. It's doable but adds boilerplate.
    # Let me open it.

    app_hn_my2 = Apply(hn, m, y2v)
    in_y2_wv = In(y2v, wv)
    succ_s2_y2 = SuccDef(s2v, y2v)
    app_hsn_ms2 = Apply(h_sn, m, s2v)

    # func_unique on hn: Recursive gives Function(hn)
    func_hn = FuncDef(hn)
    xd_hn, yd_hn = Var(), Var()
    dom_sub_hn = Forall(xd_hn, Implies(Exists(yd_hn, Apply(hn, xd_hn, yd_hn)), In(xd_hn, wv)))
    ev_hn = Var()
    base_hn = Forall(ev_hn, Implies(Empty(ev_hn), Apply(hn, ev_hn, nv)))
    nst2, valst2, snst2, fvalst2 = Var(), Var(), Var(), Var()
    step_hn = Forall(nst2, Implies(In(nst2, wv),
        Forall(valst2, Implies(Apply(hn, nst2, valst2),
            Forall(snst2, Implies(SuccDef(snst2, nst2),
                Forall(fvalst2, Implies(Apply(sfv, valst2, fvalst2),
                    Apply(hn, snst2, fvalst2)))))))))
    and_bshn = And(base_hn, step_hn)
    and_dom_bshn = And(dom_sub_hn, and_bshn)
    got_func_hn = apply_thm(and_elim_left(func_hn, and_dom_bshn, []), [],
        rec_hn_n, func_hn, ax(rec_hn_n))

    fut = func_unique_thm()
    got_eq_qy2 = apply_thm(fut, [hn, m, qv, y2v], func_hn,
        Implies(app_hn_mq, Implies(app_hn_my2, Eq(qv, y2v))),
        got_func_hn)
    got_eq_qy2 = mp(got_eq_qy2, ax(app_hn_mq), app_hn_mq,
        Implies(app_hn_my2, Eq(qv, y2v)))
    got_eq_qy2 = mp(got_eq_qy2, ax(app_hn_my2), app_hn_my2, Eq(qv, y2v))
    # [rec_hn_n, Apply(hn,m,qv), Apply(hn,m,y2v)] |- Eq(qv, y2v)

    # eq_successor_transfer: Eq(s2v,s2v) + Eq(y2v,qv) + Succ(s2v,qv)... hmm
    # I want: Succ(s2v,y2v) + Eq(qv,y2v) -> Succ(s2v,qv).
    # eq_successor_transfer: Eq(a,c) + Eq(b,d) + Succ(c,d) -> Succ(a,b).
    # Set a=s2v, b=qv, c=s2v, d=y2v: Eq(s2v,s2v) + Eq(qv,y2v) + Succ(s2v,y2v) -> Succ(s2v,qv).
    er = eq_reflexive()
    got_eq_s2s2 = apply_thm(er, [s2v], concl=Eq(s2v, s2v))

    est = eq_successor_transfer()
    # est: ∀a,b. ∀c,d. Eq(a,c) -> Eq(b,d) -> Succ(c,d) -> Succ(a,b)
    cv, dv = Var(), Var()
    fa_cd = Forall(cv, Forall(dv,
        Implies(Eq(s2v, cv), Implies(Eq(qv, dv), Implies(SuccDef(cv, dv), SuccDef(s2v, qv))))))
    got_est = apply_thm(est, [s2v, qv], concl=fa_cd)
    # fl c=s2v, d=y2v:
    fa_d = Forall(dv,
        Implies(Eq(s2v, s2v), Implies(Eq(qv, dv), Implies(SuccDef(s2v, dv), SuccDef(s2v, qv)))))
    got_est = Proof(Sequent(got_est.sequent.left, [fa_d]), 'cut',
        [wr(got_est, fa_d), wl(fl(fa_cd, fa_d, s2v), *got_est.sequent.left)], principal=fa_cd)
    inst_d = Implies(Eq(s2v, s2v), Implies(Eq(qv, y2v), Implies(SuccDef(s2v, y2v), SuccDef(s2v, qv))))
    got_est = Proof(Sequent(got_est.sequent.left, [inst_d]), 'cut',
        [wr(got_est, inst_d), wl(fl(fa_d, inst_d, y2v), *got_est.sequent.left)], principal=fa_d)
    got_succ_s2q = mp(got_est, got_eq_s2s2, Eq(s2v, s2v),
        Implies(Eq(qv, y2v), Implies(SuccDef(s2v, y2v), SuccDef(s2v, qv))))
    got_succ_s2q = mp(got_succ_s2q, got_eq_qy2, Eq(qv, y2v),
        Implies(SuccDef(s2v, y2v), SuccDef(s2v, qv)))
    got_succ_s2q = mp(got_succ_s2q, ax(succ_s2_y2), succ_s2_y2, SuccDef(s2v, qv))
    # [..., Succ(s2v,y2v)] |- Succ(s2v, qv)

    # unique_successor: Succ(s2v,qv) + Succ(sqv,qv) -> Eq(s2v, sqv)
    us = unique_successor()
    got_eq_s2sq = apply_thm(us, [qv, s2v, sqv], SuccDef(s2v, qv),
        Implies(SuccDef(sqv, qv), Eq(s2v, sqv)), got_succ_s2q)
    got_eq_s2sq = mp(got_eq_s2sq, ax(succ_sq_q), succ_sq_q, Eq(s2v, sqv))

    # eq_apply_val_transfer: Eq(s2v, sqv) -> Apply(h_sn,m,s2v) -> Apply(h_sn,m,sqv)
    eavt = eq_apply_val_transfer()
    app_hsn_msq = Apply(h_sn, m, sqv)
    got_transfer = apply_thm(eavt, [h_sn, m, s2v, sqv], Eq(s2v, sqv),
        Implies(app_hsn_ms2, app_hsn_msq), got_eq_s2sq)
    got_transfer = mp(got_transfer, ax(app_hsn_ms2), app_hsn_ms2, app_hsn_msq)
    # [..., Apply(h_sn,m,s2v), Succ(s2v,y2v), Apply(hn,m,y2v), ...] |- Apply(h_sn,m,sqv)

    # --- Build P(snv): ∃q'. Apply(hv,snv,q') ∧ In(q',wv) ∧ ∃hsn'. Rec(hsn',snv,sf,wv) ∧ Apply(hsn',m,q') ---
    # q'=sqv, hsn'=h_sn
    and_rec_app_hsn = And(rec_hsn, app_hsn_msq)
    all_step = []
    for pr in [got_rst_hm, got_sq_wv, got_transfer]:
        for f_ in pr.sequent.left:
            if not any(same(f_, g) for g in all_step):
                all_step.append(f_)
    for f_ in [rec_hsn]:
        if not any(same(f_, g) for g in all_step):
            all_step.append(f_)

    got_ra_hsn = mp(apply_thm(and_intro(rec_hsn, app_hsn_msq, []), [],
        rec_hsn, Implies(app_hsn_msq, and_rec_app_hsn),
        weaken_to(ax(rec_hsn), all_step)),
        weaken_to(got_transfer, all_step), app_hsn_msq, and_rec_app_hsn)
    got_ex_hsn = eir(got_ra_hsn,
        And(RecDef(hn, snv, sfv, wv), Apply(hn, m, sqv)), hn, h_sn)
    ex_hsn_step = got_ex_hsn.sequent.right[0]

    and_in_ex_step = And(In(sqv, wv), ex_hsn_step)
    all_s2 = list(got_ex_hsn.sequent.left)
    for f_ in got_sq_wv.sequent.left:
        if not any(same(f_, g) for g in all_s2):
            all_s2.append(f_)
    got_in_ex_step = mp(apply_thm(and_intro(In(sqv, wv), ex_hsn_step, []), [],
        In(sqv, wv), Implies(ex_hsn_step, and_in_ex_step),
        weaken_to(got_sq_wv, all_s2)),
        weaken_to(got_ex_hsn, all_s2), ex_hsn_step, and_in_ex_step)

    and_app_in_ex_step = And(Apply(hv, snv, sqv), and_in_ex_step)
    all_s3 = list(got_in_ex_step.sequent.left)
    for f_ in got_rst_hm.sequent.left:
        if not any(same(f_, g) for g in all_s3):
            all_s3.append(f_)
    got_full_step = mp(apply_thm(and_intro(Apply(hv, snv, sqv), and_in_ex_step, []), [],
        Apply(hv, snv, sqv), Implies(and_in_ex_step, and_app_in_ex_step),
        weaken_to(got_rst_hm, all_s3)),
        weaken_to(got_in_ex_step, all_s3), and_in_ex_step, and_app_in_ex_step)

    p_snv = P(snv)
    got_p_snv = eir(got_full_step,
        And(Apply(hv, snv, qv), And(In(qv, wv),
            Exists(hn, And(RecDef(hn, snv, sfv, wv), Apply(hn, m, qv))))),
        qv, sqv)
    # got_p_snv: [...lots...] |- P(snv)

    # --- Close existentials from P_strong_rss(m) and P(nv) ---
    cur_step = got_p_snv

    # Close s2v from Succ(s2v,y2v) and Apply(h_sn,m,s2v):
    and_succ_app_s2 = And(succ_s2_y2, app_hsn_ms2)
    for pred, gp in [
        (succ_s2_y2, apply_thm(and_elim_left(succ_s2_y2, app_hsn_ms2, []), [],
            and_succ_app_s2, succ_s2_y2, ax(and_succ_app_s2))),
        (app_hsn_ms2, apply_thm(and_elim_right(succ_s2_y2, app_hsn_ms2, []), [],
            and_succ_app_s2, app_hsn_ms2, ax(and_succ_app_s2)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_succ_app_s2, s2v)
    ex_s2 = cur_step.sequent.left[-1]

    # Close y2v from Apply(hn,m,y2v), In(y2v,wv), ex_s2:
    and_in_ex_y2 = And(in_y2_wv, ex_s2)
    for pred, gp in [
        (in_y2_wv, apply_thm(and_elim_left(in_y2_wv, ex_s2, []), [],
            and_in_ex_y2, in_y2_wv, ax(and_in_ex_y2))),
        (ex_s2, apply_thm(and_elim_right(in_y2_wv, ex_s2, []), [],
            and_in_ex_y2, ex_s2, ax(and_in_ex_y2)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    and_app_in_ex_y2 = And(app_hn_my2, and_in_ex_y2)
    for pred, gp in [
        (app_hn_my2, apply_thm(and_elim_left(app_hn_my2, and_in_ex_y2, []), [],
            and_app_in_ex_y2, app_hn_my2, ax(and_app_in_ex_y2))),
        (and_in_ex_y2, apply_thm(and_elim_right(app_hn_my2, and_in_ex_y2, []), [],
            and_app_in_ex_y2, and_in_ex_y2, ax(and_app_in_ex_y2)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_app_in_ex_y2, y2v)
    # Cut with P_strong_rss(m) = got_ps_m:
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_ps_m)

    # Close h_sn: cut rec_hsn with got_rec_hsn, eel h_sn from and_rec_uniq_hsn
    if any(same(rec_hsn, g) for g in cur_step.sequent.left):
        cur_step = cut(cur_step, rec_hsn, got_rec_hsn)
    if any(same(and_rec_uniq_hsn, g) for g in cur_step.sequent.left):
        cur_step = eel(cur_step, and_rec_uniq_hsn, h_sn)
        cur_step = cut(cur_step, cur_step.sequent.left[-1], got_rt_snv)

    # Close sqv from Succ(sqv, qv): eel sqv, cut with successor_exists
    cur_step = eel(cur_step, succ_sq_q, sqv)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_q)

    # Close P(nv) components: qv, hn from the IH
    # P(nv) was opened as: qv with Apply(hv,nv,qv) ∧ In(qv,wv) ∧ ∃hn. Rec(hn,nv,sf,wv) ∧ Apply(hn,m,qv)
    # Close hn from rec_hn_n and app_hn_mq:
    and_rec_app_hn = And(rec_hn_n, app_hn_mq)
    for pred, gp in [
        (rec_hn_n, apply_thm(and_elim_left(rec_hn_n, app_hn_mq, []), [],
            and_rec_app_hn, rec_hn_n, ax(and_rec_app_hn))),
        (app_hn_mq, apply_thm(and_elim_right(rec_hn_n, app_hn_mq, []), [],
            and_rec_app_hn, app_hn_mq, ax(and_rec_app_hn)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_rec_app_hn, hn)
    ex_hn_from_p = cur_step.sequent.left[-1]

    # Close qv from app_hm_nq, in_q_wv, ex_hn_from_p:
    and_in_ex_q = And(in_q_wv, ex_hn_from_p)
    for pred, gp in [
        (in_q_wv, apply_thm(and_elim_left(in_q_wv, ex_hn_from_p, []), [],
            and_in_ex_q, in_q_wv, ax(and_in_ex_q))),
        (ex_hn_from_p, apply_thm(and_elim_right(in_q_wv, ex_hn_from_p, []), [],
            and_in_ex_q, ex_hn_from_p, ax(and_in_ex_q)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    and_app_in_ex_q = And(app_hm_nq, and_in_ex_q)
    for pred, gp in [
        (app_hm_nq, apply_thm(and_elim_left(app_hm_nq, and_in_ex_q, []), [],
            and_app_in_ex_q, app_hm_nq, ax(and_app_in_ex_q))),
        (and_in_ex_q, apply_thm(and_elim_right(app_hm_nq, and_in_ex_q, []), [],
            and_app_in_ex_q, and_in_ex_q, ax(and_app_in_ex_q)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_app_in_ex_q, qv)
    # Cut with P(nv) = got_p_n:
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_p_n)

    # In(snv,wv) + P(snv) -> In(snv, pv):
    and_wp_snv = And(In(snv, wv), p_snv)
    all_s4 = list(cur_step.sequent.left)
    for f_ in got_snv_wv.sequent.left:
        if not any(same(f_, g) for g in all_s4):
            all_s4.append(f_)
    got_and_snv = mp(apply_thm(and_intro(In(snv, wv), p_snv, []), [], In(snv, wv),
        Implies(p_snv, and_wp_snv), weaken_to(got_snv_wv, all_s4)),
        weaken_to(cur_step, all_s4), p_snv, and_wp_snv)
    got_bwd_snv = char_p_bwd(snv)
    all_s5 = list(got_and_snv.sequent.left)
    for f_ in got_bwd_snv.sequent.left:
        if not any(same(f_, g) for g in all_s5):
            all_s5.append(f_)
    got_in_snp = mp(weaken_to(got_bwd_snv, all_s5), got_and_snv, and_wp_snv, In(snv, pv))

    # Close step: implies_right Succ(snv,nv), forall snv, implies_right In(nv,pv), forall nv
    imp_succ_s = Implies(succ_sn_n, In(snv, pv))
    rem_ss = [f_ for f_ in got_in_snp.sequent.left if not same(f_, succ_sn_n)]
    cur_s = Proof(Sequent(rem_ss, [imp_succ_s]), 'implies_right', [got_in_snp], principal=imp_succ_s)
    fa_snv = Forall(snv, imp_succ_s)
    cur_s = Proof(Sequent(rem_ss, [fa_snv]), 'forall_right', [cur_s], principal=fa_snv, term=snv)
    imp_inp_s = Implies(in_nv_p, fa_snv)
    rem_inp = [f_ for f_ in cur_s.sequent.left if not same(f_, in_nv_p)]
    cur_s = Proof(Sequent(rem_inp, [imp_inp_s]), 'implies_right', [cur_s], principal=imp_inp_s)
    step_ind = Forall(nv, imp_inp_s)
    proof_step = Proof(Sequent(rem_inp, [step_ind]), 'forall_right', [cur_s], principal=step_ind, term=nv)

    # ====================================================================
    # Section 8: Inductive(pv), Subset(pv,wv), omega_smallest_inductive
    # ====================================================================
    from definitions import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, wv)

    all_ind = list(proof_base.sequent.left)
    for f_ in proof_step.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind, step_ind, []), [], base_ind,
        Implies(step_ind, ind_p), weaken_to(proof_base, all_ind)),
        weaken_to(proof_step, all_ind), step_ind, ind_p)

    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv),
        And(In(xsub, wv), P(xsub)))
    got_in_xwv = apply_thm(and_elim_left(In(xsub, wv), P(xsub), []), [],
        And(In(xsub, wv), P(xsub)), In(xsub, wv), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, wv))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xwv], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, wv)
    got_osi = apply_thm(osi, [pv, wv], omega_wv, Implies(hyp_and, eq_pw), ax(omega_wv))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # ====================================================================
    # Section 9: Extract P(n) from Eq(pv,wv) + In(n,wv)
    # ====================================================================
    iff_n_pv = Iff(In(n, pv), In(n, wv))
    got_iff_n_pv = Proof(Sequent(got_eq.sequent.left, [iff_n_pv]), 'cut',
        [wr(got_eq, iff_n_pv),
         weaken_to(fl(eq_pw, iff_n_pv, n), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_np = mp(mp(iff_mp_rev(In(n, pv), In(n, wv), []),
        got_iff_n_pv, iff_n_pv, Implies(In(n, wv), In(n, pv))),
        got_in_n_wv, In(n, wv), In(n, pv))
    got_fwd_np = char_p_fwd(n)
    all_ext = list(got_in_np.sequent.left)
    for f_ in got_fwd_np.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_ext = mp(weaken_to(got_fwd_np, all_ext),
        weaken_to(got_in_np, all_ext), In(n, pv), And(In(n, wv), P(n)))
    got_p_final = apply_thm(and_elim_right(In(n, wv), P(n), []), [],
        And(In(n, wv), P(n)), P(n), got_and_ext)
    # [...] |- P(n) = ∃q. Apply(hv,n,q) ∧ In(q,wv) ∧ ∃hn. Rec(hn,n,sf,wv) ∧ Apply(hn,m,q)

    # ====================================================================
    # Section 10: From P(n) + Apply(hv,n,p) -> build Plus(n,m,p)
    # ====================================================================
    # Open P(n): ∃q. Apply(hv,n,q) ∧ In(q,wv) ∧ ∃hn'. Rec(hn',n,sf,wv) ∧ Apply(hn',m,q)
    # From func_unique on hv: Apply(hv,n,p) + Apply(hv,n,q) -> Eq(p,q).
    # Transfer: Apply(hn',m,q) + Eq(q,p) -> Apply(hn',m,p) via eq_apply_val_transfer.
    # Package: Plus(n,m,p) = ∃w. Omega(w) ∧ ∃h. ∃sf. sf_all ∧ And(Rec(h,n,sf,w), Apply(h,m,p))

    # Open P(n): work with q_final, hn_final
    q_final = Var(postfix='qf')
    hn_final = Var(postfix='hnf')

    app_hm_nqf = Apply(hv, n, q_final)
    in_qf_wv = In(q_final, wv)
    rec_hnf = RecDef(hn_final, n, sfv, wv)
    app_hnf_mqf = Apply(hn_final, m, q_final)

    # func_unique on hv: Apply(hv,n,p) + Apply(hv,n,q_final) -> Eq(p, q_final)
    func_hm_from = apply_thm(and_elim_left(func_hm,
        And(dom_sub_hm, and_base_step), []), [], rec_hm, func_hm, ax(rec_hm))
    got_eq_pqf = apply_thm(fut, [hv, n, p, q_final], func_hm,
        Implies(app_hm_np, Implies(app_hm_nqf, Eq(p, q_final))),
        func_hm_from)
    got_eq_pqf = mp(got_eq_pqf, ax(app_hm_np), app_hm_np,
        Implies(app_hm_nqf, Eq(p, q_final)))
    got_eq_pqf = mp(got_eq_pqf, ax(app_hm_nqf), app_hm_nqf, Eq(p, q_final))
    # [rec_hm, Apply(hv,n,p), Apply(hv,n,q_final)] |- Eq(p, q_final)

    # Eq(q_final, p) from eq_symmetric:
    es = eq_symmetric()
    got_eq_qfp = apply_thm(es, [p, q_final], Eq(p, q_final), Eq(q_final, p), got_eq_pqf)

    # eq_apply_val_transfer: Eq(q_final,p) -> Apply(hn_final,m,q_final) -> Apply(hn_final,m,p)
    app_hnf_mp = Apply(hn_final, m, p)
    got_hnf_mp = apply_thm(eavt, [hn_final, m, q_final, p], Eq(q_final, p),
        Implies(app_hnf_mqf, app_hnf_mp), got_eq_qfp)
    got_hnf_mp = mp(got_hnf_mp, ax(app_hnf_mqf), app_hnf_mqf, app_hnf_mp)
    # [..., Apply(hn_final,m,q_final)] |- Apply(hn_final,m,p)

    # Package: And(Rec(hn_final,n,sf,wv), Apply(hn_final,m,p))
    and_rec_app_final = And(rec_hnf, app_hnf_mp)
    all_pkg = list(got_hnf_mp.sequent.left)
    for f_ in [rec_hnf]:
        if not any(same(f_, g) for g in all_pkg):
            all_pkg.append(f_)
    got_ra_final = mp(apply_thm(and_intro(rec_hnf, app_hnf_mp, []), [],
        rec_hnf, Implies(app_hnf_mp, and_rec_app_final),
        weaken_to(ax(rec_hnf), all_pkg)),
        weaken_to(got_hnf_mp, all_pkg), app_hnf_mp, and_rec_app_final)

    # And(sf_all, and_rec_app_final)
    and_sf_ra_final = And(sf_all, and_rec_app_final)
    all_pkg2 = list(got_ra_final.sequent.left)
    for f_ in [sf_all]:
        if not any(same(f_, g) for g in all_pkg2):
            all_pkg2.append(f_)
    got_sf_ra_final = mp(apply_thm(and_intro(sf_all, and_rec_app_final, []), [],
        sf_all, Implies(and_rec_app_final, and_sf_ra_final),
        weaken_to(ax(sf_all), all_pkg2)),
        weaken_to(got_ra_final, all_pkg2), and_rec_app_final, and_sf_ra_final)

    # Existentials: ∃sf. And(sf_all, And(Rec(hn_final,n,sf,wv), Apply(hn_final,m,p)))
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc2, ysc2 = Var(), Var()
    sc_pat = Forall(xsc2, Implies(In(xsc2, wv),
        Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2)))))
    inner_sf = And(
        And(sc_pat, And(FuncDef(sf_var),
            Forall(xds, Implies(Exists(yds, Apply(sf_var, xds, yds)), In(xds, wv))))),
        And(RecDef(hn_final, n, sf_var, wv), app_hnf_mp))
    got_ex_sf = eir(got_sf_ra_final, inner_sf, sf_var, sfv)

    inner_h = Exists(sf_var, And(
        And(sc_pat, And(FuncDef(sf_var),
            Forall(xds, Implies(Exists(yds, Apply(sf_var, xds, yds)), In(xds, wv))))),
        And(RecDef(h_var, n, sf_var, wv), Apply(h_var, m, p))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hn_final)

    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex_final = And(omega_wv, ex_h_sf)
    got_omega_ex_final = mp(apply_thm(and_intro(omega_wv, ex_h_sf, []), [],
        omega_wv, Implies(ex_h_sf, and_omega_ex_final), ax(omega_wv)),
        got_ex_h, ex_h_sf, and_omega_ex_final)

    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(And(Forall(xsc2, Implies(In(xsc2, w_var),
            Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2))))),
            And(FuncDef(sf_var),
                Forall(xds, Implies(Exists(yds, Apply(sf_var, xds, yds)), In(xds, w_var))))),
            And(RecDef(h_var, n, sf_var, w_var), Apply(h_var, m, p))))))
    got_plus = eir(got_omega_ex_final, inner_w, w_var, wv)
    # got_plus: [...] |- Plus(n, m, p) (expanded)

    # ====================================================================
    # Section 11: Close existentials from P(n) extraction and fold back
    # ====================================================================
    proof = got_plus

    # Helper: cut ALL occurrences of formula from left
    def cut_all(prf, formula, derivation):
        while any(same(formula, g) for g in prf.sequent.left):
            prf = cut(prf, formula, derivation)
        return prf

    # --- Close hn_final from P(n) opening ---
    and_rec_app_hnf = And(rec_hnf, app_hnf_mqf)
    proof = cut_all(proof, rec_hnf, apply_thm(and_elim_left(rec_hnf, app_hnf_mqf, []), [],
        and_rec_app_hnf, rec_hnf, ax(and_rec_app_hnf)))
    proof = cut_all(proof, app_hnf_mqf, apply_thm(and_elim_right(rec_hnf, app_hnf_mqf, []), [],
        and_rec_app_hnf, app_hnf_mqf, ax(and_rec_app_hnf)))
    if any(same(and_rec_app_hnf, g) for g in proof.sequent.left):
        proof = eel(proof, and_rec_app_hnf, hn_final)
        ex_hnf = proof.sequent.left[-1]

        # --- Close q_final from P(n) opening ---
        and_in_exhnf = And(in_qf_wv, ex_hnf)
        proof = cut_all(proof, in_qf_wv, apply_thm(and_elim_left(in_qf_wv, ex_hnf, []), [],
            and_in_exhnf, in_qf_wv, ax(and_in_exhnf)))
        proof = cut_all(proof, ex_hnf, apply_thm(and_elim_right(in_qf_wv, ex_hnf, []), [],
            and_in_exhnf, ex_hnf, ax(and_in_exhnf)))
        and_app_in_exhnf = And(app_hm_nqf, and_in_exhnf)
        proof = cut_all(proof, app_hm_nqf, apply_thm(and_elim_left(app_hm_nqf, and_in_exhnf, []), [],
            and_app_in_exhnf, app_hm_nqf, ax(and_app_in_exhnf)))
        proof = cut_all(proof, and_in_exhnf, apply_thm(and_elim_right(app_hm_nqf, and_in_exhnf, []), [],
            and_app_in_exhnf, and_in_exhnf, ax(and_app_in_exhnf)))
        if any(same(and_app_in_exhnf, g) for g in proof.sequent.left):
            proof = eel(proof, and_app_in_exhnf, q_final)
            proof = cut(proof, proof.sequent.left[-1], got_p_final)

    # --- Close separation set ---
    if any(same(char_p, g) for g in proof.sequent.left):
        proof = eel(proof, char_p, pv)
        proof = cut(proof, proof.sequent.left[-1], got_sep)

    # --- Cut intermediate formulas back to Plus components ---
    # in_m_wv and in_n_wv derive from omega_w, omega_wv, in_m_w, in_n_w
    proof = cut_all(proof, in_m_wv, got_in_m_wv)
    proof = cut_all(proof, in_n_wv, got_in_n_wv)

    # succ_char, func_sf, dom_sub_sf derive from sf_all
    proof = cut_all(proof, succ_char, got_sc_from)
    proof = cut_all(proof, func_sf, got_func_sf)
    proof = cut_all(proof, dom_sub_sf, got_dom_sf)
    # and_func_dom derives from sf_all too
    proof = cut_all(proof, and_func_dom, got_fd_from)

    # rec_hm, app_hm_np derive from and_rec_app
    proof = cut_all(proof, rec_hm, got_rec_from)
    proof = cut_all(proof, app_hm_np, got_app_from)

    # sf_all, and_rec_app derive from and_sf_ra
    proof = cut_all(proof, sf_all, got_sf_from)
    proof = cut_all(proof, and_rec_app, got_ra_from)

    # eel sfv from and_sf_ra, then eel hv
    if any(same(and_sf_ra, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra, sfv)
        ex_sfv_formula = proof.sequent.left[-1]  # Exists(sfv, and_sf_ra)
        if any(same(ex_sfv_formula, g) for g in proof.sequent.left):
            proof = eel(proof, ex_sfv_formula, hv)
            ex_hv_formula = proof.sequent.left[-1]  # Exists(hv, Exists(sfv, and_sf_ra))
            proof = cut_all(proof, ex_hv_formula, got_exhv_from)

    # omega_wv derives from and_omega_ex
    proof = cut_all(proof, omega_wv, got_omega_from)

    # eel wv from and_omega_ex -> Exists(wv, and_omega_ex) which is plus_mn
    if any(same(and_omega_ex, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_ex, wv)

    # ====================================================================
    # Section 12: Discharge hypotheses and close foralls
    # ====================================================================
    # Discharge using goal's formula tree directly:
    # goal = Forall(w, Forall(m, Forall(n, Forall(p, Implies(omega_w, Implies(in_m_w, Implies(in_n_w, Implies(plus_mn, plus_nm))))))))
    g_p = goal.body.body.body  # Forall(p, Implies(omega_w, ...))
    g_imp_omega = g_p.body     # Implies(omega_w, Implies(in_m_w, ...))
    g_imp_m = g_imp_omega.right  # Implies(in_m_w, Implies(in_n_w, ...))
    g_imp_n = g_imp_m.right      # Implies(in_n_w, Implies(plus_mn, plus_nm))
    g_imp_plus = g_imp_n.right   # Implies(plus_mn, plus_nm)

    for hh, imp in [(plus_mn, g_imp_plus), (in_n_w, g_imp_n), (in_m_w, g_imp_m), (omega_w, g_imp_omega)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa in [(p, g_p), (n, goal.body.body), (m, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'plus_comm'
    return proof


def exists_num(k):
    """Every natural number exists as a ZFC set.
    |- exists n. Num(n, k)
    Base: EmptySet axiom -> exists n. Empty(n) = exists n. Num(n, 0).
    Step: successor_exists -> exists s. Succ(s, prev) -> Num(s, i+1)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import Num as NumDef, Successor as SuccDef
    from theorems.axioms import empty_set
    from theorems.sets import successor_exists
    from core.proof import _expand

    nv = Var(postfix='n')

    if k == 0:
        # EmptySet axiom = Exists(b, Empty(b)) alpha-matches Exists(nv, Num(nv,0)).
        es = empty_set()
        goal = Exists(nv, NumDef(nv, 0))
        # Wrap with goal on right for clean display:
        proof = Proof(Sequent(es.sequent.left, [goal]), 'axiom', principal=goal)
        proof.name = 'exists_num_0'
        return proof

    # Chain: for i = 0, 1, ..., k-1, build exists n. Num(n, i+1) from exists n. Num(n, i)
    proof = exists_num(k - 1)
    # proof: [axioms] |- exists prev. Num(prev, k-1)

    prev = Var(postfix=f'n{k-1}')
    cur = Var(postfix=f'n{k}')
    num_prev = NumDef(prev, k - 1)
    succ_cur = SuccDef(cur, prev)
    num_cur = NumDef(cur, k)
    # num_cur = Exists(m, And(Num(m, k-1), Succ(cur, m)))

    # successor_exists at prev: exists cur. Succ(cur, prev)
    se = successor_exists()
    got_se = apply_thm(se, [prev], concl=Exists(cur, succ_cur))
    # [Pairing, Union] |- Exists(cur, Succ(cur, prev))

    # From Num(prev, k-1) and Succ(cur, prev): build Num(cur, k)
    # Num(cur, k) = Exists(m, And(Num(m, k-1), Succ(cur, m)))
    from theorems.logic import and_intro
    and_ns = And(num_prev, succ_cur)
    got_and = mp(apply_thm(and_intro(num_prev, succ_cur, []), [], num_prev,
        Implies(succ_cur, and_ns), ax(num_prev)),
        ax(succ_cur), succ_cur, and_ns)
    # [Num(prev, k-1), Succ(cur, prev)] |- And(Num(prev, k-1), Succ(cur, prev))

    mv = Var()
    got_num_cur = eir(got_and, And(NumDef(mv, k - 1), SuccDef(cur, mv)), mv, prev)
    # [Num(prev, k-1), Succ(cur, prev)] |- Num(cur, k)

    # eir cur: exists cur. Num(cur, k)
    cv = Var()
    got_ex_cur = eir(got_num_cur, NumDef(cv, k), cv, cur)
    # [Num(prev, k-1), Succ(cur, prev)] |- exists cv. Num(cv, k)

    # eel cur from Succ(cur, prev), cut with got_se:
    got_ex_cur = eel(got_ex_cur, succ_cur, cur)
    got_ex_cur = cut(got_ex_cur, got_ex_cur.sequent.left[-1], got_se)
    # [Num(prev, k-1), Pairing, Union] |- exists cv. Num(cv, k)

    # eel prev from Num(prev, k-1):
    got_ex_cur = eel(got_ex_cur, num_prev, prev)
    # Cut with proof (exists prev. Num(prev, k-1)).
    # SPECIAL: EmptySet on proof.left alpha-matches the principal (Exists(prev, Num(prev,0))).
    # Can't use same()-based helpers. Use identity checks for left management.
    ex_num_prev = got_ex_cur.sequent.left[-1]  # the Exists from eel
    # Build c_left = union of proof.left and got_ex_cur.left minus ex_num_prev (by identity)
    # Use cut() helper now that Sequent enforces set semantics — no need for identity tricks.
    got_ex_cur = cut(got_ex_cur, got_ex_cur.sequent.left[-1], proof)
    # [axioms] |- exists cv. Num(cv, k)

    got_ex_cur.name = f'exists_num_{k}'
    return got_ex_cur


def plus_assoc():
    """Associativity of addition: (m + n) + k = m + (n + k).
    |- forall w, m, n, k, p, q, r.
         Omega(w) -> In(m, w) -> In(n, w) -> In(k, w) ->
         Plus(m, n, p) -> Plus(p, k, q) ->
         Plus(n, k, r) -> Plus(m, r, q)
    """
    from definitions import Plus as PlusDef

    w = Var(postfix='w')
    m, n, k = Var(postfix='m'), Var(postfix='n'), Var(postfix='k')
    p, q, r = Var(postfix='p'), Var(postfix='q'), Var(postfix='r')
    omega_w = Omega(w)

    # goal: forall w,m,n,k,p,q,r.
    #   Omega(w) -> In(m,w) -> In(n,w) -> In(k,w) ->
    #   Plus(m,n,p) -> Plus(p,k,q) -> Plus(n,k,r) -> Plus(m,r,q)
    #
    # Strategy: induction on k.
    # Open Plus(m,n,p) to get h_m with h_m(n)=p, Recursive(h_m, m, sf, w).
    # Open Plus(p,k,q) to get h_p with h_p(k)=q, Recursive(h_p, p, sf, w).
    # Open Plus(n,k,r) to get h_n with h_n(k)=r, Recursive(h_n, n, sf, w).
    # Want: Plus(m,r,q) i.e. h_m(r)=q i.e. h_m(h_n(k))=h_p(k).
    #
    # Base (k=0): h_m(h_n(0))=h_m(n)=p=h_p(0). ✓
    # Step: h_p(S(k))=S(h_p(k)), h_n(S(k))=S(h_n(k)),
    #        h_m(S(h_n(k)))=S(h_m(h_n(k)))=S(h_p(k))=h_p(S(k)). ✓

    goal = Forall(w, Forall(m, Forall(n, Forall(k, Forall(p, Forall(q, Forall(r,
        Implies(omega_w, Implies(In(m, w), Implies(In(n, w), Implies(In(k, w),
            Implies(PlusDef(m, n, p), Implies(PlusDef(p, k, q),
                Implies(PlusDef(n, k, r), PlusDef(m, r, q)))))))))))))))
    assert str(goal)

    # Direct induction on k.
    # h_m(n)=p. h_p(k)=q. h_n(k)=r. Want: h_m(r)=q.
    # P(k) = ∀q',r'. Apply(h_p,k,q') → Apply(h_n,k,r') → Apply(h_m,r',q').
    # Base (k=0): h_p(0)=p, h_n(0)=n, h_m(n)=p. ✓
    # Step: h_p(S(k))=S(q'), h_n(S(k))=S(r'), h_m(S(r'))=S(h_m(r'))=S(q'). ✓

    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef)
    from core.proof import _expand, _subst
    from theorems.axioms import separation
    from theorems.recursion import recursion_theorem
    from theorems.sets import omega_unique, successor_exists, eq_successor_transfer
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed)
    from theorems.logic import eq_symmetric

    er = eq_reflexive()
    esub = eq_substitution()

    # ====================================================================
    # Section 1: Open Plus(m,n,p) — same pattern as plus_comm section 1
    # ====================================================================
    wv = Var(postfix='wv')
    hm = Var(postfix='hm')
    sfv = Var(postfix='sfv')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    omega_wv = Omega(wv)
    succ_char = Forall(xsc, Implies(In(xsc, wv),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, wv)))
    and_func_dom = And(func_sf, dom_sub_sf)
    sf_all = And(succ_char, and_func_dom)
    rec_hm = RecDef(hm, m, sfv, wv)
    app_hm_np = Apply(hm, n, p)
    and_rec_app_m = And(rec_hm, app_hm_np)
    and_sf_ra_m = And(sf_all, and_rec_app_m)

    # Plus(p,k,q): exists w2, h2, sf2. ...
    hp = Var(postfix='hp')
    rec_hp = RecDef(hp, p, sfv, wv)  # same sfv, wv (will unify via omega_unique)
    app_hp_kq = Apply(hp, k, q)
    and_rec_app_p = And(rec_hp, app_hp_kq)
    and_sf_ra_p = And(sf_all, and_rec_app_p)

    # Plus(n,k,r): exists w3, h3, sf3. ...
    hn = Var(postfix='hn')
    rec_hn = RecDef(hn, n, sfv, wv)
    app_hn_kr = Apply(hn, k, r)
    and_rec_app_n = And(rec_hn, app_hn_kr)
    and_sf_ra_n = And(sf_all, and_rec_app_n)

    # The result we want: Plus(m, r, q) = Apply(hm, r, q) wrapped in exists
    app_hm_rq = Apply(hm, r, q)
    plus_mrq = PlusDef(m, r, q)

    # ====================================================================
    # Section 2: Set up the induction predicate
    # ====================================================================
    # P(k) = ∀q',r'. Apply(hp,k,q') → Apply(hn,k,r') → Apply(hm,r',q')
    qv = Var(postfix='qv')
    rv = Var(postfix='rv')
    P_body = Implies(Apply(hp, k, qv), Implies(Apply(hn, k, rv), Apply(hm, rv, qv)))
    P_k = Forall(qv, Forall(rv, P_body))

    # TODO: the full proof body follows plus_comm's structure
    # - Open all 3 Plus, unify omega/sf via omega_unique + sf_apply_transfer
    # - Base case: k=0, use rec_h_zero_identity for hp, hn
    # - Step case: k→S(k), use rec_step_succ for hp, hn, hm
    # - Close by omega_smallest_inductive
    # - Instantiate P(k) with actual q, r to get Apply(hm, r, q)
    # - Fold back into Plus(m, r, q)

    raise NotImplementedError('plus_assoc sections 3-10 TODO')
