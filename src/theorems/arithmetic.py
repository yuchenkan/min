"""Theorems: arithmetic module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from vocab import Empty, OrdPair, Omega, Num

from theorems.logic import (iff_mp, iff_mp_rev, iff_intro, and_intro,
    and_elim_left, and_elim_right, eq_reflexive, eq_substitution)
from theorems.sets import (kuratowski, ordpair_exists, unique_successor,
    eq_successor_transfer)
from theorems.recursion import succ_func_exists


from theorems.recursion import _tuple_inject


def sf_props():
    """Successor function exists with succ_char, Function, and dom_sub.
    Rep, Ext, Pairing |- forall w.
      exists sf. succ_char(sf, w) /\\ Function(sf) /\\ dom_sub(sf, w)
    where succ_char(sf, w) = forall x. In(x,w) -> forall y. Iff(Apply(sf,x,y), Successor(y,x))
    and dom_sub(sf, w) = forall x. (exists y. Apply(sf,x,y)) -> In(x,w)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Relation as RelDef,
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
    # succ_func_exists: ∀w. succ_closed(w) → ∃sf. sf_char
    # Provide succ_closed(w) as hypothesis (callers provide Omega(w) which implies this)
    xsc_tmp = Var(postfix='x')
    sr_tmp = Var(postfix='sr')
    succ_closed = Forall(xsc_tmp, Implies(In(xsc_tmp, w),
        Forall(sr_tmp, Implies(SuccDef(sr_tmp, xsc_tmp), In(sr_tmp, w)))))
    got_sfe = apply_thm(sfe, [w], succ_closed, Exists(sfv, sf_char), ax(succ_closed))

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
    # Build from scratch using the same pattern as cur_dm but without the And(app1,app2).
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

    # Discharge succ_closed (has w free) before closing forall w:
    proof = got_ex
    if any(same(succ_closed, f) for f in proof.sequent.left):
        imp_sc = Implies(succ_closed, proof.sequent.right[0])
        left_sc = [f for f in proof.sequent.left if not same(f, succ_closed)]
        proof = Proof(Sequent(left_sc, [imp_sc]), 'implies_right', [proof], principal=imp_sc)

    # forall w:
    body = proof.sequent.right[0]
    fa_w = Forall(w, body)
    proof = Proof(Sequent(proof.sequent.left, [fa_w]), 'forall_right', [proof], principal=fa_w, term=w)

    proof.name = 'sf_props'
    return proof


def plusfunc_elim(h, w):
    """Decompose PlusFunc(h,w) into its components.
    Returns (got_func, got_dom, got_base, got_step, pf_formula)
    where each got_* has [PlusFunc(h,w)] on left."""
    from tactics import apply_thm, ax
    from vocab.recursion import PlusFunc

    pf = PlusFunc(h, w)
    exp = pf.expand()
    # exp = And(Function(h), And(dom_eq, And(base, step)))
    func_f = exp.left
    r1 = exp.right
    dom_f = r1.left
    r2 = r1.right
    base_f = r2.left
    step_f = r2.right

    got_func = apply_thm(and_elim_left(func_f, r1, []), [], pf, func_f, ax(pf))
    got_r1 = apply_thm(and_elim_right(func_f, r1, []), [], pf, r1, ax(pf))
    got_dom = apply_thm(and_elim_left(dom_f, r2, []), [], r1, dom_f, got_r1)
    got_r2 = apply_thm(and_elim_right(dom_f, r2, []), [], r1, r2, got_r1)
    got_base = apply_thm(and_elim_left(base_f, step_f, []), [], r2, base_f, got_r2)
    got_step = apply_thm(and_elim_right(base_f, step_f, []), [], r2, step_f, got_r2)

    return got_func, got_dom, got_base, got_step, pf


def plus_func_values_agree(h1, h2, w):
    """Values of two PlusFuncs agree on all ⟨m,n⟩ ∈ ω×ω.
    [PlusFunc(h1,w), PlusFunc(h2,w), Omega(w), In(m,w)] |-
        ∀n∈w. ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)

    Omega induction on n. Q(n) = ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p).
    Base Q(0): h1(⟨m,0⟩)=p, PlusFunc base gives h1(⟨m,0⟩)=m, so p=m, PlusFunc base gives h2(⟨m,0⟩)=m.
    Step Q(n)→Q(S(n)): h1(⟨m,S(n)⟩)=p1, step gives h1(⟨m,n⟩)=p with p1=S(p),
        Q(n) gives h2(⟨m,n⟩)=p, step gives h2(⟨m,S(n)⟩)=S(p)=p1."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_intro, and_elim_left, and_elim_right
    from theorems.omega import func_unique_thm, omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.logic import eq_reflexive, eq_substitution, unique_empty, iff_mp, iff_mp_rev
    from theorems.sets import ordpair_exists, successor_exists
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty
    from core.proof import Proof, Sequent, same
    import core.zfc as zfc

    mv = Var(postfix='_mv')
    nv = Var(postfix='_nv')
    snv = Var(postfix='_snv')
    pv = Var(postfix='_pv')
    pair_v = Var(postfix='_pair')
    omega_w = Omega(w)
    in_mv_w = In(mv, w)

    pf1 = PlusFunc(h1, w)
    pf2 = PlusFunc(h2, w)

    # Decompose PlusFuncs
    got_func1, _, got_base1, got_step1, _ = plusfunc_elim(h1, w)
    got_func2, _, got_base2, got_step2, _ = plusfunc_elim(h2, w)
    fu = func_unique_thm()

    # === Base case: Q(0) ===
    # Q(0) = ∀pair. OrdPair(pair,m,0) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # From PlusFunc base for h1: In(m,w) → Empty(z) → OrdPair(pair,m,z) → Apply(h1,pair,m)
    # From PlusFunc base for h2: same → Apply(h2,pair,m)
    # Apply(h1,pair,p) + Apply(h1,pair,m) + Function(h1) → Eq(p,m)
    # Eq(p,m) + Apply(h2,pair,m) → Apply(h2,pair,p) [via eq_apply_val_transfer or similar]

    zv = Var(postfix='_zv')
    op_mz = OrdPair(pair_v, mv, zv)
    empty_z = Empty(zv)

    # Instantiate base1: In(mv,w) → Empty(zv) → OrdPair(pair,mv,zv) → Apply(h1,pair,mv)
    got_b1 = apply_thm(got_base1, [mv])
    got_b1 = mp(got_b1, ax(in_mv_w), in_mv_w, got_b1.sequent.right[0].right)
    got_b1 = apply_thm(got_b1, [zv])
    got_b1 = mp(got_b1, ax(empty_z), empty_z, got_b1.sequent.right[0].right)
    got_b1 = apply_thm(got_b1, [pair_v])
    got_b1 = mp(got_b1, ax(op_mz), op_mz, Apply(h1, pair_v, mv))
    # [pf1, In(mv,w), Empty(zv), OrdPair(pair,mv,zv)] |- Apply(h1, pair, mv)

    # Same for h2:
    got_b2 = apply_thm(got_base2, [mv])
    got_b2 = mp(got_b2, ax(in_mv_w), in_mv_w, got_b2.sequent.right[0].right)
    got_b2 = apply_thm(got_b2, [zv])
    got_b2 = mp(got_b2, ax(empty_z), empty_z, got_b2.sequent.right[0].right)
    got_b2 = apply_thm(got_b2, [pair_v])
    got_b2 = mp(got_b2, ax(op_mz), op_mz, Apply(h2, pair_v, mv))
    # [pf2, In(mv,w), Empty(zv), OrdPair(pair,mv,zv)] |- Apply(h2, pair, mv)

    # func_unique: Apply(h1,pair,p) + Apply(h1,pair,mv) + Function(h1) → Eq(p, mv)
    app1_p = Apply(h1, pair_v, pv)
    eq_p_mv = Eq(pv, mv)
    got_eq_pm = apply_thm(fu, [h1, pair_v, pv, mv])
    got_eq_pm = mp(got_eq_pm, got_func1, FuncDef(h1), got_eq_pm.sequent.right[0].right)
    got_eq_pm = mp(got_eq_pm, ax(app1_p), app1_p, got_eq_pm.sequent.right[0].right)
    got_eq_pm = mp(got_eq_pm, got_b1, Apply(h1, pair_v, mv), eq_p_mv)
    # [pf1, pf2, In(mv,w), Empty(zv), OrdPair(...), Apply(h1,pair,p)] |- Eq(p, mv)

    # Apply(h2,pair,p) from Apply(h2,pair,mv) + Eq(p,mv):
    # Eq(p,mv) → Iff(In(p,x), In(mv,x)) for any x. Use eq_apply_val_transfer.
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()
    # eq_apply_val_transfer: Eq(y1,y2) → Apply(f,x,y1) → Apply(f,x,y2)
    # We have Eq(p,mv). Want Apply(h2,pair,p) from Apply(h2,pair,mv).
    # Need Eq(mv,p) (reverse) to transfer Apply(h2,pair,mv) to Apply(h2,pair,p).
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    eq_mv_p = Eq(mv, pv)
    got_eq_mp = apply_thm(es, [pv, mv], eq_p_mv, eq_mv_p, got_eq_pm)
    got_app2_p = apply_thm(eavt, [h2, pair_v, mv, pv], eq_mv_p,
        Implies(Apply(h2, pair_v, mv), Apply(h2, pair_v, pv)), got_eq_mp)
    got_app2_p = mp(got_app2_p, got_b2, Apply(h2, pair_v, mv), Apply(h2, pair_v, pv))
    # [pf1, pf2, In(mv,w), Empty(zv), OrdPair(...), Apply(h1,pair,p)] |- Apply(h2, pair, p)

    # Discharge: Apply(h1,pair,p), OrdPair, Empty(zv)
    # Close ∀p, ∀pair, ∀zv
    proof_base = got_app2_p
    for hyp in [app1_p, op_mz, empty_z]:
        proof_base = wl(proof_base, hyp)
        imp = Implies(hyp, proof_base.sequent.right[0])
        left = [f for f in proof_base.sequent.left if not same(f, hyp)]
        proof_base = Proof(Sequent(left, [imp]), 'implies_right', [proof_base], principal=imp)
    for v in [pv, pair_v, zv]:
        body = proof_base.sequent.right[0]
        fa = Forall(v, body)
        proof_base = Proof(Sequent(proof_base.sequent.left, [fa]),
            'forall_right', [proof_base], principal=fa, term=v)
    # [pf1, pf2, In(mv,w), Pairing] |- ∀zv. Empty(zv) → ∀pair. OrdPair → ∀p. Apply(h1)→Apply(h2)
    # This IS Q(0) in the form: ∀z.Empty(z)→∀pair.OrdPair(pair,m,z)→∀p.Apply(h1,pair,p)→Apply(h2,pair,p)
    base_formula = proof_base.sequent.right[0]

    # === Step case: Q(n) → Q(S(n)) ===
    # Assume Apply(h1, pair2, p1) where OrdPair(pair2, m, S(n)).
    # PlusFunc step for h1: Apply(h1,⟨m,n⟩,p) → Apply(h1,⟨m,S(n)⟩,S(p)).
    # So p1 = S(p) for some p with Apply(h1,⟨m,n⟩,p).
    # Actually, step gives the forward direction. We need: from Apply(h1,⟨m,S(n)⟩,p1),
    # find p with Apply(h1,⟨m,n⟩,p) and p1=S(p).
    # This requires: h1 is defined at ⟨m,n⟩ (totality), then step gives Apply(h1,⟨m,S(n)⟩,S(p)),
    # then Function gives p1 = S(p).
    # But totality requires dom_eq which is heavy. Let me use a different approach.

    # Stronger Q: Q(n) = ∀pair. OrdPair(pair,m,n) → ∃p. Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # This includes definedness. But then the result isn't in the right form.

    # Actually, the step direction is fine:
    # From Q(n): ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # Plus PlusFunc step: Apply(h1,⟨m,n⟩,p) → Apply(h1,⟨m,S(n)⟩,S(p))
    # Plus PlusFunc step: Apply(h2,⟨m,n⟩,p) → Apply(h2,⟨m,S(n)⟩,S(p))
    # From Apply(h1,⟨m,S(n)⟩,p1): by step for h1 (reverse), there exists p with
    #   Apply(h1,⟨m,n⟩,p) and p1=S(p). But step only goes FORWARD, not backward.

    # The issue: PlusFunc step gives h(⟨m,S(n)⟩)=S(h(⟨m,n⟩)) in the forward direction.
    # To go backward: from Apply(h,⟨m,S(n)⟩,p1), conclude p1=S(p) where Apply(h,⟨m,n⟩,p).
    # This needs: (a) h is defined at ⟨m,n⟩, (b) step gives Apply(h,⟨m,S(n)⟩,S(p)), (c) Function gives p1=S(p).
    # (a) is the definedness/totality issue.

    # Use stronger Q: Q(n) = ∃pair,p. OrdPair(pair,m,n) ∧ Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # "h1 and h2 are both defined at ⟨m,n⟩ and agree"
    # Base: pair=⟨m,0⟩, p=m.
    # Step: from Q(n) get pair0,p with OrdPair(pair0,m,n) ∧ Apply(h1,pair0,p) ∧ Apply(h2,pair0,p).
    #   Step h1: Apply(h1,⟨m,S(n)⟩,S(p)). Step h2: Apply(h2,⟨m,S(n)⟩,S(p)).
    #   pair2=⟨m,S(n)⟩. Q(S(n)) with p2=S(p).

    # Then from Q(n), to prove the actual goal (Apply(h1,pair,p) → Apply(h2,pair,p)):
    # Q(n) gives ∃pair0,p0. ... Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0).
    # Apply(h1,pair,p) with OrdPair(pair,m,n): by ordpair_unique, pair=pair0.
    # By Function(h1): p=p0. So Apply(h2,pair0,p0) = Apply(h2,pair,p). ✓

    # This works but Q is existential. Let me use this stronger Q for the induction,
    # then derive the actual goal from Q + Function + ordpair_unique.

    # For now, let me just use the simpler approach with Q(n) including definedness.
    # Actually, the simplest: omega induction with
    # P(n) = ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # Base: proved above.
    # Step: assume P(n). Show P(S(n)).
    #   Given OrdPair(pair2,m,S(n)), Apply(h1,pair2,p1).
    #   Need Apply(h2,pair2,p1).
    #   From PlusFunc step h1 (instantiated at m,n,pair0,p,sn=S(n),sp=S(p),pair2):
    #     OrdPair(pair0,m,n) → Apply(h1,pair0,p) → Succ(S(n),n) → Succ(S(p),p) → OrdPair(pair2,m,S(n)) → Apply(h1,pair2,S(p))
    #   So Apply(h1,pair2,S(p)) for some p where Apply(h1,pair0,p) and OrdPair(pair0,m,n).
    #   Function(h1): p1 = S(p).
    #   By P(n): Apply(h1,pair0,p) → Apply(h2,pair0,p).
    #   By PlusFunc step h2: Apply(h2,pair2,S(p)) = Apply(h2,pair2,p1). ✓
    #   But we need pair0 and p to exist — i.e., h1 is defined at ⟨m,n⟩.
    #   This is the totality issue again.

    # RESOLUTION: use the STRONG induction predicate that includes definedness:
    # R(n) = ∃pair. OrdPair(pair,m,n) ∧ ∃p. Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # Base: OrdPair(pair0,m,0) from ordpair_exists. Apply(h1,pair0,m) ∧ Apply(h2,pair0,m) from base.
    # Step: R(n) gives pair0, p. Step h1/h2 give pair2=⟨m,S(n)⟩, p2=S(p). R(S(n)) with these.
    # Then: ∀n∈w. R(n). From R(n) + Apply(h1,pair,q) + OrdPair(pair,m,n):
    #   R(n) gives pair0, p with OrdPair(pair0,m,n) ∧ Apply(h1,pair0,p) ∧ Apply(h2,pair0,p).
    #   ordpair_unique: pair = pair0. Function(h1): q = p. So Apply(h2,pair,q). ✓

    # Let me implement this R(n) induction.

    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    app1_0 = Apply(h1, pair0, p0)
    app2_0 = Apply(h2, pair0, p0)
    op_mn = OrdPair(pair0, mv, nv)
    R_body = And(op_mn, And(app1_0, app2_0))
    R_n = Exists(pair0, Exists(p0, R_body))

    # --- R base: R(0) ---
    # ordpair_exists: ∃pair0. OrdPair(pair0, mv, zv)
    # PlusFunc base: Apply(h1, pair0, mv), Apply(h2, pair0, mv)
    # With zv where Empty(zv) (i.e., zv=0):
    # Use omega_contains_empty to get In(0,w), then Num(0)=Empty.
    # Actually for R(0): nv=0 means OrdPair(pair0, mv, 0). Need a zero variable.
    # For omega induction: R is parameterized. The induction var ranges over w.
    # R(e) for Empty(e): pair0=⟨mv,e⟩, p0=mv.

    # This is getting complex. Let me use the standard Separation-based omega induction.
    # Define t = {n ∈ w : R(n)}. Show Inductive(t). omega_smallest_inductive → t = w.

    # For the Separation, the predicate is R(n). Parameters: h1, h2, mv, pair0, p0.
    # But pair0, p0 are existentially bound inside R. The Separation predicate only
    # depends on n (and the parameters h1, h2, mv, w).

    phi = lambda nn: Exists(pair0, Exists(p0,
        And(OrdPair(pair0, mv, nn), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)))))
    sep = zfc.Separation(phi, [h1, h2, mv])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)

    pv_ind = Var(postfix='_pv')
    xv_ind = Var(postfix='_xv')
    char_pv = Forall(xv_ind, Iff(In(xv_ind, pv_ind), And(In(xv_ind, w), phi(xv_ind))))
    got_ex_pv = apply_thm(sep_ax, [mv, h2, h1, w], concl=Exists(pv_ind, char_pv))

    # --- Inductive base: ∀e. Empty(e) → In(e, pv) ---
    ev = Var(postfix='_ev')
    empty_ev = Empty(ev)

    # OrdPair(pair0, mv, ev): exists from ordpair_exists
    oe = ordpair_exists()
    op_mev = OrdPair(pair0, mv, ev)
    got_ex_pair = apply_thm(oe, [mv, ev], concl=Exists(pair0, op_mev))

    # Apply(h1, pair0, mv) from PlusFunc base for h1:
    got_b1_ev = apply_thm(got_base1, [mv])
    got_b1_ev = mp(got_b1_ev, ax(in_mv_w), in_mv_w, got_b1_ev.sequent.right[0].right)
    got_b1_ev = apply_thm(got_b1_ev, [ev])
    got_b1_ev = mp(got_b1_ev, ax(empty_ev), empty_ev, got_b1_ev.sequent.right[0].right)
    got_b1_ev = apply_thm(got_b1_ev, [pair0])
    got_b1_ev = mp(got_b1_ev, ax(op_mev), op_mev, Apply(h1, pair0, mv))

    # Apply(h2, pair0, mv) from PlusFunc base for h2:
    got_b2_ev = apply_thm(got_base2, [mv])
    got_b2_ev = mp(got_b2_ev, ax(in_mv_w), in_mv_w, got_b2_ev.sequent.right[0].right)
    got_b2_ev = apply_thm(got_b2_ev, [ev])
    got_b2_ev = mp(got_b2_ev, ax(empty_ev), empty_ev, got_b2_ev.sequent.right[0].right)
    got_b2_ev = apply_thm(got_b2_ev, [pair0])
    got_b2_ev = mp(got_b2_ev, ax(op_mev), op_mev, Apply(h2, pair0, mv))

    # R(ev) = ∃pair0.∃p0. OrdPair(pair0,mv,ev) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0)
    # With pair0 and p0=mv:
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_apps = mk_and(got_b1_ev, got_b2_ev)
    got_r_body = mk_and(ax(op_mev), got_apps)
    # eir p0=mv, pair0=pair0
    R_body_ev = R_body.subst(nv, ev)  # template with ev, p0 free
    got_r_ev = eir(got_r_body, R_body_ev, p0, mv)
    got_r_ev = eir(got_r_ev, got_r_ev.sequent.right[0], pair0, pair0)
    got_r_ev = eel(got_r_ev, op_mev, pair0)
    got_r_ev = cut(got_r_ev, Exists(pair0, op_mev), got_ex_pair)
    # [pf1, pf2, In(mv,w), Empty(ev), Pairing] |- R(ev)

    # In(ev, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_ev_in_w = apply_thm(oce, [w])
    got_ev_in_w = mp(got_ev_in_w, ax(omega_w), omega_w, got_ev_in_w.sequent.right[0].right)
    got_ev_in_w = apply_thm(got_ev_in_w, [ev])
    got_ev_in_w = mp(got_ev_in_w, ax(empty_ev), empty_ev, In(ev, w))

    # char_bwd: R(ev) + In(ev,w) → In(ev, pv)
    got_inst = apply_thm(ax(char_pv), [ev])
    iff_inst = got_inst.sequent.right[0]
    got_rev_iff = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []), [],
        iff_inst, Implies(iff_inst.right, iff_inst.left), got_inst)
    and_form = iff_inst.right
    ai_base = and_intro(and_form.left, and_form.right, [])
    got_and_base = mp(apply_thm(ai_base, [], and_form.left, Implies(and_form.right, and_form), got_ev_in_w),
        got_r_ev, and_form.right, and_form)
    got_base_in_pv = mp(got_rev_iff, got_and_base, and_form, In(ev, pv_ind))
    # [pf1, pf2, In(mv,w), Empty(ev), char_pv, Omega(w), Pairing] |- In(ev, pv)

    # Discharge Empty(ev), close ∀ev
    imp_empty = Implies(empty_ev, In(ev, pv_ind))
    left_base = [f for f in got_base_in_pv.sequent.left if not same(f, empty_ev)]
    got_ind_base = Proof(Sequent(left_base, [imp_empty]),
        'implies_right', [got_base_in_pv], principal=imp_empty)
    fa_base = Forall(ev, imp_empty)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_base]),
        'forall_right', [got_ind_base], principal=fa_base, term=ev)

    # --- Inductive step: ∀n∈pv. ∀sn. Succ(sn,n) → In(sn, pv) ---
    # From In(nv, pv): char_fwd → And(In(nv,w), R(nv)). Extract R(nv).
    # R(nv) = ∃pair0.∃p0. OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0)
    # Open to get pair0, p0, OrdPair, Apply h1, Apply h2.
    # PlusFunc step h1: Apply(h1,pair0,p0) → Succ(snv,nv) → Succ(sp,p0) → OrdPair(pair2,mv,snv) → Apply(h1,pair2,sp)
    # PlusFunc step h2: same → Apply(h2,pair2,sp)
    # Build R(snv) with pair2, sp. Char_bwd → In(snv, pv).

    succ_sn = SuccDef(snv, nv)
    sp = Var(postfix='_sp')
    succ_sp = SuccDef(sp, p0)
    pair2 = Var(postfix='_pr2')
    op_msn = OrdPair(pair2, mv, snv)
    in_nv_pv = In(nv, pv_ind)

    # char_fwd: In(nv, pv) → And(In(nv,w), R(nv))
    got_fwd_inst = apply_thm(ax(char_pv), [nv])
    iff_fwd = got_fwd_inst.sequent.right[0]
    got_fwd = apply_thm(iff_mp(iff_fwd.left, iff_fwd.right, []), [],
        iff_fwd, Implies(In(nv, pv_ind), iff_fwd.right), got_fwd_inst)
    got_and_nv = mp(got_fwd, ax(in_nv_pv), in_nv_pv, iff_fwd.right)
    got_in_nv_w = apply_thm(and_elim_left(In(nv, w), phi(nv), []), [],
        iff_fwd.right, In(nv, w), got_and_nv)
    got_r_nv = apply_thm(and_elim_right(In(nv, w), phi(nv), []), [],
        iff_fwd.right, phi(nv), got_and_nv)
    # [char_pv, In(nv,pv)] |- R(nv) = ∃pair0.∃p0. body

    # Open R(nv): get pair0, p0, OrdPair, Apply h1, Apply h2
    r_body_nv = And(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)))
    got_op_nv = apply_thm(and_elim_left(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), []), [],
        r_body_nv, OrdPair(pair0, mv, nv), ax(r_body_nv))
    got_apps_nv = apply_thm(and_elim_right(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), []), [],
        r_body_nv, And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), ax(r_body_nv))
    got_app1_nv = apply_thm(and_elim_left(Apply(h1, pair0, p0), Apply(h2, pair0, p0), []), [],
        And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), Apply(h1, pair0, p0), got_apps_nv)
    got_app2_nv = apply_thm(and_elim_right(Apply(h1, pair0, p0), Apply(h2, pair0, p0), []), [],
        And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), Apply(h2, pair0, p0), got_apps_nv)
    # [r_body_nv] |- OrdPair(pair0,mv,nv), Apply(h1,pair0,p0), Apply(h2,pair0,p0)

    # PlusFunc step h1: In(mv,w) → In(nv,w) → OrdPair(pair0,mv,nv) → Apply(h1,pair0,p0) →
    #   Succ(snv,nv) → Succ(sp,p0) → OrdPair(pair2,mv,snv) → Apply(h1,pair2,sp)
    got_s1 = apply_thm(got_step1, [mv])
    got_s1 = mp(got_s1, ax(in_mv_w), in_mv_w, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [nv])
    got_s1 = mp(got_s1, got_in_nv_w, In(nv, w), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair0])
    got_s1 = mp(got_s1, got_op_nv, OrdPair(pair0, mv, nv), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [p0])
    got_s1 = mp(got_s1, got_app1_nv, Apply(h1, pair0, p0), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [snv])
    got_s1 = mp(got_s1, ax(succ_sn), succ_sn, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [sp])
    got_s1 = mp(got_s1, ax(succ_sp), succ_sp, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair2])
    got_s1 = mp(got_s1, ax(op_msn), op_msn, Apply(h1, pair2, sp))
    # [pf1, r_body_nv, char_pv, In(nv,pv), In(mv,w), Succ(snv,nv), Succ(sp,p0), OrdPair(pair2,mv,snv)] |- Apply(h1,pair2,sp)

    # Same for h2:
    got_s2 = apply_thm(got_step2, [mv])
    got_s2 = mp(got_s2, ax(in_mv_w), in_mv_w, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [nv])
    got_s2 = mp(got_s2, got_in_nv_w, In(nv, w), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair0])
    got_s2 = mp(got_s2, got_op_nv, OrdPair(pair0, mv, nv), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [p0])
    got_s2 = mp(got_s2, got_app2_nv, Apply(h2, pair0, p0), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [snv])
    got_s2 = mp(got_s2, ax(succ_sn), succ_sn, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp])
    got_s2 = mp(got_s2, ax(succ_sp), succ_sp, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair2])
    got_s2 = mp(got_s2, ax(op_msn), op_msn, Apply(h2, pair2, sp))
    # [pf2, r_body_nv, ...] |- Apply(h2,pair2,sp)

    # Build R(snv): ∃pair2.∃sp. OrdPair(pair2,mv,snv) ∧ Apply(h1,pair2,sp) ∧ Apply(h2,pair2,sp)
    got_apps_sn = mk_and(got_s1, got_s2)
    got_r_body_sn = mk_and(ax(op_msn), got_apps_sn)
    got_r_sn = eir(got_r_body_sn, got_r_body_sn.sequent.right[0], sp, sp)
    got_r_sn = eir(got_r_sn, got_r_sn.sequent.right[0], pair2, pair2)
    # eel OrdPair(pair2,...), Succ(sp,...) from left
    got_r_sn = eel(got_r_sn, op_msn, pair2)
    got_ex_pair2 = apply_thm(oe, [mv, snv], concl=Exists(pair2, op_msn))
    got_r_sn = cut(got_r_sn, Exists(pair2, op_msn), got_ex_pair2)
    got_r_sn = eel(got_r_sn, succ_sp, sp)
    got_ex_sp = apply_thm(successor_exists(), [p0], concl=Exists(sp, succ_sp))
    got_r_sn = cut(got_r_sn, Exists(sp, succ_sp), got_ex_sp)
    # [pf1, pf2, r_body_nv, char_pv, In(nv,pv), In(mv,w), Succ(snv,nv), Pairing] |- R(snv)

    # In(snv, w) from omega_succ_closed:
    osc2 = omega_succ_closed()
    got_sn_in_w = apply_thm(osc2, [w])
    got_sn_in_w = mp(got_sn_in_w, ax(omega_w), omega_w, got_sn_in_w.sequent.right[0].right)
    got_sn_in_w = apply_thm(got_sn_in_w, [nv])
    got_sn_in_w = mp(got_sn_in_w, got_in_nv_w, In(nv, w), got_sn_in_w.sequent.right[0].right)
    got_sn_in_w = apply_thm(got_sn_in_w, [snv])
    got_sn_in_w = mp(got_sn_in_w, ax(succ_sn), succ_sn, In(snv, w))

    # char_bwd: R(snv) + In(snv,w) → In(snv, pv)
    got_inst_sn = apply_thm(ax(char_pv), [snv])
    iff_sn = got_inst_sn.sequent.right[0]
    got_rev_sn = apply_thm(iff_mp_rev(iff_sn.left, iff_sn.right, []), [],
        iff_sn, Implies(iff_sn.right, iff_sn.left), got_inst_sn)
    and_form_sn = iff_sn.right
    ai_sn = and_intro(and_form_sn.left, and_form_sn.right, [])
    got_and_sn = mp(apply_thm(ai_sn, [], and_form_sn.left, Implies(and_form_sn.right, and_form_sn), got_sn_in_w),
        got_r_sn, and_form_sn.right, and_form_sn)
    got_step_in_pv = mp(got_rev_sn, got_and_sn, and_form_sn, In(snv, pv_ind))

    # eel r_body_nv (pair0, p0), cut with got_r_nv
    got_step_in_pv = eel(got_step_in_pv, r_body_nv, p0)
    got_step_in_pv = eel(got_step_in_pv, Exists(p0, r_body_nv), pair0)
    got_step_in_pv = cut(got_step_in_pv, phi(nv), got_r_nv)

    # Discharge Succ(snv,nv), In(nv,pv). Close ∀snv, ∀nv.
    imp_succ = Implies(succ_sn, got_step_in_pv.sequent.right[0])
    left_step = [f for f in got_step_in_pv.sequent.left if not same(f, succ_sn)]
    got_step_in_pv = Proof(Sequent(left_step, [imp_succ]),
        'implies_right', [got_step_in_pv], principal=imp_succ)
    fa_sn = Forall(snv, imp_succ)
    got_step_in_pv = Proof(Sequent(got_step_in_pv.sequent.left, [fa_sn]),
        'forall_right', [got_step_in_pv], principal=fa_sn, term=snv)
    imp_nv = Implies(in_nv_pv, fa_sn)
    left_nv = [f for f in got_step_in_pv.sequent.left if not same(f, in_nv_pv)]
    got_ind_step = Proof(Sequent(left_nv, [imp_nv]),
        'implies_right', [got_step_in_pv], principal=imp_nv)
    fa_nv = Forall(nv, imp_nv)
    got_ind_step = Proof(Sequent(got_ind_step.sequent.left, [fa_nv]),
        'forall_right', [got_ind_step], principal=fa_nv, term=nv)

    # === Inductive(pv) → pv = w → R holds for all n∈w ===
    from vocab import Inductive, Subset
    ind_pv = And(fa_base, fa_nv)
    ai_ind = and_intro(fa_base, fa_nv, [])
    all_ctx = list(got_ind_base.sequent.left)
    for f in got_ind_step.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_ind = mp(apply_thm(ai_ind, [], fa_base, Implies(fa_nv, ind_pv),
        weaken_to(got_ind_base, all_ctx)),
        weaken_to(got_ind_step, all_ctx), fa_nv, ind_pv)

    # Subset(pv, w):
    xs = Var(postfix='_xs')
    got_fwd_xs = apply_thm(ax(char_pv), [xs])
    iff_xs = got_fwd_xs.sequent.right[0]
    got_fwd_x = apply_thm(iff_mp(iff_xs.left, iff_xs.right, []), [],
        iff_xs, Implies(In(xs, pv_ind), iff_xs.right), got_fwd_xs)
    got_in_xs_w = mp(got_fwd_x, ax(In(xs, pv_ind)), In(xs, pv_ind), iff_xs.right)
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), iff_xs.right.right, []), [],
        iff_xs.right, In(xs, w), got_in_xs_w)
    imp_sub = Implies(In(xs, pv_ind), In(xs, w))
    left_sub = [f for f in got_in_xs_w.sequent.left if not same(f, In(xs, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_in_xs_w], principal=imp_sub)
    sub_pv_w = Forall(xs, imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [sub_pv_w]),
        'forall_right', [got_sub], principal=sub_pv_w, term=xs)

    # omega_smallest_inductive: Omega(w) → Subset(pv,w) → Inductive(pv) → Eq(pv,w)
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv_ind, w)
    got_osi = apply_thm(osi, [pv_ind, w])
    while isinstance(got_osi.sequent.right[0], Implies):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    # Cut with proofs:
    all_osi = list(all_ctx)
    for f in got_sub.sequent.left:
        if not any(same(f, g) for g in all_osi):
            all_osi.append(f)
    got_and_si = mk_and(weaken_to(got_sub, all_osi), weaken_to(got_ind, all_osi))
    non_ax = [f for f in got_osi.sequent.left
        if not isinstance(f, zfc.ZFCAxiom) and not same(f, omega_w)]
    for h in non_ax:
        got_osi = cut(got_osi, h, got_and_si)

    # Eq(pv,w): ∀n∈w. In(n,pv). So ∀n∈w. R(n).
    # Extract R(nv) from In(nv, pv):
    # In(nv, pv) ↔ In(nv, w) via Eq(pv,w). So In(nv,w) → In(nv,pv).
    iff_nv_pw = Iff(In(nv, pv_ind), In(nv, w))
    got_iff_nv = cut(fl(eq_pv_w, iff_nv_pw, nv), eq_pv_w, got_osi)
    got_in_nv_pv = mp(apply_thm(iff_mp_rev(In(nv, pv_ind), In(nv, w), []), [],
        iff_nv_pw, Implies(In(nv, w), In(nv, pv_ind)), got_iff_nv),
        ax(In(nv, w)), In(nv, w), In(nv, pv_ind))
    # char_fwd → R(nv)
    got_and_final = cut(got_and_nv, in_nv_pv, got_in_nv_pv)
    got_r_final = apply_thm(and_elim_right(In(nv, w), phi(nv), []), [],
        iff_fwd.right, phi(nv), got_and_final)
    # [char_pv, In(nv,w), ...axioms...] |- R(nv) = ∃pair0.∃p0. body(nv)

    # From R(nv) + Apply(h1,pair,p) + OrdPair(pair,m,nv):
    # R(nv) gives pair0,p0 with OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0).
    # ordpair_unique: pair = pair0 (both are ⟨mv,nv⟩). func_unique: p = p0.
    # So Apply(h2,pair,p).
    # This derivation needs ~30 more lines. For now, return got_r_final for testing.

    # eel char_pv/pv_ind, cut with got_ex_pv
    got_r_final = eel(got_r_final, char_pv, pv_ind)
    got_r_final = cut(got_r_final, Exists(pv_ind, char_pv), got_ex_pv)

    got_r_final.name = 'plus_func_values_agree'
    return got_r_final


def plus_func_eq():
    """Two PlusFuncs over the same omega are equal.
    |- ∀w,h1,h2. Omega(w) → PlusFunc(h1,w) → PlusFunc(h2,w) → Eq(h1,h2)

    From plus_func_values_agree: for all m,n∈w, h1(⟨m,n⟩)=h2(⟨m,n⟩).
    Transfer: In(z,h1) → Relation gives z=⟨x,y⟩ → Apply(h1,x,y) →
    dom_eq gives x∈ω×ω → Product gives x=⟨m,n⟩ → values_agree → Apply(h2,x,y) → In(z,h2).
    Symmetry + extensionality → Eq(h1,h2)."""
    # TODO: implement - needs membership transfer via values_agree + dom_eq
    raise NotImplementedError("plus_func_eq under construction")


def plus_func_exists():
    """The addition function exists.
    |- ∀w. Omega(w) → ∃h. PlusFunc(h, w)

    Construction via Separation: collect Recursive outputs for each m."""
    # TODO: implement
    raise NotImplementedError("plus_func_exists proof under construction")


def plus_func_unique():
    """The addition function exists and is unique.
    |- ∀w. Omega(w) → ∃!h. PlusFunc(h, w)

    Combines plus_func_exists + plus_func_eq."""
    # TODO: combine plus_func_exists + plus_func_eq into ExistsUnique
    raise NotImplementedError("plus_func_unique: needs plus_func_exists + plus_func_eq")


def plus_setup():
    """Plus function setup: sf and h exist for any m ∈ ω.
    |- ∀w,m. Omega(w) → In(m,w) → ∃h,sf. sf_props(sf,w) ∧ Recursive(h,m,sf,w)

    Combines succ_func_exists (∃sf) + recursion_theorem (∃!h).
    Proved once; used by all Plus theorems to get h and sf."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp_rev
    from theorems.recursion import succ_func_exists, recursion_theorem
    from theorems.omega import omega_succ_closed
    from theorems.sets import successor_exists
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, TotalFrom)
    from vocab.omega import ExistsUnique
    from core.proof import Proof, Sequent, same

    w = Var(postfix='w')
    m = Var(postfix='m')
    omega_w = Omega(w)
    in_m_w = In(m, w)

    # === Get sf from succ_func_exists ===
    osc = omega_succ_closed()
    got_osc = apply_thm(osc, [w])
    got_sc = mp(got_osc, ax(omega_w), omega_w, got_osc.sequent.right[0].right)

    sfe = succ_func_exists()
    got_sfe = apply_thm(sfe, [w])
    got_ex_sf = mp(got_sfe, got_sc, got_sc.sequent.right[0], got_sfe.sequent.right[0].right)
    # [axioms, Omega(w)] |- ∃sf. sf_props(sf, w)

    # Open ∃sf to get sf_all on left
    sfv = Var(postfix='sfv')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    got_func_sf = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        And(func_sf, dom_sub_sf), func_sf,
        apply_thm(and_elim_right(succ_char, And(func_sf, dom_sub_sf), []), [],
            sf_all, And(func_sf, dom_sub_sf), ax(sf_all)))

    # === TotalFrom(sf, m) ===
    sm = Var(postfix='sm')
    succ_sm = SuccDef(sm, m)
    got_ex_sm = apply_thm(successor_exists(), [m], concl=Exists(sm, succ_sm))
    got_sc_m = apply_thm(ax(succ_char), [m], In(m, w),
        Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m))), ax(In(m, w)))
    got_sc_m = apply_thm(got_sc_m, [sm])
    iff_f = got_sc_m.sequent.right[0]
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_sc_m)
    got_app_sf = mp(got_rev, ax(succ_sm), succ_sm, iff_f.left)
    got_total = eir(got_app_sf, got_app_sf.sequent.right[0], sm, sm)
    got_total = eel(got_total, succ_sm, sm)
    got_total = cut(got_total, Exists(sm, succ_sm), got_ex_sm)
    # [succ_char, In(m,w), Pairing] |- TotalFrom(sf, m)

    # === Get h from recursion_theorem ===
    rt = recursion_theorem()
    got_rt = apply_thm(rt, [m, sfv, w])
    while isinstance(got_rt.sequent.right[0], Implies):
        cur = got_rt.sequent.right[0]
        hyp = cur.left
        if same(hyp, func_sf):
            got_rt = mp(got_rt, got_func_sf, hyp, cur.right)
        elif same(hyp, omega_w):
            got_rt = mp(got_rt, ax(omega_w), hyp, cur.right)
        else:
            # TotalFrom or other — try got_total or ax
            if any(same(hyp, f) for f in got_total.sequent.left) or same(hyp, got_total.sequent.right[0]):
                got_rt = mp(got_rt, got_total, hyp, cur.right)
            else:
                got_rt = mp(got_rt, ax(hyp), hyp, cur.right)
    # [...] |- ∃!h. Recursive(h, m, sf, w)

    # ExistsUnique → ∃h. Recursive(h, m, sf, w) (drop uniqueness)
    eu = got_rt.sequent.right[0]
    eu_exp = eu.expand()
    eu_hv = eu_exp.var
    eu_body = eu_exp.body  # And(Rec, ∀h'.Rec→Eq)
    got_rec_only = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    # [And(Rec,uniq)] |- Recursive(hv, m, sf, w)

    # Build And(sf_all, Recursive)
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_sf_rec = mk_and(ax(sf_all), got_rec_only)
    # [sf_all, And(Rec,uniq)] |- And(sf_all, Recursive)

    # eir h (eu_hv), eel And(Rec,uniq), cut with got_rt
    got_ex_h = eir(got_sf_rec, got_sf_rec.sequent.right[0], eu_hv, eu_hv)
    got_ex_h = eel(got_ex_h, eu_body, eu_hv)
    got_ex_h = cut(got_ex_h, eu.expand(), got_rt)

    # Cut TotalFrom before eel (it has sfv free)
    total_sf_m = TotalFrom(sfv, m)
    if any(same(total_sf_m, f) for f in got_ex_h.sequent.left):
        print(f'total_sf_m: {total_sf_m}')
        print(f'got_total right: {got_total.sequent.right[0]}')
        print(f'same: {same(total_sf_m, got_total.sequent.right[0])}')
        got_ex_h = cut(got_ex_h, total_sf_m, got_total)

    # eir sf (sfv), eel sf_all, cut with got_ex_sf
    got_ex_sf_h = eir(got_ex_h, got_ex_h.sequent.right[0], sfv, sfv)
    got_ex_sf_h = eel(got_ex_sf_h, sf_all, sfv)
    got_ex_sf_h = cut(got_ex_sf_h, got_ex_sf.sequent.right[0], got_ex_sf)
    if any(same(total_sf_m, f) for f in got_ex_sf_h.sequent.left):
        got_ex_sf_h = cut(got_ex_sf_h, total_sf_m, got_total)

    # Discharge and close
    proof = got_ex_sf_h
    for hyp in [in_m_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [m, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'plus_setup'
    return proof


def plus_zero_right():
    """m + 0 = m: Given Plus(a,b,c) and Num(b,0), derive Eq(c,a).
    |- forall w,a,b,c,h. Omega(w) -> In(a,w) -> Num(b,0) -> Plus(a,b,c) -> PlusFunc(h,w) -> Eq(c,a)

    With PlusFunc-based Plus: instantiate Plus with w,h to get Apply(h,⟨a,b⟩,c).
    From PlusFunc base: Apply(h,⟨a,0⟩,a). Function(h) → Eq(c,a)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from theorems.logic import and_elim_left, and_elim_right
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists
    from core.proof import Proof, Sequent, same

    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    num_b_0 = Num(b, 0)  # = Empty(b)
    plus_abc = PlusDef(a, b, c)
    pf_hw = PlusFunc(hv, w)
    eq_ca = Eq(c, a)

    # === Instantiate Plus(a,b,c) with w,h → Apply(h, ⟨a,b⟩, c) ===
    pair_ab = Var(postfix='pab')
    op_ab = OrdPair(pair_ab, a, b)
    app_h_pair_c = Apply(hv, pair_ab, c)

    got_plus = apply_thm(ax(plus_abc), [w])
    while isinstance(got_plus.sequent.right[0], Implies):
        cur = got_plus.sequent.right[0]
        got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
    while isinstance(got_plus.sequent.right[0], Forall):
        got_plus = apply_thm(got_plus, [hv])
        while isinstance(got_plus.sequent.right[0], Implies):
            cur = got_plus.sequent.right[0]
            got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
        if isinstance(got_plus.sequent.right[0], Forall):
            got_plus = apply_thm(got_plus, [pair_ab])
            while isinstance(got_plus.sequent.right[0], Implies):
                cur = got_plus.sequent.right[0]
                got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
    # got_plus: [plus_abc, Omega(w), PlusFunc(h,w), OrdPair(pair,a,b)] |- Apply(h, pair, c)

    # === PlusFunc base: Apply(h, ⟨a,0⟩, a) ===
    pf_exp = pf_hw.expand()
    func_h = pf_exp.left
    r1 = pf_exp.right
    dom_eq_f = r1.left
    r2 = r1.right
    base_f = r2.left
    step_f = r2.right

    got_func = apply_thm(and_elim_left(func_h, r1, []), [], pf_hw, func_h, ax(pf_hw))
    got_r1 = apply_thm(and_elim_right(func_h, r1, []), [], pf_hw, r1, ax(pf_hw))
    got_r2 = apply_thm(and_elim_right(dom_eq_f, r2, []), [], r1, r2, got_r1)
    got_base = apply_thm(and_elim_left(base_f, step_f, []), [], r2, base_f, got_r2)
    # [PlusFunc(h,w)] |- base_f = ∀m∈w. ∀z. Empty(z) → ∀pair. OrdPair(pair,m,z) → Apply(h,pair,m)

    # Instantiate base at a, b, pair_ab:
    got_base_inst = got_base
    while isinstance(got_base_inst.sequent.right[0], Forall):
        f = got_base_inst.sequent.right[0]
        # Pick the right term for each forall
        got_base_inst = apply_thm(got_base_inst, [a])
        while isinstance(got_base_inst.sequent.right[0], Implies):
            cur = got_base_inst.sequent.right[0]
            got_base_inst = mp(got_base_inst, ax(cur.left), cur.left, cur.right)
        if isinstance(got_base_inst.sequent.right[0], Forall):
            got_base_inst = apply_thm(got_base_inst, [b])
            while isinstance(got_base_inst.sequent.right[0], Implies):
                cur = got_base_inst.sequent.right[0]
                got_base_inst = mp(got_base_inst, ax(cur.left), cur.left, cur.right)
            if isinstance(got_base_inst.sequent.right[0], Forall):
                got_base_inst = apply_thm(got_base_inst, [pair_ab])
                while isinstance(got_base_inst.sequent.right[0], Implies):
                    cur = got_base_inst.sequent.right[0]
                    got_base_inst = mp(got_base_inst, ax(cur.left), cur.left, cur.right)
    # [PlusFunc(h,w), In(a,w), Num(b,0), OrdPair(pair,a,b)] |- Apply(h, pair, a)

    # === func_unique: Eq(c, a) ===
    fut = func_unique_thm()
    got_eq = apply_thm(fut, [hv, pair_ab, c, a])
    got_eq = mp(got_eq, got_func, func_h, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_plus, app_h_pair_c, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_base_inst, got_base_inst.sequent.right[0], eq_ca)
    # [..., OrdPair(pair,a,b)] |- Eq(c, a)

    # === eel pair, cut with ordpair_exists ===
    got_eq = eel(got_eq, op_ab, pair_ab)
    oe = ordpair_exists()
    got_ex_pair = apply_thm(oe, [a, b], concl=Exists(pair_ab, op_ab))
    got_eq = cut(got_eq, Exists(pair_ab, op_ab), got_ex_pair)

    # === Discharge PlusFunc(h,w) and close h first (internal) ===
    proof = got_eq
    if not any(same(pf_hw, f) for f in proof.sequent.left):
        proof = wl(proof, pf_hw)
    imp_pf = Implies(pf_hw, proof.sequent.right[0])
    left_pf = [f for f in proof.sequent.left if not same(f, pf_hw)]
    proof = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [proof], principal=imp_pf)
    fa_h = Forall(hv, imp_pf)
    proof = Proof(Sequent(proof.sequent.left, [fa_h]), 'forall_right',
        [proof], principal=fa_h, term=hv)
    # Now h is bound. The right side is ∀h. PlusFunc(h,w) → Eq(c,a).

    # Discharge remaining hypotheses
    for hyp in [plus_abc, num_b_0, in_a_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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
    # Use apply_thm with 3 terms and hyp=None:
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
    from vocab import Inductive as InductiveDef, Subset as SubsetDef
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
    """0 + m = m: Given Plus(b,a,c) and Num(b,0), derive Eq(c,a).
    |- forall w,a,b,c. Omega(w) -> In(a,w) -> Num(b,0) -> Plus(b,a,c) -> Eq(c,a)
    Opens Plus to get Recursive(h,b,sf,w') and Apply(h,a,c).
    From rec_h_zero_identity: h(m)=m for all m. So Apply(h,a,a).
    From func_unique: Eq(c,a)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef)
    from theorems.omega import func_unique_thm
    from theorems.sets import omega_unique
    from theorems.logic import and_elim_left, and_elim_right, iff_mp

    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    num_b_0 = Num(b, 0)
    plus_bac = PlusDef(b, a, c)
    eq_ca = Eq(c, a)

    goal = Forall(w, Forall(a, Forall(b, Forall(c,
        Implies(omega_w, Implies(in_a_w, Implies(num_b_0,
            Implies(plus_bac, eq_ca))))))))

    # Open Plus(b,a,c)
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
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))
    rec_h = RecDef(hv, b, sfv, wv)
    app_h_ac = Apply(hv, a, c)
    and_rec_app = And(rec_h, app_h_ac)
    and_sf_ra = And(sf_all, and_rec_app)

    got_rec = apply_thm(and_elim_left(rec_h, app_h_ac, []), [],
        and_rec_app, rec_h, ax(and_rec_app))
    got_app_ac = apply_thm(and_elim_right(rec_h, app_h_ac, []), [],
        and_rec_app, app_h_ac, ax(and_rec_app))
    got_sc = apply_thm(and_elim_left(succ_char, And(func_sf, dom_sub_sf), []), [],
        sf_all, succ_char, apply_thm(and_elim_left(sf_all, and_rec_app, []), [],
            and_sf_ra, sf_all, ax(and_sf_ra)))

    # Extract Function(h)
    func_h = FuncDef(hv)
    ev = Var()
    base_h = Forall(ev, Implies(Empty(ev), Apply(hv, ev, b)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, wv),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, wv)))
    and_bs = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_bs)

    got_func_h = apply_thm(and_elim_left(func_h, and_dom_bs, []), [],
        rec_h, func_h, got_rec)

    # rec_h_zero_identity: Omega(wv) -> succ_char -> Recursive(h,b,sf,wv) -> Empty(b) ->
    #   forall m. In(m,wv) -> Apply(h,m,m)
    rhi = rec_h_zero_identity()
    mv_rhi = Var(postfix='m')
    app_h_mm = Apply(hv, mv_rhi, mv_rhi)
    got_hmm = apply_thm(rhi, [wv, sfv, hv, b], omega_wv,
        Implies(succ_char, Implies(rec_h, Implies(num_b_0,
            Forall(mv_rhi, Implies(In(mv_rhi, wv), app_h_mm))))), ax(omega_wv))
    got_hmm = mp(got_hmm, got_sc, succ_char,
        Implies(rec_h, Implies(num_b_0, Forall(mv_rhi, Implies(In(mv_rhi, wv), app_h_mm)))))
    got_hmm = mp(got_hmm, got_rec, rec_h,
        Implies(num_b_0, Forall(mv_rhi, Implies(In(mv_rhi, wv), app_h_mm))))
    got_hmm = mp(got_hmm, ax(num_b_0), num_b_0,
        Forall(mv_rhi, Implies(In(mv_rhi, wv), app_h_mm)))
    # [and_rec_app, and_sf_ra, omega_wv, num_b_0, axioms] |- forall m. In(m,wv) -> Apply(h,m,m)

    # Need In(a, wv) from omega_unique: Eq(w, wv) + In(a, w) -> In(a, wv)
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_w_wv = apply_thm(ou, [w, wv], omega_w,
        Implies(omega_wv, eq_w_wv), ax(omega_w))
    got_eq_w_wv = mp(got_eq_w_wv, ax(omega_wv), omega_wv, eq_w_wv)
    in_a_wv = In(a, wv)
    iff_in_a = Iff(In(a, w), in_a_wv)
    got_iff = Proof(Sequent(got_eq_w_wv.sequent.left, [iff_in_a]), 'cut',
        [wr(got_eq_w_wv, iff_in_a),
         weaken_to(fl(eq_w_wv, iff_in_a, a), got_eq_w_wv.sequent.left)],
        principal=eq_w_wv)
    got_in_a_wv = mp(mp(iff_mp(In(a, w), in_a_wv, []),
        got_iff, iff_in_a, Implies(In(a, w), in_a_wv)),
        ax(in_a_w), in_a_w, in_a_wv)

    # Apply(h,a,a)
    app_h_aa = Apply(hv, a, a)
    got_app_aa = apply_thm(got_hmm, [a], in_a_wv, app_h_aa, got_in_a_wv)

    # func_unique: Apply(h,a,c) + Apply(h,a,a) -> Eq(c,a)
    fut = func_unique_thm()
    got_eq = apply_thm(fut, [hv, a, c, a], func_h,
        Implies(app_h_ac, Implies(app_h_aa, eq_ca)), got_func_h)
    got_eq = mp(got_eq, got_app_ac, app_h_ac, Implies(app_h_aa, eq_ca))
    got_eq = mp(got_eq, got_app_aa, app_h_aa, eq_ca)

    # Fold back: and_rec_app came from and_sf_ra. Cut and_rec_app → and_sf_ra stays.
    # Then: eel sfv, hv from and_sf_ra. omega_wv is standalone on left.
    # Fold omega_wv + exists into And(omega_wv, exists) via cut.
    got_ra = apply_thm(and_elim_right(sf_all, and_rec_app, []), [],
        and_sf_ra, and_rec_app, ax(and_sf_ra))
    got_eq = cut(got_eq, and_rec_app, got_ra)
    # succ_char may also be on left from got_sc; cut it from and_sf_ra too
    got_sc_from = apply_thm(and_elim_left(succ_char, And(func_sf, dom_sub_sf), []), [],
        sf_all, succ_char, apply_thm(and_elim_left(sf_all, and_rec_app, []), [],
            and_sf_ra, sf_all, ax(and_sf_ra)))
    if any(same(succ_char, g) for g in got_eq.sequent.left):
        got_eq = cut(got_eq, succ_char, got_sc_from)
    got_eq = eel(got_eq, and_sf_ra, sfv)
    got_eq = eel(got_eq, got_eq.sequent.left[-1], hv)
    ex_h_left = got_eq.sequent.left[-1]
    and_omega_ex = And(omega_wv, Exists(hv, Exists(sfv, and_sf_ra)))
    got_omega_wv = apply_thm(and_elim_left(omega_wv, Exists(hv, Exists(sfv, and_sf_ra)), []), [],
        and_omega_ex, omega_wv, ax(and_omega_ex))
    got_eq = cut(got_eq, omega_wv, got_omega_wv)
    got_ex_h = apply_thm(and_elim_right(omega_wv, Exists(hv, Exists(sfv, and_sf_ra)), []), [],
        and_omega_ex, Exists(hv, Exists(sfv, and_sf_ra)), ax(and_omega_ex))
    got_eq = cut(got_eq, ex_h_left, got_ex_h)
    got_eq = eel(got_eq, and_omega_ex, wv)

    # Discharge hypotheses
    proof = got_eq
    g4 = goal.body.body.body  # Forall(c, ...)
    g_imp = g4.body
    hyps_imps = []
    cur_imp = g_imp
    while isinstance(cur_imp, Implies):
        hyps_imps.append((cur_imp.left, cur_imp))
        cur_imp = cur_imp.right

    for hh in [omega_w, in_a_w]:
        if not any(same(hh, g) for g in proof.sequent.left):
            proof = wl(proof, hh)

    for hh, imp in reversed(hyps_imps):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa_target in [(c, g4), (b, goal.body.body), (a, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa_target]), 'forall_right',
            [proof], principal=fa_target, term=var)

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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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

    # Close: implies_right Succ(sv,yv), implies_right Apply(h2,eb,yv), forall_right sv, forall_right yv
    # This matches P(eb) = Forall(yv, Forall(sv, Implies(Apply(h2,eb,yv), Implies(succ_sy, Apply(h1,eb,sv)))))
    imp_s = Implies(succ_sy, Apply(h1, eb, sv))
    rem_s = [f_ for f_ in got_h1_es.sequent.left if not same(f_, succ_sy)]
    cur_base = Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_h1_es], principal=imp_s)
    imp_h2_s = Implies(Apply(h2, eb, yv), imp_s)
    rem_app = [f_ for f_ in cur_base.sequent.left if not same(f_, Apply(h2, eb, yv))]
    cur_base = Proof(Sequent(rem_app, [imp_h2_s]), 'implies_right', [cur_base], principal=imp_h2_s)
    fa_sv_body = Forall(sv, imp_h2_s)
    cur_base = Proof(Sequent(rem_app, [fa_sv_body]), 'forall_right',
        [cur_base], principal=fa_sv_body, term=sv)
    p_eb_formula = Forall(yv, fa_sv_body)
    cur_base = Proof(Sequent(rem_app, [p_eb_formula]), 'forall_right', [cur_base], principal=p_eb_formula, term=yv)
    # cur_base: [...] |- P(eb)

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
    from vocab import Inductive as InductiveDef, Subset as SubsetDef
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
    from vocab import (Apply, Successor as SuccDef)

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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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
    # sf_props now: ∀w. succ_closed(w) → ∃sf. and_sc_fd
    # Derive succ_closed from omega_w via omega_succ_closed
    from theorems.omega import omega_succ_closed as _osc_thm
    osc = _osc_thm()
    xsc_tmp = Var(postfix='x')
    sr_tmp = Var(postfix='sr')
    succ_closed_w = Forall(xsc_tmp, Implies(In(xsc_tmp, w),
        Forall(sr_tmp, Implies(SuccDef(sr_tmp, xsc_tmp), In(sr_tmp, w)))))
    got_sc_w = apply_thm(osc, [w], omega_w, succ_closed_w, ax(omega_w))
    got_sp = apply_thm(sp, [w], succ_closed_w, Exists(sfv, and_sc_fd), got_sc_w)
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

    # === Step F: Transfer Plus(mv, nv_final, pv_final) to Plus(mv, nv_final, cv) ===
    # Using unique_num(p_val): Num(cv, p_val) ∧ Num(pv_final, p_val) → Eq(cv, pv_final)
    # Then eq_apply_val_transfer + repackaging
    cv = Var(postfix='cv')
    num_cv = NumDef(cv, p_val)
    num_pv = NumDef(pv_final, p_val)
    plus_result = PlusDef(mv, nv_final, pv_final)

    # cur: [...] |- Plus(mv, nv_final, pv_final)
    # got_num_p: [...] |- Num(pv_final, p_val)

    # Get unique_num(p_val) for the uniqueness argument
    un = unique_num(p_val)
    # un: [axioms] |- ExistsUnique(a, Num(a, p_val))
    # Expanded: Exists(a, And(Num(a,p_val), Forall(v, Num(v,p_val)→Eq(a,v))))

    # Open ExistsUnique to get Num(witness, p_val) and uniqueness forall
    wit = Var(postfix='wit')
    v_un = Var()
    num_wit = NumDef(wit, p_val)
    uniq_part = Forall(v_un, Implies(NumDef(v_un, p_val), Eq(wit, v_un)))
    and_un = And(num_wit, uniq_part)

    got_uniq_forall = apply_thm(and_elim_right(num_wit, uniq_part, []), [],
        and_un, uniq_part, ax(and_un))

    # Instantiate at cv and pv_final:
    got_eq_wit_cv = apply_thm(got_uniq_forall, [cv], num_cv, Eq(wit, cv), ax(num_cv))
    got_eq_wit_pv = apply_thm(got_uniq_forall, [pv_final], num_pv, Eq(wit, pv_final), got_num_p)

    # eq_symmetric + eq_transitive: Eq(pv_final, cv)
    from theorems.logic import eq_symmetric, eq_transitive
    es_thm = eq_symmetric()
    et_thm = eq_transitive()

    # Eq(pv_final, wit) from Eq(wit, pv_final)
    got_eq_pv_wit = apply_thm(es_thm, [wit, pv_final],
        Eq(wit, pv_final), Eq(pv_final, wit), got_eq_wit_pv)
    # Eq(pv_final, cv) from Eq(pv_final, wit) + Eq(wit, cv)
    got_eq_pv_cv = apply_thm(et_thm, [pv_final, wit, cv],
        Eq(pv_final, wit), Implies(Eq(wit, cv), Eq(pv_final, cv)), got_eq_pv_wit)
    got_eq_pv_cv = mp(got_eq_pv_cv, got_eq_wit_cv, Eq(wit, cv), Eq(pv_final, cv))

    # eel wit from and_un, cut with un
    got_eq_pv_cv = eel(got_eq_pv_cv, and_un, wit)
    got_eq_pv_cv = cut(got_eq_pv_cv, got_eq_pv_cv.sequent.left[-1], un)
    # [Num(cv, p_val), Num(pv_final, p_val) (from got_num_p), axioms] |- Eq(pv_final, cv)

    # Transfer: Plus(mv, nv_final, pv_final) → Plus(mv, nv_final, cv)
    # Open Plus, transfer Apply via eq_apply_val_transfer, repackage.
    # For simplicity: build the Plus structure directly.

    # Inside Plus(mv,nv_final,pv_final), the only part that changes is Apply(h,nv_final,pv_final).
    # Using eq_apply_val_transfer: Eq(pv_final,cv) → Apply(h,nv_final,pv_final) → Apply(h,nv_final,cv)
    # Then repackage.
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()

    # Build: [Plus(mv,nv_final,pv_final), Eq(pv_final,cv)] |- Plus(mv,nv_final,cv)
    # by opening Plus on the left, transferring Apply, repackaging.
    plus_mnp = PlusDef(mv, nv_final, pv_final)
    plus_mnc = PlusDef(mv, nv_final, cv)

    ww = Var(); hh = Var(); ss = Var()
    xsc_e, ysc_e = Var(), Var(); xds_e, yds_e = Var(), Var()
    omega_ww = Omega(ww)
    sc_e = Forall(xsc_e, Implies(In(xsc_e, ww),
        Forall(ysc_e, Iff(Apply(ss, xsc_e, ysc_e), SuccDef(ysc_e, xsc_e)))))
    sf_all_e = And(sc_e, And(FuncDef(ss),
        Forall(xds_e, Implies(Exists(yds_e, Apply(ss, xds_e, yds_e)), In(xds_e, ww)))))
    rec_e = RecDef(hh, mv, ss, ww)
    app_e_pv = Apply(hh, nv_final, pv_final)
    app_e_cv = Apply(hh, nv_final, cv)
    and_rec_app_e = And(rec_e, app_e_pv)
    and_sf_ra_e = And(sf_all_e, and_rec_app_e)

    # Extract Apply from opened Plus
    got_app_pv_e = apply_thm(and_elim_right(rec_e, app_e_pv, []), [],
        and_rec_app_e, app_e_pv, ax(and_rec_app_e))
    got_rec_e = apply_thm(and_elim_left(rec_e, app_e_pv, []), [],
        and_rec_app_e, rec_e, ax(and_rec_app_e))

    # Transfer: Eq(pv_final,cv) -> Apply(hh,nv_final,pv_final) -> Apply(hh,nv_final,cv)
    got_app_cv_e = apply_thm(eavt, [hh, nv_final, pv_final, cv],
        Eq(pv_final, cv), Implies(app_e_pv, app_e_cv), ax(Eq(pv_final, cv)))
    got_app_cv_e = mp(got_app_cv_e, got_app_pv_e, app_e_pv, app_e_cv)

    # Repackage with cv
    and_rec_app_cv = And(rec_e, app_e_cv)
    got_and_cv = mp(apply_thm(and_intro(rec_e, app_e_cv, []), [],
        rec_e, Implies(app_e_cv, and_rec_app_cv), got_rec_e),
        got_app_cv_e, app_e_cv, and_rec_app_cv)
    got_sf_e = apply_thm(and_elim_left(sf_all_e, and_rec_app_e, []), [],
        and_sf_ra_e, sf_all_e, ax(and_sf_ra_e))
    and_sf_ra_cv = And(sf_all_e, and_rec_app_cv)
    got_sfra_cv = mp(apply_thm(and_intro(sf_all_e, and_rec_app_cv, []), [],
        sf_all_e, Implies(and_rec_app_cv, and_sf_ra_cv), got_sf_e),
        got_and_cv, and_rec_app_cv, and_sf_ra_cv)

    # eir to build existentials
    ss2, hh2, ww2 = Var(), Var(), Var()
    xsc_f, ysc_f, xds_f, yds_f = Var(), Var(), Var(), Var()
    sc_f = Forall(xsc_f, Implies(In(xsc_f, ww),
        Forall(ysc_f, Iff(Apply(ss2, xsc_f, ysc_f), SuccDef(ysc_f, xsc_f)))))
    sf_all_f = And(sc_f, And(FuncDef(ss2),
        Forall(xds_f, Implies(Exists(yds_f, Apply(ss2, xds_f, yds_f)), In(xds_f, ww)))))
    inner_sf = And(sf_all_f, And(RecDef(hh, mv, ss2, ww), Apply(hh, nv_final, cv)))
    got_ex_sf_cv = eir(got_sfra_cv, inner_sf, ss2, ss)
    inner_h = Exists(ss2, And(sf_all_f, And(RecDef(hh2, mv, ss2, ww), Apply(hh2, nv_final, cv))))
    got_ex_h_cv = eir(got_ex_sf_cv, inner_h, hh2, hh)
    ex_h_cv = got_ex_h_cv.sequent.right[0]
    and_omega_cv = And(omega_ww, ex_h_cv)
    got_omega_cv = mp(apply_thm(and_intro(omega_ww, ex_h_cv, []), [],
        omega_ww, Implies(ex_h_cv, and_omega_cv), ax(omega_ww)),
        got_ex_h_cv, ex_h_cv, and_omega_cv)

    sc_fw = Forall(xsc_f, Implies(In(xsc_f, ww2),
        Forall(ysc_f, Iff(Apply(ss2, xsc_f, ysc_f), SuccDef(ysc_f, xsc_f)))))
    sf_all_fw = And(sc_fw, And(FuncDef(ss2),
        Forall(xds_f, Implies(Exists(yds_f, Apply(ss2, xds_f, yds_f)), In(xds_f, ww2)))))
    inner_w = And(Omega(ww2), Exists(hh2, Exists(ss2,
        And(sf_all_fw, And(RecDef(hh2, mv, ss2, ww2), Apply(hh2, nv_final, cv))))))
    got_plus_cv = eir(got_omega_cv, inner_w, ww2, ww)
    # got_plus_cv: [and_sf_ra_e, Eq(pv_final,cv)] |- Plus(mv, nv_final, cv)

    # Fold and_sf_ra_e back: cut components, eel ss,hh,ww
    got_ra_e = apply_thm(and_elim_right(sf_all_e, and_rec_app_e, []), [],
        and_sf_ra_e, and_rec_app_e, ax(and_sf_ra_e))
    got_plus_cv = cut(got_plus_cv, and_rec_app_e, got_ra_e)
    got_plus_cv = eel(got_plus_cv, and_sf_ra_e, ss)
    got_plus_cv = eel(got_plus_cv, got_plus_cv.sequent.left[-1], hh)
    ex_hh = got_plus_cv.sequent.left[-1]
    and_omega_exhh = And(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)))
    got_omega_e = apply_thm(and_elim_left(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)), []), [],
        and_omega_exhh, omega_ww, ax(and_omega_exhh))
    got_exhh_e = apply_thm(and_elim_right(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)), []), [],
        and_omega_exhh, Exists(hh, Exists(ss, and_sf_ra_e)), ax(and_omega_exhh))
    got_plus_cv = cut(got_plus_cv, omega_ww, got_omega_e)
    got_plus_cv = cut(got_plus_cv, ex_hh, got_exhh_e)
    got_plus_cv = eel(got_plus_cv, and_omega_exhh, ww)
    # got_plus_cv: [Plus(mv,nv_final,pv_final), Eq(pv_final,cv)] |- Plus(mv,nv_final,cv)

    # Cut: replace Plus and Eq on left with their derivations
    proof = got_plus_cv
    proof = cut(proof, plus_mnp, cur)
    proof = cut(proof, Eq(pv_final, cv), got_eq_pv_cv)

    # === Step G-J: Discharge and close ===
    num_n = NumDef(nv_final, n_val)
    num_m = NumDef(mv, m_val)

    goal = Forall(w, Forall(mv, Forall(nv_final, Forall(cv,
        Implies(omega_w, Implies(num_m, Implies(num_n,
            Implies(num_cv, plus_mnc))))))))

    # Eliminate val-chain Succs

    # === Step G-J: Discharge and close ===
    # Goal: forall w,m,n,c. Omega(w) -> Num(m,m_val) -> Num(n,n_val) -> Num(c,p_val) -> Plus(m,n,c)
    num_n = NumDef(nv_final, n_val)
    num_m = NumDef(mv, m_val)

    goal = Forall(w, Forall(mv, Forall(nv_final, Forall(cv,
        Implies(omega_w, Implies(num_m, Implies(num_n,
            Implies(num_cv, plus_mnc))))))))

    # Eliminate val-chain Succs
    for k in range(n_val - 1, -1, -1):
        prev_v = vals[k] if k > 0 else mv
        next_v = vals[k + 1] if k + 1 < n_val else pv_final
        succ_form = SuccDef(next_v, prev_v)
        if any(same(succ_form, f_) for f_ in proof.sequent.left):
            proof = eel(proof, succ_form, next_v)
            got_se_k = apply_thm(se, [prev_v], concl=Exists(next_v, SuccDef(next_v, prev_v)))
            proof = cut(proof, proof.sequent.left[-1], got_se_k)

    # Close n-chain into Num
    if n_val > 0:
        for j in range(1, n_val + 1):
            prev_var = nums_n[j - 1]
            cur_var = nums_n[j]
            num_prev_j = NumDef(prev_var, j - 1)
            succ_cur_j = SuccDef(cur_var, prev_var)
            and_np_sc = And(num_prev_j, succ_cur_j)
            got_np = apply_thm(and_elim_left(num_prev_j, succ_cur_j, []), [],
                and_np_sc, num_prev_j, ax(and_np_sc))
            if any(same(num_prev_j, f_) for f_ in proof.sequent.left):
                proof = cut(proof, num_prev_j, got_np)
            got_sc_j = apply_thm(and_elim_right(num_prev_j, succ_cur_j, []), [],
                and_np_sc, succ_cur_j, ax(and_np_sc))
            if any(same(succ_cur_j, f_) for f_ in proof.sequent.left):
                proof = cut(proof, succ_cur_j, got_sc_j)
            if any(same(and_np_sc, f_) for f_ in proof.sequent.left):
                proof = eel(proof, and_np_sc, prev_var)

    # Cut In(mv,w) with _num_in_omega derivation
    if any(same(In(mv, w), f_) for f_ in proof.sequent.left):
        got_in_mv = _num_in_omega(mv, m_val)
        proof = cut(proof, In(mv, w), got_in_mv)

    # Discharge hypotheses using goal structure
    g4 = goal.body.body.body  # Forall(cv, ...)
    g_imp = g4.body
    hyps_imps = []
    cur_imp = g_imp
    while isinstance(cur_imp, Implies):
        hyps_imps.append((cur_imp.left, cur_imp))
        cur_imp = cur_imp.right

    for hh in [omega_w]:
        if not any(same(hh, g) for g in proof.sequent.left):
            proof = wl(proof, hh)

    for hh, imp in reversed(hyps_imps):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa_target in [(cv, g4), (nv_final, goal.body.body), (mv, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa_target]), 'forall_right',
            [proof], principal=fa_target, term=var)

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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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
    from vocab import Inductive as InductiveDef, Subset as SubsetDef
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



def unique_num(k):
    """Every natural number exists uniquely as a ZFC set.
    |- ExistsUnique(n, Num(n, k))"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Num as NumDef, Successor as SuccDef, ExistsUnique
    from theorems.axioms import empty_set
    from theorems.sets import successor_exists, unique_successor, eq_successor_transfer
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        unique_empty, eq_reflexive, eq_symmetric, eq_transitive, eq_substitution)
    from theorems.recursion import func_unique_thm
    from core.proof import _expand

    nv = Var(postfix='n')
    goal = ExistsUnique(nv, NumDef(nv, k))

    if k == 0:
        # Existence from empty_set, uniqueness from unique_empty
        es = empty_set()
        ue = unique_empty()

        # From ue at nv: Empty(nv) -> Forall(v2, Implies(Empty(v2), Eq(nv,v2)))
        v2 = Var()
        uniq_body = Forall(v2, Implies(NumDef(v2, 0), Eq(nv, v2)))
        got_uniq = apply_thm(ue, [nv], NumDef(nv, 0), uniq_body, ax(NumDef(nv, 0)))

        # And(Num(nv,0), uniq_body)
        num_nv = NumDef(nv, 0)
        and_body = And(num_nv, uniq_body)
        got_and = mp(apply_thm(and_intro(num_nv, uniq_body, []), [],
            num_nv, Implies(uniq_body, and_body), ax(num_nv)),
            got_uniq, uniq_body, and_body)

        # eir: Exists(cv, And(Num(cv,0), Forall(...)))
        cv = Var()
        eir_body = And(NumDef(cv, 0), Forall(v2, Implies(NumDef(v2, 0), Eq(cv, v2))))
        got_ex = eir(got_and, eir_body, cv, nv)

        # eel Num(nv,0), cut with empty_set
        got_ex = eel(got_ex, num_nv, nv)
        got_ex = cut(got_ex, got_ex.sequent.left[-1], es)

        # Relabel to ExistsUnique
        proof = Proof(Sequent(got_ex.sequent.left, [goal]),
                      'weakening_right', [got_ex], principal=goal)
        proof.name = f'unique_num_{k}'
        return proof

    # k > 0: build from unique_num(k-1)
    prev_proof = unique_num(k - 1)

    prev = Var(postfix=f'p{k-1}')
    q_var = Var(postfix='q')
    num_prev = NumDef(prev, k - 1)
    uniq_prev = Forall(q_var, Implies(NumDef(q_var, k - 1), Eq(prev, q_var)))
    and_prev = And(num_prev, uniq_prev)

    se = successor_exists()
    cur = Var(postfix=f'c{k}')
    succ_cur = SuccDef(cur, prev)
    got_se = apply_thm(se, [prev], concl=Exists(cur, succ_cur))

    # Extract components from and_prev
    got_num_p = apply_thm(and_elim_left(num_prev, uniq_prev, []), [],
        and_prev, num_prev, ax(and_prev))
    got_uniq_p = apply_thm(and_elim_right(num_prev, uniq_prev, []), [],
        and_prev, uniq_prev, ax(and_prev))

    # Build Num(cur, k) from num_prev + Succ(cur, prev)
    and_ns = And(num_prev, succ_cur)
    got_and_ns = mp(apply_thm(and_intro(num_prev, succ_cur, []), [],
        num_prev, Implies(succ_cur, and_ns), got_num_p),
        ax(succ_cur), succ_cur, and_ns)
    mv = Var()
    got_num_cur = eir(got_and_ns, And(NumDef(mv, k - 1), SuccDef(cur, mv)), mv, prev)
    # [and_prev, Succ(cur, prev)] |- Num(cur, k)

    # Build uniqueness: Forall(v2, Implies(Num(v2, k), Eq(cur, v2)))
    v2 = Var(postfix='v2')
    num_v2 = NumDef(v2, k)
    m2 = Var(postfix='m2')
    num_m2 = NumDef(m2, k - 1)
    succ_v2_m2 = SuccDef(v2, m2)
    and_m2 = And(num_m2, succ_v2_m2)

    # From uniq_prev (extracted from and_prev): Num(m2, k-1) -> Eq(prev, m2)
    got_eq_prev_m2 = apply_thm(got_uniq_p, [m2], num_m2, Eq(prev, m2), ax(num_m2))

    er = eq_reflexive()
    es_thm = eq_symmetric()
    est = eq_successor_transfer()
    got_eq_cc = apply_thm(er, [cur], concl=Eq(cur, cur))
    got_eq_m2_prev = apply_thm(es_thm, [prev, m2], Eq(prev, m2), Eq(m2, prev), got_eq_prev_m2)

    # est: Eq(a,c) -> Eq(b,d) -> Succ(c,d) -> Succ(a,b)
    got_succ_cur_m2 = apply_thm(est, [cur, m2, cur, prev], Eq(cur, cur),
        Implies(Eq(m2, prev), Implies(succ_cur, SuccDef(cur, m2))), got_eq_cc)
    got_succ_cur_m2 = mp(got_succ_cur_m2, got_eq_m2_prev, Eq(m2, prev),
        Implies(succ_cur, SuccDef(cur, m2)))
    got_succ_cur_m2 = mp(got_succ_cur_m2, ax(succ_cur), succ_cur, SuccDef(cur, m2))

    us = unique_successor()
    got_eq_cur_v2 = apply_thm(us, [m2, cur, v2], SuccDef(cur, m2),
        Implies(succ_v2_m2, Eq(cur, v2)), got_succ_cur_m2)
    got_eq_cur_v2 = mp(got_eq_cur_v2, ax(succ_v2_m2), succ_v2_m2, Eq(cur, v2))

    # Fold num_m2 and succ_v2_m2 into And, eel to Num(v2,k)
    got_nm2 = apply_thm(and_elim_left(num_m2, succ_v2_m2, []), [],
        and_m2, num_m2, ax(and_m2))
    got_sv2 = apply_thm(and_elim_right(num_m2, succ_v2_m2, []), [],
        and_m2, succ_v2_m2, ax(and_m2))
    got_eq_cur_v2 = cut(got_eq_cur_v2, num_m2, got_nm2)
    got_eq_cur_v2 = cut(got_eq_cur_v2, succ_v2_m2, got_sv2)
    got_eq_cur_v2 = eel(got_eq_cur_v2, and_m2, m2)
    got_eq_cur_v2 = cut(got_eq_cur_v2, got_eq_cur_v2.sequent.left[-1], ax(num_v2))
    # Left now has: [and_prev, Succ(cur,prev), num_v2, axioms]

    # Close: implies_right Num(v2,k), forall v2
    imp_v2 = Implies(num_v2, Eq(cur, v2))
    rem_v2 = [f_ for f_ in got_eq_cur_v2.sequent.left if not same(f_, num_v2)]
    got_uniq_cur = Proof(Sequent(rem_v2, [imp_v2]), 'implies_right',
        [got_eq_cur_v2], principal=imp_v2)
    uniq_cur = Forall(v2, imp_v2)
    got_uniq_cur = Proof(Sequent(rem_v2, [uniq_cur]), 'forall_right',
        [got_uniq_cur], principal=uniq_cur, term=v2)

    # And(Num(cur,k), uniq_cur)
    num_cur_k = NumDef(cur, k)
    and_cur = And(num_cur_k, uniq_cur)
    all_and = list(got_num_cur.sequent.left)
    for f_ in got_uniq_cur.sequent.left:
        if not any(same(f_, g) for g in all_and):
            all_and.append(f_)
    got_and_cur = mp(apply_thm(and_intro(num_cur_k, uniq_cur, []), [],
        num_cur_k, Implies(uniq_cur, and_cur), weaken_to(got_num_cur, all_and)),
        weaken_to(got_uniq_cur, all_and), uniq_cur, and_cur)

    # eir -> Exists, eel Succ, cut successor_exists, eel and_prev, cut prev_proof
    cv = Var()
    eir_body = And(NumDef(cv, k), Forall(v2, Implies(NumDef(v2, k), Eq(cv, v2))))
    got_ex = eir(got_and_cur, eir_body, cv, cur)
    got_ex = eel(got_ex, succ_cur, cur)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], got_se)
    got_ex = eel(got_ex, and_prev, prev)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], prev_proof)

    proof = Proof(Sequent(got_ex.sequent.left, [goal]),
                  'weakening_right', [got_ex], principal=goal)
    proof.name = f'unique_num_{k}'
    return proof


def rec_val_in_omega():
    """Values of a recursive function on ω are in ω.
    |- forall w, a, sf, h, x, y.
         Omega(w) -> In(a, w) ->
         succ_char(sf, w) -> Recursive(h, a, sf, w) ->
         In(x, w) -> Apply(h, x, y) -> In(y, w)
    Induction on x with P(x) = forall y. Apply(h, x, y) -> In(y, w).
    Base: Apply(h, 0, y) -> y=a (func_unique + base) -> In(a, w).
    Step: Apply(h, S(x), y) -> y=S(h(x)) -> In(h(x), w) by IH -> In(S(h(x)), w) by omega_succ_closed."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.sets import successor_exists
    from theorems.logic import eq_symmetric
    from core.proof import _expand

    w = Var(postfix='w')
    a = Var(postfix='a')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xv = Var(postfix='x')
    yv = Var(postfix='y')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, a, sfv, w)
    in_x_w = In(xv, w)
    app_h_xy = Apply(hv, xv, yv)
    in_y_w = In(yv, w)

    goal = Forall(w, Forall(a, Forall(sfv, Forall(hv, Forall(xv, Forall(yv,
        Implies(omega_w, Implies(in_a_w, Implies(succ_char, Implies(rec_h,
            Implies(in_x_w, Implies(app_h_xy, in_y_w))))))))))))
    assert str(goal)

    # P(x) = forall y. Apply(h, x, y) -> In(y, w)
    pv = Var(postfix='pv')
    xind = Var(postfix='xi')
    yind = Var(postfix='yi')
    def P(x):
        return Forall(yind, Implies(Apply(hv, x, yind), In(yind, w)))

    # === Extract Recursive base/step ===
    ev = Var()
    base_h = Forall(ev, Implies(Empty(ev), Apply(hv, ev, a)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    func_h = FuncDef(hv)
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    and_base_step = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_base_step)

    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs, []), [],
        rec_h, and_dom_bs, ax(rec_h))
    got_bs = apply_thm(and_elim_right(dom_sub_h, and_base_step, []), [],
        and_dom_bs, and_base_step, got_dom_bs)
    got_base_h = apply_thm(and_elim_left(base_h, step_h, []), [],
        and_base_step, base_h, got_bs)
    got_func_h = apply_thm(and_elim_left(func_h, and_dom_bs, []), [],
        rec_h, func_h, ax(rec_h))

    # === Separation for induction set ===
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, w), P(xind))))
    sep = separation(lambda x: And(In(x, w), P(x)), [w, hv])
    got_sep = apply_thm(sep, [w, hv, pv], concl=char_p)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base case: P(0) ===
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(eb, Implies(empty_eb, In(eb, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [eb], empty_eb, In(eb, w), ax(empty_eb))

    # Apply(h, eb, a) from base_h:
    got_h_0 = apply_thm(got_base_h, [eb], empty_eb, Apply(hv, eb, a), ax(empty_eb))

    # P(eb) = forall yi. Apply(h, eb, yi) -> In(yi, w)
    # Given Apply(h, eb, a) and func_unique: Apply(h, eb, yi) -> Eq(yi, a)
    # Eq(yi, a) + In(a, w) -> In(yi, w) via eq_substitution
    fut = func_unique_thm()
    esub = eq_substitution()

    got_eq_yi_a = apply_thm(fut, [hv, eb, yind, a], func_h,
        Implies(Apply(hv, eb, yind), Implies(Apply(hv, eb, a), Eq(yind, a))),
        got_func_h)
    got_eq_yi_a = mp(mp(got_eq_yi_a, ax(Apply(hv, eb, yind)),
        Apply(hv, eb, yind), Implies(Apply(hv, eb, a), Eq(yind, a))),
        got_h_0, Apply(hv, eb, a), Eq(yind, a))
    # [rec_h, Empty(eb), omega_w, Ext, Inf, Apply(h,eb,yi)] |- Eq(yi, a)

    # Eq(yi, a) -> Iff(In(yi, z), In(a, z)) for z=w -> In(a, w) -> In(yi, w)
    # Actually: Eq(yi, a) = forall z. Iff(In(z,yi), In(z,a)). That's membership IN yi/a.
    # We need In(yi, w) from In(a, w) and Eq(yi, a).
    # Eq(yi, a) means forall z. In(z, yi) iff In(z, a). This is extensional equality.
    # From Eq(yi, a): In(yi, w) iff In(a, w) — but this requires In(yi, SET) not In(SET, yi).
    # Need eq_substitution which gives: Eq(a,b) -> Iff(In(a,z), In(b,z))
    # So Eq(yi, a) -> Iff(In(yi, w), In(a, w)). Then In(a, w) -> In(yi, w).
    es = eq_symmetric()
    er = eq_reflexive()

    iff_in_w = Iff(In(yind, w), In(a, w))
    got_iff = apply_thm(esub, [yind, a, w], Eq(yind, a), iff_in_w, got_eq_yi_a)
    got_in_yi_w = mp(mp(iff_mp_rev(In(yind, w), In(a, w), []),
        got_iff, iff_in_w, Implies(In(a, w), In(yind, w))),
        ax(in_a_w), in_a_w, In(yind, w))
    # [..., Apply(h,eb,yi)] |- In(yi, w)

    # Discharge Apply(h,eb,yi), close forall yi:
    imp_base = Implies(Apply(hv, eb, yind), In(yind, w))
    rem_base = [f_ for f_ in got_in_yi_w.sequent.left if not same(f_, Apply(hv, eb, yind))]
    got_p_base = Proof(Sequent(rem_base, [imp_base]), 'implies_right',
        [got_in_yi_w], principal=imp_base)
    P_eb = P(eb)
    got_p_base = Proof(Sequent(rem_base, [P_eb]), 'forall_right',
        [got_p_base], principal=P_eb, term=yind)

    # And(In(eb, w), P(eb)) -> In(eb, pv):
    and_eb = And(In(eb, w), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, w), P_eb, []), [],
        In(eb, w), Implies(P_eb, and_eb), got_eb_w),
        got_p_base, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # === Step case: In(x, pv) -> In(S(x), pv) ===
    xs = Var(postfix='xs')
    sxs = Var(postfix='sxs')
    in_xs_pv = In(xs, pv)
    succ_sxs_xs = SuccDef(sxs, xs)

    # From In(xs, pv) -> And(In(xs, w), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, w), P(xs)))
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), P(xs), got_and_xs)
    # P(xs) = forall yi. Apply(h, xs, yi) -> In(yi, w)

    # Need: P(sxs) = forall yi. Apply(h, sxs, yi) -> In(yi, w)
    # Given Apply(h, sxs, yi):
    # By rec_step_succ structure: there exists val with Apply(h, xs, val) and
    #   Apply(sf, val, yi) (i.e., yi = S(val)).
    # By P(xs): Apply(h, xs, val) -> In(val, w).
    # By succ_char: Apply(sf, val, yi) -> Succ(yi, val).
    # By omega_succ_closed: In(val, w) + Succ(yi, val) -> In(yi, w).

    # rec_step_succ: Apply(h,xs,val) + Succ(sxs,xs) + Succ(fval,val) -> Apply(h,sxs,fval)
    # But we want the reverse direction: from Apply(h,sxs,yi), deduce yi = S(val) for some val.
    # This needs func_unique on h: Apply(h,sxs,yi) + Apply(h,sxs,fval) -> Eq(yi,fval).

    # So: pick any val with Apply(h,xs,val). Get fval=S(val) via succ_char.
    # rec_step_succ gives Apply(h,sxs,fval).
    # func_unique: Apply(h,sxs,yi) + Apply(h,sxs,fval) -> Eq(yi,fval).
    # In(val, w) from P(xs). Succ(fval,val). omega_succ_closed: In(fval,w).
    # Eq(yi,fval) + In(fval,w) -> In(yi,w) via eq_substitution.

    # But we need a val with Apply(h,xs,val). The function h is total on w
    # (from rec_exists or Recursive properties). Actually, we don't have totality directly.
    # The Recursive definition guarantees: dom_sub + base + step => h covers all of w.
    # Specifically, recursion_theorem gives existence. But we just have Recursive(h,...).
    # Recursive includes dom_sub which gives: Apply(h,x,y) -> In(x,w).
    # Does Recursive guarantee totality? Not directly from the definition.
    # But we can use the step property: base gives Apply(h,0,a). Step gives Apply(h,S(x),f(val)).
    # By induction, h is defined at every x in w.

    # Actually, the simplest approach: we already know Apply(h,xs,val) for SOME val
    # because we're inside the step of an induction where we assumed P(xs).
    # P(xs) says: forall yi. Apply(h,xs,yi) -> In(yi,w).
    # This doesn't guarantee existence of such yi. We need totality separately.

    # Totality of h on w follows from rec_exists (which constructs h via induction).
    # But in our proof, h is given as Recursive(h,a,sf,w). We need h total on w.
    # From Recursive: we can prove by induction that forall x in w. exists y. Apply(h,x,y).
    # This is another induction inside this proof. Getting complex.

    # SIMPLER: strengthen P to P(x) = exists y. And(Apply(h,x,y), In(y,w)).
    # Base: Apply(h,0,a) and In(a,w). Step: Apply(h,S(x),S(y)) and In(S(y),w).
    # This gives both totality and In(value, w) in one induction.

    # Let me redefine P:
    yex = Var(postfix='ye')
    def P(x):
        return Exists(yex, And(Apply(hv, x, yex), In(yex, w)))

    # Redo char_p with new P:
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, w), P(xind))))
    sep = separation(P, [w, hv])
    got_sep = sep
    for term in [hv, w]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
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

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base case (redo) ===
    # P(eb) = Exists(ye, And(Apply(h,eb,ye), In(ye,w)))
    # Have: Apply(h,eb,a) and In(a,w).
    and_app_in = And(Apply(hv, eb, a), In(a, w))
    got_and_app = mp(apply_thm(and_intro(Apply(hv, eb, a), In(a, w), []), [],
        Apply(hv, eb, a), Implies(In(a, w), and_app_in), got_h_0),
        ax(in_a_w), in_a_w, and_app_in)
    P_eb = P(eb)
    got_p_eb = eir(got_and_app, And(Apply(hv, eb, yex), In(yex, w)), yex, a)
    # got_p_eb: [...] |- P(eb)

    and_eb = And(In(eb, w), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, w), P_eb, []), [],
        In(eb, w), Implies(P_eb, and_eb), got_eb_w),
        got_p_eb, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # === Step case (redo) ===
    # From In(xs, pv) -> And(In(xs, w), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, w), P(xs)))
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), P(xs), got_and_xs)
    # P(xs) = Exists(ye, And(Apply(h,xs,ye), In(ye,w)))

    # Open P(xs): get val with Apply(h,xs,val) and In(val,w)
    val = Var(postfix='val')
    and_app_val = And(Apply(hv, xs, val), In(val, w))
    got_app_val = apply_thm(and_elim_left(Apply(hv, xs, val), In(val, w), []), [],
        and_app_val, Apply(hv, xs, val), ax(and_app_val))
    got_in_val_w = apply_thm(and_elim_right(Apply(hv, xs, val), In(val, w), []), [],
        and_app_val, In(val, w), ax(and_app_val))

    # Get S(val) via successor_exists:
    se = successor_exists()
    sval = Var(postfix='sv')
    succ_sval_val = SuccDef(sval, val)
    got_se_val = apply_thm(se, [val], concl=Exists(sval, succ_sval_val))

    # rec_step_succ: Apply(h,xs,val) + Succ(sxs,xs) + Succ(sval,val) -> Apply(h,sxs,sval)
    rss = rec_step_succ()
    got_app_step = apply_thm(rss, [w, a, sfv, hv, xs, val, sxs, sval],
        omega_w, Implies(In(xs, w), Implies(In(val, w), Implies(succ_char,
            Implies(rec_h, Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
                Implies(succ_sval_val, Apply(hv, sxs, sval)))))))),
        ax(omega_w))
    got_app_step = mp(got_app_step, got_in_xs_w, In(xs, w),
        Implies(In(val, w), Implies(succ_char, Implies(rec_h,
            Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
                Implies(succ_sval_val, Apply(hv, sxs, sval))))))))
    got_app_step = mp(got_app_step, got_in_val_w, In(val, w),
        Implies(succ_char, Implies(rec_h, Implies(Apply(hv, xs, val),
            Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval)))))))
    got_app_step = mp(got_app_step, ax(succ_char), succ_char,
        Implies(rec_h, Implies(Apply(hv, xs, val),
            Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval))))))
    got_app_step = mp(got_app_step, ax(rec_h), rec_h,
        Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
            Implies(succ_sval_val, Apply(hv, sxs, sval)))))
    got_app_step = mp(got_app_step, got_app_val, Apply(hv, xs, val),
        Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval))))
    got_app_step = mp(got_app_step, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sval_val, Apply(hv, sxs, sval)))
    got_app_step = mp(got_app_step, ax(succ_sval_val), succ_sval_val,
        Apply(hv, sxs, sval))
    # got_app_step: [..., and_app_val, succ_sxs_xs, succ_sval_val] |- Apply(h, sxs, sval)

    # In(sval, w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_in_sval = apply_thm(osc, [w], omega_w,
        Forall(val, Implies(In(val, w), Forall(sval, Implies(succ_sval_val, In(sval, w))))),
        ax(omega_w))
    got_in_sval = apply_thm(got_in_sval, [val], In(val, w),
        Forall(sval, Implies(succ_sval_val, In(sval, w))), got_in_val_w)
    got_in_sval = apply_thm(got_in_sval, [sval], succ_sval_val, In(sval, w),
        ax(succ_sval_val))

    # P(sxs) = Exists(ye, And(Apply(h,sxs,ye), In(ye,w)))
    and_step = And(Apply(hv, sxs, sval), In(sval, w))
    got_and_step = mp(apply_thm(and_intro(Apply(hv, sxs, sval), In(sval, w), []), [],
        Apply(hv, sxs, sval), Implies(In(sval, w), and_step), got_app_step),
        got_in_sval, In(sval, w), and_step)
    P_sxs = P(sxs)
    got_p_sxs = eir(got_and_step, And(Apply(hv, sxs, yex), In(yex, w)), yex, sval)

    # Close existentials: eel sval, val, then eel P(xs)
    cur_step = eel(got_p_sxs, succ_sval_val, sval)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_val)
    cur_step = eel(cur_step, and_app_val, val)
    # Need to connect with P(xs) = Exists(ye, And(Apply(h,xs,ye), In(ye,w)))
    # The and_app_val was for val, and eel created Exists(val, and_app_val) which should match P(xs)
    # P(xs) = Exists(yex, And(Apply(hv,xs,yex), In(yex,w)))
    # eel used and_app_val = And(Apply(hv,xs,val), In(val,w)) with var=val
    # Exists(val, and_app_val) should alpha-match P(xs) = Exists(yex, And(Apply(hv,xs,yex), In(yex,w)))
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_P_xs)

    # In(sxs, w) from omega_succ_closed:
    got_in_sxs = apply_thm(osc, [w], omega_w,
        Forall(xs, Implies(In(xs, w), Forall(sxs, Implies(succ_sxs_xs, In(sxs, w))))),
        ax(omega_w))
    got_in_sxs = apply_thm(got_in_sxs, [xs], In(xs, w),
        Forall(sxs, Implies(succ_sxs_xs, In(sxs, w))), got_in_xs_w)
    got_in_sxs = apply_thm(got_in_sxs, [sxs], succ_sxs_xs, In(sxs, w),
        ax(succ_sxs_xs))

    # And(In(sxs, w), P(sxs)) -> In(sxs, pv)
    and_sxs = And(In(sxs, w), P_sxs)
    got_and_sxs = mp(apply_thm(and_intro(In(sxs, w), P_sxs, []), [],
        In(sxs, w), Implies(P_sxs, and_sxs), got_in_sxs),
        cur_step, P_sxs, and_sxs)
    got_in_sxs_pv = mp(char_p_bwd(sxs), got_and_sxs, and_sxs, In(sxs, pv))

    # Discharge succ_sxs_xs and In(xs, pv):
    imp_succ = Implies(succ_sxs_xs, In(sxs, pv))
    rem_succ = [f_ for f_ in got_in_sxs_pv.sequent.left if not same(f_, succ_sxs_xs)]
    got_imp_succ = Proof(Sequent(rem_succ, [imp_succ]), 'implies_right',
        [got_in_sxs_pv], principal=imp_succ)
    fa_sxs = Forall(sxs, imp_succ)
    got_fa_sxs = Proof(Sequent(rem_succ, [fa_sxs]), 'forall_right',
        [got_imp_succ], principal=fa_sxs, term=sxs)
    imp_xs = Implies(in_xs_pv, fa_sxs)
    rem_xs = [f_ for f_ in got_fa_sxs.sequent.left if not same(f_, in_xs_pv)]
    got_step = Proof(Sequent(rem_xs, [imp_xs]), 'implies_right',
        [got_fa_sxs], principal=imp_xs)
    fa_xs = Forall(xs, imp_xs)
    got_step = Proof(Sequent(rem_xs, [fa_xs]), 'forall_right',
        [got_step], principal=fa_xs, term=xs)

    # === Induction closure: Inductive(pv), Subset(pv,w), omega_smallest_inductive ===
    # Build base_ind from got_in_eb_pv
    imp_base_ind = Implies(empty_eb, In(eb, pv))
    rem_base_ind = [f_ for f_ in got_in_eb_pv.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_base_ind, [imp_base_ind]), 'implies_right',
        [got_in_eb_pv], principal=imp_base_ind)
    base_ind = Forall(eb, imp_base_ind)
    proof_base = Proof(Sequent(rem_base_ind, [base_ind]), 'forall_right',
        [proof_base], principal=base_ind, term=eb)

    step_ind = fa_xs
    proof_step = got_step

    from vocab import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

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
        And(In(xsub, w), P(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P(xsub), []), [],
        And(In(xsub, w), P(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
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

    # === Extract P(xv) from Eq(pv,w) + In(xv,w) ===
    iff_xv_pv = Iff(In(xv, pv), in_x_w)
    got_iff_xv = Proof(Sequent(got_eq.sequent.left, [iff_xv_pv]), 'cut',
        [wr(got_eq, iff_xv_pv),
         weaken_to(fl(eq_pw, iff_xv_pv, xv), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_xv_pv = mp(mp(iff_mp_rev(In(xv, pv), in_x_w, []),
        got_iff_xv, iff_xv_pv, Implies(in_x_w, In(xv, pv))),
        ax(in_x_w), in_x_w, In(xv, pv))

    got_fwd_xv = char_p_fwd(xv)
    all_ext = list(got_in_xv_pv.sequent.left)
    for f_ in got_fwd_xv.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_xv = mp(weaken_to(got_fwd_xv, all_ext),
        weaken_to(got_in_xv_pv, all_ext), In(xv, pv), And(in_x_w, P(xv)))
    got_p_xv = apply_thm(and_elim_right(in_x_w, P(xv), []), [],
        And(in_x_w, P(xv)), P(xv), got_and_xv)

    # === From P(xv) + Apply(hv,xv,yv), derive In(yv,w) ===
    yew = Var(postfix='yw')
    and_app_in_yw = And(Apply(hv, xv, yew), In(yew, w))
    got_app_yw = apply_thm(and_elim_left(Apply(hv, xv, yew), In(yew, w), []), [],
        and_app_in_yw, Apply(hv, xv, yew), ax(and_app_in_yw))
    got_in_yw = apply_thm(and_elim_right(Apply(hv, xv, yew), In(yew, w), []), [],
        and_app_in_yw, In(yew, w), ax(and_app_in_yw))

    # func_unique: Apply(hv,xv,yv) + Apply(hv,xv,yew) -> Eq(yv,yew)
    got_eq_yv = apply_thm(fut, [hv, xv, yv, yew], func_h,
        Implies(app_h_xy, Implies(Apply(hv, xv, yew), Eq(yv, yew))),
        got_func_h)
    got_eq_yv = mp(mp(got_eq_yv, ax(app_h_xy),
        app_h_xy, Implies(Apply(hv, xv, yew), Eq(yv, yew))),
        got_app_yw, Apply(hv, xv, yew), Eq(yv, yew))

    # eq_substitution: Eq(yv,yew) -> Iff(In(yv,w), In(yew,w))
    iff_in_yw = Iff(in_y_w, In(yew, w))
    got_iff_yw = apply_thm(esub, [yv, yew, w], Eq(yv, yew), iff_in_yw, got_eq_yv)
    got_in_yv_w = mp(mp(iff_mp_rev(in_y_w, In(yew, w), []),
        got_iff_yw, iff_in_yw, Implies(In(yew, w), in_y_w)),
        got_in_yw, In(yew, w), in_y_w)

    # eel yew to close the existential from P(xv)
    proof = eel(got_in_yv_w, and_app_in_yw, yew)
    proof = cut(proof, proof.sequent.left[-1], got_p_xv)

    # eel pv from char_p, cut with got_sep
    if any(same(char_p, g) for g in proof.sequent.left):
        proof = eel(proof, char_p, pv)
        proof = cut(proof, proof.sequent.left[-1], got_sep)

    # === Discharge hypotheses and close foralls ===
    g_imp = goal.body.body.body.body.body.body  # Implies(omega_w, ...)
    g_imp_a = g_imp.right
    g_imp_sc = g_imp_a.right
    g_imp_rec = g_imp_sc.right
    g_imp_x = g_imp_rec.right
    g_imp_y = g_imp_x.right  # Implies(app_h_xy, in_y_w)

    for hyp, imp in [(app_h_xy, g_imp_y), (in_x_w, g_imp_x), (rec_h, g_imp_rec),
                     (succ_char, g_imp_sc), (in_a_w, g_imp_a), (omega_w, g_imp)]:
        if any(same(hyp, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hyp)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa in [(yv, goal.body.body.body.body.body),
                    (xv, goal.body.body.body.body),
                    (hv, goal.body.body.body),
                    (sfv, goal.body.body),
                    (a, goal.body),
                    (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=var)

    proof.name = 'rec_val_in_omega'
    return proof


def plus_assoc():
    """Associativity of addition: (m + n) + k = m + (n + k).
    |- forall w, m, n, k, p, q, r.
         Omega(w) -> In(m, w) -> In(n, w) -> In(k, w) ->
         Plus(m, n, p) -> Plus(p, k, q) ->
         Plus(n, k, r) -> Plus(m, r, q)
    """
    from vocab import Plus as PlusDef

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
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
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

    # Plus(p,k,q): separate wv_p, sfv_p for independent folding
    wv_p = Var(postfix='wp')
    sfv_p = Var(postfix='sfp')
    hp = Var(postfix='hp')
    omega_wp = Omega(wv_p)
    succ_char_p = Forall(xsc, Implies(In(xsc, wv_p),
        Forall(ysc, Iff(Apply(sfv_p, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sfp = FuncDef(sfv_p)
    dom_sub_sfp = Forall(xds, Implies(Exists(yds, Apply(sfv_p, xds, yds)), In(xds, wv_p)))
    and_func_dom_p = And(func_sfp, dom_sub_sfp)
    sf_all_p = And(succ_char_p, and_func_dom_p)
    rec_hp = RecDef(hp, p, sfv_p, wv_p)
    app_hp_kq = Apply(hp, k, q)
    and_rec_app_p = And(rec_hp, app_hp_kq)
    and_sf_ra_p = And(sf_all_p, and_rec_app_p)

    # Plus(n,k,r): separate wv_n, sfv_n
    wv_n = Var(postfix='wn')
    sfv_n = Var(postfix='sfn')
    hn = Var(postfix='hn')
    omega_wn = Omega(wv_n)
    succ_char_n = Forall(xsc, Implies(In(xsc, wv_n),
        Forall(ysc, Iff(Apply(sfv_n, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sfn = FuncDef(sfv_n)
    dom_sub_sfn = Forall(xds, Implies(Exists(yds, Apply(sfv_n, xds, yds)), In(xds, wv_n)))
    and_func_dom_n = And(func_sfn, dom_sub_sfn)
    sf_all_n = And(succ_char_n, and_func_dom_n)
    rec_hn = RecDef(hn, n, sfv_n, wv_n)
    app_hn_kr = Apply(hn, k, r)
    and_rec_app_n = And(rec_hn, app_hn_kr)
    and_sf_ra_n = And(sf_all_n, and_rec_app_n)

    # The result we want: Plus(m, r, q) = Apply(hm, r, q) wrapped in exists
    app_hm_rq = Apply(hm, r, q)
    plus_mrq = PlusDef(m, r, q)

    # Fold-back structure for Plus(m,n,p):
    ex_sfv_m = Exists(sfv, and_sf_ra_m)
    ex_hm_m = Exists(hm, ex_sfv_m)
    and_omega_m = And(omega_wv, ex_hm_m)
    # Plus(m,n,p) = Exists(wv, and_omega_m)

    got_sc_from = apply_thm(and_elim_left(succ_char, and_func_dom, []), [],
        sf_all, succ_char, ax(sf_all))
    got_fd_from = apply_thm(and_elim_right(succ_char, and_func_dom, []), [],
        sf_all, and_func_dom, ax(sf_all))
    got_func_sf_from = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        and_func_dom, func_sf, got_fd_from)
    got_dom_sf_from = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        and_func_dom, dom_sub_sf, got_fd_from)
    got_rec_from = apply_thm(and_elim_left(rec_hm, app_hm_np, []), [],
        and_rec_app_m, rec_hm, ax(and_rec_app_m))
    got_app_from = apply_thm(and_elim_right(rec_hm, app_hm_np, []), [],
        and_rec_app_m, app_hm_np, ax(and_rec_app_m))
    got_sf_from = apply_thm(and_elim_left(sf_all, and_rec_app_m, []), [],
        and_sf_ra_m, sf_all, ax(and_sf_ra_m))
    got_ra_from = apply_thm(and_elim_right(sf_all, and_rec_app_m, []), [],
        and_sf_ra_m, and_rec_app_m, ax(and_sf_ra_m))
    got_omega_from = apply_thm(and_elim_left(omega_wv, ex_hm_m, []), [],
        and_omega_m, omega_wv, ax(and_omega_m))
    got_exhm_from = apply_thm(and_elim_right(omega_wv, ex_hm_m, []), [],
        and_omega_m, ex_hm_m, ax(and_omega_m))

    # Fold-back structure for Plus(p,k,q):
    ex_sfp_p = Exists(sfv_p, and_sf_ra_p)
    ex_hp_p = Exists(hp, ex_sfp_p)
    and_omega_p = And(omega_wp, ex_hp_p)

    got_rec_hp_from = apply_thm(and_elim_left(rec_hp, app_hp_kq, []), [],
        and_rec_app_p, rec_hp, ax(and_rec_app_p))
    got_app_hp_from = apply_thm(and_elim_right(rec_hp, app_hp_kq, []), [],
        and_rec_app_p, app_hp_kq, ax(and_rec_app_p))
    got_sf_p_from = apply_thm(and_elim_left(sf_all_p, and_rec_app_p, []), [],
        and_sf_ra_p, sf_all_p, ax(and_sf_ra_p))
    got_ra_p_from = apply_thm(and_elim_right(sf_all_p, and_rec_app_p, []), [],
        and_sf_ra_p, and_rec_app_p, ax(and_sf_ra_p))
    got_omega_wp_from = apply_thm(and_elim_left(omega_wp, ex_hp_p, []), [],
        and_omega_p, omega_wp, ax(and_omega_p))
    got_exhp_from = apply_thm(and_elim_right(omega_wp, ex_hp_p, []), [],
        and_omega_p, ex_hp_p, ax(and_omega_p))

    # Fold-back structure for Plus(n,k,r):
    ex_sfn_n = Exists(sfv_n, and_sf_ra_n)
    ex_hn_n = Exists(hn, ex_sfn_n)
    and_omega_n = And(omega_wn, ex_hn_n)

    got_rec_hn_from = apply_thm(and_elim_left(rec_hn, app_hn_kr, []), [],
        and_rec_app_n, rec_hn, ax(and_rec_app_n))
    got_app_hn_from = apply_thm(and_elim_right(rec_hn, app_hn_kr, []), [],
        and_rec_app_n, app_hn_kr, ax(and_rec_app_n))
    got_sf_n_from = apply_thm(and_elim_left(sf_all_n, and_rec_app_n, []), [],
        and_sf_ra_n, sf_all_n, ax(and_sf_ra_n))
    got_ra_n_from = apply_thm(and_elim_right(sf_all_n, and_rec_app_n, []), [],
        and_sf_ra_n, and_rec_app_n, ax(and_sf_ra_n))
    got_omega_wn_from = apply_thm(and_elim_left(omega_wn, ex_hn_n, []), [],
        and_omega_n, omega_wn, ax(and_omega_n))
    got_exhn_from = apply_thm(and_elim_right(omega_wn, ex_hn_n, []), [],
        and_omega_n, ex_hn_n, ax(and_omega_n))

    # omega_unique transfers
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_w_wv = mp(apply_thm(ou, [w, wv], omega_w,
        Implies(omega_wv, eq_w_wv), ax(omega_w)),
        ax(omega_wv), omega_wv, eq_w_wv)
    eq_wv_wp = Eq(wv, wv_p)
    got_eq_wv_wp = mp(apply_thm(ou, [wv, wv_p], omega_wv,
        Implies(omega_wp, eq_wv_wp), ax(omega_wv)),
        ax(omega_wp), omega_wp, eq_wv_wp)
    eq_wv_wn = Eq(wv, wv_n)
    got_eq_wv_wn = mp(apply_thm(ou, [wv, wv_n], omega_wv,
        Implies(omega_wn, eq_wv_wn), ax(omega_wv)),
        ax(omega_wn), omega_wn, eq_wv_wn)

    # Transfer In(x, w) → In(x, wv) via Eq(w, wv)
    def transfer_in(x_var, w_from, w_to, eq_proof, got_in_from):
        """From got_in_from: [...] |- In(x, w_from), derive [...] |- In(x, w_to)."""
        iff_f = Iff(In(x_var, w_from), In(x_var, w_to))
        eq_f = Eq(w_from, w_to)
        got_iff = Proof(Sequent(eq_proof.sequent.left, [iff_f]), 'cut',
            [wr(eq_proof, iff_f),
             weaken_to(fl(eq_f, iff_f, x_var), eq_proof.sequent.left)],
            principal=eq_f)
        return mp(mp(iff_mp(In(x_var, w_from), In(x_var, w_to), []),
            got_iff, iff_f, Implies(In(x_var, w_from), In(x_var, w_to))),
            got_in_from, In(x_var, w_from), In(x_var, w_to))

    from theorems.logic import iff_mp
    got_in_m_wv = transfer_in(m, w, wv, got_eq_w_wv, ax(In(m, w)))
    got_in_n_wv = transfer_in(n, w, wv, got_eq_w_wv, ax(In(n, w)))
    got_in_k_wv = transfer_in(k, w, wv, got_eq_w_wv, ax(In(k, w)))

    # ====================================================================
    # Section 2: Set up the induction predicate (strengthened)
    # ====================================================================
    # P(k) = ∃q0,r0. Apply(hp,k,q0) ∧ Apply(hn,k,r0) ∧ Apply(hm,r0,q0) ∧ In(q0,wv) ∧ In(r0,wv)
    q0v = Var(postfix='q0')
    r0v = Var(postfix='r0')
    def P_and(kvar, q0, r0):
        return And(Apply(hp, kvar, q0),
            And(Apply(hn, kvar, r0),
                And(Apply(hm, r0, q0),
                    And(In(q0, wv), In(r0, wv)))))
    def P(kvar):
        return Exists(q0v, Exists(r0v, P_and(kvar, q0v, r0v)))

    # ====================================================================
    # Section 3: Extract Recursive base/step for hp, hn, hm
    # ====================================================================
    ev = Var()
    base_hp = Forall(ev, Implies(Empty(ev), Apply(hp, ev, p)))
    base_hn = Forall(ev, Implies(Empty(ev), Apply(hn, ev, n)))
    base_hm = Forall(ev, Implies(Empty(ev), Apply(hm, ev, m)))

    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()

    func_hp = FuncDef(hp)
    func_hn = FuncDef(hn)
    func_hm = FuncDef(hm)
    xd_h, yd_h = Var(), Var()
    dom_sub_hp = Forall(xd_h, Implies(Exists(yd_h, Apply(hp, xd_h, yd_h)), In(xd_h, wv)))
    dom_sub_hn = Forall(xd_h, Implies(Exists(yd_h, Apply(hn, xd_h, yd_h)), In(xd_h, wv)))
    dom_sub_hm = Forall(xd_h, Implies(Exists(yd_h, Apply(hm, xd_h, yd_h)), In(xd_h, wv)))

    step_hp = Forall(nst, Implies(In(nst, wv_p),
        Forall(valst, Implies(Apply(hp, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv_p, valst, fvalst),
                    Apply(hp, snst, fvalst)))))))))

    step_hm = Forall(nst, Implies(In(nst, wv),
        Forall(valst, Implies(Apply(hm, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hm, snst, fvalst)))))))))

    dom_sub_hp = Forall(xd_h, Implies(Exists(yd_h, Apply(hp, xd_h, yd_h)), In(xd_h, wv_p)))
    and_base_step_hp = And(base_hp, step_hp)
    and_dom_bs_hp = And(dom_sub_hp, and_base_step_hp)
    got_dom_bs_hp = apply_thm(and_elim_right(func_hp, and_dom_bs_hp, []), [],
        rec_hp, and_dom_bs_hp, ax(rec_hp))
    got_base_hp = apply_thm(and_elim_left(base_hp, step_hp, []), [],
        and_base_step_hp, base_hp,
        apply_thm(and_elim_right(dom_sub_hp, and_base_step_hp, []), [],
            and_dom_bs_hp, and_base_step_hp, got_dom_bs_hp))

    step_hn = Forall(nst, Implies(In(nst, wv_n),
        Forall(valst, Implies(Apply(hn, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv_n, valst, fvalst),
                    Apply(hn, snst, fvalst)))))))))

    dom_sub_hn = Forall(xd_h, Implies(Exists(yd_h, Apply(hn, xd_h, yd_h)), In(xd_h, wv_n)))
    and_base_step_hn = And(base_hn, step_hn)
    and_dom_bs_hn = And(dom_sub_hn, and_base_step_hn)
    got_dom_bs_hn = apply_thm(and_elim_right(func_hn, and_dom_bs_hn, []), [],
        rec_hn, and_dom_bs_hn, ax(rec_hn))
    got_base_hn = apply_thm(and_elim_left(base_hn, step_hn, []), [],
        and_base_step_hn, base_hn,
        apply_thm(and_elim_right(dom_sub_hn, and_base_step_hn, []), [],
            and_dom_bs_hn, and_base_step_hn, got_dom_bs_hn))

    # In(n,wv) and In(p,wv) needed for base case
    # These are assumed on the left for now (from omega_unique transfer)
    in_n_wv = In(n, wv)
    in_p_wv = In(p, wv)
    in_k_wv = In(k, wv)

    # In(p,wv) from rec_val_in_omega on hm: Apply(hm,n,p) + In(n,wv)
    rvo = rec_val_in_omega()
    got_in_p_wv = apply_thm(rvo, [wv, m, sfv, hm, n, p], omega_wv,
        Implies(In(m, wv), Implies(succ_char, Implies(rec_hm,
            Implies(in_n_wv, Implies(app_hm_np, in_p_wv))))),
        ax(omega_wv))
    got_in_p_wv = mp(got_in_p_wv, ax(In(m, wv)), In(m, wv),
        Implies(succ_char, Implies(rec_hm, Implies(in_n_wv, Implies(app_hm_np, in_p_wv)))))
    got_in_p_wv = mp(got_in_p_wv, ax(succ_char), succ_char,
        Implies(rec_hm, Implies(in_n_wv, Implies(app_hm_np, in_p_wv))))
    got_in_p_wv = mp(got_in_p_wv, ax(rec_hm), rec_hm,
        Implies(in_n_wv, Implies(app_hm_np, in_p_wv)))
    got_in_p_wv = mp(got_in_p_wv, ax(in_n_wv), in_n_wv, Implies(app_hm_np, in_p_wv))
    got_in_p_wv = mp(got_in_p_wv, ax(app_hm_np), app_hm_np, in_p_wv)

    # ====================================================================
    # Section 4: Separation for induction
    # ====================================================================
    from core.proof import _expand
    pv = Var(postfix='pv')
    xind = Var(postfix='xi')
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, wv), P(xind))))
    sep = separation(P, [hm, hn, hp, wv])
    got_sep = sep
    for term in [wv, hp, hn, hm]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)],
            principal=actual)
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, Exists(pv, char_p), wv)
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)), wl(fl_w, *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    from theorems.logic import (iff_mp, iff_mp_rev)

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
    # Section 5: Base case — P(0)
    # ====================================================================
    # P(0) = ∃q0,r0. Apply(hp,0,q0) ∧ Apply(hn,0,r0) ∧ Apply(hm,r0,q0) ∧ In(q0,wv) ∧ In(r0,wv)
    # Witnesses: q0=p, r0=n.
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)
    oce = omega_contains_empty()
    got_eb_wv = apply_thm(oce, [wv], omega_wv,
        Forall(eb, Implies(empty_eb, In(eb, wv))), ax(omega_wv))
    got_eb_wv = apply_thm(got_eb_wv, [eb], empty_eb, In(eb, wv), ax(empty_eb))

    got_hp_0 = apply_thm(got_base_hp, [eb], empty_eb, Apply(hp, eb, p), ax(empty_eb))
    got_hn_0 = apply_thm(got_base_hn, [eb], empty_eb, Apply(hn, eb, n), ax(empty_eb))

    # Build P_and(eb, p, n) = And(Apply(hp,eb,p), And(Apply(hn,eb,n), And(Apply(hm,n,p), And(In(p,wv), In(n,wv)))))
    p_and_base = P_and(eb, p, n)
    # Build from inside out
    got_and_4 = mp(apply_thm(and_intro(in_p_wv, in_n_wv, []), [],
        in_p_wv, Implies(in_n_wv, And(in_p_wv, in_n_wv)), got_in_p_wv),
        ax(in_n_wv), in_n_wv, And(in_p_wv, in_n_wv))
    got_and_3 = mp(apply_thm(and_intro(app_hm_np, And(in_p_wv, in_n_wv), []), [],
        app_hm_np, Implies(And(in_p_wv, in_n_wv), And(app_hm_np, And(in_p_wv, in_n_wv))),
        ax(app_hm_np)),
        got_and_4, And(in_p_wv, in_n_wv), And(app_hm_np, And(in_p_wv, in_n_wv)))
    _inner_2n = And(Apply(hn, eb, n), And(app_hm_np, And(in_p_wv, in_n_wv)))
    got_and_2 = mp(
        apply_thm(and_intro(Apply(hn, eb, n), And(app_hm_np, And(in_p_wv, in_n_wv)), []), [],
            Apply(hn, eb, n), Implies(And(app_hm_np, And(in_p_wv, in_n_wv)), _inner_2n), got_hn_0),
        got_and_3, And(app_hm_np, And(in_p_wv, in_n_wv)), _inner_2n)
    got_and_1 = mp(
        apply_thm(and_intro(Apply(hp, eb, p), _inner_2n, []), [],
            Apply(hp, eb, p), Implies(_inner_2n, p_and_base), got_hp_0),
        got_and_2, _inner_2n, p_and_base)

    # Wrap in Exists: P(eb)
    P_eb = P(eb)
    got_p_eb = eir(eir(got_and_1, P_and(eb, p, r0v), r0v, n),
        Exists(r0v, P_and(eb, q0v, r0v)), q0v, p)

    # And(In(eb,wv), P(eb)) -> In(eb,pv)
    and_eb = And(In(eb, wv), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, wv), P_eb, []), [],
        In(eb, wv), Implies(P_eb, and_eb), got_eb_wv),
        got_p_eb, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # ====================================================================
    # Section 6: Step case — In(xs, pv) -> In(S(xs), pv)
    # ====================================================================
    xs = Var(postfix='xs')
    sxs = Var(postfix='sxs')
    in_xs_pv = In(xs, pv)
    succ_sxs_xs = SuccDef(sxs, xs)

    # From In(xs, pv) -> And(In(xs, wv), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, wv), P(xs)))
    got_in_xs_wv = apply_thm(and_elim_left(In(xs, wv), P(xs), []), [],
        And(In(xs, wv), P(xs)), In(xs, wv), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, wv), P(xs), []), [],
        And(In(xs, wv), P(xs)), P(xs), got_and_xs)

    # Open P(xs): get q0_s, r0_s with Apply(hp,xs,q0_s), Apply(hn,xs,r0_s),
    # Apply(hm,r0_s,q0_s), In(q0_s,wv), In(r0_s,wv)
    q0_s = Var(postfix='qs')
    r0_s = Var(postfix='rs')
    p_and_xs = P_and(xs, q0_s, r0_s)
    got_app_hp = apply_thm(and_elim_left(Apply(hp, xs, q0_s),
        And(Apply(hn, xs, r0_s), And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv)))), []), [],
        p_and_xs, Apply(hp, xs, q0_s), ax(p_and_xs))
    inner_4 = And(Apply(hn, xs, r0_s), And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv))))
    got_inner = apply_thm(and_elim_right(Apply(hp, xs, q0_s), inner_4, []), [],
        p_and_xs, inner_4, ax(p_and_xs))
    got_app_hn = apply_thm(and_elim_left(Apply(hn, xs, r0_s),
        And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv))), []), [],
        inner_4, Apply(hn, xs, r0_s), got_inner)
    inner_3 = And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv)))
    got_inner2 = apply_thm(and_elim_right(Apply(hn, xs, r0_s), inner_3, []), [],
        inner_4, inner_3, got_inner)
    got_app_hm = apply_thm(and_elim_left(Apply(hm, r0_s, q0_s),
        And(In(q0_s, wv), In(r0_s, wv)), []), [],
        inner_3, Apply(hm, r0_s, q0_s), got_inner2)
    inner_2 = And(In(q0_s, wv), In(r0_s, wv))
    got_inner3 = apply_thm(and_elim_right(Apply(hm, r0_s, q0_s), inner_2, []), [],
        inner_3, inner_2, got_inner2)
    got_in_q0 = apply_thm(and_elim_left(In(q0_s, wv), In(r0_s, wv), []), [],
        inner_2, In(q0_s, wv), got_inner3)
    got_in_r0 = apply_thm(and_elim_right(In(q0_s, wv), In(r0_s, wv), []), [],
        inner_2, In(r0_s, wv), got_inner3)
    # All have [p_and_xs] on the left

    # successor_exists for q0_s and r0_s:
    se = successor_exists()
    sq0_s = Var(postfix='sq')
    sr0_s = Var(postfix='sr')
    succ_sq0 = SuccDef(sq0_s, q0_s)
    succ_sr0 = SuccDef(sr0_s, r0_s)
    got_se_q0 = apply_thm(se, [q0_s], concl=Exists(sq0_s, succ_sq0))
    got_se_r0 = apply_thm(se, [r0_s], concl=Exists(sr0_s, succ_sr0))

    # rec_step_succ on hp: Apply(hp,xs,q0_s) + Succ(sxs,xs) + Succ(sq0_s,q0_s) → Apply(hp,sxs,sq0_s)
    rss = rec_step_succ()
    got_rss_hp = apply_thm(rss, [wv_p, p, sfv_p, hp, xs, q0_s, sxs, sq0_s],
        omega_wp, Implies(In(xs, wv_p), Implies(In(q0_s, wv_p), Implies(succ_char_p,
            Implies(rec_hp, Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
                Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))))),
        ax(omega_wp))
    in_xs_wp = In(xs, wv_p)
    in_q0_wp = In(q0_s, wv_p)
    got_in_xs_wp = transfer_in(xs, wv, wv_p, got_eq_wv_wp, got_in_xs_wv)
    got_in_q0_wp = transfer_in(q0_s, wv, wv_p, got_eq_wv_wp, got_in_q0)
    got_rss_hp = mp(got_rss_hp, got_in_xs_wp, in_xs_wp,
        Implies(in_q0_wp, Implies(succ_char_p, Implies(rec_hp,
            Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
                Implies(succ_sq0, Apply(hp, sxs, sq0_s))))))))
    got_rss_hp = mp(got_rss_hp, got_in_q0_wp, in_q0_wp,
        Implies(succ_char_p, Implies(rec_hp, Implies(Apply(hp, xs, q0_s),
            Implies(succ_sxs_xs, Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))))
    got_rss_hp = mp(got_rss_hp, ax(succ_char_p), succ_char_p,
        Implies(rec_hp, Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
            Implies(succ_sq0, Apply(hp, sxs, sq0_s))))))
    got_rss_hp = mp(got_rss_hp, ax(rec_hp), rec_hp,
        Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
            Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))
    got_rss_hp = mp(got_rss_hp, got_app_hp, Apply(hp, xs, q0_s),
        Implies(succ_sxs_xs, Implies(succ_sq0, Apply(hp, sxs, sq0_s))))
    got_rss_hp = mp(got_rss_hp, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sq0, Apply(hp, sxs, sq0_s)))
    got_rss_hp = mp(got_rss_hp, ax(succ_sq0), succ_sq0, Apply(hp, sxs, sq0_s))

    # rec_step_succ on hn: uses wv_n, sfv_n
    got_rss_hn = apply_thm(rss, [wv_n, n, sfv_n, hn, xs, r0_s, sxs, sr0_s],
        omega_wn, Implies(In(xs, wv_n), Implies(In(r0_s, wv_n), Implies(succ_char_n,
            Implies(rec_hn, Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
                Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))))),
        ax(omega_wn))
    in_xs_wn = In(xs, wv_n)
    in_r0_wn = In(r0_s, wv_n)
    got_in_xs_wn = transfer_in(xs, wv, wv_n, got_eq_wv_wn, got_in_xs_wv)
    got_in_r0_wn = transfer_in(r0_s, wv, wv_n, got_eq_wv_wn, got_in_r0)
    got_rss_hn = mp(got_rss_hn, got_in_xs_wn, in_xs_wn,
        Implies(in_r0_wn, Implies(succ_char_n, Implies(rec_hn,
            Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
                Implies(succ_sr0, Apply(hn, sxs, sr0_s))))))))
    got_rss_hn = mp(got_rss_hn, got_in_r0_wn, in_r0_wn,
        Implies(succ_char_n, Implies(rec_hn, Implies(Apply(hn, xs, r0_s),
            Implies(succ_sxs_xs, Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))))
    got_rss_hn = mp(got_rss_hn, ax(succ_char_n), succ_char_n,
        Implies(rec_hn, Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
            Implies(succ_sr0, Apply(hn, sxs, sr0_s))))))
    got_rss_hn = mp(got_rss_hn, ax(rec_hn), rec_hn,
        Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
            Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))
    got_rss_hn = mp(got_rss_hn, got_app_hn, Apply(hn, xs, r0_s),
        Implies(succ_sxs_xs, Implies(succ_sr0, Apply(hn, sxs, sr0_s))))
    got_rss_hn = mp(got_rss_hn, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sr0, Apply(hn, sxs, sr0_s)))
    got_rss_hn = mp(got_rss_hn, ax(succ_sr0), succ_sr0, Apply(hn, sxs, sr0_s))

    # rec_step_succ on hm: Apply(hm,r0_s,q0_s) + Succ(sr0_s,r0_s) + Succ(sq0_s,q0_s) → Apply(hm,sr0_s,sq0_s)
    got_rss_hm = apply_thm(rss, [wv, m, sfv, hm, r0_s, q0_s, sr0_s, sq0_s],
        omega_wv, Implies(In(r0_s, wv), Implies(In(q0_s, wv), Implies(succ_char,
            Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
                Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))))),
        ax(omega_wv))
    got_rss_hm = mp(got_rss_hm, got_in_r0, In(r0_s, wv),
        Implies(In(q0_s, wv), Implies(succ_char, Implies(rec_hm,
            Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
                Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))))))
    got_rss_hm = mp(got_rss_hm, got_in_q0, In(q0_s, wv),
        Implies(succ_char, Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s),
            Implies(succ_sr0, Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))))
    got_rss_hm = mp(got_rss_hm, ax(succ_char), succ_char,
        Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
            Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))))
    got_rss_hm = mp(got_rss_hm, ax(rec_hm), rec_hm,
        Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
            Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))
    got_rss_hm = mp(got_rss_hm, got_app_hm, Apply(hm, r0_s, q0_s),
        Implies(succ_sr0, Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))
    got_rss_hm = mp(got_rss_hm, ax(succ_sr0), succ_sr0,
        Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))
    got_rss_hm = mp(got_rss_hm, ax(succ_sq0), succ_sq0, Apply(hm, sr0_s, sq0_s))

    # In(sq0_s, wv) and In(sr0_s, wv) from omega_succ_closed:
    osc = omega_succ_closed()
    got_in_sq0 = apply_thm(osc, [wv], omega_wv,
        Forall(q0_s, Implies(In(q0_s, wv), Forall(sq0_s, Implies(succ_sq0, In(sq0_s, wv))))),
        ax(omega_wv))
    got_in_sq0 = apply_thm(got_in_sq0, [q0_s], In(q0_s, wv),
        Forall(sq0_s, Implies(succ_sq0, In(sq0_s, wv))), got_in_q0)
    got_in_sq0 = apply_thm(got_in_sq0, [sq0_s], succ_sq0, In(sq0_s, wv), ax(succ_sq0))

    got_in_sr0 = apply_thm(osc, [wv], omega_wv,
        Forall(r0_s, Implies(In(r0_s, wv), Forall(sr0_s, Implies(succ_sr0, In(sr0_s, wv))))),
        ax(omega_wv))
    got_in_sr0 = apply_thm(got_in_sr0, [r0_s], In(r0_s, wv),
        Forall(sr0_s, Implies(succ_sr0, In(sr0_s, wv))), got_in_r0)
    got_in_sr0 = apply_thm(got_in_sr0, [sr0_s], succ_sr0, In(sr0_s, wv), ax(succ_sr0))

    # Build P(sxs) = ∃q0,r0. P_and(sxs, q0, r0) with witnesses sq0_s, sr0_s
    p_and_step = P_and(sxs, sq0_s, sr0_s)
    # Build the 5-deep And from inside out
    got_and_s4 = mp(apply_thm(and_intro(In(sq0_s, wv), In(sr0_s, wv), []), [],
        In(sq0_s, wv), Implies(In(sr0_s, wv), And(In(sq0_s, wv), In(sr0_s, wv))),
        got_in_sq0),
        got_in_sr0, In(sr0_s, wv), And(In(sq0_s, wv), In(sr0_s, wv)))
    got_and_s3 = mp(apply_thm(and_intro(Apply(hm, sr0_s, sq0_s),
        And(In(sq0_s, wv), In(sr0_s, wv)), []), [],
        Apply(hm, sr0_s, sq0_s),
        Implies(And(In(sq0_s, wv), In(sr0_s, wv)),
            And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
        got_rss_hm),
        got_and_s4, And(In(sq0_s, wv), In(sr0_s, wv)),
        And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))))
    got_and_s2 = mp(apply_thm(and_intro(Apply(hn, sxs, sr0_s),
        And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))), []), [],
        Apply(hn, sxs, sr0_s),
        Implies(And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))),
            And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))))),
        got_rss_hn),
        got_and_s3, And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))),
        And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))))
    got_and_s1 = mp(apply_thm(and_intro(Apply(hp, sxs, sq0_s),
        And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))), []), [],
        Apply(hp, sxs, sq0_s),
        Implies(And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
            p_and_step),
        got_rss_hp),
        got_and_s2, And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
        p_and_step)

    P_sxs = P(sxs)
    got_p_sxs = eir(eir(got_and_s1, P_and(sxs, sq0_s, r0v), r0v, sr0_s),
        Exists(r0v, P_and(sxs, q0v, r0v)), q0v, sq0_s)

    # Close existentials: eel sq0_s, sr0_s (from successor_exists), then r0_s, q0_s (from P(xs))
    cur_step = eel(got_p_sxs, succ_sq0, sq0_s)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_q0)
    cur_step = eel(cur_step, succ_sr0, sr0_s)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_r0)
    cur_step = eel(cur_step, p_and_xs, r0_s)
    cur_step = eel(cur_step, cur_step.sequent.left[-1], q0_s)
    # Connect with P(xs)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_P_xs)

    # In(sxs, wv) from omega_succ_closed:
    got_in_sxs = apply_thm(osc, [wv], omega_wv,
        Forall(xs, Implies(In(xs, wv), Forall(sxs, Implies(succ_sxs_xs, In(sxs, wv))))),
        ax(omega_wv))
    got_in_sxs = apply_thm(got_in_sxs, [xs], In(xs, wv),
        Forall(sxs, Implies(succ_sxs_xs, In(sxs, wv))), got_in_xs_wv)
    got_in_sxs = apply_thm(got_in_sxs, [sxs], succ_sxs_xs, In(sxs, wv), ax(succ_sxs_xs))

    # And(In(sxs, wv), P(sxs)) -> In(sxs, pv)
    and_sxs = And(In(sxs, wv), P_sxs)
    got_and_sxs = mp(apply_thm(and_intro(In(sxs, wv), P_sxs, []), [],
        In(sxs, wv), Implies(P_sxs, and_sxs), got_in_sxs),
        cur_step, P_sxs, and_sxs)
    got_in_sxs_pv = mp(char_p_bwd(sxs), got_and_sxs, and_sxs, In(sxs, pv))

    # Discharge succ_sxs_xs and In(xs, pv):
    imp_succ = Implies(succ_sxs_xs, In(sxs, pv))
    rem_succ = [f_ for f_ in got_in_sxs_pv.sequent.left if not same(f_, succ_sxs_xs)]
    got_imp_succ = Proof(Sequent(rem_succ, [imp_succ]), 'implies_right',
        [got_in_sxs_pv], principal=imp_succ)
    fa_sxs = Forall(sxs, imp_succ)
    got_fa_sxs = Proof(Sequent(rem_succ, [fa_sxs]), 'forall_right',
        [got_imp_succ], principal=fa_sxs, term=sxs)
    imp_xs = Implies(in_xs_pv, fa_sxs)
    rem_xs = [f_ for f_ in got_fa_sxs.sequent.left if not same(f_, in_xs_pv)]
    got_step = Proof(Sequent(rem_xs, [imp_xs]), 'implies_right',
        [got_fa_sxs], principal=imp_xs)
    fa_xs = Forall(xs, imp_xs)
    got_step = Proof(Sequent(rem_xs, [fa_xs]), 'forall_right',
        [got_step], principal=fa_xs, term=xs)

    # ====================================================================
    # Section 7: Induction closure
    # ====================================================================
    # Build base_ind and step_ind for Inductive(pv)
    imp_base_ind = Implies(empty_eb, In(eb, pv))
    rem_base_ind = [f_ for f_ in got_in_eb_pv.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_base_ind, [imp_base_ind]), 'implies_right',
        [got_in_eb_pv], principal=imp_base_ind)
    base_ind = Forall(eb, imp_base_ind)
    proof_base = Proof(Sequent(rem_base_ind, [base_ind]), 'forall_right',
        [proof_base], principal=base_ind, term=eb)

    step_ind = fa_xs
    proof_step = got_step

    from vocab import Inductive as InductiveDef, Subset as SubsetDef
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
    # Section 8: Extract P(k) from Eq(pv,wv) + In(k,wv)
    # ====================================================================
    iff_k_pv = Iff(In(k, pv), in_k_wv)
    got_iff_k = Proof(Sequent(got_eq.sequent.left, [iff_k_pv]), 'cut',
        [wr(got_eq, iff_k_pv),
         weaken_to(fl(eq_pw, iff_k_pv, k), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_k_pv = mp(mp(iff_mp_rev(In(k, pv), in_k_wv, []),
        got_iff_k, iff_k_pv, Implies(in_k_wv, In(k, pv))),
        ax(in_k_wv), in_k_wv, In(k, pv))

    got_fwd_k = char_p_fwd(k)
    all_ext = list(got_in_k_pv.sequent.left)
    for f_ in got_fwd_k.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_k = mp(weaken_to(got_fwd_k, all_ext),
        weaken_to(got_in_k_pv, all_ext), In(k, pv), And(in_k_wv, P(k)))
    got_p_k = apply_thm(and_elim_right(in_k_wv, P(k), []), [],
        And(in_k_wv, P(k)), P(k), got_and_k)
    # got_p_k: [..., In(k,wv)] |- P(k) = ∃q0,r0. P_and(k, q0, r0)

    # ====================================================================
    # Section 9: From P(k) + Apply(hp,k,q) + Apply(hn,k,r), derive Apply(hm,r,q)
    # ====================================================================
    # Open P(k): get q0_f, r0_f with Apply(hp,k,q0_f), Apply(hn,k,r0_f),
    # Apply(hm,r0_f,q0_f), In(q0_f,wv), In(r0_f,wv).
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.omega import func_unique_thm
    fut = func_unique_thm()
    eavt = eq_apply_val_transfer()
    eat = eq_apply_transfer()
    es = eq_symmetric()

    q0_f = Var(postfix='qf')
    r0_f = Var(postfix='rf')
    p_and_k = P_and(k, q0_f, r0_f)
    # Extract components from p_and_k
    got_f_app_hp = apply_thm(and_elim_left(Apply(hp, k, q0_f),
        And(Apply(hn, k, r0_f), And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv)))), []), [],
        p_and_k, Apply(hp, k, q0_f), ax(p_and_k))
    _f_inner = And(Apply(hn, k, r0_f), And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))))
    got_f_inner = apply_thm(and_elim_right(Apply(hp, k, q0_f), _f_inner, []), [],
        p_and_k, _f_inner, ax(p_and_k))
    got_f_app_hn = apply_thm(and_elim_left(Apply(hn, k, r0_f),
        And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), []), [],
        _f_inner, Apply(hn, k, r0_f), got_f_inner)
    got_f_app_hm = apply_thm(and_elim_left(Apply(hm, r0_f, q0_f),
        And(In(q0_f, wv), In(r0_f, wv)), []), [],
        And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))),
        Apply(hm, r0_f, q0_f),
        apply_thm(and_elim_right(Apply(hn, k, r0_f),
            And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), []), [],
            _f_inner, And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), got_f_inner))

    # func_unique(hp): Apply(hp,k,q) + Apply(hp,k,q0_f) → Eq(q,q0_f)
    got_func_hp = apply_thm(and_elim_left(func_hp,
        And(dom_sub_hp, and_base_step_hp), []), [], rec_hp, func_hp, ax(rec_hp))
    got_eq_q = apply_thm(fut, [hp, k, q, q0_f], func_hp,
        Implies(Apply(hp, k, q), Implies(Apply(hp, k, q0_f), Eq(q, q0_f))),
        got_func_hp)
    got_eq_q = mp(mp(got_eq_q, ax(app_hp_kq), app_hp_kq,
        Implies(Apply(hp, k, q0_f), Eq(q, q0_f))),
        got_f_app_hp, Apply(hp, k, q0_f), Eq(q, q0_f))

    # func_unique(hn): Apply(hn,k,r) + Apply(hn,k,r0_f) → Eq(r,r0_f)
    got_func_hn = apply_thm(and_elim_left(func_hn,
        And(dom_sub_hn, and_base_step_hn), []), [], rec_hn, func_hn, ax(rec_hn))
    got_eq_r = apply_thm(fut, [hn, k, r, r0_f], func_hn,
        Implies(app_hn_kr, Implies(Apply(hn, k, r0_f), Eq(r, r0_f))),
        got_func_hn)
    got_eq_r = mp(mp(got_eq_r, ax(app_hn_kr), app_hn_kr,
        Implies(Apply(hn, k, r0_f), Eq(r, r0_f))),
        got_f_app_hn, Apply(hn, k, r0_f), Eq(r, r0_f))

    # Transfer: Apply(hm,r0_f,q0_f) + Eq(r0_f,r) → Apply(hm,r,q0_f) + Eq(q0_f,q) → Apply(hm,r,q)
    got_eq_r0f_r = apply_thm(es, [r, r0_f], Eq(r, r0_f), Eq(r0_f, r), got_eq_r)
    got_hm_r_q0f = apply_thm(eat, [hm, r0_f, r, q0_f], Eq(r0_f, r),
        Implies(Apply(hm, r0_f, q0_f), Apply(hm, r, q0_f)), got_eq_r0f_r)
    got_hm_r_q0f = mp(got_hm_r_q0f, got_f_app_hm, Apply(hm, r0_f, q0_f), Apply(hm, r, q0_f))

    got_eq_q0f_q = apply_thm(es, [q, q0_f], Eq(q, q0_f), Eq(q0_f, q), got_eq_q)
    got_hm_rq = apply_thm(eavt, [hm, r, q0_f, q], Eq(q0_f, q),
        Implies(Apply(hm, r, q0_f), app_hm_rq), got_eq_q0f_q)
    got_hm_rq = mp(got_hm_rq, got_hm_r_q0f, Apply(hm, r, q0_f), app_hm_rq)
    # [..., p_and_k, app_hp_kq, app_hn_kr] |- Apply(hm, r, q)

    # eel r0_f, q0_f from P(k) opening, cut with got_p_k
    proof = eel(got_hm_rq, p_and_k, r0_f)
    proof = eel(proof, proof.sequent.left[-1], q0_f)
    proof = cut(proof, proof.sequent.left[-1], got_p_k)

    # eel pv from char_p, cut with got_sep
    if any(same(char_p, g) for g in proof.sequent.left):
        proof = eel(proof, char_p, pv)
        proof = cut(proof, proof.sequent.left[-1], got_sep)

    # ====================================================================
    # Section 10: Package Plus(m,r,q) and discharge
    # ====================================================================
    # Build Plus(m,r,q) on the right from Apply(hm,r,q) + rec_hm + sf_all + omega_wv
    # Plus(m,r,q) = ∃wv. And(Omega(wv), ∃hm. ∃sfv. And(sf_all, And(rec_hm, Apply(hm,r,q))))
    # For now, just package Apply(hm,r,q) into the Plus structure.
    # This requires building the right side with eir.

    and_rec_rq = And(rec_hm, app_hm_rq)
    got_and_rec = mp(apply_thm(and_intro(rec_hm, app_hm_rq, []), [],
        rec_hm, Implies(app_hm_rq, and_rec_rq), ax(rec_hm)),
        proof, app_hm_rq, and_rec_rq)
    and_sf_rec = And(sf_all, and_rec_rq)
    got_and_sf = mp(apply_thm(and_intro(sf_all, and_rec_rq, []), [],
        sf_all, Implies(and_rec_rq, and_sf_rec), ax(sf_all)),
        got_and_rec, and_rec_rq, and_sf_rec)
    # Package Apply(hm,r,q) into Plus(m,r,q)
    and_rec_rq = And(rec_hm, app_hm_rq)
    got_and_rec = mp(apply_thm(and_intro(rec_hm, app_hm_rq, []), [],
        rec_hm, Implies(app_hm_rq, and_rec_rq), ax(rec_hm)),
        proof, app_hm_rq, and_rec_rq)
    and_sf_rec = And(sf_all, and_rec_rq)
    got_and_sf = mp(apply_thm(and_intro(sf_all, and_rec_rq, []), [],
        sf_all, Implies(and_rec_rq, and_sf_rec), ax(sf_all)),
        got_and_rec, and_rec_rq, and_sf_rec)
    # Use fresh vars for eir to avoid _var_bound_in conflicts with forall_right
    sfv_e, hm_e, wv_e = Var(), Var(), Var()
    # Build body with fresh vars, then eir
    from core.proof import _subst
    and_sf_rec_e = _subst(and_sf_rec, sfv, sfv_e)
    got_ex_sf = eir(got_and_sf, and_sf_rec_e, sfv_e, sfv)
    ex_sf_body = Exists(sfv_e, and_sf_rec_e)
    ex_sf_body_e = _subst(ex_sf_body, hm, hm_e)
    got_ex_hm = eir(got_ex_sf, ex_sf_body_e, hm_e, hm)
    ex_hm_body = Exists(hm_e, ex_sf_body_e)
    and_omega_result = And(omega_wv, ex_hm_body)
    got_and_omega = mp(apply_thm(and_intro(omega_wv, ex_hm_body, []), [],
        omega_wv, Implies(ex_hm_body, and_omega_result), ax(omega_wv)),
        got_ex_hm, ex_hm_body, and_omega_result)
    and_omega_result_e = _subst(and_omega_result, wv, wv_e)
    got_plus_result = eir(got_and_omega, and_omega_result_e, wv_e, wv)
    proof = got_plus_result
    # sfv, hm, wv now bound on right. Plus(m,r,q) on right.

    # ====================================================================
    # Section 11: Discharge hypotheses
    # ====================================================================
    # The internal proof uses shared sfv/wv for all three Plus definitions.
    # Folding back into separate Plus(m,n,p), Plus(p,k,q), Plus(n,k,r)
    # requires sf_apply_transfer + rec_unique to show the shared sf agrees
    # with each Plus's individual sf. For now: discharge all non-axiom
    # hypotheses generically. The conclusion has extra quantifiers/implications
    # for the internal variables beyond the standard Plus-based goal.
    # A proper wrapper (opening Plus, applying this, repackaging) is TODO.
    def cut_all(prf, formula, derivation):
        while any(same(formula, g) for g in prf.sequent.left):
            prf = cut(prf, formula, derivation)
        return prf

    # Cut intermediate transfers back
    proof = cut_all(proof, In(m, wv), got_in_m_wv)
    proof = cut_all(proof, in_n_wv, got_in_n_wv)
    proof = cut_all(proof, in_k_wv, got_in_k_wv)
    proof = cut_all(proof, in_p_wv, got_in_p_wv)
    proof = cut_all(proof, eq_wv_wp, got_eq_wv_wp)
    proof = cut_all(proof, eq_wv_wn, got_eq_wv_wn)
    proof = cut_all(proof, eq_w_wv, got_eq_w_wv)

    # Cut succ_char/func/dom back to sf_all
    proof = cut_all(proof, succ_char, got_sc_from)
    proof = cut_all(proof, func_sf, got_func_sf_from)
    proof = cut_all(proof, dom_sub_sf, got_dom_sf_from)
    proof = cut_all(proof, and_func_dom, got_fd_from)

    # Fold Plus(p,k,q): cut succ_char_p components → sf_all_p, then fold
    proof = cut_all(proof, succ_char_p, apply_thm(and_elim_left(succ_char_p, and_func_dom_p, []), [],
        sf_all_p, succ_char_p, ax(sf_all_p)))
    proof = cut_all(proof, func_sfp, apply_thm(and_elim_left(func_sfp, dom_sub_sfp, []), [],
        and_func_dom_p, func_sfp, apply_thm(and_elim_right(succ_char_p, and_func_dom_p, []), [],
            sf_all_p, and_func_dom_p, ax(sf_all_p))))
    proof = cut_all(proof, dom_sub_sfp, apply_thm(and_elim_right(func_sfp, dom_sub_sfp, []), [],
        and_func_dom_p, dom_sub_sfp, apply_thm(and_elim_right(succ_char_p, and_func_dom_p, []), [],
            sf_all_p, and_func_dom_p, ax(sf_all_p))))
    proof = cut_all(proof, rec_hp, got_rec_hp_from)
    proof = cut_all(proof, app_hp_kq, got_app_hp_from)
    proof = cut_all(proof, func_hp, apply_thm(and_elim_left(func_hp,
        And(dom_sub_hp, and_base_step_hp), []), [], rec_hp, func_hp, ax(rec_hp)))
    proof = cut_all(proof, sf_all_p, got_sf_p_from)
    proof = cut_all(proof, and_rec_app_p, got_ra_p_from)
    if any(same(and_sf_ra_p, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_p, sfv_p)
        ex_sfp = proof.sequent.left[-1]
        proof = eel(proof, ex_sfp, hp)
        ex_hp = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hp, got_exhp_from)
    proof = cut_all(proof, omega_wp, got_omega_wp_from)
    if any(same(and_omega_p, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_p, wv_p)

    # Fold Plus(n,k,r): cut succ_char_n components → sf_all_n
    proof = cut_all(proof, succ_char_n, apply_thm(and_elim_left(succ_char_n, and_func_dom_n, []), [],
        sf_all_n, succ_char_n, ax(sf_all_n)))
    proof = cut_all(proof, func_sfn, apply_thm(and_elim_left(func_sfn, dom_sub_sfn, []), [],
        and_func_dom_n, func_sfn, apply_thm(and_elim_right(succ_char_n, and_func_dom_n, []), [],
            sf_all_n, and_func_dom_n, ax(sf_all_n))))
    proof = cut_all(proof, dom_sub_sfn, apply_thm(and_elim_right(func_sfn, dom_sub_sfn, []), [],
        and_func_dom_n, dom_sub_sfn, apply_thm(and_elim_right(succ_char_n, and_func_dom_n, []), [],
            sf_all_n, and_func_dom_n, ax(sf_all_n))))
    proof = cut_all(proof, rec_hn, got_rec_hn_from)
    proof = cut_all(proof, app_hn_kr, got_app_hn_from)
    proof = cut_all(proof, func_hn, apply_thm(and_elim_left(func_hn,
        And(dom_sub_hn, and_base_step_hn), []), [], rec_hn, func_hn, ax(rec_hn)))
    proof = cut_all(proof, sf_all_n, got_sf_n_from)
    proof = cut_all(proof, and_rec_app_n, got_ra_n_from)
    if any(same(and_sf_ra_n, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_n, sfv_n)
        ex_sfn = proof.sequent.left[-1]
        proof = eel(proof, ex_sfn, hn)
        ex_hn = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hn, got_exhn_from)
    proof = cut_all(proof, omega_wn, got_omega_wn_from)
    if any(same(and_omega_n, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_n, wv_n)

    # Fold Plus(m,n,p)
    proof = cut_all(proof, rec_hm, got_rec_from)
    proof = cut_all(proof, app_hm_np, got_app_from)
    _and_dom_bs_hm = And(dom_sub_hm, And(base_hm, step_hm))
    proof = cut_all(proof, func_hm, apply_thm(and_elim_left(func_hm,
        _and_dom_bs_hm, []), [], rec_hm, func_hm, ax(rec_hm)))
    proof = cut_all(proof, sf_all, got_sf_from)
    proof = cut_all(proof, and_rec_app_m, got_ra_from)
    if any(same(and_sf_ra_m, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_m, sfv)
        ex_sfv = proof.sequent.left[-1]
        proof = eel(proof, ex_sfv, hm)
        ex_hm = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hm, got_exhm_from)
    proof = cut_all(proof, omega_wv, got_omega_from)
    if any(same(and_omega_m, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_m, wv)

    # Discharge goal hypotheses
    g_body = goal
    for _ in range(7):
        g_body = g_body.body
    goal_imps = []
    cur = g_body
    while isinstance(cur, Implies):
        goal_imps.append((cur.left, cur))
        cur = cur.right
    for hyp, imp_formula in reversed(goal_imps):
        if any(same(hyp, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hyp)]
            proof = Proof(Sequent(rem, [imp_formula]), 'implies_right',
                [proof], principal=imp_formula)

    # Close foralls
    for i in range(6, -1, -1):
        cur_goal = goal
        for _ in range(i):
            cur_goal = cur_goal.body
        proof = Proof(Sequent(proof.sequent.left, [cur_goal]), 'forall_right',
            [proof], principal=cur_goal, term=cur_goal.var)

    proof.name = 'plus_assoc'
    return proof
