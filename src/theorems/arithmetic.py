"""Theorems: arithmetic module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from definitions import Empty, OrdPair, Omega

from theorems.logic import (iff_mp, iff_mp_rev, iff_intro, and_intro,
    and_elim_left, and_elim_right, eq_reflexive, eq_substitution)
from theorems.sets import (kuratowski, ordpair_exists, unique_successor,
    eq_successor_transfer)
from theorems.recursion import succ_func_exists


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
    got_eq_qq = apply_thm(er, [qv], concl=Eq(qv, qv))
    got_ti = apply_thm(ku, [xsc, ysc, xsf, ssf, qv], ordp_q,
        Forall(qv2, Implies(OrdPair(qv2, xsf, ssf), Implies(Eq(qv, qv2),
            And(Eq(xsc, xsf), Eq(ysc, ssf))))), ax(ordp_q))
    got_ti = apply_thm(got_ti, [qv], ordp_q_xs,
        Implies(Eq(qv, qv), And(Eq(xsc, xsf), Eq(ysc, ssf))), ax(ordp_q_xs))
    got_ti = mp(got_ti, got_eq_qq, Eq(qv, qv), And(Eq(xsc, xsf), Eq(ysc, ssf)))

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
    got_ti_dm = apply_thm(ku, [xsv, y1sv, xsf, ssf, q_dm], ordp_dm,
        Forall(qv2, Implies(OrdPair(qv2, xsf, ssf), Implies(Eq(q_dm, qv2),
            And(Eq(xsv, xsf), Eq(y1sv, ssf))))), ax(ordp_dm))
    got_ti_dm = apply_thm(got_ti_dm, [q_dm], ordp_dm_xs,
        Implies(Eq(q_dm, q_dm), And(Eq(xsv, xsf), Eq(y1sv, ssf))), ax(ordp_dm_xs))
    got_ti_dm = mp(got_ti_dm, apply_thm(er, [q_dm], concl=Eq(q_dm, q_dm)),
        Eq(q_dm, q_dm), And(Eq(xsv, xsf), Eq(y1sv, ssf)))
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
    got_ti_ds = apply_thm(ku, [xds, yds, xsf, ssf, q_ds], ordp_ds,
        Forall(qv2, Implies(OrdPair(qv2, xsf, ssf), Implies(Eq(q_ds, qv2),
            And(Eq(xds, xsf), Eq(yds, ssf))))), ax(ordp_ds))
    got_ti_ds = apply_thm(got_ti_ds, [q_ds], ordp_ds_xs,
        Implies(Eq(q_ds, q_ds), And(Eq(xds, xsf), Eq(yds, ssf))), ax(ordp_ds_xs))
    got_ti_ds = mp(got_ti_ds, apply_thm(er, [q_ds], concl=Eq(q_ds, q_ds)),
        Eq(q_ds, q_ds), And(Eq(xds, xsf), Eq(yds, ssf)))
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
    plus_goal = PlusDef(m, ev, m)

    goal = Forall(w, Forall(m, Forall(ev,
        Implies(omega_w, Implies(in_m_w, Implies(empty_ev, plus_goal))))))

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
    # Plus = Exists(w', And(Omega(w'), Exists(h, Exists(sf, And(succ_char, And(Rec, Apply))))))
    # Build And(Recursive, Apply):
    and_rec_app = And(rec_h, app_h_em)
    got_ra = mp(apply_thm(and_intro(rec_h, app_h_em, []), [], rec_h,
        Implies(app_h_em, and_rec_app), got_rec_from),
        got_app_em, app_h_em, and_rec_app)
    # And(succ_char, And(Rec, Apply)):
    and_sc_ra = And(succ_char, and_rec_app)
    got_scra = mp(apply_thm(and_intro(succ_char, and_rec_app, []), [], succ_char,
        Implies(and_rec_app, and_sc_ra), weaken_to(got_sc_from, got_ra.sequent.left)),
        got_ra, and_rec_app, and_sc_ra)
    # Exists sf, h, w:
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc3, ysc3 = Var(), Var()
    sc_pat = Forall(xsc3, Implies(In(xsc3, w), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3)))))
    inner_sf = And(sc_pat, And(RecDef(hv, m, sf_var, w), Apply(hv, ev, m)))
    got_ex_sf = eir(got_scra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sc_pat, And(RecDef(h_var, m, sf_var, w), Apply(h_var, ev, m))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(Forall(xsc3, Implies(In(xsc3, w_var), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3))))),
            And(RecDef(h_var, m, sf_var, w_var), Apply(h_var, ev, m))))))
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
    for hh in [empty_ev, In(m, w), omega_w]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [ev, m, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

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

    # === Discharge and close ===
    proof = wl(got_result, omega_w)  # omega_w not used but part of goal
    for hh in [succ_sp_p, succ_sn_n, app_h_np, rec_h, succ_char, in_p_w, in_n_w, omega_w]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [sp, sn, p, n, hv, sfv, m, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

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
    app_h_mm = Apply(hv, mv, mv)

    goal = Forall(w, Forall(sfv, Forall(hv, Forall(ev,
        Implies(omega_w, Implies(succ_char, Implies(rec_h, Implies(empty_ev,
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

    # === Discharge and close ===
    imp_mv = Implies(In(mv, w), app_h_mm)
    rem_mv = [f_ for f_ in proof.sequent.left if not same(f_, In(mv, w))]
    proof = Proof(Sequent(rem_mv, [imp_mv]), 'implies_right', [proof], principal=imp_mv)
    fa_mv = Forall(mv, imp_mv)
    proof = Proof(Sequent(rem_mv, [fa_mv]), 'forall_right', [proof], principal=fa_mv, term=mv)
    for hh in [empty_ev, rec_h, succ_char, omega_w]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [ev, hv, sfv, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

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
    plus_goal = PlusDef(ev, mv, mv)

    goal = Forall(w, Forall(mv, Forall(ev,
        Implies(omega_w, Implies(in_m_w, Implies(empty_ev, plus_goal))))))

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

    # === Package into Plus(e, m, m) ===
    # Same pattern as plus_zero_right:
    and_rec_app = And(rec_h, app_h_mm)
    got_ra = mp(apply_thm(and_intro(rec_h, app_h_mm, []), [], rec_h,
        Implies(app_h_mm, and_rec_app), ax(rec_h)),
        got_hmm, app_h_mm, and_rec_app)
    and_sc_ra = And(succ_char, and_rec_app)
    got_scra = mp(apply_thm(and_intro(succ_char, and_rec_app, []), [], succ_char,
        Implies(and_rec_app, and_sc_ra), ax(succ_char)),
        got_ra, and_rec_app, and_sc_ra)
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc2, ysc2 = Var(), Var()
    sc_pat = Forall(xsc2, Implies(In(xsc2, w), Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2)))))
    inner_sf = And(sc_pat, And(RecDef(hv, ev, sf_var, w), Apply(hv, mv, mv)))
    got_ex_sf = eir(got_scra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sc_pat, And(RecDef(h_var, ev, sf_var, w), Apply(h_var, mv, mv))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(Forall(xsc2, Implies(In(xsc2, w_var), Forall(ysc2, Iff(Apply(sf_var, xsc2, ysc2), SuccDef(ysc2, xsc2))))),
            And(RecDef(h_var, ev, sf_var, w_var), Apply(h_var, mv, mv))))))
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

    # Discharge and close:
    proof = cur
    for hh in [empty_ev, in_m_w, omega_w]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [ev, mv, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'plus_zero_left'
    return proof


def plus_comm():
    """Commutativity of addition: m + n = n + m.
    |- forall w, m, n, p.
         Omega(w) -> In(m, w) -> In(n, w) ->
         Plus(m, n, p) -> Plus(n, m, p)
    Requires: plus_zero_right, plus_succ_right, plus_zero_left, plus_succ_left."""
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
