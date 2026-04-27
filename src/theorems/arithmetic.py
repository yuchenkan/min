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

    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')

    # === Step 1: sf from sf_props ===
    sp = sf_props()
    # sp: [Pairing, Ext, Rep] |- forall w. exists sf. And(succ_char, Function(sf))
    app_sf = Apply(sfv, xsc, ysc)
    succ_yx = SuccDef(ysc, xsc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf, succ_yx))))
    func_sf = FuncDef(sfv)
    and_sc_func = And(succ_char, func_sf)
    ex_sf = Exists(sfv, and_sc_func)
    got_sp = apply_thm(sp, [w], concl=ex_sf)
    # got_sp: [axioms] |- Exists(sfv, And(succ_char, Function(sf)))

    # === Step 2: Build dom_closed(sf, m) ===
    # dom_closed = And(f_at_a, ran_f_closed) where f=sf, a=m
    # f_at_a = exists z. Apply(sf, m, z): from m in w + succ_char + successor_exists
    # ran_f_closed = forall y,z. Apply(sf,y,z) -> exists q. Apply(sf,z,q):
    #   from succ_char: Apply(sf,y,z) -> y in w and Succ(z,y) -> z in w (omega_succ_closed)
    #   -> exists q. Apply(sf,z,q) (backward succ_char + successor_exists)

    # f_at_a: succ_char at (m, sm): In(m,w) -> Iff(Apply(sf,m,sm), Succ(sm,m))
    # backward: Succ(sm,m) -> Apply(sf,m,sm). From successor_exists: exists sm. Succ(sm,m).
    sm = Var(postfix='sm')
    se = successor_exists()
    got_se = apply_thm(se, [m], concl=Exists(sm, SuccDef(sm, m)))
    # [Pairing] |- Exists(sm, Succ(sm,m))

    # succ_char at m: In(m,w) -> forall y. Iff(Apply(sf,m,y), Succ(y,m))
    sc_at_m = Implies(In(m, w), Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m))))
    got_sc_m = fl(succ_char, sc_at_m, m)
    fa_y_at_m = Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m)))
    got_fa_y_m = mp(got_sc_m, ax(In(m, w)), In(m, w), fa_y_at_m)
    # [succ_char, In(m,w)] |- forall y. Iff(Apply(sf,m,y), Succ(y,m))

    # Instantiate at sm: Iff(Apply(sf,m,sm), Succ(sm,m))
    iff_m_sm = Iff(Apply(sfv, m, sm), SuccDef(sm, m))
    got_iff_m = apply_thm(got_fa_y_m, [sm], concl=iff_m_sm)
    # backward: Succ(sm,m) -> Apply(sf,m,sm)
    got_app_m = mp(iff_mp_rev(Apply(sfv, m, sm), SuccDef(sm, m), []),
        got_iff_m, iff_m_sm, Implies(SuccDef(sm, m), Apply(sfv, m, sm)))
    got_app_m = mp(got_app_m, ax(SuccDef(sm, m)), SuccDef(sm, m), Apply(sfv, m, sm))
    # [succ_char, In(m,w), Succ(sm,m)] |- Apply(sf,m,sm)

    # eir sm -> exists z. Apply(sf,m,z):
    zfa2 = Var()
    got_ex_app_m = eir(got_app_m, Apply(sfv, m, zfa2), zfa2, sm)
    # eel sm from Succ(sm,m):
    got_ex_app_m = eel(got_ex_app_m, SuccDef(sm, m), sm)
    # cut with got_se:
    got_ex_app_m = cut(got_ex_app_m, got_ex_app_m.sequent.left[-1], got_se)
    f_at_a = Exists(zfa2, Apply(sfv, m, zfa2))
    # got_ex_app_m: [succ_char, In(m,w), Pairing] |- f_at_a

    # ran_f_closed: forall y,z. Apply(sf,y,z) -> exists q. Apply(sf,z,q)
    # From Apply(sf,y,z) + succ_char: need In(y,w) first.
    # But we proved in sf_props that Apply(sf,y,z) implies In(y,w) (from sf_char).
    # However sf_char is not available here — we only have succ_char + Function(sf).
    # Function(sf) includes dom(sf) info... no, Function is just Relation + single-valued.
    # We need dom_sub from Recursive, but that's circular.
    # Actually, for ran_f_closed, we need: Apply(sf,y,z) -> exists q. Apply(sf,z,q).
    # From succ_char: if In(y,w), then Apply(sf,y,z) -> Succ(z,y) -> z in w (omega_succ_closed)
    #   -> exists q with Succ(q,z) (successor_exists) -> Apply(sf,z,q) (succ_char backward).
    # But we need In(y,w). From the recursion theorem's dom_sub for h, h's values are in w.
    # Actually, the recursion theorem needs dom_closed as INPUT, not output.
    # We need to show: for ANY y with Apply(sf,y,z), there exists q with Apply(sf,z,q).
    # If y is not in w, Apply(sf,y,z) is false (sf only has pairs for elements of w,
    # from sf_char which is captured by Function(sf) + succ_char).
    # But we can't derive this from succ_char alone — succ_char only speaks about In(x,w).
    # For y not in w, succ_char says nothing about Apply(sf,y,z).
    # However, if Apply(sf,y,z) is true and y not in w, then from sf's construction,
    # this can't happen (sf only has pairs <x,S(x)> for x in w).
    # But succ_char doesn't capture this — it's only the forward/backward for x in w.
    # We need to derive In(y,w) from Apply(sf,y,z).
    # This is the dom_sub property of sf: Apply(sf,y,z) -> In(y,w).
    # We proved this inside sf_props (the single-valued section).
    # But sf_props doesn't export it as a separate result.
    # Solution: use the full sf characterization. sf_props gives succ_char + Function(sf).
    # Function(sf) doesn't directly give dom_sub.
    # BUT: succ_char says In(x,w) -> forall y. Iff(Apply(sf,x,y), Succ(y,x)).
    # The BACKWARD direction says: if In(x,w) and Succ(y,x), then Apply(sf,x,y).
    # The FORWARD direction says: if In(x,w) and Apply(sf,x,y), then Succ(y,x).
    # Neither says: Apply(sf,x,y) -> In(x,w).
    # So from succ_char + Function alone, we CANNOT derive dom_sub.
    # We need dom_sub from sf_char, which is inside sf_props but not exported.

    # Options:
    # A) Add dom_sub to sf_props output: And(succ_char, And(Function(sf), dom_sub_sf))
    # B) Add a separate sf_dom_sub theorem
    # C) Restructure to pass sf_char through

    # Option A is cleanest. Let me modify sf_props to include dom_sub.
    # For now, let me just note this and come back to fix sf_props.

    # Actually wait — the recursion theorem's hypothesis is:
    # Function(f) -> And(f_at_a, ran_f_closed) -> Omega(w) -> exists! h. Recursive(h,a,f,w)
    # ran_f_closed = forall y,z. Apply(f,y,z) -> exists q. Apply(f,z,q)
    # This is about the RANGE being in the domain.
    # For sf: Apply(sf,y,z) means z=S(y). Then Apply(sf,z,q) means q=S(z)=S(S(y)).
    # We need z=S(y) to be in w (so we can use succ_char backward to get Apply(sf,z,q)).
    # z=S(y) is in w iff y is in w (omega is inductive).
    # And y is in w iff Apply(sf,y,z) implies y in w (dom_sub).
    # Circular without dom_sub!

    # So I DO need dom_sub in sf_props. Let me fix sf_props to output it too.
    raise NotImplementedError('plus_zero_right: need dom_sub from sf_props')


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
