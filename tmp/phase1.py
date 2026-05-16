"""Phase1P proof split into sub-theorems.

phase1_base(): proves P(z) from [Num(z,0), TMConfig(c0,q0,z,tape), ZFC]
phase1_step_case(): proves Or(In(sn,a),Eq(sn,a)) → P(n) → P(sn) from hypotheses
phase1(): omega induction combining base + step → Phase1P
"""
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
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty)
from theorems.sets import (eq_transfer, ordpair_exists,
    omega_transitive_set as ots_fn, singleton_exists)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
import core.zfc as zfc


# Shared P(n) definition — all phase1 sub-theorems use these same Var objects
d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
a=Var(postfix='a');tape=Var(postfix='tape');c0=Var(postfix='c0')
w=Var(postfix='w');one=Var(postfix='one');b=Var(postfix='b')
trace=Var(postfix='tra');cn=Var(postfix='cn')
k=Var(postfix='k');sk=Var(postfix='sk');ck=Var(postfix='ck');ck1=Var(postfix='ck1')
zp=Var(postfix='zp');xd=Var(postfix='xd');yd=Var(postfix='yd')

def base_cond(tr): return Forall(zp, Implies(Empty(zp), Apply(tr, zp, c0)))
def dom_bound(tr, nn): return Forall(xd, Forall(yd, Implies(Apply(tr, xd, yd), Or(In(xd, nn), Eq(xd, nn)))))
def step_valid(tr, nn): return Forall(k, Implies(In(k, nn), Forall(sk, Implies(Successor(sk, k), Forall(ck, Implies(Apply(tr, k, ck), Exists(ck1, And(Apply(tr, sk, ck1), TMStep(d, ck, ck1)))))))))
def P(nn): return Exists(trace, Exists(cn, And(FuncDef(trace), And(dom_bound(trace, nn), And(base_cond(trace), And(TMConfig(cn, q0, nn, tape), And(Apply(trace, nn, cn), step_valid(trace, nn))))))))


def mk_and(gl, gr):
    L, R = gl.sequent.right[0], gr.sequent.right[0]
    return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))


def phase1_base():
    """Prove P(z) from [Num(z,0), TMConfig(c0,q0,z,tape), Pairing].
    |- ∀d,q0,z,tape,c0. Num(z,0) → TMConfig(c0,q0,z,tape) → P(z)"""
    num_z = Num(z, 0); cfg_c0 = TMConfig(c0, q0, z, tape)

    # Singleton trace {z→c0}
    pair_zc0 = Var(postfix='pzc'); t_sing = Var(postfix='ts')
    op_pair = OrdPair(pair_zc0, z, c0); sing_t = Singleton(t_sing, pair_zc0)
    oe = ordpair_exists(); got_ex_pair = apply_thm(oe, [z, c0], concl=Exists(pair_zc0, op_pair))

    # Function(t_sing)
    sif = singleton_is_function()
    got_func_s = apply_thm(sif, [pair_zc0, z, c0, t_sing])
    got_func_s = mp(got_func_s, ax(op_pair), op_pair, got_func_s.sequent.right[0].right)
    got_func_s = mp(got_func_s, ax(sing_t), sing_t, FuncDef(t_sing))

    # Apply(t_sing, z, c0)
    iff_is = Iff(In(pair_zc0, t_sing), Eq(pair_zc0, pair_zc0))
    got_iff_s = apply_thm(ax(sing_t), [pair_zc0], concl=iff_is)
    got_epp = apply_thm(eq_reflexive(), [pair_zc0])
    got_inp = mp(apply_thm(iff_mp_rev(In(pair_zc0, t_sing), Eq(pair_zc0, pair_zc0), []),
        [], iff_is, Implies(Eq(pair_zc0, pair_zc0), In(pair_zc0, t_sing)), got_iff_s),
        got_epp, Eq(pair_zc0, pair_zc0), In(pair_zc0, t_sing))
    got_app_s = eir(mk_and(ax(op_pair), got_inp),
        And(OrdPair(pair_zc0, z, c0), In(pair_zc0, t_sing)), pair_zc0, pair_zc0)

    # base_cond(t_sing)
    ue = unique_empty(); es = eq_symmetric(); eat = eq_apply_transfer()
    got_ezz = apply_thm(ue, [zp], Empty(zp), Forall(z, Implies(num_z, Eq(zp, z))), ax(Empty(zp)))
    got_ezz = apply_thm(got_ezz, [z], num_z, Eq(zp, z), ax(num_z))
    got_ezzp = apply_thm(es, [zp, z], Eq(zp, z), Eq(z, zp), got_ezz)
    got_azp = apply_thm(eat, [t_sing, z, zp, c0])
    got_azp = mp(got_azp, got_ezzp, Eq(z, zp), Implies(Apply(t_sing, z, c0), Apply(t_sing, zp, c0)))
    got_azp = mp(got_azp, got_app_s, Apply(t_sing, z, c0), Apply(t_sing, zp, c0))
    imp_b = Implies(Empty(zp), Apply(t_sing, zp, c0))
    lb = [f for f in got_azp.sequent.left if not same(f, Empty(zp))]
    got_bc = Proof(Sequent(lb, [imp_b]), 'implies_right', [got_azp], principal=imp_b)
    got_bc = Proof(Sequent(got_bc.sequent.left, [Forall(zp, imp_b)]),
        'forall_right', [got_bc], principal=Forall(zp, imp_b), term=zp)

    # dom_bound(t_sing, z): singleton_apply_eq gives Eq(z,xd) → Or right
    sae = singleton_apply_eq()
    got_sae = apply_thm(sae, [z, c0, pair_zc0, t_sing, xd, yd])
    got_sae = mp(got_sae, ax(op_pair), op_pair, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(sing_t), sing_t, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(Apply(t_sing, xd, yd)), Apply(t_sing, xd, yd), got_sae.sequent.right[0].right)
    got_ezxd = apply_thm(and_elim_left(Eq(z, xd), Eq(c0, yd), []), [],
        got_sae.sequent.right[0], Eq(z, xd), got_sae)
    got_exdz = apply_thm(es, [z, xd], Eq(z, xd), Eq(xd, z), got_ezxd)
    or_xdz = Or(In(xd, z), Eq(xd, z))
    got_orx = apply_thm(or_intro_right(In(xd, z), Eq(xd, z), []), [], Eq(xd, z), or_xdz, got_exdz)
    imp_db = Implies(Apply(t_sing, xd, yd), or_xdz)
    ldb = [f for f in got_orx.sequent.left if not same(f, Apply(t_sing, xd, yd))]
    got_db = Proof(Sequent(ldb, [imp_db]), 'implies_right', [got_orx], principal=imp_db)
    got_db = Proof(Sequent(got_db.sequent.left, [Forall(yd, imp_db)]),
        'forall_right', [got_db], principal=Forall(yd, imp_db), term=yd)
    got_db = Proof(Sequent(got_db.sequent.left, [Forall(xd, Forall(yd, imp_db))]),
        'forall_right', [got_db], principal=Forall(xd, Forall(yd, imp_db)), term=xd)

    # step_valid(t_sing, z): vacuous
    got_nkz = apply_thm(ax(num_z), [k])
    sv_inner = Forall(sk, Implies(Successor(sk, k), Forall(ck, Implies(Apply(t_sing, k, ck),
        Exists(ck1, And(Apply(t_sing, sk, ck1), TMStep(d, ck, ck1)))))))
    nkz = Not(In(k, z))
    gb = Proof(Sequent([In(k, z), nkz], []), 'not_left', [ax(In(k, z))], principal=nkz)
    gb = Proof(Sequent(gb.sequent.left, [sv_inner]), 'weakening_right', [gb], principal=sv_inner)
    gb = cut(gb, nkz, got_nkz)
    imp_sv = Implies(In(k, z), sv_inner)
    lsv = [f for f in gb.sequent.left if not same(f, In(k, z))]
    got_sv = Proof(Sequent(lsv, [imp_sv]), 'implies_right', [gb], principal=imp_sv)
    got_sv = Proof(Sequent(got_sv.sequent.left, [Forall(k, imp_sv)]),
        'forall_right', [got_sv], principal=Forall(k, imp_sv), term=k)

    # Assemble P(z)
    pza = mk_and(got_app_s, got_sv)
    pza = mk_and(ax(cfg_c0), pza)
    pza = mk_and(got_bc, pza)
    pza = mk_and(got_db, pza)
    pza = mk_and(got_func_s, pza)

    # eir cn=c0, trace=t_sing
    bfc = And(FuncDef(t_sing), And(dom_bound(t_sing, z), And(base_cond(t_sing),
        And(TMConfig(cn, q0, z, tape), And(Apply(t_sing, z, cn), step_valid(t_sing, z))))))
    got_ecn = eir(pza, bfc, cn, c0)
    got_etr = eir(got_ecn, P(z).body, trace, t_sing)
    assert same(got_etr.sequent.right[0], P(z)), 'P(z) mismatch'

    # eel singleton eigenvars
    se2 = singleton_exists()
    got_es = apply_thm(se2, [pair_zc0], concl=Exists(t_sing, sing_t))
    got_etr = eel(got_etr, sing_t, t_sing)
    got_etr = cut(got_etr, Exists(t_sing, sing_t), got_es)
    got_etr = eel(got_etr, op_pair, pair_zc0)
    got_etr = cut(got_etr, Exists(pair_zc0, op_pair), got_ex_pair)

    proof = got_etr
    proof.name = 'phase1_base'
    return proof


def phase1_step_case():
    """Prove P(n) → P(sn) given In(n,a) and hypotheses.
    Left: [P(n), In(n,a), Succ(sn,n), TMTransition, Omega, In(a,w), In(n,w),
           Function(d), Function(tape), Num(one,1), UnaryTape, ZFC]
    Right: P(sn)"""
    n = Var(postfix='ind_n'); sn = Var(postfix='ind_sn')
    trans = TMTransition(d, q0, one, one, one, q0)
    omega_w = Omega(w); in_a_w = In(a, w)
    func_d = FuncDef(d); func_tape = FuncDef(tape)
    num_one = Num(one, 1); utape = UnaryTape(tape, a, b)
    succ_sn = Successor(sn, n)

    # Decompose P(n)
    pn = P(n); pntb = pn.body; pncb = pntb.body
    b0 = pncb
    gft = apply_thm(and_elim_left(b0.left, b0.right, []), [], b0, b0.left, ax(b0))
    b1 = b0.right; gb1 = apply_thm(and_elim_right(b0.left, b1, []), [], b0, b1, ax(b0))
    gdb = apply_thm(and_elim_left(b1.left, b1.right, []), [], b1, b1.left, gb1)
    b2 = b1.right; gb2 = apply_thm(and_elim_right(b1.left, b2, []), [], b1, b2, gb1)
    gbt = apply_thm(and_elim_left(b2.left, b2.right, []), [], b2, b2.left, gb2)
    b3 = b2.right; gb3 = apply_thm(and_elim_right(b2.left, b3, []), [], b2, b3, gb2)
    gcn = apply_thm(and_elim_left(b3.left, b3.right, []), [], b3, b3.left, gb3)
    b4 = b3.right; gb4 = apply_thm(and_elim_right(b3.left, b4, []), [], b3, b4, gb3)
    gatn = apply_thm(and_elim_left(b4.left, b4.right, []), [], b4, b4.left, gb4)
    gsvn = apply_thm(and_elim_right(b4.left, b4.right, []), [], b4, b4.right, gb4)

    # tape_read_low: In(n,a) → Apply(tape,n,one)
    _trl = tape_read_low()
    gat = apply_thm(_trl, [tape, a, b, n, one])
    gat = mp(gat, ax(utape), utape, gat.sequent.right[0].right)
    gat = mp(gat, ax(In(n, a)), In(n, a), gat.sequent.right[0].right)
    gat = mp(gat, ax(num_one), num_one, Apply(tape, n, one))

    # phase1_step_tmstep: ∃cn_new. And(TMConfig(cn_new,q0,sn,tape), TMStep(d,cn,cn_new))
    _pst = phase1_step_tmstep()
    gts = apply_thm(_pst, [d, q0, n, sn, tape, cn, one, one])
    gts = mp(gts, ax(func_d), func_d, gts.sequent.right[0].right)
    gts = mp(gts, ax(trans), trans, gts.sequent.right[0].right)
    gts = mp(gts, gcn, gcn.sequent.right[0], gts.sequent.right[0].right)
    gts = mp(gts, ax(func_tape), func_tape, gts.sequent.right[0].right)
    gts = mp(gts, gat, Apply(tape, n, one), gts.sequent.right[0].right)
    gts = mp(gts, ax(num_one), num_one, gts.sequent.right[0].right)
    gts = mp(gts, ax(succ_sn), succ_sn, gts.sequent.right[0].right)

    # Open ∃cn_new
    tsx = gts.sequent.right[0]; cnw = tsx.var; tsb = tsx.body
    gcfn = apply_thm(and_elim_left(tsb.left, tsb.right, []), [], tsb, tsb.left, ax(tsb))
    gstn = apply_thm(and_elim_right(tsb.left, tsb.right, []), [], tsb, tsb.right, ax(tsb))

    # phase1_step_extend_trace
    from theorems.omega import omega_succ_closed
    osc = omega_succ_closed()
    # Need In(n,w) for extend_trace
    got_in_nw = ax(In(n, w))

    _pet = phase1_step_extend_trace()
    gext = apply_thm(_pet, [trace, sn, cnw, c0, n, d, cn, w])
    gext = mp(gext, gft, gft.sequent.right[0], gext.sequent.right[0].right)
    gext = mp(gext, gdb, gdb.sequent.right[0], gext.sequent.right[0].right)
    gext = mp(gext, ax(omega_w), omega_w, gext.sequent.right[0].right)
    gext = mp(gext, got_in_nw, In(n, w), gext.sequent.right[0].right)
    gext = mp(gext, ax(succ_sn), succ_sn, gext.sequent.right[0].right)
    gext = mp(gext, gbt, gbt.sequent.right[0], gext.sequent.right[0].right)
    gext = mp(gext, gsvn, gsvn.sequent.right[0], gext.sequent.right[0].right)
    gext = mp(gext, gstn, gstn.sequent.right[0], gext.sequent.right[0].right)
    gext = mp(gext, gatn, gatn.sequent.right[0], gext.sequent.right[0].right)

    # Open ∃trn, decompose, insert TMConfig, reassemble P(sn)
    extx = gext.sequent.right[0]; trn = extx.var; extb = extx.body
    e0 = extb
    gef = apply_thm(and_elim_left(e0.left, e0.right, []), [], e0, e0.left, ax(e0))
    e1 = e0.right; ge1 = apply_thm(and_elim_right(e0.left, e1, []), [], e0, e1, ax(e0))
    gedb = apply_thm(and_elim_left(e1.left, e1.right, []), [], e1, e1.left, ge1)
    e2 = e1.right; ge2 = apply_thm(and_elim_right(e1.left, e2, []), [], e1, e2, ge1)
    gebc = apply_thm(and_elim_left(e2.left, e2.right, []), [], e2, e2.left, ge2)
    e3 = e2.right; ge3 = apply_thm(and_elim_right(e2.left, e3, []), [], e2, e3, ge2)
    geap = apply_thm(and_elim_left(e3.left, e3.right, []), [], e3, e3.left, ge3)
    gesv = apply_thm(and_elim_right(e3.left, e3.right, []), [], e3, e3.right, ge3)

    # Reassemble with TMConfig inserted
    psna = mk_and(geap, gesv)
    psna = mk_and(gcfn, psna)
    psna = mk_and(gebc, psna)
    psna = mk_and(gedb, psna)
    psna = mk_and(gef, psna)

    # eir cn=cnw, trace=trn → P(sn)
    bfcn = And(FuncDef(trn), And(dom_bound(trn, sn), And(base_cond(trn),
        And(TMConfig(cn, q0, sn, tape), And(Apply(trn, sn, cn), step_valid(trn, sn))))))
    got_ecn2 = eir(psna, bfcn, cn, cnw)
    got_etr2 = eir(got_ecn2, P(sn).body, trace, trn)
    assert same(got_etr2.sequent.right[0], P(sn)), 'P(sn) mismatch'

    # eel eigenvars: trn from extb, cnw from tsb, cn and trace from P(n)
    got_etr2 = eel(got_etr2, extb, trn)
    got_etr2 = cut(got_etr2, extx, gext)
    got_etr2 = eel(got_etr2, tsb, cnw)
    got_etr2 = cut(got_etr2, tsx, gts)
    got_etr2 = eel(got_etr2, pncb, cn)
    # After eel cn: left has Exists(cn, pncb) = pntb. Now eel trace:
    got_etr2 = eel(got_etr2, pntb, trace)
    # After eel trace: left has Exists(trace, pntb) = P(n). Cut with ax(P(n)):
    got_etr2 = cut(got_etr2, pn, ax(pn))

    proof = got_etr2
    proof.name = 'phase1_step_case'
    return proof


if __name__ == '__main__':
    print('=== phase1_base ===')
    p = phase1_base()
    print(f'  OK, same(P(z))? {same(p.sequent.right[0], P(z))}')

    print('=== phase1_step_case ===')
    p2 = phase1_step_case()
    # P(sn) uses the sn Var from inside the function. Check structurally:
    r = p2.sequent.right[0]
    print(f'  Right: {str(r)[:80]}')
    print(f'  Is Exists? {type(r).__name__}')
    print(f'  Left ({len(p2.sequent.left)}):')
    for f in p2.sequent.left:
        print(f'    {str(f)[:60]}')
