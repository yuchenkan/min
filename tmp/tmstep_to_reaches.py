"""tmstep_to_reaches: TMStep(d,c1,c2) + Num(z,0) + Successor(one,z) → TMReaches(d,c1,one,c2)

Build a 2-entry trace {z→c1, one→c2}. Prove base, step_valid, reached.
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty, Singleton
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, eq_reflexive, eq_symmetric,
    iff_mp, iff_mp_rev, unique_empty)
from theorems.sets import ordpair_exists, singleton_exists
from theorems.omega import func_unique_thm
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
from theorems.tm import phase1_step_extend_trace


def tmstep_to_reaches():
    """Pairing,Union,Separation,Infinity |- ∀d,c1,c2,z,one,w.
        TMStep(d,c1,c2) → Num(z,0) → Successor(one,z) → Omega(w) → In(z,w) →
        TMReaches(d,c1,one,c2)

    Builds 2-entry trace via phase1_step_extend_trace on singleton {z→c1}.
    Omega+In(z,w) needed for the extend_trace anti-reflexivity check."""
    d=Var(postfix='d');c1=Var(postfix='c1');c2=Var(postfix='c2')
    z=Var(postfix='z');one=Var(postfix='one');w=Var(postfix='w')
    tmstep_f=TMStep(d,c1,c2);num_z=Num(z,0);succ_oz=Successor(one,z)
    omega_w=Omega(w);in_z_w=In(z,w)

    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    # Build singleton trace {z→c1}: Function, Apply(tra,z,c1), base_cond, dom_bound, step_valid
    pair_zc1=Var(postfix='pzc');tra=Var(postfix='tra')
    op_pair=OrdPair(pair_zc1,z,c1);sing_t=Singleton(tra,pair_zc1)
    got_ex_pair=apply_thm(ordpair_exists(),[z,c1],concl=Exists(pair_zc1,op_pair))

    sif=singleton_is_function()
    got_func=apply_thm(sif,[pair_zc1,z,c1,tra])
    got_func=mp(got_func,ax(op_pair),op_pair,got_func.sequent.right[0].right)
    got_func=mp(got_func,ax(sing_t),sing_t,FuncDef(tra))

    # Apply(tra,z,c1)
    iff_is=Iff(In(pair_zc1,tra),Eq(pair_zc1,pair_zc1))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc1],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc1])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc1,tra),Eq(pair_zc1,pair_zc1),[]),[],
        iff_is,Implies(Eq(pair_zc1,pair_zc1),In(pair_zc1,tra)),got_iff_s),
        got_epp,Eq(pair_zc1,pair_zc1),In(pair_zc1,tra))
    got_app_z=eir(mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc1,tra)),pair_zc1,pair_zc1)

    # base_cond(tra,c1): ∀zp. Empty(zp)→Apply(tra,zp,c1)
    zp=Var(postfix='_zp')
    ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[tra,z,zp,c1])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(tra,z,c1),Apply(tra,zp,c1)))
    got_azp=mp(got_azp,got_app_z,Apply(tra,z,c1),Apply(tra,zp,c1))
    imp_bc=Implies(Empty(zp),Apply(tra,zp,c1));lbc=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lbc,[imp_bc]),'implies_right',[got_azp],principal=imp_bc)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_bc)]),'forall_right',[got_bc],principal=Forall(zp,imp_bc),term=zp)

    # dom_bound(tra,z): ∀xd,yd. Apply(tra,xd,yd)→Or(In(xd,z),Eq(xd,z))
    xd=Var(postfix='_xd');yd=Var(postfix='_yd')
    sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c1,pair_zc1,tra,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(tra,xd,yd)),Apply(tra,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c1,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(tra,xd,yd),or_xdz);ldb=[f for f in got_orx.sequent.left if not same(f,Apply(tra,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)

    # step_valid(tra,z): vacuous
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(tra,_k,_ck),Exists(_ck1,And(Apply(tra,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz);imp_sv=Implies(In(_k,z),sv_inner)
    lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Now extend trace with {one→c2} via phase1_step_extend_trace
    # phase1_step_extend_trace: ∀tra2,ska,cn_new,c0,ka,delta,ca,w2.
    #   Function(tra2)→dom_bound(tra2,ka)→Omega(w2)→In(ka,w2)→Succ(ska,ka)→
    #   base_cond(tra2,c0)→step_valid(tra2,ka)→TMStep(delta,ca,cn_new)→Apply(tra2,ka,ca)→
    #   ∃trn. And(Function(trn),And(dom_bound(trn,ska),And(base_cond(trn,c0),And(Apply(trn,ska,cn_new),step_valid(trn,ska)))))
    _pet=phase1_step_extend_trace()
    got_ext=apply_thm(_pet,[tra,one,c2,c1,z,d,c1,w])
    got_ext=mp(got_ext,got_func,FuncDef(tra),got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_db,got_db.sequent.right[0],got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(omega_w),omega_w,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(in_z_w),in_z_w,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(succ_oz),succ_oz,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_bc,got_bc.sequent.right[0],got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_sv,got_sv.sequent.right[0],got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(tmstep_f),tmstep_f,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_app_z,Apply(tra,z,c1),got_ext.sequent.right[0].right)
    # ∃trn. And(Function(trn), And(dom_bound(trn,one), And(base_cond(trn,c1), And(Apply(trn,one,c2), step_valid(trn,one)))))
    print(f'extend done: {str(got_ext.sequent.right[0])[:80]}')

    # Extract components from ∃trn, build TMReaches(d,c1,one,c2)
    ext_ex=got_ext.sequent.right[0]; trn=ext_ex.var; ext_body=ext_ex.body
    # ext_body = And(Func(trn), And(db(trn,one), And(bc(trn,c1), And(Apply(trn,one,c2), sv(trn,one)))))
    e0=ext_body
    # skip Function and dom_bound, extract base_cond, Apply, step_valid
    gb1=apply_thm(and_elim_right(e0.left,e0.right,[]),[],e0,e0.right,ax(e0))
    e1=e0.right
    gb2=apply_thm(and_elim_right(e1.left,e1.right,[]),[],e1,e1.right,gb1)
    e2=e1.right  # And(base_cond, And(Apply, step_valid))
    g_bc=apply_thm(and_elim_left(e2.left,e2.right,[]),[],e2,e2.left,gb2)
    e3=e2.right  # And(Apply(trn,one,c2), step_valid(trn,one))
    gb3=apply_thm(and_elim_right(e2.left,e3,[]),[],e2,e3,gb2)
    g_app=apply_thm(and_elim_left(e3.left,e3.right,[]),[],e3,e3.left,gb3)
    g_sv=apply_thm(and_elim_right(e3.left,e3.right,[]),[],e3,e3.right,gb3)

    # TMReaches(d,c1,one,c2).expand() = ∃trace. And(base, And(step, reached))
    reaches=TMReaches(d,c1,one,c2)
    rexp=reaches.expand(); r_tra=rexp.var; r_body=rexp.body
    # r_body = And(base_r, And(step_r, reached_r))
    # base_r = ∀z'. Empty(z')→Apply(r_tra,z',c1) — matches g_bc with tra=trn
    # step_r = ∀k... — matches g_sv with tra=trn
    # reached_r = Apply(r_tra,one,c2) — matches g_app with tra=trn
    # Assemble: And(base, And(step, reached)) with trn as witness
    r_and=mk_and(g_sv,g_app); r_and=mk_and(g_bc,r_and)
    # eir r_tra=trn into TMReaches body
    got_reaches=eir(r_and,r_body,r_tra,trn)
    got_reaches=cut(ax(reaches),reaches,got_reaches)
    print(f'TMReaches cut: {same(got_reaches.sequent.right[0],reaches,expand=False)}')

    # eel trn from ext_body, cut with got_ext
    got_reaches=eel(got_reaches,ext_body,trn)
    got_reaches=cut(got_reaches,ext_ex,got_ext)
    # eel singleton eigenvars
    got_es=apply_thm(singleton_exists(),[pair_zc1],concl=Exists(tra,sing_t))
    got_reaches=eel(got_reaches,sing_t,tra);got_reaches=cut(got_reaches,Exists(tra,sing_t),got_es)
    got_reaches=eel(got_reaches,op_pair,pair_zc1);got_reaches=cut(got_reaches,Exists(pair_zc1,op_pair),got_ex_pair)

    # Discharge + ∀-close
    for hyp in [in_z_w, omega_w, succ_oz, num_z, tmstep_f]:
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [w,one,z,c2,c1,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)

    got_reaches.name='tmstep_to_reaches'
    return got_reaches


if __name__ == '__main__':
    p = tmstep_to_reaches()
    print(f'tmstep_to_reaches: OK')
    print(f'  Right: {str(p.sequent.right[0])[:100]}')
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'  Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
