"""Phase3P proof — omega induction scanning past b ones in second group.

Like Phase1P but head starts at sa, position tracked via Plus(sa,j,pos_j).
Tape read via Phase3P's hypothesis: ∀p∈b.∀pp.Plus(sa,p,pp)→Apply(tape2,pp,one).
Same transition as Phase1P: q1,one→one,one(right),q1.
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.recursion import Plus as PlusDef
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists, singleton_exists,
    omega_transitive_set as ots_fn)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import (Phase3P, phase1_step_tmstep, phase1_step_extend_trace,
    config_exists)
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
from theorems.arithmetic import plus_zero_exists, plus_succ_right, plus_val_in_omega
import core.zfc as zfc


class Phase3Ind:
    """Strong induction predicate for Phase3 trace construction.
    Phase3Ind(n, d, q1, sa, tape2, c1) =
      ∃pos_n. Plus(sa,n,pos_n) ∧
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c1) ∧
                 TMConfig(cn,q1,pos_n,tape2) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n','d','q1','sa','tape2','c1')
    def __init__(self, n, d, q1, sa, tape2, c1):
        self.n=n;self.d=d;self.q1=q1;self.sa=sa;self.tape2=tape2;self.c1=c1
    def expand(self):
        pos_n=Var(postfix='_pn');tra=Var(postfix='_tra');cn=Var(postfix='_cn')
        k=Var(postfix='_k');sk=Var(postfix='_sk');ck=Var(postfix='_ck');ck1=Var(postfix='_ck1')
        zp=Var(postfix='_zp');xd=Var(postfix='_xd');yd=Var(postfix='_yd')
        base_cond=Forall(zp,Implies(Empty(zp),Apply(tra,zp,self.c1)))
        dom_bound=Forall(xd,Forall(yd,Implies(Apply(tra,xd,yd),Or(In(xd,self.n),Eq(xd,self.n)))))
        step_valid=Forall(k,Implies(In(k,self.n),Forall(sk,Implies(Successor(sk,k),
            Forall(ck,Implies(Apply(tra,k,ck),Exists(ck1,And(Apply(tra,sk,ck1),TMStep(self.d,ck,ck1)))))))))
        inner=Exists(tra,Exists(cn,And(FuncDef(tra),And(dom_bound,And(base_cond,
            And(TMConfig(cn,self.q1,pos_n,self.tape2),And(Apply(tra,self.n,cn),step_valid)))))))
        return Exists(pos_n,And(PlusDef(self.sa,self.n,pos_n),inner))
    def subst(self,old,new):
        r=lambda f:new if f is old else f
        return Phase3Ind(r(self.n),r(self.d),r(self.q1),r(self.sa),r(self.tape2),r(self.c1))
    def __str__(self):
        return f'P3Ind({self.n})'


if __name__=='__main__':
    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    tape2=Var(postfix='t2');c1=Var(postfix='c1');z=Var(postfix='z');n=Var(postfix='n')
    p=Phase3Ind(z,d,q1,sa,tape2,c1)
    print(f'Phase3Ind(z,...): {p}')
    print(f'  expand: {str(p.expand())[:120]}')
    print(f'  same(self,self)? {same(p,p)}')


def phase3_base():
    """Pairing |- ∀d,q1,sa,tape2,c1,z,w.
        Num(z,0) → Omega(w) → In(sa,w) →
        TMConfig(c1,q1,sa,tape2) → Phase3Ind(z,d,q1,sa,tape2,c1)"""
    from core.proof import Proof, Sequent, same, _subst
    from vocab.sets import Singleton

    def mk_and(gl,gr):
        L,R=gl.sequent.right[0],gr.sequent.right[0]
        return mp(apply_thm(and_intro(L,R,[]),[],L,Implies(R,And(L,R)),gl),gr,R,And(L,R))

    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    tape2=Var(postfix='t2');c1=Var(postfix='c1');z=Var(postfix='z');w=Var(postfix='w')
    num_z=Num(z,0);omega_w=Omega(w);in_sa_w=In(sa,w)
    cfg_c1=TMConfig(c1,q1,sa,tape2)
    goal=Phase3Ind(z,d,q1,sa,tape2,c1)

    # Plus(sa,z,sa) from plus_zero_exists
    _pze=plus_zero_exists()
    got_plus=apply_thm(_pze,[w,sa,z])
    got_plus=mp(got_plus,ax(omega_w),omega_w,got_plus.sequent.right[0].right)
    got_plus=mp(got_plus,ax(in_sa_w),in_sa_w,got_plus.sequent.right[0].right)
    got_plus=mp(got_plus,ax(num_z),num_z,got_plus.sequent.right[0].right)
    # |- Plus(sa,z,sa)

    # Singleton trace {z→c1} — same as phase1_base
    pair_zc1=Var(postfix='pzc');t_sing=Var(postfix='ts')
    op_pair=OrdPair(pair_zc1,z,c1);sing_t=Singleton(t_sing,pair_zc1)
    got_ex_pair=apply_thm(ordpair_exists(),[z,c1],concl=Exists(pair_zc1,op_pair))
    sif=singleton_is_function()
    got_func_s=apply_thm(sif,[pair_zc1,z,c1,t_sing])
    got_func_s=mp(got_func_s,ax(op_pair),op_pair,got_func_s.sequent.right[0].right)
    got_func_s=mp(got_func_s,ax(sing_t),sing_t,FuncDef(t_sing))
    # Apply(t_sing,z,c1)
    iff_is=Iff(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc1],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc1])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1),[]),[],
        iff_is,Implies(Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing))
    got_app_s=eir(mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc1,t_sing)),pair_zc1,pair_zc1)
    # base_cond, dom_bound, step_valid — identical to phase1_base
    zp=Var(postfix='_zp');ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[t_sing,z,zp,c1])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(t_sing,z,c1),Apply(t_sing,zp,c1)))
    got_azp=mp(got_azp,got_app_s,Apply(t_sing,z,c1),Apply(t_sing,zp,c1))
    imp_bc=Implies(Empty(zp),Apply(t_sing,zp,c1))
    lbc=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lbc,[imp_bc]),'implies_right',[got_azp],principal=imp_bc)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_bc)]),'forall_right',[got_bc],principal=Forall(zp,imp_bc),term=zp)
    # dom_bound
    xd=Var(postfix='_xd');yd=Var(postfix='_yd');sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c1,pair_zc1,t_sing,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,xd,yd)),Apply(t_sing,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c1,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,xd,yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)
    # step_valid — vacuous
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz);imp_sv=Implies(In(_k,z),sv_inner)
    lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Assemble Phase3Ind(z,...) = ∃pos_n. And(Plus(sa,z,pos_n), ∃tra,cn.(...))
    # Inner: And(Function, And(dom_bound, And(base_cond, And(TMConfig(cn,q1,sa,tape2), And(Apply,step_valid)))))
    pza=mk_and(got_app_s,got_sv);pza=mk_and(ax(cfg_c1),pza);pza=mk_and(got_bc,pza)
    pza=mk_and(got_db,pza);pza=mk_and(got_func_s,pza)
    # eir cn=c1, tra=t_sing into inner ∃
    exp=goal.expand()
    pos_n_var=exp.var  # ∃pos_n
    and_plus_inner=exp.body  # And(Plus(sa,z,pos_n), inner_exists)
    inner_exists=and_plus_inner.right  # ∃tra.∃cn.(...)
    tra_var=inner_exists.var
    inner_cn=inner_exists.body  # ∃cn.(...)
    cn_var=inner_cn.var
    inner_and=inner_cn.body  # And(Function(tra),...)
    # eir cn=c1 (body needs tra→t_sing and pos_n→sa substituted)
    body_cn=_subst(_subst(inner_and,tra_var,t_sing),pos_n_var,sa)
    got_ecn=eir(pza,body_cn,cn_var,c1)
    # eir tra=t_sing (inner_cn with pos_n→sa)
    inner_cn_sa=_subst(inner_cn,pos_n_var,sa)
    got_etr=eir(got_ecn,inner_cn_sa,tra_var,t_sing)
    # eir pos_n=sa: And(Plus(sa,z,pos_n), inner_exists)
    got_and_plus=mk_and(got_plus,got_etr)
    got_epos=eir(got_and_plus,and_plus_inner,pos_n_var,sa)
    assert same(got_epos.sequent.right[0],goal),'Phase3Ind(z) mismatch'
    # eel singleton eigenvars
    se2=singleton_exists();got_es2=apply_thm(se2,[pair_zc1],concl=Exists(t_sing,sing_t))
    got_epos=eel(got_epos,sing_t,t_sing);got_epos=cut(got_epos,Exists(t_sing,sing_t),got_es2)
    got_epos=eel(got_epos,op_pair,pair_zc1);got_epos=cut(got_epos,Exists(pair_zc1,op_pair),got_ex_pair)
    # Discharge + close
    for hyp in [cfg_c1,in_sa_w,omega_w,num_z]:
        got_epos=wl(got_epos,hyp);imp=Implies(hyp,got_epos.sequent.right[0])
        left=[f for f in got_epos.sequent.left if not same(f,hyp)]
        got_epos=Proof(Sequent(left,[imp]),'implies_right',[got_epos],principal=imp)
    for v in [w,z,c1,tape2,sa,q1,d]:
        body=got_epos.sequent.right[0];fa=Forall(v,body)
        got_epos=Proof(Sequent(got_epos.sequent.left,[fa]),'forall_right',[got_epos],principal=fa,term=v)
    got_epos.name='phase3_base'
    return got_epos


if __name__=='__main__':
    p=phase3_base()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'phase3_base: OK, non-ZFC={len(non)}')
