"""Phase1P proof — proper vocab, pure sub-theorems."""
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
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists,
    omega_transitive_set as ots_fn, singleton_exists)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
import core.zfc as zfc


class Phase1Ind:
    """Strong induction predicate for Phase1 trace construction.
    Phase1Ind(n, d, q0, tape, c0) =
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c0) ∧
                 TMConfig(cn,q0,n,tape) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n', 'd', 'q0', 'tape', 'c0')
    def __init__(self, n, d, q0, tape, c0):
        self.n = n; self.d = d; self.q0 = q0; self.tape = tape; self.c0 = c0
    def expand(self):
        tra = Var(postfix='_tra'); cn = Var(postfix='_cn')
        k = Var(postfix='_k'); sk = Var(postfix='_sk')
        ck = Var(postfix='_ck'); ck1 = Var(postfix='_ck1')
        zp = Var(postfix='_zp')
        xd = Var(postfix='_xd'); yd = Var(postfix='_yd')
        base_cond = Forall(zp, Implies(Empty(zp), Apply(tra, zp, self.c0)))
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.n), Eq(xd, self.n)))))
        step_valid = Forall(k, Implies(In(k, self.n),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tra, k, ck),
                    Exists(ck1, And(Apply(tra, sk, ck1), TMStep(self.d, ck, ck1)))))))))
        return Exists(tra, Exists(cn, And(FuncDef(tra),
            And(dom_bound,
            And(base_cond,
            And(TMConfig(cn, self.q0, self.n, self.tape),
            And(Apply(tra, self.n, cn),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Ind(r(self.n), r(self.d), r(self.q0), r(self.tape), r(self.c0))
    def __str__(self):
        return f'P1Ind({self.n},{self.d},{self.q0},{self.tape},{self.c0})'


def _mk_and(gl, gr):
    L, R = gl.sequent.right[0], gr.sequent.right[0]
    return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))


def phase1_base():
    """Pairing |- ∀d,q0,z,tape,c0. Num(z,0) → TMConfig(c0,q0,z,tape) → Phase1Ind(z,d,q0,tape,c0)"""
    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    num_z=Num(z,0);cfg_c0=TMConfig(c0,q0,z,tape)
    goal = Phase1Ind(z, d, q0, tape, c0)

    # Build singleton trace {z→c0}
    pair_zc0=Var(postfix='pzc');t_sing=Var(postfix='ts')
    op_pair=OrdPair(pair_zc0,z,c0);sing_t=Singleton(t_sing,pair_zc0)
    oe=ordpair_exists();got_ex_pair=apply_thm(oe,[z,c0],concl=Exists(pair_zc0,op_pair))
    sif=singleton_is_function()
    got_func_s=apply_thm(sif,[pair_zc0,z,c0,t_sing])
    got_func_s=mp(got_func_s,ax(op_pair),op_pair,got_func_s.sequent.right[0].right)
    got_func_s=mp(got_func_s,ax(sing_t),sing_t,FuncDef(t_sing))

    # Apply(t_sing,z,c0)
    iff_is=Iff(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc0],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc0])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0),[]),[],
        iff_is,Implies(Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing))
    got_app_s=eir(_mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc0,t_sing)),pair_zc0,pair_zc0)

    # base_cond: ∀zp. Empty(zp) → Apply(t_sing,zp,c0)
    zp=Var(postfix='_zp')
    ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[t_sing,z,zp,c0])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(t_sing,z,c0),Apply(t_sing,zp,c0)))
    got_azp=mp(got_azp,got_app_s,Apply(t_sing,z,c0),Apply(t_sing,zp,c0))
    imp_b=Implies(Empty(zp),Apply(t_sing,zp,c0))
    lb=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lb,[imp_b]),'implies_right',[got_azp],principal=imp_b)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_b)]),'forall_right',[got_bc],principal=Forall(zp,imp_b),term=zp)

    # dom_bound: ∀xd,yd. Apply(t_sing,xd,yd) → Or(In(xd,z),Eq(xd,z))
    xd=Var(postfix='_xd');yd=Var(postfix='_yd')
    sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c0,pair_zc0,t_sing,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,xd,yd)),Apply(t_sing,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c0,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,xd,yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)

    # step_valid: vacuous (∀k∈z=∅, impossible)
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz)
    imp_sv=Implies(In(_k,z),sv_inner);lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Assemble Phase1Ind(z,...) via And + eir
    pza=_mk_and(got_app_s,got_sv);pza=_mk_and(ax(cfg_c0),pza)
    pza=_mk_and(got_bc,pza);pza=_mk_and(got_db,pza);pza=_mk_and(got_func_s,pza)
    # eir: use goal.expand() structure
    exp = goal.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = exp.var; inner_ex = exp.body  # Exists(cn, And(...))
    cn_v = inner_ex.var; and_body = inner_ex.body  # And(Function(tra), And(db, ...))
    # pza has the And with t_sing and c0. eir cn_v=c0, tra_v=t_sing.
    # Body for cn eir: and_body with tra_v=t_sing (cn_v free)
    from core.proof import _subst
    body_cn = _subst(and_body, tra_v, t_sing)  # And with t_sing, cn_v still free
    got_ecn = eir(pza, body_cn, cn_v, c0)
    # Body for trace eir: inner_ex with tra_v free
    got_etr = eir(got_ecn, inner_ex, tra_v, t_sing)
    assert same(got_etr.sequent.right[0], goal), f'Phase1Ind(z) mismatch'

    # eel singleton eigenvars
    se2=singleton_exists();got_es=apply_thm(se2,[pair_zc0],concl=Exists(t_sing,sing_t))
    got_etr=eel(got_etr,sing_t,t_sing);got_etr=cut(got_etr,Exists(t_sing,sing_t),got_es)
    got_etr=eel(got_etr,op_pair,pair_zc0);got_etr=cut(got_etr,Exists(pair_zc0,op_pair),got_ex_pair)

    # Discharge + ∀-close
    for hyp in [cfg_c0, num_z]:
        got_etr=wl(got_etr,hyp);imp=Implies(hyp,got_etr.sequent.right[0])
        left=[f for f in got_etr.sequent.left if not same(f,hyp)]
        got_etr=Proof(Sequent(left,[imp]),'implies_right',[got_etr],principal=imp)
    for v in [c0,tape,z,q0,d]:
        body=got_etr.sequent.right[0];fa=Forall(v,body)
        got_etr=Proof(Sequent(got_etr.sequent.left,[fa]),'forall_right',[got_etr],principal=fa,term=v)
    got_etr.name='phase1_base'
    return got_etr


def phase1_step_case():
    """ZFC |- ∀d,q0,a,b,tape,c0,n,sn,w,one.
        TMTransition(d,q0,one,one,one,q0) → Omega(w) → In(a,w) → In(n,w) →
        Function(d) → Function(tape) → Num(one,1) → UnaryTape(tape,a,b) →
        Successor(sn,n) → In(n,a) → Phase1Ind(n,d,q0,tape,c0) → Phase1Ind(sn,d,q0,tape,c0)"""
    d=Var(postfix='d');q0=Var(postfix='q0');a=Var(postfix='a');b=Var(postfix='b')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    n=Var(postfix='n');sn=Var(postfix='sn');w=Var(postfix='w');one=Var(postfix='one')
    trans=TMTransition(d,q0,one,one,one,q0);omega_w=Omega(w);in_a_w=In(a,w)
    func_d=FuncDef(d);func_tape=FuncDef(tape);num_one=Num(one,1)
    utape=UnaryTape(tape,a,b);succ_sn=Successor(sn,n)
    pn=Phase1Ind(n,d,q0,tape,c0);psn=Phase1Ind(sn,d,q0,tape,c0)

    # Decompose Phase1Ind(n,...) by expanding
    pn_exp = pn.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = pn_exp.var; pn_inner = pn_exp.body
    cn_v = pn_inner.var; pn_and = pn_inner.body
    # pn_and = And(Func(tra), And(db(tra,n), And(bc(tra), And(TMConfig(cn,q0,n,tape), And(Apply(tra,n,cn), sv(tra,n))))))
    b0=pn_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    gdb=apply_thm(and_elim_left(b1.left,b1.right,[]),[],b1,b1.left,gb1)
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcn=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatn=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsvn=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)

    # tape_read_low: In(n,a) → Apply(tape,n,one)
    _trl=tape_read_low()
    gat=apply_thm(_trl,[tape,a,b,n,one])
    gat=mp(gat,ax(utape),utape,gat.sequent.right[0].right)
    gat=mp(gat,ax(In(n,a)),In(n,a),gat.sequent.right[0].right)
    gat=mp(gat,ax(num_one),num_one,Apply(tape,n,one))

    # phase1_step_tmstep: ∃cn_new. And(TMConfig(cn_new,q0,sn,tape), TMStep(d,cn,cn_new))
    _pst=phase1_step_tmstep()
    gts=apply_thm(_pst,[d,q0,n,sn,tape,cn_v,one,one])
    gts=mp(gts,ax(func_d),func_d,gts.sequent.right[0].right)
    gts=mp(gts,ax(trans),trans,gts.sequent.right[0].right)
    gts=mp(gts,gcn,gcn.sequent.right[0],gts.sequent.right[0].right)
    gts=mp(gts,ax(func_tape),func_tape,gts.sequent.right[0].right)
    gts=mp(gts,gat,Apply(tape,n,one),gts.sequent.right[0].right)
    gts=mp(gts,ax(num_one),num_one,gts.sequent.right[0].right)
    gts=mp(gts,ax(succ_sn),succ_sn,gts.sequent.right[0].right)

    # Open ∃cn_new
    tsx=gts.sequent.right[0];cnw=tsx.var;tsb=tsx.body
    gcfn=apply_thm(and_elim_left(tsb.left,tsb.right,[]),[],tsb,tsb.left,ax(tsb))
    gstn=apply_thm(and_elim_right(tsb.left,tsb.right,[]),[],tsb,tsb.right,ax(tsb))

    # phase1_step_extend_trace
    _pet=phase1_step_extend_trace()
    gext=apply_thm(_pet,[tra_v,sn,cnw,c0,n,d,cn_v,w])
    gext=mp(gext,gft,gft.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gdb,gdb.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,ax(omega_w),omega_w,gext.sequent.right[0].right)
    gext=mp(gext,ax(In(n,w)),In(n,w),gext.sequent.right[0].right)
    gext=mp(gext,ax(succ_sn),succ_sn,gext.sequent.right[0].right)
    gext=mp(gext,gbt,gbt.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gsvn,gsvn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gstn,gstn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gatn,gatn.sequent.right[0],gext.sequent.right[0].right)

    # Open ∃trn, decompose, insert TMConfig, reassemble Phase1Ind(sn,...)
    extx=gext.sequent.right[0];trn=extx.var;extb=extx.body
    e0=extb
    gef=apply_thm(and_elim_left(e0.left,e0.right,[]),[],e0,e0.left,ax(e0))
    e1=e0.right;ge1=apply_thm(and_elim_right(e0.left,e1,[]),[],e0,e1,ax(e0))
    gedb=apply_thm(and_elim_left(e1.left,e1.right,[]),[],e1,e1.left,ge1)
    e2=e1.right;ge2=apply_thm(and_elim_right(e1.left,e2,[]),[],e1,e2,ge1)
    gebc=apply_thm(and_elim_left(e2.left,e2.right,[]),[],e2,e2.left,ge2)
    e3=e2.right;ge3=apply_thm(and_elim_right(e2.left,e3,[]),[],e2,e3,ge2)
    geap=apply_thm(and_elim_left(e3.left,e3.right,[]),[],e3,e3.left,ge3)
    gesv=apply_thm(and_elim_right(e3.left,e3.right,[]),[],e3,e3.right,ge3)

    # Reassemble with TMConfig(cnw,q0,sn,tape) inserted
    psna=_mk_and(geap,gesv);psna=_mk_and(gcfn,psna);psna=_mk_and(gebc,psna)
    psna=_mk_and(gedb,psna);psna=_mk_and(gef,psna)

    # eir using psn.expand() structure
    psn_exp=psn.expand();psn_tra=psn_exp.var;psn_inner=psn_exp.body
    psn_cn=psn_inner.var;psn_and=psn_inner.body
    from core.proof import _subst
    body_cn2=_subst(psn_and,psn_tra,trn)
    got_ecn2=eir(psna,body_cn2,psn_cn,cnw)
    got_etr2=eir(got_ecn2,psn_inner,psn_tra,trn)
    assert same(got_etr2.sequent.right[0],psn),f'Phase1Ind(sn) mismatch'

    # eel eigenvars
    got_etr2=eel(got_etr2,extb,trn);got_etr2=cut(got_etr2,extx,gext)
    got_etr2=eel(got_etr2,tsb,cnw);got_etr2=cut(got_etr2,tsx,gts)
    got_etr2=eel(got_etr2,pn_and,cn_v);got_etr2=cut(got_etr2,pn_inner,ax(pn_inner))
    got_etr2=eel(got_etr2,pn_inner,tra_v);got_etr2=cut(got_etr2,pn_exp,ax(pn))

    # Discharge + ∀-close
    hyps=[pn,In(n,a),succ_sn,num_one,utape,func_tape,func_d,In(n,w),in_a_w,omega_w,trans]
    for hyp in hyps:
        got_etr2=wl(got_etr2,hyp);imp=Implies(hyp,got_etr2.sequent.right[0])
        left=[f for f in got_etr2.sequent.left if not same(f,hyp)]
        got_etr2=Proof(Sequent(left,[imp]),'implies_right',[got_etr2],principal=imp)
    for v in [one,w,sn,n,c0,tape,b,a,q0,d]:
        body=got_etr2.sequent.right[0];fa=Forall(v,body)
        got_etr2=Proof(Sequent(got_etr2.sequent.left,[fa]),'forall_right',[got_etr2],principal=fa,term=v)
    got_etr2.name='phase1_step_case'
    return got_etr2


if __name__ == '__main__':
    print('=== phase1_base ===')
    p = phase1_base()
    print(f'  OK. Left: {[type(f).__name__ for f in p.sequent.left]}')

    print('=== phase1_step_case ===')
    p2 = phase1_step_case()
    print(f'  OK. Left: {[type(f).__name__ for f in p2.sequent.left]}')
    print(f'  Right: {str(p2.sequent.right[0])[:80]}')
