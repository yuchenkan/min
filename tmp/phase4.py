"""headmove_left_elim for Phase4P."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import Successor
from vocab.omega import Num
from vocab.tm import HeadMove
from vocab.functions import Apply
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl
from theorems.logic import (and_elim_left, and_elim_right, or_elim,
    eq_symmetric, iff_sym, iff_chain)
from theorems.sets import eq_transfer, unique_successor
from theorems.tm import zero_neq_one

def headmove_left_elim():
    """Pairing |- forall h,hn,dir,c,hf,zero.
        HeadMove(h,hn,dir)→Eq(h,hf)→Eq(dir,zero)→Num(zero,0)→Successor(hf,c)→Eq(hn,c)"""
    h,hn,dir_v=Var(postfix='hh'),Var(postfix='hhn'),Var(postfix='hd')
    c,hf,zero_v=Var(postfix='hc'),Var(postfix='hhf'),Var(postfix='hz')
    hm=HeadMove(h,hn,dir_v);eq_h_hf=Eq(h,hf);eq_d_z=Eq(dir_v,zero_v)
    num_zero=Num(zero_v,0);succ_hf_c=Successor(hf,c);eq_hn_c=Eq(hn,c)
    left_and=And(Num(dir_v,1),Successor(hn,h))
    right_and=And(Num(dir_v,0),Successor(h,hn))
    # Right case: Succ(h,hn)→transfer to Succ(hf,hn)→unique_successor→Eq(hn,c)
    got_shhn=apply_thm(and_elim_right(Num(dir_v,0),Successor(h,hn),[]),[],right_and,Successor(h,hn),ax(right_and))
    z=Var(postfix='hz2')
    iff_zh=Iff(In(z,h),Or(In(z,hn),Eq(z,hn)))
    got_iff_zh=apply_thm(got_shhn,[z],concl=iff_zh)
    _et=eq_transfer();iff_hhf=Iff(In(z,h),In(z,hf))
    got_iff_hhf=apply_thm(_et,[h,hf,z]);got_iff_hhf=mp(got_iff_hhf,ax(eq_h_hf),eq_h_hf,got_iff_hhf.sequent.right[0].right)
    got_hfh=apply_thm(iff_sym(In(z,h),In(z,hf),[]),[],iff_hhf,Iff(In(z,hf),In(z,h)),got_iff_hhf)
    iff_hf_orn=Iff(In(z,hf),Or(In(z,hn),Eq(z,hn)))
    ic=iff_chain(In(z,hf),In(z,h),Or(In(z,hn),Eq(z,hn)),[])
    got_hf_orn=mp(apply_thm(ic,[],Iff(In(z,hf),In(z,h)),Implies(iff_zh,iff_hf_orn),got_hfh),got_iff_zh,iff_zh,iff_hf_orn)
    succ_hf_hn=Successor(hf,hn);fa_hfhn=Forall(z,iff_hf_orn)
    got_fa=Proof(Sequent(got_hf_orn.sequent.left,[fa_hfhn]),'forall_right',[got_hf_orn],principal=fa_hfhn,term=z)
    got_shfhn=cut(ax(succ_hf_hn),succ_hf_hn,got_fa)
    _us=unique_successor();got_eq=apply_thm(_us,[hf,hn,c])
    got_eq=mp(got_eq,got_shfhn,succ_hf_hn,got_eq.sequent.right[0].right)
    got_eq=mp(got_eq,ax(succ_hf_c),succ_hf_c,eq_hn_c)
    got_right=got_eq
    # Left case: Num(dir,1)+Eq(dir,zero)+Num(zero,0)→zero_neq_one→contradiction
    got_nd1=apply_thm(and_elim_left(Num(dir_v,1),Successor(hn,h),[]),[],left_and,Num(dir_v,1),ax(left_and))
    succ_dz=Successor(dir_v,zero_v)
    got_sdz=apply_thm(got_nd1,[zero_v],num_zero,succ_dz,ax(num_zero))
    _zno=zero_neq_one();not_eq_zd=Not(Eq(zero_v,dir_v))
    got_zno=apply_thm(_zno,[zero_v,dir_v,zero_v])
    got_zno=mp(got_zno,ax(num_zero),num_zero,got_zno.sequent.right[0].right)
    got_zno=mp(got_zno,got_sdz,succ_dz,not_eq_zd)
    _es=eq_symmetric();got_ezd=apply_thm(_es,[dir_v,zero_v],eq_d_z,Eq(zero_v,dir_v),ax(eq_d_z))
    gb=Proof(Sequent([Eq(zero_v,dir_v),not_eq_zd],[]),'not_left',[ax(Eq(zero_v,dir_v))],principal=not_eq_zd)
    gb=Proof(Sequent(gb.sequent.left,[eq_hn_c]),'weakening_right',[gb],principal=eq_hn_c)
    gb=cut(gb,not_eq_zd,got_zno);gb=cut(gb,Eq(zero_v,dir_v),got_ezd)
    got_left=gb
    # or_elim
    imp_l=Implies(left_and,eq_hn_c);ll=[f for f in got_left.sequent.left if not same(f,left_and)]
    got_il=Proof(Sequent(ll,[imp_l]),'implies_right',[got_left],principal=imp_l)
    imp_r=Implies(right_and,eq_hn_c);lr=[f for f in got_right.sequent.left if not same(f,right_and)]
    got_ir=Proof(Sequent(lr,[imp_r]),'implies_right',[got_right],principal=imp_r)
    oe=or_elim(left_and,right_and,eq_hn_c,[])
    got=apply_thm(oe,[],hm,Implies(imp_l,Implies(imp_r,eq_hn_c)),ax(hm))
    got=mp(got,got_il,imp_l,Implies(imp_r,eq_hn_c));got=mp(got,got_ir,imp_r,eq_hn_c)
    for p in [succ_hf_c,num_zero,eq_d_z,eq_h_hf,hm]:
        got=wl(got,p);imp=Implies(p,got.sequent.right[0])
        left=[f for f in got.sequent.left if not same(f,p)]
        got=Proof(Sequent(left,[imp]),'implies_right',[got],principal=imp)
    proof=got
    for v in [zero_v,hf,c,dir_v,hn,h]:
        body=proof.sequent.right[0];fa=Forall(v,body)
        proof=Proof(Sequent(proof.sequent.left,[fa]),'forall_right',[proof],principal=fa,term=v)
    proof.name='headmove_left_elim'
    return proof

if __name__=='__main__':
    p=headmove_left_elim()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'headmove_left_elim: OK, non-ZFC={len(non)}')
