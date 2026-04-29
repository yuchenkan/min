"""Test ring0 decode+verify for all proofs with shared context."""

import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, In
from core.serialize import serialize
from ring0.decode import decode, save_ctx, load_ctx, EncodeContext, DecodeContext
import theorems
import os


if __name__ == '__main__':
    x, y, z, w = Var(), Var(), Var(), Var()
    c = Var()

    all_proofs = [
        ('extensionality', theorems.extensionality()),
        ('empty_set', theorems.empty_set()),
        ('pairing', theorems.pairing()),
        ('union', theorems.union()),
        ('power_set', theorems.power_set()),
        ('separation', theorems.separation(lambda x: In(x, c), [c])),
        ('infinity', theorems.infinity()),
        ('choice', theorems.choice()),
        ('replacement', theorems.replacement(lambda x, y: In(x, y), [])),
        ('regularity', theorems.regularity()),
        ('modus_ponens', theorems.modus_ponens(In(x, y), In(y, z), [x, y, z])),
        ('double_negation', theorems.double_negation(In(x, y), [x, y])),
        ('forall_instantiation', theorems.forall_instantiation(x, In(x, y), z, [y, z])),
        ('unique_empty', theorems.unique_empty()),
        ('eq_reflexive', theorems.eq_reflexive()),
        ('iff_intro', theorems.iff_intro(In(x, y), In(y, z), [x, y, z])),
        ('iff_elim_left', theorems.iff_elim_left(In(x, y), In(y, z), [x, y, z])),
        ('iff_elim_right', theorems.iff_elim_right(In(x, y), In(y, z), [x, y, z])),
        ('eq_symmetric', theorems.eq_symmetric()),
        ('eq_transitive', theorems.eq_transitive()),
        ('singleton_exists', theorems.singleton_exists()),
        ('singleton_eq', theorems.singleton_eq()),
        ('or_elim', theorems.or_elim(In(x, y), In(y, z), In(x, z), [x, y, z])),
        ('eq_substitution', theorems.eq_substitution()),
        ('and_intro', theorems.and_intro(In(x, y), In(y, z), [x, y, z])),
        ('and_elim_left', theorems.and_elim_left(In(x, y), In(y, z), [x, y, z])),
        ('and_elim_right', theorems.and_elim_right(In(x, y), In(y, z), [x, y, z])),
        ('or_intro_left', theorems.or_intro_left(In(x, y), In(y, z), [x, y, z])),
        ('or_intro_right', theorems.or_intro_right(In(x, y), In(y, z), [x, y, z])),
        ('iff_sym', theorems.iff_sym(In(x, y), In(y, z), [x, y, z])),
        ('iff_mp', theorems.iff_mp(In(x, y), In(y, z), [x, y, z])),
        ('iff_mp_rev', theorems.iff_mp_rev(In(x, y), In(y, z), [x, y, z])),
        ('or_iff_compat', theorems.or_iff_compat(In(x, y), In(y, z), In(z, w), In(x, w), [x, y, z, w])),
        ('eq_transfer', theorems.eq_transfer()),
        ('iff_chain', theorems.iff_chain(In(x, y), In(y, z), In(x, z), [x, y, z])),
        ('singleton_injection', theorems.singleton_injection()),
        ('pair_injection', theorems.pair_injection()),
        ('tuple_injection', theorems.tuple_injection()),
        ('forall_implies_exists', theorems.forall_implies_exists(In(x, y), In(y, z), x, [y, z])),
        ('singleton_pair_eq', theorems.singleton_pair_eq()),
        ('kuratowski', theorems.kuratowski()),
        ('successor_exists', theorems.successor_exists()),
        ('union_exists', theorems.union_exists()),
        ('intersect_exists', theorems.intersect_exists()),
        ('big_union_exists', theorems.big_union_exists()),
        ('eq_in_eq', theorems.eq_in_eq()),
        ('unique_successor', theorems.unique_successor()),
        ('infinity_gives_inductive', theorems.infinity_gives_inductive()),
        ('omega_is_inductive', theorems.omega_is_inductive()),
        ('omega_smallest_inductive', theorems.omega_smallest_inductive()),
        ('func_preserves_eq', theorems.func_preserves_eq()),
        ('func_unique', theorems.func_unique_thm()),
        ('omega_contains_empty', theorems.omega_contains_empty()),
        ('omega_succ_closed', theorems.omega_succ_closed()),
        ('rec_approx_zero', theorems.rec_approx_zero()),
        ('rec_agree', theorems.rec_agree()),
        ('ordpair_exists', theorems.ordpair_exists()),
        ('succ_not_empty', theorems.succ_not_empty()),
        ('apply_singleton', theorems.apply_singleton()),
        ('singleton_apply_eq', theorems.singleton_apply_eq()),
        ('eq_apply_transfer', theorems.eq_apply_transfer()),
        ('successor_injection', theorems.successor_injection()),
        ('eq_apply_val_transfer', theorems.eq_apply_val_transfer()),
        ('extend_function', theorems.extend_function()),
        ('ordpair_eq_transfer', theorems.ordpair_eq_transfer()),
        ('apply_union_intro_left', theorems.apply_union_intro_left()),
        ('apply_union_intro_right', theorems.apply_union_intro_right()),
        ('apply_union_elim', theorems.apply_union_elim()),
        ('rec_exists_step', theorems.rec_exists_step()),
        ('rec_exists', theorems.rec_exists()),
        ('ordpair_val_transfer', theorems.ordpair_val_transfer()),
        ('rec_func_exists', theorems.rec_func_exists()),
        ('rec_graph_exists', theorems.rec_graph_exists()),
        ('rec_h_apply', theorems.rec_h_apply()),
        ('rec_h_apply_fwd', theorems.rec_h_apply_fwd()),
        ('rec_h_dom_sub', theorems.rec_h_dom_sub()),
        ('rec_h_step', theorems.rec_h_step()),
        ('rec_h_function', theorems.rec_h_function()),
        ('succ_func_exists', theorems.succ_func_exists()),
        ('recursion_theorem', theorems.recursion_theorem()),
        ('ordpair_unique', theorems.ordpair_unique()),
        ('rec_value', theorems.rec_value()),
        ('singleton_is_recapprox', theorems.singleton_is_recapprox()),
        ('rec_values_agree', theorems.rec_values_agree()),
        ('rec_unique', theorems.rec_unique()),
        ('eq_successor_transfer', theorems.eq_successor_transfer()),
        ('sf_props', theorems.sf_props()),
        ('plus_zero_right', theorems.plus_zero_right()),
        ('rec_step_succ', theorems.rec_step_succ()),
        ('rec_h_zero_identity', theorems.rec_h_zero_identity()),
        ('plus_zero_left', theorems.plus_zero_left()),
        ('rec_succ_shift', theorems.rec_succ_shift()),
        ('omega_unique', theorems.omega_unique()),
        ('omega_exists', theorems.omega_exists()),
        ('sf_apply_transfer', theorems.sf_apply_transfer()),
        ('plus_comm', theorems.plus_comm()),
        ('rec_val_in_omega', theorems.rec_val_in_omega()),
        ('plus_assoc', theorems.plus_assoc()),
        ('plus_2_3', theorems.prove_addition(2, 3)),
        ('exists_num_5', theorems.exists_num(5)),
    ]

    ctx_path = '/tmp/ring0_all.pkl'
    if os.path.exists(ctx_path):
        ctx = load_ctx(ctx_path)
        print(f'loaded ctx: {len(ctx[1].verified):,} verified nodes')
    else:
        ctx = (EncodeContext(), DecodeContext())
    failed = []
    for name, proof in all_proofs:
        ok = decode(serialize(proof), ctx)
        status = 'ok' if ok else 'FAILED'
        print(f'{name}: {status}', flush=True)
        if not ok:
            failed.append(name)

    print(f'\n{len(all_proofs) - len(failed)}/{len(all_proofs)} ring0 verified.')
    print(f'verified nodes: {len(ctx[1].verified):,}')

    save_ctx(ctx, ctx_path)
    print(f'saved: {os.path.getsize(ctx_path):,} bytes')

    assert not failed, f'failed: {failed}'
