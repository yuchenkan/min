"""Verify all 203 theorems with theorem-level caching."""

import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

import functools, inspect, time
from core import Var, In, qed
from core.zfc import is_axiom

# Import all theorem modules
import theorems
import theorems.axioms, theorems.logic, theorems.sets, theorems.omega
import theorems.recursion, theorems.arithmetic, theorems.tm

# Cache all parameterless theorems
modules = [theorems.axioms, theorems.logic, theorems.sets, theorems.omega,
           theorems.recursion, theorems.arithmetic, theorems.tm]
cached_count = 0
for mod in modules:
    for name in dir(mod):
        fn = getattr(mod, name)
        if callable(fn) and not name.startswith('_') and not inspect.isclass(fn):
            try:
                sig = inspect.signature(fn)
                if len(sig.parameters) == 0:
                    cached = functools.cache(fn)
                    setattr(mod, name, cached)
                    if hasattr(theorems, name):
                        setattr(theorems, name, cached)
                    cached_count += 1
            except (ValueError, TypeError):
                pass

print(f'Cached {cached_count} parameterless theorems')


if __name__ == '__main__':
    x, y, z, w = Var(), Var(), Var(), Var()
    c = Var()
    A, B, C, D = In(x, y), In(y, z), In(z, w), In(x, w)

    all_proofs = [
        # --- axioms (10) ---
        ('extensionality', lambda: theorems.axioms.extensionality()),
        ('empty_set', lambda: theorems.axioms.empty_set()),
        ('pairing', lambda: theorems.axioms.pairing()),
        ('union', lambda: theorems.axioms.union()),
        ('power_set', lambda: theorems.axioms.power_set()),
        ('separation', lambda: theorems.axioms.separation(lambda sv: In(sv, c), Var(), [c])),
        ('infinity', lambda: theorems.axioms.infinity()),
        ('choice', lambda: theorems.axioms.choice()),
        ('replacement', lambda: theorems.axioms.replacement(In(x, y), x, y, [])),
        ('regularity', lambda: theorems.axioms.regularity()),

        # --- logic (25) ---
        ('modus_ponens', lambda: theorems.logic.modus_ponens(A, B, [x, y, z])),
        ('double_negation', lambda: theorems.logic.double_negation(A, [x, y])),
        ('iff_intro', lambda: theorems.logic.iff_intro(A, B, [x, y, z])),
        ('iff_elim_left', lambda: theorems.logic.iff_elim_left(A, B, [x, y, z])),
        ('iff_elim_right', lambda: theorems.logic.iff_elim_right(A, B, [x, y, z])),
        ('or_intro_left', lambda: theorems.logic.or_intro_left(A, B, [x, y, z])),
        ('or_intro_right', lambda: theorems.logic.or_intro_right(A, B, [x, y, z])),
        ('or_elim', lambda: theorems.logic.or_elim(A, B, C, [x, y, z, w])),
        ('and_intro', lambda: theorems.logic.and_intro(A, B, [x, y, z])),
        ('and_elim_left', lambda: theorems.logic.and_elim_left(A, B, [x, y, z])),
        ('and_elim_right', lambda: theorems.logic.and_elim_right(A, B, [x, y, z])),
        ('forall_instantiation', lambda: theorems.logic.forall_instantiation(x, A, z, [y, z])),
        ('forall_implies_exists', lambda: theorems.logic.forall_implies_exists(A, B, x, [y, z])),
        ('eq_reflexive', lambda: theorems.logic.eq_reflexive()),
        ('eq_symmetric', lambda: theorems.logic.eq_symmetric()),
        ('eq_transitive', lambda: theorems.logic.eq_transitive()),
        ('unique_empty', lambda: theorems.logic.unique_empty()),
        ('iff_chain', lambda: theorems.logic.iff_chain(A, B, C, [x, y, z, w])),
        ('eq_substitution', lambda: theorems.logic.eq_substitution()),
        ('or_iff_compat', lambda: theorems.logic.or_iff_compat(A, B, C, D, [x, y, z, w])),
        ('iff_mp', lambda: theorems.logic.iff_mp(A, B, [x, y, z])),
        ('iff_mp_rev', lambda: theorems.logic.iff_mp_rev(A, B, [x, y, z])),
        ('iff_sym', lambda: theorems.logic.iff_sym(A, B, [x, y, z])),
        ('char_transfer', lambda: theorems.logic.char_transfer(A, B, C, [x, y, z, w])),
        ('exists_unique_bridge', lambda: theorems.logic.exists_unique_bridge(In(x, y), In(x, z), x, [y, z])),

        # --- sets (40) ---
        ('singleton_exists', lambda: theorems.sets.singleton_exists()),
        ('pairset_exists', lambda: theorems.sets.pairset_exists()),
        ('singleton_eq', lambda: theorems.sets.singleton_eq()),
        ('eq_transfer', lambda: theorems.sets.eq_transfer()),
        ('singleton_injection', lambda: theorems.sets.singleton_injection()),
        ('singleton_pair_eq', lambda: theorems.sets.singleton_pair_eq()),
        ('pair_injection', lambda: theorems.sets.pair_injection()),
        ('tuple_injection', lambda: theorems.sets.tuple_injection()),
        ('kuratowski', lambda: theorems.sets.kuratowski()),
        ('union_exists', lambda: theorems.sets.union_exists()),
        ('successor_exists', lambda: theorems.sets.successor_exists()),
        ('intersect_exists', lambda: theorems.sets.intersect_exists()),
        ('big_union_exists', lambda: theorems.sets.big_union_exists()),
        ('unique_successor', lambda: theorems.sets.unique_successor()),
        ('eq_in_eq', lambda: theorems.sets.eq_in_eq()),
        ('ordpair_exists', lambda: theorems.sets.ordpair_exists()),
        ('succ_not_empty', lambda: theorems.sets.succ_not_empty()),
        ('ordpair_eq_transfer', lambda: theorems.sets.ordpair_eq_transfer()),
        ('ordpair_val_transfer', lambda: theorems.sets.ordpair_val_transfer()),
        ('ordpair_unique', lambda: theorems.sets.ordpair_unique()),
        ('eq_successor_transfer', lambda: theorems.sets.eq_successor_transfer()),
        ('omega_unique', lambda: theorems.sets.omega_unique()),
        ('ordpair_set_transfer', lambda: theorems.sets.ordpair_set_transfer()),
        ('unique_singleton', lambda: theorems.sets.unique_singleton()),
        ('unique_successor_set', lambda: theorems.sets.unique_successor_set()),
        ('unique_ordpair', lambda: theorems.sets.unique_ordpair()),
        ('apply_first_in_double_union', lambda: theorems.sets.apply_first_in_double_union()),
        ('omega_transitive_set', lambda: theorems.sets.omega_transitive_set()),
        ('subset_in_powerset', lambda: theorems.sets.subset_in_powerset()),
        ('ordpair_bounded', lambda: theorems.sets.ordpair_bounded()),
        ('omega_no_self_membership', lambda: theorems.sets.omega_no_self_membership()),
        ('domain_exists', lambda: theorems.sets.domain_exists()),
        ('product_exists', lambda: theorems.sets.product_exists()),
        ('product_in_intro', lambda: theorems.sets.product_in_intro()),
        ('succ_neq', lambda: theorems.sets.succ_neq()),
        ('omega_pred', lambda: theorems.sets.omega_pred()),
        ('succ_injection', lambda: theorems.sets.succ_injection()),
        ('omega_transitive', lambda: theorems.sets.omega_transitive()),
        ('func_ext', lambda: theorems.sets.func_ext()),
        ('pairset_exists', lambda: theorems.sets.pairset_exists()),

        # --- omega (9) ---
        ('infinity_gives_inductive', lambda: theorems.omega.infinity_gives_inductive()),
        ('omega_is_inductive', lambda: theorems.omega.omega_is_inductive()),
        ('omega_contains_empty', lambda: theorems.omega.omega_contains_empty()),
        ('omega_succ_closed', lambda: theorems.omega.omega_succ_closed()),
        ('omega_smallest_inductive', lambda: theorems.omega.omega_smallest_inductive()),
        ('func_preserves_eq', lambda: theorems.omega.func_preserves_eq()),
        ('func_unique_thm', lambda: theorems.omega.func_unique_thm()),
        ('omega_exists', lambda: theorems.omega.omega_exists()),
        ('unique_omega', lambda: theorems.omega.unique_omega()),

        # --- recursion (34) ---
        ('rec_approx_zero', lambda: theorems.recursion.rec_approx_zero()),
        ('rec_agree', lambda: theorems.recursion.rec_agree()),
        ('apply_singleton', lambda: theorems.recursion.apply_singleton()),
        ('singleton_apply_eq', lambda: theorems.recursion.singleton_apply_eq()),
        ('singleton_is_function', lambda: theorems.recursion.singleton_is_function()),
        ('eq_apply_transfer', lambda: theorems.recursion.eq_apply_transfer()),
        ('successor_injection_omega', lambda: theorems.recursion.successor_injection_omega()),
        ('eq_apply_val_transfer', lambda: theorems.recursion.eq_apply_val_transfer()),
        ('apply_set_transfer', lambda: theorems.recursion.apply_set_transfer()),
        ('extend_function', lambda: theorems.recursion.extend_function()),
        ('apply_union_intro_left', lambda: theorems.recursion.apply_union_intro_left()),
        ('apply_union_intro_right', lambda: theorems.recursion.apply_union_intro_right()),
        ('apply_union_elim', lambda: theorems.recursion.apply_union_elim()),
        ('rec_exists_step', lambda: theorems.recursion.rec_exists_step()),
        ('singleton_is_recapprox', lambda: theorems.recursion.singleton_is_recapprox()),
        ('rec_exists', lambda: theorems.recursion.rec_exists()),
        ('rec_value', lambda: theorems.recursion.rec_value()),
        ('rec_func_exists', lambda: theorems.recursion.rec_func_exists()),
        ('rec_approx_val_in_w', lambda: theorems.recursion.rec_approx_val_in_w()),
        ('rec_graph_exists', lambda: theorems.recursion.rec_graph_exists()),
        ('rec_h_apply', lambda: theorems.recursion.rec_h_apply()),
        ('rec_h_apply_fwd', lambda: theorems.recursion.rec_h_apply_fwd()),
        ('rec_h_dom_sub', lambda: theorems.recursion.rec_h_dom_sub()),
        ('rec_h_step', lambda: theorems.recursion.rec_h_step()),
        ('succ_func_exists', lambda: theorems.recursion.succ_func_exists()),
        ('rec_h_function', lambda: theorems.recursion.rec_h_function()),
        ('recursion_theorem', lambda: theorems.recursion.recursion_theorem()),
        ('rec_values_agree', lambda: theorems.recursion.rec_values_agree()),
        ('rec_unique', lambda: theorems.recursion.rec_unique()),
        ('succ_not_empty', lambda: theorems.recursion.succ_not_empty()),
        ('ordpair_eq_transfer', lambda: theorems.recursion.ordpair_eq_transfer()),
        ('ordpair_unique', lambda: theorems.recursion.ordpair_unique()),
        ('singleton_exists', lambda: theorems.recursion.singleton_exists()),
        ('ordpair_val_transfer', lambda: theorems.recursion.ordpair_val_transfer()),

        # --- arithmetic (44) ---
        ('sf_total_from', lambda: theorems.arithmetic.sf_total_from()),
        ('rec_for_each_m', lambda: theorems.arithmetic.rec_for_each_m()),
        ('sf_props', lambda: theorems.arithmetic.sf_props()),
        ('plus_func_eq', lambda: theorems.arithmetic.plus_func_eq()),
        ('plus_func_exists', lambda: theorems.arithmetic.plus_func_exists()),
        ('plus_func_unique', lambda: theorems.arithmetic.plus_func_unique()),
        ('plus_zero_right', lambda: theorems.arithmetic.plus_zero_right()),
        ('rec_step_succ', lambda: theorems.arithmetic.rec_step_succ()),
        ('h_zero_identity', lambda: theorems.arithmetic.h_zero_identity()),
        ('h_succ_left', lambda: theorems.arithmetic.h_succ_left()),
        ('h_comm_identity', lambda: theorems.arithmetic.h_comm_identity()),
        ('h_val_in_omega', lambda: theorems.arithmetic.h_val_in_omega()),
        ('plus_zero_exists', lambda: theorems.arithmetic.plus_zero_exists()),
        ('plus_succ_right', lambda: theorems.arithmetic.plus_succ_right()),
        ('plus_val_in_omega', lambda: theorems.arithmetic.plus_val_in_omega()),
        ('plus_zero_left', lambda: theorems.arithmetic.plus_zero_left()),
        ('sf_apply_transfer', lambda: theorems.arithmetic.sf_apply_transfer()),
        ('prove_addition_0_0', lambda: theorems.arithmetic.prove_addition(0, 0)),
        ('prove_addition_0_1', lambda: theorems.arithmetic.prove_addition(0, 1)),
        ('prove_addition_1_0', lambda: theorems.arithmetic.prove_addition(1, 0)),
        ('prove_addition_1_1', lambda: theorems.arithmetic.prove_addition(1, 1)),
        ('prove_addition_2_2', lambda: theorems.arithmetic.prove_addition(2, 2)),
        ('prove_addition_4_3', lambda: theorems.arithmetic.prove_addition(4, 3)),
        ('plus_comm', lambda: theorems.arithmetic.plus_comm()),
        ('unique_num_0', lambda: theorems.arithmetic.unique_num(0)),
        ('unique_num_3', lambda: theorems.arithmetic.unique_num(3)),
        ('rec_val_in_omega', lambda: theorems.arithmetic.rec_val_in_omega()),
        ('h_assoc_identity', lambda: theorems.arithmetic.h_assoc_identity()),
        ('plus_assoc', lambda: theorems.arithmetic.plus_assoc()),
        ('plus_geq', lambda: theorems.arithmetic.plus_geq()),
        ('num_exists_0', lambda: theorems.arithmetic.num_exists(0)),
        ('num_exists_3', lambda: theorems.arithmetic.num_exists(3)),
        ('plus_val_unique', lambda: theorems.arithmetic.plus_val_unique()),
        ('plus_pred', lambda: theorems.arithmetic.plus_pred()),
        ('plus_bounded_exists', lambda: theorems.arithmetic.plus_bounded_exists()),
        ('eq_reflexive', lambda: theorems.arithmetic.eq_reflexive()),
        ('eq_substitution', lambda: theorems.arithmetic.eq_substitution()),
        ('eq_successor_transfer', lambda: theorems.arithmetic.eq_successor_transfer()),
        ('kuratowski', lambda: theorems.arithmetic.kuratowski()),
        ('ordpair_exists', lambda: theorems.arithmetic.ordpair_exists()),
        ('unique_successor', lambda: theorems.arithmetic.unique_successor()),
        ('eq_in_eq', lambda: theorems.recursion.eq_in_eq()),

        # --- tm (41) ---
        ('tape_update_exists', lambda: theorems.tm.tape_update_exists()),
        ('config_intro', lambda: theorems.tm.config_intro()),
        ('tape_update_function', lambda: theorems.tm.tape_update_function()),
        ('tape_read_high', lambda: theorems.tm.tape_read_high()),
        ('tape_update_other', lambda: theorems.tm.tape_update_other()),
        ('tape_update_at', lambda: theorems.tm.tape_update_at()),
        ('tape_update_other_rev', lambda: theorems.tm.tape_update_other_rev()),
        ('config_exists', lambda: theorems.tm.config_exists()),
        ('tm_add_correct', lambda: theorems.tm.tm_add_correct()),
        ('config_elim', lambda: theorems.tm.config_elim()),
        ('transition_apply', lambda: theorems.tm.transition_apply()),
        ('head_move_right', lambda: theorems.tm.head_move_right()),
        ('head_move_left', lambda: theorems.tm.head_move_left()),
        ('step_elim', lambda: theorems.tm.step_elim()),
        ('zero_neq_one', lambda: theorems.tm.zero_neq_one()),
        ('tape_update_eq', lambda: theorems.tm.tape_update_eq()),
        ('config_eq', lambda: theorems.tm.config_eq()),
        ('config_eq_transfer', lambda: theorems.tm.config_eq_transfer()),
        ('transition_unique', lambda: theorems.tm.transition_unique()),
        ('config_decompose', lambda: theorems.tm.config_decompose()),
        ('apply_func_transfer', lambda: theorems.tm.apply_func_transfer()),
        ('tape_update_unique', lambda: theorems.tm.tape_update_unique()),
        ('tape_update_eq_args', lambda: theorems.tm.tape_update_eq_args()),
        ('headmove_right_elim', lambda: theorems.tm.headmove_right_elim()),
        ('func_eq_transfer', lambda: theorems.tm.func_eq_transfer()),
        ('phase1_step_tmstep', lambda: theorems.tm.phase1_step_tmstep()),
        ('phase1_step_extend_trace', lambda: theorems.tm.phase1_step_extend_trace()),
        ('tape_read_sep', lambda: theorems.tm.tape_read_sep()),
        ('tape_read_low', lambda: theorems.tm.tape_read_low()),
        ('phase1_base', lambda: theorems.tm.phase1_base()),
        ('phase1_step_case', lambda: theorems.tm.phase1_step_case()),
        ('phase1', lambda: theorems.tm.phase1()),
        ('tmstep_to_reaches', lambda: theorems.tm.tmstep_to_reaches()),
        ('phase2', lambda: theorems.tm.phase2()),
        ('phase4', lambda: theorems.tm.phase4()),
        ('phase5', lambda: theorems.tm.phase5()),
        ('phase3_base', lambda: theorems.tm.phase3_base()),
        ('phase3_step_case', lambda: theorems.tm.phase3_step_case()),
        ('phase3', lambda: theorems.tm.phase3()),
        ('tmreaches_compose', lambda: theorems.tm.tmreaches_compose()),
    ]

    # Filter by command line args
    filters = sys.argv[1:]
    if filters:
        all_proofs = [(n, b) for n, b in all_proofs if any(f in n for f in filters)]

    print(f'{len(all_proofs)} theorems to verify')
    t0 = time.time()
    failed = []
    for name, build in all_proofs:
        try:
            proof = build()
            ok = qed(proof, is_axiom)
            if not ok:
                print(f'  {name}: qed FAILED')
                failed.append(name)
        except Exception as e:
            print(f'  {name}: ERROR {e}')
            failed.append(name)

    elapsed = time.time() - t0
    passed = len(all_proofs) - len(failed)
    print(f'\n{passed}/{len(all_proofs)} verified in {elapsed:.1f}s')
    if failed:
        print(f'Failed: {failed}')
    assert not failed, f'failed: {failed}'
