"""Verify all proofs."""

import sys
sys.path.insert(0, 'src')

from core import Var, In, verify
from core.zfc import is_axiom
import theorems


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
        ('forall_instantiation', theorems.forall_instantiation(x, In(x, y), z, [x, y, z])),
        ('unique_empty', theorems.unique_empty()),
        ('eq_reflexive', theorems.eq_reflexive()),
        ('iff_intro', theorems.iff_intro(In(x, y), In(y, z), [x, y, z])),
        ('iff_elim_left', theorems.iff_elim_left(In(x, y), In(y, z), [x, y, z])),
        ('iff_elim_right', theorems.iff_elim_right(In(x, y), In(y, z), [x, y, z])),
        ('eq_symmetric', theorems.eq_symmetric()),
        ('eq_transitive', theorems.eq_transitive()),
        ('singleton_exists', theorems.singleton_exists()),
        # ('singleton_eq', theorems.singleton_eq()),
        ('or_elim', theorems.or_elim(In(x, y), In(y, z), In(x, z), [x, y, z])),
        ('eq_substitution', theorems.eq_substitution()),
        ('and_intro', theorems.and_intro(In(x, y), In(y, z), [x, y, z])),
        ('and_elim_left', theorems.and_elim_left(In(x, y), In(y, z), [x, y, z])),
        ('and_elim_right', theorems.and_elim_right(In(x, y), In(y, z), [x, y, z])),
        ('or_intro_left', theorems.or_intro_left(In(x, y), In(y, z), [x, y, z])),
        ('or_intro_right', theorems.or_intro_right(In(x, y), In(y, z), [x, y, z])),
        # ('iff_mp', theorems.iff_mp(In(x, y), In(y, z), [x, y, z])),
        # ('iff_mp_rev', theorems.iff_mp_rev(In(x, y), In(y, z), [x, y, z])),
        # ('or_iff_compat', theorems.or_iff_compat(In(x, y), In(y, z), In(z, w), In(x, w), [x, y, z, w])),
        # ('eq_transfer', theorems.eq_transfer()),
        ('iff_chain', theorems.iff_chain(In(x, y), In(y, z), In(x, z), [x, y, z])),
        # ('tuple_injection', theorems.tuple_injection()),
        ('forall_implies_exists', theorems.forall_implies_exists(In(x, y), In(y, z), x, [x, y, z])),
        # ('tuple_injection_full', theorems.tuple_injection_full()),
        # ('singleton_from_tuple', theorems.singleton_from_tuple()),
        # ('kuratowski', theorems.kuratowski()),
    ]

    for name, proof in all_proofs:
        ok = verify(proof, is_axiom)
        print(f'{name}: {"ok" if ok else "FAILED"}  {proof.theorem()}')
        assert ok, f'{name} failed'

    print(f'\n{len(all_proofs)} proofs verified.')
