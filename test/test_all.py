"""Verify all proofs: ZFC axioms, schemas, and theorems."""

import sys
sys.path.insert(0, 'src')

from core import Var, In, verify
from core.proof import Proof
from core import zfc
import theorems


def collect_proofs(module):
    for name in dir(module):
        val = getattr(module, name)
        if isinstance(val, Proof):
            yield name, val


if __name__ == '__main__':
    x, y, z = Var(), Var(), Var()

    all_proofs = list(collect_proofs(zfc)) + [
        ('modus_ponens', theorems.modus_ponens(In(x, y), In(y, z))),
        ('double_negation', theorems.double_negation(In(x, y))),
        ('forall_instantiation', theorems.forall_instantiation(x, In(x, y), z)),
        ('unique_empty', theorems.unique_empty()),
        ('eq_reflexive', theorems.eq_reflexive()),
        ('iff_intro', theorems.iff_intro(In(x, y), In(y, z))),
        ('iff_elim_left', theorems.iff_elim_left(In(x, y), In(y, z))),
        ('iff_elim_right', theorems.iff_elim_right(In(x, y), In(y, z))),
        ('eq_symmetric', theorems.eq_symmetric()),
        ('eq_transitive', theorems.eq_transitive()),
        ('singleton_eq', theorems.singleton_eq()),
        ('or_elim', theorems.or_elim(In(x, y), In(y, z), In(x, z))),
        ('eq_substitution', theorems.eq_substitution()),
        ('and_intro', theorems.and_intro(In(x, y), In(y, z))),
        ('and_elim_left', theorems.and_elim_left(In(x, y), In(y, z))),
        ('and_elim_right', theorems.and_elim_right(In(x, y), In(y, z))),
        ('eq_transfer', theorems.eq_transfer()),
        ('or_iff_compat', theorems.or_iff_compat(In(x, y), In(y, z), In(z, x), In(x, z))),
        ('pair_eq_forward', theorems.tuple_injection()),
        ('or_intro_left', theorems.or_intro_left(In(x, y), In(y, z))),
        ('or_intro_right', theorems.or_intro_right(In(x, y), In(y, z))),
        ('tuple_injection', theorems.tuple_injection_full()),
        ('singleton_from_tuple', theorems.singleton_from_tuple()),
        ('forall_implies_exists', theorems.forall_implies_exists(In(x, y), In(y, z), x)),
        ('kuratowski', theorems.kuratowski()),
    ]

    for name, proof in all_proofs:
        ok = verify(proof)
        print(f'{name}: {"ok" if ok else "FAILED"}')
        assert ok, f'{name} failed'

    print(f'\n{len(all_proofs)} proofs verified.')
