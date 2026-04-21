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
    ]

    for name, proof in all_proofs:
        ok = verify(proof)
        print(f'{name}: {"ok" if ok else "FAILED"}')
        assert ok, f'{name} failed'

    print(f'\n{len(all_proofs)} proofs verified.')
