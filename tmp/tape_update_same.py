def tape_update_same_val():
    """If tape_in(pos)=v and we write v at position a, then tape2(pos)=v regardless of pos=a.
    |- ∀t2,t,a,v,pos. TapeUpdate(t2,t,a,v) → Function(t2) → Apply(t,pos,v) → Apply(t2,pos,v)

    Case split on Eq(pos,a) vs Not(Eq(pos,a)):
    - Eq(pos,a): tape_update_at gives Apply(t2,a,v). Transfer via Eq(pos,a).
    - Not(Eq(pos,a)): tape_update_other gives Apply(t2,pos,v) directly."""
    # Actually, there's an even simpler approach using the TapeUpdate definition directly.
    # TapeUpdate(t2,t,a,v) = ∀x,y. (x∈t2 ↔ ((x∈t ∧ ¬OrdPair(x,a)) ∨ OrdPair(x,a,v)))
    # Hmm, that's the Separation-level definition. Let me just check what tape_update_eq gives.

    # tape_update_eq: TapeUpdate(t2,t,a,w) ∧ Eq(pos,a) → Apply(t2,pos,w)
    # tape_update_other: TapeUpdate(t2,t,a,w) ∧ Apply(t,pos,v) ∧ Not(Eq(pos,a)) → Apply(t2,pos,v)

    # For same value: Apply(t,pos,v) ∧ TapeUpdate(t2,t,a,v):
    # If pos=a: tape_update_eq gives Apply(t2,a,v). Eq(pos,a) → Apply(t2,pos,v) via transfer.
    # If pos≠a: tape_update_other gives Apply(t2,pos,v).

    # But I need excluded middle: Eq(pos,a) ∨ Not(Eq(pos,a)).
    # In the kernel this is provable (classical logic).

    # Actually, the sequent calculus has built-in excluded middle via the structural rules.
    # [Eq(pos,a)] |- Eq(pos,a)  and  [Not(Eq(pos,a))] |- Not(Eq(pos,a))
    # Both give Apply(t2,pos,v). Cut gives Apply(t2,pos,v) unconditionally.

    # Let me just build it directly without a new theorem.
    # The caller (phase3_step) can do this inline.
    pass

# Actually, let me think simpler. In phase3, the tape2 was created by writing one at position a.
# The original tape has one at all positions in [0,a) and [sa, sa+b).
# Position pos = sa + j where sa = S(a), j ∈ b. So pos ≥ S(a) > a.
# Therefore pos ≠ a, and tape_update_other applies directly.
# The key fact: pos > a, i.e., a ∈ pos (in omega ordering).
# From Plus(sa,j,pos) with sa=S(a): pos ≥ sa = S(a) > a.
# In omega: In(a, S(a)) and In(S(a), pos) or Eq(S(a), pos).
# TransitiveSet(pos): In(a, S(a)) ∧ In(S(a), pos) → In(a, pos).
# In(a, pos) → Not(Eq(pos, a)) via omega_no_self_membership.

# Let me check if we have omega_no_self_membership:
import sys; sys.path.insert(0, '/root/min/src')
from theorems.sets import omega_no_self_membership
print("omega_no_self_membership exists")
