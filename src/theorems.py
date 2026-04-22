"""Theorems proved from the sequent calculus. All theorems are closed (no free vars)."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import zfc


# --- ZFC axioms as theorems (A |- A) ---

def extensionality():
    ax = zfc.Extensionality()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='extensionality')

def empty_set():
    ax = zfc.EmptySet()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='empty_set')

def pairing():
    ax = zfc.Pairing()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='pairing')

def union():
    ax = zfc.Union()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='union')

def power_set():
    ax = zfc.PowerSet()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='power_set')

def separation(phi, vars: list[Var]):
    ax = zfc.Separation(phi, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='separation')

def infinity():
    ax = zfc.Infinity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='infinity')

def choice():
    ax = zfc.Choice()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='choice')

def replacement(phi, vars: list[Var]):
    ax = zfc.Replacement(phi, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='replacement')

def regularity():
    ax = zfc.Regularity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='regularity')
