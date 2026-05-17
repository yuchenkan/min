"""Theorems: axioms module."""

from core.lang import Var, In
from core.proof import Sequent, Proof
from core import zfc
from vocab import Empty

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



def separation(phi, x, vars: list[Var]):
    ax = zfc.Separation(phi, x, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='separation')



def infinity():
    ax = zfc.Infinity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='infinity')



def choice():
    ax = zfc.Choice()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='choice')



def replacement(phi, x, y, vars: list[Var]):
    ax = zfc.Replacement(phi, x, y, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='replacement')



def regularity():
    ax = zfc.Regularity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='regularity')


