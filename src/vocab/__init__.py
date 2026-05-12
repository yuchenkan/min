"""Vocabulary: formal predicates built on core language."""

from vocab.sets import (SetSpec, Empty, Singleton, PairSet, Subset,
    Union, Intersect, BigUnion, BigIntersect, PowerSet, Diff, Product)
from vocab.ordpair import OrdPair, Successor
from vocab.functions import Apply, Domain, Range, Relation, Function, Total
from vocab.omega import Inductive, Omega, Nat, Num, ExistsUnique
from vocab.recursion import TotalFrom, Recursive, RecApprox, PlusFunc, Plus
