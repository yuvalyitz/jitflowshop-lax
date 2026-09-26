import Lax496464.HittingSet
import Lax429075.Satisfiability

/-!
---
title: The reduction from satisfiability to Hitting Set
type: definition
---
A CNF formula $F$ on the variables $x_0, \dots, x_{V-1}$ becomes an instance of Hitting Set
on the universe $\{0, \dots, 2V - 1\}$, in which $2i$ stands for the literal $x_i$ and
$2i + 1$ for $\bar x_i$. The family has one set $\{2i, 2i+1\}$ for each variable and one set
for each clause, holding the elements of its literals; the required size is $V$.

A hitting set of size $V$ meets each of the $V$ disjoint pairs in exactly one element, so
it is a truth assignment, and it meets the set of a clause exactly when the assignment
satisfies the clause. This is the composition of Karp's reductions from satisfiability to
Clique and from Clique to Node Cover, read on the literals rather than on the occurrences.

The reduction on words decodes a formula, builds the instance and encodes it; a word that
encodes no formula is treated as the formula with one empty clause, whose instance has no
hitting set.

# Formalization notes

Formulas, their binary encoding and satisfiability are those of the archive's Cook–Levin
theorem (`lax-429075`).

The number of variables is one more than the largest index occurring, and at least two: the
hardness statements ask for a solution size of at least two, and a fresh pair costs nothing.
An empty clause gives an empty set, which no hitting set meets, as it should.

The sets are written as lists of elements, and the family is the membership predicate of
those lists on `Fin (2V)`; an element of a clause lies below $2V$ by the choice of $V$.
-/

namespace Lax496464.HittingSetFromSat

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax496464.HittingSet

/-- One more than the largest variable index of the formula, and `1` for no literal. -/
def bound (F : Formula) : ℕ := (F.flatMap id).foldr (fun l n => max (l.index + 1) n) 1

/-- The number of variables of the construction: the formula's, but at least two. -/
def vars (F : Formula) : ℕ := max (bound F) 2

/-- The element standing for a literal: `2i` for `x_i`, `2i + 1` for `¬x_i`. -/
def elem (l : Literal) : ℕ := 2 * l.index + if l.positive then 0 else 1

/-- The sets, as lists of elements: the pair of each variable, then the elements of each
clause. -/
def sets (F : Formula) : List (List ℕ) :=
  (List.range (vars F)).map (fun i => [2 * i, 2 * i + 1]) ++ F.map fun C => C.map elem

/-- The instance of a formula: the universe `2·vars F`, one set per variable and one per
clause. -/
def inst (F : Formula) : Instance where
  n := 2 * vars F
  m := vars F + F.length
  F := fun j => Finset.univ.filter fun i : Fin (2 * vars F) => (i : ℕ) ∈ (sets F).getD j []

/-- The instance with its solution size. -/
def transform (F : Formula) : Instance × ℕ := (inst F, vars F)

/-- The formula a word encodes, and the formula with one empty clause if it encodes none. -/
def parseF (w : Word) : Formula := (decodeCNF w).getD [[]]

/-- The reduction on words, to an instance with its solution size. -/
def reduce (w : Word) : Instance × ℕ := transform (parseF w)

/-- The reduction on words, to the binary word of the instance. -/
def reduceWord (w : Word) : Word := encodeInstance (reduce w).1 (reduce w).2

end Lax496464.HittingSetFromSat
