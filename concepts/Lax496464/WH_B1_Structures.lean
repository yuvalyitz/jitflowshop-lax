import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
---
title: Finite relational structures
type: definition
---
A *relational structure* $\mathcal A$ consists of a finite universe $A$ and, for each symbol of a
finite vocabulary $\tau$, a relation on $A$ of the symbol's arity [FG06, Section 4.2]. The
parameterized problems that define the W- and A-hierarchies take structures as input.

# Formalization notes

**Structures.** The universe is $\{0, \dots, \mathrm{size}-1\}$; the vocabulary is the list
`arities`, symbol $i$ having arity `arities[i]` $\ge 1$. Both the universe and the vocabulary may
be empty. A relation is a finite set of tuples, each a list of elements. A formula that mentions a
symbol outside the vocabulary does not fit the structure (`WH_B2_FirstOrder.Formula.Fits`) and is
false in it [FG06, p. 76].

**Words.** The word of a structure (`Encodes`) lists the number of symbols, the arities, the size
of the universe, and then, for each symbol, the number of its tuples followed by their entries.
The tuples of a relation may be listed in any order without repetition; the yes-instances of every
problem are independent of the order. The encoding is self-delimiting, so a structure may be
followed by further entries, as in an instance $(\mathcal A, k)$.

**Size.** The size of the universe is written as a single number. The word therefore has
$O(|\tau| + \sum_R |R|\cdot\mathrm{arity}(R))$ entries, whereas the size $\|\mathcal A\|$
[FG06, p. 74] (`Structure.norm`) counts the universe in unary. A reduction that ranges over the
universe first restricts it to the elements occurring in the relations together with a bounded
number of further elements. This preserves the answer, since elements that occur in no relation
are interchangeable.
-/

namespace Lax496464.WH_B1_Structures

open scoped BigOperators

/-- A finite relational structure. -/
structure Structure where
  /-- The vocabulary: the arities of the relation symbols `0, 1, …`. -/
  arities : List ℕ
  /-- The universe is `{0, …, size - 1}`. -/
  size : ℕ
  /-- The relation of each symbol, as a set of tuples. -/
  rel : ℕ → Finset (List ℕ)
  /-- Every arity is at least one. -/
  arity_pos : ∀ a ∈ arities, 1 ≤ a
  /-- The tuples of symbol `i` have its arity and entries in the universe; other symbols have no
  tuples. -/
  wf : ∀ i, ∀ t ∈ rel i, i < arities.length ∧ t.length = arities.getD i 0 ∧ ∀ a ∈ t, a < size

/-- The size `‖A‖ = |τ| + |A| + Σ_R |R^A| · arity(R)` of a structure [FG06, p. 74]. -/
def Structure.norm (A : Structure) : ℕ :=
  A.arities.length + A.size +
    ∑ i ∈ Finset.range A.arities.length, (A.rel i).card * A.arities.getD i 0

/-- The block of one relation: the number of its tuples, then the tuples, in some order without
repetition. -/
def EncodesRel (R : Finset (List ℕ)) (blk : List ℕ) : Prop :=
  ∃ ts : List (List ℕ), ts.Nodup ∧ ts.toFinset = R ∧ blk = ts.length :: ts.flatten

/-- The word `x` is an encoding of the structure `A`: the number of symbols, the arities, the size
of the universe, and one block per symbol. -/
def Encodes (x : List ℕ) (A : Structure) : Prop :=
  ∃ blocks : List (List ℕ), blocks.length = A.arities.length ∧
    (∀ i < A.arities.length, EncodesRel (A.rel i) (blocks.getD i [])) ∧
    x = A.arities.length :: (A.arities ++ A.size :: blocks.flatten)

end Lax496464.WH_B1_Structures
