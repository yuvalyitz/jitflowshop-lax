import Lax496464.ParameterizedComplexity
import Lax434930.PolynomialTime
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

/-!
---
title: Hitting Set
type: definition
---
An instance consists of a universe $\{1, \dots, n\}$ and a family $F_1, \dots, F_m$ of
subsets of it; together with an integer $k$ it asks whether some $H$ with $|H| = k$ meets
every set of the family. Hitting Set is the problem the hardness results of this
submission reduce from, parameterized by the solution size $k$.

This is the problem [SP8] of Garey and Johnson. It contains Karp's *Node Cover* (problem 5
of his list) as the case of sets of size two. Karp's own *Hitting Set* (problem 15) is a
different problem: it asks for a set meeting every member of the family in exactly one
element.

The instances considered here are those with $2 \le k \le n$. The lower bound is what the
construction of the reduction needs, and the upper bound is a normalization: a hitting
set of size exactly $k$ cannot exist once $k$ exceeds the universe. Neither restriction
costs anything — see the statement of the problem's hardness.

# Formalization notes

The family is presented to a machine in the compressed sparse row form that presents a
graph to a machine elsewhere in the archive: an array of $m+1$ offsets cutting a member
array into one block per set. The blocks are not required to be sorted and repetitions
are not forbidden; leaving those conditions out admits more words and therefore
strengthens every claim about programs reading the format. The solution size is the final
entry, so that the family occupies the same offsets whether or not it is followed by one.

The universe is `Fin n`, counted from zero where the paper counts from one. The
construction of the reduction uses an element as an additive offset inside a due date and
needs it to be at least one, so it adds one; that is a detail of the construction and not
of the problem.

The required size is exact, $|H| = k$, as the paper writes it. For a nonempty universe
the exact and the "at most" versions are interchangeable, and the exact one is what the
construction's target is calibrated against.

The universe is required to be no larger than the word: $n \le |x|$. Every reduction of this
submission writes an instance of size at least $n^2$, and a word states $n$ as a single
entry, so without the bound a word of five entries could name a universe of a billion
elements and no reduction could write its image in time bounded by the length of the word.
The bound costs nothing — an element occurring in no set can be deleted and the others
renumbered, and the reduction from satisfiability of `HittingSetFromSat` already emits
instances with $n + m$ polynomial in the size of its input — and it agrees with the
convention that every element of the universe occurs.

The binary encoding exists beside the word encoding for the same reason as elsewhere: a
claim quantifying over NP is a claim about a Turing machine and hence about bits. It
writes the two counts and the solution size, and then each set as its size followed by its
members in increasing order. A number is written as its binary digits, least significant
first, preceded by their number in unary; that code is prefix-free, so the encoding is
injective. The language of Hitting Set is the set of binary words of the instances, with a
solution size, that have a hitting set of that size.
-/

namespace Lax496464.HittingSet

open Lax496464.ParameterizedComplexity Lax434930.PolynomialTime

/-- An instance of Hitting Set: a universe `Fin n` and a family of `m` subsets of it. The
solution size is carried separately, as the parameter. -/
structure Instance where
  /-- The size `n` of the universe. -/
  n : ℕ
  /-- The number `m` of sets in the family. -/
  m : ℕ
  /-- The family `F₁, …, F_m`. -/
  F : Fin m → Finset (Fin n)

/-- `P` has a hitting set of size exactly `k`. -/
def Instance.HasHittingSet (P : Instance) (k : ℕ) : Prop :=
  ∃ H : Finset (Fin P.n), H.card = k ∧ ∀ j : Fin P.m, ∃ i ∈ H, i ∈ P.F j

/-- The size of the universe declared by a word: its first entry. -/
def universeSize (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of sets declared by a word: its second entry. -/
def setCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The `i`-th offset: the `m+1` offsets follow the two header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `t`-th entry of the member array, which follows the offsets. -/
def member (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + setCount x + t) 0

/-- The solution size `k`: the entry following the member array. -/
def solutionSize (x : List ℕ) : ℕ :=
  x.getD (3 + setCount x + offset x (setCount x)) 0

/-- The word `x` encodes the instance `P` with solution size `k`. -/
structure Encodes (x : List ℕ) (P : Instance) (k : ℕ) : Prop where
  /-- The word declares `P`'s universe. -/
  universeSize_eq : universeSize x = P.n
  /-- The word declares `P`'s family. -/
  setCount_eq : setCount x = P.m
  /-- The word is the two header entries, the `m+1` offsets, a member array as long as
  the last offset says, and the solution size. -/
  length_eq : x.length = 4 + P.m + offset x P.m
  /-- The block of the first set begins at the start of the member array. -/
  offset_zero : offset x 0 = 0
  /-- The offsets are nondecreasing, so they cut the member array into one block per
  set. -/
  offset_mono : ∀ j < P.m, offset x j ≤ offset x (j + 1)
  /-- Every entry of the member array is an element of the universe. -/
  member_lt : ∀ t < offset x P.m, member x t < P.n
  /-- The block of a set lists exactly its elements. -/
  mem_iff : ∀ (j : Fin P.m) (i : Fin P.n),
    i ∈ P.F j ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ member x t = i
  /-- The word declares the solution size. -/
  solutionSize_eq : solutionSize x = k
  /-- The solution size is at least two and at most the size of the universe. -/
  size_bounds : 2 ≤ k ∧ k ≤ P.n
  /-- The universe is no larger than the word that presents it. -/
  universeSize_le : P.n ≤ x.length

/-- The words that encode an instance with its solution size. -/
def Instances : Set (List ℕ) := {x | ∃ P k, Encodes x P k}

/-- **Hitting Set**, parameterized by the solution size. -/
def byK : Problem where
  Domain := Instances
  Yes x := ∃ P k, Encodes x P k ∧ Instance.HasHittingSet P k
  param x := solutionSize x

/-- The elements of the `j`-th set, in the order of the universe. -/
def Instance.members (P : Instance) (j : Fin P.m) : List (Fin P.n) :=
  (List.finRange P.n).filter fun i => decide (i ∈ P.F j)

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance with its solution size as a binary word: the two counts, the solution
size, and then each set as its size followed by its members. -/
def encodeInstance (P : Instance) (k : ℕ) : Word :=
  encodeNat P.n ++ encodeNat P.m ++ encodeNat k ++
    (List.finRange P.m).flatMap fun j =>
      encodeNat (P.F j).card ++ (P.members j).flatMap fun i => encodeNat i

/-- **Hitting Set** as a language: the binary words of the instances, with a solution size,
that have a hitting set of that size. -/
def HittingSetLanguage : Language :=
  {w | ∃ (P : Instance) (k : ℕ), encodeInstance P k = w ∧ P.HasHittingSet k}

end Lax496464.HittingSet
