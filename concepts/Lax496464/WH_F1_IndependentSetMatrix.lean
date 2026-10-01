import Lax762056.GraphProblems
import Lax888481.ParameterizedComplexity

/-!
---
title: Independent Set on adjacency matrices
type: definition
---
**$p$-Independent-Set.** *Instance:* a graph $G$ on $n$ vertices and $k \in \mathbb N$.
*Parameter:* $k$. *Question:* does $G$ have an independent set of at least $k$ vertices?
[FG06, Section 1.2]

This is the source problem of the reduction to Multicoloured Clique in part F.

# Formalization notes

**Instances and question** are those of the archive's Independent Set (`Lax762056.GraphProblems`),
whose NP-hardness is proved there. An instance is written as the bit string
$1^n\,0\,A\,1^k\,0$: the order $n$ in unary, the $n^2$ entries of the adjacency matrix $A$ in row
order, and $k$ in unary.

**Words.** The word of an instance is this bit string with each bit written as the number $0$ or
$1$, and the instances are exactly the words of this form. The parameter of a word is the length of
the run of ones that ends just before its last entry; on the word of an instance it is $k$, since
the last matrix entry is a diagonal entry and hence $0$.

**Relation to `WH_C1_GraphProblems.IndependentSet`.** That problem asks the same question for an
exact solution size, on compressed sparse row words. The two problems differ only in the encoding.
-/

namespace Lax496464.WH_F1_IndependentSetMatrix

open Lax762056.GraphEncoding Lax888481.ParameterizedComplexity

/-- A bit as a number. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- The word of an instance: its adjacency-matrix encoding, one number `0` or `1` per bit. -/
noncomputable def word (I : Instance) : List ℕ := (encode I).map bitNat

/-- The words that present an instance. -/
def Instances : Set (List ℕ) := Set.range word

/-- The parameter `k` of a word: the run of ones ending just before its last entry. -/
def threshold (x : List ℕ) : ℕ := (x.dropLast.reverse.takeWhile fun v => v == 1).length

/-- **`p-Independent-Set`** on adjacency-matrix words. -/
def problem : Problem where
  Domain := Instances
  Yes x := ∃ I, x = word I ∧ Lax762056.GraphProblems.IndependentSet I
  param := threshold

end Lax496464.WH_F1_IndependentSetMatrix
