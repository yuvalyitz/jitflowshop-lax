import Lax888481.ParameterizedComplexity
import Lax496464.HittingSet

/-!
---
title: Hitting Set
type: definition
---
**$p$-Hitting-Set.** *Instance:* a hypergraph — a universe and a family of subsets of it — and
$k \in \mathbb N$. *Parameter:* $k$. *Question:* is there a set of $k$ elements of the universe that
meets every set of the family? [FG06, Example 4.42]

# Formalization Notes

The instances and the question are those of the Hitting Set of the just-in-time flow shop part of
this submission (`Lax496464.HittingSet`): a universe $\{0,\dots,n-1\}$, sets
$F_0,\dots,F_{m-1}$ and an exact size $k$. The word is its binary encoding of the instance with $k$,
each bit written as the number $0$ or $1$. Hardness results for this problem are therefore results
about the problem the flow shop reductions start from.

The binary code is prefix-free, so a word encodes at most one instance and one $k$; the parameter
of a word is the $k$ it encodes. Since $n$ and $k$ are written in binary, a reduction from this
problem that ranges over the universe first restricts it to the elements occurring in the sets.
-/

namespace Lax496464.WH_C2_HittingSet

open Lax496464.HittingSet
open Lax888481.ParameterizedComplexity (Problem)

/-- The word of an instance with solution size `k`: its binary word, one number `0` or `1` per
bit. -/
def word (P : Instance) (k : ℕ) : List ℕ := (encodeInstance P k).map fun b => if b then 1 else 0

open Classical in
/-- The solution size a word encodes (`0` on other words). -/
noncomputable def sizeParam (x : List ℕ) : ℕ :=
  if h : ∃ p : Instance × ℕ, x = word p.1 p.2 then (Classical.choose h).2 else 0

/-- **`p-Hitting-Set`**. -/
noncomputable def HittingSet : Problem where
  Domain := {x | ∃ P k, x = word P k}
  Yes x := ∃ P k, x = word P k ∧ P.HasHittingSet k
  param := sizeParam

end Lax496464.WH_C2_HittingSet
