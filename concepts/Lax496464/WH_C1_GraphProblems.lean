import Lax888481.ParameterizedComplexity
import Lax271696.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: Clique, Independent Set and Dominating Set
type: definition
---
Three graph problems parameterized by the solution size [FG06, Section 1.2].

**$p$-Clique.** *Instance:* a graph $G$ and $k \in \mathbb N$. *Parameter:* $k$. *Question:* does
$G$ have a clique of $k$ vertices?

**$p$-Independent-Set.** The same with $k$ pairwise non-adjacent vertices.

**$p$-Dominating-Set.** The same with $k$ vertices such that every vertex is one of them or adjacent
to one of them.

# Formalization Notes

The three problems share the archive's format for a graph with a parameter
(`Lax271696.VertexCover.EncodesParamInstance`): the compressed sparse row encoding of the graph
followed by $k$. The parameter is the last entry. Solution sizes are exact; for cliques and
independent sets this is equivalent to "at least $k$", and for dominating sets to "at most $k$"
whenever $k$ does not exceed the number of vertices.

Multicoloured Clique is the archive's `Lax888481.MulticolouredClique.problem`, on the same graph
encoding followed by the colours (`WH_D12_MulticolouredClique`).
-/

namespace Lax496464.WH_C1_GraphProblems

open Lax271696.VertexCover
open Lax888481.ParameterizedComplexity (Problem)

/-- The words that present a graph with a parameter. -/
def GraphInstances : Set (List ℕ) := {x | ∃ n G k, EncodesParamInstance x n G k}

/-- **`p-Clique`**. -/
def Clique : Problem where
  Domain := GraphInstances
  Yes x := ∃ n G k, EncodesParamInstance x n G k ∧ ∃ s : Finset (Fin n), G.IsNClique k s
  param x := x.getLast?.getD 0

/-- **`p-Independent-Set`**. -/
def IndependentSet : Problem where
  Domain := GraphInstances
  Yes x := ∃ n G k, EncodesParamInstance x n G k ∧ ∃ s : Finset (Fin n), Gᶜ.IsNClique k s
  param x := x.getLast?.getD 0

/-- **`p-Dominating-Set`**. -/
def DominatingSet : Problem where
  Domain := GraphInstances
  Yes x := ∃ n G k, EncodesParamInstance x n G k ∧
    ∃ s : Finset (Fin n), s.card = k ∧ ∀ v, v ∈ s ∨ ∃ u ∈ s, G.Adj u v
  param x := x.getLast?.getD 0

end Lax496464.WH_C1_GraphProblems
