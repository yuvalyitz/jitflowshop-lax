import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C1_GraphProblems
import Lax888481.MulticolouredClique

/-!
---
title: Multicoloured Clique Is W[1]-Complete
type: theorem
---
Multicoloured Clique — given a graph whose vertices are properly coloured with $k$ colours, is
there a clique with one vertex of each colour? — is W[1]-complete under fpt-reductions,
parameterized by $k$ [CFK+15, Theorem 13.7]. It is the usual starting point of W[1]-hardness
proofs.

* **$p$-Clique $\le$ Multicoloured Clique.** Take $k$ copies of the vertex set, copy $c$ coloured $c$,
  and join $(c, u)$ and $(c', v)$ when $c \ne c'$ and $uv$ is an edge. A multicoloured clique picks
  $k$ distinct pairwise adjacent vertices, and conversely.
* **Multicoloured Clique $\le$ $p$-Clique.** Forget the colours: adjacent vertices have different
  colours, so a clique of $k$ vertices in a $k$-coloured graph has one vertex of each colour.

# Formalization Notes

Multicoloured Clique is the archive's `Lax888481.MulticolouredClique.problem`: the compressed sparse
row encoding with sorted adjacency lists, one colour per vertex, and the number of colours.
-/

namespace Lax496464.WH_D12_MulticolouredClique

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- The parameter of Multicoloured Clique is computable in polynomial time. -/
axiom multicolouredClique_isParameterized :
    IsParameterized Lax888481.MulticolouredClique.problem

/-- **`p-Clique ≤fpt Multicoloured Clique`.** -/
axiom clique_le_multicolouredClique : Clique ≤ᶠᵖᵗ Lax888481.MulticolouredClique.problem

/-- **`Multicoloured Clique ≤fpt p-Clique`.** -/
axiom multicolouredClique_le_clique : Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ Clique

/-- **Multicoloured Clique is W[1]-complete.** -/
axiom multicolouredClique_W1_complete : Complete (W 1) Lax888481.MulticolouredClique.problem

end Lax496464.WH_D12_MulticolouredClique
