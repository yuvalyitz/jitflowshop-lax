import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C1_GraphProblems
import Lax496464.WH_C2_HittingSet

/-!
---
title: Dominating Set is W[2]-complete
type: theorem
---
$p$-Dominating-Set is W[2]-complete under fpt-reductions [FG06, Corollary 7.15]: it is
fpt-equivalent to $p$-Hitting-Set [FG06, Example 2.7], which is W[2]-complete
(`WH_E2_HittingSetW2Complete`).

* **Dominating Set $\le$ Hitting Set.** The universe is the vertex set, and the hyperedges are the
  closed neighbourhoods $N[v]$: a set dominates the graph exactly when it meets every $N[v]$.
* **Hitting Set $\le$ Dominating Set.** The graph has a vertex for every element and every hyperedge;
  the elements form a clique, and an element is joined to the hyperedges containing it. A hitting
  set of $k$ elements dominates the graph; conversely, a dominating set of $k$ vertices yields a
  hitting set of $k$ elements by replacing each hyperedge-vertex by an element of that hyperedge.
  The universe is first restricted to the elements occurring in the sets; instances with an empty
  hyperedge or with $k$ larger than the universe are mapped to a fixed no-instance.
-/

namespace Lax496464.WH_E3_DominatingSet

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions
open Lax496464.WH_C1_GraphProblems Lax496464.WH_C2_HittingSet

/-- The parameter of `p-Dominating-Set` is computable in polynomial time. -/
axiom dominatingSet_isParameterized : IsParameterized DominatingSet

/-- **`p-Dominating-Set ≤fpt p-Hitting-Set`**, by closed neighbourhoods. -/
axiom dominatingSet_le_hittingSet : DominatingSet ≤ᶠᵖᵗ HittingSet

/-- **`p-Hitting-Set ≤fpt p-Dominating-Set`** [FG06, Example 2.7]. -/
axiom hittingSet_le_dominatingSet : HittingSet ≤ᶠᵖᵗ DominatingSet

/-- **`p-Dominating-Set` is W[2]-complete** [FG06, Corollary 7.15]. -/
axiom dominatingSet_W2_complete : Complete (W 2) DominatingSet

end Lax496464.WH_E3_DominatingSet
