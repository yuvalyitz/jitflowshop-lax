import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C1_GraphProblems

/-!
---
title: Independent Set Is W[1]-Complete
type: theorem
---
$p$-Independent-Set is W[1]-complete under fpt-reductions [FG06, Corollary 6.2].

A set of vertices is independent in $G$ exactly when it is a clique in the complement $\overline G$, so
$(G, k) \mapsto (\overline G, k)$ reduces each problem to the other. The complement is computable in
polynomial time and the parameter is unchanged. Completeness follows from that of Clique
(`WH_D10_CliqueW1Complete`).
-/

namespace Lax496464.WH_D11_IndependentSet

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- The parameter of `p-Independent-Set` is computable in polynomial time. -/
axiom independentSet_isParameterized : IsParameterized IndependentSet

/-- **`p-Clique ≤fpt p-Independent-Set`**, by the complement graph. -/
axiom clique_le_independentSet : Clique ≤ᶠᵖᵗ IndependentSet

/-- **`p-Independent-Set ≤fpt p-Clique`**, by the complement graph. -/
axiom independentSet_le_clique : IndependentSet ≤ᶠᵖᵗ Clique

/-- **`p-Independent-Set` is W[1]-complete.** -/
axiom independentSet_W1_complete : Complete (W 1) IndependentSet

end Lax496464.WH_D11_IndependentSet
