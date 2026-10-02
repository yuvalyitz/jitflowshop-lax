import Lax496464.WH_D02_CliqueInA1

/-!
---
title: Clique Is A[1]-Complete
type: theorem
---
$p$-Clique is A[1]-complete under fpt-reductions [FG06, Theorem 6.1].

It is in A[1] (`WH_D02_CliqueInA1`), and it is A[1]-hard by the chain

$$p\text{-MC}(\Sigma_1) \le p\text{-MC}(\Sigma_1^+) \le p\text{-MC}(\Sigma_1^+[2]) \le
p\text{-MC}(\Sigma_1[2]) \le p\text{-Clique}$$

of `WH_D03_NegationElimination`, `WH_D04_IncidenceStructure`, the inclusion
$\Sigma_1^+[2] \subseteq \Sigma_1[2]$, and `WH_D05_BinaryToClique`.
-/

namespace Lax496464.WH_D06_CliqueA1Complete

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- **`p-Clique` is A[1]-complete** [FG06, Theorem 6.1]. -/
axiom clique_A1_complete : Complete (A 1) Clique

end Lax496464.WH_D06_CliqueA1Complete
