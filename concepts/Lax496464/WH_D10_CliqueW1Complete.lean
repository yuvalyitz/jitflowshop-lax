import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C1_GraphProblems

/-!
---
title: Clique Is W[1]-Complete
type: theorem
---
$p$-Clique is W[1]-complete under fpt-reductions [FG06, Theorems 6.1 and 6.35]: it is in W[1]
(`WH_D01_CliqueInW1`), and it is W[1]-hard since it is A[1]-hard (`WH_D06_CliqueA1Complete`) and
W[1] = A[1] (`WH_D09_W1EqA1`).

A problem is W[1]-hard as soon as Clique, or any other W[1]-hard problem, fpt-reduces to it
(`WH_A3_ReductionCalculus.hard_of_fptReduces`); it is then not fixed-parameter tractable unless
$\mathrm{W}[1] \subseteq \mathrm{FPT}$ (`WH_B5_HierarchyFacts.not_mem_FPT_of_hard`).
-/

namespace Lax496464.WH_D10_CliqueW1Complete

open Lax496464.WH_B4_Hierarchies Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- **`p-Clique` is W[1]-complete.** -/
axiom clique_W1_complete : Complete (W 1) Clique

/-- **`p-Clique` is W[1]-hard.** -/
axiom clique_W1_hard : Hard (W 1) Clique

end Lax496464.WH_D10_CliqueW1Complete
