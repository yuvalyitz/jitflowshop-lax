import Lax496464.WH_D01_CliqueInW1

/-!
---
title: Clique Is in A[1]
type: theorem
---
$p$-Clique is in A[1] [FG06, Example 5.8]: a graph has a clique of $k$ vertices exactly when it
satisfies the $\Sigma_1$-sentence

$$\mathrm{clique}_k \;=\; \exists x_1 \dots \exists x_k \Big(\bigwedge_{1 \le i < j \le k} \neg\, x_i = x_j
\;\wedge \bigwedge_{1 \le i < j \le k} E x_i x_j\Big),$$

so $(G, k) \mapsto (G, \mathrm{clique}_k)$ is an fpt-reduction from $p$-Clique to
$p\text{-MC}(\Sigma_1)$. The formula depends on $k$ only and has size $O(k^2)$, the new parameter.
-/

namespace Lax496464.WH_D02_CliqueInA1

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- **The reduction:** `p-Clique ≤fpt p-MC(Σ_1)`. -/
axiom clique_le_pMC : Clique ≤ᶠᵖᵗ pMC {φ | IsSigma 1 φ}

/-- **`p-Clique ∈ A[1]`.** -/
axiom clique_mem_A1 : Clique ∈ A 1

end Lax496464.WH_D02_CliqueInA1
