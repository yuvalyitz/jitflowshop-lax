import Lax496464.WH_B4_Hierarchies

/-!
---
title: W[1] = A[1]
type: theorem
---
The first level of the W-hierarchy equals the first level of the A-hierarchy [FG06, Theorem 6.35].

* $\mathrm{A}[1] \subseteq \mathrm{W}[1]$: every problem of A[1] fpt-reduces to Clique
  (`WH_D06_CliqueA1Complete`), which is in W[1] (`WH_D01_CliqueInW1`).
* $\mathrm{W}[1] \subseteq \mathrm{A}[1]$: every problem of W[1] fpt-reduces to some
  $p\text{-WD}_\varphi$ with $\varphi \in \Pi_1$, which fpt-reduces to $p\text{-WSat}(d\text{-CNF})$
  (`WH_D07_DefinabilityToWSat`), which is in A[1] (`WH_D08_WSatInA1`).
-/

namespace Lax496464.WH_D09_W1EqA1

open Lax496464.WH_B4_Hierarchies

/-- **`W[1] = A[1]`** [FG06, Theorem 6.35]. -/
axiom W1_eq_A1 : W 1 = A 1

end Lax496464.WH_D09_W1EqA1
