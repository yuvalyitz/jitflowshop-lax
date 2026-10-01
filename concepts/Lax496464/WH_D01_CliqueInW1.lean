import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C1_GraphProblems

/-!
---
title: Clique is in W[1]
type: theorem
---
$p$-Clique is in W[1] [FG06, Example 5.2]. A set $X$ of vertices is a clique exactly when the graph
satisfies the $\Pi_1$-sentence [FG06, Example 4.39]

$$\mathrm{clique}(X) \;=\; \forall y\,\forall z\,\big((Xy \wedge Xz \wedge \neg\, y = z) \to Eyz\big),$$

so $p$-Clique fpt-reduces to $p\text{-WD}_{\mathrm{clique}}$: the graph becomes the structure whose
universe is its vertex set and whose one relation is its edge relation, and $k$ is unchanged.

# Formalization notes

In `cliqueFormula` the variables $y, z$ are $0, 1$, the edge relation $E$ is the binary symbol $0$,
and $X$ is unary. The edge relation contains both $(u, v)$ and $(v, u)$ for every edge $uv$.
-/

namespace Lax496464.WH_D01_CliqueInW1

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems

/-- `clique(X) = ∀y ∀z ((Xy ∧ Xz ∧ ¬ y = z) → E y z)`. -/
def cliqueFormula : Formula :=
  .all 0 (.all 1 (Formula.imp
    (.and (.setVar [0]) (.and (.setVar [1]) (.neg (.eq 0 1))))
    (.rel 0 [0, 1])))

/-- `clique(X)` is a `Π_1`-formula. -/
axiom cliqueFormula_isPi : IsPi 1 cliqueFormula

/-- `clique(X)` is a sentence. -/
axiom cliqueFormula_isSentence : IsSentence cliqueFormula

/-- The parameter of `p-Clique` is computable in polynomial time. -/
axiom clique_isParameterized : IsParameterized Clique

/-- **The reduction:** `p-Clique ≤fpt p-WD_clique`. -/
axiom clique_le_pWD : Clique ≤ᶠᵖᵗ pWD cliqueFormula 1

/-- **`p-Clique ∈ W[1]`.** -/
axiom clique_mem_W1 : Clique ∈ W 1

end Lax496464.WH_D01_CliqueInW1
