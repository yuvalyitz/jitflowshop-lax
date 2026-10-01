import Lax496464.WH_B3_LogicProblems
import Lax496464.WH_A2_FptReductions

/-!
---
title: The W-hierarchy and the A-hierarchy
type: definition
---
For $t \ge 0$,

$$\mathrm{W}[t] := [\,p\text{-WD-}\Pi_t\,]^{\mathrm{fpt}}, \qquad
\mathrm{A}[t] := [\,p\text{-MC}(\Sigma_t)\,]^{\mathrm{fpt}}:$$

$\mathrm{W}[t]$ is the class of parameterized problems that fpt-reduce to $p\text{-WD}_\varphi$ for
some $\Pi_t$-sentence $\varphi(X)$ [FG06, Definition 5.1], and $\mathrm{A}[t]$ the class of those
that fpt-reduce to model checking for $\Sigma_t$-formulas [FG06, Definition 5.7].

This characterization of the W-hierarchy by weighted Fagin definability is equivalent to the
definition by weighted satisfiability of circuits of bounded weft [FG06, Theorems 5.6 and 7.20]. It
places the classes, the model-checking problems and the reductions between them on the same
objects, structures and first-order formulas.

# Formalization notes

$p\text{-WD-}\Pi_t$ (`pWDPi t`) is the set of problems $p\text{-WD}_\varphi$ for all
$\Pi_t$-sentences $\varphi$ and all arities of $X$; `W t` and `A t` are the closures of
`WH_A2_FptReductions.Closure`.
-/

namespace Lax496464.WH_B4_Hierarchies

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions
open Lax888481.ParameterizedComplexity (Problem)

/-- **`p-WD-Π_t`**: the weighted definability problems of `Π_t`-sentences. -/
def pWDPi (t : ℕ) : Set Problem :=
  {P | ∃ (φ : Formula) (s : ℕ), IsPi t φ ∧ IsSentence φ ∧ P = pWD φ s}

/-- **`W[t]`**, the `t`-th class of the W-hierarchy. -/
def W (t : ℕ) : Set Problem := Closure (pWDPi t)

/-- **`A[t]`**, the `t`-th class of the A-hierarchy. -/
noncomputable def A (t : ℕ) : Set Problem := Closure {pMC {φ | IsSigma t φ}}

end Lax496464.WH_B4_Hierarchies
