import Lax496464.WH_B4_Hierarchies

/-!
---
title: Basic Facts About the Hierarchies
type: theorem
---
* The defining problems are parameterized problems: the parameters of $p\text{-WD}_\varphi$ (the
  last entry) and of $p\text{-MC}(\Phi)$ (the size of the formula) are computable in polynomial time.
  Hence $p\text{-WD}_\varphi \in \mathrm{W}[t]$ for every $\Pi_t$-sentence $\varphi$, and
  $p\text{-MC}(\Sigma_t) \in \mathrm{A}[t]$.
* Model checking for a class of formulas fpt-reduces to model checking for any larger class.
* The hierarchies are increasing: $\mathrm{W}[t] \subseteq \mathrm{W}[t+1]$ and
  $\mathrm{A}[t] \subseteq \mathrm{A}[t+1]$.
* **Conditional lower bounds.** A $\mathrm{W}[t]$-hard problem in FPT places all of $\mathrm{W}[t]$
  in FPT; so, unless $\mathrm{W}[t] \subseteq \mathrm{FPT}$, no $\mathrm{W}[t]$-hard problem is
  fixed-parameter tractable.
-/

namespace Lax496464.WH_B5_HierarchyFacts

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions
open Lax888481.ParameterizedComplexity (Problem)

/-- The parameter of a weighted definability problem is computable in polynomial time. -/
axiom pWD_isParameterized (φ : Formula) (s : ℕ) : IsParameterized (pWD φ s)

/-- The parameter of a model-checking problem is computable in polynomial time. -/
axiom pMC_isParameterized (Φ : Set Formula) : IsParameterized (pMC Φ)

/-- Model checking for a class fpt-reduces to model checking for a larger class. -/
axiom pMC_mono {Φ Φ' : Set Formula} : Φ ⊆ Φ' → pMC Φ ≤ᶠᵖᵗ pMC Φ'

/-- `p-WD_φ ∈ W[t]` for every `Π_t`-sentence `φ`. -/
axiom pWD_mem_W {t : ℕ} {φ : Formula} (s : ℕ) : IsPi t φ → IsSentence φ → pWD φ s ∈ W t

/-- `p-MC(Σ_t) ∈ A[t]`. -/
axiom pMC_mem_A (t : ℕ) : pMC {φ | IsSigma t φ} ∈ A t

/-- The W-hierarchy is increasing. -/
axiom W_mono (t : ℕ) : W t ⊆ W (t + 1)

/-- The A-hierarchy is increasing. -/
axiom A_mono (t : ℕ) : A t ⊆ A (t + 1)

/-- **A `W[t]`-hard problem in FPT puts `W[t]` into FPT.** -/
axiom W_subset_FPT_of_hard {t : ℕ} {P : Problem} : Hard (W t) P → P ∈ FPT → W t ⊆ FPT

/-- **Unless `W[t] ⊆ FPT`, no `W[t]`-hard problem is fixed-parameter tractable.** -/
axiom not_mem_FPT_of_hard {t : ℕ} {P : Problem} : ¬ W t ⊆ FPT → Hard (W t) P → P ∉ FPT

end Lax496464.WH_B5_HierarchyFacts
