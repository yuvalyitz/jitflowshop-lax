import Lax496464.WH_A2_FptReductions

/-!
---
title: The Calculus of FPT-Reductions
type: theorem
---
The rules by which hardness results are combined and applied.

* Fpt-reducibility is reflexive and transitive [FG06, Lemma 2.3].
* **Hardness is inherited along reductions:** if $P$ is $C$-hard and $P \le^{\mathrm{fpt}} Q$, then
  $Q$ is $C$-hard. To show a new problem $C$-hard, reduce a known $C$-hard problem to it.
* If $Q$ is $C$-complete, a problem is $C$-hard exactly when $Q$ fpt-reduces to it.
* Membership in $[C]^{\mathrm{fpt}}$ is inherited backwards along reductions, and $[C]^{\mathrm{fpt}}$
  is monotone in $C$; a problem is $[C]^{\mathrm{fpt}}$-hard as soon as every member of $C$
  fpt-reduces to it.
* FPT is closed under fpt-reductions [FG06, Lemma 2.2], so a $C$-hard problem in FPT places all of
  $C$ in FPT. This is the sense in which W[1]-hardness is a lower bound.

# Formalization Notes

Each rule follows from the two machine facts of `WH_A4_MachineFacts` — the identity is computable,
and fixed-parameter computations compose — and none of the statements mentions a program.
-/

namespace Lax496464.WH_A3_ReductionCalculus

open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_A2_FptReductions

/-- **Reflexivity** [FG06, Lemma 2.3]. -/
axiom fptReduces_refl (P : Problem) : P ≤ᶠᵖᵗ P

/-- **Transitivity** [FG06, Lemma 2.3]. -/
axiom fptReduces_trans {P Q R : Problem} : P ≤ᶠᵖᵗ Q → Q ≤ᶠᵖᵗ R → P ≤ᶠᵖᵗ R

/-- **Hardness is inherited along fpt-reductions.** -/
axiom hard_of_fptReduces {C : Set Problem} {P Q : Problem} : Hard C P → P ≤ᶠᵖᵗ Q → Hard C Q

/-- A complete problem of a class is the only one that needs reducing: `P` is `C`-hard exactly
when the `C`-complete problem `Q` fpt-reduces to it. -/
axiom hard_iff_of_complete {C : Set Problem} {P Q : Problem} (hQ : Complete C Q) :
    Hard C P ↔ Q ≤ᶠᵖᵗ P

/-- A parameterized member of `C` belongs to `[C]^fpt`. -/
axiom mem_closure_of_mem {C : Set Problem} {P : Problem} :
    P ∈ C → IsParameterized P → P ∈ Closure C

/-- **Membership is inherited backwards along fpt-reductions.** -/
axiom mem_closure_of_fptReduces {C : Set Problem} {P Q : Problem} :
    IsParameterized P → P ≤ᶠᵖᵗ Q → Q ∈ Closure C → P ∈ Closure C

/-- `[·]^fpt` is monotone. -/
axiom closure_mono {C C' : Set Problem} : C ⊆ C' → Closure C ⊆ Closure C'

/-- To be `[C]^fpt`-hard it suffices that every member of `C` fpt-reduce. -/
axiom hard_closure_of {C : Set Problem} {Q : Problem} :
    (∀ P ∈ C, P ≤ᶠᵖᵗ Q) → Hard (Closure C) Q

/-- **FPT is closed under fpt-reductions** [FG06, Lemma 2.2]. -/
axiom mem_FPT_of_fptReduces {P Q : Problem} :
    IsParameterized P → P ≤ᶠᵖᵗ Q → Q ∈ FPT → P ∈ FPT

/-- **A hard problem in FPT collapses its class into FPT.** -/
axiom subset_FPT_of_hard {C : Set Problem} {Q : Problem} :
    (∀ P ∈ C, IsParameterized P) → Hard C Q → Q ∈ FPT → C ⊆ FPT

end Lax496464.WH_A3_ReductionCalculus
