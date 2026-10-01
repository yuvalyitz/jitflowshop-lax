import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_A6_ComputableBounds

/-! The calculus of fpt-reductions, from the two machine facts (the identity, composition) and
the monotone bound of a computable function. -/

namespace Lax496464Proofs.WHierarchy.Calculus

open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_A4_MachineFacts
open Lax496464.WH_A6_ComputableBounds

/-- The identity is an fpt-reduction from a problem to itself. -/
theorem isFptReduction_id (P : Problem) : IsFptReduction P P fun x => x :=
  ⟨⟨fun _ hx => hx, fun _ _ => Iff.rfl⟩, ⟨id, Computable.id, fun _ _ => le_rfl⟩,
    fptTimeOn_id _ _⟩

/-- The composite of two fpt-reductions is one. -/
theorem isFptReduction_comp {P Q R : Problem} {F G : List ℕ → List ℕ}
    (hF : IsFptReduction P Q F) (hG : IsFptReduction Q R G) :
    IsFptReduction P R fun x => G (F x) := by
  obtain ⟨⟨hFd, hFc⟩, ⟨g₁, hg₁, hb₁⟩, hFt⟩ := hF
  obtain ⟨⟨hGd, hGc⟩, ⟨g₂, hg₂, hb₂⟩, hGt⟩ := hG
  obtain ⟨G₂, hG₂c, hG₂m, hG₂b⟩ := exists_monotone_bound hg₂
  refine ⟨⟨fun x hx => hGd _ (hFd x hx), fun x hx => (hFc x hx).trans (hGc _ (hFd x hx))⟩,
    ⟨fun k => G₂ (g₁ k), hG₂c.comp hg₁, fun x hx => ?_⟩, fptTimeOn_comp hFt hFd hg₁ hb₁ hGt⟩
  exact (hb₂ _ (hFd x hx)).trans ((hG₂b _).trans (hG₂m (hb₁ x hx)))

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.fptReduces_refl
---
-/
theorem fptReduces_refl (P : Problem) : P ≤ᶠᵖᵗ P := ⟨_, isFptReduction_id P⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.fptReduces_trans
---
-/
theorem fptReduces_trans {P Q R : Problem} : P ≤ᶠᵖᵗ Q → Q ≤ᶠᵖᵗ R → P ≤ᶠᵖᵗ R :=
  fun ⟨_, hF⟩ ⟨_, hG⟩ => ⟨_, isFptReduction_comp hF hG⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces
---
-/
theorem hard_of_fptReduces {C : Set Problem} {P Q : Problem} :
    Hard C P → P ≤ᶠᵖᵗ Q → Hard C Q :=
  fun hP h R hR => fptReduces_trans (hP R hR) h

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.hard_iff_of_complete
---
-/
theorem hard_iff_of_complete {C : Set Problem} {P Q : Problem} (hQ : Complete C Q) :
    Hard C P ↔ Q ≤ᶠᵖᵗ P :=
  ⟨fun h => h Q hQ.1, fun h => hard_of_fptReduces hQ.2 h⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.mem_closure_of_mem
---
-/
theorem mem_closure_of_mem {C : Set Problem} {P : Problem} :
    P ∈ C → IsParameterized P → P ∈ Closure C :=
  fun hP hpar => ⟨hpar, P, hP, fptReduces_refl P⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.mem_closure_of_fptReduces
---
-/
theorem mem_closure_of_fptReduces {C : Set Problem} {P Q : Problem} :
    IsParameterized P → P ≤ᶠᵖᵗ Q → Q ∈ Closure C → P ∈ Closure C :=
  fun hpar h ⟨_, R, hR, hQR⟩ => ⟨hpar, R, hR, fptReduces_trans h hQR⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.closure_mono
---
-/
theorem closure_mono {C C' : Set Problem} : C ⊆ C' → Closure C ⊆ Closure C' :=
  fun h _ ⟨hpar, Q, hQ, hPQ⟩ => ⟨hpar, Q, h hQ, hPQ⟩

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.hard_closure_of
---
-/
theorem hard_closure_of {C : Set Problem} {Q : Problem} :
    (∀ P ∈ C, P ≤ᶠᵖᵗ Q) → Hard (Closure C) Q :=
  fun h _ ⟨_, R, hR, hPR⟩ => fptReduces_trans hPR (h R hR)

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.mem_FPT_of_fptReduces
---
-/
theorem mem_FPT_of_fptReduces {P Q : Problem} :
    IsParameterized P → P ≤ᶠᵖᵗ Q → Q ∈ FPT → P ∈ FPT := by
  classical
  rintro hpar ⟨R, ⟨hRd, hRc⟩, ⟨g, hg, hb⟩, hRt⟩ ⟨_, hQt⟩
  refine ⟨hpar, fptTimeOn_congr (fun x hx => ?_) (fptTimeOn_comp hRt hRd hg hb hQt)⟩
  by_cases h : P.Yes x
  · rw [if_pos ((hRc x hx).mp h), if_pos h]
  · rw [if_neg (fun h' => h ((hRc x hx).mpr h')), if_neg h]

/--
---
conclusion: Lax496464.WH_A3_ReductionCalculus.subset_FPT_of_hard
---
-/
theorem subset_FPT_of_hard {C : Set Problem} {Q : Problem} :
    (∀ P ∈ C, IsParameterized P) → Hard C Q → Q ∈ FPT → C ⊆ FPT :=
  fun hC hQ hfpt P hP => mem_FPT_of_fptReduces (hC P hP) (hQ P hP) hfpt

end Lax496464Proofs.WHierarchy.Calculus
