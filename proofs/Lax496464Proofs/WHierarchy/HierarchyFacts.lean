import Lax496464.WH_B5_HierarchyFacts
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts

/-! The basic facts about the hierarchies that follow from the calculus of reductions and from the
syntax of `Σ_t` and `Π_t`. -/

namespace Lax496464Proofs.WHierarchy.HierarchyFacts

open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_A3_ReductionCalculus Lax496464.WH_A4_MachineFacts
open Lax496464.WH_B5_HierarchyFacts

/-- One more level, with either kind of first block: an empty block of the other kind in
front. -/
theorem alt_succ : ∀ (t : ℕ) (b : Bool) (φ : Formula),
    Alt b t φ → Alt b (t + 1) φ ∧ Alt (!b) (t + 1) φ
  | 0, true, φ, h => ⟨⟨[], φ, rfl, h⟩, ⟨[], φ, rfl, h⟩⟩
  | 0, false, φ, h => ⟨⟨[], φ, rfl, h⟩, ⟨[], φ, rfl, h⟩⟩
  | t + 1, true, φ, ⟨xs, ψ, hφ, hψ⟩ =>
    ⟨⟨xs, ψ, hφ, (alt_succ t false ψ hψ).1⟩, ⟨[], φ, rfl, ⟨xs, ψ, hφ, hψ⟩⟩⟩
  | t + 1, false, φ, ⟨xs, ψ, hφ, hψ⟩ =>
    ⟨⟨xs, ψ, hφ, (alt_succ t true ψ hψ).1⟩, ⟨[], φ, rfl, ⟨xs, ψ, hφ, hψ⟩⟩⟩

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.pMC_mono
---
-/
theorem pMC_mono {Φ Φ' : Set Formula} (h : Φ ⊆ Φ') : pMC Φ ≤ᶠᵖᵗ pMC Φ' :=
  ⟨fun x => x,
    ⟨fun _ ⟨A, φ, he, hφ, hn⟩ => ⟨A, φ, he, h hφ, hn⟩, fun _ _ => Iff.rfl⟩,
    ⟨id, Computable.id, fun _ _ => le_rfl⟩, fptTimeOn_id _ _⟩

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.pWD_mem_W
---
-/
theorem pWD_mem_W {t : ℕ} {φ : Formula} (s : ℕ) (hφ : IsPi t φ) (hs : IsSentence φ) :
    pWD φ s ∈ W t :=
  mem_closure_of_mem ⟨φ, s, hφ, hs, rfl⟩ (pWD_isParameterized φ s)

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.pMC_mem_A
---
-/
theorem pMC_mem_A (t : ℕ) : pMC {φ | IsSigma t φ} ∈ A t :=
  mem_closure_of_mem (Set.mem_singleton _) (pMC_isParameterized _)

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.W_mono
---
-/
theorem W_mono (t : ℕ) : W t ⊆ W (t + 1) :=
  closure_mono fun _ ⟨φ, s, hφ, hs, hP⟩ => ⟨φ, s, (alt_succ t false φ hφ).1, hs, hP⟩

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.A_mono
---
-/
theorem A_mono (t : ℕ) : A t ⊆ A (t + 1) := by
  rintro P ⟨hpar, Q, hQ, hPQ⟩
  rw [Set.mem_singleton_iff] at hQ
  subst hQ
  exact ⟨hpar, _, Set.mem_singleton _,
    fptReduces_trans hPQ (pMC_mono fun φ hφ => (alt_succ t true φ hφ).1)⟩

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.W_subset_FPT_of_hard
---
-/
theorem W_subset_FPT_of_hard {t : ℕ} {P : Problem} : Hard (W t) P → P ∈ FPT → W t ⊆ FPT :=
  subset_FPT_of_hard fun _ hQ => hQ.1

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.not_mem_FPT_of_hard
---
-/
theorem not_mem_FPT_of_hard {t : ℕ} {P : Problem} : ¬ W t ⊆ FPT → Hard (W t) P → P ∉ FPT :=
  fun hW hP hfpt => hW (W_subset_FPT_of_hard hP hfpt)

end Lax496464Proofs.WHierarchy.HierarchyFacts
