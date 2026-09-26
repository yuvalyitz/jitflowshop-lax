import Lax496464Proofs.Ram.D2Ach
import Lax496464Proofs.Ram.DpM

/-!
# Theorem 2: reading the answer off the column
-/

namespace Lax496464Proofs.Ram.D2Answer

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Ach

/-- With no job or no machine only the empty set is feasible. -/
theorem hasWeight_trivial {I : Instance} (h : I.jobs = 0 ∨ I.machines = 0) (W : ℕ) :
    HasWeight I W ↔ W = 0 := by
  constructor
  · rintro ⟨Z, hZ, hW⟩
    have hZe : Z = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      rcases h with h | h
      · exact absurd j.isLt (by omega)
      · obtain ⟨S⟩ := hZ
        have := S.mach_lt j hj
        omega
    subst hZe
    simp [weight] at hW
    omega
  · rintro rfl
    exact ⟨∅, ⟨⟨fun _ => 0, fun _ => 0, by simp, by simp, by simp, by simp, by simp⟩⟩, by simp⟩

/-- **The answer.** The entry at the threshold is non-zero iff a feasible set of weight at least
`W` exists. -/
theorem entry_ne_zero_iff {J : Instance} (hest : EstOrdered J) {inf t W : ℕ} (hinf : 0 < inf)
    (h : Rep inf t (fun P' => AchGe J (firstM J) W P')) :
    t ≠ 0 ↔ HasWeight J W := by
  rw [Dp1.rep_nonzero h hinf]
  constructor
  · rintro ⟨P', hP, W'', hW, hach⟩
    have := (Lax496464Proofs.Section3.achievable_readoff J hest W'').mp ⟨P', hP, hach⟩
    obtain ⟨Z, hZ, hwZ⟩ := this
    exact ⟨Z, hZ, by omega⟩
  · rintro ⟨Z, hZ, hW⟩
    obtain ⟨P', hP, hach⟩ := (Lax496464Proofs.Section3.achievable_readoff J hest (weight J Z)).mpr
      ⟨Z, hZ, rfl⟩
    exact ⟨P', hP, weight J Z, hW, hach⟩

end Lax496464Proofs.Ram.D2Answer
