import Lax496464Proofs.Ram.F5MScan

/-!
# Theorem 5 (table of Section 3): small facts

The degenerate cases (no job or no machine) and the read-off of the scan.
-/

namespace Lax496464Proofs.F5MPre

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas
open Lax496464Proofs.F5Math
open Lax496464Proofs.Ram.D2Answer (hasWeight_trivial)

/-- With no job or no machine the scheme writes `0`. -/
theorem fptasOut_trivial (J : Instance) (e : ℕ) (h : J.jobs = 0 ∨ J.machines = 0) :
    fptasOut J e = 0 := by
  have hw : HasWeight (scaled J e) (scaledOpt J e) := (hasWeight_scaled J e _).mpr le_rfl
  have h0 : scaledOpt J e = 0 := (hasWeight_trivial (I := scaled J e) h _).mp hw
  unfold fptasOut
  rw [h0]
  split_ifs <;> simp

/-- The last non-zero cell of the column is the optimum. -/
theorem best_eq_m {W1 base opt best : ℕ} {T : List ℕ} (hopt : opt < W1)
    (hfin : ∀ c < W1, 0 < T.getD (base + c) 0 ↔ c ≤ opt)
    (hub : ∀ idx < W1, 0 < T.getD (base + idx) 0 → idx ≤ best)
    (hatt : best = 0 ∨ (best < W1 ∧ 0 < T.getD (base + best) 0)) : best = opt := by
  apply le_antisymm
  · rcases hatt with h | ⟨h1, h2⟩
    · omega
    · exact (hfin best h1).mp h2
  · exact hub opt hopt ((hfin opt hopt).mpr le_rfl)

end Lax496464Proofs.F5MPre
