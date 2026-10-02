import Lax496464Proofs.Ram.SegProg
import Lax496464Proofs.Ram.T4Trees

/-!
# Theorem 4's Machine, Part 1: the Trees as Sets

`TreeOK` says that the array `a` is a maximum tree whose leaves are a given function and
whose cells all fit in a word; `tset`/`tfind` (`Ram/SegProg.lean`) are restated on it, and
`dropLeaf` — clear one leaf from both trees — is proved once.
-/

namespace Lax496464Proofs.Ram.T4Defs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax496464Proofs.Ram.SegTree Lax496464Proofs.Ram.SegProg Lax496464Proofs.Ram.T4Trees

/-- The array `a` is a maximum tree over `2^h` leaves whose leaves are `f`, cells below `B`. -/
def TreeOK (a : String) (h : ℕ) (f : ℕ → ℕ) (B : ℕ) (σ : Env) : Prop :=
  Cons (σ.arrs a) h ∧ Leaves (σ.arrs a) h f ∧ ∀ x ∈ σ.arrs a, x < B

/-- Store `v` in leaf `pos` of the tree `a`, on the machine. -/
theorem tset_tree {B : ℕ} (a : String) (h pos v : ℕ) (f : ℕ → ℕ) (hB : 2 * 2 ^ h + 2 < B)
    (hvB : v < B) (hpos : pos < 2 ^ h) :
    Spec B (fun σ => σ.vars "tN" = 2 ^ h ∧ σ.vars "th" = h ∧ σ.vars "tp" = pos ∧
        σ.vars "tv" = v ∧ TreeOK a h f B σ) (tset a)
      (fun _ σ' => TreeOK a h (upd f pos v) B σ') (68 * h + 40) := by
  refine (tset_spec a h pos v hB hvB hpos).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hN, hth, hp, hv, hC, hL, hAB⟩
    exact ⟨hN, hth, hp, hv, hC, hAB⟩
  · rintro σ σ' ⟨hN, hth, hp, hv, hC, hL, hAB⟩ ⟨hC', hpv, hrest, hAB'⟩
    refine ⟨hC', fun ℓ hℓ => ?_, hAB'⟩
    by_cases hℓp : ℓ = pos
    · subst hℓp; rw [hpv]; simp
    · rw [hrest _ (by omega) (by omega), hL ℓ hℓ]; simp [hℓp]

/-- Clear the leaf `ti - tN` from both trees. -/
def dropLeaf : Com :=
  .seq (.assign "tp" (.bin .sub (V "ti") (V "tN")))
    (.seq (.assign "tv" (.lit 0)) (.seq (tset "TX") (tset "TY")))

theorem dropLeaf_spec {B : ℕ} (h ℓ : ℕ) (f g : ℕ → ℕ) (hB : 2 * 2 ^ h + 2 < B) (hℓ : ℓ < 2 ^ h) :
    Spec B (fun σ => σ.vars "tN" = 2 ^ h ∧ σ.vars "th" = h ∧ σ.vars "ti" = 2 ^ h + ℓ ∧
        TreeOK "TX" h f B σ ∧ TreeOK "TY" h g B σ) dropLeaf
      (fun _σ σ' => TreeOK "TX" h (upd f ℓ 0) B σ' ∧ TreeOK "TY" h (upd g ℓ 0) B σ' ∧
        σ'.vars "tN" = 2 ^ h ∧ σ'.vars "th" = h) (136 * h + 86) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hN, hth, hti, hX, hY⟩ := hσ
  have hvI : (V "ti").evalB B σ = some (2 ^ h + ℓ) := hti ▸ evalB_var (by rw [hti]; omega)
  have hvN : (V "tN").evalB B σ = some (2 ^ h) := hN ▸ evalB_var (by rw [hN]; omega)
  have hr1 : Run B (.assign "tp" (.bin .sub (V "ti") (V "tN"))) σ (σ.setVar "tp" ℓ) 4 :=
    Run.assign (v := ℓ) (evalB_bin hvI hvN (by rw [Bop.apply_sub]; omega) |>.trans (by
      simp))
  set σ1 := σ.setVar "tp" ℓ with hσ1
  have hr2 : Run B (.assign "tv" (.lit 0)) σ1 (σ1.setVar "tv" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  set σ2 := σ1.setVar "tv" 0 with hσ2
  have hX2 : TreeOK "TX" h f B σ2 := by simpa [hσ2, hσ1, TreeOK] using hX
  have hY2 : TreeOK "TY" h g B σ2 := by simpa [hσ2, hσ1, TreeOK] using hY
  obtain ⟨σ3, hr3, hX3⟩ := (tset_tree "TX" h ℓ 0 f hB (by omega) hℓ).run
    ⟨by simp [hσ2, hσ1, hN], by simp [hσ2, hσ1, hth], by simp [hσ2, hσ1], by simp [hσ2], hX2⟩
  have hY3 : TreeOK "TY" h g B σ3 := by
    have := hr3.frame_arr "TY" (by decide)
    unfold TreeOK; rw [this]; exact hY2
  have hN3 : σ3.vars "tN" = 2 ^ h := by rw [hr3.frame_var "tN" (by decide)]; simp [hσ2, hσ1, hN]
  have hth3 : σ3.vars "th" = h := by rw [hr3.frame_var "th" (by decide)]; simp [hσ2, hσ1, hth]
  have hp3 : σ3.vars "tp" = ℓ := by rw [hr3.frame_var "tp" (by decide)]; simp [hσ2, hσ1]
  obtain ⟨σ4, hr4, hY4⟩ := (tset_tree "TY" h ℓ 0 g hB (by omega) hℓ).run
    ⟨hN3, hth3, hp3, by rw [hr3.frame_var "tv" (by decide)]; simp [hσ2], hY3⟩
  have hX4 : TreeOK "TX" h (upd f ℓ 0) B σ4 := by
    have := hr4.frame_arr "TX" (by decide)
    unfold TreeOK; rw [this]; exact hX3
  refine ⟨σ4, _, (hr1.seq (hr2.seq (hr3.seq hr4))).mono (by omega), le_rfl, hX4, hY4, ?_, ?_⟩
  · rw [hr4.frame_var "tN" (by decide)]; exact hN3
  · rw [hr4.frame_var "th" (by decide)]; exact hth3

end Lax496464Proofs.Ram.T4Defs
