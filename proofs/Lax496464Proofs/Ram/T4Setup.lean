import Lax496464Proofs.Ram.T4Job
import Lax496464Proofs.Ram.BitsNat

/-!
# Theorem 4's machine, part 5: the height of the trees, and the answer
-/

namespace Lax496464Proofs.Ram.T4Setup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.SegProg (V bump)

/-- `tN := 2^th` with `th` the least height such that `n ≤ 2^th`. -/
def sizeLoop : Com :=
  .seq (.assign "tN" (.lit 1)) (.seq (.assign "th" (.lit 0))
    (.while (.lt (V "tN") (V "n"))
      (.seq (.assign "tN" (.bin .mul (V "tN") (.lit 2))) (bump "th"))))

theorem lt_size_of {n t : ℕ} (h : 2 ^ t < n) : t + 1 ≤ (n - 1).size := by
  have : 2 ^ t ≤ n - 1 := by omega
  exact Nat.lt_size.mpr this

theorem size_le_of {n t : ℕ} (h : n ≤ 2 ^ t) : (n - 1).size ≤ t := by
  apply Nat.size_le.mpr
  have : 0 < 2 ^ t := by positivity
  omega

/-- The loop invariant. -/
def SI (n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "tN" = 2 ^ σ.vars "th" ∧ σ.vars "th" ≤ (n - 1).size

theorem two_pow_size_le (n : ℕ) : 2 ^ (n - 1).size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
  · rw [h0]; simp
  · have hs : 1 ≤ (n - 1).size := by rw [Nat.one_le_iff_ne_zero]; intro h; rw [Nat.size_eq_zero] at h; omega
    have h1 : 2 ^ ((n - 1).size - 1) ≤ n - 1 := Nat.lt_size.mp (by omega)
    have h2 : 2 ^ (n - 1).size = 2 * 2 ^ ((n - 1).size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem sizeBody_spec {B n : ℕ} (hnB : 2 * n + 4 < B) :
    Spec B (fun σ => SI n σ ∧ (Cond.lt (V "tN") (V "n")).evalB B σ = some true)
      (.seq (.assign "tN" (.bin .mul (V "tN") (.lit 2))) (bump "th"))
      (fun σ σ' => SI n σ' ∧ (n - 1).size - σ'.vars "th" < (n - 1).size - σ.vars "th") 8 := by
  refine Spec.of_exists fun σ ⟨⟨hn, hN, hth⟩, hc⟩ => ?_
  have hlt : σ.vars "tN" < σ.vars "n" := by
    simp only [evalB_condLt_iff, evalB_var_iff] at hc
    obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := hc
    simpa using hr.symm
  rw [hn] at hlt
  have hsz := lt_size_of (n := n) (t := σ.vars "th") (by rw [← hN]; exact hlt)
  have hsle := Lax496464Proofs.Ram.BitsNat.size_le_self (n - 1)
  have hthB : σ.vars "th" + 1 < B := by omega
  have hNB : σ.vars "tN" < B := by omega
  have hv1 : (V "tN").evalB B σ = some (σ.vars "tN") := evalB_var hNB
  have hr1 : Run B (.assign "tN" (.bin .mul (V "tN") (.lit 2))) σ
      (σ.setVar "tN" (σ.vars "tN" * 2)) 4 :=
    Run.assign (evalB_bin hv1 (evalB_lit (by omega)) (by rw [Bop.apply_mul]; omega))
  set σ1 := σ.setVar "tN" (σ.vars "tN" * 2) with hσ1
  have hthv : (V "th").evalB B σ1 = some (σ.vars "th") := by
    have : σ1.vars "th" = σ.vars "th" := by simp [hσ1]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hr2 : Run B (bump "th") σ1 (σ1.setVar "th" (σ.vars "th" + 1)) 4 :=
    Run.assign (evalB_bin hthv (evalB_lit (by omega)) (by rw [Bop.apply_add]; omega))
  refine ⟨_, _, (hr1.seq hr2).mono (by omega), le_rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [hσ1, hn]
  · simp [hσ1, hN, pow_succ]
  · simp; omega
  · simp; omega

theorem sizeLoop_spec {B n : ℕ} (hnB : 2 * n + 4 < B) :
    Spec B (fun σ => σ.vars "n" = n) sizeLoop
      (fun _ σ' => σ'.vars "tN" = 2 ^ (n - 1).size ∧ σ'.vars "th" = (n - 1).size ∧
        σ'.vars "n" = n) (12 * (n - 1).size + 8) := by
  have hsle := Lax496464Proofs.Ram.BitsNat.size_le_self (n - 1)
  refine Spec.of_exists fun σ hn => ?_
  have hr1 : Run B (.assign "tN" (.lit 1)) σ (σ.setVar "tN" 1) 2 := Run.assign (evalB_lit (by omega))
  have hr2 : Run B (.assign "th" (.lit 0)) (σ.setVar "tN" 1) ((σ.setVar "tN" 1).setVar "th" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hI0 : SI n ((σ.setVar "tN" 1).setVar "th" 0) := ⟨by simp [hn], by simp, by simp⟩
  have hloop := Spec.while_count (B := B) (P := SI n) (K := 12 * (n - 1).size + 4)
    (b := .lt (V "tN") (V "n")) (c := .seq (.assign "tN" (.bin .mul (V "tN") (.lit 2))) (bump "th"))
    (SI n) (fun σ => (n - 1).size - σ.vars "th") 8
    (fun σ hI => by
      obtain ⟨hn', hN, hth⟩ := hI
      exact evalB_condLt_vars (by
        have h1 : 2 ^ σ.vars "th" ≤ 2 ^ (n - 1).size := Nat.pow_le_pow_right (by norm_num) hth
        have h2 := two_pow_size_le n
        rw [hN]; omega) (by rw [hn']; omega))
    (sizeBody_spec hnB) (fun σ h => h)
    (fun σ hI => by
      have hb : (Cond.lt (V "tN") (V "n")).size = 3 := by simp [Cond.size, Expr.size]
      rw [hb]
      have : (n - 1).size - σ.vars "th" ≤ (n - 1).size := Nat.sub_le _ _
      nlinarith)
  obtain ⟨σ3, hr3, hI3, hfalse⟩ := hloop.run hI0
  obtain ⟨hn3, hN3, hth3⟩ := hI3
  have hge := le_of_condLt_false hfalse
  rw [hn3] at hge
  have hn0 : n ≤ 2 ^ σ3.vars "th" := by rw [← hN3]; exact hge
  have hsz := size_le_of hn0
  refine ⟨σ3, _, hr1.seq (hr2.seq hr3), by omega, ?_, by omega, hn3⟩
  rw [hN3]; congr 1; omega

end Lax496464Proofs.Ram.T4Setup
