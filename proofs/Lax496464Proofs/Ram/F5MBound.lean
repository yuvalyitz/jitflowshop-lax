import Lax496464Proofs.Ram.F5MRun
import Lax496464Proofs.Ram.D2Bound

/-!
# Theorem 5 (Table of Section 3): the Running Time, Against `(W+1)(n+1)^m + sortCost`
-/

namespace Lax496464Proofs.F5MBound

open Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Step Lax496464Proofs.Ram.D2Bound
open Lax496464Proofs.F5MRest

theorem arith_main (n m S PP W1 sK su lw : ℕ) (hsK : sK ≤ 390 * S)
    (hsu : su ≤ 100 + 68 * m + 54 * n + 112 * S) (hlw : lw ≤ 1000 * PP) (hm : m ≤ PP)
    (hn : n ≤ PP) (_hnS : n ≤ S) (hS : 1 ≤ S) (_hP : 1 ≤ PP) (hW : W1 ≤ PP) :
    10 * ((2 * sK + 1000 * n + 2000) +
      (((44 * n + 10) + 20 + (44 * n + 10) + 10) + 30 +
        (su + (lw + 4) + (34 * W1 + 20) + 12 + 20))) + 1 ≤ 100000 * PP + 100000 * S := by
  omega

theorem cost5m_le {n m W len : ℕ} (hn : n ≤ len) :
    10 * ((2 * Lax496464Proofs.Ram.Sort.sortK 90 n + 1000 * n + 2000) + cost5m n m W) + 1 ≤
      100000 * ((W + 1) * (n + 1) ^ m) +
      100000 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  set S := (len + 1) * (Nat.log 2 (len + 2) + 1) with hS
  have hS1 : 1 ≤ S := Nat.mul_pos (by omega) (by omega)
  have hnS : n ≤ S :=
    le_trans (by omega) (Nat.le_mul_of_pos_right (len + 1)
      (by omega : 1 ≤ Nat.log 2 (len + 2) + 1))
  have hsK : Lax496464Proofs.Ram.Sort.sortK 90 n ≤ 390 * S := by
    have := Lax496464Proofs.Ram.Sort.sortK_le 90 n len hn
    rw [hS]; simpa using this
  have hP : 1 ≤ (W + 1) * (n + 1) ^ m := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  unfold cost5m
  by_cases h : 1 ≤ n ∧ 1 ≤ m
  · rw [if_pos h]
    have hsu := setupCost_le (m := m) hn
    have hlw := loopWork_le n m W
    have hm := m_le_pow (n := n) (m := m) h.1
    have hnp := n_le_pow (n := n) (m := m) h.2
    have hmP : (n + 1) ^ m ≤ (W + 1) * (n + 1) ^ m := Nat.le_mul_of_pos_left _ (by omega)
    have hWP : W + 1 ≤ (W + 1) * (n + 1) ^ m :=
      Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    rw [← hS] at hsu
    exact arith_main n m S _ (W + 1) _ _ _ hsK hsu hlw
      (le_trans hm hmP) (le_trans hnp hmP) hnS hS1 hP hWP
  · rw [if_neg h]
    omega

end Lax496464Proofs.F5MBound
