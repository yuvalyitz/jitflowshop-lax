import Lax496464Proofs.Ram.D4Layout
import Lax496464Proofs.Ram.D2Bound

/-!
# Corollary 2: the Running Time, Against the Printed Bound

The program's cost is `O((P+1)(n+1)^m + sortCost)`, with no factor `m`, by the same counting as
Theorem 2 (`D2Bound.loopWork_le` at `W := P`).
-/

namespace Lax496464Proofs.Ram.D4Bound

open Lax496464Proofs.Ram.D4Core Lax496464Proofs.Ram.D2Step Lax496464Proofs.Ram.D2Bound
open Lax496464Proofs.Ram.D2Core (setupCost)

/-- The cost of the whole program on an instance of `n` jobs, `m` machines, total preprocessing
time `R`. -/
noncomputable def cost4 (n m R : ℕ) : ℕ :=
  (2 * Lax496464Proofs.Ram.Sort.sortK 90 n + 1000 * n + 2000) + 30 +
    (if 1 ≤ n ∧ 1 ≤ m then setupCost4 n m + (loopWork n m R ((n + 1) ^ m) + 4) + 20 else 10)

/-- **The bound.** -/
theorem cost4_le {n m R len : ℕ} (hn : n ≤ len) :
    10 * cost4 n m R + 1 ≤ 100000 * ((R + 1) * (n + 1) ^ m) +
      100000 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  set S := (len + 1) * (Nat.log 2 (len + 2) + 1) with hS
  have hS1 : 1 ≤ S := Nat.mul_pos (by omega) (by omega)
  have hnS : n ≤ S := le_trans (by omega) (Nat.le_mul_of_pos_right (len + 1) (by omega : 1 ≤ Nat.log 2 (len + 2) + 1))
  have hsK : Lax496464Proofs.Ram.Sort.sortK 90 n ≤ 390 * S := by
    have := Lax496464Proofs.Ram.Sort.sortK_le 90 n len hn
    rw [hS]; simpa using this
  have hP : 1 ≤ (R + 1) * (n + 1) ^ m := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  unfold cost4
  by_cases h : 1 ≤ n ∧ 1 ≤ m
  · rw [if_pos h]
    have hsu := setupCost_le (m := m) hn
    have hlw := loopWork_le n m R
    have hm := m_le_pow (n := n) (m := m) h.1
    have hnp := n_le_pow (n := n) (m := m) h.2
    have hmP : (n + 1) ^ m ≤ (R + 1) * (n + 1) ^ m := Nat.le_mul_of_pos_left _ (by omega)
    rw [← hS] at hsu
    unfold setupCost4
    omega
  · rw [if_neg h]
    omega

end Lax496464Proofs.Ram.D4Bound
