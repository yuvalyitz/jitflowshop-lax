import Lax496464Proofs.Ram.D2Layout
import Lax496464Proofs.Ram.Sort

/-!
# Theorem 2: the running time, against the printed bound

The program's cost is `O((W+1)(n+1)^m + sortCost)`.  `loopWork_le` uses `D2Count.sum_codes_le`
(the sets have `Σ(|X|+1) ≤ 2(n+1)^m`), which is why no factor `m` appears.
-/

namespace Lax496464Proofs.Ram.D2Bound

open Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Step Lax496464Proofs.Ram.D2Count
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Bsearch

theorem loopWork_le (n m W : ℕ) :
    loopWork n m W ((n + 1) ^ m) ≤ 1000 * ((W + 1) * (n + 1) ^ m) := by
  classical
  unfold loopWork turnCost blockCost
  have hs := sum_codes_le n m (W + 1)
  have h1 : ∑ c ∈ Finset.range ((n + 1) ^ m),
      (600 + (if IsCode n m c then 128 * lenOf n m c + 104 * (W + 1) else 0) + 4) ≤
      ∑ c ∈ Finset.range ((n + 1) ^ m),
        (604 + 128 * (if IsCode n m c then lenOf n m c + 1 + (W + 1) else 0)) := by
    apply Finset.sum_le_sum
    intro c _
    by_cases h : IsCode n m c
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
  refine le_trans h1 ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hs' : ∑ c ∈ Finset.range ((n + 1) ^ m),
      (if IsCode n m c then lenOf n m c + 1 + (W + 1) else 0) ≤ (2 + (W + 1)) * (n + 1) ^ m := hs
  have hN : 0 ≤ (n + 1) ^ m := Nat.zero_le _
  nlinarith [Nat.zero_le (W * (n + 1) ^ m)]

theorem size_le_log' {n len : ℕ} (hn : n ≤ len) : n.size ≤ Nat.log 2 (len + 2) + 1 := by
  apply Nat.size_le.mpr
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (len + 2)
  omega

/-- The set-up costs `O(m + sortCost)`. -/
theorem setupCost_le {n m len : ℕ} (hn : n ≤ len) :
    setupCost n m ≤ 100 + 68 * m + 54 * n +
      112 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  unfold setupCost
  set Lg := Nat.log 2 (len + 2) + 1 with hLg
  have hs : n.size ≤ Lg := size_le_log' hn
  have hLg1 : 1 ≤ Lg := by omega
  have h1 : n * Lg ≤ (len + 1) * Lg := Nat.mul_le_mul_right _ (by omega)
  have h2 : n.size * n ≤ Lg * n := Nat.mul_le_mul_right _ hs
  have h3 : n ≤ (len + 1) * Lg := le_trans (by omega) (Nat.le_mul_of_pos_right (len + 1) hLg1)
  have h4 : (68 + 44 * n.size) * n = 68 * n + 44 * (n.size * n) := by ring
  rw [h4]
  nlinarith

theorem m_le_pow {n m : ℕ} (hn : 1 ≤ n) : m ≤ (n + 1) ^ m := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ (n + 1) ^ m := Nat.pow_le_pow_left (by omega) m
  omega

theorem n_le_pow {n m : ℕ} (hm : 1 ≤ m) : n ≤ (n + 1) ^ m := by
  calc n ≤ n + 1 := by omega
    _ = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ (n + 1) ^ m := Nat.pow_le_pow_right (by omega) hm

/-- The cost of the whole program on an instance of `n` jobs, `m` machines, threshold `W`. -/
noncomputable def cost2 (n m W : ℕ) : ℕ :=
  (2 * Lax496464Proofs.Ram.Sort.sortK 90 n + 1000 * n + 2000) + 30 +
    (if 1 ≤ n ∧ 1 ≤ m then setupCost n m + (loopWork n m W ((n + 1) ^ m) + 4) + 20 else 10)

/-- **The bound.** -/
theorem cost2_le {n m W len : ℕ} (hn : n ≤ len) :
    10 * cost2 n m W + 1 ≤ 100000 * ((W + 1) * (n + 1) ^ m) +
      100000 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  set S := (len + 1) * (Nat.log 2 (len + 2) + 1) with hS
  have hS1 : 1 ≤ S := Nat.mul_pos (by omega) (by omega)
  have hnS : n ≤ S := le_trans (by omega) (Nat.le_mul_of_pos_right (len + 1) (by omega : 1 ≤ Nat.log 2 (len + 2) + 1))
  have hsK : Lax496464Proofs.Ram.Sort.sortK 90 n ≤ 390 * S := by
    have := Lax496464Proofs.Ram.Sort.sortK_le 90 n len hn
    rw [hS]; simpa using this
  have hP : 1 ≤ (W + 1) * (n + 1) ^ m := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  unfold cost2
  by_cases h : 1 ≤ n ∧ 1 ≤ m
  · rw [if_pos h]
    have hsu := setupCost_le (m := m) hn
    have hlw := loopWork_le n m W
    have hm := m_le_pow (n := n) (m := m) h.1
    have hnp := n_le_pow (n := n) (m := m) h.2
    have hmP : (n + 1) ^ m ≤ (W + 1) * (n + 1) ^ m := Nat.le_mul_of_pos_left _ (by omega)
    rw [← hS] at hsu
    omega
  · rw [if_neg h]
    omega

end Lax496464Proofs.Ram.D2Bound
