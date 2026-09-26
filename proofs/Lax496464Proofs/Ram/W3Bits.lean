import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Sets of slots as bit masks

The width sweep keeps a table indexed by the set of *slots* the running selected jobs occupy,
written as the number `∑ i ∈ S, 2^i`. This file is the arithmetic of that encoding, using
Mathlib's `Nat.bitIndices`: a mask determines its set (`maskOf_inj`), a bit is set exactly when
its slot belongs (`testBit_maskOf`), the popcount is the cardinality (`pcnt_maskOf`), and the two
recurrences the machine uses — a bit test by division, the popcount by halving — are right.
-/

namespace Lax496464Proofs.Ram.W3Bits

/-- The mask of a set of slots. -/
def maskOf (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

/-- The number of set bits. -/
def pcnt (X : ℕ) : ℕ := X.bitIndices.length

theorem maskOf_eq (S : Finset ℕ) : maskOf S = ((S.sort).map fun i => 2 ^ i).sum := by
  unfold maskOf
  have h := List.sum_toFinset (fun i => 2 ^ i) (Finset.sort_nodup S (· ≤ ·))
  rw [Finset.sort_toFinset] at h
  exact h

theorem bitIndices_maskOf (S : Finset ℕ) : (maskOf S).bitIndices = S.sort := by
  rw [maskOf_eq]
  exact Nat.bitIndices_sum_map_two_pow (Finset.sortedLT_sort S)

theorem testBit_maskOf {S : Finset ℕ} {b : ℕ} : (maskOf S).testBit b = true ↔ b ∈ S := by
  rw [← Nat.mem_bitIndices, bitIndices_maskOf, Finset.mem_sort]

theorem maskOf_insert {S : Finset ℕ} {a : ℕ} (ha : a ∉ S) :
    maskOf (insert a S) = maskOf S + 2 ^ a := by
  unfold maskOf
  rw [Finset.sum_insert ha]; ring

theorem pcnt_maskOf (S : Finset ℕ) : pcnt (maskOf S) = S.card := by
  unfold pcnt
  rw [bitIndices_maskOf, Finset.length_sort]

/-- The popcount recurrence the machine's table uses. -/
theorem pcnt_div_two (X : ℕ) : pcnt X = pcnt (X / 2) + X % 2 := by
  unfold pcnt
  rcases Nat.even_or_odd' X with ⟨k, rfl | rfl⟩
  · have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k % 2 = 0 := by omega
    rw [h1, h2, Nat.bitIndices_two_mul]; simp
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    rw [h1, h2, Nat.bitIndices_two_mul_add_one]; simp

/-- The bit test the machine performs, by division. -/
theorem testBit_iff_div (X b : ℕ) : X.testBit b = true ↔ X / 2 ^ b % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp

end Lax496464Proofs.Ram.W3Bits
