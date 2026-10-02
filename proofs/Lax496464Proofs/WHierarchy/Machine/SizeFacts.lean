import Lax496464.WH_A4_MachineFacts
import Mathlib.Data.Nat.Size

/-! Bit size of words. -/

namespace Lax496464Proofs.WHierarchy.Machine.SizeFacts

open Lax759944.BinaryWordEncoding

theorem bitSize_nil : bitSize [] = 0 := by unfold bitSize; try rfl

theorem bitSize_cons (v : ℕ) (x : List ℕ) : bitSize (v :: x) = v.size + 1 + bitSize x := by
  simp [bitSize, encode, encodeNat, Nat.size_eq_bits_len]
  omega

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.length_le_bitSize
---
-/
theorem length_le_bitSize (x : List ℕ) : x.length ≤ bitSize x := by
  induction x with
  | nil => simp [bitSize_nil]
  | cons v x ih => rw [bitSize_cons]; simp; omega

theorem size_le_bitSize {x : List ℕ} {v : ℕ} (h : v ∈ x) : v.size ≤ bitSize x := by
  induction x with
  | nil => simp at h
  | cons u x ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize
---
-/
theorem lt_two_pow_bitSize {x : List ℕ} {v : ℕ} (h : v ∈ x) : v < 2 ^ bitSize x :=
  lt_of_lt_of_le (Nat.lt_size_self v) (Nat.pow_le_pow_right (by norm_num) (size_le_bitSize h))

end Lax496464Proofs.WHierarchy.Machine.SizeFacts
