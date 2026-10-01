import Lax496464Proofs.WHierarchy.HittingSet.Parse
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # Bounds shared by the programs that read a Hitting Set word

Every number of the instance is below `2 ^ L` and every count is at most `L`, for `L` the length of
the word; so the value bound `2 ^ (L + 3)` serves the reader, and its cost is cubic in `L`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Common

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Parse

/-- The entries of a word are bits. -/
theorem word_le_one {P : Instance} {k v : ℕ} (h : v ∈ word P k) : v ≤ 1 := by
  rw [word_eq_natBits] at h
  simp only [natBits, List.mem_map] at h
  obtain ⟨b, -, rfl⟩ := h
  cases b <;> simp

theorem lt_two_pow_of_size_le {v L : ℕ} (h : v.size ≤ L) : v < 2 ^ L :=
  lt_of_lt_of_le (Nat.lt_size_self v) (Nat.pow_le_pow_right (by norm_num) h)

/-- The dimensions against the length `L` of the word. -/
theorem dims (P : Instance) (k : ℕ) :
    P.m + total P ≤ (word P k).length ∧ P.n < 2 ^ (word P k).length ∧
      P.m < 2 ^ (word P k).length ∧ k < 2 ^ (word P k).length ∧
      szB P k ≤ (word P k).length := by
  have h := dims_le P k
  refine ⟨by omega, lt_two_pow_of_size_le (by omega), lt_two_pow_of_size_le (by omega),
    lt_two_pow_of_size_le (by omega), by unfold szB; omega⟩

theorem fits_of_le (P : Instance) (k : ℕ) {B : ℕ} (hB : 2 ^ ((word P k).length + 3) ≤ B) :
    Fits P k B := by
  obtain ⟨h1, h2, h3, h4, -⟩ := dims P k
  have hL : (word P k).length < 2 ^ (word P k).length := Nat.lt_two_pow_self
  have : 2 ^ ((word P k).length + 3) = 8 * 2 ^ (word P k).length := by ring
  unfold Fits; omega

/-- The cost of the reader is cubic in the length of the word. -/
theorem Kread_le (P : Instance) (k : ℕ) :
    Kread P k ≤ 200 * ((word P k).length + 1) ^ 3 := by
  obtain ⟨h1, -, -, -, h5⟩ := dims P k
  set L := (word P k).length
  have hR : Rn P k ≤ 32 * L + 20 := by unfold Rn; omega
  have hT : total P ≤ L := by omega
  have hm : P.m ≤ L := by omega
  have e1 : (Rn P k + 18) * total P ≤ (32 * L + 38) * L :=
    Nat.mul_le_mul (by omega) hT
  have hK : Kset P k ≤ 32 * L + 20 + (32 * L + 38) * L + 15 := by unfold Kset; omega
  have e2 : (Kset P k + 4) * P.m ≤ (32 * L + 39 + (32 * L + 38) * L) * L :=
    Nat.mul_le_mul (by omega) hm
  unfold Kread
  have e3 : (32 * L + 39 + (32 * L + 38) * L) * L + 96 * L + 80 ≤ 200 * (L + 1) ^ 3 := by
    nlinarith [Nat.zero_le L]
  omega

end Lax496464Proofs.WHierarchy.HittingSet.Common
