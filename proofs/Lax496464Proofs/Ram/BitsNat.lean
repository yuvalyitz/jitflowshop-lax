import Lax496464.HittingSet
import Mathlib.Data.Nat.Size

/-!
# A Number's Self-Delimiting Code, as Zeros and Ones

`HittingSet.encodeNat n` is a list of `Bool`; a word RAM is handed zeros and ones, not
booleans, so this restates the code as a list of `ℕ` and gives its digits a closed form:
`n.size` ones, a zero, then the `n.size` binary digits of `n`, least significant first.
This is the fact `Ram/DecodeNat.lean`'s program is checked against.
-/

namespace Lax496464Proofs.Ram.BitsNat

open Lax496464.HittingSet Lax434930.PolynomialTime

/-- A binary word as a list of zeros and ones. -/
def natBits (w : Word) : List ℕ := w.map fun b => if b then 1 else 0

/-- The `i`-th binary digit of `n`. -/
def digit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The self-delimiting code of a number, as zeros and ones. -/
def bitsNat (n : ℕ) : List ℕ :=
  List.replicate n.size 1 ++ [0] ++ (List.range n.size).map (digit n)

theorem bits_eq_digits (n : ℕ) :
    n.bits.map (fun b => if b then 1 else 0) = (List.range n.size).map (digit n) := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · rw [hz]; simp
      · rw [Nat.bits_append_bit n b h, Nat.size_bit hz, List.range_succ_eq_map, List.map_cons,
          List.map_cons, List.map_map, ih]
        congr 1
        · cases b <;> simp [digit, Nat.bit_val]
        · refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp, digit, pow_succ]
          rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
          congr 2
          cases b <;> simp [Nat.bit_val]; omega

/-- **The code, as zeros and ones.** -/
theorem natBits_encodeNat (n : ℕ) : natBits (encodeNat n) = bitsNat n := by
  simp only [natBits, encodeNat, bitsNat, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [bits_eq_digits, Nat.size_eq_bits_len]
  simp

/-- The digits determine the number: summing `d_i \cdot 2^i` over `i < n.size` recovers `n`. -/
theorem sum_digit (n : ℕ) :
    ∑ i ∈ Finset.range n.size, digit n i * 2 ^ i = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n' h ih =>
      by_cases hz : Nat.bit b n' = 0
      · simp [hz]
      · rw [Nat.size_bit hz, Finset.sum_range_succ']
        have hd0 : digit (Nat.bit b n') 0 = b.toNat := by
          rcases b <;> simp [digit, Nat.bit_val]
        have hdiv : Nat.bit b n' / 2 = n' := by
          rw [Nat.bit_val]; rcases b <;> simp; omega
        have hdi : ∀ i, digit (Nat.bit b n') (i + 1) = digit n' i := by
          intro i
          unfold digit
          rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        have hsum : ∑ i ∈ Finset.range n'.size, digit (Nat.bit b n') (i + 1) * 2 ^ (i + 1)
            = 2 * ∑ i ∈ Finset.range n'.size, digit n' i * 2 ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdi]; ring
        rw [hsum, ih, hd0, pow_zero, mul_one, Nat.bit_val]

/-! ## Reading the code back off, one bit at a time -/

/-! ## Writing the code, one bit at a time -/

/-- Halving strictly decreases the size, once the number is positive. -/
theorem size_succ_of_ne_zero {v : ℕ} (h : v ≠ 0) : v.size = (v / 2).size + 1 := by
  induction v using Nat.binaryRec' with
  | zero => exact absurd rfl h
  | bit b n _ =>
      have hz : Nat.bit b n ≠ 0 := h
      have hdiv : Nat.bit b n / 2 = n := by rw [Nat.bit_val]; rcases b <;> simp; omega
      rw [Nat.size_bit hz, hdiv]

/-- A number's own bit-length never exceeds the number itself. -/
theorem size_le_self (v : ℕ) : v.size ≤ v := by
  induction v using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · simp [hz]
      · rw [Nat.size_bit hz]
        have hz' : 2 * n + b.toNat ≠ 0 := by rw [← Nat.bit_val]; exact hz
        have hbn : b.toNat ≤ 1 := by rcases b <;> simp
        have hn1 : n + 1 ≤ 2 * n + b.toNat := by omega
        rw [Nat.bit_val]
        omega

end Lax496464Proofs.Ram.BitsNat
