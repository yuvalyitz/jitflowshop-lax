import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

/-! # The value bound of the program

For an input word of bit size `n` with `k` last, the values stay below
`Bv = 16 · 2^n · (n + 4)^(d + k + 5) · (d + 2)^(k + 1) · (k + 2)^(d + 3)`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds

open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

/-- The factor of the bound that depends on the parameter only. -/
def Pk (d k : ℕ) : ℕ := (d + 2) ^ (k + 1) * (k + 2) ^ (d + 3)

/-- **The value bound.** -/
def Bv (d n k : ℕ) : ℕ := 16 * 2 ^ n * (n + 4) ^ (d + k + 5) * Pk d k

theorem one_le_Pk (d k : ℕ) : 1 ≤ Pk d k :=
  Nat.one_le_iff_ne_zero.mpr (by unfold Pk; positivity)

theorem pow_le_Pk_left {d k i : ℕ} (hi : i ≤ k) : d ^ i ≤ Pk d k := by
  unfold Pk
  calc d ^ i ≤ (d + 2) ^ i := Nat.pow_le_pow_left (by omega) _
    _ ≤ (d + 2) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)

theorem pow_le_Pk_right {d k i : ℕ} (hi : i ≤ d + 3) : (k + 1) ^ i ≤ Pk d k := by
  unfold Pk
  calc (k + 1) ^ i ≤ (k + 2) ^ i := Nat.pow_le_pow_left (by omega) _
    _ ≤ (k + 2) ^ (d + 3) := Nat.pow_le_pow_right (by omega) hi
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

theorem d_le_Pk (d k : ℕ) : d + 2 ≤ Pk d k := by
  unfold Pk
  have h1 : (d + 2) ^ 1 ≤ (d + 2) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 1 ≤ (k + 2) ^ (d + 3) := Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at h1
  nlinarith

theorem k_le_Pk (d k : ℕ) : k + 2 ≤ Pk d k := by
  unfold Pk
  have h1 : (k + 2) ^ 1 ≤ (k + 2) ^ (d + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 1 ≤ (d + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at h1
  nlinarith

theorem nv_le_Pk (d k : ℕ) : nv d k + 1 ≤ 3 * Pk d k := by
  unfold nv FF
  have h1 := pow_le_Pk_right (d := d) (k := k) (i := d + 2) (by omega)
  have h2 := k_le_Pk d k
  have e : (k + 1) ^ (d + 1) * (k + 1) = (k + 1) ^ (d + 2) := by ring
  omega

variable {cl : List (List ℕ)} {d k n : ℕ}

/-- **The bound suffices.** -/
theorem bb_Bv (hlen : cl.length + nL cl + 2 ≤ n) (hent : ∀ v ∈ wordOf' cl k, v < 2 ^ n) :
    BB cl d k (Bv d n k) := by
  have hE : n < 2 ^ n := Nat.lt_two_pow_self
  have hE1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hP := one_le_Pk d k
  have hMn : MM cl ≤ n + 4 := by unfold MM; omega
  set A := (n + 4) ^ (d + k + 5) with hA
  have hA4 : n + 4 ≤ A := by
    calc n + 4 = (n + 4) ^ 1 := (pow_one _).symm
      _ ≤ A := Nat.pow_le_pow_right (by omega) (by omega)
  have hMA : ∀ i ≤ d + k + 5, MM cl ^ i ≤ A := fun i hi =>
    (Nat.pow_le_pow_left hMn i).trans (Nat.pow_le_pow_right (by omega) hi)
  set E := 2 ^ n with hEdef
  set P := Pk d k with hPdef
  have hB : Bv d n k = 16 * (E * A * P) := by rw [Bv]; ring
  -- the bound dominates each factor and products of two of them
  have hEA : E * A ≤ E * A * P := Nat.le_mul_of_pos_right _ (by omega)
  have hAP : A * P ≤ E * A * P := by nlinarith
  have hEP : E * P ≤ E * A * P := by nlinarith
  have hAle : A ≤ E * A := Nat.le_mul_of_pos_left _ (by omega)
  have hPle : P ≤ A * P := Nat.le_mul_of_pos_left _ (by omega)
  have hEle : E ≤ E * A := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩, fun v hv => ?_, ?_,
    fun j hj => ?_, ?_⟩
  · have := pow_le_Pk_left (d := d) hi; rw [hB]; omega
  · have := hMA i (by omega); rw [hB]; omega
  · have := pow_le_Pk_right (d := d) (k := k) (i := i) (by omega); rw [hB]; omega
  · -- the size of the array of numbers
    have h1 : d ^ k ≤ P := pow_le_Pk_left le_rfl
    have h2 : cl.length * d ^ k ≤ n * P := Nat.mul_le_mul (by omega) h1
    have h3 : n * P ≤ E * P := Nat.mul_le_mul_right _ hE.le
    unfold sz; rw [hB]; nlinarith
  · have := nv_le_Pk d k; rw [hB]; omega
  · have h1 := d_le_Pk d k
    have h2 := k_le_Pk d k
    rw [hB]; nlinarith
  · have := hent v hv; rw [hB]; nlinarith
  · rw [hB]; nlinarith
  · have hc := code_lt hent hj
    have h1 : code cl j / 2 * MM cl ≤ E * A :=
      Nat.mul_le_mul (by have := Nat.div_le_self (code cl j) 2; omega) (by omega)
    rw [hB]; nlinarith
  · have h1 : MM cl ^ (d + k + 4) * (n + 4) ≤ A := by
      calc MM cl ^ (d + k + 4) * (n + 4) ≤ (n + 4) ^ (d + k + 4) * (n + 4) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hMn _)
        _ = A := by rw [hA]; ring
    rw [hB]; nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds
