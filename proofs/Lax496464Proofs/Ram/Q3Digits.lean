import Lax496464Proofs.Ram.Q3Defs

/-!
# Q3: the number theory of base-`bb` digits

`dig bb x i = x / bb^i % bb`, `digsum bb qm x = ∑ i<qm, dig bb x i`.  Digit extraction, digit
composition, uniqueness, and the effect of subtracting a power of the base on the digits.
-/

namespace Lax496464Proofs.Ram.Q3Digits

open Lax496464Proofs.Ram.Q3Defs

theorem dig_div (bb x δ i : ℕ) : dig bb (x / bb ^ δ) i = dig bb x (δ + i) := by
  unfold dig
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem dig_lt {bb x i : ℕ} (hbb : 1 ≤ bb) : dig bb x i < bb :=
  Nat.mod_lt _ hbb

theorem dig_of_ge {bb qm x i : ℕ} (hx : x < bb ^ qm) (hi : qm ≤ i) : dig bb x i = 0 := by
  unfold dig
  rcases Nat.eq_zero_or_pos bb with h0 | hpos
  · subst h0
    rcases Nat.eq_zero_or_pos qm with hq | hq
    · subst hq
      have : x = 0 := by simpa using hx
      subst this
      simp
    · rw [zero_pow (by omega)] at hx
      omega
  · have h1 : bb ^ qm ≤ bb ^ i := Nat.pow_le_pow_right hpos hi
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx h1)]
    simp

theorem div_lt_pow {bb qm x : ℕ} (_hbb : 1 ≤ bb) (hx : x < bb ^ qm) (δ : ℕ) :
    x / bb ^ δ < bb ^ qm :=
  lt_of_le_of_lt (Nat.div_le_self _ _) hx

theorem sum_dig {bb qm x : ℕ} (hbb : 1 ≤ bb) (hx : x < bb ^ qm) :
    ∑ i ∈ Finset.range qm, dig bb x i * bb ^ i = x := by
  induction qm generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst this
    simp
  | succ q ih =>
    have hpos : 0 < bb := hbb
    have hx' : x / bb < bb ^ q := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      rw [pow_succ] at hx
      exact hx
    have ih' := ih (x := x / bb) hx'
    rw [Finset.sum_range_succ']
    have h1 : ∀ i, dig bb x (i + 1) * bb ^ (i + 1) = bb * (dig bb (x / bb) i * bb ^ i) := by
      intro i
      have := dig_div bb x 1 i
      rw [pow_one, add_comm 1 i] at this
      rw [← this, pow_succ]
      ring
    simp only [h1]
    rw [← Finset.mul_sum, ih']
    have h0 : dig bb x 0 * bb ^ 0 = x % bb := by simp [dig]
    rw [h0]
    exact Nat.div_add_mod x bb

theorem dig_sum {bb qm : ℕ} (hbb : 1 ≤ bb) (f : ℕ → ℕ) (hf : ∀ i < qm, f i < bb) :
    (∑ i ∈ Finset.range qm, f i * bb ^ i) < bb ^ qm ∧
    ∀ k < qm, dig bb (∑ i ∈ Finset.range qm, f i * bb ^ i) k = f k := by
  have hpos : 0 < bb := hbb
  induction qm generalizing f with
  | zero => simp
  | succ q ih =>
    obtain ⟨hA, hAd⟩ := ih (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
    set A := ∑ i ∈ Finset.range q, f (i + 1) * bb ^ i with hAdef
    have hs : ∑ i ∈ Finset.range (q + 1), f i * bb ^ i = bb * A + f 0 := by
      rw [Finset.sum_range_succ', hAdef, Finset.mul_sum]
      have : ∀ i, f (i + 1) * bb ^ (i + 1) = bb * (f (i + 1) * bb ^ i) := by
        intro i; rw [pow_succ]; ring
      simp only [this]
      simp
    rw [hs]
    have hf0 : f 0 < bb := hf 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [pow_succ]
      have : bb * (A + 1) ≤ bb * bb ^ q := Nat.mul_le_mul_left _ hA
      nlinarith
    · intro k hk
      have hdiv : (bb * A + f 0) / bb = A := by
        rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hf0]; simp
      have hmod : (bb * A + f 0) % bb = f 0 := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hf0]
      cases k with
      | zero => simpa [dig] using hmod
      | succ j =>
        have := dig_div bb (bb * A + f 0) 1 j
        rw [pow_one, hdiv, add_comm 1 j] at this
        rw [← this]
        exact hAd j (by omega)

theorem ext_of_dig {bb qm x y : ℕ} (hbb : 1 ≤ bb) (hx : x < bb ^ qm) (hy : y < bb ^ qm)
    (h : ∀ i < qm, dig bb x i = dig bb y i) : x = y := by
  rw [← sum_dig hbb hx, ← sum_dig hbb hy]
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.1 hi)])

theorem sub_pow {bb qm x k : ℕ} (hbb : 1 ≤ bb) (hx : x < bb ^ qm) (hk : k < qm)
    (hd : 1 ≤ x / bb ^ k % bb) :
    x - bb ^ k < bb ^ qm ∧ ∀ i < qm, dig bb (x - bb ^ k) i = dig bb x i - (if i = k then 1 else 0) := by
  have hd' : 1 ≤ dig bb x k := hd
  set f : ℕ → ℕ := fun i => dig bb x i - (if i = k then 1 else 0) with hf
  have hflt : ∀ i < qm, f i < bb := fun i _ => lt_of_le_of_lt (Nat.sub_le _ _) (dig_lt hbb)
  have hpt : ∀ i, dig bb x i * bb ^ i = f i * bb ^ i + (if i = k then bb ^ k else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp only [hf, if_true]
      obtain ⟨e, he⟩ : ∃ e, dig bb x i = e + 1 := ⟨dig bb x i - 1, by omega⟩
      rw [he]; simp; ring
    · simp [hf, hik]
  have hsum : ∑ i ∈ Finset.range qm, dig bb x i * bb ^ i
      = ∑ i ∈ Finset.range qm, f i * bb ^ i + bb ^ k := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range qm) k (fun _ => bb ^ k)]
    simp [hk]
  rw [sum_dig hbb hx] at hsum
  have hS : ∑ i ∈ Finset.range qm, f i * bb ^ i = x - bb ^ k := by omega
  obtain ⟨h1, h2⟩ := dig_sum hbb f hflt
  rw [hS] at h1 h2
  exact ⟨h1, h2⟩

theorem digsum_sub_pow {bb qm x k : ℕ} (hbb : 1 ≤ bb) (hx : x < bb ^ qm) (hk : k < qm)
    (hd : 1 ≤ x / bb ^ k % bb) : digsum bb qm (x - bb ^ k) + 1 = digsum bb qm x := by
  obtain ⟨_, hdg⟩ := sub_pow hbb hx hk hd
  have hd' : 1 ≤ dig bb x k := hd
  unfold digsum
  rw [Finset.sum_congr rfl (fun i hi => hdg i (Finset.mem_range.1 hi))]
  have hpt : ∀ i, dig bb x i = (dig bb x i - (if i = k then 1 else 0)) + (if i = k then 1 else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik; simp; omega
    · simp [hik]
  conv_rhs => rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range qm) k (fun _ => 1)]
  simp [hk]

end Lax496464Proofs.Ram.Q3Digits
