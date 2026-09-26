import Lax496464Proofs.Ram.D2Scan

/-!
# Theorem 2, pure layer 3: which numbers are codes

The machine has to skip every number that is not the code of a set of thresholds — without reading
its digits one by one.  A number `c < b^m` is a code iff it is the all-padding number, or its first
digit is smaller than its second and the number obtained by dropping the first digit (and padding
on the right) is again a code; that is `isCode_iff`, and it is the recurrence the machine's
`VALID` array is filled by.
-/

namespace Lax496464Proofs.Ram.D2Valid

open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan

/-- The first (most significant) digit of the `m`-digit number `c`. -/
def x1 (n m c : ℕ) : ℕ := c / (n + 1) ^ (m - 1)

/-- The second digit, with the padding digit `n` when there is no second. -/
def x2 (n m c : ℕ) : ℕ := if m = 1 then n else c / (n + 1) ^ (m - 2) % (n + 1)

/-- Drop the first digit and pad on the right. -/
def sufc (n m c : ℕ) : ℕ := (c % (n + 1) ^ (m - 1)) * (n + 1) + n

/-- The code of the empty set. -/
def top (n m : ℕ) : ℕ := (n + 1) ^ m - 1

theorem top_eq (n m : ℕ) : codeL n m [] = top n m := codeL_nil n m

theorem sl_tail {n m j : ℕ} {Zs : List ℕ} (h : SL n m (j :: Zs)) : SL n (m - 1) Zs :=
  ⟨by
    have := h.sorted
    rw [List.sortedLT_iff_pairwise] at this ⊢
    exact (List.pairwise_cons.mp this).2,
   fun z hz => h.lt z (List.mem_cons_of_mem _ hz),
   by have := h.len; simp only [List.length_cons] at this; omega⟩

theorem lstOf_snoc {n m : ℕ} {Zs : List ℕ} (h : Zs.length < m) :
    lstOf n m Zs = lstOf n (m - 1) Zs ++ [n] := by
  have : m - Zs.length = (m - 1 - Zs.length) + 1 := by omega
  simp only [lstOf, this, List.replicate_succ', List.append_assoc]

theorem enc_snoc (b : ℕ) (A : List ℕ) (d : ℕ) : enc b (A ++ [d]) = enc b A * b + d := by
  rw [enc_append]; simp

theorem enc_snoc_mod {b : ℕ} (_hb : 0 < b) (A : List ℕ) {d : ℕ} (hd : d < b) :
    enc b (A ++ [d]) % b = d := by
  rw [enc_snoc, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]

theorem sufc_mod {n m c : ℕ} : sufc n m c % (n + 1) = n := by
  unfold sufc
  rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- The second digit of the number `enc (j :: T)`, `T` of length `m - 1 ≥ 1`. -/
theorem x2_eq {n m j : ℕ} {T : List ℕ} (hm : 2 ≤ m) (hT : T.length = m - 1)
    (hj : j < n + 1) (hTlt : ∀ x ∈ T, x < n + 1) :
    x2 n m (enc (n + 1) (j :: T)) = T.getD 0 0 := by
  have hd := dig_enc (b := n + 1) (by omega) (L := j :: T)
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hj
      · exact hTlt x hx) 1 (by simp; omega)
  have hlen : (j :: T).length = m := by simp [hT]; omega
  rw [hlen] at hd
  simp only [List.getD_cons_succ] at hd
  unfold x2
  rw [if_neg (by omega)]
  rw [hd]
  unfold dig
  congr 3

theorem isCode_of_recursion {n m c : ℕ} (hm : 1 ≤ m) (hc : c < (n + 1) ^ m)
    (h : c = top n m ∨ (x1 n m c < x2 n m c ∧ IsCode n m (sufc n m c))) : IsCode n m c := by
  rcases h with h | ⟨hlt, Zs', hsl', hcode⟩
  · exact ⟨[], ⟨List.sortedLT_iff_pairwise.mpr List.Pairwise.nil, by simp, by simp⟩,
      by rw [top_eq, h]⟩
  · set b := n + 1 with hb
    have hb0 : 0 < b := by omega
    -- the last digit of `sufc` is the padding digit, so `Zs'` is not full
    have hZlt : Zs'.length < m := by
      by_contra hfull
      have hfull' : Zs'.length = m := le_antisymm hsl'.len (not_lt.mp hfull)
      have hne : Zs' ≠ [] := by intro h0; rw [h0] at hfull'; simp at hfull'; omega
      obtain ⟨A, z, hAz⟩ := (List.eq_nil_or_concat Zs').resolve_left hne
      have hzn : z < n := hsl'.lt z (by rw [hAz]; simp)
      have hcl : codeL n m Zs' = enc b (A ++ [z]) := by
        unfold codeL lstOf
        rw [hfull', Nat.sub_self, List.replicate_zero, List.append_nil, hAz, List.concat_eq_append]
      have h1 : sufc n m c % b = n := sufc_mod
      rw [← hcode, hcl, enc_snoc_mod hb0 A (by omega)] at h1
      omega
    have hZ1 : Zs'.length ≤ m - 1 := by omega
    set T := lstOf n (m - 1) Zs' with hT
    have hTsl : SL n (m - 1) Zs' := ⟨hsl'.sorted, hsl'.lt, hZ1⟩
    have hTlen : T.length = m - 1 := hTsl.lstOf_length
    have hTlt : ∀ x ∈ T, x < b := hTsl.lstOf_lt
    have hcT : enc b T = c % b ^ (m - 1) := by
      have h1 : enc b (T ++ [n]) = sufc n m c := by
        rw [← hcode]; unfold codeL; rw [lstOf_snoc hZlt]
      rw [enc_snoc] at h1
      unfold sufc at h1
      simp only [← hb] at h1
      exact Nat.eq_of_mul_eq_mul_right hb0 (by omega)
    have hdm := Nat.div_add_mod c (b ^ (m - 1))
    have hcE : c = enc b (x1 n m c :: T) := by
      rw [enc_cons, hTlen, hcT]
      simp only [x1, ← hb]
      rw [Nat.mul_comm] at hdm
      omega
    have hx1b : x1 n m c < b := by
      simp only [x1, ← hb]
      rw [Nat.div_lt_iff_lt_mul (pow_pos hb0 _)]
      have : b ^ m = b * b ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
      rw [← this]; exact hc
    have hx2 : x2 n m c ≤ n := by
      simp only [x2, ← hb]
      split_ifs
      · exact le_rfl
      · have := Nat.mod_lt (c / b ^ (m - 2)) hb0; omega
    have hxn : x1 n m c < n := by omega
    refine ⟨x1 n m c :: Zs', ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.sortedLT_iff_pairwise, List.pairwise_cons]
      refine ⟨?_, List.sortedLT_iff_pairwise.mp hsl'.sorted⟩
      intro z hz
      -- Zs' is nonempty, so m ≥ 2 and the second digit is its head
      have hm2 : 2 ≤ m := by
        have : 0 < Zs'.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hz)
        omega
      have hx2T : x2 n m c = T.getD 0 0 := by
        rw [hcE]
        exact x2_eq hm2 hTlen hx1b hTlt
      rw [hx2T] at hlt
      obtain ⟨a, Zr, hZr⟩ : ∃ a Zr, Zs' = a :: Zr := by
        cases h : Zs' with
        | nil => rw [h] at hz; simp at hz
        | cons a Zr => exact ⟨a, Zr, rfl⟩
      have hTa : T.getD 0 0 = a := by
        simp only [hT, lstOf, hZr, List.cons_append, List.getD_cons_zero]
      rw [hTa] at hlt
      have hpw := List.sortedLT_iff_pairwise.mp hsl'.sorted
      rw [hZr] at hz hpw
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hlt
      · exact lt_trans hlt ((List.pairwise_cons.mp hpw).1 z hz)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxn
      · exact hsl'.lt z hz
    · simp only [List.length_cons]; omega
    · unfold codeL
      rw [lstOf_cons hm hZ1, ← hT, ← hcE]

theorem recursion_of_isCode {n m c : ℕ} (hm : 1 ≤ m) (hc : IsCode n m c) :
    c = top n m ∨ (x1 n m c < x2 n m c ∧ IsCode n m (sufc n m c)) := by
  obtain ⟨Zs, hsl, rfl⟩ := hc
  cases Zs with
  | nil => left; rw [top_eq]
  | cons j Zs' =>
    right
    set b := n + 1 with hb
    have hb0 : 0 < b := by omega
    have hTsl : SL n (m - 1) Zs' := sl_tail hsl
    have hZ1 : Zs'.length ≤ m - 1 := hTsl.len
    set T := lstOf n (m - 1) Zs' with hT
    have hTlen : T.length = m - 1 := hTsl.lstOf_length
    have hTlt : ∀ x ∈ T, x < b := hTsl.lstOf_lt
    have hjn : j < n := hsl.lt j (by simp)
    have hcE : codeL n m (j :: Zs') = enc b (j :: T) := by
      unfold codeL; rw [lstOf_cons hm hZ1]
    have hdm := div_mod_pow b j (enc b T) (m - 1) hb0 (hTlen ▸ enc_lt hTlt)
    have hx1 : x1 n m (codeL n m (j :: Zs')) = j := by
      unfold x1; rw [hcE, enc_cons, hTlen]; exact hdm.1
    have hsuf : sufc n m (codeL n m (j :: Zs')) = codeL n m Zs' := by
      unfold sufc
      rw [hcE, enc_cons, hTlen, hdm.2]
      unfold codeL
      rw [lstOf_snoc (by omega), enc_snoc]
    refine ⟨?_, ?_⟩
    · rw [hx1]
      by_cases hm1 : m = 1
      · unfold x2; rw [if_pos hm1]; exact hjn
      · have hm2 : 2 ≤ m := by omega
        rw [hcE, x2_eq hm2 hTlen (by omega) hTlt]
        cases hZ : Zs' with
        | nil =>
          have : T.getD 0 0 = n := by
            simp only [hT, lstOf, hZ, List.nil_append, List.length_nil, Nat.sub_zero]
            obtain ⟨t, ht⟩ : ∃ t, m - 1 = t + 1 := ⟨m - 2, by omega⟩
            rw [ht]; simp [List.replicate_succ]
          rw [this]; exact hjn
        | cons a Zr =>
          have hTa : T.getD 0 0 = a := by
            simp only [hT, lstOf, hZ, List.cons_append, List.getD_cons_zero]
          rw [hTa]
          have := List.sortedLT_iff_pairwise.mp hsl.sorted
          rw [hZ] at this
          exact (List.pairwise_cons.mp this).1 a (by simp)
    · rw [hsuf]
      exact ⟨Zs', ⟨hTsl.sorted, hTsl.lt, by omega⟩, rfl⟩

theorem sufc_lt_pow {n m c : ℕ} (hm : 1 ≤ m) : sufc n m c < (n + 1) ^ m := by
  set b := n + 1 with hb
  have hb0 : 0 < b := by omega
  have hB : 0 < b ^ (m - 1) := pow_pos hb0 _
  have hr : c % b ^ (m - 1) < b ^ (m - 1) := Nat.mod_lt _ hB
  have hpow : b ^ m = b ^ (m - 1) * b := by rw [← pow_succ]; congr 1; omega
  unfold sufc
  simp only [← hb]
  rw [hpow]
  have : (c % b ^ (m - 1) + 1) * b ≤ b ^ (m - 1) * b := Nat.mul_le_mul_right _ hr
  nlinarith

theorem sufc_gt {n m c : ℕ} (hm : 1 ≤ m) (h : x1 n m c < x2 n m c) : c < sufc n m c := by
  set b := n + 1 with hb
  have hb0 : 0 < b := by omega
  by_cases hm1 : m = 1
  · subst hm1
    simp only [x1, x2, sufc, if_true, pow_zero, Nat.mod_one, zero_mul, zero_add,
      Nat.div_one, Nat.sub_self] at *
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
    have e1 : t + 2 - 1 = t + 1 := by omega
    have e2 : t + 2 - 2 = t := by omega
    have hB2 : 0 < b ^ t := pow_pos hb0 _
    have hB1 : b ^ (t + 1) = b ^ t * b := pow_succ b t
    simp only [x1, x2, sufc, e1, e2, if_neg hm1, ← hb] at h ⊢
    set B2 := b ^ t with hB2d
    set r := c % b ^ (t + 1) with hr
    set q1 := c / b ^ (t + 1) with hq1
    have hdm : b ^ (t + 1) * q1 + r = c := Nat.div_add_mod c (b ^ (t + 1))
    have hrlt : r < b ^ (t + 1) := Nat.mod_lt _ (pow_pos hb0 _)
    -- the second digit is at most `r / B2`
    have hc2 : c / B2 = r / B2 + b * q1 := by
      have : c = r + B2 * (b * q1) := by rw [← hdm, hB1]; ring
      rw [this, Nat.add_mul_div_left _ _ hB2]
    have hx2 : c / B2 % b ≤ r / B2 := by
      rw [hc2, Nat.add_mul_mod_self_left]; exact Nat.mod_le _ _
    have h3 : (c / B2 % b) * B2 ≤ r := by
      calc (c / B2 % b) * B2 ≤ (r / B2) * B2 := Nat.mul_le_mul_right _ hx2
        _ ≤ r := Nat.div_mul_le_self r B2
    have h4 : (q1 + 1) * b ^ (t + 1) ≤ r * b := by
      have : (q1 + 1) * B2 ≤ r := le_trans (Nat.mul_le_mul_right _ h) h3
      calc (q1 + 1) * b ^ (t + 1) = ((q1 + 1) * B2) * b := by rw [hB1]; ring
        _ ≤ r * b := Nat.mul_le_mul_right _ this
    nlinarith

/-- **The recurrence the `VALID` array is filled by.** -/
theorem isCode_iff {n m c : ℕ} (hm : 1 ≤ m) (hc : c < (n + 1) ^ m) :
    IsCode n m c ↔ c = top n m ∨ (x1 n m c < x2 n m c ∧ IsCode n m (sufc n m c)) :=
  ⟨recursion_of_isCode hm, isCode_of_recursion hm hc⟩

end Lax496464Proofs.Ram.D2Valid
