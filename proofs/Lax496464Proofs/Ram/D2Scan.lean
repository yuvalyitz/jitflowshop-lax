import Lax496464Proofs.Ram.D2Digits

/-!
# Theorem 2, pure layer 2: replacing the smallest threshold

The recursion (1) of Section 3 removes the smallest threshold `j` of `X` and inserts the smallest
index `≥ y` not already in `X` (`y = j+1` for `X₁`, `y = nxt j` for `X₂`).  On digit strings that is
one left-to-right scan of the tail of the string (`scanF`) followed by one rotation of a prefix, and
on the numbers it is `((c / b^q % b^k) * b + cur) * b^q + c % b^q`.  This file proves the scan
correct (`scanF_ok`), that the rotated string is again a code (`SL.ins`), the formula for its number
(`code_formula`), and that its number is larger than the old one (`code_lt`).
-/

namespace Lax496464Proofs.Ram.D2Scan

open Lax496464Proofs.Ram.D2Digits

/-- The scan: `cur` is the candidate, the list the digits after the smallest one.  Returns the
final candidate and the number of digits passed. -/
def scanF (n : ℕ) : List ℕ → ℕ → ℕ × ℕ
  | [], cur => (cur, 0)
  | x :: T, cur =>
    if x < n ∧ x ≤ cur then
      ((scanF n T (if x = cur then cur + 1 else cur)).1,
        (scanF n T (if x = cur then cur + 1 else cur)).2 + 1)
    else (cur, 0)

/-- What the scan promises about a sorted list `Zs` of thresholds. -/
structure ScanOK (n : ℕ) (Zs : List ℕ) (cur : ℕ) (r : ℕ × ℕ) : Prop where
  le_n : r.1 ≤ n
  ge : cur ≤ r.1
  notMem : r.1 ∉ Zs
  cover : ∀ v, cur ≤ v → v < r.1 → v ∈ Zs
  k_le : r.2 ≤ Zs.length
  take_lt : ∀ z ∈ Zs.take r.2, z < r.1
  drop_gt : ∀ z ∈ Zs.drop r.2, r.1 < z

theorem scanF_ok (n : ℕ) :
    ∀ (Zs : List ℕ) (p cur : ℕ), Zs.Pairwise (· < ·) → (∀ z ∈ Zs, z < n) → cur ≤ n →
      ScanOK n Zs cur (scanF n (Zs ++ List.replicate p n) cur) := by
  intro Zs
  induction Zs with
  | nil =>
    intro p cur _ _ hc
    have h : scanF n (List.replicate p n) cur = (cur, 0) := by
      cases p with
      | zero => rfl
      | succ p => simp [List.replicate_succ, scanF]
    simp only [List.nil_append, h]
    exact ⟨hc, le_rfl, by simp, fun v h1 h2 => absurd h2 (by omega), le_rfl, by simp, by simp⟩
  | cons z Zs ih =>
    intro p cur hpw hlt hc
    have hz : z < n := hlt z (by simp)
    rw [List.pairwise_cons] at hpw
    have hpw' := hpw.2
    have hzs : ∀ y ∈ Zs, z < y := hpw.1
    have hlt' : ∀ y ∈ Zs, y < n := fun y hy => hlt y (List.mem_cons_of_mem _ hy)
    by_cases hzc : z ≤ cur
    · -- consume or skip
      have hc' : (if z = cur then cur + 1 else cur) ≤ n := by
        split_ifs with h
        · omega
        · exact hc
      have IH := ih p _ hpw' hlt' hc'
      have hsc : scanF n (z :: Zs ++ List.replicate p n) cur =
          ((scanF n (Zs ++ List.replicate p n) (if z = cur then cur + 1 else cur)).1,
           (scanF n (Zs ++ List.replicate p n) (if z = cur then cur + 1 else cur)).2 + 1) := by
        simp only [List.cons_append, scanF, hz, hzc, and_self, if_true]
      rw [hsc]
      set r := scanF n (Zs ++ List.replicate p n) (if z = cur then cur + 1 else cur) with hr
      have hcur' : cur ≤ (if z = cur then cur + 1 else cur) := by split_ifs <;> omega
      have hzlt : z < (if z = cur then cur + 1 else cur) := by
        split_ifs with h
        · omega
        · omega
      refine ⟨IH.le_n, le_trans hcur' IH.ge, ?_, ?_, ?_, ?_, ?_⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · have := IH.ge; simp only at h ⊢; omega
        · exact IH.notMem h
      · intro v hv1 hv2
        show v ∈ z :: Zs
        by_cases hv : v < (if z = cur then cur + 1 else cur)
        · have : z = cur := by
            by_contra hne
            simp only [hne, if_false] at hv
            omega
          simp only [this, if_true] at hv
          have : v = cur := by omega
          rw [this]; simp [*]
        · exact List.mem_cons_of_mem _ (IH.cover v (by omega) hv2)
      · simp only [List.length_cons]; have := IH.k_le; omega
      · intro y hy
        simp only [List.take_succ_cons, List.mem_cons] at hy
        rcases hy with h | h
        · have := IH.ge; simp only at h ⊢; omega
        · exact IH.take_lt y h
      · intro y hy
        simp only [List.drop_succ_cons] at hy
        exact IH.drop_gt y hy
    · -- stop
      have hzc' : cur < z := by omega
      have hsc : scanF n (z :: Zs ++ List.replicate p n) cur = (cur, 0) := by
        simp only [List.cons_append, scanF]
        rw [if_neg (by omega)]
      rw [hsc]
      refine ⟨hc, le_rfl, ?_, fun v h1 h2 => absurd h2 (by omega), by simp, by simp, ?_⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · simp only at h; omega
        · have := hzs cur h; omega
      · intro y hy
        simp only [List.drop_zero, List.mem_cons] at hy
        rcases hy with h | h
        · simp only; omega
        · have := hzs y h; simp only; omega

/-- Insert `v` after the first `k` elements. -/
def ins (Zs : List ℕ) (k v : ℕ) : List ℕ := Zs.take k ++ v :: Zs.drop k

theorem mem_ins {Zs : List ℕ} {k v x : ℕ} : x ∈ ins Zs k v ↔ x = v ∨ x ∈ Zs := by
  unfold ins
  constructor
  · intro h
    simp only [List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · right; exact List.mem_of_mem_take h
    · left; exact h
    · right; exact List.mem_of_mem_drop h
  · rintro (h | h)
    · simp [h]
    · have := List.take_append_drop k Zs
      rw [← this] at h
      simp only [List.mem_append] at h
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem length_ins {Zs : List ℕ} {k v : ℕ} (hk : k ≤ Zs.length) : (ins Zs k v).length = Zs.length + 1 := by
  simp [ins]; omega

theorem ins_pairwise {Zs : List ℕ} {k v : ℕ} (hp : Zs.Pairwise (· < ·))
    (h1 : ∀ z ∈ Zs.take k, z < v) (h2 : ∀ z ∈ Zs.drop k, v < z) :
    (ins Zs k v).Pairwise (· < ·) := by
  unfold ins
  have hsplit := hp
  rw [← List.take_append_drop k Zs, List.pairwise_append] at hsplit
  obtain ⟨hA, hB, hAB⟩ := hsplit
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hA, ⟨h2, hB⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h1 a ha
  · exact hAB a ha b hb


theorem lstOf_cons {n m j : ℕ} {Zs : List ℕ} (_hm : 1 ≤ m) (_h : Zs.length ≤ m - 1) :
    lstOf n m (j :: Zs) = j :: lstOf n (m - 1) Zs := by
  have : m - (Zs.length + 1) = m - 1 - Zs.length := by omega
  simp only [lstOf, List.length_cons, List.cons_append, this]

/-- The new set after the scan: `cur` inserted, unless it is the padding digit. -/
def newL (n : ℕ) (Zs : List ℕ) (cur k : ℕ) : List ℕ := if cur < n then ins Zs k cur else Zs

theorem rot_lst {n m : ℕ} {Zs : List ℕ} (hm : 1 ≤ m) (hsl : SL n (m - 1) Zs) {c0 cur k : ℕ}
    (hr : ScanOK n Zs c0 (cur, k)) :
    lstOf n m (newL n Zs cur k) =
      (lstOf n (m - 1) Zs).take k ++ cur :: (lstOf n (m - 1) Zs).drop k := by
  have hk : k ≤ Zs.length := hr.k_le
  have hlen := hsl.len
  have hT1 : (lstOf n (m - 1) Zs).take k = Zs.take k := by
    simp only [lstOf]; exact List.take_append_of_le_length hk
  have hT2 : (lstOf n (m - 1) Zs).drop k =
      Zs.drop k ++ List.replicate (m - 1 - Zs.length) n := by
    simp only [lstOf]; exact List.drop_append_of_le_length hk
  rw [hT1, hT2]
  unfold newL
  by_cases hcn : cur < n
  · rw [if_pos hcn]
    unfold ins lstOf
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    have : m - (min k Zs.length + (Zs.length - k + 1)) = m - 1 - Zs.length := by
      rw [min_eq_left hk]; omega
    rw [this]
    simp
  · rw [if_neg hcn]
    have hcur : cur = n := by have := hr.le_n; simp only at this; omega
    have hdrop : Zs.drop k = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have h1 := hr.drop_gt z hz
      have h2 := hsl.lt z (List.mem_of_mem_drop hz)
      simp only at h1; omega
    have hkk : k = Zs.length := by
      have := List.length_drop (i := k) (l := Zs)
      rw [hdrop] at this
      simp at this; omega
    rw [hdrop, hcur, hkk, List.take_length]
    unfold lstOf
    have : m - Zs.length = (m - 1 - Zs.length) + 1 := by omega
    rw [this, List.replicate_succ]
    simp

theorem newL_sl {n m : ℕ} {Zs : List ℕ} (hm : 1 ≤ m) (hsl : SL n (m - 1) Zs) {c0 cur k : ℕ}
    (hr : ScanOK n Zs c0 (cur, k)) : SL n m (newL n Zs cur k) := by
  have hk : k ≤ Zs.length := hr.k_le
  have hp : Zs.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp hsl.sorted
  unfold newL
  by_cases hcn : cur < n
  · rw [if_pos hcn]
    refine ⟨List.sortedLT_iff_pairwise.mpr (ins_pairwise hp hr.take_lt hr.drop_gt), ?_, ?_⟩
    · intro z hz
      rcases mem_ins.mp hz with rfl | hz
      · exact hcn
      · exact hsl.lt z hz
    · rw [length_ins hk]; have := hsl.len; omega
  · rw [if_neg hcn]
    exact ⟨hsl.sorted, hsl.lt, by have := hsl.len; omega⟩

/-- **The number of the rotated string**, from the number of the old one. -/
theorem code_formula {n m : ℕ} {j : ℕ} {Zs : List ℕ} (hm : 1 ≤ m) (hsl : SL n (m - 1) Zs)
    (_hj : j < n + 1) {c0 cur k : ℕ} (hr : ScanOK n Zs c0 (cur, k)) (_hcur : cur < n + 1) :
    codeL n m (newL n Zs cur k) =
      ((codeL n m (j :: Zs) / (n + 1) ^ (m - 1 - k) % (n + 1) ^ k) * (n + 1) + cur) *
        (n + 1) ^ (m - 1 - k) + codeL n m (j :: Zs) % (n + 1) ^ (m - 1 - k) := by
  have hk : k ≤ Zs.length := hr.k_le
  have hlen := hsl.len
  set b := n + 1 with hb
  have hb0 : 0 < b := by omega
  set T := lstOf n (m - 1) Zs with hT
  have hTlen : T.length = m - 1 := hsl.lstOf_length
  have hTlt : ∀ x ∈ T, x < b := hsl.lstOf_lt
  have hc : codeL n m (j :: Zs) = enc b (j :: T) := by
    unfold codeL; rw [lstOf_cons hm hlen]
  have hnew : codeL n m (newL n Zs cur k) = enc b (T.take k ++ cur :: T.drop k) := by
    unfold codeL; rw [rot_lst hm hsl hr]
  rw [hc, hnew]
  set q := m - 1 - k with hq
  have hdl : (T.drop k).length = q := by simp [hTlen]; omega
  have htl : (T.take k).length = k := by simp [hTlen]; omega
  have hd_lt : enc b (T.drop k) < b ^ q := by
    have := enc_lt (b := b) (L := T.drop k) (fun x hx => hTlt x (List.mem_of_mem_drop hx))
    rwa [hdl] at this
  have ht_lt : enc b (T.take k) < b ^ k := by
    have := enc_lt (b := b) (L := T.take k) (fun x hx => hTlt x (List.mem_of_mem_take hx))
    rwa [htl] at this
  have hT_eq : enc b T = enc b (T.take k) * b ^ q + enc b (T.drop k) := by
    conv_lhs => rw [← List.take_append_drop k T]
    rw [enc_append, hdl]
  have hcE : enc b (j :: T) = (j * b ^ k + enc b (T.take k)) * b ^ q + enc b (T.drop k) := by
    rw [enc_cons, hTlen, hT_eq]
    have : b ^ (m - 1) = b ^ k * b ^ q := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hdm := div_mod_pow b (j * b ^ k + enc b (T.take k)) (enc b (T.drop k)) q hb0 hd_lt
  rw [hcE, hdm.1, hdm.2]
  have hdm2 := div_mod_pow b j (enc b (T.take k)) k hb0 ht_lt
  rw [hdm2.2]
  have hnE : enc b (T.take k ++ cur :: T.drop k) =
      (enc b (T.take k) * b + cur) * b ^ q + enc b (T.drop k) := by
    have : T.take k ++ cur :: T.drop k = (T.take k ++ [cur]) ++ T.drop k := by simp
    rw [this, enc_append, hdl, enc_append]
    simp
  rw [hnE]

/-- The rotated string, read as a number, is larger than the old one: its first digit is larger. -/
theorem enc_lt_of_head {b : ℕ} {d : ℕ} {A A' : List ℕ} {d' : ℕ} (hA : ∀ x ∈ A, x < b)
    (hl : A.length = A'.length) (hdd : d < d') :
    enc b (d :: A) < enc b (d' :: A') := by
  have h1 := enc_lt hA
  simp only [enc_cons, ← hl] at *
  have : (d + 1) * b ^ A.length ≤ d' * b ^ A.length := Nat.mul_le_mul_right _ hdd
  nlinarith [Nat.zero_le (enc b A')]

theorem code_lt {n m : ℕ} {j : ℕ} {Zs : List ℕ} (hm : 1 ≤ m) (hsl : SL n (m - 1) Zs)
    (hjn : j < n) (hjZ : ∀ z ∈ Zs, j < z) {c0 cur k : ℕ} (hr : ScanOK n Zs c0 (cur, k))
    (hjc : j < c0) :
    codeL n m (j :: Zs) < codeL n m (newL n Zs cur k) := by
  have hk : k ≤ Zs.length := hr.k_le
  set b := n + 1 with hb
  set T := lstOf n (m - 1) Zs with hT
  have hTlen : T.length = m - 1 := hsl.lstOf_length
  have hTlt : ∀ x ∈ T, x < b := hsl.lstOf_lt
  have hc : codeL n m (j :: Zs) = enc b (j :: T) := by
    unfold codeL; rw [lstOf_cons hm hsl.len]
  have hnew : codeL n m (newL n Zs cur k) = enc b (T.take k ++ cur :: T.drop k) := by
    unfold codeL; rw [rot_lst hm hsl hr]
  rw [hc, hnew]
  -- every entry of the new string exceeds `j`
  have hTj : ∀ x ∈ T, j < x := by
    intro x hx
    simp only [hT, lstOf, List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨-, rfl⟩
    · exact hjZ x hx
    · exact hjn
  have hcurj : j < cur := lt_of_lt_of_le hjc hr.ge
  have hne : T.take k ++ cur :: T.drop k ≠ [] := by simp
  obtain ⟨d', A', hdA⟩ : ∃ d' A', T.take k ++ cur :: T.drop k = d' :: A' := by
    cases h : T.take k ++ cur :: T.drop k with
    | nil => exact absurd h hne
    | cons d' A' => exact ⟨d', A', rfl⟩
  have hd'j : j < d' := by
    have hmem : d' ∈ T.take k ++ cur :: T.drop k := by rw [hdA]; simp
    simp only [List.mem_append, List.mem_cons] at hmem
    rcases hmem with h | h | h
    · exact hTj d' (List.mem_of_mem_take h)
    · rw [h]; exact hcurj
    · exact hTj d' (List.mem_of_mem_drop h)
  have hlenA : T.length = A'.length := by
    have := congrArg List.length hdA
    simp only [List.length_append, List.length_cons, List.length_take, List.length_drop] at this
    omega
  rw [hdA]
  exact enc_lt_of_head hTlt hlenA hd'j

end Lax496464Proofs.Ram.D2Scan
