import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits

/-! # Blocks of slots: partial knowledge of a sorted set of codes

The weight-`k` set of tuple codes is written as its increasing list `t = t_0 < … < t_{k-1}` of codes
below `N`. A *block* is a list of `D` slots; slot `j` names an index `b_j ≤ k` (the value `k`
meaning *unused*) and a value `v_j ≤ N`. A block with values is *consistent* with `t` if every used
slot carries the right value, `v_j = t_{b_j}`.

* `no_conflict`: two blocks consistent with a valid `t` are not in `conflict`: a used slot with a
  value `≥ N`, two slots of one index with different values, or two slots whose values are not in
  the order of their indices.
* `exists_valid`: conversely, a choice of values for all blocks without conflicts comes from a
  valid `t` (read off the blocks with one used slot, `single i`).
* `dec`: what a block says about a code `u`: `u ∈ t` if a used slot has value `u`; `u ∉ t` if
  `k = 0`, or `u` is below the value of index `0`, above that of index `k-1`, or strictly between
  the values of two consecutive indices; nothing otherwise. `dec_sound`: a consistent block says
  only true things. `dec_complete`: for a few codes (at most `D / 2`) some block, with the values
  of `t`, decides all of them. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks

open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits

/-- The entry `j` of a list, `0` out of range. -/
abbrev g (l : List ℕ) (j : ℕ) : ℕ := l.getD j 0

/-- `t` is an increasing list of `k` codes below `N`. -/
structure Valid (k N : ℕ) (t : List ℕ) : Prop where
  len : t.length = k
  lt : ∀ i < k, g t i < N
  mono : ∀ i i', i < i' → i' < k → g t i < g t i'

/-- The used slots carry the values of `t`. -/
def Consistent (k : ℕ) (t bl vl : List ℕ) : Prop :=
  ∀ j < bl.length, g bl j < k → g vl j = g t (g bl j)

/-- **A conflict** between two blocks with values. -/
def Conflict (k N D : ℕ) (b1 v1 b2 v2 : List ℕ) : Prop :=
  ∃ j < D, ∃ j' < D, g b1 j < k ∧ (N ≤ g v1 j ∨ (g b2 j' < k ∧
    ((g b1 j = g b2 j' ∧ g v1 j ≠ g v2 j') ∨ (g b1 j < g b2 j' ∧ g v2 j' ≤ g v1 j))))

instance (k N D : ℕ) (b1 v1 b2 v2 : List ℕ) : Decidable (Conflict k N D b1 v1 b2 v2) := by
  unfold Conflict; infer_instance

/-- A used slot has the value `u`. -/
def DecT (k D : ℕ) (bl vl : List ℕ) (u : ℕ) : Prop := ∃ j < D, g bl j < k ∧ g vl j = u

/-- The block shows that `u` is not among the values. -/
def DecF (k D : ℕ) (bl vl : List ℕ) (u : ℕ) : Prop :=
  k = 0 ∨ (∃ j < D, g bl j = 0 ∧ u < g vl j) ∨ (∃ j < D, g bl j + 1 = k ∧ g vl j < u) ∨
    ∃ j < D, ∃ j' < D, g bl j + 1 = g bl j' ∧ g bl j' < k ∧ g vl j < u ∧ u < g vl j'

instance (k D : ℕ) (bl vl : List ℕ) (u : ℕ) : Decidable (DecT k D bl vl u) := by
  unfold DecT; infer_instance

instance (k D : ℕ) (bl vl : List ℕ) (u : ℕ) : Decidable (DecF k D bl vl u) := by
  unfold DecF; infer_instance

/-- **What a block says about `u`.** -/
def dec (k D : ℕ) (bl vl : List ℕ) (u : ℕ) : Option Bool :=
  if DecT k D bl vl u then some true else if DecF k D bl vl u then some false else none

theorem getD_mem {l : List ℕ} {j : ℕ} (h : j < l.length) : g l j ∈ l := by
  unfold g; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

section Valid
variable {k N : ℕ} {t : List ℕ} (ht : Valid k N t)
include ht

theorem Valid.mem_iff {u : ℕ} : u ∈ t ↔ ∃ i < k, g t i = u := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    refine ⟨i, by rw [← ht.len]; exact hi, ?_⟩
    unfold g; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  · rintro ⟨i, hi, rfl⟩; exact getD_mem (by rw [ht.len]; exact hi)

theorem Valid.le_of_le {i i' : ℕ} (h : i ≤ i') (hi' : i' < k) : g t i ≤ g t i' := by
  rcases Nat.lt_or_ge i i' with h' | h'
  · exact (ht.mono i i' h' hi').le
  · rw [Nat.le_antisymm h h']

theorem Valid.inj {i i' : ℕ} (hi : i < k) (hi' : i' < k) (h : g t i = g t i') : i = i' := by
  rcases Nat.lt_trichotomy i i' with h' | h' | h'
  · have := ht.mono i i' h' hi'; omega
  · exact h'
  · have := ht.mono i' i h' hi; omega

end Valid

/-! ### No conflicts -/

/-- **Blocks consistent with a valid `t` are not in conflict.** -/
theorem no_conflict {k N D : ℕ} {t b1 v1 b2 v2 : List ℕ} (ht : Valid k N t)
    (hl1 : b1.length = D) (hl2 : b2.length = D) (h1 : Consistent k t b1 v1)
    (h2 : Consistent k t b2 v2) : ¬ Conflict k N D b1 v1 b2 v2 := by
  rintro ⟨j, hj, j', hj', hb1, hc⟩
  have e1 := h1 j (by rw [hl1]; exact hj) hb1
  have hlt := ht.lt _ hb1
  rcases hc with hc | ⟨hb2, hc⟩
  · omega
  · have e2 := h2 j' (by rw [hl2]; exact hj') hb2
    rcases hc with ⟨he, hne⟩ | ⟨hlt', hle⟩
    · exact hne (by rw [e1, e2, he])
    · have := ht.mono _ _ hlt' hb2
      omega

/-! ### Blocks with one used slot -/

/-- The block using only slot `0`, for index `i`. -/
def single (k D i : ℕ) : ℕ := codeOf (k + 1) (i :: List.replicate (D - 1) k)

theorem single_digits {k D i : ℕ} (hD : 1 ≤ D) (hi : i ≤ k) :
    digits (k + 1) D (single k D i) = i :: List.replicate (D - 1) k := by
  have hl : (i :: List.replicate (D - 1) k).length = D := by simp; omega
  have := digits_codeOf (n := k + 1) (i :: List.replicate (D - 1) k) (fun d hd => by
    simp only [List.mem_cons, List.mem_replicate] at hd
    omega)
  rw [hl] at this; exact this

theorem single_lt {k D i : ℕ} (hD : 1 ≤ D) (hi : i ≤ k) : single k D i < (k + 1) ^ D := by
  have := codeOf_lt (n := k + 1) (i :: List.replicate (D - 1) k) (fun d hd => by
    simp only [List.mem_cons, List.mem_replicate] at hd
    omega)
  have hl : (i :: List.replicate (D - 1) k).length = D := by simp; omega
  rw [hl] at this; exact this

/-- **A conflict-free choice of values comes from a valid `t`.** -/
theorem exists_valid {k N D : ℕ} (hD : 1 ≤ D) (v : ℕ → ℕ)
    (hnc : ∀ b1 < (k + 1) ^ D, ∀ b2 < (k + 1) ^ D, ¬ Conflict k N D (digits (k + 1) D b1)
      (digits (N + 1) D (v b1)) (digits (k + 1) D b2) (digits (N + 1) D (v b2))) :
    ∃ t, Valid k N t ∧
      ∀ b < (k + 1) ^ D, Consistent k t (digits (k + 1) D b) (digits (N + 1) D (v b)) := by
  set val : ℕ → ℕ := fun i => g (digits (N + 1) D (v (single k D i))) 0 with hval
  set t := (List.range k).map val with htdef
  have ht : ∀ i < k, g t i = val i := by
    intro i hi
    simp [htdef, g, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hsd : ∀ i < k, g (digits (k + 1) D (single k D i)) 0 = i := by
    intro i hi; rw [single_digits hD hi.le]; rfl
  have hD0 : 0 < D := hD
  refine ⟨t, ⟨by simp [htdef], fun i hi => ?_, fun i i' hii hi' => ?_⟩, fun b hb j hj hbj => ?_⟩
  · rw [ht i hi]
    by_contra hn
    exact hnc (single k D i) (single_lt hD hi.le) (single k D i) (single_lt hD hi.le)
      ⟨0, hD0, 0, hD0, by rw [hsd i hi]; exact hi, Or.inl (by simp only [hval] at hn ⊢; omega)⟩
  · have hik : i < k := by omega
    rw [ht i hik, ht i' hi']
    by_contra hn
    exact hnc (single k D i) (single_lt hD hik.le) (single k D i') (single_lt hD hi'.le)
      ⟨0, hD0, 0, hD0, by rw [hsd i hik]; exact hik, Or.inr ⟨by rw [hsd i' hi']; exact hi',
        Or.inr ⟨by rw [hsd i hik, hsd i' hi']; exact hii, by simp only [hval] at hn ⊢; omega⟩⟩⟩
  · rw [length_digits] at hj
    set i := g (digits (k + 1) D b) j with hi
    rw [ht i hbj]
    by_contra hn
    exact hnc b hb (single k D i) (single_lt hD hbj.le)
      ⟨j, hj, 0, hD0, hbj, Or.inr ⟨by rw [hsd i hbj]; exact hbj,
        Or.inl ⟨by rw [hsd i hbj], by simp only [hval] at hn ⊢; exact hn⟩⟩⟩

/-! ### The canonical values of a block -/

/-- The values `t` gives the slots of a block. -/
def canonL (k : ℕ) (t bl : List ℕ) : List ℕ := bl.map fun i => if i < k then g t i else 0

/-- Their code. -/
def canon (k N D : ℕ) (t : List ℕ) (b : ℕ) : ℕ :=
  codeOf (N + 1) (canonL k t (digits (k + 1) D b))

section Canon
variable {k N D : ℕ} {t : List ℕ} (ht : Valid k N t)
include ht

theorem canonL_lt (bl : List ℕ) : ∀ d ∈ canonL k t bl, d < N + 1 := by
  intro d hd
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
  split_ifs with h
  · have := ht.lt i h; omega
  · omega

omit ht in
theorem length_canonL (bl : List ℕ) : (canonL k t bl).length = bl.length := by simp [canonL]

theorem canon_digits (b : ℕ) :
    digits (N + 1) D (canon k N D t b) = canonL k t (digits (k + 1) D b) := by
  have := digits_codeOf (canonL k t (digits (k + 1) D b)) (canonL_lt ht _)
  rw [length_canonL, length_digits] at this
  exact this

theorem canon_lt (b : ℕ) : canon k N D t b < (N + 1) ^ D := by
  have := codeOf_lt (canonL k t (digits (k + 1) D b)) (canonL_lt ht _)
  rw [length_canonL, length_digits] at this
  exact this

theorem canon_consistent (b : ℕ) :
    Consistent k t (digits (k + 1) D b) (digits (N + 1) D (canon k N D t b)) := by
  intro j hj hjk
  rw [canon_digits ht]
  unfold canonL g
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  simp only [Option.map_some, Option.getD_some]
  rw [if_pos (by
    have : (digits (k + 1) D b).getD j 0 = (digits (k + 1) D b)[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [← this]; exact hjk)]
  rw [List.getD_eq_getElem?_getD (l := digits (k + 1) D b), List.getElem?_eq_getElem hj]
  rfl

end Canon

/-! ### Soundness of the decisions -/

/-- **A consistent block says only true things.** -/
theorem dec_sound {k N D : ℕ} {t bl vl : List ℕ} (ht : Valid k N t) (hl : bl.length = D)
    (hc : Consistent k t bl vl) (u : ℕ) :
    (dec k D bl vl u = some true → u ∈ t) ∧ (dec k D bl vl u = some false → u ∉ t) := by
  have hcj : ∀ j < D, g bl j < k → g vl j = g t (g bl j) := fun j hj => hc j (by rw [hl]; exact hj)
  unfold dec
  constructor
  · intro h
    by_cases h1 : DecT k D bl vl u
    · obtain ⟨j, hj, hb, hv⟩ := h1
      rw [ht.mem_iff]; exact ⟨_, hb, by rw [← hv, hcj j hj hb]⟩
    · rw [if_neg h1] at h
      split_ifs at h
      simp at h
  · intro h hmem
    by_cases h1 : DecT k D bl vl u
    · rw [if_pos h1] at h; simp at h
    rw [if_neg h1] at h
    by_cases h2 : DecF k D bl vl u
    swap
    · rw [if_neg h2] at h; simp at h
    obtain ⟨i, hi, rfl⟩ := ht.mem_iff.mp hmem
    rcases h2 with h2 | ⟨j, hj, hb, hu⟩ | ⟨j, hj, hb, hu⟩ | ⟨j, hj, j', hj', hb, hb', hu1, hu2⟩
    · omega
    · rw [hcj j hj (by omega), hb] at hu
      have := ht.le_of_le (Nat.zero_le i) hi
      omega
    · rw [hcj j hj (by omega), show g bl j = k - 1 by omega] at hu
      have := ht.le_of_le (show i ≤ k - 1 by omega) (by omega)
      omega
    · rw [hcj j hj (by omega)] at hu1
      rw [hcj j' hj' hb'] at hu2
      rcases Nat.lt_or_ge i (g bl j') with h3 | h3
      · have := ht.le_of_le (show i ≤ g bl j by omega) (by omega)
        omega
      · have := ht.le_of_le h3 hi
        omega

/-! ### Completeness of the decisions -/

section Complete
variable {k N : ℕ} {t : List ℕ} (ht : Valid k N t)

open Classical in
/-- The indices a block needs to decide `u`. -/
noncomputable def wit (k : ℕ) (t : List ℕ) (u : ℕ) : List ℕ :=
  if u ∈ t then [t.idxOf u]
  else if k = 0 then []
  else if h : ∃ i, i < k ∧ u < g t i then
    (if Nat.find h = 0 then [0] else [Nat.find h - 1, Nat.find h])
  else [k - 1]

theorem length_wit (u : ℕ) : (wit k t u).length ≤ 2 := by
  unfold wit; split_ifs <;> simp

include ht

theorem wit_lt (u : ℕ) : ∀ i ∈ wit k t u, i < k := by
  intro i hi
  unfold wit at hi
  split_ifs at hi with h1 h2 h3 h4
  · simp only [List.mem_singleton] at hi; subst hi
    rw [← ht.len]; exact List.idxOf_lt_length_iff.mpr h1
  · simp at hi
  · simp only [List.mem_singleton] at hi; subst hi; omega
  · have := (Nat.find_spec h3).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  · simp only [List.mem_singleton] at hi; omega

/-- A block whose used slots include those of `u`'s witnesses and carry the values of `t` decides
`u` correctly. -/
theorem dec_of_wit {D : ℕ} {bl vl : List ℕ} (hl : bl.length = D) (hc : Consistent k t bl vl)
    (u : ℕ) (hw : ∀ i ∈ wit k t u, ∃ j < D, g bl j = i) :
    dec k D bl vl u = some (decide (u ∈ t)) := by
  have hcj : ∀ j < D, g bl j < k → g vl j = g t (g bl j) := fun j hj => hc j (by rw [hl]; exact hj)
  by_cases hu : u ∈ t
  · have hw' := hw (t.idxOf u) (by unfold wit; rw [if_pos hu]; simp)
    obtain ⟨j, hj, hbj⟩ := hw'
    have hik : t.idxOf u < k := by rw [← ht.len]; exact List.idxOf_lt_length_iff.mpr hu
    have hT : DecT k D bl vl u := ⟨j, hj, by rw [hbj]; exact hik, by
      rw [hcj j hj (by rw [hbj]; exact hik), hbj]
      unfold g
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hu)]
      simp⟩
    simp [dec, hT, hu]
  · have hT : ¬ DecT k D bl vl u := by
      rintro ⟨j, hj, hb, hv⟩
      apply hu
      rw [ht.mem_iff]; exact ⟨_, hb, by rw [← hv, hcj j hj hb]⟩
    have hF : DecF k D bl vl u := by
      by_cases hk : k = 0
      · exact Or.inl hk
      by_cases h : ∃ i, i < k ∧ u < g t i
      · have hwit : wit k t u =
            if Nat.find h = 0 then [0] else [Nat.find h - 1, Nat.find h] := by
          unfold wit; rw [if_neg hu, if_neg hk, dif_pos h]
        obtain ⟨hmk, hmu⟩ := Nat.find_spec h
        by_cases h0 : Nat.find h = 0
        · obtain ⟨j, hj, hbj⟩ := hw 0 (by rw [hwit, if_pos h0]; simp)
          refine Or.inr (Or.inl ⟨j, hj, hbj, ?_⟩)
          rw [hcj j hj (by omega), hbj, ← h0]; exact hmu
        · rw [if_neg h0] at hwit
          obtain ⟨j, hj, hbj⟩ := hw (Nat.find h - 1) (by rw [hwit]; simp)
          obtain ⟨j', hj', hbj'⟩ := hw (Nat.find h) (by rw [hwit]; simp)
          have hmin := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
          have hle : g t (Nat.find h - 1) ≤ u := by
            by_contra hn; exact hmin ⟨by omega, by omega⟩
          have hne : g t (Nat.find h - 1) ≠ u := fun he =>
            hu (ht.mem_iff.mpr ⟨_, by omega, he⟩)
          refine Or.inr (Or.inr (Or.inr ⟨j, hj, j', hj', by omega, by omega, ?_, ?_⟩))
          · rw [hcj j hj (by omega), hbj]; omega
          · rw [hcj j' hj' (by omega), hbj']; exact hmu
      · have hwit : wit k t u = [k - 1] := by
          unfold wit; rw [if_neg hu, if_neg hk, dif_neg h]
        obtain ⟨j, hj, hbj⟩ := hw (k - 1) (by rw [hwit]; simp)
        have hle : g t (k - 1) ≤ u := by
          by_contra hn; exact h ⟨k - 1, by omega, by omega⟩
        have hne : g t (k - 1) ≠ u := fun he => hu (ht.mem_iff.mpr ⟨_, by omega, he⟩)
        refine Or.inr (Or.inr (Or.inl ⟨j, hj, by omega, ?_⟩))
        rw [hcj j hj (by omega), hbj]; omega
    simp [dec, hT, hF, hu]

/-- **Some block decides a few codes correctly.** -/
theorem dec_complete {D : ℕ} (us : List ℕ) (hD : 2 * us.length ≤ D) :
    ∃ b < (k + 1) ^ D, ∀ u ∈ us,
      dec k D (digits (k + 1) D b) (digits (N + 1) D (canon k N D t b)) u =
        some (decide (u ∈ t)) := by
  set w := us.flatMap (wit k t) with hw
  have hwl : w.length ≤ D := by
    have : w.length ≤ 2 * us.length := by
      rw [hw, List.length_flatMap]
      have := List.sum_le_card_nsmul (us.map fun u => (wit k t u).length) 2 (by
        intro a ha; obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha; exact length_wit u)
      simp at this; omega
    omega
  set bl := w ++ List.replicate (D - w.length) k with hbl
  have hbll : bl.length = D := by simp [hbl]; omega
  have hblt : ∀ d ∈ bl, d < k + 1 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨u, -, hu⟩ := List.mem_flatMap.mp hd
      have := wit_lt ht u d hu; omega
    · rw [List.mem_replicate] at hd; omega
  refine ⟨codeOf (k + 1) bl, by have := codeOf_lt bl hblt; rwa [hbll] at this, fun u hu => ?_⟩
  have hdig : digits (k + 1) D (codeOf (k + 1) bl) = bl := by
    have := digits_codeOf bl hblt; rwa [hbll] at this
  refine dec_of_wit ht (by rw [hdig]; exact hbll) (canon_consistent ht _) u fun i hi => ?_
  rw [hdig]
  have hib : i ∈ bl := List.mem_append_left _ (List.mem_flatMap.mpr ⟨u, hu, hi⟩)
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hib
  refine ⟨j, by rw [← hbll]; exact hj, ?_⟩
  unfold g; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hji

end Complete

/-! ### The increasing list of a finite set -/

/-- The increasing list of a finite set of codes below `N` is valid. -/
theorem valid_sort {N : ℕ} (T : Finset ℕ) (hT : ∀ c ∈ T, c < N) :
    Valid T.card N (T.sort (· ≤ ·)) := by
  have hlen : (T.sort (· ≤ ·)).length = T.card := Finset.length_sort _
  have hpw := List.pairwise_iff_getElem.mp (Finset.pairwise_sort T (· ≤ ·))
  have hnd := Finset.sort_nodup T (· ≤ ·)
  have hget : ∀ i (h : i < T.card), g (T.sort (· ≤ ·)) i = (T.sort (· ≤ ·))[i]'(by omega) := by
    intro i h; unfold g; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  refine ⟨hlen, fun i hi => ?_, fun i i' hii hi' => ?_⟩
  · rw [hget i hi]
    exact hT _ ((Finset.mem_sort _).mp (List.getElem_mem _))
  · rw [hget i (by omega), hget i' hi']
    have h1 := hpw i i' (by omega) (by omega) hii
    have h2 : (T.sort (· ≤ ·))[i]'(by omega) ≠ (T.sort (· ≤ ·))[i']'(by omega) := by
      intro he
      have := (List.Nodup.getElem_inj_iff hnd).mp he
      omega
    omega

theorem mem_sort_iff (T : Finset ℕ) (u : ℕ) : u ∈ T.sort (· ≤ ·) ↔ u ∈ T := Finset.mem_sort _

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
