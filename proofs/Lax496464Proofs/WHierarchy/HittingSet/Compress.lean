import Lax496464Proofs.WHierarchy.HittingSet.Form

/-! # Compressing a Hitting Set instance

The universe of a Hitting Set instance is written in binary, so it can be exponentially larger than
the word; and so can `k`. A reduction that writes one vertex per element has to shrink the universe
first. The compressed instance keeps the sets and renames each element that occurs in a set by the
position of its first occurrence in `memL` (`fst`); its universe is `{0, …, T + k' - 1}` for `T` the
number of members and `k' = min k m`, so that it has room for `k'` elements, and its solution size is
`k'`. When `k ≤ n` the answer does not change (`hasHittingSet_compress`): a hitting set can be taken
of size at most `k`, then of size at most `m` (one element per set), and then moved to the first
occurrences. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Compress

open Lax496464.HittingSet Lax496464Proofs.WHierarchy.HittingSet.Form

/-! ## The first occurrence of an entry -/

/-- The first position of `memL` holding the same entry as position `p`. -/
def fst (P : Instance) (p : ℕ) : ℕ := (memL P).idxOf ((memL P).getD p 0)

/-- The first position holding `a` is characterized as the least one. -/
theorem idxOf_eq_of_least : ∀ (l : List ℕ) (a r : ℕ), r < l.length → l.getD r 0 = a →
    (∀ q < r, l.getD q 0 ≠ a) → l.idxOf a = r
  | [], _, _, h, _, _ => by simp at h
  | x :: xs, a, 0, _, ha, _ => by
      simp only [List.getD_cons_zero] at ha
      subst ha; simp
  | x :: xs, a, r + 1, hr, ha, hmin => by
      have hx : x ≠ a := by simpa using hmin 0 (by omega)
      rw [List.idxOf_cons]
      have : (x == a) = false := by simpa using hx
      rw [this, cond_false, idxOf_eq_of_least xs a r (by simpa using hr) (by simpa using ha)
        (fun q hq => by simpa using hmin (q + 1) (by omega))]

theorem getD_idxOf {l : List ℕ} {a : ℕ} (h : a ∈ l) : l.getD (l.idxOf a) 0 = a := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem h), List.getElem_idxOf]

theorem getD_mem {l : List ℕ} {p : ℕ} (hp : p < l.length) : l.getD p 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp

theorem mem_memL_getD {P : Instance} {p : ℕ} (hp : p < total P) : (memL P).getD p 0 ∈ memL P :=
  getD_mem (by rw [length_memL]; exact hp)

theorem fst_lt {P : Instance} {p : ℕ} (hp : p < total P) : fst P p < total P := by
  have := List.idxOf_lt_length_of_mem (mem_memL_getD hp)
  rwa [length_memL] at this

theorem getD_fst {P : Instance} {p : ℕ} (hp : p < total P) :
    (memL P).getD (fst P p) 0 = (memL P).getD p 0 :=
  getD_idxOf (mem_memL_getD hp)

/-- Two positions of the same set with the same first occurrence are the same position. -/
theorem fst_inj {P : Instance} {p p' : ℕ} (hp : p < total P) (hp' : p' < total P)
    (ho : (ownL P).getD p 0 = (ownL P).getD p' 0) (hf : fst P p = fst P p') : p = p' := by
  refine pos_inj P hp hp' ho ?_
  rw [← getD_fst hp, ← getD_fst hp', hf]

/-! ## The compressed instance -/

/-- The solution size of the compressed instance. -/
def kk (P : Instance) (k : ℕ) : ℕ := min k P.m

/-- The universe size of the compressed instance. -/
def NN (P : Instance) (k : ℕ) : ℕ := total P + kk P k

/-- The element `a` lies in set `j` of the compressed instance. -/
def InF (P : Instance) (a j : ℕ) : Prop := ∃ p < total P, fst P p = a ∧ (ownL P).getD p 0 = j

open Classical in
/-- **The compressed instance.** -/
noncomputable def compress (P : Instance) (k : ℕ) : Instance where
  n := NN P k
  m := P.m
  F j := Finset.univ.filter fun a : Fin (NN P k) => InF P a j

theorem mem_compress_F {P : Instance} {k : ℕ} (j : Fin (compress P k).m)
    (a : Fin (compress P k).n) :
    a ∈ (compress P k).F j ↔ InF P a j := by
  classical
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

theorem mem_memL_of_mem_mlist {P : Instance} {j e : ℕ} (hj : j < P.m) (he : e ∈ mlist P j) :
    e ∈ memL P := by
  unfold memL
  exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, he⟩

/-- Membership in a compressed set, by the original members. -/
theorem inF_iff {P : Instance} {a j : ℕ} (hj : j < P.m) :
    InF P a j ↔ ∃ e ∈ mlist P j, (memL P).idxOf e = a := by
  constructor
  · rintro ⟨p, hp, rfl, rfl⟩
    exact ⟨_, memL_mem P hp, rfl⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨p, hp, hpe, hpo⟩ := exists_pos_of_mem P hj he
    exact ⟨p, hp, by rw [fst, hpe], hpo⟩

theorem inF_lt {P : Instance} {a j : ℕ} (h : InF P a j) : a < total P := by
  obtain ⟨p, hp, rfl, -⟩ := h
  exact fst_lt hp

theorem kk_le_NN (P : Instance) (k : ℕ) : kk P k ≤ NN P k := by unfold NN; omega

/-! ## The answer is unchanged -/

/-- With `k` at most the size of the universe, a hitting set of size exactly `k` exists as soon as
one of size at most `k` does. -/
theorem hasHittingSet_iff_le (Q : Instance) {k : ℕ} (hk : k ≤ Q.n) :
    Q.HasHittingSet k ↔ ∃ H : Finset (Fin Q.n), H.card ≤ k ∧ ∀ j, ∃ i ∈ H, i ∈ Q.F j := by
  constructor
  · rintro ⟨H, hc, hh⟩; exact ⟨H, hc.le, hh⟩
  · rintro ⟨H, hc, hh⟩
    obtain ⟨H', hHH', hc'⟩ := Finset.exists_superset_card_eq hc (by simpa using hk)
    exact ⟨H', hc', fun j => by obtain ⟨i, hi, hij⟩ := hh j; exact ⟨i, hHH' hi, hij⟩⟩

/-- A hitting set can be shrunk to one element per set. -/
theorem shrink (Q : Instance) {H : Finset (Fin Q.n)} (hh : ∀ j, ∃ i ∈ H, i ∈ Q.F j) :
    ∃ H' : Finset (Fin Q.n), H' ⊆ H ∧ H'.card ≤ Q.m ∧ ∀ j, ∃ i ∈ H', i ∈ Q.F j := by
  choose f hf using hh
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact (hf j).1
  · exact Finset.card_image_le.trans (by simp)
  · intro j
    exact ⟨f j, Finset.mem_image_of_mem _ (Finset.mem_univ _), (hf j).2⟩

/-- From the original instance to the compressed one. -/
theorem to_compress (P : Instance) (k : ℕ) {c : ℕ} {H : Finset (Fin P.n)} (hc : H.card ≤ c)
    (hh : ∀ j, ∃ i ∈ H, i ∈ P.F j) :
    ∃ H'' : Finset (Fin (compress P k).n), H''.card ≤ c ∧ ∀ j, ∃ a ∈ H'', a ∈ (compress P k).F j := by
  classical
  refine ⟨Finset.univ.filter fun a : Fin (NN P k) => ∃ i ∈ H, (memL P).idxOf i.val = a.val,
    ?_, ?_⟩
  · refine le_trans ?_ hc
    calc (Finset.univ.filter fun a : Fin (NN P k) => ∃ i ∈ H, (memL P).idxOf i.val = a.val).card
        = ((Finset.univ.filter fun a : Fin (NN P k) => ∃ i ∈ H, (memL P).idxOf i.val = a.val).map
            Fin.valEmbedding).card := (Finset.card_map _).symm
      _ ≤ (H.image fun i => (memL P).idxOf i.val).card := by
          refine Finset.card_le_card fun v hv => ?_
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
          obtain ⟨i, hi, hia⟩ := (Finset.mem_filter.mp ha).2
          exact Finset.mem_image.mpr ⟨i, hi, hia⟩
      _ ≤ H.card := Finset.card_image_le
  · intro j
    obtain ⟨i, hi, hij⟩ := hh j
    have he : (i : ℕ) ∈ mlist P j := (mem_mlist_iff P j.isLt i).mpr hij
    have hin : InF P ((memL P).idxOf i.val) j := (inF_iff (P := P) j.isLt).mpr ⟨_, he, rfl⟩
    have hlt : (memL P).idxOf i.val < NN P k := by
      have := inF_lt hin; unfold NN; omega
    refine ⟨⟨_, hlt⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, rfl⟩
    · exact (mem_compress_F (P := P) (k := k) j _).mpr hin

/-- From the compressed instance back to the original one. -/
theorem of_compress (P : Instance) (k : ℕ) {c : ℕ} {H : Finset (Fin (compress P k).n)}
    (hc : H.card ≤ c) (hh : ∀ j, ∃ a ∈ H, a ∈ (compress P k).F j) :
    ∃ H' : Finset (Fin P.n), H'.card ≤ c ∧ ∀ j, ∃ i ∈ H', i ∈ P.F j := by
  classical
  refine ⟨Finset.univ.filter fun i : Fin P.n => ∃ a ∈ H, (memL P).getD a.val 0 = i.val, ?_, ?_⟩
  · refine le_trans ?_ hc
    calc (Finset.univ.filter fun i : Fin P.n => ∃ a ∈ H, (memL P).getD a.val 0 = i.val).card
        = ((Finset.univ.filter fun i : Fin P.n => ∃ a ∈ H, (memL P).getD a.val 0 = i.val).map
            Fin.valEmbedding).card := (Finset.card_map _).symm
      _ ≤ (H.image fun a => (memL P).getD a.val 0).card := by
          refine Finset.card_le_card fun v hv => ?_
          obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
          obtain ⟨a, ha, hai⟩ := (Finset.mem_filter.mp hi).2
          exact Finset.mem_image.mpr ⟨a, ha, hai⟩
      _ ≤ H.card := Finset.card_image_le
  · intro j
    obtain ⟨a, ha, haj⟩ := hh j
    have hin : InF P a j := (mem_compress_F (P := P) (k := k) j a).mp haj
    obtain ⟨e, he, hea⟩ := (inF_iff (P := P) j.isLt).mp hin
    have hen : e < P.n := mlist_lt P he
    refine ⟨⟨e, hen⟩, ?_, (mem_mlist_iff P j.isLt ⟨e, hen⟩).mp he⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, ?_⟩
    rw [← hea]
    exact getD_idxOf (mem_memL_of_mem_mlist j.isLt he)

/-- **Compression keeps the answer**, when `k` is at most the size of the universe. -/
theorem hasHittingSet_compress (P : Instance) {k : ℕ} (hk : k ≤ P.n) :
    P.HasHittingSet k ↔ (compress P k).HasHittingSet (kk P k) := by
  rw [hasHittingSet_iff_le P hk, hasHittingSet_iff_le (compress P k) (kk_le_NN P k)]
  constructor
  · rintro ⟨H, hc, hh⟩
    obtain ⟨H', hH', hc', hh'⟩ := shrink P hh
    exact to_compress P k (c := kk P k)
      (le_min ((Finset.card_le_card hH').trans hc) hc') hh'
  · rintro ⟨H, hc, hh⟩
    obtain ⟨H', hc', hh'⟩ := of_compress P k hc hh
    exact ⟨H', hc'.trans (min_le_left _ _), hh'⟩

end Lax496464Proofs.WHierarchy.HittingSet.Compress
