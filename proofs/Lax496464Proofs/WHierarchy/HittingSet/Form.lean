import Lax496464Proofs.WHierarchy.HittingSet.Words

/-! # The word of an instance, number by number

The closed form of a Hitting Set word that the reading program is checked against: the codes of
`n`, `m` and `k`, then per set the code of its size and the codes of its members in increasing
order (`word_eq`). Next to it, the arrays the reader fills in: the members of all sets one after
the other (`memL`), the set each of them belongs to (`ownL`), and the offsets of the sets in
`memL` (`offs`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Form

open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464Proofs.WHierarchy.HittingSet.Words

/-! ## Generic facts about lists -/

theorem map_val_finRange (n : ℕ) : List.map Fin.val (List.finRange n) = List.range n := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem flatMap_finRange {α : Type} (m : ℕ) (g : Fin m → List α) :
    (List.finRange m).flatMap g =
      (List.range m).flatMap (fun j => if h : j < m then g ⟨j, h⟩ else []) := by
  rw [← map_val_finRange, List.flatMap_map]
  refine List.flatMap_congr fun j _ => ?_
  simp [j.isLt]

theorem range_split (m j : ℕ) (hj : j < m) :
    List.range m = List.range j ++ j :: List.range' (j + 1) (m - j - 1) := by
  rw [List.range_eq_range', List.range_eq_range']
  rw [show m = j + (m - j) by omega, ← List.range'_append]
  rw [show m - j = (m - j - 1) + 1 by omega, List.range'_succ]
  simp

/-- The sum of the lengths of the first `j` blocks. -/
def pre {α : Type} (g : ℕ → List α) (j : ℕ) : ℕ := ((List.range j).map fun i => (g i).length).sum

theorem pre_zero {α : Type} (g : ℕ → List α) : pre g 0 = 0 := by simp [pre]

theorem pre_succ {α : Type} (g : ℕ → List α) (j : ℕ) : pre g (j + 1) = pre g j + (g j).length := by
  simp [pre, List.range_succ]

theorem pre_mono {α : Type} (g : ℕ → List α) {i j : ℕ} (h : i ≤ j) : pre g i ≤ pre g j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · rw [pre_succ]; have := ih (by omega); omega
      · rw [show i = j + 1 by omega]

theorem length_flatMap_range {α : Type} (g : ℕ → List α) (m : ℕ) :
    ((List.range m).flatMap g).length = pre g m := by
  simp [pre, List.length_flatMap]

/-- The entry at position `q` of block `j` of a concatenation of blocks. -/
theorem getD_flatMap_range {α : Type} (g : ℕ → List α) {m j q : ℕ} (hj : j < m)
    (hq : q < (g j).length) (d : α) :
    ((List.range m).flatMap g).getD (pre g j + q) d = (g j).getD q d := by
  rw [range_split m j hj, List.flatMap_append, List.flatMap_cons]
  have hl : ((List.range j).flatMap g).length = pre g j := length_flatMap_range g j
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hq]

/-- Every position of a concatenation of blocks lies in one block. -/
theorem exists_block {α : Type} (g : ℕ → List α) {m p : ℕ}
    (hp : p < ((List.range m).flatMap g).length) :
    ∃ j < m, ∃ q < (g j).length, p = pre g j + q := by
  induction m with
  | zero => simp at hp
  | succ m ih =>
      rw [length_flatMap_range, pre_succ] at hp
      rcases Nat.lt_or_ge p (pre g m) with h | h
      · obtain ⟨j, hj, q, hq, rfl⟩ := ih (by rw [length_flatMap_range]; exact h)
        exact ⟨j, by omega, q, hq, rfl⟩
      · exact ⟨m, by omega, p - pre g m, by omega, by omega⟩

/-! ## The sets, as lists of numbers -/

/-- The members of set `j`, in increasing order, as numbers (empty for `j ≥ m`). -/
def mlist (P : Instance) (j : ℕ) : List ℕ :=
  if h : j < P.m then (P.members ⟨j, h⟩).map Fin.val else []

/-- The code of a set: its size, then its members. -/
def setBits (l : List ℕ) : List ℕ := bitsNat l.length ++ l.flatMap bitsNat

/-- The codes of the sets from `j` on. -/
def restSets (P : Instance) (j : ℕ) : List ℕ :=
  ((List.range P.m).drop j).flatMap fun i => setBits (mlist P i)

theorem mlist_of_lt (P : Instance) {j : ℕ} (h : j < P.m) :
    mlist P j = (P.members ⟨j, h⟩).map Fin.val := by
  simp [mlist, h]

/-- **The closed form of a Hitting Set word.** -/
theorem word_eq (P : Instance) (k : ℕ) :
    word P k = bitsNat P.n ++ bitsNat P.m ++ bitsNat k ++ restSets P 0 := by
  rw [word_eq_natBits]
  simp only [encodeInstance, natBits_append, natBits_flatMap, natBits_encodeNat,
    card_eq_length_members, bind_pure_comp, List.map_eq_map]
  rw [flatMap_finRange]
  simp only [restSets, List.drop_zero]
  congr 1
  refine List.flatMap_congr fun j hj => ?_
  have hj' := List.mem_range.mp hj
  rw [dif_pos hj', setBits, mlist_of_lt P hj', List.length_map]

theorem restSets_cons (P : Instance) {j : ℕ} (hj : j < P.m) :
    restSets P j = setBits (mlist P j) ++ restSets P (j + 1) := by
  unfold restSets
  rw [List.drop_eq_getElem_cons (by simpa using hj)]
  simp [List.flatMap_cons]

theorem restSets_m (P : Instance) : restSets P P.m = [] := by
  simp [restSets, List.drop_eq_nil_of_le]

/-- The members of a set are below `n`. -/
theorem mlist_lt (P : Instance) {j a : ℕ} (ha : a ∈ mlist P j) : a < P.n := by
  unfold mlist at ha
  split_ifs at ha with h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact i.isLt
  · simp at ha

/-- A set has at most `n` members. -/
theorem length_mlist_le (P : Instance) (j : ℕ) : (mlist P j).length ≤ P.n := by
  unfold mlist
  split_ifs with h
  · simp only [List.length_map, Instance.members]
    exact (List.length_filter_le _ _).trans (by simp)
  · simp

theorem mem_mlist_iff (P : Instance) {j : ℕ} (hj : j < P.m) (i : Fin P.n) :
    (i : ℕ) ∈ mlist P j ↔ i ∈ P.F ⟨j, hj⟩ := by
  rw [mlist_of_lt P hj]
  simp [Instance.members, Fin.val_inj]

/-- The members of a set are listed in strictly increasing order. -/
theorem mlist_sorted (P : Instance) (j : ℕ) : (mlist P j).Pairwise (· < ·) := by
  unfold mlist
  split_ifs with h
  · simp only [Instance.members]
    refine List.Pairwise.map _ (fun a b hab => hab) ?_
    exact (List.pairwise_lt_finRange P.n).filter _
  · simp

theorem mlist_nodup (P : Instance) (j : ℕ) : (mlist P j).Nodup :=
  (mlist_sorted P j).imp (fun h => Nat.ne_of_lt h)

/-! ## The arrays the reader fills in -/

/-- All members of all sets, set after set. -/
def memL (P : Instance) : List ℕ := (List.range P.m).flatMap (mlist P)

/-- For each entry of `memL`, the set it belongs to. -/
def ownL (P : Instance) : List ℕ :=
  (List.range P.m).flatMap fun j => List.replicate (mlist P j).length j

/-- The offset of set `j` in `memL`. -/
def offs (P : Instance) (j : ℕ) : ℕ := pre (mlist P) j

/-- The total number of members. -/
def total (P : Instance) : ℕ := offs P P.m

theorem offs_zero (P : Instance) : offs P 0 = 0 := pre_zero _

theorem offs_succ (P : Instance) (j : ℕ) : offs P (j + 1) = offs P j + (mlist P j).length :=
  pre_succ _ _

theorem offs_mono (P : Instance) {i j : ℕ} (h : i ≤ j) : offs P i ≤ offs P j := pre_mono _ h

theorem length_memL (P : Instance) : (memL P).length = total P := length_flatMap_range _ _

theorem pre_replicate (P : Instance) :
    pre (fun j => List.replicate (mlist P j).length j) = offs P := by
  funext j; simp [pre, offs]

theorem length_ownL (P : Instance) : (ownL P).length = total P := by
  unfold ownL; rw [length_flatMap_range, pre_replicate]; rfl

theorem memL_getD (P : Instance) {j q : ℕ} (hj : j < P.m) (hq : q < (mlist P j).length) :
    (memL P).getD (offs P j + q) 0 = (mlist P j).getD q 0 :=
  getD_flatMap_range (mlist P) hj hq 0

theorem ownL_getD (P : Instance) {j q : ℕ} (hj : j < P.m) (hq : q < (mlist P j).length) :
    (ownL P).getD (offs P j + q) 0 = j := by
  have := getD_flatMap_range (fun j => List.replicate (mlist P j).length j) hj
    (by simpa using hq) 0
  rw [pre_replicate] at this
  unfold ownL
  rw [this]
  simp [List.getD_eq_getElem?_getD, hq]

/-- Every position of `memL` is in some set. -/
theorem exists_pos (P : Instance) {p : ℕ} (hp : p < total P) :
    ∃ j < P.m, ∃ q < (mlist P j).length, p = offs P j + q :=
  exists_block (mlist P) (by rw [← length_memL] at hp; exact hp)

/-- The position `offs j + q` of `memL`: its entry, its owner, and where it is. -/
theorem pos_facts (P : Instance) {j q : ℕ} (hj : j < P.m) (hq : q < (mlist P j).length) :
    offs P j + q < total P ∧ (memL P).getD (offs P j + q) 0 = (mlist P j).getD q 0 ∧
      (ownL P).getD (offs P j + q) 0 = j := by
  refine ⟨?_, memL_getD P hj hq, ownL_getD P hj hq⟩
  have h1 := offs_succ P j
  have h2 := offs_mono P (show j + 1 ≤ P.m by omega)
  unfold total; omega

theorem ownL_lt (P : Instance) {p : ℕ} (hp : p < total P) : (ownL P).getD p 0 < P.m := by
  obtain ⟨j, hj, q, hq, rfl⟩ := exists_pos P hp
  rw [ownL_getD P hj hq]; exact hj

theorem memL_lt (P : Instance) {p : ℕ} (hp : p < total P) : (memL P).getD p 0 < P.n := by
  obtain ⟨j, hj, q, hq, rfl⟩ := exists_pos P hp
  rw [memL_getD P hj hq]
  exact mlist_lt P (by rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq)

/-- The owner of a position locates it between two offsets. -/
theorem offs_le_of_own (P : Instance) {p : ℕ} (hp : p < total P) :
    offs P ((ownL P).getD p 0) ≤ p ∧ p < offs P ((ownL P).getD p 0 + 1) := by
  obtain ⟨j, hj, q, hq, rfl⟩ := exists_pos P hp
  rw [ownL_getD P hj hq, offs_succ]
  omega

/-- A position is owned by `j` exactly when it lies between the offsets of `j`. -/
theorem own_eq_iff (P : Instance) {p j : ℕ} (hp : p < total P) (hj : j < P.m) :
    (ownL P).getD p 0 = j ↔ offs P j ≤ p ∧ p < offs P (j + 1) := by
  constructor
  · rintro rfl; exact offs_le_of_own P hp
  · rintro ⟨h1, h2⟩
    obtain ⟨j', hj', q, hq, rfl⟩ := exists_pos P hp
    rw [ownL_getD P hj' hq]
    have e1 := offs_succ P j'
    rcases Nat.lt_trichotomy j j' with h | h | h
    · have := offs_mono P (show j + 1 ≤ j' by omega); omega
    · exact h.symm
    · have := offs_mono P (show j' + 1 ≤ j by omega); omega

/-- The entry of a position is a member of its owner. -/
theorem memL_mem (P : Instance) {p : ℕ} (hp : p < total P) :
    (memL P).getD p 0 ∈ mlist P ((ownL P).getD p 0) := by
  obtain ⟨j, hj, q, hq, rfl⟩ := exists_pos P hp
  rw [memL_getD P hj hq, ownL_getD P hj hq, List.getD_eq_getElem _ _ hq]
  exact List.getElem_mem hq

/-- Every member of a set occurs at a position owned by that set. -/
theorem exists_pos_of_mem (P : Instance) {j a : ℕ} (hj : j < P.m) (ha : a ∈ mlist P j) :
    ∃ p < total P, (memL P).getD p 0 = a ∧ (ownL P).getD p 0 = j := by
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨h1, h2, h3⟩ := pos_facts P hj hq
  exact ⟨_, h1, by rw [h2, List.getD_eq_getElem _ _ hq], h3⟩

/-- Two positions of the same set with the same entry are the same position. -/
theorem pos_inj (P : Instance) {p p' : ℕ} (hp : p < total P) (hp' : p' < total P)
    (ho : (ownL P).getD p 0 = (ownL P).getD p' 0) (hm : (memL P).getD p 0 = (memL P).getD p' 0) :
    p = p' := by
  obtain ⟨j, hj, q, hq, rfl⟩ := exists_pos P hp
  obtain ⟨j', hj', q', hq', rfl⟩ := exists_pos P hp'
  rw [ownL_getD P hj hq, ownL_getD P hj' hq'] at ho
  subst ho
  rw [memL_getD P hj hq, memL_getD P hj hq', List.getD_eq_getElem _ _ hq,
    List.getD_eq_getElem _ _ hq'] at hm
  have := (List.Nodup.getElem_inj_iff (mlist_nodup P j)).mp hm
  omega

/-! ## Sizes -/

theorem sum_le_sum_of_succ {g h : ℕ → ℕ} (hgh : ∀ i, g i + 1 ≤ h i) (m : ℕ) :
    m + ((List.range m).map g).sum ≤ ((List.range m).map h).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      have := hgh m
      omega

theorem length_flatMap_bitsNat (l : List ℕ) : l.length ≤ (l.flatMap bitsNat).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, length_bitsNat,
      List.length_cons]; omega

theorem length_setBits (l : List ℕ) : l.length + 1 ≤ (setBits l).length := by
  unfold setBits
  rw [List.length_append, length_bitsNat]
  have := length_flatMap_bitsNat l
  omega

/-- The sets take at least one entry each, and one more per member. -/
theorem sets_len (P : Instance) : P.m + total P ≤ (restSets P 0).length := by
  unfold restSets total offs pre
  rw [List.drop_zero, List.length_flatMap]
  exact sum_le_sum_of_succ (fun i => length_setBits (mlist P i)) P.m

theorem length_word (P : Instance) (k : ℕ) :
    (word P k).length = (2 * P.n.size + 1) + (2 * P.m.size + 1) + (2 * k.size + 1) +
      (restSets P 0).length := by
  rw [word_eq]; simp; omega

/-- The dimensions of an instance are bounded by the length of its word. -/
theorem dims_le (P : Instance) (k : ℕ) :
    P.m + total P + 2 * (P.n.size + P.m.size + k.size) + 3 ≤ (word P k).length := by
  have := sets_len P
  rw [length_word]; omega

end Lax496464Proofs.WHierarchy.HittingSet.Form
