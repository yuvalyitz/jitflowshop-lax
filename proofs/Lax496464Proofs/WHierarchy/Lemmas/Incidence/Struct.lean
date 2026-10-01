import Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! # The incidence structure, built from the listing of the tuples

`IncData` is what the program reads off the word of a structure `A`: the number `s` of symbols, the
size `N` of the universe, the arities `ar`, the number `cnt i` of tuples of symbol `i` and entry `l`
of tuple `j` of symbol `i`, `ent i j l`, in the order in which the word lists them; and `r`, the
number of binary symbols wanted. The tuples are numbered globally in that order, tuple `j` of symbol
`i` getting `po i + j`, and becomes the new element `N + po i + j`.

The incidence structure (`toStructure`) has universe `N + T` (`T` the number of tuples) and the
symbols
* `P_i = i` for `i < s`, unary: the new elements of the tuples of symbol `i`;
* `E_l = s + l` for `l < r`, binary: `(a, b)` when `a` is entry `l` of the tuple of `b`.

Its word (`word`) lists the tuples in this order, which is the order the program writes them in. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct

open Lax496464.WH_B1_Structures Lax496464Proofs.WHierarchy.Logic.StructureCode

/-- The data the incidence structure is built from. -/
structure IncData where
  s : ℕ
  N : ℕ
  r : ℕ
  ar : ℕ → ℕ
  cnt : ℕ → ℕ
  ent : ℕ → ℕ → ℕ → ℕ

namespace IncData

variable (D : IncData)

/-- The number of tuples of the symbols below `i`. -/
def po (i : ℕ) : ℕ := ((List.range i).map D.cnt).sum

/-- The number of tuples. -/
def T : ℕ := D.po D.s

/-- The size of the incidence structure. -/
def size : ℕ := D.N + D.T

/-- The tuples of `P_i`. -/
def pList (i : ℕ) : List (List ℕ) := (List.range (D.cnt i)).map fun j => [D.N + D.po i + j]

/-- The tuples of `E_l` coming from symbol `i`. -/
def eRow (l i : ℕ) : List (List ℕ) :=
  if l < D.ar i then (List.range (D.cnt i)).map fun j => [D.ent i j l, D.N + D.po i + j] else []

/-- The tuples of `E_l`. -/
def eList (l : ℕ) : List (List ℕ) := (List.range D.s).flatMap (D.eRow l)

/-- The tuples of symbol `k` of the incidence structure, in the order they are written. -/
def relList (k : ℕ) : List (List ℕ) :=
  if k < D.s then D.pList k else if k < D.s + D.r then D.eList (k - D.s) else []

/-- The new vocabulary: `s` unary symbols, then `r` binary ones. -/
def arities : List ℕ := List.replicate D.s 1 ++ List.replicate D.r 2

/-- A tuple with entries in the new universe. -/
def good (t : List ℕ) : Bool := t.all fun a => decide (a < D.size)

/-- The tuples of symbol `i`, as the data list them. -/
def listOf (i : ℕ) : List (List ℕ) :=
  (List.range (D.cnt i)).map fun j => (List.range (D.ar i)).map (D.ent i j)

/-- The listed entries are in the old universe. -/
def Valid : Prop := ∀ i < D.s, ∀ j < D.cnt i, ∀ l < D.ar i, D.ent i j l < D.N

theorem length_arities : D.arities.length = D.s + D.r := by simp [arities]

theorem arities_getD (k : ℕ) :
    D.arities.getD k 0 = if k < D.s then 1 else if k < D.s + D.r then 2 else 0 := by
  unfold arities
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : k < D.s
  · rw [List.getElem?_append_left (by simpa using h1)]; simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    by_cases h2 : k < D.s + D.r
    · simp only [h1, h2, List.getElem?_replicate, List.length_replicate, if_false, if_true]
      rw [if_pos (by omega)]; rfl
    · simp only [h1, h2, List.getElem?_replicate, List.length_replicate, if_false]
      rw [if_neg (by omega)]; rfl

theorem mem_eRow {l i : ℕ} {t : List ℕ} :
    t ∈ D.eRow l i ↔ l < D.ar i ∧ ∃ j < D.cnt i, t = [D.ent i j l, D.N + D.po i + j] := by
  unfold eRow
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem mem_eList {l : ℕ} {t : List ℕ} :
    t ∈ D.eList l ↔ ∃ i < D.s, l < D.ar i ∧ ∃ j < D.cnt i, t = [D.ent i j l, D.N + D.po i + j] := by
  simp [eList, mem_eRow]

theorem mem_pList {i : ℕ} {t : List ℕ} :
    t ∈ D.pList i ↔ ∃ j < D.cnt i, t = [D.N + D.po i + j] := by
  simp [pList, eq_comm]

theorem length_of_mem_relList {k : ℕ} {t : List ℕ} (h : t ∈ D.relList k) :
    k < D.s + D.r ∧ t.length = D.arities.getD k 0 := by
  rw [arities_getD]
  unfold relList at h
  by_cases h1 : k < D.s
  · rw [if_pos h1] at h
    obtain ⟨j, -, rfl⟩ := (D.mem_pList).mp h
    simp [h1]; omega
  · rw [if_neg h1] at h
    by_cases h2 : k < D.s + D.r
    · rw [if_pos h2] at h
      obtain ⟨i, -, -, j, -, rfl⟩ := (D.mem_eList).mp h
      simp [h1, h2]
    · rw [if_neg h2] at h; simp at h

/-- **The incidence structure.** -/
def toStructure : Structure where
  arities := D.arities
  size := D.size
  rel k := ((D.relList k).filter D.good).toFinset
  arity_pos := by
    intro a ha
    simp only [arities, List.mem_append, List.mem_replicate] at ha
    omega
  wf k t ht := by
    simp only [List.mem_toFinset, List.mem_filter] at ht
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨hk, hl⟩ := D.length_of_mem_relList h1
    refine ⟨by rw [length_arities]; exact hk, hl, fun a ha => ?_⟩
    simp only [good, List.all_eq_true, decide_eq_true_eq] at h2
    exact h2 a ha

@[simp] theorem toStructure_arities : D.toStructure.arities = D.arities := rfl
@[simp] theorem toStructure_size : D.toStructure.size = D.size := rfl

theorem mem_rel {k : ℕ} {t : List ℕ} :
    t ∈ D.toStructure.rel k ↔ t ∈ D.relList k ∧ D.good t = true := by
  simp [toStructure]

/-! ### The global numbering of the tuples -/

theorem po_succ (i : ℕ) : D.po (i + 1) = D.po i + D.cnt i := by
  simp [po, List.range_succ]

theorem po_zero : D.po 0 = 0 := rfl

theorem po_mono {i i' : ℕ} (h : i ≤ i') : D.po i ≤ D.po i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [po_succ]; omega

theorem po_add_lt {i i' j : ℕ} (hj : j < D.cnt i) (h : i < i') : D.po i + j < D.po i' := by
  have := D.po_mono (show i + 1 ≤ i' by omega)
  rw [po_succ] at this; omega

theorem po_add_lt_T {i j : ℕ} (hi : i < D.s) (hj : j < D.cnt i) : D.po i + j < D.T :=
  D.po_add_lt hj hi

/-- **The global number of a tuple determines the tuple.** -/
theorem po_inj {i i' j j' : ℕ} (hj : j < D.cnt i) (hj' : j' < D.cnt i')
    (h : D.po i + j = D.po i' + j') : i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hlt | rfl | hgt
  · have := D.po_add_lt hj hlt; omega
  · exact ⟨rfl, by omega⟩
  · have := D.po_add_lt hj' hgt; omega

theorem good_of_mem {k : ℕ} {t : List ℕ} (hv : D.Valid) (h : t ∈ D.relList k) : D.good t = true := by
  simp only [good, List.all_eq_true, decide_eq_true_eq]
  intro a ha
  unfold relList at h
  unfold size
  split_ifs at h with h1 h2
  · obtain ⟨j, hj, rfl⟩ := (D.mem_pList).mp h
    simp only [List.mem_singleton] at ha
    have := D.po_add_lt_T h1 hj; omega
  · obtain ⟨i, hi, hl, j, hj, rfl⟩ := (D.mem_eList).mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have := D.po_add_lt_T hi hj
    have := hv i hi j hj _ hl
    omega
  · simp at h

/-- The unary symbols: `[b] ∈ P_i` exactly for the new elements of the tuples of `i`. -/
theorem mem_rel_P (hv : D.Valid) {k : ℕ} (hk : k < D.s) {t : List ℕ} :
    t ∈ D.toStructure.rel k ↔ ∃ j < D.cnt k, t = [D.N + D.po k + j] := by
  rw [mem_rel]
  constructor
  · rintro ⟨h, -⟩; unfold relList at h; rw [if_pos hk] at h; exact (D.mem_pList).mp h
  · intro h
    have h' : t ∈ D.relList k := by unfold relList; rw [if_pos hk]; exact (D.mem_pList).mpr h
    exact ⟨h', D.good_of_mem hv h'⟩

/-- The binary symbols: `[a, b] ∈ E_l` exactly when `a` is entry `l` of the tuple of `b`. -/
theorem mem_rel_E (hv : D.Valid) (l : ℕ) {t : List ℕ} :
    t ∈ D.toStructure.rel (D.s + l) ↔
      l < D.r ∧ ∃ i < D.s, l < D.ar i ∧ ∃ j < D.cnt i, t = [D.ent i j l, D.N + D.po i + j] := by
  rw [mem_rel]
  unfold relList
  rw [if_neg (by omega)]
  by_cases hl : D.s + l < D.s + D.r
  · rw [if_pos hl, show D.s + l - D.s = l by omega]
    constructor
    · rintro ⟨h, -⟩; exact ⟨by omega, (D.mem_eList).mp h⟩
    · rintro ⟨-, h⟩
      have h' : t ∈ D.relList (D.s + l) := by
        unfold relList; rw [if_neg (by omega), if_pos hl, show D.s + l - D.s = l by omega]
        exact (D.mem_eList).mpr h
      exact ⟨(D.mem_eList).mpr h, D.good_of_mem hv h'⟩
  · rw [if_neg hl]; simp; omega

/-! ### The word -/

theorem nodup_pList (i : ℕ) : (D.pList i).Nodup := by
  refine (List.nodup_range).map ?_
  intro j j' h
  simp only [List.cons.injEq, and_true] at h
  omega

theorem nodup_eList (l : ℕ) : (D.eList l).Nodup := by
  unfold eList
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ?_, (List.pairwise_lt_range).imp fun {i i'} hlt => ?_⟩
  · unfold eRow
    split_ifs
    · refine (List.nodup_range).map ?_
      intro j j' h
      simp only [List.cons.injEq, and_true] at h
      omega
    · exact List.nodup_nil
  · intro t ht ht'
    obtain ⟨-, j, hj, rfl⟩ := (D.mem_eRow).mp ht
    obtain ⟨-, j', hj', h⟩ := (D.mem_eRow).mp ht'
    simp only [List.cons.injEq, and_true] at h
    have := D.po_add_lt hj hlt
    omega

theorem nodup_relList (k : ℕ) : (D.relList k).Nodup := by
  unfold relList
  split_ifs
  · exact D.nodup_pList k
  · exact D.nodup_eList _
  · exact List.nodup_nil

/-- The word of the incidence structure. -/
def word : List ℕ := wordOf D.arities D.size ((List.range (D.s + D.r)).map D.relList)

/-- **The word encodes the incidence structure.** -/
theorem encodes_word (hv : D.Valid) : Encodes D.word D.toStructure := by
  refine encodes_wordOf D.toStructure _ (by simp [length_arities]) fun k hk => ?_
  simp only [toStructure_arities, length_arities] at hk
  have hg : (List.map D.relList (List.range (D.s + D.r))).getD k [] = D.relList k := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [hg]
  refine ⟨D.nodup_relList k, ?_⟩
  ext t
  simp only [List.mem_toFinset, mem_rel]
  exact ⟨fun h => ⟨h, D.good_of_mem hv h⟩, fun h => h.1⟩

/-- The number of tuples of `E_l`. -/
def eCount (l : ℕ) : ℕ := ((List.range D.s).map fun i => if l < D.ar i then D.cnt i else 0).sum

theorem length_eList (l : ℕ) : (D.eList l).length = D.eCount l := by
  unfold eList eCount
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  unfold eRow
  split_ifs <;> simp

theorem flatMap_singleton_eq_map (l : List ℕ) (f : ℕ → ℕ) :
    (l.flatMap fun j => [f j]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem flatten_flatMap' {α : Type} (l : List ℕ) (g : ℕ → List (List α)) :
    (l.flatMap g).flatten = l.flatMap fun i => (g i).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The entries of the block of `P_i`. -/
def pFlat (i : ℕ) : List ℕ := (List.range (D.cnt i)).map fun j => D.N + D.po i + j

/-- The entries of the block of `E_l` from symbol `i`. -/
def eFlat (l i : ℕ) : List ℕ :=
  if l < D.ar i then (List.range (D.cnt i)).flatMap fun j => [D.ent i j l, D.N + D.po i + j]
  else []

theorem blockOf_pList (i : ℕ) : blockOf (D.pList i) = D.cnt i :: D.pFlat i := by
  simp [blockOf, pList, pFlat, List.flatten_eq_flatMap, List.flatMap_map,
    flatMap_singleton_eq_map]

theorem blockOf_eList (l : ℕ) :
    blockOf (D.eList l) = D.eCount l :: (List.range D.s).flatMap (D.eFlat l) := by
  rw [blockOf, length_eList]
  congr 1
  unfold eList eFlat eRow
  rw [flatten_flatMap']
  refine List.flatMap_congr fun i _ => ?_
  split_ifs
  · simp [List.flatten_eq_flatMap, List.flatMap_map]
  · rfl

/-- **The word, as the program writes it.** -/
theorem word_eq :
    D.word = [D.s + D.r] ++ List.replicate D.s 1 ++ List.replicate D.r 2 ++ [D.size] ++
      (List.range D.s).flatMap (fun i => D.cnt i :: D.pFlat i) ++
      (List.range D.r).flatMap (fun l => D.eCount l :: (List.range D.s).flatMap (D.eFlat l)) := by
  unfold word wordOf
  rw [length_arities, List.range_add, List.map_append, List.map_append, List.flatten_append]
  have h1 : ((List.range D.s).map D.relList).map blockOf =
      (List.range D.s).map fun i => D.cnt i :: D.pFlat i := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, relList, if_pos (List.mem_range.mp hi), blockOf_pList]
  have h2 : ((List.map (fun l => D.s + l) (List.range D.r)).map D.relList).map blockOf =
      (List.range D.r).map fun l => D.eCount l :: (List.range D.s).flatMap (D.eFlat l) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, relList, if_neg (show ¬ D.s + l < D.s by omega),
      if_pos (show D.s + l < D.s + D.r by omega), show D.s + l - D.s = l by omega, blockOf_eList]
  rw [h1, h2]
  simp [arities, List.flatten_eq_flatMap, List.flatMap_map]

end IncData

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
