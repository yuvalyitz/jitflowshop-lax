import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars
import Lax496464Proofs.WHierarchy.Logic.StructureCode
import Mathlib.Data.List.Lex
import Mathlib.Tactic.IntervalCases

/-! # Negation elimination: the expanded structure

The expanded structure has the old universe `{0, …, N-1}` and the symbols of `Syntax`: the order
`<` (all pairs `[a, b]` with `a < b < N`), and per old symbol `i` with tuples `L i` (as the input word
lists them) the relation itself, its lexicographically first tuple `minL`, its last tuple `maxL`,
the pairs `u ++ v` of lexicographically consecutive tuples (`sList`, `v = succOf u`), and `Z_i`, the
whole universe if `L i` is empty. Tuples are compared by Mathlib's lexicographic order on `List ℕ`.

The lists are defined by the scans the program does: `minL` keeps the first tuple and replaces it by
every smaller one, `succOf u` scans for the smallest tuple above `u`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.StructureCode
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars

/-! ### First, last and consecutive tuples -/

/-- One step of the scan for the first tuple. -/
def minStep (m t : List ℕ) : List ℕ := if t < m then t else m

/-- One step of the scan for the last tuple. -/
def maxStep (m t : List ℕ) : List ℕ := if m < t then t else m

/-- The lexicographically first tuple. -/
def minL (L : List (List ℕ)) : List ℕ := L.foldl minStep (L.headD [])

/-- The lexicographically last tuple. -/
def maxL (L : List (List ℕ)) : List ℕ := L.foldl maxStep (L.headD [])

/-- One step of the scan for the successor of `u`. -/
def succStep (u : List ℕ) (acc : Option (List ℕ)) (w : List ℕ) : Option (List ℕ) :=
  if u < w then
    match acc with
    | none => some w
    | some v => some (if w < v then w else v)
  else acc

/-- The successor of `u`: the smallest tuple above `u`, if any. -/
def succOf (L : List (List ℕ)) (u : List ℕ) : Option (List ℕ) := L.foldl (succStep u) none

theorem foldl_minStep : ∀ (L : List (List ℕ)) (m : List ℕ),
    (L.foldl minStep m = m ∨ L.foldl minStep m ∈ L) ∧ L.foldl minStep m ≤ m ∧
      ∀ t ∈ L, L.foldl minStep m ≤ t
  | [], m => by simp
  | t :: L, m => by
    obtain ⟨h1, h2, h3⟩ := foldl_minStep L (minStep m t)
    simp only [List.foldl_cons]
    unfold minStep at h1 h2 h3 ⊢
    split_ifs at h1 h2 h3 ⊢ with h
    · refine ⟨?_, le_trans h2 (le_of_lt h), ?_⟩
      · rcases h1 with h1 | h1
        · right; rw [h1]; simp
        · right; simp [h1]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h2
        · exact h3 w hw
    · refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1
        · left; exact h1
        · right; simp [h1]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact le_trans h2 (not_lt.mp h)
        · exact h3 w hw

theorem foldl_maxStep : ∀ (L : List (List ℕ)) (m : List ℕ),
    (L.foldl maxStep m = m ∨ L.foldl maxStep m ∈ L) ∧ m ≤ L.foldl maxStep m ∧
      ∀ t ∈ L, t ≤ L.foldl maxStep m
  | [], m => by simp
  | t :: L, m => by
    obtain ⟨h1, h2, h3⟩ := foldl_maxStep L (maxStep m t)
    simp only [List.foldl_cons]
    unfold maxStep at h1 h2 h3 ⊢
    split_ifs at h1 h2 h3 ⊢ with h
    · refine ⟨?_, le_trans (le_of_lt h) h2, ?_⟩
      · rcases h1 with h1 | h1
        · right; rw [h1]; simp
        · right; simp [h1]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h2
        · exact h3 w hw
    · refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1
        · left; exact h1
        · right; simp [h1]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact le_trans (not_lt.mp h) h2
        · exact h3 w hw

theorem minL_mem {L : List (List ℕ)} (h : L ≠ []) : minL L ∈ L := by
  obtain ⟨t, L', rfl⟩ := List.exists_cons_of_ne_nil h
  rcases (foldl_minStep (t :: L') t).1 with h1 | h1
  · unfold minL; rw [List.headD_cons, h1]; simp
  · exact h1

theorem minL_le {L : List (List ℕ)} {t : List ℕ} (h : t ∈ L) : minL L ≤ t :=
  (foldl_minStep L _).2.2 t h

theorem maxL_mem {L : List (List ℕ)} (h : L ≠ []) : maxL L ∈ L := by
  obtain ⟨t, L', rfl⟩ := List.exists_cons_of_ne_nil h
  rcases (foldl_maxStep (t :: L') t).1 with h1 | h1
  · unfold maxL; rw [List.headD_cons, h1]; simp
  · exact h1

theorem le_maxL {L : List (List ℕ)} {t : List ℕ} (h : t ∈ L) : t ≤ maxL L :=
  (foldl_maxStep L _).2.2 t h

theorem foldl_succStep (u : List ℕ) : ∀ (L : List (List ℕ)) (acc : Option (List ℕ)),
    (∀ a, acc = some a → u < a) →
      (L.foldl (succStep u) acc = none ↔ acc = none ∧ ∀ w ∈ L, ¬ u < w) ∧
      ∀ v, L.foldl (succStep u) acc = some v →
        (acc = some v ∨ v ∈ L) ∧ u < v ∧ (∀ w ∈ L, u < w → v ≤ w) ∧ (∀ a, acc = some a → v ≤ a)
  | [], acc, hacc => by
    refine ⟨by simp, fun v hv => ?_⟩
    simp only [List.foldl_nil] at hv
    subst hv
    exact ⟨Or.inl rfl, hacc v rfl, by simp, fun a ha => by cases ha; exact le_rfl⟩
  | w :: L, acc, hacc => by
    simp only [List.foldl_cons]
    by_cases huw : u < w
    · have hstep : ∃ v', succStep u acc w = some v' ∧ u < v' ∧ v' ≤ w ∧
          (v' = w ∨ acc = some v') ∧ ∀ a, acc = some a → v' ≤ a := by
        unfold succStep
        rw [if_pos huw]
        rcases acc with _ | a
        · exact ⟨w, rfl, huw, le_rfl, Or.inl rfl, fun a ha => by cases ha⟩
        · refine ⟨if w < a then w else a, rfl, ?_, ?_, ?_, ?_⟩
          · split_ifs
            · exact huw
            · exact hacc a rfl
          · split_ifs with h
            · exact le_rfl
            · exact not_lt.mp h
          · split_ifs
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro a' ha'
            cases ha'
            split_ifs with h
            · exact le_of_lt h
            · exact le_rfl
      obtain ⟨v', hv', huv', hvw, hvor, hvacc⟩ := hstep
      rw [hv']
      obtain ⟨ih1, ih2⟩ := foldl_succStep u L (some v') (fun a ha => by cases ha; exact huv')
      refine ⟨?_, fun v hv => ?_⟩
      · rw [ih1]
        constructor
        · rintro ⟨h, -⟩; cases h
        · rintro ⟨-, h⟩; exact absurd huw (h w (by simp))
      · obtain ⟨h1, h2, h3, h4⟩ := ih2 v hv
        have hvv' := h4 v' rfl
        refine ⟨?_, h2, ?_, fun a ha => le_trans hvv' (hvacc a ha)⟩
        · rcases h1 with h1 | h1
          · cases h1
            rcases hvor with rfl | h
            · right; simp
            · left; exact h
          · right; simp [h1]
        · intro w' hw' huw'
          rcases List.mem_cons.mp hw' with rfl | hw'
          · exact le_trans hvv' hvw
          · exact h3 w' hw' huw'
    · have hstep : succStep u acc w = acc := by unfold succStep; rw [if_neg huw]
      rw [hstep]
      obtain ⟨ih1, ih2⟩ := foldl_succStep u L acc hacc
      refine ⟨?_, fun v hv => ?_⟩
      · rw [ih1]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨fun ⟨a, b⟩ => ⟨a, huw, b⟩, fun ⟨a, _, b⟩ => ⟨a, b⟩⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih2 v hv
        refine ⟨?_, h2, ?_, h4⟩
        · rcases h1 with h1 | h1
          · left; exact h1
          · right; simp [h1]
        · intro w' hw' huw'
          rcases List.mem_cons.mp hw' with rfl | hw'
          · exact absurd huw' huw
          · exact h3 w' hw' huw'

/-- **The successor**: the smallest tuple above `u`. -/
theorem succOf_some {L : List (List ℕ)} {u v : List ℕ} (h : succOf L u = some v) :
    v ∈ L ∧ u < v ∧ ∀ w ∈ L, u < w → v ≤ w := by
  obtain ⟨h1, h2, h3, -⟩ := (foldl_succStep u L none (fun a ha => by cases ha)).2 v h
  exact ⟨h1.resolve_left (by simp), h2, h3⟩

theorem succOf_none {L : List (List ℕ)} {u : List ℕ} :
    succOf L u = none ↔ ∀ w ∈ L, ¬ u < w := by
  rw [succOf, (foldl_succStep u L none (fun a ha => by cases ha)).1]; simp

/-! ### The lists of tuples of the new symbols -/

/-- Consecutive tuples `u ++ v`, `v` the successor of `u`, in the order of `u`. -/
def sList (L : List (List ℕ)) : List (List ℕ) := L.filterMap fun u => (succOf L u).map (u ++ ·)

/-- The first tuple, if any. -/
def fList (L : List (List ℕ)) : List (List ℕ) := if L = [] then [] else [minL L]

/-- The last tuple, if any. -/
def lList (L : List (List ℕ)) : List (List ℕ) := if L = [] then [] else [maxL L]

/-- The universe, if there are no tuples. -/
def zList (N : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  if L = [] then (List.range N).map fun a => [a] else []

/-- The pairs `[a, b]` with `a < b < N`, in lexicographic order. -/
def ltList (N : ℕ) : List (List ℕ) :=
  (List.range N).flatMap fun a => ((List.range N).filter (a < ·)).map fun b => [a, b]

theorem mem_ltList {N : ℕ} {t : List ℕ} : t ∈ ltList N ↔ ∃ a b, t = [a, b] ∧ a < b ∧ b < N := by
  simp only [ltList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩; exact ⟨a, b, rfl, hab, hb⟩
  · rintro ⟨a, b, rfl, hab, hb⟩; exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl⟩

theorem mem_sList {L : List (List ℕ)} {t : List ℕ} :
    t ∈ sList L ↔ ∃ u ∈ L, ∃ v, succOf L u = some v ∧ t = u ++ v := by
  simp only [sList, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

theorem mem_fList {L : List (List ℕ)} {t : List ℕ} : t ∈ fList L ↔ L ≠ [] ∧ t = minL L := by
  unfold fList; split_ifs with h <;> simp [h]

theorem mem_lList {L : List (List ℕ)} {t : List ℕ} : t ∈ lList L ↔ L ≠ [] ∧ t = maxL L := by
  unfold lList; split_ifs with h <;> simp [h]

theorem mem_zList {N : ℕ} {L : List (List ℕ)} {t : List ℕ} :
    t ∈ zList N L ↔ L = [] ∧ ∃ a < N, t = [a] := by
  unfold zList; split_ifs with h <;> simp [h, eq_comm]

theorem nodup_ltList (N : ℕ) : (ltList N).Nodup := by
  unfold ltList
  refine List.nodup_flatMap.mpr ⟨fun a _ => ?_, ?_⟩
  · refine List.Nodup.map (fun b b' h => by simpa using h) ((List.nodup_range).filter _)
  · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a a' _ _ hne
    simp only [Function.onFun, List.disjoint_iff_ne, List.mem_map, List.mem_filter]
    rintro _ ⟨b, -, rfl⟩ _ ⟨b', -, rfl⟩ h
    simp at h; exact hne h.1

theorem nodup_sList {L : List (List ℕ)} {r : ℕ} (hL : L.Nodup) (hr : ∀ t ∈ L, t.length = r) :
    (sList L).Nodup := by
  have hp : L.Pairwise (fun u u' => u ≠ u' ∧ u.length = r ∧ u'.length = r) :=
    hL.imp_of_mem fun hu hu' hne => ⟨hne, hr _ hu, hr _ hu'⟩
  unfold sList
  refine hp.filterMap _ ?_
  rintro u u' ⟨hne, hu, hu'⟩ b hb b' hb' rfl
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨v, -, rfl⟩ := hb
  obtain ⟨v', -, he⟩ := hb'
  exact hne (List.append_inj he.symm (by rw [hu, hu'])).1

theorem nodup_fList (L : List (List ℕ)) : (fList L).Nodup := by
  unfold fList; split_ifs <;> simp

theorem nodup_lList (L : List (List ℕ)) : (lList L).Nodup := by
  unfold lList; split_ifs <;> simp

theorem nodup_zList (N : ℕ) (L : List (List ℕ)) : (zList N L).Nodup := by
  unfold zList; split_ifs
  · exact List.nodup_range.map fun a b h => by simpa using h
  · simp

/-! ### Lists of five per symbol -/

theorem length_flatMap_range {α : Type} (f : ℕ → List α) (hf : ∀ i, (f i).length = 5) :
    ∀ s, ((List.range s).flatMap f).length = 5 * s
  | 0 => by simp
  | s + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range f hf s]
    simp [hf]; ring

theorem getD_flatMap_range {α : Type} (f : ℕ → List α) (hf : ∀ i, (f i).length = 5) (d : α) :
    ∀ (s i j : ℕ), j < 5 →
      ((List.range s).flatMap f).getD (5 * i + j) d = if i < s then (f i).getD j d else d
  | 0, i, j, _ => by simp
  | s + 1, i, j, hj => by
    have hl := length_flatMap_range f hf s
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_or_ge i s with hi | hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hl]; omega),
        ← List.getD_eq_getElem?_getD, getD_flatMap_range f hf d s i j hj, if_pos hi,
        if_pos (by omega)]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl,
        ← List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_ge i (s + 1) with hi' | hi'
      · have : i = s := by omega
        subst this
        rw [if_pos hi', show 5 * i + j - 5 * i = j by omega]
      · rw [if_neg (by omega)]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hf]; omega)]
        rfl

/-- Every `k` is `0` or `5 i + 1 + j` with `j < 5`. -/
theorem index_cases (k : ℕ) : k = 0 ∨ ∃ i j, j < 5 ∧ k = 5 * i + 1 + j := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact Or.inl h
  · exact Or.inr ⟨(k - 1) / 5, (k - 1) % 5, Nat.mod_lt _ (by decide), by omega⟩

/-! ### The data of the expanded structure -/

/-- The data the expanded structure is built from: the number of old symbols, the size of the
universe, the arities, and the tuples of each old symbol as the word lists them. -/
structure NData where
  s : ℕ
  N : ℕ
  ar : ℕ → ℕ
  L : ℕ → List (List ℕ)

namespace NData

variable (D : NData)

/-- The data describe a structure. -/
structure Valid : Prop where
  pos : ∀ i < D.s, 1 ≤ D.ar i
  nodup : ∀ i < D.s, (D.L i).Nodup
  tup : ∀ i < D.s, ∀ t ∈ D.L i, t.length = D.ar i ∧ ∀ a ∈ t, a < D.N

/-- The expanded vocabulary. -/
def arities : List ℕ := 2 :: (List.range D.s).flatMap fun i => arBlk (D.ar i)

/-- The lists of tuples of the five new symbols of the old symbol `i`. -/
def blocks (i : ℕ) : List (List (List ℕ)) :=
  [D.L i, fList (D.L i), lList (D.L i), sList (D.L i), zList D.N (D.L i)]

/-- The lists of tuples of all new symbols. -/
def tss : List (List (List ℕ)) := ltList D.N :: (List.range D.s).flatMap D.blocks

/-- The tuples of new symbol `k`. -/
def relList (k : ℕ) : List (List ℕ) := D.tss.getD k []

/-- **The word of the expanded structure.** -/
def word : List ℕ := wordOf D.arities D.N D.tss

theorem length_arities : D.arities.length = 5 * D.s + 1 := by
  rw [arities, List.length_cons, length_flatMap_range (fun i => arBlk (D.ar i)) (fun i => rfl)]

theorem length_tss : D.tss.length = 5 * D.s + 1 := by
  rw [tss, List.length_cons, length_flatMap_range D.blocks (fun i => rfl)]

theorem arities_zero : D.arities.getD 0 0 = 2 := rfl

theorem arities_blk (i j : ℕ) (hj : j < 5) :
    D.arities.getD (5 * i + 1 + j) 0 = if i < D.s then (arBlk (D.ar i)).getD j 0 else 0 := by
  rw [arities, show 5 * i + 1 + j = (5 * i + j) + 1 by ring, List.getD_cons_succ,
    getD_flatMap_range _ (fun i => rfl) 0 D.s i j hj]

theorem relList_zero : D.relList 0 = ltList D.N := rfl

theorem relList_blk (i j : ℕ) (hj : j < 5) :
    D.relList (5 * i + 1 + j) = if i < D.s then (D.blocks i).getD j [] else [] := by
  rw [relList, tss, show 5 * i + 1 + j = (5 * i + j) + 1 by ring, List.getD_cons_succ,
    getD_flatMap_range _ (fun i => rfl) [] D.s i j hj]

variable {D}

/-- Every tuple of a new symbol has its arity and entries in the universe. -/
theorem relList_wf (hv : D.Valid) (k : ℕ) {t : List ℕ} (ht : t ∈ D.relList k) :
    k < D.arities.length ∧ t.length = D.arities.getD k 0 ∧ ∀ a ∈ t, a < D.N := by
  rcases index_cases k with rfl | ⟨i, j, hj, rfl⟩
  · rw [relList_zero, mem_ltList] at ht
    obtain ⟨a, b, rfl, hab, hb⟩ := ht
    refine ⟨by rw [length_arities]; omega, by rw [arities_zero]; rfl, ?_⟩
    intro c hc; simp at hc; omega
  · rw [relList_blk D i j hj] at ht
    by_cases hi : i < D.s
    swap; · rw [if_neg hi] at ht; simp at ht
    rw [if_pos hi] at ht
    rw [length_arities, arities_blk D i j hj, if_pos hi]
    refine ⟨by omega, ?_⟩
    have ht' := hv.tup i hi
    interval_cases j
    · exact ht' t ht
    · obtain ⟨hne, rfl⟩ := mem_fList.mp ht; exact ht' _ (minL_mem hne)
    · obtain ⟨hne, rfl⟩ := mem_lList.mp ht; exact ht' _ (maxL_mem hne)
    · obtain ⟨u, hu, v, hv', rfl⟩ := mem_sList.mp ht
      have hvm := (succOf_some hv').1
      refine ⟨by simp [arBlk, (ht' u hu).1, (ht' v hvm).1]; ring, fun a ha => ?_⟩
      rcases List.mem_append.mp ha with ha | ha
      · exact (ht' u hu).2 a ha
      · exact (ht' v hvm).2 a ha
    · obtain ⟨-, a, ha, rfl⟩ := mem_zList.mp ht
      exact ⟨rfl, by simpa using ha⟩

theorem arities_pos (hv : D.Valid) : ∀ a ∈ D.arities, 1 ≤ a := by
  intro a ha
  simp only [arities, List.mem_cons, List.mem_flatMap, List.mem_range, arBlk] at ha
  rcases ha with rfl | ⟨i, hi, ha⟩
  · norm_num
  · have := hv.pos i hi
    simp at ha; omega

/-- **The expanded structure.** -/
def toStructure (hv : D.Valid) : Structure where
  arities := D.arities
  size := D.N
  rel k := (D.relList k).toFinset
  arity_pos := arities_pos hv
  wf i _ ht := relList_wf hv i (List.mem_toFinset.mp ht)

theorem nodup_relList (hv : D.Valid) (k : ℕ) : (D.relList k).Nodup := by
  rcases index_cases k with rfl | ⟨i, j, hj, rfl⟩
  · exact nodup_ltList _
  · rw [relList_blk D i j hj]
    by_cases hi : i < D.s
    swap; · rw [if_neg hi]; simp
    rw [if_pos hi]
    interval_cases j
    · exact hv.nodup i hi
    · exact nodup_fList _
    · exact nodup_lList _
    · exact nodup_sList (hv.nodup i hi) fun t ht => (hv.tup i hi t ht).1
    · exact nodup_zList _ _

/-- **The word encodes the expanded structure.** -/
theorem encodes_word (hv : D.Valid) : Encodes D.word (toStructure hv) := by
  refine encodes_wordOf (toStructure hv) D.tss ?_ fun k _ => ⟨nodup_relList hv k, rfl⟩
  show D.tss.length = D.arities.length
  rw [length_tss, length_arities]

/-! ### The relations of the expanded structure -/

theorem mem_rel_lt (hv : D.Valid) {t : List ℕ} :
    t ∈ (toStructure hv).rel 0 ↔ ∃ a b, t = [a, b] ∧ a < b ∧ b < D.N := by
  show t ∈ (D.relList 0).toFinset ↔ _
  rw [List.mem_toFinset, relList_zero, mem_ltList]

theorem mem_rel_blk (hv : D.Valid) {i : ℕ} (hi : i < D.s) (j : ℕ) (hj : j < 5) {t : List ℕ} :
    t ∈ (toStructure hv).rel (5 * i + 1 + j) ↔ t ∈ (D.blocks i).getD j [] := by
  show t ∈ (D.relList _).toFinset ↔ _
  rw [List.mem_toFinset, relList_blk D i j hj, if_pos hi]

theorem mem_rel_r (hv : D.Valid) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ (toStructure hv).rel (rI i) ↔ t ∈ D.L i := mem_rel_blk hv hi 0 (by decide)

theorem mem_rel_f (hv : D.Valid) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ (toStructure hv).rel (fI i) ↔ D.L i ≠ [] ∧ t = minL (D.L i) := by
  rw [← mem_fList]; exact mem_rel_blk hv hi 1 (by decide)

theorem mem_rel_l (hv : D.Valid) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ (toStructure hv).rel (lI i) ↔ D.L i ≠ [] ∧ t = maxL (D.L i) := by
  rw [← mem_lList]; exact mem_rel_blk hv hi 2 (by decide)

theorem mem_rel_s (hv : D.Valid) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ (toStructure hv).rel (sI i) ↔ ∃ u ∈ D.L i, ∃ v, succOf (D.L i) u = some v ∧ t = u ++ v := by
  rw [← mem_sList]; exact mem_rel_blk hv hi 3 (by decide)

theorem mem_rel_z (hv : D.Valid) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ (toStructure hv).rel (zI i) ↔ D.L i = [] ∧ ∃ a < D.N, t = [a] := by
  rw [← mem_zList]; exact mem_rel_blk hv hi 4 (by decide)

/-- The expanded vocabulary of `as`. -/
theorem extAr {as : List ℕ} (hv : D.Valid) (hs : as.length = D.s)
    (har : ∀ i < D.s, as.getD i 0 = D.ar i) : ExtAr as D.arities where
  len := by rw [length_arities, hs]
  zero := rfl
  blk i hi j hj := by rw [arities_blk D i j hj, if_pos (by omega), har i (by omega)]
  pos i hi := by rw [har i (by omega)]; exact hv.pos i (by omega)

end NData

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct
