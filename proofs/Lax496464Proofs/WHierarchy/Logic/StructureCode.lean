import Lax496464.WH_B1_Structures
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-! The word of a structure (`WH_B1_Structures.Encodes`) is self-delimiting and determines the
structure: two encodings of which one extends the other are the same word, of the same structure.
The listing order of the tuples of a relation is free, but the relation as a set of tuples is
determined, and structures with the same arities, size and relations are equal.

Also a canonical encoder `canonicalWord : Structure → List ℕ` (each relation's tuples sorted in the
lexicographic order of `List ℕ`), and the general builder `wordOf` of a word from one list of tuples
per symbol, with the conditions under which it encodes a given structure. -/

namespace Lax496464Proofs.WHierarchy.Logic.StructureCode

open Lax496464.WH_B1_Structures

/-! ### Equality of structures -/

/-- **Extensionality.** Structures with the same arities, size and relations are equal. -/
theorem Structure.ext' {A A' : Structure} (ha : A.arities = A'.arities) (hs : A.size = A'.size)
    (hr : ∀ i, A.rel i = A'.rel i) : A = A' := by
  cases A; cases A'
  simp only at ha hs hr
  subst ha hs
  have : _ = _ := funext hr
  subst this
  rfl

/-- A symbol outside the vocabulary has no tuples. -/
theorem rel_eq_empty_of_le (A : Structure) {i : ℕ} (hi : A.arities.length ≤ i) : A.rel i = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun t ht => ?_
  have := (A.wf i t ht).1
  omega

/-- Every tuple of symbol `i` has the arity of `i`. -/
theorem length_of_mem_rel (A : Structure) {i : ℕ} {t : List ℕ} (ht : t ∈ A.rel i) :
    t.length = A.arities.getD i 0 := (A.wf i t ht).2.1

/-! ### Blocks -/

/-- A block of tuples of arity `a`: a count `c`, then `c * a` entries. -/
def BlockShape (a : ℕ) (blk : List ℕ) : Prop := ∃ c rest, blk = c :: rest ∧ rest.length = c * a

theorem length_flatten_of_forall {ts : List (List ℕ)} {a : ℕ} (h : ∀ t ∈ ts, t.length = a) :
    ts.flatten.length = ts.length * a := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h t (by simp), ih fun u hu => h u (by simp [hu])]
    ring

/-- A block of tuples all of arity `a` has the shape of an `a`-block. -/
theorem blockShape_of_encodesRel {R : Finset (List ℕ)} {blk : List ℕ} {a : ℕ}
    (h : EncodesRel R blk) (hR : ∀ t ∈ R, t.length = a) : BlockShape a blk := by
  obtain ⟨ts, -, hts, rfl⟩ := h
  refine ⟨ts.length, ts.flatten, rfl, length_flatten_of_forall fun t ht => hR t ?_⟩
  rw [← hts]; exact List.mem_toFinset.mpr ht

/-- A list of tuples of one length is determined by its flattening and its number of tuples. -/
theorem tuples_eq_of_flatten : ∀ {ts ts' : List (List ℕ)} {a : ℕ},
    (∀ t ∈ ts, t.length = a) → (∀ t ∈ ts', t.length = a) → ts.length = ts'.length →
    ts.flatten = ts'.flatten → ts = ts'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | t :: ts, t' :: ts', a, h1, h2, hl, hf => by
    simp only [List.flatten_cons] at hf
    obtain ⟨rfl, hf'⟩ := List.append_inj hf (by rw [h1 t (by simp), h2 t' (by simp)])
    rw [tuples_eq_of_flatten (fun u hu => h1 u (by simp [hu])) (fun u hu => h2 u (by simp [hu]))
      (by simpa using hl) hf']

/-- **A sequence of blocks is self-delimiting**, given the arities. -/
theorem blocks_prefix : ∀ (as : List ℕ) (bs bs' : List (List ℕ)) (r r' : List ℕ),
    bs.length = as.length → bs'.length = as.length →
    (∀ i < as.length, BlockShape (as.getD i 0) (bs.getD i [])) →
    (∀ i < as.length, BlockShape (as.getD i 0) (bs'.getD i [])) →
    bs.flatten ++ r = bs'.flatten ++ r' → bs = bs' ∧ r = r'
  | [], [], [], r, r', _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, _, h, _, _, _, _ => by simp at h
  | [], [], _ :: _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _, _, _ => by simp at h
  | a :: as, b :: bs, b' :: bs', r, r', hl, hl', hb, hb', h => by
    obtain ⟨c, rest, rfl, hrest⟩ := hb 0 (by simp)
    obtain ⟨c', rest', rfl, hrest'⟩ := hb' 0 (by simp)
    simp only [List.getD_cons_zero] at hrest hrest'
    simp only [List.flatten_cons, List.cons_append, List.append_assoc, List.cons.injEq] at h
    obtain ⟨hc, h1⟩ := h
    subst hc
    obtain ⟨hr1, h2⟩ := List.append_inj h1 (by rw [hrest, hrest'])
    subst hr1
    obtain ⟨h3, h4⟩ := blocks_prefix as bs bs' r r' (by simpa using hl) (by simpa using hl')
      (fun i hi => by simpa using hb (i + 1) (by simp; omega))
      (fun i hi => by simpa using hb' (i + 1) (by simp; omega)) h2
    subst h3
    exact ⟨rfl, h4⟩

/-! ### The structure word -/

/-- The blocks of an encoding have the shape given by the arities. -/
theorem blockShape_of_encodes {A : Structure} {blocks : List (List ℕ)}
    (h : ∀ i < A.arities.length, EncodesRel (A.rel i) (blocks.getD i [])) :
    ∀ i < A.arities.length, BlockShape (A.arities.getD i 0) (blocks.getD i []) :=
  fun i hi => blockShape_of_encodesRel (h i hi) fun _ ht => length_of_mem_rel A ht

/-- **The structure code is self-delimiting and determines the structure.** -/
theorem encodes_prefix {y y' r r' : List ℕ} {A A' : Structure} (h : Encodes y A)
    (h' : Encodes y' A') (he : y ++ r = y' ++ r') : y = y' ∧ A = A' ∧ r = r' := by
  obtain ⟨bl, hbl, hrel, rfl⟩ := h
  obtain ⟨bl', hbl', hrel', rfl⟩ := h'
  simp only [List.cons_append, List.append_assoc, List.cons.injEq] at he
  obtain ⟨hs, he⟩ := he
  obtain ⟨har, he⟩ := List.append_inj he hs
  simp only [List.cons.injEq] at he
  obtain ⟨hsz, he⟩ := he
  have hsh := blockShape_of_encodes hrel
  have hsh' := blockShape_of_encodes hrel'
  rw [← har] at hbl' hsh'
  obtain ⟨rfl, rfl⟩ := blocks_prefix A.arities bl bl' r r' hbl hbl' hsh hsh' he
  have hA : A = A' := by
    refine Structure.ext' har hsz fun i => ?_
    by_cases hi : i < A.arities.length
    · obtain ⟨ts, -, hts, hb⟩ := hrel i hi
      obtain ⟨ts', -, hts', hb'⟩ := hrel' i (by rw [← har]; exact hi)
      rw [hb] at hb'
      simp only [List.cons.injEq] at hb'
      have hlen : ∀ t ∈ ts, t.length = A.arities.getD i 0 := fun t ht =>
        length_of_mem_rel A (by rw [← hts]; exact List.mem_toFinset.mpr ht)
      have hlen' : ∀ t ∈ ts', t.length = A.arities.getD i 0 := fun t ht => by
        rw [har]; exact length_of_mem_rel A' (by rw [← hts']; exact List.mem_toFinset.mpr ht)
      rw [← hts, ← hts', tuples_eq_of_flatten hlen hlen' hb'.1 hb'.2]
    · rw [rel_eq_empty_of_le A (by omega), rel_eq_empty_of_le A' (by rw [← har]; omega)]
  subst hA
  exact ⟨rfl, rfl, rfl⟩

/-- An encoding determines the structure. -/
theorem encodes_unique {y : List ℕ} {A A' : Structure} (h : Encodes y A) (h' : Encodes y A') :
    A = A' :=
  (encodes_prefix (r := []) (r' := []) h h' rfl).2.1

/-- The word of a structure begins with its number of symbols. -/
theorem encodes_head {y : List ℕ} {A : Structure} (h : Encodes y A) :
    y = A.arities.length :: (A.arities ++ A.size :: y.drop (A.arities.length + 2)) := by
  obtain ⟨bl, -, -, rfl⟩ := h
  simp [List.drop_append]

/-- The length of the word of a structure: the header and one block per symbol. -/
theorem length_of_encodes {y : List ℕ} {A : Structure} (h : Encodes y A) :
    y.length = 2 + A.arities.length +
      ∑ i ∈ Finset.range A.arities.length, (1 + (A.rel i).card * A.arities.getD i 0) := by
  obtain ⟨bl, hbl, hrel, rfl⟩ := h
  have key : ∀ (bl : List (List ℕ)) (as : List ℕ) (R : ℕ → Finset (List ℕ)),
      bl.length = as.length →
      (∀ i < as.length, EncodesRel (R i) (bl.getD i [])) →
      (∀ i, ∀ t ∈ R i, t.length = as.getD i 0) →
      bl.flatten.length = ∑ i ∈ Finset.range as.length, (1 + (R i).card * as.getD i 0) := by
    intro bl
    induction bl with
    | nil => intro as R h _ _; cases as <;> simp_all
    | cons b bl ih =>
      intro as R hl hr hlen
      cases as with
      | nil => simp at hl
      | cons a as =>
        rw [List.length_cons, Finset.sum_range_succ']
        simp only [List.flatten_cons, List.length_append, List.getD_cons_succ,
          List.getD_cons_zero]
        rw [ih as (fun i => R (i + 1)) (by simpa using hl)
          (fun i hi => by simpa using hr (i + 1) (by simp; omega))
          (fun i t ht => by simpa using hlen (i + 1) t ht)]
        obtain ⟨ts, hnd, hts, hb⟩ := hr 0 (by simp)
        simp only [List.getD_cons_zero] at hb
        rw [hb, ← hts, List.toFinset_card_of_nodup hnd]
        simp only [List.length_cons]
        rw [length_flatten_of_forall (a := a) fun t ht => by
          simpa using hlen 0 t (by rw [← hts]; exact List.mem_toFinset.mpr ht)]
        ring
  rw [show (A.arities.length :: (A.arities ++ A.size :: bl.flatten)).length =
    2 + A.arities.length + bl.flatten.length by simp; ring,
    key bl A.arities A.rel hbl hrel fun i t ht => length_of_mem_rel A ht]

/-! ### Building words -/

/-- The block of a list of tuples. -/
def blockOf (ts : List (List ℕ)) : List ℕ := ts.length :: ts.flatten

/-- The word with the given arities and size and one list of tuples per symbol. -/
def wordOf (arities : List ℕ) (size : ℕ) (tss : List (List (List ℕ))) : List ℕ :=
  arities.length :: (arities ++ size :: (tss.map blockOf).flatten)

/-- **`wordOf` encodes a structure** when each list lists its relation without repetition. -/
theorem encodes_wordOf (A : Structure) (tss : List (List (List ℕ)))
    (hlen : tss.length = A.arities.length)
    (h : ∀ i < A.arities.length, (tss.getD i []).Nodup ∧ (tss.getD i []).toFinset = A.rel i) :
    Encodes (wordOf A.arities A.size tss) A := by
  refine ⟨tss.map blockOf, by simpa using hlen, fun i hi => ?_, rfl⟩
  refine ⟨tss.getD i [], (h i hi).1, (h i hi).2, ?_⟩
  have hi' : i < tss.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', blockOf]

/-- The tuples of a relation in the lexicographic order of `List ℕ`. -/
def sortedTuples (R : Finset (List ℕ)) : List (List ℕ) := R.sort

theorem sortedTuples_nodup (R : Finset (List ℕ)) : (sortedTuples R).Nodup := Finset.sort_nodup _ _

theorem sortedTuples_toFinset (R : Finset (List ℕ)) : (sortedTuples R).toFinset = R :=
  Finset.sort_toFinset _ _

/-- The canonical lists of tuples of a structure. -/
def canonicalTuples (A : Structure) : List (List (List ℕ)) :=
  (List.range A.arities.length).map fun i => sortedTuples (A.rel i)

/-- **The canonical word of a structure**: the relations' tuples sorted lexicographically. -/
def canonicalWord (A : Structure) : List ℕ := wordOf A.arities A.size (canonicalTuples A)

theorem encodes_canonicalWord (A : Structure) : Encodes (canonicalWord A) A := by
  refine encodes_wordOf A _ (by simp [canonicalTuples]) fun i hi => ?_
  have : (canonicalTuples A).getD i [] = sortedTuples (A.rel i) := by
    simp [canonicalTuples, List.getD_eq_getElem?_getD, hi]
  rw [this]
  exact ⟨sortedTuples_nodup _, sortedTuples_toFinset _⟩

/-- Every structure has an encoding. -/
theorem exists_encodes (A : Structure) : ∃ y, Encodes y A := ⟨_, encodes_canonicalWord A⟩

/-- The canonical word of a structure is its only word up to the listing order: every word of
`A` has the same length as the canonical one. -/
theorem length_eq_of_encodes {y y' : List ℕ} {A : Structure} (h : Encodes y A)
    (h' : Encodes y' A) : y.length = y'.length := by
  rw [length_of_encodes h, length_of_encodes h']

end Lax496464Proofs.WHierarchy.Logic.StructureCode
