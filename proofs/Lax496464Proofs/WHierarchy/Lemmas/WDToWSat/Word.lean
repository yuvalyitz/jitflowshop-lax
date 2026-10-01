import Lax496464Proofs.WHierarchy.Logic.StructureCode
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm
import Lax496464.WH_B3_LogicProblems

/-! # Reading a weighted-definability word

The quantities the reduction reads off the word `x` of `(A, k)`: the number of symbols, the arities,
the size `N` of the universe, `k`, the start of the block of each relation (`boW`), membership of a
tuple in a relation by a scan of its block (`memW`), and the list `UW` of the elements the reduction
works with: `0, …, L-1` for `L = min(N, |x| + s·k + r)`, followed by every other entry of the word
below `N`, once. Every active element is among them (it is an entry of the word). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word

open Lax496464.WH_B1_Structures Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.StructureCode Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm

/-- The number of symbols. -/
def spW (x : List ℕ) : ℕ := x.getD 0 0

/-- The size of the universe. -/
def NW (x : List ℕ) : ℕ := x.getD (1 + spW x) 0

/-- The last entry, `k`. -/
def kW (x : List ℕ) : ℕ := x.getD (x.length - 1) 0

/-- The position of the block of symbol `i`. -/
def boW (x : List ℕ) : ℕ → ℕ
  | 0 => 2 + spW x
  | i + 1 => boW x i + 1 + x.getD (boW x i) 0 * x.getD (1 + i) 0

/-- The tuple is listed in the block of symbol `i` (read with the tuple's length as the arity). -/
def memW (x : List ℕ) (i : ℕ) (tup : List ℕ) : Prop :=
  ∃ t < x.getD (boW x i) 0, ∀ q < tup.length,
    x.getD (boW x i + 1 + t * tup.length + q) 0 = tup.getD q 0

instance (x : List ℕ) (i : ℕ) (tup : List ℕ) : Decidable (memW x i tup) := by
  unfold memW; infer_instance

/-- The number of elements `0, …, L-1` taken in full. -/
def LW (s r : ℕ) (x : List ℕ) : ℕ := min (NW x) (x.length + s * kW x + r)

/-- One step of collecting the entries: append `e` if it is in `[L, N)` and new. -/
def pushStep (L N : ℕ) (acc : List ℕ) (e : ℕ) : List ℕ :=
  if L ≤ e ∧ e < N ∧ e ∉ acc then acc ++ [e] else acc

/-- **The elements the reduction works with.** -/
def UW (s r : ℕ) (x : List ℕ) : List ℕ := x.foldl (pushStep (LW s r x) (NW x)) (List.range (LW s r x))

/-! ### Collecting entries -/

section Collect
variable {L N : ℕ}

theorem foldl_push_nodup : ∀ (ys acc : List ℕ), acc.Nodup → (ys.foldl (pushStep L N) acc).Nodup
  | [], _, h => h
  | e :: ys, acc, h => by
    rw [List.foldl_cons]
    refine foldl_push_nodup ys _ ?_
    unfold pushStep
    split_ifs with he
    · exact List.nodup_append.mpr ⟨h, List.nodup_singleton e, by simp; intro a ha hae; exact he.2.2 (hae ▸ ha)⟩
    · exact h

theorem mem_foldl_push : ∀ (ys acc : List ℕ) (v : ℕ),
    v ∈ ys.foldl (pushStep L N) acc ↔ v ∈ acc ∨ (v ∈ ys ∧ L ≤ v ∧ v < N)
  | [], acc, v => by simp
  | e :: ys, acc, v => by
    rw [List.foldl_cons, mem_foldl_push ys _ v]
    unfold pushStep
    split_ifs with he
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, he.1, he.2.1⟩
        · exact Or.inr ⟨Or.inr h.1, h.2⟩
      · rintro (h | ⟨rfl | h, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨h, h1, h2⟩
    · simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h.1, h.2⟩
      · rintro (h | ⟨rfl | h, h1, h2⟩)
        · exact Or.inl h
        · by_cases hv : v ∈ acc
          · exact Or.inl hv
          · exact absurd ⟨h1, h2, hv⟩ he
        · exact Or.inr ⟨h, h1, h2⟩

theorem length_foldl_push : ∀ (ys acc : List ℕ),
    (ys.foldl (pushStep L N) acc).length ≤ acc.length + ys.length
  | [], acc => by simp
  | e :: ys, acc => by
    rw [List.foldl_cons]
    have := length_foldl_push ys (pushStep L N acc e)
    have h2 : (pushStep L N acc e).length ≤ acc.length + 1 := by
      unfold pushStep; split_ifs <;> simp
    simp only [List.length_cons]; omega

/-- A prefix of the input collected: one more entry is one more step. -/
theorem foldl_push_take (ys acc : List ℕ) (p : ℕ) (hp : p < ys.length) :
    (ys.take (p + 1)).foldl (pushStep L N) acc =
      pushStep L N ((ys.take p).foldl (pushStep L N) acc) (ys.getD p 0) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hp]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]

end Collect

theorem LW_le (s r : ℕ) (x : List ℕ) : LW s r x ≤ NW x := min_le_left _ _

theorem UW_nodup (s r : ℕ) (x : List ℕ) : (UW s r x).Nodup :=
  foldl_push_nodup x _ (List.nodup_range)

theorem mem_UW {s r : ℕ} {x : List ℕ} {v : ℕ} :
    v ∈ UW s r x ↔ v < LW s r x ∨ (v ∈ x ∧ LW s r x ≤ v ∧ v < NW x) := by
  unfold UW; rw [mem_foldl_push]; simp

theorem lt_of_mem_UW {s r : ℕ} {x : List ℕ} {v : ℕ} (h : v ∈ UW s r x) : v < NW x := by
  rcases mem_UW.mp h with h | ⟨-, -, h⟩
  · exact lt_of_lt_of_le h (LW_le s r x)
  · exact h

theorem mem_UW_of_lt {s r : ℕ} {x : List ℕ} {v : ℕ} (h : v < LW s r x) : v ∈ UW s r x :=
  mem_UW.mpr (Or.inl h)

theorem mem_UW_of_mem {s r : ℕ} {x : List ℕ} {v : ℕ} (h : v ∈ x) (hv : v < NW x) :
    v ∈ UW s r x := by
  by_cases hl : v < LW s r x
  · exact mem_UW_of_lt hl
  · exact mem_UW.mpr (Or.inr ⟨h, by omega, hv⟩)

theorem length_UW_le (s r : ℕ) (x : List ℕ) : (UW s r x).length ≤ LW s r x + x.length := by
  have := length_foldl_push (L := LW s r x) (N := NW x) x (List.range (LW s r x))
  unfold UW; simpa using this

/-! ### Words of structures -/

/-- An entry of a flattened list of lists, by block and offset. -/
theorem getD_flatten : ∀ (bl : List (List ℕ)) (i q : ℕ), i < bl.length →
    q < (bl.getD i []).length →
    bl.flatten.getD ((bl.take i).flatten.length + q) 0 = (bl.getD i []).getD q 0
  | [], _, _, h, _ => absurd h (by simp)
  | b :: bl, 0, q, _, hq => by
    simp only [List.getD_cons_zero] at hq
    simp [List.flatten_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left hq]
  | b :: bl, i + 1, q, hi, hq => by
    simp only [List.getD_cons_succ] at hq ⊢
    simp only [List.take_succ_cons, List.flatten_cons, List.length_append]
    rw [List.getD_eq_getElem?_getD, Nat.add_assoc, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    exact getD_flatten bl i q (by simpa using hi) hq

/-- The tuples of a block of tuples of one length `l`, by index and offset. -/
theorem getD_flatten_uniform {ts : List (List ℕ)} {l : ℕ} (h : ∀ t ∈ ts, t.length = l)
    {t q : ℕ} (ht : t < ts.length) (hq : q < l) :
    ts.flatten.getD (t * l + q) 0 = (ts.getD t []).getD q 0 := by
  have hlen : (ts.take t).flatten.length = t * l := by
    rw [length_flatten_of_forall (a := l) fun u hu => h u (List.mem_of_mem_take hu)]
    simp; omega
  rw [← hlen]
  refine getD_flatten ts t q ht ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  simp [h _ (List.getElem_mem ht), hq]

theorem getD_last_append (l : List ℕ) (k : ℕ) : (l ++ [k]).getD ((l ++ [k]).length - 1) 0 = k := by
  rw [List.getD_eq_getElem?_getD, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getElem?_append_right le_rfl, Nat.sub_self]; rfl

theorem len_flatten_take_le (bl : List (List ℕ)) (n : ℕ) :
    (bl.take n).flatten.length ≤ bl.flatten.length := by
  have := congrArg (fun l : List (List ℕ) => l.flatten.length) (List.take_append_drop n bl)
  simp only [List.flatten_append, List.length_append] at this; omega

theorem len_flatten_take_succ {bl : List (List ℕ)} {i : ℕ} (hbl : i < bl.length) :
    (bl.take (i + 1)).flatten.length = (bl.take i).flatten.length + (bl.getD i []).length := by
  rw [List.take_add_one, List.flatten_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]

/-- The data of an encoding, as used below. -/
structure Enc (x : List ℕ) (A : Structure) (k : ℕ) (bl : List (List ℕ)) : Prop where
  len : bl.length = A.arities.length
  rel : ∀ i < A.arities.length, EncodesRel (A.rel i) (bl.getD i [])
  eq : x = (A.arities.length :: (A.arities ++ A.size :: bl.flatten)) ++ [k]

theorem exists_enc {x : List ℕ} {A : Structure} {k : ℕ} (h : EncodesWD x A k) :
    ∃ bl, Enc x A k bl := by
  obtain ⟨y, ⟨bl, h1, h2, rfl⟩, rfl⟩ := h
  exact ⟨bl, h1, h2, rfl⟩

section Enc
variable {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl)
include he

theorem Enc.getD_pre {j : ℕ} (hj : j < 2 + A.arities.length) :
    x.getD j 0 = (A.arities.length :: (A.arities ++ [A.size])).getD j 0 := by
  rw [he.eq]
  have : (A.arities.length :: (A.arities ++ A.size :: bl.flatten)) ++ [k] =
      (A.arities.length :: (A.arities ++ [A.size])) ++ (bl.flatten ++ [k]) := by simp
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
    ← List.getD_eq_getElem?_getD]

theorem Enc.spW_eq : spW x = A.arities.length := by
  unfold Word.spW; rw [he.getD_pre (by omega)]; rfl

theorem Enc.arity {i : ℕ} (hi : i < A.arities.length) :
    x.getD (1 + i) 0 = A.arities.getD i 0 := by
  rw [he.getD_pre (by omega), Nat.add_comm, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem Enc.NW_eq : NW x = A.size := by
  unfold Word.NW; rw [he.spW_eq, he.getD_pre (by omega), Nat.add_comm, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem Enc.kW_eq : kW x = k := by
  unfold Word.kW; rw [he.eq]; exact getD_last_append _ k

/-- The entries of the blocks. -/
theorem Enc.getD_blocks {j : ℕ} (hj : j < bl.flatten.length) :
    x.getD (2 + A.arities.length + j) 0 = bl.flatten.getD j 0 := by
  rw [he.eq]
  have : (A.arities.length :: (A.arities ++ A.size :: bl.flatten)) ++ [k] =
      (A.arities.length :: (A.arities ++ [A.size])) ++ (bl.flatten ++ [k]) := by simp
  have hl : (A.arities.length :: (A.arities ++ [A.size])).length = 2 + A.arities.length := by
    simp; omega
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl,
    Nat.add_sub_cancel_left, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]

/-- The shape of a block: its count, then its tuples. -/
theorem Enc.block (i : ℕ) (hi : i < A.arities.length) :
    ∃ ts : List (List ℕ), ts.Nodup ∧ ts.toFinset = A.rel i ∧ bl.getD i [] = ts.length :: ts.flatten ∧
      ∀ t ∈ ts, t.length = A.arities.getD i 0 := by
  obtain ⟨ts, hnd, hts, hb⟩ := he.rel i hi
  exact ⟨ts, hnd, hts, hb, fun t ht =>
    length_of_mem_rel A (by rw [← hts]; exact List.mem_toFinset.mpr ht)⟩

/-- The length of a block. -/
theorem Enc.length_block (i : ℕ) (hi : i < A.arities.length) :
    (bl.getD i []).length = 1 + (bl.getD i []).getD 0 0 * A.arities.getD i 0 := by
  obtain ⟨ts, -, -, hb, hl⟩ := he.block i hi
  rw [hb, List.length_cons, length_flatten_of_forall hl]; simp; omega

/-- **The position of the block of symbol `i`.** -/
theorem Enc.boW_eq : ∀ i ≤ A.arities.length,
    boW x i = 2 + A.arities.length + (bl.take i).flatten.length
  | 0, _ => by simp [Word.boW, he.spW_eq]
  | i + 1, hi => by
    have hi' : i < A.arities.length := by omega
    have hbl : i < bl.length := by rw [he.len]; exact hi'
    have ih := Enc.boW_eq i (by omega)
    have hblk := he.length_block i hi'
    have hpos : 0 < (bl.getD i []).length := by omega
    have hflat : (bl.take i).flatten.length < bl.flatten.length := by
      have h2 := len_flatten_take_succ hbl
      have h3 := len_flatten_take_le bl (i + 1)
      omega
    have hc : x.getD (boW x i) 0 = (bl.getD i []).getD 0 0 := by
      have h0 := getD_flatten bl i 0 hbl hpos
      rw [Nat.add_zero] at h0
      rw [ih, he.getD_blocks hflat, h0]
    simp only [Word.boW]
    rw [hc, he.arity hi', ih]
    rw [len_flatten_take_succ hbl, hblk]; ring

/-- An entry of the block of symbol `i`. -/
theorem Enc.getD_boW {i q : ℕ} (hi : i < A.arities.length) (hq : q < (bl.getD i []).length) :
    x.getD (boW x i + q) 0 = (bl.getD i []).getD q 0 := by
  have hbl : i < bl.length := by rw [he.len]; exact hi
  have hflat : (bl.take i).flatten.length + q < bl.flatten.length := by
    have h2 := len_flatten_take_succ hbl
    have h3 := len_flatten_take_le bl (i + 1)
    omega
  rw [he.boW_eq i hi.le, Nat.add_assoc, he.getD_blocks hflat, getD_flatten bl i q hbl hq]

/-- **Membership by scanning the block.** -/
theorem Enc.memW_iff {i : ℕ} (hi : i < A.arities.length) {tup : List ℕ}
    (hl : tup.length = A.arities.getD i 0) : memW x i tup ↔ tup ∈ A.rel i := by
  obtain ⟨ts, hnd, hts, hb, htl⟩ := he.block i hi
  have hlen : (bl.getD i []).length = 1 + ts.length * A.arities.getD i 0 := by
    rw [hb, List.length_cons, length_flatten_of_forall htl]; omega
  have hcnt : x.getD (boW x i) 0 = ts.length := by
    have := he.getD_boW hi (q := 0) (by omega)
    rw [Nat.add_zero] at this; rw [this, hb]; rfl
  have hent : ∀ t < ts.length, ∀ q < tup.length,
      x.getD (boW x i + 1 + t * tup.length + q) 0 = (ts.getD t []).getD q 0 := by
    intro t ht q hq
    have hpos : 1 + (t * tup.length + q) < (bl.getD i []).length := by
      rw [hlen, ← hl]
      have : t * tup.length + q < ts.length * tup.length := by
        have := Nat.mul_le_mul_right tup.length (show t + 1 ≤ ts.length by omega)
        rw [Nat.succ_mul] at this; omega
      omega
    rw [show boW x i + 1 + t * tup.length + q = boW x i + (1 + (t * tup.length + q)) by ring,
      he.getD_boW hi hpos, hb, Nat.add_comm, List.getD_cons_succ,
      getD_flatten_uniform (fun u hu => by rw [htl u hu, hl]) ht (by omega)]
  unfold memW
  rw [hcnt, ← hts, List.mem_toFinset]
  constructor
  · rintro ⟨t, ht, h⟩
    have hmem : ts.getD t [] ∈ ts := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
    have htlen : (ts.getD t []).length = tup.length := by rw [htl _ hmem, hl]
    have : ts.getD t [] = tup := by
      refine List.ext_getElem htlen fun q h1 h2 => ?_
      have e1 := (hent t ht q h2).symm.trans (h q h2)
      rw [List.getD_eq_getElem?_getD (l := ts.getD t []), List.getElem?_eq_getElem h1,
        List.getD_eq_getElem?_getD (l := tup), List.getElem?_eq_getElem h2,
        Option.getD_some, Option.getD_some] at e1
      exact e1
    rw [← this]; exact hmem
  · intro hmem
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hmem
    refine ⟨t, ht, fun q hq => ?_⟩
    rw [hent t ht q hq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- **Every active element is an entry of the word.** -/
theorem Enc.mem_of_active {e : ℕ} (h : Active A e) : e ∈ x := by
  obtain ⟨i, t, ht, he'⟩ := h
  have hi : i < A.arities.length := (A.wf i t ht).1
  obtain ⟨ts, -, hts, hb, -⟩ := he.block i hi
  have htm : t ∈ ts := by rw [← hts] at ht; exact List.mem_toFinset.mp ht
  have hbl : i < bl.length := by rw [he.len]; exact hi
  have hbm : bl.getD i [] ∈ bl := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]; exact List.getElem_mem hbl
  rw [he.eq]
  refine List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, hbm, ?_⟩))))
  rw [hb]
  exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨t, htm, he'⟩)

end Enc

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
