import Lax496464Proofs.WHierarchy.Logic.StructureCode
import Mathlib.Tactic.Ring

/-! # Reading a structure off its word

The functions below read, from a word `x` that begins with the word of a structure `A`, the
number of symbols, the size, the arities, and the tuples in the order in which `x` lists them: the block of
symbol `i` begins at position `bo x i`, and entry `l` of its tuple `j` is at
`bo x i + 1 + j · arity i + l`. `parse` says that these are the data of `A`, and that the blocks end
where the rest of the word begins. (The same reading as `Lemmas/Incidence/Parse.lean`, kept
separate so that the two lemmas do not depend on each other.) -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse

open Lax496464.WH_B1_Structures Lax496464Proofs.WHierarchy.Logic.StructureCode

/-- The number of symbols. -/
def sOf (x : List ℕ) : ℕ := x.getD 0 0

/-- The arity of symbol `i`. -/
def arOf (x : List ℕ) (i : ℕ) : ℕ := x.getD (1 + i) 0

/-- The size of the universe. -/
def nOf (x : List ℕ) : ℕ := x.getD (1 + sOf x) 0

/-- The position of the block of symbol `i`. -/
def bo (x : List ℕ) : ℕ → ℕ
  | 0 => 2 + sOf x
  | i + 1 => bo x i + 1 + x.getD (bo x i) 0 * arOf x i

/-- The number of tuples of symbol `i`. -/
def cntOf (x : List ℕ) (i : ℕ) : ℕ := x.getD (bo x i) 0

/-- Entry `l` of tuple `j` of symbol `i`. -/
def entOf (x : List ℕ) (i j l : ℕ) : ℕ := x.getD (bo x i + 1 + j * arOf x i + l) 0

/-- The largest entry of a word. -/
def maxEntry (x : List ℕ) : ℕ := x.foldr max 0

/-- The tuples of symbol `i`, as the word lists them. -/
def listOf (x : List ℕ) (i : ℕ) : List (List ℕ) :=
  (List.range (cntOf x i)).map fun j => (List.range (arOf x i)).map (entOf x i j)

theorem le_maxEntry {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ maxEntry x := by
  induction x with
  | nil => simp at h
  | cons a x ih =>
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem getD_drop (x : List ℕ) (k m : ℕ) : (x.drop k).getD m 0 = x.getD (k + m) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j · a + l` of a list of tuples of length `a`. -/
theorem flatten_getD : ∀ {ts : List (List ℕ)} {a j l : ℕ}, (∀ t ∈ ts, t.length = a) →
    j < ts.length → l < a → ts.flatten.getD (j * a + l) 0 = (ts.getD j []).getD l 0
  | [], _, _, _, _, hj, _ => by simp at hj
  | t :: ts, a, 0, l, h, _, hl => by
    have ht := h t (by simp)
    simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  | t :: ts, a, j + 1, l, h, hj, hl => by
    have ht := h t (by simp)
    simp only [List.flatten_cons, List.getD_cons_succ]
    rw [← flatten_getD (fun u hu => h u (by simp [hu])) (by simpa using hj) hl]
    have e1 : (j + 1) * a + l = j * a + l + a := by rw [Nat.succ_mul]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [e1, List.getElem?_append_right (by omega), ht, Nat.add_sub_cancel]

section Parse

variable {x y rest : List ℕ} {A : Structure}

theorem take_flatten_succ (bl : List (List ℕ)) {i : ℕ} (hi : i < bl.length) :
    (bl.take (i + 1)).flatten = (bl.take i).flatten ++ bl.getD i [] := by
  rw [List.take_add_one, List.flatten_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem drop_flatten_eq (bl : List (List ℕ)) {i : ℕ} (hi : i < bl.length) :
    (bl.drop i).flatten = bl.getD i [] ++ (bl.drop (i + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hi, List.flatten_cons, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-- The word, cut at the start of block `i`. -/
theorem drop_bo_aux (bl : List (List ℕ)) (hx : x = A.arities.length ::
    (A.arities ++ A.size :: bl.flatten) ++ rest) (i : ℕ) :
    x.drop (2 + A.arities.length + ((bl.take i).flatten).length) =
      (bl.drop i).flatten ++ rest := by
  subst hx
  have : bl.flatten = (bl.take i).flatten ++ (bl.drop i).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [this]
  simp only [List.cons_append, List.append_assoc]
  rw [show 2 + A.arities.length + ((bl.take i).flatten).length =
    1 + (A.arities.length + (1 + ((bl.take i).flatten).length)) by omega]
  rw [← List.drop_drop, List.drop_one, List.tail_cons, ← List.drop_drop,
    List.drop_left, ← List.drop_drop, List.drop_one, List.tail_cons, List.drop_left]

/-- **Reading the word of a structure.** -/
theorem parse (hy : Encodes y A) (hx : x = y ++ rest) :
    sOf x = A.arities.length ∧ nOf x = A.size ∧
      (∀ i < sOf x, arOf x i = A.arities.getD i 0) ∧
      (∀ i < sOf x, (listOf x i).Nodup ∧ (listOf x i).toFinset = A.rel i) ∧
      bo x (sOf x) = y.length := by
  obtain ⟨bl, hbl, hrel, rfl⟩ := hy
  have hx' : x = A.arities.length :: (A.arities ++ A.size :: bl.flatten) ++ rest := by
    rw [hx]
  have hs : sOf x = A.arities.length := by rw [hx']; rfl
  have har : ∀ i < A.arities.length, arOf x i = A.arities.getD i 0 := by
    intro i hi
    rw [arOf, hx']
    simp only [List.cons_append, List.getD_eq_getElem?_getD]
    rw [show 1 + i = i + 1 by omega, List.getElem?_cons_succ, List.append_assoc,
      List.getElem?_append_left hi]
  have hN : nOf x = A.size := by
    rw [nOf, hs, hx']
    simp only [List.cons_append, List.getD_eq_getElem?_getD]
    rw [show 1 + A.arities.length = A.arities.length + 1 by omega, List.getElem?_cons_succ,
      List.append_assoc, List.getElem?_append_right le_rfl]
    simp
  -- the positions of the blocks
  have hshape := blockShape_of_encodes hrel
  have hbo : ∀ i ≤ A.arities.length,
      bo x i = 2 + A.arities.length + ((bl.take i).flatten).length := by
    intro i
    induction i with
    | zero => intro _; simp [bo, hs]
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hib : i < bl.length := by omega
      have hd := drop_bo_aux bl hx' i
      rw [← ih', drop_flatten_eq bl hib] at hd
      obtain ⟨c, rest', hblk, hlen⟩ := hshape i (by omega)
      have hc : x.getD (bo x i) 0 = c := by
        rw [← Nat.add_zero (bo x i), ← getD_drop, hd, hblk]; rfl
      rw [bo, hc, ih', take_flatten_succ bl hib, List.length_append, hblk, List.length_cons,
        hlen, har i (by omega)]
      ring
  refine ⟨hs, hN, fun i hi => har i (by omega), fun i hi => ?_, ?_⟩
  · rw [hs] at hi
    obtain ⟨ts, hnd, hts, hb⟩ := hrel i hi
    have hlen : ∀ t ∈ ts, t.length = A.arities.getD i 0 := fun t ht =>
      length_of_mem_rel A (by rw [← hts]; exact List.mem_toFinset.mpr ht)
    have hib : i < bl.length := by omega
    have hd := drop_bo_aux bl hx' i
    rw [← hbo i hi.le, drop_flatten_eq bl hib, hb] at hd
    have hcnt : cntOf x i = ts.length := by
      rw [cntOf, ← Nat.add_zero (bo x i), ← getD_drop, hd]; rfl
    have hlist : listOf x i = ts := by
      apply List.ext_getElem
      · simp [listOf, hcnt]
      · intro j h1 h2
        simp only [listOf, List.getElem_map, List.getElem_range]
        have hj : j < ts.length := h2
        have hlj := hlen _ (List.getElem_mem hj)
        apply List.ext_getElem
        · simp [har i hi, hlj]
        · intro l h3 h4
          simp only [List.getElem_map, List.getElem_range]
          have hl : l < A.arities.getD i 0 := by simp [har i hi] at h3; exact h3
          have hlt : j * A.arities.getD i 0 + l < ts.flatten.length := by
            rw [length_flatten_of_forall hlen]
            have : (j + 1) * A.arities.getD i 0 ≤ ts.length * A.arities.getD i 0 :=
              Nat.mul_le_mul_right _ hj
            rw [Nat.succ_mul] at this; omega
          have hfl := flatten_getD hlen hj hl
          rw [entOf, har i hi]
          generalize A.arities.getD i 0 = a at hl hlen hlt hfl ⊢
          rw [show bo x i + 1 + j * a + l = bo x i + ((j * a + l) + 1) by omega, ← getD_drop, hd]
          rw [List.getD_eq_getElem?_getD]
          simp only [List.cons_append, List.getElem?_cons_succ, List.append_assoc]
          rw [List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD, hfl]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
            List.getElem?_eq_getElem h4]
    rw [hlist]
    exact ⟨hnd, hts⟩
  · rw [hs, hbo _ le_rfl, List.take_of_length_le (by omega)]
    simp; omega

end Parse

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse
