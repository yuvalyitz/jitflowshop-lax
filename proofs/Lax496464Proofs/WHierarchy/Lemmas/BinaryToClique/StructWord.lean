import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
import Lax496464.WH_B3_LogicProblems
import Lax496464Proofs.WHierarchy.Logic.StructureCode

/-!
# Σ₁[2] model checking to Clique: reading the structure off the word

For a word `x = y ++ rest` with `y` an encoding of the structure `A`: the number of symbols, the
arities and the size are where the header says; the header walk `hp` finds the start of every
block and ends at the end of `y`; the scan `memX` of the block of a symbol of arity one or two
decides membership of a tuple in its relation; every tuple entry is an entry of the word.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.StructWord

open Lax496464.WH_B1_Structures
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs

theorem rd_append_left {y rest : List ℕ} {i : ℕ} (h : i < y.length) :
    rd (y ++ rest) i = y.getD i 0 := by
  unfold rd
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_add (x : List ℕ) (p j : ℕ) : rd x (p + j) = (x.drop p).getD j 0 := by
  unfold rd
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_append_left' {l l' : List ℕ} {j : ℕ} (h : j < l.length) :
    (l ++ l').getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem length_flatten_of_forall {ts : List (List ℕ)} {a : ℕ} (h : ∀ t ∈ ts, t.length = a) :
    ts.flatten.length = ts.length * a :=
  Lax496464Proofs.WHierarchy.Logic.StructureCode.length_flatten_of_forall h

/-- Indexing the flattening of tuples of one length. -/
theorem getD_flatten_mul : ∀ {ts : List (List ℕ)} {a : ℕ}, (∀ t ∈ ts, t.length = a) →
    ∀ {t j : ℕ}, t < ts.length → j < a → ts.flatten.getD (t * a + j) 0 = (ts.getD t []).getD j 0
  | [], _, _, _, _, ht, _ => absurd ht (Nat.not_lt_zero _)
  | u :: ts, a, h, 0, j, _, hj => by
    simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
    exact getD_append_left' (by rw [h u (by simp)]; exact hj)
  | u :: ts, a, h, t + 1, j, ht, hj => by
    simp only [List.flatten_cons, List.getD_cons_succ]
    have hu : u.length = a := h u (by simp)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hu]; nlinarith),
      ← List.getD_eq_getElem?_getD, hu, show (t + 1) * a + j - a = t * a + j by
        rw [Nat.add_mul, Nat.one_mul]; omega]
    exact getD_flatten_mul (fun v hv => h v (by simp [hv])) (by simp at ht; omega) hj

theorem length_flatten_take_le (l : List (List ℕ)) (i : ℕ) :
    (l.take i).flatten.length ≤ l.flatten.length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatten_append, List.length_append]; omega

theorem length_le_of_mem {l : List (List ℕ)} {t : List ℕ} (h : t ∈ l) :
    t.length ≤ l.flatten.length := by
  induction l with
  | nil => simp at h
  | cons u l ih =>
    rw [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

section

variable {x y rest : List ℕ} {A : Structure} {blocks : List (List ℕ)}

/-- The hypotheses: `x = y ++ rest`, and `y` encodes `A` with these blocks. -/
structure SW (x y rest : List ℕ) (A : Structure) (blocks : List (List ℕ)) : Prop where
  hx : x = y ++ rest
  hbl : blocks.length = A.arities.length
  hrel : ∀ i < A.arities.length, EncodesRel (A.rel i) (blocks.getD i [])
  hy : y = A.arities.length :: (A.arities ++ A.size :: blocks.flatten)

theorem SW.of_encodes (h : Encodes y A) : ∃ blocks, SW (y ++ rest) y rest A blocks := by
  obtain ⟨bl, h1, h2, h3⟩ := h
  exact ⟨bl, rfl, h1, h2, h3⟩

theorem SW.length_y (h : SW x y rest A blocks) :
    y.length = 2 + A.arities.length + blocks.flatten.length := by
  rw [h.hy]; simp; omega

theorem SW.length_le (h : SW x y rest A blocks) : y.length ≤ x.length := by
  rw [h.hx]; simp

theorem SW.sX_eq (h : SW x y rest A blocks) : sX x = A.arities.length := by
  unfold sX
  rw [h.hx, rd_append_left (by rw [h.hy]; simp), h.hy]; rfl

theorem SW.rd_arity (h : SW x y rest A blocks) {i : ℕ} (hi : i < A.arities.length) :
    rd x (1 + i) = A.arities.getD i 0 := by
  rw [h.hx, rd_append_left (by rw [h.length_y]; omega), h.hy]
  rw [Nat.add_comm, List.getD_cons_succ, getD_append_left' hi]

theorem SW.NsX_eq (h : SW x y rest A blocks) : NsX x = A.size := by
  unfold NsX
  rw [h.sX_eq, h.hx, rd_append_left (by rw [h.length_y]; omega), h.hy, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

/-- The block `i`: its count and its tuples. -/
theorem SW.block (h : SW x y rest A blocks) {i : ℕ} (hi : i < A.arities.length) :
    ∃ ts : List (List ℕ), ts.Nodup ∧ ts.toFinset = A.rel i ∧
      blocks.getD i [] = ts.length :: ts.flatten ∧
      ∀ t ∈ ts, t.length = A.arities.getD i 0 := by
  obtain ⟨ts, hnd, hts, hb⟩ := h.hrel i hi
  refine ⟨ts, hnd, hts, hb, fun t ht => ?_⟩
  exact (A.wf i t (by rw [← hts]; exact List.mem_toFinset.2 ht)).2.1

theorem SW.length_block (h : SW x y rest A blocks) {i : ℕ} (hi : i < A.arities.length) :
    (blocks.getD i []).length = 1 + (blocks.getD i []).headD 0 * A.arities.getD i 0 := by
  obtain ⟨ts, -, -, hb, hlen⟩ := h.block hi
  rw [hb, List.length_cons, List.headD_cons, length_flatten_of_forall hlen]; ring

theorem drop_y (h : SW x y rest A blocks) (i : ℕ) :
    y.drop (2 + A.arities.length + (blocks.take i).flatten.length) = (blocks.drop i).flatten := by
  rw [h.hy]
  have e : A.arities.length :: (A.arities ++ A.size :: blocks.flatten) =
      (A.arities.length :: A.arities ++ [A.size] ++ (blocks.take i).flatten) ++
        (blocks.drop i).flatten := by
    conv_lhs => rw [← List.take_append_drop i blocks, List.flatten_append]
    simp
  rw [e, List.drop_append_of_le_length (by simp; omega)]
  rw [List.drop_eq_nil_of_le (by simp; omega), List.nil_append]

/-- **The header walk finds the blocks.** -/
theorem SW.hp_eq (h : SW x y rest A blocks) :
    ∀ i ≤ A.arities.length, hp x i = 2 + A.arities.length + (blocks.take i).flatten.length
  | 0, _ => by
    have hl := h.length_y
    have hle := h.length_le
    simp only [hp, hp0, h.sX_eq, List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]; omega
  | i + 1, hi => by
    have ih := SW.hp_eq h i (by omega)
    have hil : i < blocks.length := by rw [h.hbl]; omega
    have htake : blocks.take (i + 1) = blocks.take i ++ [blocks.getD i []] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]; simp
    have hlenT : (blocks.take (i + 1)).flatten.length =
        (blocks.take i).flatten.length + (blocks.getD i []).length := by
      rw [htake]; simp
    have hdrop : blocks.drop i = blocks.getD i [] :: blocks.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
      rfl
    -- the count
    have hcount : rd x (hp x i) = (blocks.getD i []).headD 0 := by
      rw [ih, h.hx, show 2 + A.arities.length + (blocks.take i).flatten.length =
        2 + A.arities.length + (blocks.take i).flatten.length + 0 by rfl, rd_add,
        List.drop_append_of_le_length (by
          rw [h.length_y]
          have := length_flatten_take_le blocks i
          omega),
        drop_y h i, hdrop, List.flatten_cons]
      obtain ⟨ts, -, -, hb, -⟩ := h.block (show i < A.arities.length by omega)
      rw [hb]; simp
    have hlen := h.length_block (show i < A.arities.length by omega)
    have hbound : 2 + A.arities.length + (blocks.take (i + 1)).flatten.length ≤ x.length := by
      have := length_flatten_take_le blocks (i + 1)
      have := h.length_y; have := h.length_le; omega
    simp only [hp, hpStep]
    rw [hcount, h.rd_arity (by omega), ih]
    rw [if_neg (by omega)]
    omega

theorem SW.hp_last (h : SW x y rest A blocks) : hp x A.arities.length = y.length := by
  rw [h.hp_eq _ le_rfl, h.length_y, ← h.hbl, List.take_length]

/-- The entries of block `i`, read from the word. -/
theorem SW.rd_block (h : SW x y rest A blocks) {i : ℕ} (hi : i < A.arities.length) {j : ℕ}
    (hj : j < (blocks.getD i []).length) : rd x (hp x i + j) = (blocks.getD i []).getD j 0 := by
  have hil : i < blocks.length := by rw [h.hbl]; exact hi
  have hdrop : blocks.drop i = blocks.getD i [] :: blocks.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
    rfl
  rw [h.hp_eq i hi.le, rd_add, h.hx, List.drop_append_of_le_length (by
      rw [h.length_y]
      have := length_flatten_take_le blocks i
      omega),
    drop_y h i, hdrop, List.flatten_cons, List.append_assoc, getD_append_left' hj]

/-- **The scan decides membership**, for a symbol of arity one or two. -/
theorem SW.memX_iff (h : SW x y rest A blocks) {i : ℕ} (hi : i < A.arities.length)
    (ha : A.arities.getD i 0 = 1 ∨ A.arities.getD i 0 = 2) (w1 w2 : ℕ) :
    memX x (hp x i) (A.arities.getD i 0) w1 w2 = true ↔
      (if A.arities.getD i 0 = 1 then [w1] else [w1, w2]) ∈ A.rel i := by
  obtain ⟨ts, hnd, hts, hb, hlen⟩ := h.block hi
  set a := A.arities.getD i 0 with hadef
  have hrdb : ∀ j < (blocks.getD i []).length, rd x (hp x i + j) = (blocks.getD i []).getD j 0 :=
    fun j hj => h.rd_block hi hj
  have hbl : (blocks.getD i []).length = 1 + ts.length * a := by
    rw [hb, List.length_cons, length_flatten_of_forall hlen]; ring
  have hcnt : cntX x (hp x i) = ts.length := by
    have h0 := hrdb 0 (by omega)
    rw [Nat.add_zero, hb] at h0
    simp only [List.getD_cons_zero] at h0
    have hle : ts.length ≤ x.length := by
      have h1 := h.length_le
      have h2 := h.length_y
      have h3 : (blocks.getD i []).length ≤ blocks.flatten.length := by
        have hil : i < blocks.length := by rw [h.hbl]; exact hi
        rw [List.getD_eq_getElem _ _ hil]
        exact length_le_of_mem (List.getElem_mem hil)
      have : ts.length ≤ (blocks.getD i []).length := by
        rw [hbl]; rcases ha with ha | ha <;> rw [ha] <;> omega
      omega
    unfold cntX; rw [h0, if_neg (by omega)]
  -- entries of tuple `t`
  have hent : ∀ t < ts.length, ∀ j < a, rd x (hp x i + 1 + t * a + j) = (ts.getD t []).getD j 0 := by
    intro t ht j hj
    have hlt : t * a + j < ts.length * a := by
      have : (t + 1) * a ≤ ts.length * a := Nat.mul_le_mul_right _ ht
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    rw [show hp x i + 1 + t * a + j = hp x i + (1 + (t * a + j)) by ring,
      hrdb _ (by rw [hbl]; omega), hb, Nat.add_comm, List.getD_cons_succ]
    exact getD_flatten_mul hlen ht hj
  unfold memX memN
  rw [hcnt, ← hts, List.mem_toFinset]
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨t, ht, hhit⟩
    have htl : (ts.getD t []).length = a := hlen _ (by
      rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
    have hmem : ts.getD t [] ∈ ts := by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
    unfold tupHit at hhit
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hhit
    obtain ⟨h1, h2⟩ := hhit
    rw [show hp x i + 1 + t * a = hp x i + 1 + t * a + 0 by rfl,
      hent t ht 0 (by rcases ha with ha | ha <;> omega)] at h1
    rcases ha with ha | ha
    · rw [if_pos ha]
      obtain ⟨u, hu⟩ : ∃ u, ts.getD t [] = [u] := by
        match ts.getD t [], htl with
        | [u], _ => exact ⟨u, rfl⟩
        | [], htl' => simp at htl'; omega
        | _ :: _ :: _, htl' => simp at htl'; omega
      rw [hu] at h1 hmem
      simp only [List.getD_cons_zero] at h1
      rw [← h1]; exact hmem
    · rw [if_neg (by omega)]
      rcases h2 with h2 | h2
      · exact absurd h2 (by omega)
      rw [hent t ht 1 (by omega)] at h2
      obtain ⟨u, v, hu⟩ : ∃ u v, ts.getD t [] = [u, v] := by
        match ts.getD t [], htl with
        | [u, v], _ => exact ⟨u, v, rfl⟩
        | [], htl' => simp at htl'; omega
        | [_], htl' => simp at htl'; omega
        | _ :: _ :: _ :: _, htl' => simp at htl'; omega
      rw [hu] at h1 h2 hmem
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
      rw [← h1, ← h2]; exact hmem
  · intro hmem
    obtain ⟨t, ht, htq⟩ := List.getElem_of_mem hmem
    refine ⟨t, ht, ?_⟩
    have hq : ts.getD t [] = (if a = 1 then [w1] else [w1, w2]) := by
      rw [List.getD_eq_getElem _ _ ht, htq]
    unfold tupHit
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    rw [show hp x i + 1 + t * a = hp x i + 1 + t * a + 0 by rfl,
      hent t ht 0 (by rcases ha with ha | ha <;> omega), hq]
    rcases ha with ha | ha
    · rw [if_pos ha]; simp [ha]
    · rw [if_neg (by omega)]
      refine ⟨by simp, Or.inr ?_⟩
      rw [hent t ht 1 (by omega), hq, if_neg (by omega)]; simp

/-- Every tuple entry is an entry of the word. -/
theorem SW.mem_of_tuple (h : SW x y rest A blocks) {i : ℕ} {t : List ℕ} (ht : t ∈ A.rel i)
    {a : ℕ} (ha : a ∈ t) : a ∈ x := by
  have hi : i < A.arities.length := (A.wf i t ht).1
  obtain ⟨ts, -, hts, hb, -⟩ := h.block hi
  have hil : i < blocks.length := by rw [h.hbl]; exact hi
  have htm : t ∈ ts := by rw [← hts] at ht; exact List.mem_toFinset.1 ht
  have hblk : blocks.getD i [] ∈ blocks := by
    rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil
  have hab : a ∈ blocks.getD i [] := by
    rw [hb]; exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨t, htm, ha⟩)
  rw [h.hx, h.hy]
  simp only [List.cons_append, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (Or.inr (Or.inr (List.mem_flatten.2 ⟨_, hblk, hab⟩))))

end

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.StructWord
