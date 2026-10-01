import Lax496464Proofs.WHierarchy.Logic.Words
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The parameter of a model-checking word, computed by a scan: mathematics

A model-checking word is `s, arities, size, blocks, formula`. The blocks are skipped with the
header (block `i` is `c_i` followed by `c_i · arity_i` entries), and the size of the formula is the
sum, over the tags of its prefix code, of a contribution read off the tag and at most the two
entries after it. This file states both facts in the terms the program uses: positions in the word
and the entries at them.
-/

namespace Lax496464Proofs.WHierarchy.Logic.McParam.Math

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.StructureCode Lax496464Proofs.WHierarchy.Logic.Words

/-! ### Decoding a model-checking word -/

/-- A model-checking word, taken apart. -/
structure Dec where
  A : Structure
  φ : Formula
  bl : List (List ℕ)
  hbl : bl.length = A.arities.length
  hrel : ∀ i < A.arities.length, EncodesRel (A.rel i) (bl.getD i [])

namespace Dec

variable (D : Dec)

/-- The word. -/
def word : List ℕ := D.A.arities.length :: (D.A.arities ++ D.A.size :: D.bl.flatten) ++ D.φ.encode

/-- Every model-checking word can be taken apart. -/
theorem exists_of {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    ∃ D : Dec, x = D.word ∧ D.A = A ∧ D.φ = φ := by
  obtain ⟨y, ⟨bl, hbl, hrel, rfl⟩, rfl⟩ := h
  exact ⟨⟨A, φ, bl, hbl, hrel⟩, rfl, rfl, rfl⟩

/-- The number of symbols. -/
def s : ℕ := D.A.arities.length

/-- The arity of symbol `i`. -/
def ar (i : ℕ) : ℕ := D.A.arities.getD i 0

/-- The number of tuples of symbol `i`, as written. -/
def cnt (i : ℕ) : ℕ := (D.bl.getD i []).headD 0

/-- The total length of the first `i` blocks. -/
def pre (i : ℕ) : ℕ := ((D.bl.take i).map List.length).sum

/-- The position where the formula begins. -/
def start : ℕ := D.s + 2 + D.pre D.s

theorem encodesMC : EncodesMC D.word D.A D.φ := ⟨_, ⟨D.bl, D.hbl, D.hrel, rfl⟩, rfl⟩

theorem mcParam_eq : mcParam D.word = D.φ.size :=
  Lax496464Proofs.WHierarchy.Logic.Words.mcParam_eq D.encodesMC

theorem blockShape {i : ℕ} (hi : i < D.s) : BlockShape (D.ar i) (D.bl.getD i []) :=
  blockShape_of_encodes D.hrel i hi

theorem length_block {i : ℕ} (hi : i < D.s) :
    (D.bl.getD i []).length = 1 + D.cnt i * D.ar i := by
  obtain ⟨c, rest, hb, hr⟩ := D.blockShape hi
  rw [cnt, hb]; simp [hr]; ring

theorem drop_flatten_append (bl : List (List ℕ)) (r : List ℕ) (i : ℕ) :
    (bl.flatten ++ r).drop ((bl.take i).map List.length).sum = (bl.drop i).flatten ++ r := by
  conv_lhs => rw [← List.take_append_drop i bl]
  rw [List.flatten_append, List.append_assoc, List.drop_left']
  simp [List.length_flatten]

/-- **The rest of the word from the `i`-th block.** -/
theorem drop_pre (i : ℕ) :
    D.word.drop (D.s + 2 + D.pre i) = (D.bl.drop i).flatten ++ D.φ.encode := by
  rw [word, s, pre, show D.A.arities.length + 2 + ((D.bl.take i).map List.length).sum =
    (D.A.arities.length + 2) + ((D.bl.take i).map List.length).sum by ring, ← List.drop_drop]
  have : (D.A.arities.length :: (D.A.arities ++ D.A.size :: D.bl.flatten) ++ D.φ.encode).drop
      (D.A.arities.length + 2) = D.bl.flatten ++ D.φ.encode := by
    simp [List.drop_append]
  rw [this, drop_flatten_append]

theorem getD_eq_of_drop {x l : List ℕ} {p : ℕ} (h : x.drop p = l) (j : ℕ) :
    x.getD (p + j) 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← h, List.getElem?_drop]

theorem getD_cnt {i : ℕ} (hi : i < D.s) : D.word.getD (D.s + 2 + D.pre i) 0 = D.cnt i := by
  have h := getD_eq_of_drop (D.drop_pre i) 0
  rw [Nat.add_zero] at h
  rw [h]
  have hi' : i < D.bl.length := by rw [D.hbl]; exact hi
  rw [List.drop_eq_getElem_cons hi']
  obtain ⟨c, rest, hb, -⟩ := D.blockShape hi
  have e : D.bl[i] = c :: rest := by
    rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  rw [e, cnt, hb]; simp

theorem getD_ar {i : ℕ} (hi : i < D.s) : D.word.getD (1 + i) 0 = D.ar i := by
  have hi' : i < D.A.arities.length := hi
  rw [word, ar, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, show 1 + i = i + 1 by ring]
  simp [List.getElem?_append_left hi']

theorem pre_succ {i : ℕ} (hi : i < D.s) : D.pre (i + 1) = D.pre i + 1 + D.cnt i * D.ar i := by
  have hi' : i < D.bl.length := by rw [D.hbl]; exact hi
  have hl := D.length_block hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at hl
  simp only [Option.getD_some] at hl
  rw [pre, pre, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi']
  simp [hl]
  ring

theorem drop_start : D.word.drop D.start = D.φ.encode := by
  have h := D.drop_pre D.s
  have e : D.bl.drop D.s = [] := List.drop_eq_nil_of_le (by rw [D.hbl]; rfl)
  rw [e, List.flatten_nil, List.nil_append] at h
  exact h

theorem start_eq : D.start + D.φ.encode.length = D.word.length := by
  have hl := congrArg List.length D.drop_start
  rw [List.length_drop] at hl
  have : D.start ≤ D.word.length := by
    by_contra hc
    have : D.word.length - D.start = 0 := by omega
    rw [this] at hl
    have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil D.φ
    exact this (List.eq_nil_of_length_eq_zero hl.symm)
  omega

theorem pre_le {i : ℕ} (hi : i ≤ D.s) : D.pre i ≤ D.pre D.s := by
  unfold pre
  conv_rhs => rw [← List.take_append_drop i (D.bl.take D.s), List.take_take, min_eq_left hi]
  simp

theorem length_encode_pos : 0 < D.φ.encode.length :=
  List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil D.φ)

/-- A block begins strictly before the formula. -/
theorem pos_lt {i : ℕ} (hi : i < D.s) : D.s + 2 + D.pre i < D.word.length := by
  have h1 := D.pre_le (Nat.succ_le_of_lt hi)
  rw [pre_succ D hi] at h1
  have := D.start_eq
  have := D.length_encode_pos
  unfold start at *
  omega

theorem cnt_mul_le {i : ℕ} (hi : i < D.s) : D.cnt i * D.ar i ≤ D.word.length := by
  have h1 := D.pre_le (Nat.succ_le_of_lt hi)
  rw [pre_succ D hi] at h1
  have := D.start_eq
  unfold start at *
  omega

theorem s_lt : D.s + 2 < D.word.length := by
  have h1 := D.start_eq
  have h2 := D.length_encode_pos
  unfold start at h1; omega

end Dec

/-! ### The scan of the formula -/

/-- What a tag `t` adds to the size (`l1`, `l2` are the next two entries). -/
def dAcc (t l1 l2 : ℕ) : ℕ :=
  if t = 0 then l2 + 1 else if t = 1 then l1 + 1 else if t = 2 then 3 else if t < 6 then 1 else 2

/-- How far a tag `t` moves the position. -/
def dP (t l1 l2 : ℕ) : ℕ :=
  if t = 0 then 3 + l2 else if t = 1 then 2 + l1 else if t = 2 then 3 else if t < 6 then 1 else 2

/-- The codes of a list of pending formulas. -/
def pend (fs : List Formula) : List ℕ := (fs.map Formula.encode).flatten

/-- The total size of a list of pending formulas. -/
def psize (fs : List Formula) : ℕ := (fs.map Formula.size).sum

@[simp] theorem pend_nil : pend [] = [] := rfl

@[simp] theorem pend_cons (f : Formula) (fs : List Formula) :
    pend (f :: fs) = f.encode ++ pend fs := rfl

@[simp] theorem psize_nil : psize [] = 0 := rfl

@[simp] theorem psize_cons (f : Formula) (fs : List Formula) :
    psize (f :: fs) = f.size + psize fs := rfl

theorem pend_eq_nil {fs : List Formula} (h : pend fs = []) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    simp only [pend_cons, List.append_eq_nil_iff] at h
    exact absurd h.1 (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f)

theorem getD_of_drop {w l : List ℕ} {p : ℕ} (h : w.drop p = l) (j : ℕ) :
    w.getD (p + j) 0 = l.getD j 0 := Dec.getD_eq_of_drop h j

theorem length_of_drop {w l : List ℕ} {p : ℕ} (h : w.drop p = l) (hl : l ≠ []) :
    p + l.length = w.length := by
  have h1 := congrArg List.length h
  rw [List.length_drop] at h1
  have : p < w.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact hl h.symm
  omega

/-- **One step of the scan.** From a position where the pending formulas `f :: fs` begin, the
tag and the next two entries say how much `f`'s own symbol adds to the size and how far to move;
the pending formulas afterwards are `f`'s subformulas followed by `fs`. -/
theorem scan_step {w : List ℕ} {p : ℕ} {f : Formula} {fs : List Formula}
    (h : w.drop p = pend (f :: fs)) :
    ∃ fs', w.drop (p + dP (w.getD p 0) (w.getD (p + 1) 0) (w.getD (p + 2) 0)) = pend fs' ∧
      dAcc (w.getD p 0) (w.getD (p + 1) 0) (w.getD (p + 2) 0) + psize fs' = f.size + psize fs ∧
      p + dP (w.getD p 0) (w.getD (p + 1) 0) (w.getD (p + 2) 0) + (pend fs').length =
        w.length ∧
      (w.getD p 0 = 0 → p + 2 < w.length) ∧ (w.getD p 0 = 1 → p + 1 < w.length) := by
  have hne : pend (f :: fs) ≠ [] := by
    simp [Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f]
  have hL := length_of_drop h hne
  have g0 := getD_of_drop h 0
  have g1 := getD_of_drop h 1
  have g2 := getD_of_drop h 2
  rw [Nat.add_zero] at g0
  have hd : ∀ j, w.drop (p + j) = (pend (f :: fs)).drop j := fun j => by
    rw [← List.drop_drop, h]
  cases f with
  | rel i xs =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ] at g0 g1 g2 hL
    refine ⟨fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, g2, dP, if_pos rfl, hd]
      show List.drop (3 + xs.length) ([0, i, xs.length] ++ (xs ++ pend fs)) = pend fs
      rw [← List.drop_drop, List.drop_left' (by simp), List.drop_left]
    · rw [g0, g2, dAcc, if_pos rfl]; simp [Formula.size]
    · rw [g0, g2, dP, if_pos rfl]; simp [pend] at hL ⊢; omega
    · intro _; simp [pend] at hL; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | setVar xs =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ] at g0 g1 g2 hL
    refine ⟨fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, g1, dP, if_neg (by norm_num), if_pos rfl, hd]
      show List.drop (2 + xs.length) ([1, xs.length] ++ (xs ++ pend fs)) = pend fs
      rw [← List.drop_drop, List.drop_left' (by simp), List.drop_left]
    · rw [g0, g1, dAcc, if_neg (by norm_num), if_pos rfl]; simp [Formula.size]
    · rw [g0, g1, dP, if_neg (by norm_num), if_pos rfl]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro _; simp [pend] at hL; omega
  | eq a b =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero,
      List.getD_cons_succ] at g0 g1 g2 hL
    refine ⟨fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, hd]
      simp [Formula.encode, pend]
    · rw [g0, dAcc, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]; simp [Formula.size]
    · rw [g0, dP, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | neg φ =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero] at g0 hL
    refine ⟨φ :: fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP]; simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 2 by norm_num, show (3 : ℕ) < 6 by norm_num, if_false, if_true]
      rw [hd]; simp [Formula.encode, pend]
    · rw [g0, dAcc]; simp [Formula.size]; ring
    · rw [g0, dP]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | and φ ψ =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero] at g0 hL
    refine ⟨φ :: ψ :: fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP]; simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num,
        show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) < 6 by norm_num, if_false, if_true]
      rw [hd]; simp [Formula.encode, pend]
    · rw [g0, dAcc]; simp [Formula.size]; ring
    · rw [g0, dP]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | or φ ψ =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero] at g0 hL
    refine ⟨φ :: ψ :: fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP]; simp only [show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num,
        show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) < 6 by norm_num, if_false, if_true]
      rw [hd]; simp [Formula.encode, pend]
    · rw [g0, dAcc]; simp [Formula.size]; ring
    · rw [g0, dP]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | ex x φ =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero] at g0 hL
    refine ⟨φ :: fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP]; simp only [show (6 : ℕ) ≠ 0 by norm_num, show (6 : ℕ) ≠ 1 by norm_num,
        show (6 : ℕ) ≠ 2 by norm_num, show ¬ (6 : ℕ) < 6 by norm_num, if_false]
      rw [hd]; simp [Formula.encode, pend]
    · rw [g0, dAcc]; simp [Formula.size]; ring
    · rw [g0, dP]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
  | all x φ =>
    simp only [pend_cons, Formula.encode, List.cons_append, List.getD_cons_zero] at g0 hL
    refine ⟨φ :: fs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, dP]; simp only [show (7 : ℕ) ≠ 0 by norm_num, show (7 : ℕ) ≠ 1 by norm_num,
        show (7 : ℕ) ≠ 2 by norm_num, show ¬ (7 : ℕ) < 6 by norm_num, if_false]
      rw [hd]; simp [Formula.encode, pend]
    · rw [g0, dAcc]; simp [Formula.size]; ring
    · rw [g0, dP]; simp [pend] at hL ⊢; omega
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)
    · intro h1; rw [g0] at h1; exact absurd h1 (by norm_num)

end Lax496464Proofs.WHierarchy.Logic.McParam.Math
