import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord

/-! # The translation of the formula, as the program produces it

The program walks the prefix code of the formula with a stack of polarities. The pending formulas
(with their polarities) are `fs`; their codes are the rest of the word (`pend fs`) and their
translations, with fresh variables counted from `c` on, are `trL fs c`. One turn of the walk
replaces the first pending formula by its children and writes the part of the translation that
comes before them (`trL_*`). The codes of `lexF` and `negRel` are spelled out the way the program
writes them. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath

open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax

/-- A polarity as a number. -/
def pb (b : Bool) : ℕ := if b then 1 else 0

/-- The codes of the pending formulas. -/
def pend (fs : List (Bool × Formula)) : List ℕ := (fs.map fun f => f.2.encode).flatten

/-- The number of fresh variables of the pending formulas. -/
def cntL (fs : List (Bool × Formula)) : ℕ := (fs.map fun f => cnt f.1 f.2).sum

/-- The translations of the pending formulas. -/
def trL : List (Bool × Formula) → ℕ → List ℕ
  | [], _ => []
  | (p, f) :: fs, c => (tr p f c).encode ++ trL fs (c + cnt p f)

@[simp] theorem pend_cons (f : Bool × Formula) (fs : List (Bool × Formula)) :
    pend (f :: fs) = f.2.encode ++ pend fs := by unfold pend; try rfl
@[simp] theorem cntL_cons (f : Bool × Formula) (fs : List (Bool × Formula)) :
    cntL (f :: fs) = cnt f.1 f.2 + cntL fs := by unfold cntL; try rfl

/-! ### One turn -/

theorem trL_neg (p : Bool) (f : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, .neg f) :: fs) c = trL ((!p, f) :: fs) c := by
  cases p <;> rfl

theorem cntL_neg (p : Bool) (f : Formula) (fs : List (Bool × Formula)) :
    cntL ((p, .neg f) :: fs) = cntL ((!p, f) :: fs) := by
  cases p <;> rfl

theorem trL_and (p : Bool) (f g : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, .and f g) :: fs) c = (if p then 4 else 5) :: trL ((p, f) :: (p, g) :: fs) c := by
  cases p <;> simp [trL, tr, cnt, Formula.encode, Nat.add_assoc]

theorem trL_or (p : Bool) (f g : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, .or f g) :: fs) c = (if p then 5 else 4) :: trL ((p, f) :: (p, g) :: fs) c := by
  cases p <;> simp [trL, tr, cnt, Formula.encode, Nat.add_assoc]

theorem cntL_and (p : Bool) (f g : Formula) (fs : List (Bool × Formula)) :
    cntL ((p, .and f g) :: fs) = cntL ((p, f) :: (p, g) :: fs) := by
  cases p <;> simp [cnt, Nat.add_assoc]

theorem cntL_or (p : Bool) (f g : Formula) (fs : List (Bool × Formula)) :
    cntL ((p, .or f g) :: fs) = cntL ((p, f) :: (p, g) :: fs) := by
  cases p <;> simp [cnt, Nat.add_assoc]

theorem trL_ex (p : Bool) (y : ℕ) (f : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, .ex y f) :: fs) c = 6 :: y :: trL ((p, f) :: fs) c := by
  cases p <;> simp [trL, tr, cnt, Formula.encode]

theorem trL_all (p : Bool) (y : ℕ) (f : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, .all y f) :: fs) c = 7 :: y :: trL ((p, f) :: fs) c := by
  cases p <;> simp [trL, tr, cnt, Formula.encode]

theorem cntL_ex (p : Bool) (y : ℕ) (f : Formula) (fs : List (Bool × Formula)) :
    cntL ((p, .ex y f) :: fs) = cntL ((p, f) :: fs) := by
  cases p <;> simp [cnt]

theorem cntL_all (p : Bool) (y : ℕ) (f : Formula) (fs : List (Bool × Formula)) :
    cntL ((p, .all y f) :: fs) = cntL ((p, f) :: fs) := by
  cases p <;> simp [cnt]

theorem trL_atom (p : Bool) (f : Formula) (fs : List (Bool × Formula)) (c : ℕ) :
    trL ((p, f) :: fs) c = (tr p f c).encode ++ trL fs (c + cnt p f) := rfl

/-! ### Sequences of variables -/

/-- Entry `l` of a sequence: `x[g + l]` (kind `0`) or `g + l` (other kinds). -/
def seqE (x : List ℕ) (k g l : ℕ) : ℕ := if k = 0 then x.getD (g + l) 0 else g + l

/-- A sequence of length `n`. -/
def seqL (x : List ℕ) (k g n : ℕ) : List ℕ := (List.range n).map (seqE x k g)

theorem seqL_succ (x : List ℕ) (k g n : ℕ) : seqL x k g (n + 1) = seqL x k g n ++ [seqE x k g n] := by
  simp [seqL, List.range_succ]

@[simp] theorem length_seqL (x : List ℕ) (k g n : ℕ) : (seqL x k g n).length = n := by simp [seqL]

theorem seqL_fresh (x : List ℕ) (k g n : ℕ) (hk : k ≠ 0) : seqL x k g n = List.range' g n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [seqL, seqE, hk, List.getElem_range']; try ring

/-- The code of `ȳ <ₗ z̄`, the way the program writes it: all but the last position, then the last. -/
def lexBodyL (ys zs : List ℕ) (m : ℕ) : List ℕ :=
  (List.range m).flatMap fun l => [5, 0, 0, 2, ys.getD l 0, zs.getD l 0, 4, 2, ys.getD l 0, zs.getD l 0]

@[simp] theorem lexBodyL_zero (ys zs : List ℕ) : lexBodyL ys zs 0 = [] := by unfold lexBodyL; try rfl

theorem lexBodyL_succ (ys zs : List ℕ) (m : ℕ) : lexBodyL ys zs (m + 1) = lexBodyL ys zs m ++
    [5, 0, 0, 2, ys.getD m 0, zs.getD m 0, 4, 2, ys.getD m 0, zs.getD m 0] := by
  simp [lexBodyL, List.range_succ]

theorem encode_lexF : ∀ (ys zs : List ℕ), ys.length = zs.length → ys ≠ [] →
    (lexF ys zs).encode = lexBodyL ys zs (ys.length - 1) ++
      [0, 0, 2, ys.getD (ys.length - 1) 0, zs.getD (ys.length - 1) 0]
  | [], _, _, h => (h rfl).elim
  | _ :: _, [], hl, _ => by simp at hl
  | y :: ys, z :: zs, hl, _ => by
    unfold lexF
    split_ifs with hys
    · subst hys
      have : zs = [] := by simpa using hl.symm
      subst this
      simp [Formula.encode, lexBodyL]
    · have ih := encode_lexF ys zs (by simpa using hl) hys
      obtain ⟨m, hm⟩ : ∃ m, ys.length = m + 1 := ⟨ys.length - 1, by
        have := List.length_pos_iff.mpr hys; omega⟩
      simp only [Formula.encode, List.cons_append, List.nil_append]
      rw [ih]
      simp only [List.length_cons, hm, Nat.add_sub_cancel]
      have e : lexBodyL (y :: ys) (z :: zs) (m + 1) =
          [5, 0, 0, 2, y, z, 4, 2, y, z] ++ lexBodyL ys zs m := by
        unfold lexBodyL
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
        rfl
      rw [e]
      simp

/-- The code of `negRel`, the way the program writes it. -/
theorem encode_negRel (i : ℕ) (ys : List ℕ) (c : ℕ) (hys : ys ≠ []) :
    (negRel i ys c).encode =
      [5, 0, 5 * i + 5, 1, ys.headD 0, 5, 4, 0, 5 * i + 2, ys.length] ++
      List.range' c ys.length ++ (lexF ys (List.range' c ys.length)).encode ++
      [5, 4, 0, 5 * i + 4, 2 * ys.length] ++ List.range' c (2 * ys.length) ++ [4] ++
      (lexF (List.range' c ys.length) ys).encode ++
      (lexF ys (List.range' (c + ys.length) ys.length)).encode ++
      [4, 0, 5 * i + 3, ys.length] ++ List.range' (c + ys.length) ys.length ++
      (lexF (List.range' (c + ys.length) ys.length) ys).encode := by
  have hr : List.range' c (2 * ys.length) =
      List.range' c ys.length ++ List.range' (c + ys.length) ys.length := by
    rw [show 2 * ys.length = ys.length + ys.length by ring, ← List.range'_append]; simp
  rw [hr]
  unfold negRel
  rw [if_neg hys]
  simp [Formula.encode, zI, fI, sI, lI]
  ring_nf

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
