import Lax496464.WH_B2_FirstOrder
import Mathlib.Tactic.Ring
import Mathlib.Data.List.GetD

/-! # The translation of a formula for the incidence structure, token by token

The prefix code of a formula is the concatenation of the codes of its *tokens* (`Token`), listed in
preorder (`toks`). The translation `TrCtx.tr` replaces every atom `R_i y_0 … y_{k-1}` by

`E_0 y_0 z ∧ (E_1 y_1 z ∧ ( … ∧ (E_{k-1} y_{k-1} z ∧ P_i z)))`

for a fresh variable `z = F + c`, `c` the number of atoms of relation symbols before it; the
symbol `P_i` is `i` and `E_l` is `s + l` in the incidence structure. An atom that does not fit the
vocabulary (`i ≥ s` or `k ≠ arity i`) gets the symbol `s + r` instead of `P_i`, which is outside
the new vocabulary. The code of the translation is computed token by token (`encode_tr`), which is
what the program does. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok

open Lax496464.WH_B2_FirstOrder

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The tokens of the prefix code of formulas. -/
inductive Token
  | rel (i : ℕ) (ys : List ℕ)
  | setVar (ys : List ℕ)
  | eq (x y : ℕ)
  | neg
  | and
  | or
  | ex (x : ℕ)
  | all (x : ℕ)

/-- The code of a token. -/
def Token.code : Token → List ℕ
  | .rel i ys => 0 :: i :: ys.length :: ys
  | .setVar ys => 1 :: ys.length :: ys
  | .eq x y => [2, x, y]
  | .neg => [3]
  | .and => [4]
  | .or => [5]
  | .ex x => [6, x]
  | .all x => [7, x]

/-- `1` for an atom of a relation symbol, `0` otherwise. -/
def Token.isRel : Token → ℕ
  | .rel _ _ => 1
  | _ => 0

/-- The number of arguments of an atom of a relation symbol, `0` for other tokens. -/
def Token.relLen : Token → ℕ
  | .rel _ ys => ys.length
  | _ => 0

/-- The tokens of a formula, in preorder. -/
def toks : Formula → List Token
  | .rel i ys => [.rel i ys]
  | .setVar ys => [.setVar ys]
  | .eq x y => [.eq x y]
  | .neg φ => .neg :: toks φ
  | .and φ ψ => .and :: (toks φ ++ toks ψ)
  | .or φ ψ => .or :: (toks φ ++ toks ψ)
  | .ex x φ => .ex x :: toks φ
  | .all x φ => .all x :: toks φ

/-- **The code of a formula is the concatenation of the codes of its tokens.** -/
theorem encode_eq_toks : ∀ φ : Formula, φ.encode = (toks φ).flatMap Token.code
  | .rel i ys => by simp [Formula.encode, toks, Token.code]
  | .setVar ys => by simp [Formula.encode, toks, Token.code]
  | .eq x y => by simp [Formula.encode, toks, Token.code]
  | .neg φ => by simp [Formula.encode, toks, Token.code, encode_eq_toks φ]
  | .and φ ψ => by simp [Formula.encode, toks, Token.code, encode_eq_toks φ, encode_eq_toks ψ]
  | .or φ ψ => by simp [Formula.encode, toks, Token.code, encode_eq_toks φ, encode_eq_toks ψ]
  | .ex x φ => by simp [Formula.encode, toks, Token.code, encode_eq_toks φ]
  | .all x φ => by simp [Formula.encode, toks, Token.code, encode_eq_toks φ]

/-- The number of atoms of relation symbols in a list of tokens. -/
def nrelT (l : List Token) : ℕ := (l.map Token.isRel).sum

/-- The largest number of arguments of an atom of a relation symbol in a list of tokens. -/
def rmaxT (l : List Token) : ℕ := l.foldr (fun t m => max t.relLen m) 0

@[simp] theorem nrelT_nil : nrelT [] = 0 := by unfold nrelT; try rfl
@[simp] theorem nrelT_cons (t : Token) (l : List Token) : nrelT (t :: l) = t.isRel + nrelT l := by
  simp [nrelT]
@[simp] theorem nrelT_append (l l' : List Token) : nrelT (l ++ l') = nrelT l + nrelT l' := by
  simp [nrelT]

@[simp] theorem rmaxT_nil : rmaxT [] = 0 := by unfold rmaxT; try rfl
@[simp] theorem rmaxT_cons (t : Token) (l : List Token) : rmaxT (t :: l) = max t.relLen (rmaxT l) :=
  by unfold rmaxT; try rfl
theorem rmaxT_append (l l' : List Token) : rmaxT (l ++ l') = max (rmaxT l) (rmaxT l') := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.cons_append, rmaxT_cons, ih]; omega

/-- The number of atoms of relation symbols of a formula. -/
def nrel (φ : Formula) : ℕ := nrelT (toks φ)

/-- The largest number of arguments of an atom of a relation symbol of a formula. -/
def rOf (φ : Formula) : ℕ := rmaxT (toks φ)

@[simp] theorem nrel_rel (i : ℕ) (ys : List ℕ) : nrel (.rel i ys) = 1 := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_setVar (ys : List ℕ) : nrel (.setVar ys) = 0 := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_eq (x y : ℕ) : nrel (.eq x y) = 0 := by simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_neg (φ : Formula) : nrel (.neg φ) = nrel φ := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_and (φ ψ : Formula) : nrel (.and φ ψ) = nrel φ + nrel ψ := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_or (φ ψ : Formula) : nrel (.or φ ψ) = nrel φ + nrel ψ := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_ex (x : ℕ) (φ : Formula) : nrel (.ex x φ) = nrel φ := by
  simp [nrel, toks, Token.isRel]
@[simp] theorem nrel_all (x : ℕ) (φ : Formula) : nrel (.all x φ) = nrel φ := by
  simp [nrel, toks, Token.isRel]

/-- Every atom of a relation symbol has at most `r` arguments. -/
def RelLe (r : ℕ) : Formula → Prop
  | .rel _ ys => ys.length ≤ r
  | .setVar _ => True
  | .eq _ _ => True
  | .neg φ => RelLe r φ
  | .and φ ψ => RelLe r φ ∧ RelLe r ψ
  | .or φ ψ => RelLe r φ ∧ RelLe r ψ
  | .ex _ φ => RelLe r φ
  | .all _ φ => RelLe r φ

theorem relLe_of_rmaxT_le : ∀ (φ : Formula) {r : ℕ}, rmaxT (toks φ) ≤ r → RelLe r φ
  | .rel i ys, r, h => by simpa [toks, Token.relLen, RelLe] using h
  | .setVar _, _, _ => trivial
  | .eq _ _, _, _ => trivial
  | .neg φ, r, h => relLe_of_rmaxT_le φ (by simpa [toks, Token.relLen] using h)
  | .and φ ψ, r, h => by
    simp only [toks, rmaxT_cons, rmaxT_append, Token.relLen] at h
    exact ⟨relLe_of_rmaxT_le φ (by omega), relLe_of_rmaxT_le ψ (by omega)⟩
  | .or φ ψ, r, h => by
    simp only [toks, rmaxT_cons, rmaxT_append, Token.relLen] at h
    exact ⟨relLe_of_rmaxT_le φ (by omega), relLe_of_rmaxT_le ψ (by omega)⟩
  | .ex _ φ, r, h => relLe_of_rmaxT_le φ (by simpa [toks, Token.relLen] using h)
  | .all _ φ, r, h => relLe_of_rmaxT_le φ (by simpa [toks, Token.relLen] using h)

/-- Every atom of a formula has at most `rOf φ` arguments. -/
theorem relLe_rOf (φ : Formula) : RelLe (rOf φ) φ := relLe_of_rmaxT_le φ le_rfl

/-! ### The translation -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- What the translation needs to know: the number `s` of symbols and the arities `ar` of the old
vocabulary, the number `r` of binary symbols `E_l`, and the first fresh variable `F`. -/
structure TrCtx where
  s : ℕ
  r : ℕ
  F : ℕ
  ar : ℕ → ℕ

namespace TrCtx

variable (C : TrCtx)

/-- The symbol that replaces `R_i` in an atom with `k` arguments: `P_i = i` if the atom fits the
vocabulary, else `s + r`, outside the new vocabulary. -/
def pIdx (i k : ℕ) : ℕ := if i < C.s ∧ k = C.ar i then i else C.s + C.r

/-- `E_l y_l z ∧ (E_{l+1} y_{l+1} z ∧ ( … ∧ P z))`. -/
def relAux (P z : ℕ) : ℕ → List ℕ → Formula
  | _, [] => .rel P [z]
  | l, y :: ys => .and (.rel (C.s + l) [y, z]) (relAux P z (l + 1) ys)

/-- The translation of the atom `R_i ys`, with `z` for its fresh variable. -/
def relTr (i : ℕ) (ys : List ℕ) (z : ℕ) : Formula := C.relAux (C.pIdx i ys.length) z 0 ys

/-- **The translation**, the atoms of relation symbols before this subformula numbering `c`. -/
def tr : ℕ → Formula → Formula
  | c, .rel i ys => C.relTr i ys (C.F + c)
  | _, .setVar ys => .setVar ys
  | _, .eq x y => .eq x y
  | c, .neg φ => .neg (tr c φ)
  | c, .and φ ψ => .and (tr c φ) (tr (c + nrel φ) ψ)
  | c, .or φ ψ => .or (tr c φ) (tr (c + nrel φ) ψ)
  | c, .ex x φ => .ex x (tr c φ)
  | c, .all x φ => .all x (tr c φ)

/-- The code the program writes for an atom `R_i ys` with fresh variable `z`. -/
def relCode (i : ℕ) (ys : List ℕ) (z : ℕ) : List ℕ :=
  (List.range ys.length).flatMap (fun l => [4, 0, C.s + l, 2, ys.getD l 0, z]) ++
    [0, C.pIdx i ys.length, 1, z]

/-- The code the program writes for one token. -/
def emitTok (c : ℕ) : Token → List ℕ
  | .rel i ys => C.relCode i ys (C.F + c)
  | t => t.code

/-- The code the program writes for a list of tokens. -/
def emit : ℕ → List Token → List ℕ
  | _, [] => []
  | c, t :: ts => C.emitTok c t ++ emit (c + t.isRel) ts

theorem emit_append (c : ℕ) (l l' : List Token) :
    C.emit c (l ++ l') = C.emit c l ++ C.emit (c + nrelT l) l' := by
  induction l generalizing c with
  | nil => simp [emit]
  | cons t l ih =>
    simp only [List.cons_append, emit, ih, nrelT_cons, List.append_assoc]
    congr 3; ring

theorem emit_singleton (c : ℕ) (t : Token) : C.emit c [t] = C.emitTok c t := by simp [emit]

theorem encode_relAux (P z : ℕ) : ∀ (ys : List ℕ) (l : ℕ),
    (C.relAux P z l ys).encode =
      (List.range ys.length).flatMap (fun m => [4, 0, C.s + (l + m), 2, ys.getD m 0, z]) ++
        [0, P, 1, z]
  | [], l => by simp [relAux, Formula.encode]
  | y :: ys, l => by
    rw [relAux, Formula.encode, encode_relAux P z ys (l + 1), List.length_cons,
      List.range_succ_eq_map]
    simp only [Formula.encode, List.length_cons, List.length_nil, List.flatMap_cons,
      List.flatMap_map, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    simp only [List.cons_append, List.nil_append]
    congr 7
    refine List.flatMap_congr fun m _ => ?_
    congr 3; omega

theorem encode_relTr (i : ℕ) (ys : List ℕ) (z : ℕ) :
    (C.relTr i ys z).encode = C.relCode i ys z := by
  rw [relTr, encode_relAux, relCode]
  simp

/-- **The code of the translation is written token by token.** -/
theorem encode_tr : ∀ (φ : Formula) (c : ℕ), (C.tr c φ).encode = C.emit c (toks φ)
  | .rel i ys, c => by
    simp [tr, toks, emit, emitTok, encode_relTr]
  | .setVar ys, c => by simp [tr, toks, emit, emitTok, Formula.encode, Token.code]
  | .eq x y, c => by simp [tr, toks, emit, emitTok, Formula.encode, Token.code]
  | .neg φ, c => by
    simp [tr, toks, emit, emitTok, Formula.encode, Token.code, Token.isRel, encode_tr φ]
  | .and φ ψ, c => by
    simp [tr, toks, emit, emitTok, Formula.encode, Token.code, Token.isRel, encode_tr φ,
      encode_tr ψ, emit_append, nrel]
  | .or φ ψ, c => by
    simp [tr, toks, emit, emitTok, Formula.encode, Token.code, Token.isRel, encode_tr φ,
      encode_tr ψ, emit_append, nrel]
  | .ex x φ, c => by
    simp [tr, toks, emit, emitTok, Formula.encode, Token.code, Token.isRel, encode_tr φ]
  | .all x φ, c => by
    simp [tr, toks, emit, emitTok, Formula.encode, Token.code, Token.isRel, encode_tr φ]

/-! ### Size -/

theorem size_relAux (P z : ℕ) : ∀ (ys : List ℕ) (l : ℕ),
    (C.relAux P z l ys).size = 4 * ys.length + 2
  | [], l => by simp [relAux, Formula.size]
  | y :: ys, l => by
    rw [relAux, Formula.size, size_relAux P z ys (l + 1)]
    simp [Formula.size]; ring

/-- The translation is at most four times as large. -/
theorem size_tr : ∀ (φ : Formula) (c : ℕ), (C.tr c φ).size ≤ 4 * φ.size
  | .rel i ys, c => by
    simp only [tr, relTr, size_relAux, Formula.size]; omega
  | .setVar ys, c => by simp only [tr, Formula.size]; omega
  | .eq x y, c => by simp only [tr, Formula.size]; omega
  | .neg φ, c => by have := size_tr φ c; simp only [tr, Formula.size]; omega
  | .and φ ψ, c => by
    have := size_tr φ c; have := size_tr ψ (c + nrel φ); simp only [tr, Formula.size]; omega
  | .or φ ψ, c => by
    have := size_tr φ c; have := size_tr ψ (c + nrel φ); simp only [tr, Formula.size]; omega
  | .ex x φ, c => by have := size_tr φ c; simp only [tr, Formula.size]; omega
  | .all x φ, c => by have := size_tr φ c; simp only [tr, Formula.size]; omega

end TrCtx

/-- There are at most as many atoms as symbols. -/
theorem nrel_le_size : ∀ φ : Formula, nrel φ ≤ φ.size
  | .rel i ys => by simp [Formula.size]
  | .setVar ys => by simp
  | .eq x y => by simp
  | .neg φ => by have := nrel_le_size φ; simp [Formula.size]; omega
  | .and φ ψ => by
    have := nrel_le_size φ; have := nrel_le_size ψ; simp [Formula.size]; omega
  | .or φ ψ => by
    have := nrel_le_size φ; have := nrel_le_size ψ; simp [Formula.size]; omega
  | .ex x φ => by have := nrel_le_size φ; simp [Formula.size]; omega
  | .all x φ => by have := nrel_le_size φ; simp [Formula.size]; omega

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok
