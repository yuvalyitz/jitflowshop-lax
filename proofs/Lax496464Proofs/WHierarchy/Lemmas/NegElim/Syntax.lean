import Lax496464Proofs.WHierarchy.Logic.SatFacts
import Lax496464Proofs.WHierarchy.Logic.FormulaCode

/-! # Negation elimination: the translation of a formula

The expanded vocabulary has the binary order `<` as symbol `0` and, for every old symbol `i` of arity
`r`, the five symbols `R_i = 5i+1` (arity `r`), `R_i^f = 5i+2` (the first tuple, arity `r`),
`R_i^l = 5i+3` (the last tuple, arity `r`), `R_i^s = 5i+4` (consecutive tuples, arity `2r`) and
`Z_i = 5i+5` (arity `1`, the whole universe when `R_i` is empty and nothing otherwise).

`tr p φ c` translates `φ` (if `p`) or `¬φ` (if not `p`) into a positive formula, pushing negations
to the atoms. A negative atom `¬R_i ȳ` becomes

`Z_i y_0 ∨ (R_i^f ū ∧ ȳ <ₗ ū) ∨ (R_i^s ū v̄ ∧ ū <ₗ ȳ ∧ ȳ <ₗ v̄) ∨ (R_i^l v̄ ∧ v̄ <ₗ ȳ)`

with fresh variables `ū = c, …, c+r-1` and `v̄ = c+r, …, c+2r-1` (`<ₗ` is the lexicographic order,
`lexF`), and `¬ x = y` becomes `x < y ∨ y < x`. The fresh variables of the whole translation are
`c, …, c + cnt p φ - 1`; they are bound in front of it (`phiOf`), in a block of any length
`K ≥ cnt p φ` (the program uses `K = 2 |code of φ|`, which it knows before it translates). -/

set_option linter.unnecessarySeqFocus false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! ### The symbols of the expanded vocabulary -/

/-- `R_i`. -/
def rI (i : ℕ) : ℕ := 5 * i + 1
/-- `R_i^f`, the first tuple. -/
def fI (i : ℕ) : ℕ := 5 * i + 2
/-- `R_i^l`, the last tuple. -/
def lI (i : ℕ) : ℕ := 5 * i + 3
/-- `R_i^s`, consecutive tuples. -/
def sI (i : ℕ) : ℕ := 5 * i + 4
/-- `Z_i`, the universe if `R_i` is empty. -/
def zI (i : ℕ) : ℕ := 5 * i + 5

/-- The arities of the five symbols of an old symbol of arity `a`. -/
def arBlk (a : ℕ) : List ℕ := [a, a, a, 2 * a, 1]

/-! ### The translation -/

/-- The lexicographic order `ȳ <ₗ z̄` of two tuples of variables of the same length. -/
def lexF : List ℕ → List ℕ → Formula
  | y :: ys, z :: zs =>
    if ys = [] then .rel 0 [y, z] else .or (.rel 0 [y, z]) (.and (.eq y z) (lexF ys zs))
  | _, _ => .rel 0 []

/-- The positive formula replacing `¬R_i ȳ`, with fresh variables from `c` on. -/
def negRel (i : ℕ) (ys : List ℕ) (c : ℕ) : Formula :=
  if ys = [] then .rel (fI i) [] else
    .or (.rel (zI i) [ys.headD 0])
      (.or (.and (.rel (fI i) (List.range' c ys.length)) (lexF ys (List.range' c ys.length)))
        (.or (.and (.rel (sI i) (List.range' c ys.length ++ List.range' (c + ys.length) ys.length))
              (.and (lexF (List.range' c ys.length) ys)
                (lexF ys (List.range' (c + ys.length) ys.length))))
          (.and (.rel (lI i) (List.range' (c + ys.length) ys.length))
            (lexF (List.range' (c + ys.length) ys.length) ys))))

/-- The number of fresh variables the translation uses. -/
def cnt : Bool → Formula → ℕ
  | true, .rel _ _ => 0
  | false, .rel _ ys => 2 * ys.length
  | _, .setVar _ => 0
  | _, .eq _ _ => 0
  | p, .neg φ => cnt (!p) φ
  | p, .and φ ψ => cnt p φ + cnt p ψ
  | p, .or φ ψ => cnt p φ + cnt p ψ
  | p, .ex _ φ => cnt p φ
  | p, .all _ φ => cnt p φ

/-- **The translation** of `φ` (polarity `true`) or of `¬φ` (polarity `false`), with fresh variables
from `c` on. -/
def tr : Bool → Formula → ℕ → Formula
  | true, .rel i ys, _ => .rel (rI i) ys
  | false, .rel i ys, c => negRel i ys c
  | _, .setVar ys, _ => .setVar ys
  | true, .eq x y, _ => .eq x y
  | false, .eq x y, _ => .or (.rel 0 [x, y]) (.rel 0 [y, x])
  | p, .neg φ, c => tr (!p) φ c
  | true, .and φ ψ, c => .and (tr true φ c) (tr true ψ (c + cnt true φ))
  | false, .and φ ψ, c => .or (tr false φ c) (tr false ψ (c + cnt false φ))
  | true, .or φ ψ, c => .or (tr true φ c) (tr true ψ (c + cnt true φ))
  | false, .or φ ψ, c => .and (tr false φ c) (tr false ψ (c + cnt false φ))
  | p, .ex x φ, c => .ex x (tr p φ c)
  | p, .all x φ, c => .all x (tr p φ c)

/-- **The new formula**: the variables `b, …, b + K - 1`, among them the fresh ones, bound in front
of the translation. -/
def phiOf (b K : ℕ) (φ : Formula) : Formula := Formula.exBlock (List.range' b K) (tr true φ b)

/-! ### Syntactic properties -/

theorem lexF_isPositive : ∀ ys zs : List ℕ, (lexF ys zs).IsPositive
  | [], _ => by simp [lexF, Formula.IsPositive]
  | _ :: _, [] => by simp [lexF, Formula.IsPositive]
  | y :: ys, z :: zs => by
    unfold lexF
    split_ifs
    · simp [Formula.IsPositive]
    · exact ⟨trivial, trivial, lexF_isPositive ys zs⟩

theorem lexF_isQF : ∀ ys zs : List ℕ, (lexF ys zs).IsQF
  | [], _ => by simp [lexF, Formula.IsQF]
  | _ :: _, [] => by simp [lexF, Formula.IsQF]
  | y :: ys, z :: zs => by
    unfold lexF
    split_ifs
    · simp [Formula.IsQF]
    · exact ⟨trivial, trivial, lexF_isQF ys zs⟩

theorem lexF_noSetVar : ∀ ys zs : List ℕ, (lexF ys zs).NoSetVar
  | [], _ => by simp [lexF, Formula.NoSetVar]
  | _ :: _, [] => by simp [lexF, Formula.NoSetVar]
  | y :: ys, z :: zs => by
    unfold lexF
    split_ifs
    · simp [Formula.NoSetVar]
    · exact ⟨trivial, trivial, lexF_noSetVar ys zs⟩

theorem negRel_isPositive (i : ℕ) (ys : List ℕ) (c : ℕ) : (negRel i ys c).IsPositive := by
  unfold negRel
  split_ifs
  · trivial
  · exact ⟨trivial, ⟨trivial, lexF_isPositive _ _⟩, ⟨trivial, lexF_isPositive _ _,
      lexF_isPositive _ _⟩, trivial, lexF_isPositive _ _⟩

theorem negRel_isQF (i : ℕ) (ys : List ℕ) (c : ℕ) : (negRel i ys c).IsQF := by
  unfold negRel
  split_ifs
  · trivial
  · exact ⟨trivial, ⟨trivial, lexF_isQF _ _⟩, ⟨trivial, lexF_isQF _ _, lexF_isQF _ _⟩, trivial,
      lexF_isQF _ _⟩

theorem negRel_noSetVar (i : ℕ) (ys : List ℕ) (c : ℕ) : (negRel i ys c).NoSetVar := by
  unfold negRel
  split_ifs
  · trivial
  · exact ⟨trivial, ⟨trivial, lexF_noSetVar _ _⟩, ⟨trivial, lexF_noSetVar _ _,
      lexF_noSetVar _ _⟩, trivial, lexF_noSetVar _ _⟩

/-- **The translation is positive.** -/
theorem tr_isPositive : ∀ (p : Bool) (φ : Formula) (c : ℕ), (tr p φ c).IsPositive
  | true, .rel _ _, _ => trivial
  | false, .rel i ys, c => negRel_isPositive i ys c
  | true, .setVar _, _ => trivial
  | false, .setVar _, _ => trivial
  | true, .eq _ _, _ => trivial
  | false, .eq _ _, _ => ⟨trivial, trivial⟩
  | p, .neg φ, c => by simpa [tr] using tr_isPositive (!p) φ c
  | true, .and φ ψ, c => ⟨tr_isPositive _ φ _, tr_isPositive _ ψ _⟩
  | false, .and φ ψ, c => ⟨tr_isPositive _ φ _, tr_isPositive _ ψ _⟩
  | true, .or φ ψ, c => ⟨tr_isPositive _ φ _, tr_isPositive _ ψ _⟩
  | false, .or φ ψ, c => ⟨tr_isPositive _ φ _, tr_isPositive _ ψ _⟩
  | true, .ex _ φ, c => tr_isPositive _ φ _
  | false, .ex _ φ, c => tr_isPositive _ φ _
  | true, .all _ φ, c => tr_isPositive _ φ _
  | false, .all _ φ, c => tr_isPositive _ φ _

/-- The translation of a quantifier-free formula is quantifier-free. -/
theorem tr_isQF : ∀ (p : Bool) (φ : Formula) (c : ℕ), φ.IsQF → (tr p φ c).IsQF
  | true, .rel _ _, _, _ => trivial
  | false, .rel i ys, c, _ => negRel_isQF i ys c
  | true, .setVar _, _, _ => trivial
  | false, .setVar _, _, _ => trivial
  | true, .eq _ _, _, _ => trivial
  | false, .eq _ _, _, _ => ⟨trivial, trivial⟩
  | p, .neg φ, c, h => by simpa [tr] using tr_isQF (!p) φ c h
  | true, .and φ ψ, c, h => ⟨tr_isQF _ φ _ h.1, tr_isQF _ ψ _ h.2⟩
  | false, .and φ ψ, c, h => ⟨tr_isQF _ φ _ h.1, tr_isQF _ ψ _ h.2⟩
  | true, .or φ ψ, c, h => ⟨tr_isQF _ φ _ h.1, tr_isQF _ ψ _ h.2⟩
  | false, .or φ ψ, c, h => ⟨tr_isQF _ φ _ h.1, tr_isQF _ ψ _ h.2⟩
  | _, .ex _ _, _, h => h.elim
  | _, .all _ _, _, h => h.elim

/-- The translation of a formula without the relation variable does not use it. -/
theorem tr_noSetVar : ∀ (p : Bool) (φ : Formula) (c : ℕ), φ.NoSetVar → (tr p φ c).NoSetVar
  | true, .rel _ _, _, _ => trivial
  | false, .rel i ys, c, _ => negRel_noSetVar i ys c
  | _, .setVar _, _, h => h.elim
  | true, .eq _ _, _, _ => trivial
  | false, .eq _ _, _, _ => ⟨trivial, trivial⟩
  | p, .neg φ, c, h => by simpa [tr] using tr_noSetVar (!p) φ c h
  | true, .and φ ψ, c, h => ⟨tr_noSetVar _ φ _ h.1, tr_noSetVar _ ψ _ h.2⟩
  | false, .and φ ψ, c, h => ⟨tr_noSetVar _ φ _ h.1, tr_noSetVar _ ψ _ h.2⟩
  | true, .or φ ψ, c, h => ⟨tr_noSetVar _ φ _ h.1, tr_noSetVar _ ψ _ h.2⟩
  | false, .or φ ψ, c, h => ⟨tr_noSetVar _ φ _ h.1, tr_noSetVar _ ψ _ h.2⟩
  | true, .ex _ φ, c, h => tr_noSetVar _ φ _ h
  | false, .ex _ φ, c, h => tr_noSetVar _ φ _ h
  | true, .all _ φ, c, h => tr_noSetVar _ φ _ h
  | false, .all _ φ, c, h => tr_noSetVar _ φ _ h

theorem tr_exBlock (ψ : Formula) (c : ℕ) :
    ∀ xs : List ℕ, tr true (Formula.exBlock xs ψ) c = Formula.exBlock xs (tr true ψ c)
  | [] => rfl
  | x :: xs => by simp [tr, tr_exBlock ψ c xs]

theorem cnt_exBlock (ψ : Formula) :
    ∀ xs : List ℕ, cnt true (Formula.exBlock xs ψ) = cnt true ψ
  | [] => rfl
  | x :: xs => by simp [cnt, cnt_exBlock ψ xs]

/-! ### Sizes -/

theorem size_lexF_le : ∀ ys zs : List ℕ, (lexF ys zs).size ≤ 8 * ys.length + 3
  | [], _ => by simp [lexF, Formula.size]
  | _ :: _, [] => by simp [lexF, Formula.size]
  | y :: ys, z :: zs => by
    have := size_lexF_le ys zs
    unfold lexF
    split_ifs
    · simp [Formula.size]
    · simp [Formula.size]; omega

theorem size_negRel_le (i : ℕ) (ys : List ℕ) (c : ℕ) :
    (negRel i ys c).size ≤ 60 * (ys.length + 1) := by
  unfold negRel
  split_ifs
  · simp [Formula.size] <;> omega
  · have h1 := size_lexF_le ys (List.range' c ys.length)
    have h2 := size_lexF_le (List.range' c ys.length) ys
    have h3 := size_lexF_le ys (List.range' (c + ys.length) ys.length)
    have h4 := size_lexF_le (List.range' (c + ys.length) ys.length) ys
    simp only [List.length_range'] at h2 h4
    simp only [Formula.size, List.length_cons, List.length_nil, List.length_range',
      List.length_append]
    omega

/-- **The translation is at most 60 times as large.** -/
theorem size_tr_le : ∀ (p : Bool) (φ : Formula) (c : ℕ), (tr p φ c).size ≤ 60 * φ.size
  | true, .rel _ _, _ => by simp [tr, Formula.size]
  | false, .rel i ys, c => by simpa [tr, Formula.size] using size_negRel_le i ys c
  | true, .setVar _, _ => by simp [tr, Formula.size]
  | false, .setVar _, _ => by simp [tr, Formula.size]
  | true, .eq _ _, _ => by simp [tr, Formula.size]
  | false, .eq _ _, _ => by simp [tr, Formula.size]
  | p, .neg φ, c => by have := size_tr_le (!p) φ c; simp [tr, Formula.size] <;> omega
  | true, .and φ ψ, c => by
    have := size_tr_le true φ c; have := size_tr_le true ψ (c + cnt true φ)
    simp [tr, Formula.size] <;> omega
  | false, .and φ ψ, c => by
    have := size_tr_le false φ c; have := size_tr_le false ψ (c + cnt false φ)
    simp [tr, Formula.size] <;> omega
  | true, .or φ ψ, c => by
    have := size_tr_le true φ c; have := size_tr_le true ψ (c + cnt true φ)
    simp [tr, Formula.size] <;> omega
  | false, .or φ ψ, c => by
    have := size_tr_le false φ c; have := size_tr_le false ψ (c + cnt false φ)
    simp [tr, Formula.size] <;> omega
  | true, .ex _ φ, c => by have := size_tr_le true φ c; simp [tr, Formula.size] <;> omega
  | false, .ex _ φ, c => by have := size_tr_le false φ c; simp [tr, Formula.size] <;> omega
  | true, .all _ φ, c => by have := size_tr_le true φ c; simp [tr, Formula.size] <;> omega
  | false, .all _ φ, c => by have := size_tr_le false φ c; simp [tr, Formula.size] <;> omega

/-- **At most two fresh variables per symbol.** -/
theorem cnt_le : ∀ (p : Bool) (φ : Formula), cnt p φ ≤ 2 * φ.size
  | true, .rel _ _ => by simp [cnt]
  | false, .rel _ ys => by simp [cnt, Formula.size]
  | true, .setVar _ => by simp [cnt]
  | false, .setVar _ => by simp [cnt]
  | true, .eq _ _ => by simp [cnt]
  | false, .eq _ _ => by simp [cnt]
  | p, .neg φ => by have := cnt_le (!p) φ; simp [cnt, Formula.size]; omega
  | p, .and φ ψ => by
    have := cnt_le p φ; have := cnt_le p ψ; simp [cnt, Formula.size]; omega
  | p, .or φ ψ => by
    have := cnt_le p φ; have := cnt_le p ψ; simp [cnt, Formula.size]; omega
  | p, .ex _ φ => by have := cnt_le p φ; simp [cnt, Formula.size]; omega
  | p, .all _ φ => by have := cnt_le p φ; simp [cnt, Formula.size]; omega

/-- **The new formula is at most 72 times as large** when `K = 2 |code of φ|`. -/
theorem size_phiOf_le (b : ℕ) (φ : Formula) :
    (phiOf b (2 * φ.encode.length) φ).size ≤ 72 * φ.size := by
  unfold phiOf
  rw [size_exBlock]
  have := size_tr_le true φ b
  have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.length_encode_le_three_mul_size φ
  simp only [List.length_range']
  omega

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax
