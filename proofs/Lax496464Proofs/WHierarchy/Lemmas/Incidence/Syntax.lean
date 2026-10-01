import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! # Syntax of the translated formula

The translation for the incidence structure of the data `D`, with fresh variables from `F`
(`ctxOf D F`): its free variables are those of the formula and the fresh ones (`mem_freeVars_tr`),
it fits the new vocabulary exactly when the formula fits the old one (`fits_tr`), and it stays
quantifier-free, positive, at most binary and free of the relation variable. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct

/-- The context of the translation for the data `D`, fresh variables from `F`. -/
def ctxOf (D : IncData) (F : ℕ) : TrCtx := ⟨D.s, D.r, F, D.ar⟩

/-- Every variable occurring in the formula, free or bound, is below `F`. -/
def VarsLt (F : ℕ) : Formula → Prop
  | .rel _ ys => ∀ y ∈ ys, y < F
  | .setVar ys => ∀ y ∈ ys, y < F
  | .eq x y => x < F ∧ y < F
  | .neg φ => VarsLt F φ
  | .and φ ψ => VarsLt F φ ∧ VarsLt F ψ
  | .or φ ψ => VarsLt F φ ∧ VarsLt F ψ
  | .ex x φ => x < F ∧ VarsLt F φ
  | .all x φ => x < F ∧ VarsLt F φ

/-- The variables of a formula are entries of its code. -/
theorem varsLt_of_encode {F : ℕ} : ∀ φ : Formula, (∀ v ∈ φ.encode, v < F) → VarsLt F φ
  | .rel _ ys, h => fun y hy => h y (by simp [Formula.encode, hy])
  | .setVar ys, h => fun y hy => h y (by simp [Formula.encode, hy])
  | .eq x y, h => ⟨h x (by simp [Formula.encode]), h y (by simp [Formula.encode])⟩
  | .neg φ, h => varsLt_of_encode φ fun v hv => h v (by simp [Formula.encode, hv])
  | .and φ ψ, h => ⟨varsLt_of_encode φ fun v hv => h v (by simp [Formula.encode, hv]),
      varsLt_of_encode ψ fun v hv => h v (by simp [Formula.encode, hv])⟩
  | .or φ ψ, h => ⟨varsLt_of_encode φ fun v hv => h v (by simp [Formula.encode, hv]),
      varsLt_of_encode ψ fun v hv => h v (by simp [Formula.encode, hv])⟩
  | .ex x φ, h => ⟨h x (by simp [Formula.encode]),
      varsLt_of_encode φ fun v hv => h v (by simp [Formula.encode, hv])⟩
  | .all x φ, h => ⟨h x (by simp [Formula.encode]),
      varsLt_of_encode φ fun v hv => h v (by simp [Formula.encode, hv])⟩

/-- The free variables are below `F`. -/
theorem lt_of_mem_freeVars {F : ℕ} : ∀ {φ : Formula}, VarsLt F φ → ∀ {v}, v ∈ φ.freeVars → v < F
  | .rel _ ys, h, v, hv => h v (by simpa [Formula.freeVars] using hv)
  | .setVar ys, h, v, hv => h v (by simpa [Formula.freeVars] using hv)
  | .eq x y, h, v, hv => by
    simp only [Formula.freeVars, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h.1
    · exact h.2
  | .neg φ, h, v, hv => lt_of_mem_freeVars (φ := φ) h hv
  | .and φ ψ, h, v, hv => by
    simp only [Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact lt_of_mem_freeVars h.1 hv
    · exact lt_of_mem_freeVars h.2 hv
  | .or φ ψ, h, v, hv => by
    simp only [Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact lt_of_mem_freeVars h.1 hv
    · exact lt_of_mem_freeVars h.2 hv
  | .ex x φ, h, v, hv => lt_of_mem_freeVars h.2 (Finset.mem_of_mem_erase hv)
  | .all x φ, h, v, hv => lt_of_mem_freeVars h.2 (Finset.mem_of_mem_erase hv)

/-! ### The translation of an atom -/

section RelAux

variable (C : TrCtx) (P z : ℕ)

theorem mem_freeVars_relAux : ∀ (ys : List ℕ) (l : ℕ) (v : ℕ),
    v ∈ (C.relAux P z l ys).freeVars ↔ v ∈ ys ∨ v = z
  | [], l, v => by simp [TrCtx.relAux, Formula.freeVars]
  | y :: ys, l, v => by
    simp only [TrCtx.relAux, Formula.freeVars, Finset.mem_union, mem_freeVars_relAux ys,
      List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    tauto

theorem sat_relAux (M : Structure) (S : Set (List ℕ)) : ∀ (ys : List ℕ) (l : ℕ) (ρ : Assignment),
    Sat M S (C.relAux P z l ys) ρ ↔
      (∀ m < ys.length, [ρ (ys.getD m 0), ρ z] ∈ M.rel (C.s + (l + m))) ∧ [ρ z] ∈ M.rel P
  | [], l, ρ => by simp [TrCtx.relAux, Sat]
  | y :: ys, l, ρ => by
    simp only [TrCtx.relAux, Sat, sat_relAux M S ys (l + 1) ρ, List.map_cons, List.map_nil,
      List.length_cons]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun m hm => ?_, h2⟩
      rcases m with _ | m
      · simpa using h0
      · have := h1 m (by omega)
        simp only [List.getD_cons_succ]
        rwa [show l + (m + 1) = l + 1 + m by omega]
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun m hm => ?_, h2⟩
      have := h1 (m + 1) (by omega)
      simp only [List.getD_cons_succ] at this
      rwa [show l + 1 + m = l + (m + 1) by omega]

theorem fits_relAux (ar : List ℕ) : ∀ (ys : List ℕ) (l : ℕ),
    (C.relAux P z l ys).Fits ar 0 ↔
      (∀ m < ys.length, C.s + (l + m) < ar.length ∧ 2 = ar.getD (C.s + (l + m)) 0) ∧
        P < ar.length ∧ 1 = ar.getD P 0
  | [], l => by simp [TrCtx.relAux, Formula.Fits]
  | y :: ys, l => by
    simp only [TrCtx.relAux, Formula.Fits, fits_relAux ar ys (l + 1), List.length_cons,
      List.length_nil]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun m hm => ?_, h2⟩
      rcases m with _ | m
      · simpa using h0
      · rw [show l + (m + 1) = l + 1 + m by omega]; exact h1 m (by omega)
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun m hm => ?_, h2⟩
      rw [show l + 1 + m = l + (m + 1) by omega]; exact h1 (m + 1) (by omega)

theorem isQF_relAux : ∀ (ys : List ℕ) (l : ℕ), (C.relAux P z l ys).IsQF
  | [], _ => trivial
  | _ :: ys, l => ⟨trivial, isQF_relAux ys (l + 1)⟩

theorem isPositive_relAux : ∀ (ys : List ℕ) (l : ℕ), (C.relAux P z l ys).IsPositive
  | [], _ => trivial
  | _ :: ys, l => ⟨trivial, isPositive_relAux ys (l + 1)⟩

theorem noSetVar_relAux : ∀ (ys : List ℕ) (l : ℕ), (C.relAux P z l ys).NoSetVar
  | [], _ => trivial
  | _ :: ys, l => ⟨trivial, noSetVar_relAux ys (l + 1)⟩

theorem arity_relAux : ∀ (ys : List ℕ) (l : ℕ), (C.relAux P z l ys).ArityAtMost 2
  | [], _ => by simp [TrCtx.relAux, Formula.ArityAtMost]
  | _ :: ys, l => ⟨by simp [Formula.ArityAtMost], arity_relAux ys (l + 1)⟩

end RelAux

/-! ### The translation of a formula -/

section Tr

variable (C : TrCtx)

theorem isQF_tr : ∀ (φ : Formula) (c : ℕ), φ.IsQF → (C.tr c φ).IsQF
  | .rel _ ys, _, _ => isQF_relAux C _ _ ys 0
  | .setVar _, _, _ => trivial
  | .eq _ _, _, _ => trivial
  | .neg φ, c, h => isQF_tr φ c h
  | .and φ ψ, c, h => ⟨isQF_tr φ c h.1, isQF_tr ψ _ h.2⟩
  | .or φ ψ, c, h => ⟨isQF_tr φ c h.1, isQF_tr ψ _ h.2⟩
  | .ex _ _, _, h => h.elim
  | .all _ _, _, h => h.elim

theorem isPositive_tr : ∀ (φ : Formula) (c : ℕ), φ.IsPositive → (C.tr c φ).IsPositive
  | .rel _ ys, _, _ => isPositive_relAux C _ _ ys 0
  | .setVar _, _, _ => trivial
  | .eq _ _, _, _ => trivial
  | .neg _, _, h => h.elim
  | .and φ ψ, c, h => ⟨isPositive_tr φ c h.1, isPositive_tr ψ _ h.2⟩
  | .or φ ψ, c, h => ⟨isPositive_tr φ c h.1, isPositive_tr ψ _ h.2⟩
  | .ex _ φ, c, h => isPositive_tr φ c h
  | .all _ φ, c, h => isPositive_tr φ c h

theorem noSetVar_tr : ∀ (φ : Formula) (c : ℕ), φ.NoSetVar → (C.tr c φ).NoSetVar
  | .rel _ ys, _, _ => noSetVar_relAux C _ _ ys 0
  | .setVar _, _, h => h.elim
  | .eq _ _, _, _ => trivial
  | .neg φ, c, h => noSetVar_tr φ c h
  | .and φ ψ, c, h => ⟨noSetVar_tr φ c h.1, noSetVar_tr ψ _ h.2⟩
  | .or φ ψ, c, h => ⟨noSetVar_tr φ c h.1, noSetVar_tr ψ _ h.2⟩
  | .ex _ φ, c, h => noSetVar_tr φ c h
  | .all _ φ, c, h => noSetVar_tr φ c h

theorem arity_tr : ∀ (φ : Formula) (c : ℕ), (C.tr c φ).ArityAtMost 2
  | .rel _ ys, _ => arity_relAux C _ _ ys 0
  | .setVar _, _ => trivial
  | .eq _ _, _ => trivial
  | .neg φ, c => arity_tr φ c
  | .and φ ψ, c => ⟨arity_tr φ c, arity_tr ψ _⟩
  | .or φ ψ, c => ⟨arity_tr φ c, arity_tr ψ _⟩
  | .ex _ φ, c => arity_tr φ c
  | .all _ φ, c => arity_tr φ c

theorem tr_exBlock (c : ℕ) (φ : Formula) :
    ∀ xs : List ℕ, C.tr c (Formula.exBlock xs φ) = Formula.exBlock xs (C.tr c φ)
  | [] => rfl
  | x :: xs => by simp only [exBlock_cons, TrCtx.tr, tr_exBlock c φ xs]

/-- **The free variables of the translation**: those of the formula and the fresh ones. -/
theorem mem_freeVars_tr : ∀ (φ : Formula) (c : ℕ), VarsLt C.F φ → ∀ v : ℕ,
    v ∈ (C.tr c φ).freeVars ↔ v ∈ φ.freeVars ∨ (C.F + c ≤ v ∧ v < C.F + c + nrel φ)
  | .rel i ys, c, _, v => by
    simp only [TrCtx.tr, TrCtx.relTr, mem_freeVars_relAux, Formula.freeVars, List.mem_toFinset,
      nrel_rel]
    constructor
    · rintro (h | rfl)
      · exact Or.inl h
      · right; omega
    · rintro (h | h)
      · exact Or.inl h
      · right; omega
  | .setVar ys, c, _, v => by simp [TrCtx.tr]
  | .eq x y, c, _, v => by simp [TrCtx.tr]
  | .neg φ, c, h, v => by
    simp only [TrCtx.tr, Formula.freeVars, nrel_neg]; exact mem_freeVars_tr φ c h v
  | .and φ ψ, c, h, v => by
    simp only [TrCtx.tr, Formula.freeVars, Finset.mem_union, nrel_and,
      mem_freeVars_tr φ c h.1 v, mem_freeVars_tr ψ _ h.2 v]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl (Or.inl h)
      · right; omega
      · exact Or.inl (Or.inr h)
      · right; omega
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · by_cases h' : v < C.F + c + nrel φ
        · left; right; omega
        · right; right; omega
  | .or φ ψ, c, h, v => by
    simp only [TrCtx.tr, Formula.freeVars, Finset.mem_union, nrel_or,
      mem_freeVars_tr φ c h.1 v, mem_freeVars_tr ψ _ h.2 v]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl (Or.inl h)
      · right; omega
      · exact Or.inl (Or.inr h)
      · right; omega
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · by_cases h' : v < C.F + c + nrel φ
        · left; right; omega
        · right; right; omega
  | .ex x φ, c, h, v => by
    simp only [TrCtx.tr, Formula.freeVars, Finset.mem_erase, nrel_ex,
      mem_freeVars_tr φ c h.2 v]
    have hx := h.1
    constructor
    · rintro ⟨hne, h | h⟩
      · exact Or.inl ⟨hne, h⟩
      · exact Or.inr h
    · rintro (⟨hne, h⟩ | h)
      · exact ⟨hne, Or.inl h⟩
      · exact ⟨by omega, Or.inr h⟩
  | .all x φ, c, h, v => by
    simp only [TrCtx.tr, Formula.freeVars, Finset.mem_erase, nrel_all,
      mem_freeVars_tr φ c h.2 v]
    have hx := h.1
    constructor
    · rintro ⟨hne, h | h⟩
      · exact Or.inl ⟨hne, h⟩
      · exact Or.inr h
    · rintro (⟨hne, h⟩ | h)
      · exact ⟨hne, Or.inl h⟩
      · exact ⟨by omega, Or.inr h⟩

end Tr

theorem nrel_exBlock (φ : Formula) : ∀ xs : List ℕ, nrel (Formula.exBlock xs φ) = nrel φ
  | [] => rfl
  | x :: xs => by rw [exBlock_cons, nrel_ex, nrel_exBlock φ xs]

theorem exBlock_append (φ : Formula) (xs ys : List ℕ) :
    Formula.exBlock (xs ++ ys) φ = Formula.exBlock xs (Formula.exBlock ys φ) := by
  simp [Formula.exBlock, List.foldr_append]

theorem isPositive_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).IsPositive ↔ φ.IsPositive
  | [] => Iff.rfl
  | _ :: xs => isPositive_exBlock φ xs

theorem arity_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).ArityAtMost 2 ↔ φ.ArityAtMost 2
  | [] => Iff.rfl
  | _ :: xs => arity_exBlock φ xs

theorem relLe_exBlock (r : ℕ) (φ : Formula) :
    ∀ xs : List ℕ, RelLe r (Formula.exBlock xs φ) ↔ RelLe r φ
  | [] => Iff.rfl
  | _ :: xs => relLe_exBlock r φ xs

theorem varsLt_exBlock {F : ℕ} (φ : Formula) :
    ∀ xs : List ℕ, VarsLt F (Formula.exBlock xs φ) ↔ (∀ x ∈ xs, x < F) ∧ VarsLt F φ
  | [] => by simp
  | x :: xs => by
    simp only [exBlock_cons, VarsLt, varsLt_exBlock φ xs, List.mem_cons, forall_eq_or_imp]
    tauto

/-! ### Fitting the new vocabulary -/

/-- The translation fits the new vocabulary exactly when the formula fits the old one. -/
theorem fits_tr {A : Structure} {D : IncData} (F : ℕ) (hs : D.s = A.arities.length)
    (har : ∀ i < D.s, D.ar i = A.arities.getD i 0) :
    ∀ (φ : Formula) (c : ℕ), RelLe D.r φ →
      (((ctxOf D F).tr c φ).Fits D.arities 0 ↔ φ.Fits A.arities 0)
  | .rel i ys, c, hr => by
    have hr' : ys.length ≤ D.r := hr
    have hcs : (ctxOf D F).s = D.s := rfl
    have hE : ∀ m < ys.length, D.s + (0 + m) < D.arities.length ∧
        2 = D.arities.getD (D.s + (0 + m)) 0 := by
      intro m hm
      rw [D.length_arities, D.arities_getD, if_neg (by omega), if_pos (by omega)]
      exact ⟨by omega, rfl⟩
    simp only [TrCtx.tr, TrCtx.relTr, fits_relAux, Formula.Fits, hcs]
    by_cases hc : i < D.s ∧ ys.length = D.ar i
    · have hp : (ctxOf D F).pIdx i ys.length = i := by unfold TrCtx.pIdx; exact if_pos hc
      have h1 : i < D.arities.length := by rw [D.length_arities]; omega
      have h2 : D.arities.getD i 0 = 1 := by rw [D.arities_getD, if_pos hc.1]
      rw [hp, h2]
      exact ⟨fun _ => ⟨by rw [← hs]; exact hc.1, by rw [← har i hc.1]; exact hc.2⟩,
        fun _ => ⟨hE, h1, rfl⟩⟩
    · have hp : (ctxOf D F).pIdx i ys.length = D.s + D.r := by
        unfold TrCtx.pIdx; exact if_neg hc
      rw [hp, D.length_arities]
      constructor
      · rintro ⟨-, h, -⟩; omega
      · rintro ⟨h1, h2⟩
        exact absurd ⟨by rw [hs]; exact h1, by rw [har i (by rw [hs]; exact h1)]; exact h2⟩ hc
  | .setVar ys, c, _ => by simp [TrCtx.tr, Formula.Fits]
  | .eq x y, c, _ => by simp [TrCtx.tr, Formula.Fits]
  | .neg φ, c, hr => by simp only [TrCtx.tr, Formula.Fits]; exact fits_tr F hs har φ c hr
  | .and φ ψ, c, hr => by
    simp only [TrCtx.tr, Formula.Fits]
    rw [fits_tr F hs har φ c hr.1, fits_tr F hs har ψ _ hr.2]
  | .or φ ψ, c, hr => by
    simp only [TrCtx.tr, Formula.Fits]
    rw [fits_tr F hs har φ c hr.1, fits_tr F hs har ψ _ hr.2]
  | .ex x φ, c, hr => by simp only [TrCtx.tr, Formula.Fits]; exact fits_tr F hs har φ c hr
  | .all x φ, c, hr => by simp only [TrCtx.tr, Formula.Fits]; exact fits_tr F hs har φ c hr

/-- A quantifier-free formula without the relation variable that fits a vocabulary of positive
arities has a free variable. -/
theorem exists_freeVar {A : Structure} : ∀ ψ : Formula, ψ.IsQF → ψ.NoSetVar →
    ψ.Fits A.arities 0 → ∃ v, v ∈ ψ.freeVars
  | .rel i ys, _, _, hf => by
    obtain ⟨hi, hl⟩ := hf
    have hmem : A.arities.getD i 0 ∈ A.arities := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    have := A.arity_pos _ hmem
    obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_length_pos (show 0 < ys.length by omega)
    exact ⟨y, by simp [Formula.freeVars]⟩
  | .setVar _, _, h, _ => h.elim
  | .eq x y, _, _, _ => ⟨x, by simp [Formula.freeVars]⟩
  | .neg φ, hq, hn, hf => exists_freeVar (A := A) φ hq hn hf
  | .and φ ψ, hq, hn, hf => by
    obtain ⟨v, hv⟩ := exists_freeVar (A := A) φ hq.1 hn.1 hf.1
    exact ⟨v, by simp [Formula.freeVars, hv]⟩
  | .or φ ψ, hq, hn, hf => by
    obtain ⟨v, hv⟩ := exists_freeVar (A := A) φ hq.1 hn.1 hf.1
    exact ⟨v, by simp [Formula.freeVars, hv]⟩
  | .ex _ _, hq, _, _ => hq.elim
  | .all _ _, hq, _, _ => hq.elim

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax
