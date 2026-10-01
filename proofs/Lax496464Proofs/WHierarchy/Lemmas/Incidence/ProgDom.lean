import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs

/-! # What the program needs of an instance word

`Dom x φ`: the word `x` is the word of a structure followed by the code of the formula `φ`, whose
tokens are those of a positive `Σ_1`-formula (atoms, equations, `∧`, `∨`, `∃`), and whose arities
are positive. From it: where the blocks, the tuples and the tokens are, and bounds on every value
the program computes (`BOK`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct

/-- The tokens of positive `Σ_1`-formulas. -/
def Token.Ok : Token → Prop
  | .rel _ _ => True
  | .eq _ _ => True
  | .and => True
  | .or => True
  | .ex _ => True
  | _ => False

/-- What the program needs of an instance word. -/
structure Dom (x : List ℕ) (φ : Formula) : Prop where
  drop_eq : x.drop (bo x (sOf x)) = φ.encode
  fs_eq : bo x (sOf x) + φ.encode.length = x.length
  ar_pos : ∀ i < sOf x, 1 ≤ arOf x i
  ok : ∀ t ∈ toks φ, Token.Ok t

theorem ok_qf : ∀ ψ : Formula, ψ.IsQF → ψ.IsPositive → ψ.NoSetVar → ∀ t ∈ toks ψ, Token.Ok t
  | .rel _ _, _, _, _, t, ht => by simp [toks] at ht; subst ht; trivial
  | .setVar _, _, _, h, _, _ => h.elim
  | .eq _ _, _, _, _, t, ht => by simp [toks] at ht; subst ht; trivial
  | .neg _, _, h, _, _, _ => h.elim
  | .and φ ψ, hq, hp, hn, t, ht => by
    simp only [toks, List.mem_cons, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · trivial
    · exact ok_qf φ hq.1 hp.1 hn.1 t ht
    · exact ok_qf ψ hq.2 hp.2 hn.2 t ht
  | .or φ ψ, hq, hp, hn, t, ht => by
    simp only [toks, List.mem_cons, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · trivial
    · exact ok_qf φ hq.1 hp.1 hn.1 t ht
    · exact ok_qf ψ hq.2 hp.2 hn.2 t ht
  | .ex _ _, h, _, _, _, _ => h.elim
  | .all _ _, h, _, _, _, _ => h.elim

theorem ok_exBlock (ψ : Formula) (h : ∀ t ∈ toks ψ, Token.Ok t) :
    ∀ xs : List ℕ, ∀ t ∈ toks (Formula.exBlock xs ψ), Token.Ok t
  | [] => h
  | x :: xs => by
    intro t ht
    simp only [exBlock_cons, toks, List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact ok_exBlock ψ h xs t ht

/-- **An instance word has what the program needs.** -/
theorem dom_of_mem {x : List ℕ} (hx : x ∈ (pMC Source).Domain) :
    ∃ A φ, EncodesMC x A φ ∧ Dom x φ ∧ Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem.Compat A
      (dataOf x (rOf φ)) := by
  obtain ⟨A, φ, h, ⟨hσ, hpos⟩, hns⟩ := hx
  obtain ⟨y, hy, hxy⟩ := h
  obtain ⟨hs, hN, har, hlist, hbo⟩ := parse hy hxy
  refine ⟨A, φ, ⟨y, hy, hxy⟩, ⟨?_, ?_, ?_, ?_⟩, compat hy hxy _⟩
  · rw [hbo, hxy, List.drop_left]
  · rw [hbo, hxy, List.length_append]
  · intro i hi
    rw [har i hi]
    rw [hs] at hi
    have hmem : A.arities.getD i 0 ∈ A.arities := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    exact A.arity_pos _ hmem
  · obtain ⟨xs, ψ, rfl, hqf⟩ := hσ
    rw [Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax.isPositive_exBlock] at hpos
    rw [noSetVar_exBlock] at hns
    exact ok_exBlock ψ (ok_qf ψ hqf hpos hns) xs

/-! ### Positions -/

/-- The number of tuples of the symbols below `i`. -/
def poOf (x : List ℕ) (i : ℕ) : ℕ := ((List.range i).map (cntOf x)).sum

/-- The number of tuples. -/
def tOf (x : List ℕ) : ℕ := poOf x (sOf x)

theorem po_dataOf (x : List ℕ) (r i : ℕ) : (dataOf x r).po i = poOf x i := rfl

theorem T_dataOf (x : List ℕ) (r : ℕ) : (dataOf x r).T = tOf x := rfl

theorem poOf_succ (x : List ℕ) (i : ℕ) : poOf x (i + 1) = poOf x i + cntOf x i := by
  simp [poOf, List.range_succ]

section Pos

variable {x : List ℕ} {φ : Formula}

theorem bo_le_succ (x : List ℕ) (i : ℕ) : bo x i + 1 ≤ bo x (i + 1) := by
  simp only [bo]; omega

theorem bo_mono (x : List ℕ) {i i' : ℕ} (h : i ≤ i') : bo x i ≤ bo x i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => have := bo_le_succ x t; omega

theorem bo_zero (x : List ℕ) : bo x 0 = 2 + sOf x := rfl

theorem bo_succ (x : List ℕ) (i : ℕ) :
    bo x (i + 1) = bo x i + 1 + cntOf x i * arOf x i := rfl

theorem fs_le (hd : Dom x φ) : bo x (sOf x) ≤ x.length := by have := hd.fs_eq; omega

theorem hdr_lt (hd : Dom x φ) : 2 + sOf x ≤ x.length := by
  have := bo_mono x (Nat.zero_le (sOf x)); rw [bo_zero] at this; have := fs_le hd; omega

theorem bo_lt (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) : bo x i < x.length := by
  have h1 := bo_le_succ x i
  have h2 := bo_mono x (show i + 1 ≤ sOf x by omega)
  have := fs_le hd; omega

theorem bo_succ_le (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) : bo x (i + 1) ≤ x.length :=
  (bo_mono x (show i + 1 ≤ sOf x by omega)).trans (fs_le hd)

/-- The entries of the tuples are inside their block. -/
theorem ent_pos_lt (x : List ℕ) {i j l : ℕ} (hj : j < cntOf x i) (hl : l < arOf x i) :
    bo x i + 1 + j * arOf x i + l < bo x (i + 1) := by
  rw [bo_succ]
  have : (j + 1) * arOf x i ≤ cntOf x i * arOf x i := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at this
  omega

/-- The tuples before a block are fewer than the positions before it. -/
theorem po_le_bo (hd : Dom x φ) (r : ℕ) : ∀ i ≤ sOf x, (dataOf x r).po i + 2 + sOf x ≤ bo x i
  | 0, _ => by simp [IncData.po_zero, bo_zero]
  | i + 1, hi => by
    have ih := po_le_bo hd r i (by omega)
    rw [IncData.po_succ, bo_succ]
    have ha := hd.ar_pos i (by omega)
    have : cntOf x i ≤ cntOf x i * arOf x i := Nat.le_mul_of_pos_right _ ha
    show (dataOf x r).po i + cntOf x i + 2 + sOf x ≤ _
    omega

theorem T_le (hd : Dom x φ) (r : ℕ) : (dataOf x r).T + 2 + sOf x ≤ bo x (sOf x) :=
  po_le_bo hd r _ le_rfl

end Pos

/-! ### Sizes of the formula part -/

theorem nrelT_le_length : ∀ l : List Token, nrelT l ≤ (l.flatMap Token.code).length
  | [] => le_rfl
  | t :: l => by
    have := nrelT_le_length l
    cases t <;> simp [Token.isRel, Token.code] at * <;> omega

theorem rmaxT_le_length : ∀ l : List Token, rmaxT l ≤ (l.flatMap Token.code).length
  | [] => le_rfl
  | t :: l => by
    have := rmaxT_le_length l
    cases t <;> simp [Token.relLen, Token.code] at * <;> omega

theorem nrel_le_length (φ : Formula) : nrel φ ≤ φ.encode.length := by
  rw [encode_eq_toks]; exact nrelT_le_length _

theorem rOf_le_length (φ : Formula) : rOf φ ≤ φ.encode.length := by
  rw [encode_eq_toks]; exact rmaxT_le_length _

/-! ### The value bound -/

/-- The bound the values of the program stay under. -/
def BOK (x : List ℕ) (B : ℕ) : Prop := maxEntry x + 2 * x.length + 8 < B

theorem getD_le_maxEntry (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ maxEntry x := by
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact le_maxEntry (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; exact Nat.zero_le _

theorem getD_lt {x : List ℕ} {B : ℕ} (hB : BOK x B) (i : ℕ) : x.getD i 0 < B := by
  have := getD_le_maxEntry x i; unfold BOK at hB; omega

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
