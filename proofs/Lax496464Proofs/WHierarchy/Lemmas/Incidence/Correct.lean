import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.ComputableBounds
import Lax496464.WH_A2_FptReductions

/-! # The reduction on words: construction, correctness and the parameter bound

On a word `x = y ++ φ.encode` with `y` the word of a structure `A`, the reduction writes the word of
the incidence structure of `A`, with its tuples numbered in the order `y` lists them and `r = rOf φ`
binary symbols (the largest arity of an atom of `φ`), followed by the code of the translation of `φ`
with fresh variables from `F = 1 + max x`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Logic.Words Lax496464Proofs.WHierarchy.Logic.FormulaCode
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse

/-- The first fresh variable: above every entry of the word. -/
def fOf (x : List ℕ) : ℕ := maxEntry x + 1

/-- The output for the formula `φ` of the word `x`. -/
def outWord (x : List ℕ) (φ : Formula) : List ℕ :=
  (dataOf x (rOf φ)).word ++ (phiOf (dataOf x (rOf φ)) (fOf x) φ).encode

open Classical in
/-- **The reduction on words.** -/
noncomputable def red (x : List ℕ) : List ℕ :=
  if h : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 then outWord x (Classical.choose h).2
  else []

theorem red_eq {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    red x = outWord x φ := by
  have hex : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 := ⟨(A, φ), h⟩
  unfold red
  rw [dif_pos hex, (encodesMC_unique (Classical.choose_spec hex) h).2]

theorem compat {x y rest : List ℕ} {A : Structure} (hy : Encodes y A) (hx : x = y ++ rest)
    (r : ℕ) : Compat A (dataOf x r) := by
  obtain ⟨hs, hN, har, hlist, -⟩ := parse hy hx
  exact ⟨hs, hN, har, hlist⟩

theorem varsLt_fOf {x y : List ℕ} {φ : Formula} (hx : x = y ++ φ.encode) : VarsLt (fOf x) φ :=
  varsLt_of_encode φ fun v hv => by
    have : v ∈ x := by rw [hx]; exact List.mem_append_right _ hv
    have := le_maxEntry this
    unfold fOf; omega

/-- The target class. -/
abbrev Target : Set Formula := {φ | IsSigma 1 φ ∧ φ.IsPositive ∧ φ.ArityAtMost 2}

theorem phiOf_mem {D : IncData} {F : ℕ} {φ : Formula} (hσ : IsSigma 1 φ)
    (hpos : φ.IsPositive) : phiOf D F φ ∈ Target := by
  obtain ⟨xs, ψ, rfl, hqf⟩ := hσ
  rw [isPositive_exBlock] at hpos
  rw [phiOf_exBlock]
  refine ⟨⟨_, _, rfl, isQF_tr _ ψ 0 hqf⟩, (isPositive_exBlock _ _).mpr (isPositive_tr _ ψ 0 hpos),
    (arity_exBlock _ _).mpr (arity_tr _ ψ 0)⟩

theorem phiOf_noSetVar {D : IncData} {F : ℕ} {φ : Formula} (hns : φ.NoSetVar) :
    (phiOf D F φ).NoSetVar :=
  (noSetVar_exBlock _ _).mpr (noSetVar_tr _ φ 0 hns)

theorem size_phiOf (D : IncData) (F : ℕ) (φ : Formula) : (phiOf D F φ).size ≤ 6 * φ.size := by
  rw [phiOf, size_exBlock]
  have h1 := TrCtx.size_tr (ctxOf D F) φ 0
  have h2 := nrel_le_size φ
  simp only [zsOf, List.length_map, List.length_range]
  omega

section Main

variable {x : List ℕ} {A : Structure} {φ : Formula}

/-- On an instance, the reduction writes an encoding of the incidence structure and the
translated formula. -/
theorem encodesMC_red (h : EncodesMC x A φ) (hA : Compat A (dataOf x (rOf φ))) :
    EncodesMC (red x) (dataOf x (rOf φ)).toStructure (phiOf (dataOf x (rOf φ)) (fOf x) φ) := by
  rw [red_eq h]
  exact ⟨_, (dataOf x (rOf φ)).encodes_word hA.valid, rfl⟩

/-- The source problem. -/
abbrev Source : Set Formula := {φ | IsSigma 1 φ ∧ φ.IsPositive}

/-- **Step 1: construction and correctness.** -/
theorem isReduction : IsReduction (pMC Source) (pMC Target) red where
  maps_domain x hx := by
    obtain ⟨A, φ, h, ⟨hσ, hpos⟩, hns⟩ := hx
    obtain ⟨y, hy, hxy⟩ := h
    have hc := compat hy hxy (rOf φ)
    exact ⟨_, _, encodesMC_red ⟨y, hy, hxy⟩ hc, phiOf_mem hσ hpos, phiOf_noSetVar hns⟩
  correct x hx := by
    obtain ⟨A, φ, h, ⟨hσ, hpos⟩, hns⟩ := hx
    obtain ⟨y, hy, hxy⟩ := h
    have hc := compat hy hxy (rOf φ)
    rw [pMC_yes_iff _ ⟨y, hy, hxy⟩, pMC_yes_iff _ (encodesMC_red ⟨y, hy, hxy⟩ hc)]
    exact models_iff hc (varsLt_fOf hxy) (relLe_rOf φ) hσ hpos hns

/-- **Step 2: the parameter at most sextuples.** -/
theorem paramBounded : ParamBounded (pMC Source) (pMC Target) red := by
  refine ⟨fun k => 6 * k, Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const 6)
    Computable.id, fun x hx => ?_⟩
  obtain ⟨A, φ, h, -, -⟩ := hx
  obtain ⟨y, hy, hxy⟩ := h
  have hc := compat hy hxy (rOf φ)
  show mcParam (red x) ≤ 6 * mcParam x
  rw [mcParam_eq (encodesMC_red ⟨y, hy, hxy⟩ hc), mcParam_eq ⟨y, hy, hxy⟩]
  exact size_phiOf _ _ _

end Main

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
