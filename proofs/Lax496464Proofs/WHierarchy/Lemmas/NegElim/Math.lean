import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.ComputableBounds
import Lax496464.WH_A2_FptReductions

/-! # Negation elimination: the reduction on words, its correctness and parameter bound

`red x` is the word of the expanded structure of the compressed structure, read off `x` (`dataOf`),
followed by the code of `phiOf b K φ` with `K = 2 |code of φ|`, where `φ` is the formula of `x` and
`b = 1 + max x` is above every variable of `φ`. The compression renames the entries of the tuples by
their rank among all entries (`rkx`) and cuts the universe to `min N (#entries + |x|)`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Logic.Words
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem Lax496464Proofs.WHierarchy.Lemmas.NegElim.Correct
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress

/-- All entries of all tuples, symbol by symbol. -/
def entries (x : List ℕ) : List ℕ := (List.range (sOf x)).flatMap fun i => (listOf x i).flatten

/-- The set of entries. -/
def Ux (x : List ℕ) : Finset ℕ := (entries x).toFinset

/-- The renaming of the entries: their rank among the entries. -/
def rkx (x : List ℕ) (e : ℕ) : ℕ := rk (Ux x) e

/-- The size of the compressed universe. -/
def MOf (x : List ℕ) : ℕ := min (nOf x) ((entries x).length + x.length)

/-- The data of the expanded structure, read off the word. -/
def dataOf (x : List ℕ) : NData := ⟨sOf x, MOf x, arOf x, fun i => (listOf x i).map (List.map (rkx x))⟩

/-- The first fresh variable: above every entry of the word. -/
def bOf (x : List ℕ) : ℕ := maxEntry x + 1

open Classical in
/-- The formula of a model-checking word. -/
noncomputable def φOf (x : List ℕ) : Formula :=
  if h : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 then (Classical.choose h).2 else .eq 0 0

/-- **The reduction.** -/
noncomputable def red (x : List ℕ) : List ℕ :=
  (dataOf x).word ++ (phiOf (bOf x) (2 * (φOf x).encode.length) (φOf x)).encode

theorem φOf_eq {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) : φOf x = φ := by
  have hex : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 := ⟨(A, φ), h⟩
  unfold φOf
  rw [dif_pos hex]
  exact (encodesMC_unique (Classical.choose_spec hex) h).2

theorem mem_Ux {x : List ℕ} {a : ℕ} :
    a ∈ Ux x ↔ ∃ i < sOf x, ∃ t ∈ listOf x i, a ∈ t := by
  simp [Ux, entries, List.mem_flatMap, List.mem_flatten]

/-- The entries cover the tuples. -/
theorem cover {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    Cover A (Ux x) := by
  obtain ⟨y, hy, hx⟩ := h
  obtain ⟨hs, hN, har, hL, -⟩ := parse hy hx
  refine ⟨fun i t ht a ha => ?_, fun a ha => ?_⟩
  · have hi : i < sOf x := by rw [hs]; exact (A.wf i t ht).1
    refine mem_Ux.mpr ⟨i, hi, t, ?_, ha⟩
    rw [← List.mem_toFinset, (hL i hi).2]; exact ht
  · obtain ⟨i, hi, t, ht, ha⟩ := mem_Ux.mp ha
    have : t ∈ A.rel i := by rw [← (hL i hi).2, List.mem_toFinset]; exact ht
    exact (A.wf i t this).2.2 a ha

theorem nOf_eq {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    nOf x = A.size := by
  obtain ⟨y, hy, hx⟩ := h
  exact (parse hy hx).2.1

theorem card_le_MOf {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    (Ux x).card ≤ MOf x := by
  have h1 := (cover h).card_le
  have h2 : (Ux x).card ≤ (entries x).length := List.toFinset_card_le _
  rw [← nOf_eq h] at h1
  unfold MOf; omega

/-- The compressed structure of an instance. -/
noncomputable def cstr {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    Structure := compress (cover h) (MOf x) (card_le_MOf h)

/-- The word lists the data of the compressed structure. -/
theorem compat {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    Compat (cstr h) (dataOf x) := by
  have hU := cover h
  obtain ⟨y, hy, hx⟩ := h
  obtain ⟨hs, hN, har, hL, -⟩ := parse hy hx
  refine ⟨hs, ?_, fun i hi => har i hi, fun i hi => ⟨?_, ?_⟩⟩
  · rfl
  · have hent : ∀ t ∈ listOf x i, ∀ a ∈ t, a ∈ Ux x := fun t ht a ha =>
      mem_Ux.mpr ⟨i, hi, t, ht, ha⟩
    refine (hL i hi).1.map_on fun u hu t ht he => map_rk_inj (hent u hu) (hent t ht) he
  · show ((listOf x i).map (List.map (rkx x))).toFinset = (A.rel i).image (List.map (rk (Ux x)))
    rw [← (hL i hi).2]; ext t; simp; rfl

theorem lt_bOf {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    ∀ v ∈ φ.encode, v < bOf x := by
  obtain ⟨y, -, rfl⟩ := h
  intro v hv
  have := le_maxEntry (List.mem_append_right y hv)
  unfold bOf; omega

theorem isPositive_exBlock (θ : Formula) (h : θ.IsPositive) :
    ∀ xs : List ℕ, (Formula.exBlock xs θ).IsPositive
  | [] => h
  | _ :: xs => isPositive_exBlock θ h xs

/-- The new formula of a `Σ_1`-formula is a positive `Σ_1`-formula without the relation
variable. -/
theorem phiOf_mem {φ : Formula} (hφ : IsSigma 1 φ) (hns : φ.NoSetVar) (b K : ℕ) :
    IsSigma 1 (phiOf b K φ) ∧ (phiOf b K φ).IsPositive ∧ (phiOf b K φ).NoSetVar := by
  obtain ⟨xs, ψ, rfl, hq⟩ : ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ ψ.IsQF := hφ
  have hnsψ : ψ.NoSetVar := (noSetVar_exBlock ψ xs).mp hns
  have e : phiOf b K (Formula.exBlock xs ψ) =
      Formula.exBlock (List.range' b K ++ xs) (tr true ψ b) := by
    rw [phiOf, tr_exBlock, exBlock_append]
  rw [e]
  exact ⟨isSigma_one_exBlock (tr_isQF true ψ b hq) _,
    isPositive_exBlock _ (tr_isPositive true ψ b) _,
    (noSetVar_exBlock _ _).mpr (tr_noSetVar true ψ b hnsψ)⟩

/-- On an instance, the reduction writes the expanded structure and the new formula. -/
theorem red_encodes {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    EncodesMC (red x) (NData.toStructure (compat h).valid)
      (phiOf (bOf x) (2 * φ.encode.length) φ) := by
  unfold red
  rw [φOf_eq h]
  exact encodesMC_append (NData.encodes_word _) _

/-- **Step 1: construction and correctness.** -/
theorem isReduction :
    IsReduction (pMC {φ | IsSigma 1 φ}) (pMC {φ | IsSigma 1 φ ∧ φ.IsPositive}) red := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨A, φ, h, hφ, hns⟩ := hx
    obtain ⟨h1, h2, h3⟩ := phiOf_mem hφ hns (bOf x) _
    exact ⟨_, _, red_encodes h, ⟨h1, h2⟩, h3⟩
  · obtain ⟨A, φ, h, hφ, hns⟩ := hx
    rw [pMC_yes_iff _ h, pMC_yes_iff _ (red_encodes h)]
    have hn : φ.size ≤ x.length := by
      obtain ⟨y, -, rfl⟩ := h
      have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.size_le_length_encode φ
      simp; omega
    have hMN : MOf x ≤ A.size := by rw [← nOf_eq h]; unfold MOf; omega
    have hMn : min A.size ((Ux x).card + x.length) ≤ MOf x := by
      have h2 : (Ux x).card ≤ (entries x).length := List.toFinset_card_le _
      rw [← nOf_eq h]; unfold MOf; omega
    rw [models_compress_iff x.length (cover h) (card_le_MOf h) hMN hMn hφ hn]
    refine models_iff (compat h) hφ hns (lt_bOf h) ?_
    have := cnt_le true φ
    have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.size_le_length_encode φ
    omega

/-- The parameter bound `72 k`. -/
def gNE (k : ℕ) : ℕ := 72 * k

theorem computable_gNE : Computable gNE :=
  Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const 72) Computable.id

/-- **Step 2: the parameter bound.** -/
theorem paramBounded :
    ParamBounded (pMC {φ | IsSigma 1 φ}) (pMC {φ | IsSigma 1 φ ∧ φ.IsPositive}) red := by
  refine ⟨gNE, computable_gNE, fun x hx => ?_⟩
  obtain ⟨A, φ, h, -, -⟩ := hx
  show mcParam (red x) ≤ gNE (mcParam x)
  rw [mcParam_eq (red_encodes h), mcParam_eq h, gNE]
  exact size_phiOf_le _ _

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
