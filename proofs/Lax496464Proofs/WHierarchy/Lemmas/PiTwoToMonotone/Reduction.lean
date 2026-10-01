import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Correct
import Lax496464Proofs.WHierarchy.HittingSet.WSHSMath
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.ComputableBounds
import Lax496464.WH_A2_FptReductions

/-! # The reduction `p-WD_φ → p-WSat(monotone)`: construction, correctness, parameter

For a `Π₂`-sentence `φ = ∀ xs ∃ ys ψ` the map `Out.R (dataOf xs ys ψ s)` sends instances to
instances (`isReduction`), and the new parameter is `W = (k+1)^D ≤ g(k)` for the computable
`g k = (k+1)^D + k`, `D` fixed by `φ` (`paramBounded`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Reduction

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Logic.Words
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Correct

theorem pWSat_yes_iff (Γ : Set Lax429075.CNF.Formula) (α : Lax429075.CNF.Formula) (k : ℕ) :
    (pWSat Γ).Yes (encode α ++ [k]) ↔ WeightSat α k := by
  constructor
  · rintro ⟨α', k', h, hw⟩
    obtain ⟨rfl, rfl⟩ := Lax496464Proofs.WHierarchy.HittingSet.WSHSMath.encode_inj h
    exact hw
  · exact fun hw => ⟨α, k, rfl, hw⟩

theorem not_weightSat_empty (k : ℕ) : ¬ WeightSat [[]] k := by
  rintro ⟨S, -, -, h⟩
  simp [Lax429075.CNF.eval] at h

section
variable {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
  (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys)
include hq hv

/-- **Construction and correctness.** -/
theorem isReduction :
    IsReduction (pWD (Formula.allBlock xs (Formula.exBlock ys ψ)) s)
      (pWSat {α | IsMonotone α}) (R (dataOf xs ys ψ s)) := by
  refine ⟨fun x _ => R_mem _ x, fun x hx => ?_⟩
  obtain ⟨A, k, hxe⟩ := hx
  obtain ⟨bl, he⟩ := exists_enc hxe
  rw [pWD_yes_iff _ _ hxe]
  unfold R
  split_ifs with hfit
  · rw [pWSat_yes_iff]
    exact witness_iff_weightSat hq hv he hfit
  · rw [show [1, 0, kW x] = encode [[]] ++ [kW x] by rfl, pWSat_yes_iff]
    constructor
    · intro hw
      refine absurd ((fitW_iff he xs ys ψ s).mpr ?_) hfit
      have := hw.1
      rwa [fits_allBlock, fits_exBlock] at this
    · intro hw; exact absurd hw (not_weightSat_empty _)

end

/-- **The parameter bound**: the new parameter is at most `(k+1)^D`. -/
theorem paramBounded (φ : Formula) (s : ℕ) (Dt : Data) :
    ParamBounded (pWD φ s) (pWSat {α | IsMonotone α}) (R Dt) := by
  refine ⟨fun k => (k + 1) ^ Dt.D + k,
    Lax496464Proofs.WHierarchy.ComputableBounds.computable_add
      (Lax496464Proofs.WHierarchy.ComputableBounds.computable_pow Dt.D Primrec.succ.to_comp) Computable.id,
    fun x hx => ?_⟩
  obtain ⟨A, k, hxe⟩ := hx
  rw [pWD_param_eq φ s hxe]
  obtain ⟨bl, he⟩ := exists_enc hxe
  show (R Dt x).getLast?.getD 0 ≤ (k + 1) ^ Dt.D + k
  rw [← he.kW_eq]
  exact R_last Dt x

/-- The decomposition of a `Π₂`-sentence. -/
theorem decompose {φ : Formula} (hφ : IsPi 2 φ) (hs : IsSentence φ) :
    ∃ xs ys ψ, φ = Formula.allBlock xs (Formula.exBlock ys ψ) ∧ ψ.IsQF ∧
      ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys := by
  obtain ⟨xs, φ1, rfl, ys, ψ, rfl, hq⟩ := hφ
  refine ⟨xs, ys, ψ, rfl, hq, fun v hv => ?_⟩
  unfold IsSentence at hs
  rw [freeVars_allBlock, freeVars_exBlock] at hs
  by_contra hn
  simp only [not_or] at hn
  have : v ∈ (ψ.freeVars \ ys.toFinset) \ xs.toFinset := by
    simp [hv, hn.1, hn.2]
  rw [hs] at this; simp at this

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Reduction
