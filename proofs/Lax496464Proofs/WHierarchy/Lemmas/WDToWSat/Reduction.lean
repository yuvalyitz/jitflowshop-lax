import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Correct
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464.WH_A2_FptReductions

/-! # The reduction `p-WD_φ → p-WSat(d-CNF)`: construction, correctness, parameter

For a `Π_1`-sentence `φ = ∀ xs ψ` the map `R (dataOf xs ψ s)` sends instances to instances
(`isReduction`), and the parameter stays `k` (`paramBounded`). The word of a CNF followed by `k`
determines both (`encode_append_inj`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Reduction

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Logic.Words
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Correct

/-! ### The word of a CNF determines it -/

theorem litCode_inj {l l' : Lax429075.CNF.Literal} (h : litCode l = litCode l') : l = l' := by
  obtain ⟨i, p⟩ := l
  obtain ⟨j, q⟩ := l'
  simp only [litCode] at h
  cases p <;> cases q <;> simp at h ⊢ <;> omega

/-- The clause part of a CNF word. -/
def body (α : Lax429075.CNF.Formula) : List ℕ := α.flatMap fun C => C.length :: C.map litCode

theorem body_prefix : ∀ (α α' : Lax429075.CNF.Formula) (r r' : List ℕ), α.length = α'.length →
    body α ++ r = body α' ++ r' → α = α' ∧ r = r'
  | [], [], r, r', _, h => ⟨rfl, by simpa [body] using h⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | C :: α, C' :: α', r, r', hl, h => by
    simp only [body, List.flatMap_cons, List.cons_append, List.append_assoc, List.cons.injEq] at h
    obtain ⟨hlen, h⟩ := h
    obtain ⟨hC, h⟩ := List.append_inj h (by simp [hlen])
    have hCC : C = C' := List.map_injective_iff.mpr (fun _ _ => litCode_inj) hC
    obtain ⟨h1, h2⟩ := body_prefix α α' r r' (by simpa using hl) h
    exact ⟨by rw [hCC, h1], h2⟩

theorem encode_append_inj {α α' : Lax429075.CNF.Formula} {k k' : ℕ}
    (h : encode α ++ [k] = encode α' ++ [k']) : α = α' ∧ k = k' := by
  simp only [encode, List.cons_append, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  obtain ⟨h1, h2⟩ := body_prefix α α' [k] [k'] hl h
  exact ⟨h1, by simpa using h2⟩

theorem pWSat_yes_iff (Γ : Set Lax429075.CNF.Formula) (α : Lax429075.CNF.Formula) (k : ℕ) :
    (pWSat Γ).Yes (encode α ++ [k]) ↔ WeightSat α k := by
  constructor
  · rintro ⟨α', k', h, hw⟩
    obtain ⟨rfl, rfl⟩ := encode_append_inj h
    exact hw
  · exact fun hw => ⟨α, k, rfl, hw⟩

theorem not_weightSat_empty (k : ℕ) : ¬ WeightSat [[]] k := by
  rintro ⟨S, -, -, h⟩
  simp [Lax429075.CNF.eval] at h

/-! ### The reduction -/

section
variable {xs : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs)
include hq hv

/-- **Construction and correctness.** -/
theorem isReduction :
    IsReduction (pWD (Formula.allBlock xs ψ) s)
      (pWSat {α | IsDCNF (dBound (dataOf xs ψ s)) α}) (R (dataOf xs ψ s)) := by
  refine ⟨fun x _ => R_mem _ x, fun x hx => ?_⟩
  obtain ⟨A, k, hxe⟩ := hx
  obtain ⟨bl, he⟩ := exists_enc hxe
  rw [pWD_yes_iff _ _ hxe]
  unfold R
  split_ifs with hfit
  · rw [pWSat_yes_iff, he.kW_eq, weightSat_iff hq hv he hfit, witness_iff hq hv he]
    exact ⟨fun h => h.2, fun h => ⟨(fitW_iff he xs ψ s).mp hfit, h⟩⟩
  · rw [show [1, 0, kW x] = encode [[]] ++ [kW x] by rfl, pWSat_yes_iff]
    constructor
    · intro hw; exact absurd ((fitW_iff he xs ψ s).mpr hw.1) hfit
    · intro hw; exact absurd hw (not_weightSat_empty _)

end

/-- **The parameter bound**: the parameter stays `k`. -/
theorem paramBounded (φ : Formula) (s : ℕ) (D : Data) :
    ParamBounded (pWD φ s) (pWSat {α | IsDCNF (dBound D) α}) (R D) := by
  refine ⟨id, Computable.id, fun x hx => ?_⟩
  obtain ⟨A, k, hxe⟩ := hx
  rw [pWD_param_eq φ s hxe]
  obtain ⟨bl, he⟩ := exists_enc hxe
  show (R D x).getLast?.getD 0 ≤ k
  unfold R
  split_ifs <;> simp [he.kW_eq]

/-- The decomposition of a `Π_1`-sentence. -/
theorem decompose {φ : Formula} (hφ : IsPi 1 φ) (hs : IsSentence φ) :
    ∃ xs ψ, φ = Formula.allBlock xs ψ ∧ ψ.IsQF ∧ ∀ v ∈ ψ.freeVars, v ∈ xs := by
  obtain ⟨xs, ψ, rfl, hq⟩ := hφ
  refine ⟨xs, ψ, rfl, hq, fun v hv => ?_⟩
  unfold IsSentence at hs
  rw [freeVars_allBlock] at hs
  by_contra hn
  have : v ∈ ψ.freeVars \ xs.toFinset := Finset.mem_sdiff.mpr ⟨hv, by simpa using hn⟩
  rw [hs] at this; simp at this

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Reduction
