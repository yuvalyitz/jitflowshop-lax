import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Correct

/-! # The reduction on words: construction, correctness and the parameter bound

Weighted satisfiability read off the clause codes (`weightSat_iff`), the output of `red d` encodes
the structure and the sentence (`encodesMC_red`), `red d` is a reduction (`isReduction`), and its
parameter is bounded by a computable function of `k` (`paramBounded`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Reduction

open Lax429075.CNF
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Logic.Words
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Correct

/-! ### Clauses as codes -/

theorem litCode_div (l : Literal) : litCode l / 2 = l.index := by
  unfold litCode; split_ifs <;> omega

theorem litCode_mod (l : Literal) : litCode l % 2 = if l.positive then 0 else 1 := by
  unfold litCode; split_ifs <;> omega

theorem flatten_codesOf (α : Lax429075.CNF.Formula) :
    (codesOf α).flatten = α.flatten.map litCode := by
  unfold codesOf; rw [List.map_flatten]

theorem code_codesOf (α : Lax429075.CNF.Formula) {j : ℕ} (hj : j < α.flatten.length) :
    code (codesOf α) j = litCode (α.flatten[j]) := by
  unfold code
  rw [flatten_codesOf, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
    List.getElem_map]

theorem nL_codesOf (α : Lax429075.CNF.Formula) : nL (codesOf α) = α.flatten.length := by
  unfold nL; rw [flatten_codesOf, List.length_map]

theorem mem_vars (α : Lax429075.CNF.Formula) (v : ℕ) :
    v ∈ vars α ↔ ∃ j < nL (codesOf α), code (codesOf α) j / 2 = v := by
  unfold vars
  rw [List.mem_toFinset, nL_codesOf]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨C, hC, l, hl, rfl⟩
    have hmem : l ∈ α.flatten := List.mem_flatten.mpr ⟨C, hC, hl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
    exact ⟨j, hj, by rw [code_codesOf α hj, litCode_div]⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨C, hC, hl⟩ := List.mem_flatten.mp (List.getElem_mem hj)
    exact ⟨C, hC, _, hl, by rw [code_codesOf α hj, litCode_div]⟩

theorem length_codesOf (α : Lax429075.CNF.Formula) : (codesOf α).length = α.length := by
  simp [codesOf]

theorem len_codesOf (α : Lax429075.CNF.Formula) {c : ℕ} (hc : c < α.length) :
    len (codesOf α) c = α[c].length := by
  unfold len codesOf
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]; simp

theorem code_off_codesOf (α : Lax429075.CNF.Formula) {c p : ℕ} (hc : c < α.length)
    (hp : p < α[c].length) : code (codesOf α) (off (codesOf α) c + p) = litCode α[c][p] := by
  rw [code_off _ (by rw [length_codesOf]; exact hc) (by rw [len_codesOf α hc]; exact hp)]
  have h1 : (codesOf α).getD c [] = α[c].map litCode := by
    unfold codesOf
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hc), List.getElem_map]
  rw [h1, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hp), List.getElem_map]

theorem lit_iff (l : Literal) (S : Finset ℕ) :
    l.eval (fun i => decide (i ∈ S)) = true ↔
      (litCode l % 2 = 0 ∧ litCode l / 2 ∈ S) ∨ (litCode l % 2 = 1 ∧ litCode l / 2 ∉ S) := by
  rw [litCode_mod, litCode_div]
  unfold Literal.eval
  cases l.positive <;> simp

theorem eval_iff (α : Lax429075.CNF.Formula) (S : Finset ℕ) :
    eval α (fun i => decide (i ∈ S)) = true ↔ satC (codesOf α) S := by
  unfold eval satC
  rw [List.all_eq_true, length_codesOf]
  constructor
  · intro h c hc
    have h1 := h _ (List.getElem_mem hc)
    rw [List.any_eq_true] at h1
    obtain ⟨l, hl, hle⟩ := h1
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hl
    refine ⟨p, by rw [len_codesOf α hc]; exact hp, ?_⟩
    rw [code_off_codesOf α hc hp]; exact (lit_iff _ S).mp hle
  · intro h C hC
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hC
    obtain ⟨p, hp, hlit⟩ := h c hc
    rw [len_codesOf α hc] at hp
    rw [code_off_codesOf α hc hp] at hlit
    rw [List.any_eq_true]
    exact ⟨_, List.getElem_mem hp, (lit_iff _ S).mpr hlit⟩

/-- **Weighted satisfiability, on the codes.** -/
theorem weightSat_iff (α : Lax429075.CNF.Formula) (k : ℕ) :
    WeightSat α k ↔ weightC (codesOf α) k := by
  unfold WeightSat weightC
  refine exists_congr fun S => ?_
  rw [eval_iff]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h v hv; exact (mem_vars α v).mp (h hv)
  · intro h v hv; exact (mem_vars α v).mpr (h v hv)

theorem dcnf_codesOf {d : ℕ} {α : Lax429075.CNF.Formula} (h : IsDCNF d α) :
    ∀ C ∈ codesOf α, C.length ≤ d := by
  intro C hC
  simp only [codesOf, List.mem_map] at hC
  obtain ⟨C', hC', rfl⟩ := hC
  rw [List.length_map]; exact h C' hC'

/-! ### The reduction -/

variable (d : ℕ)

theorem red_eq (α : Lax429075.CNF.Formula) (k : ℕ) :
    red d (encode α ++ [k]) = structWord (codesOf α) d k ++ (phi d k).encode := by
  unfold red
  rw [encode_eq, clOf_wordOf', kOf_wordOf']

theorem encodesMC_red (α : Lax429075.CNF.Formula) (k : ℕ) :
    EncodesMC (red d (encode α ++ [k])) (A (codesOf α) d k) (phi d k) := by
  rw [red_eq]; exact encodesMC_append (encodes_structWord _ d k) _

/-- **Step 1: construction and correctness.** -/
theorem isReduction :
    IsReduction (pWSat {α | IsDCNF d α}) (pMC {φ | IsSigma 1 φ}) (red d) where
  maps_domain := by
    rintro x ⟨α, -, k, rfl⟩
    exact ⟨_, _, encodesMC_red d α k, isSigma_phi d k, noSetVar_phi d k⟩
  correct := by
    rintro x ⟨α, hα, k, rfl⟩
    rw [pMC_yes_iff _ (encodesMC_red d α k), ← weightC_iff _ d k (dcnf_codesOf hα),
      ← weightSat_iff]
    constructor
    · rintro ⟨α', k', he, hw⟩
      obtain ⟨rfl, rfl⟩ := encode_unique he.symm
      exact hw
    · exact fun hw => ⟨α, k, rfl, hw⟩

/-- **Step 2: the parameter bound.** -/
theorem paramBounded :
    ParamBounded (pWSat {α | IsDCNF d α}) (pMC {φ | IsSigma 1 φ}) (red d) := by
  refine ⟨gBound d, computable_gBound d, ?_⟩
  rintro x ⟨α, -, k, rfl⟩
  rw [pMC_param_eq _ (encodesMC_red d α k)]
  have : (pWSat {α | IsDCNF d α}).param (encode α ++ [k]) = k := by simp [pWSat]
  rw [this]
  exact size_phi d k

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Reduction
