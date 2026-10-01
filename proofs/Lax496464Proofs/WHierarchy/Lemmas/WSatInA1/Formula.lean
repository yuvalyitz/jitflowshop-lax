import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs
import Lax496464Proofs.WHierarchy.ComputableBounds

/-! # The sentence: syntax, meaning and size

Big conjunctions and disjunctions; the sentence of the reduction is a `Σ_1`-sentence that fits the
vocabulary (`isSigma_phi`, `fits_phi`), its meaning (`sat_psi`), and its size, bounded by a
computable function of `k` (`size_phi`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs

/-! ### Big conjunctions and disjunctions -/

theorem sat_bigAnd (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) :
    ∀ l : List Formula, Sat A S (bigAnd l) ρ ↔ ∀ φ ∈ l, Sat A S φ ρ
  | [] => by simp [bigAnd, tru, Sat]
  | φ :: l => by simp [bigAnd, Sat, sat_bigAnd A S ρ l]

theorem sat_bigOr (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) :
    ∀ l : List Formula, Sat A S (bigOr l) ρ ↔ ∃ φ ∈ l, Sat A S φ ρ
  | [] => by simp [bigOr, fls, Sat]
  | φ :: l => by simp [bigOr, Sat, sat_bigOr A S ρ l]

theorem isQF_bigAnd : ∀ l : List Formula, (∀ φ ∈ l, φ.IsQF) → (bigAnd l).IsQF
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), isQF_bigAnd l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem isQF_bigOr : ∀ l : List Formula, (∀ φ ∈ l, φ.IsQF) → (bigOr l).IsQF
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), isQF_bigOr l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem noSetVar_bigAnd : ∀ l : List Formula, (∀ φ ∈ l, φ.NoSetVar) → (bigAnd l).NoSetVar
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), noSetVar_bigAnd l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem noSetVar_bigOr : ∀ l : List Formula, (∀ φ ∈ l, φ.NoSetVar) → (bigOr l).NoSetVar
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), noSetVar_bigOr l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem fits_bigAnd (ar : List ℕ) (s : ℕ) :
    ∀ l : List Formula, (∀ φ ∈ l, φ.Fits ar s) → (bigAnd l).Fits ar s
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), fits_bigAnd ar s l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem fits_bigOr (ar : List ℕ) (s : ℕ) :
    ∀ l : List Formula, (∀ φ ∈ l, φ.Fits ar s) → (bigOr l).Fits ar s
  | [], _ => trivial
  | φ :: l, h => ⟨h φ (by simp), fits_bigOr ar s l fun ψ hψ => h ψ (by simp [hψ])⟩

theorem freeVars_bigAnd {n : ℕ} (hn : 0 < n) :
    ∀ l : List Formula, (∀ φ ∈ l, ∀ v ∈ φ.freeVars, v < n) → ∀ v ∈ (bigAnd l).freeVars, v < n
  | [], _ => by simp [bigAnd, tru, Formula.freeVars]; omega
  | φ :: l, h => by
    intro v hv
    simp only [bigAnd, Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact h φ (by simp) v hv
    · exact freeVars_bigAnd hn l (fun ψ hψ => h ψ (by simp [hψ])) v hv

theorem freeVars_bigOr {n : ℕ} (hn : 0 < n) :
    ∀ l : List Formula, (∀ φ ∈ l, ∀ v ∈ φ.freeVars, v < n) → ∀ v ∈ (bigOr l).freeVars, v < n
  | [], _ => by simp [bigOr, fls, Formula.freeVars]; omega
  | φ :: l, h => by
    intro v hv
    simp only [bigOr, Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact h φ (by simp) v hv
    · exact freeVars_bigOr hn l (fun ψ hψ => h ψ (by simp [hψ])) v hv

theorem size_bigAnd_le {s : ℕ} : ∀ l : List Formula, (∀ φ ∈ l, φ.size ≤ s) →
    (bigAnd l).size ≤ l.length * (s + 1) + 3
  | [], _ => by simp [bigAnd, tru, Formula.size]
  | φ :: l, h => by
    have h1 := h φ (by simp)
    have h2 := size_bigAnd_le l fun ψ hψ => h ψ (by simp [hψ])
    simp only [bigAnd, Formula.size, List.length_cons]
    nlinarith

theorem size_bigOr_le {s : ℕ} : ∀ l : List Formula, (∀ φ ∈ l, φ.size ≤ s) →
    (bigOr l).size ≤ l.length * (s + 1) + 4
  | [], _ => by simp [bigOr, fls, Formula.size]
  | φ :: l, h => by
    have h1 := h φ (by simp)
    have h2 := size_bigOr_le l fun ψ hψ => h ψ (by simp [hψ])
    simp only [bigOr, Formula.size, List.length_cons]
    nlinarith

/-! ### The syntax of the sentence -/

variable (d k : ℕ)

theorem vt_lt (t : ℕ) : ∀ v ∈ vt d k t, v < k + 1 := by
  intro v hv
  simp only [vt, List.mem_map] at hv
  obtain ⟨p, -, rfl⟩ := hv
  exact Nat.mod_lt _ (by omega)

theorem length_vt (t : ℕ) : (vt d k t).length = d + 1 := by simp [vt]

theorem length_yt (t : ℕ) : (yt k t).length = k + 1 := by simp [yt]

theorem one_le_FF : 1 ≤ FF d k := Nat.one_le_pow _ _ (by omega)

theorem yv_lt {t j : ℕ} (ht : t < FF d k) (hj : j < k + 1) : yv k t j < nv d k := by
  unfold yv nv
  have : (t + 1) * (k + 1) ≤ FF d k * (k + 1) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem isQF_psi : (psi d k).IsQF := by
  refine ⟨trivial, isQF_bigAnd _ (by simp [Formula.IsQF]), isQF_bigAnd _ ?_,
    isQF_bigAnd _ ?_⟩
  · intro φ hφ
    simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, -, j, -, rfl⟩ := hφ; trivial
  · intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨t, -, rfl⟩ := hφ
    refine ⟨trivial, trivial, isQF_bigAnd _ fun ψ hψ => ?_⟩
    simp only [List.mem_map, List.mem_range] at hψ
    obtain ⟨j, -, rfl⟩ := hψ
    exact isQF_bigOr _ (by simp [Formula.IsQF])

theorem noSetVar_psi : (psi d k).NoSetVar := by
  refine ⟨trivial, noSetVar_bigAnd _ (by simp [Formula.NoSetVar]), noSetVar_bigAnd _ ?_,
    noSetVar_bigAnd _ ?_⟩
  · intro φ hφ
    simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, -, j, -, rfl⟩ := hφ; trivial
  · intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨t, -, rfl⟩ := hφ
    refine ⟨trivial, trivial, noSetVar_bigAnd _ fun ψ hψ => ?_⟩
    simp only [List.mem_map, List.mem_range] at hψ
    obtain ⟨j, -, rfl⟩ := hψ
    exact noSetVar_bigOr _ (by simp [Formula.NoSetVar])

theorem fits_psi : (psi d k).Fits (arities d k) 0 := by
  refine ⟨by simp [Formula.Fits, arities], fits_bigAnd _ _ _ (by simp [Formula.Fits, arities]),
    fits_bigAnd _ _ _ ?_, fits_bigAnd _ _ _ ?_⟩
  · intro φ hφ
    simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, -, j, -, rfl⟩ := hφ; trivial
  · intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨t, -, rfl⟩ := hφ
    have h1 : (Formula.rel 2 (vt d k t)).Fits (arities d k) 0 := by
      simp [Formula.Fits, arities, length_vt]
    have h2 : (Formula.rel 3 (vt d k t ++ yt k t)).Fits (arities d k) 0 := by
      simp only [Formula.Fits, arities, List.length_append, length_vt, length_yt]
      simp; omega
    refine ⟨h1, h2, fits_bigAnd _ _ _ fun ψ hψ => ?_⟩
    simp only [List.mem_map, List.mem_range] at hψ
    obtain ⟨j, -, rfl⟩ := hψ
    exact fits_bigOr _ _ _ (by simp [Formula.Fits])

theorem freeVars_psi : ∀ v ∈ (psi d k).freeVars, v < nv d k := by
  have hk : k + 1 ≤ nv d k := by unfold nv; omega
  have hn : 0 < nv d k := by omega
  intro v hv
  simp only [psi, Formula.freeVars, Finset.mem_union] at hv
  rcases hv with hv | hv | hv | hv
  · simp at hv; omega
  · refine freeVars_bigAnd hn _ (fun φ hφ w hw => ?_) v hv
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨i, hi, rfl⟩ := hφ
    simp [Formula.freeVars] at hw; omega
  · refine freeVars_bigAnd hn _ (fun φ hφ w hw => ?_) v hv
    simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, hi, j, hj, rfl⟩ := hφ
    simp [Formula.freeVars] at hw; omega
  · refine freeVars_bigAnd hn _ (fun φ hφ w hw => ?_) v hv
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨t, ht, rfl⟩ := hφ
    have hvt := vt_lt d k t
    simp only [clauseF, Formula.freeVars, Finset.mem_union, List.mem_toFinset,
      List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw
    · have := hvt w hw; omega
    · have := hvt w hw; omega
    · simp only [yt, List.mem_map, List.mem_range] at hw
      obtain ⟨j, hj, rfl⟩ := hw; exact yv_lt d k ht hj
    · refine freeVars_bigAnd hn _ (fun ψ hψ u hu => ?_) w hw
      simp only [List.mem_map, List.mem_range] at hψ
      obtain ⟨j, hj, rfl⟩ := hψ
      refine freeVars_bigOr hn _ (fun χ hχ u' hu' => ?_) u hu
      simp only [List.mem_map, List.mem_range] at hχ
      obtain ⟨i, hi, rfl⟩ := hχ
      simp only [Formula.freeVars, Finset.mem_insert, Finset.mem_singleton] at hu'
      rcases hu' with rfl | rfl
      · exact yv_lt d k ht hj
      · omega

theorem isSentence_phi : IsSentence (phi d k) :=
  isSentence_exBlock fun v hv => List.mem_range.mpr (freeVars_psi d k v hv)

theorem isSigma_phi : IsSigma 1 (phi d k) := isSigma_one_exBlock (isQF_psi d k) _

theorem noSetVar_phi : (phi d k).NoSetVar := (noSetVar_exBlock _ _).mpr (noSetVar_psi d k)

theorem fits_phi : (phi d k).Fits (arities d k) 0 := (fits_exBlock _ _ _ _).mpr (fits_psi d k)

/-! ### The meaning of the sentence -/

theorem sat_inS (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) (t j : ℕ) :
    Sat A S (inS k t j) ρ ↔ ∃ i < k + 1, ρ (yv k t j) = ρ i := by
  simp [inS, sat_bigOr, Sat]

theorem sat_psi (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) :
    Sat A S (psi d k) ρ ↔
      [ρ k] ∈ A.rel 0 ∧ (∀ i < k, [ρ i] ∈ A.rel 1) ∧ (∀ i < k, ∀ j < i, ρ i ≠ ρ j) ∧
      ∀ t < FF d k, (vt d k t).map ρ ∈ A.rel 2 →
        (vt d k t ++ yt k t).map ρ ∈ A.rel 3 ∧ ∀ j < k + 1, ∃ i < k + 1, ρ (yv k t j) = ρ i := by
  simp only [psi, Sat, sat_bigAnd, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, List.map_cons, List.map_nil]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · intro h i hi j hj; exact h _ ⟨i, hi, j, hj, rfl⟩
    · rintro h φ ⟨i, hi, j, hj, rfl⟩; exact h i hi j hj
  · refine forall_congr' fun t => forall_congr' fun _ => ?_
    simp only [clauseF, Sat, sat_bigAnd, List.mem_map, List.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sat_inS]
    tauto

/-! ### The size of the sentence -/

/-- The bound on the size of the sentence. -/
def gBound (k : ℕ) : ℕ := (2 * d + 60) * (k + 1) ^ 2 * ((k + 1) ^ (d + 1) + 1)

theorem computable_gBound : Computable (gBound d) := by
  open Lax496464Proofs.WHierarchy.ComputableBounds in
  have h1 : Computable fun k : ℕ => k + 1 := computable_add Computable.id (Computable.const 1)
  exact computable_mul (computable_mul (Computable.const _) (computable_pow 2 h1))
    (computable_add (computable_pow (d + 1) h1) (Computable.const 1))

theorem size_clauseF (t : ℕ) : (clauseF d k t).size ≤ (2 * d + 30) * (k + 1) ^ 2 := by
  have hin : ∀ j, (inS k t j).size ≤ 4 * (k + 1) + 4 := by
    intro j
    have := size_bigOr_le (s := 3) ((List.range (k + 1)).map fun i => Formula.eq (yv k t j) i)
      (by simp [Formula.size])
    simp only [List.length_map, List.length_range] at this
    unfold inS; omega
  have hand := size_bigAnd_le (s := 4 * (k + 1) + 4) ((List.range (k + 1)).map (inS k t))
    (by simp only [List.mem_map, List.mem_range]; rintro φ ⟨j, -, rfl⟩; exact hin j)
  simp only [List.length_map, List.length_range] at hand
  simp only [clauseF, Formula.size, List.length_append, length_vt, length_yt]
  have e1 : (k + 1) * (4 * (k + 1) + 4 + 1) ≤ 9 * (k + 1) ^ 2 := by nlinarith
  have e2 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e3 : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
  have e4 : 2 * d ≤ 2 * d * (k + 1) ^ 2 := by nlinarith
  have e5 : (2 * d + 30) * (k + 1) ^ 2 = 2 * d * (k + 1) ^ 2 + 30 * (k + 1) ^ 2 := by ring
  omega

theorem size_phi : (phi d k).size ≤ gBound d k := by
  have hF := one_le_FF d k
  set F := FF d k with hFdef
  have hC := size_bigAnd_le (s := 2) ((List.range k).map fun i => Formula.rel 1 [i])
    (by simp [Formula.size])
  have hD := size_bigAnd_le (s := 4) (distinctL k) (by
    intro φ hφ
    simp only [distinctL, List.mem_flatMap, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, -, j, -, rfl⟩ := hφ; simp [Formula.size])
  have hDl : (distinctL k).length ≤ k * k := by
    unfold distinctL
    rw [List.length_flatMap]
    calc ((List.range k).map fun i => ((List.range i).map fun j => Formula.neg (.eq i j)).length).sum
        ≤ ((List.range k).map fun _ => k).sum := List.sum_le_sum (by
          simp only [List.mem_range, List.length_map, List.length_range]; intro i hi; omega)
      _ = k * k := by simp
  have hE := size_bigAnd_le (s := (2 * d + 30) * (k + 1) ^ 2) ((List.range F).map (clauseF d k))
    (by simp only [List.mem_map, List.mem_range]; rintro φ ⟨t, -, rfl⟩; exact size_clauseF d k t)
  simp only [List.length_map, List.length_range] at hC hE
  unfold phi gBound
  rw [size_exBlock, List.length_range]
  simp only [psi, Formula.size, List.length_cons, List.length_nil]
  unfold nv
  rw [← hFdef]
  have e1 : (k + 1) ^ (d + 1) = F := rfl
  rw [e1]
  have hk2 : k * k ≤ (k + 1) ^ 2 := by nlinarith
  have hDl' := Nat.mul_le_mul_right 5 hDl
  have hFk : F * ((2 * d + 30) * (k + 1) ^ 2 + 1) ≤ F * ((2 * d + 31) * (k + 1) ^ 2) := by
    apply Nat.mul_le_mul_left; nlinarith
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula
