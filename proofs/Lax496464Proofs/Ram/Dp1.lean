import Lax496464Proofs.Ram.DpCore
import Lax496464Proofs.Section3
import Lax496464Proofs.Ram.EstPermute

/-!
# The dynamic program for one machine

With a single machine a set of thresholds is `∅` or one job, so the table of Section 3 is an
array `T[j][W']` for `j = 0 … n` and `W' = 0 … n` (`j = n` standing for `∅`). This file is
that table as a function of natural numbers and the proof that it is Section 3's:
`dpK k j W'` codes, in the sense of `DpCore.Rep`, the predicate "a set of weight `W'` compatible
with the threshold `j` can be preprocessed from `P'`". The jobs are in earliest-start-time
order with unit weights and positive processing times, and `nxt j` is the paper's `j₂`.
-/

namespace Lax496464Proofs.Ram.Dp1

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore

variable (J : Instance)

/-- The threshold `j`, or no threshold at all once `j` is past the last job. -/
def Xj (j : ℕ) : Finset J.Job := if h : j < J.jobs then {⟨j, h⟩} else ∅

variable {J}

theorem Xj_of_le {j : ℕ} (h : J.jobs ≤ j) : Xj J j = ∅ := by
  unfold Xj; rw [dif_neg (by omega)]

theorem Xj_of_lt {j : ℕ} (h : j < J.jobs) : Xj J j = {⟨j, h⟩} := by
  unfold Xj; rw [dif_pos h]

/-- Nothing with positive weight is compatible with no threshold. -/
theorem achievable_empty (W' : ℕ) (P' : ℤ) :
    Achievable J ∅ W' P' ↔ W' = 0 := by
  constructor
  · rintro ⟨Z, hw, ⟨mach, hm, -, -⟩, -⟩
    have : Z = ∅ := by
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact absurd (hm j hj) (Finset.notMem_empty _)
    subst this
    simpa [weight] using hw.symm
  · rintro rfl
    refine ⟨∅, by simp [weight], ⟨fun j => j, by simp, by simp, by simp⟩, by simp [PreprocessableFrom]⟩

/-- Weight zero is always achievable. -/
theorem achievable_zero (X : Finset J.Job) (P' : ℤ) : Achievable J X 0 P' :=
  ⟨∅, by simp [weight], ⟨fun j => j, by simp, by simp, by simp⟩, by simp [PreprocessableFrom]⟩

/-- Passing over the threshold `j` leaves the threshold `j + 1`. -/
theorem X1_singleton (j : ℕ) (h : j < J.jobs) : X1 J (Xj J j) ⟨j, h⟩ = Xj J (j + 1) := by
  unfold X1 j1
  rw [Xj_of_lt h]
  let := Classical.decPred fun x : J.Job => x ∉ ({⟨j, h⟩} : Finset J.Job) ∧ (⟨j, h⟩ : J.Job) < x
  split_ifs with hne
  · have hmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
    have hjm : j < ((Finset.min' _ hne : J.Job) : ℕ) := by
      have := hmem.2.2
      exact this
    have hn : j + 1 < J.jobs := by
      have := (Finset.min' _ hne : J.Job).isLt; omega
    have hle : (Finset.min' _ hne : J.Job) ≤ (⟨j + 1, hn⟩ : J.Job) :=
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro hh; have := Finset.mem_singleton.mp hh; simp [Fin.ext_iff] at this,
        show j < j + 1 from Nat.lt_succ_self j⟩)
    have hm : (Finset.min' _ hne : J.Job) = ⟨j + 1, hn⟩ := by
      apply le_antisymm hle
      exact Fin.mk_le_of_le_val (by omega)
    rw [hm, Xj_of_lt hn]
    ext x
    simp [Fin.ext_iff]
  · rw [Xj_of_le]
    · simp
    · by_contra hn
      apply hne
      exact ⟨⟨j + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro hh; have := Finset.mem_singleton.mp hh; simp [Fin.ext_iff] at this,
        show j < j + 1 from Nat.lt_succ_self j⟩⟩

/-- `y` is the paper's `j₂` of job `j`: the first job whose second operation starts at or after
`d j`, or `n` if there is none. -/
def IsNxt (j : ℕ) (h : j < J.jobs) (y : ℕ) : Prop :=
  ((∃ hy : y < J.jobs, (J.d ⟨j, h⟩ : ℤ) ≤ s (⟨y, hy⟩ : J.Job)) ∨ y = J.jobs) ∧
    ∀ x : J.Job, (x : ℕ) < y → s x < (J.d ⟨j, h⟩ : ℤ)

/-- Selecting the threshold `j` leaves the threshold `j₂`. -/
theorem X2_singleton (hq : ∀ j : J.Job, 0 < J.q j) (j : ℕ) (h : j < J.jobs) (y : ℕ)
    (hy : IsNxt j h y) : X2 J (Xj J j) ⟨j, h⟩ = Xj J y := by
  have hsj : s (⟨j, h⟩ : J.Job) < (J.d ⟨j, h⟩ : ℤ) := by
    have := hq ⟨j, h⟩
    unfold s; omega
  unfold X2 j2
  rw [Xj_of_lt h]
  let := Classical.decPred fun x : J.Job =>
    x ∉ ({⟨j, h⟩} : Finset J.Job) ∧ (J.d ⟨j, h⟩ : ℤ) ≤ s x
  split_ifs with hne
  · have hmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
    have hd : (J.d ⟨j, h⟩ : ℤ) ≤ s (Finset.min' _ hne : J.Job) := hmem.2.2
    have hyn : y < J.jobs := by
      rcases hy.1 with ⟨hyn, -⟩ | rfl
      · exact hyn
      · exfalso
        have := (Finset.min' _ hne : J.Job).isLt
        have := hy.2 _ this
        linarith
    have hyd : (J.d ⟨j, h⟩ : ℤ) ≤ s (⟨y, hyn⟩ : J.Job) := by
      rcases hy.1 with ⟨hyn', hd'⟩ | rfl
      · exact hd'
      · omega
    have hle : (Finset.min' _ hne : J.Job) ≤ (⟨y, hyn⟩ : J.Job) :=
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro hh
        have := Finset.mem_singleton.mp hh
        rw [Fin.ext_iff] at this
        have hyj : y = j := this
        subst hyj
        linarith, hyd⟩)
    have hge : (⟨y, hyn⟩ : J.Job) ≤ (Finset.min' _ hne : J.Job) := by
      by_contra hlt
      have hlt' : ((Finset.min' _ hne : J.Job) : ℕ) < y := by
        rw [not_le, Fin.lt_def] at hlt; exact hlt
      have := hy.2 _ hlt'
      linarith
    have hm : (Finset.min' _ hne : J.Job) = ⟨y, hyn⟩ := le_antisymm hle hge
    rw [hm, Xj_of_lt hyn]
    ext x
    simp [Fin.ext_iff]
  · have hyn : y = J.jobs := by
      rcases hy.1 with ⟨hyn, hyd⟩ | hy'
      · exfalso
        apply hne
        refine ⟨⟨y, hyn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hyd⟩⟩
        intro hh
        have := Finset.mem_singleton.mp hh
        rw [Fin.ext_iff] at this
        have hyj : y = j := this
        subst hyj
        linarith
      · exact hy'
    rw [Xj_of_le (by omega)]
    simp

/-! ## The table -/

/-- The preprocessing time of job `j`; zero past the last job. -/
def pv (J : Instance) (j : ℕ) : ℕ := if h : j < J.jobs then J.p ⟨j, h⟩ else 0

/-- The start time of job `j`; zero past the last job. -/
def sv (J : Instance) (j : ℕ) : ℤ := if h : j < J.jobs then s (⟨j, h⟩ : J.Job) else 0

/-- The processing time of job `j`; zero past the last job. -/
def qv (J : Instance) (j : ℕ) : ℕ := if h : j < J.jobs then J.q ⟨j, h⟩ else 0

/-- The due date of job `j`; zero past the last job. -/
def dv (J : Instance) (j : ℕ) : ℕ := if h : j < J.jobs then J.d ⟨j, h⟩ else 0

/-- The table: `dpK k j W'` is the code of the entry `T[j, W']`, correct whenever
`n ≤ j + k`. -/
def dpK (J : Instance) (inf : ℕ) (nxt : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, W' => if W' = 0 then inf else 0
  | k + 1, j, W' =>
    if J.jobs ≤ j then (if W' = 0 then inf else 0)
    else if W' = 0 then inf
    else max (dpK J inf nxt k (j + 1) W')
      (stepF inf (dpK J inf nxt k (nxt j) (W' - 1)) (sv J j) (pv J j))

theorem stepF_le {inf t : ℕ} (s : ℤ) (p : ℕ) (hs : s + 1 < inf) (hi : 1 < inf) :
    stepF inf t s p ≤ inf := by
  unfold stepF
  split_ifs with h0 h1 h2 <;> omega

/-- `j₂` comes after `j`. -/
theorem nxt_gt (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {j : ℕ} (h : j < J.jobs)
    {y : ℕ} (hy : IsNxt j h y) : j < y := by
  rcases hy.1 with ⟨hyn, hd⟩ | rfl
  · by_contra hle
    have hle' : (⟨y, hyn⟩ : J.Job) ≤ ⟨j, h⟩ := Fin.mk_le_mk.mpr (by omega)
    have h1 := hest _ _ hle'
    have := hq ⟨j, h⟩
    unfold s at h1 hd; omega
  · exact h

/-- Recursion (1) at a single threshold, with unit weights. -/
theorem ach_rec (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hw : ∀ j : J.Job, J.w j = 1)
    {j : ℕ} (h : j < J.jobs) {y : ℕ} (hy : IsNxt j h y) (W1 : ℕ) (P' : ℤ) :
    Achievable J (Xj J j) (W1 + 1) P' ↔
      Achievable J (Xj J (j + 1)) (W1 + 1) P' ∨
        (P' + (pv J j : ℤ) ≤ sv J j ∧ Achievable J (Xj J y) W1 (P' + (pv J j : ℤ))) := by
  have hr := Lax496464Proofs.Section3.achievable_recursion J hest hq
    (X := Xj J j) (j := ⟨j, h⟩) (by rw [Xj_of_lt h]; simp)
    (by rw [Xj_of_lt h]; intro x hx; rw [Finset.mem_singleton.mp hx]) (W1 + 1) P'
  rw [X1_singleton j h, X2_singleton hq j h y hy, hw, Nat.add_sub_cancel] at hr
  rw [hr]
  have hp : (J.p ⟨j, h⟩ : ℤ) = (pv J j : ℤ) := by unfold pv; rw [dif_pos h]
  have hs : s (⟨j, h⟩ : J.Job) = sv J j := by unfold sv; rw [dif_pos h]
  rw [hp, hs]
  simp

theorem dpK_rep (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hw : ∀ j : J.Job, J.w j = 1)
    (inf : ℕ) (hi1 : 1 < inf) (hinf : ∀ j : J.Job, s j + 1 < inf) (nxt : ℕ → ℕ)
    (hnxt : ∀ (j : ℕ) (h : j < J.jobs), IsNxt j h (nxt j)) :
    ∀ (k j W' : ℕ), J.jobs ≤ j + k →
      Rep inf (dpK J inf nxt k j W') (fun P' => Achievable J (Xj J j) W' P') := by
  intro k
  induction k with
  | zero =>
    intro j W' hj
    unfold dpK
    rw [Xj_of_le (by omega)]
    by_cases hW : W' = 0
    · subst hW; simp only [if_true]
      exact Or.inr (Or.inl ⟨rfl, fun P' _ => (achievable_empty 0 P').mpr rfl⟩)
    · simp only [hW, if_false]
      exact Or.inl ⟨rfl, fun P' _ hq' => hW ((achievable_empty W' P').mp hq')⟩
  | succ k ih =>
    intro j W' hj
    unfold dpK
    by_cases hjn : J.jobs ≤ j
    · simp only [hjn, if_true]
      rw [Xj_of_le hjn]
      by_cases hW : W' = 0
      · subst hW; simp only [if_true]
        exact Or.inr (Or.inl ⟨rfl, fun P' _ => (achievable_empty 0 P').mpr rfl⟩)
      · simp only [hW, if_false]
        exact Or.inl ⟨rfl, fun P' _ hq' => hW ((achievable_empty W' P').mp hq')⟩
    · have hjlt : j < J.jobs := by omega
      simp only [hjn, if_false]
      by_cases hW : W' = 0
      · subst hW; simp only [if_true]
        exact Or.inr (Or.inl ⟨rfl, fun P' _ => achievable_zero _ P'⟩)
      · simp only [hW, if_false]
        obtain ⟨W1, rfl⟩ : ∃ W1, W' = W1 + 1 := ⟨W' - 1, by omega⟩
        have hgt := nxt_gt hest hq hjlt (hnxt j hjlt)
        have ih1 := ih (j + 1) (W1 + 1) (by omega)
        have ih2 := ih (nxt j) (W1 + 1 - 1) (by omega)
        have hsj : sv J j + 1 < inf := by
          unfold sv; rw [dif_pos hjlt]; exact hinf _
        have hst := stepF_rep (sv J j) (pv J j) hsj hi1 ih2
        have hmx := max_rep (stepF_le (t := dpK J inf nxt k (nxt j) (W1 + 1 - 1)) (sv J j) (pv J j) hsj hi1) ih1 hst
        refine hmx.congr fun P' hP => ?_
        rw [ach_rec hest hq hw hjlt (hnxt j hjlt) W1 P']
        simp only [Nat.add_sub_cancel]

theorem firstM_eq_Xj (hm : J.machines = 1) : firstM J = Xj J 0 := by
  unfold firstM Xj
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hm]
  by_cases h0 : 0 < J.jobs
  · rw [dif_pos h0]
    simp [Fin.ext_iff]
  · rw [dif_neg h0]
    have := x.isLt
    omega

theorem rep_nonzero {inf t : ℕ} {Q : ℤ → Prop} (h : Rep inf t Q) (hi : 0 < inf) :
    t ≠ 0 ↔ ∃ P' : ℤ, 0 ≤ P' ∧ Q P' := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨v, h0, h1, h2, h3⟩
  · constructor
    · intro h; exact absurd h0 h
    · rintro ⟨P, hP, hq⟩; exact absurd hq (h1 P hP)
  · exact ⟨fun _ => ⟨0, le_rfl, h1 0 le_rfl⟩, fun _ => by omega⟩
  · exact ⟨fun _ => ⟨0, le_rfl, (h3 0 le_rfl).mpr (by omega)⟩, fun _ => h2⟩

/-- **The answer, read off the table.** A feasible set of weight at least `W` exists exactly
when some entry `T[0, W'']`, `W ≤ W'' ≤ n`, is not `−∞`. -/
theorem hasWeight_iff_dp (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j)
    (hw : ∀ j : J.Job, J.w j = 1) (hm : J.machines = 1) (inf : ℕ) (hi1 : 1 < inf)
    (hinf : ∀ j : J.Job, s j + 1 < inf) (nxt : ℕ → ℕ)
    (hnxt : ∀ (j : ℕ) (h : j < J.jobs), IsNxt j h (nxt j)) (W : ℕ) :
    HasWeight J W ↔ ∃ W'', W ≤ W'' ∧ W'' ≤ J.jobs ∧ dpK J inf nxt J.jobs 0 W'' ≠ 0 := by
  have hrep : ∀ W'', Rep inf (dpK J inf nxt J.jobs 0 W'')
      (fun P' => Achievable J (Xj J 0) W'' P') := fun W'' =>
    dpK_rep hest hq hw inf hi1 hinf nxt hnxt J.jobs 0 W'' (by omega)
  have hread := fun W'' => Lax496464Proofs.Section3.achievable_readoff J hest W''
  simp only [firstM_eq_Xj hm] at hread
  have hwt : ∀ Z : Finset J.Job, weight J Z = Z.card := fun Z => by
    unfold weight; simp [hw]
  constructor
  · rintro ⟨Z, hZ, hW⟩
    refine ⟨weight J Z, hW, ?_, ?_⟩
    · rw [hwt]; simpa using Finset.card_le_univ Z
    · rw [rep_nonzero (hrep _) (by omega)]
      exact (hread _).mpr ⟨Z, hZ, rfl⟩
  · rintro ⟨W'', hW, -, hne⟩
    rw [rep_nonzero (hrep _) (by omega)] at hne
    obtain ⟨Z, hZ, hwZ⟩ := (hread _).mp hne
    exact ⟨Z, hZ, by omega⟩

/-! ## The column form, in natural numbers only -/

/-- The recursion's second branch, unrolled in natural numbers: the code of the instants
`P'` with `P' + p ≤ d − q` and `Q₂ (P' + p)`, from the code `t₂` of `Q₂`. -/
def fNat (inf t₂ d q p : ℕ) : ℕ :=
  if t₂ = 0 then 0
  else if t₂ = inf then (if p + q ≤ d then d - q - p + 1 else 0)
  else if p + 1 ≤ t₂ ∧ p + q ≤ d then min (t₂ - 1 - p) (d - q - p) + 1 else 0

theorem fNat_eq_stepF (inf t₂ d q p : ℕ) :
    fNat inf t₂ d q p = stepF inf t₂ ((d : ℤ) - q) p := by
  unfold fNat stepF
  by_cases h0 : t₂ = 0
  · simp [h0]
  by_cases h1 : t₂ = inf
  · subst h1
    simp only [h0, if_true, if_false]
    by_cases hp : p + q ≤ d
    · rw [if_pos hp, if_pos (by omega)]; omega
    · rw [if_neg hp, if_neg (by omega)]
  · simp only [h0, h1, if_false]
    by_cases hp : p + 1 ≤ t₂ ∧ p + q ≤ d
    · rw [if_pos hp, if_pos (by omega)]; omega
    · rw [if_neg hp, if_neg (by omega)]

/-- One column of the table from the column before it, by recursion downward from the end:
`colStep … prev j = T[j, W']` when `prev = T[·, W' − 1]`. -/
def colStep (n inf : ℕ) (nxt pF qF dF : ℕ → ℕ) (prev : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : n ≤ j then 0
  else max (colStep n inf nxt pF qF dF prev (j + 1))
    (fNat inf (prev (nxt j)) (dF j) (qF j) (pF j))
termination_by n - j

theorem colStep_of_le {n inf : ℕ} {nxt pF qF dF prev : ℕ → ℕ} {j : ℕ} (h : n ≤ j) :
    colStep n inf nxt pF qF dF prev j = 0 := by
  rw [colStep, dif_pos h]

theorem colStep_of_lt {n inf : ℕ} {nxt pF qF dF prev : ℕ → ℕ} {j : ℕ} (h : j < n) :
    colStep n inf nxt pF qF dF prev j =
      max (colStep n inf nxt pF qF dF prev (j + 1))
        (fNat inf (prev (nxt j)) (dF j) (qF j) (pF j)) := by
  rw [colStep, dif_neg (by omega)]

/-- All the columns: column `0` is `+∞` throughout; each next column is `colStep`. -/
def colAll (n inf : ℕ) (nxt pF qF dF : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => inf
  | W1 + 1 => colStep n inf nxt pF qF dF (colAll n inf nxt pF qF dF W1)

/-- The table, by columns, is the table by fuel. -/
theorem dpK_eq_colAll (nxt : ℕ → ℕ) (inf : ℕ) (hnx : ∀ j, j < J.jobs → j < nxt j) :
    ∀ (k W' j : ℕ), J.jobs ≤ j + k →
      dpK J inf nxt k j W' =
        colAll J.jobs inf nxt (pv J) (fun j => if h : j < J.jobs then J.q ⟨j, h⟩ else 0)
          (fun j => if h : j < J.jobs then J.d ⟨j, h⟩ else 0) W' j := by
  intro k
  induction k with
  | zero =>
    intro W' j hj
    unfold dpK
    cases W' with
    | zero => simp [colAll]
    | succ W1 =>
      simp only [colAll, colStep_of_le (show J.jobs ≤ j by omega)]
      simp
  | succ k ih =>
    intro W' j hj
    cases W' with
    | zero => unfold dpK; by_cases h : J.jobs ≤ j <;> simp [h, colAll]
    | succ W1 =>
      unfold dpK
      by_cases hjn : J.jobs ≤ j
      · simp only [hjn, if_true, colAll, colStep_of_le hjn]; simp
      · have hjlt : j < J.jobs := by omega
        simp only [hjn, if_false, Nat.succ_ne_zero, colAll]
        rw [colStep_of_lt hjlt, ih (W1 + 1) (j + 1) (by omega), Nat.add_sub_cancel,
          ih W1 (nxt j) (by have := hnx j hjlt; omega), fNat_eq_stepF]
        simp only [colAll]
        unfold sv pv
        simp only [dif_pos hjlt]
        rfl

end Lax496464Proofs.Ram.Dp1
