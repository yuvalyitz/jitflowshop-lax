import Lax496464Proofs.Ram.D2Count
import Lax496464Proofs.Ram.Dp1

/-!
# Theorem 2, pure layer 5: the table's entries mean what Section 3 says

The table `T[X, W']` here is the *monotone* form of Section 3's: the latest instant from which a set
of weight **at least** `W'` compatible with `X` can be preprocessed (`AchGe`).  Recursion (1) turns
into `T[X, W'] = max(T[X₁, W'], f(T[X₂, W' ∸ w_j]))` with a truncated subtraction, which is what lets
the table have only `W + 1` rows whatever the weights are.  `X₁` and `X₂` are, on thresholds written
as strictly increasing lists, `newL` of the scan of `scanF` (`X1_ofList`, `X2_ofList`).
-/

namespace Lax496464Proofs.Ram.D2Ach

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.Dp1 (IsNxt nxt_gt fNat fNat_eq_stepF)

variable {J : Instance}

/-- The jobs whose number occurs in `L`. -/
def ofList (J : Instance) (L : List ℕ) : Finset J.Job :=
  Finset.univ.filter (fun j => (j : ℕ) ∈ L)

theorem mem_ofList {L : List ℕ} {x : J.Job} : x ∈ ofList J L ↔ (x : ℕ) ∈ L := by
  simp [ofList]

theorem ofList_nil : ofList J [] = ∅ := by
  ext x; simp [ofList]

/-- A set of weight at least `W'` compatible with `X` can be preprocessed from `P'`. -/
def AchGe (J : Instance) (X : Finset J.Job) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ W'', W' ≤ W'' ∧ Achievable J X W'' P'

theorem achGe_empty (W' : ℕ) (P' : ℤ) : AchGe J ∅ W' P' ↔ W' = 0 := by
  constructor
  · rintro ⟨W'', hW, h⟩
    have := (Dp1.achievable_empty W'' P').mp h
    omega
  · rintro rfl
    exact ⟨0, le_rfl, (Dp1.achievable_empty 0 P').mpr rfl⟩

/-- **Recursion (1), for the monotone table.** -/
theorem achGe_rec (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) (W' : ℕ) (P' : ℤ) :
    AchGe J X W' P' ↔ AchGe J (X1 J X j) W' P' ∨
      (P' + (J.p j : ℤ) ≤ s j ∧ AchGe J (X2 J X j) (W' - J.w j) (P' + J.p j)) := by
  have hrec := fun W'' => Lax496464Proofs.Section3.achievable_recursion J hest hq hjX hjmin W'' P'
  constructor
  · rintro ⟨W'', hW, hach⟩
    rcases (hrec W'').mp hach with h | ⟨hw, hp, h2⟩
    · exact Or.inl ⟨W'', hW, h⟩
    · exact Or.inr ⟨hp, W'' - J.w j, by omega, h2⟩
  · rintro (⟨W'', hW, h⟩ | ⟨hp, V, hV, h2⟩)
    · exact ⟨W'', hW, (hrec W'').mpr (Or.inl h)⟩
    · refine ⟨V + J.w j, by omega, (hrec _).mpr (Or.inr ⟨by omega, hp, ?_⟩)⟩
      rw [Nat.add_sub_cancel]; exact h2

/-! ## `X₁` and `X₂` on lists -/

/-- `j₁` is the first free index above `j`, when `cur` is one. -/
theorem j1_spec (X : Finset J.Job) (j : J.Job) (cur : ℕ) (hge : (j : ℕ) + 1 ≤ cur)
    (hnot : ∀ hc : cur < J.jobs, (⟨cur, hc⟩ : J.Job) ∉ X)
    (hcov : ∀ x : J.Job, (j : ℕ) + 1 ≤ x → (x : ℕ) < cur → x ∈ X) :
    j1 J X j = if hc : cur < J.jobs then some ⟨cur, hc⟩ else none := by
  unfold j1
  let := Classical.decPred fun x : J.Job => x ∉ X ∧ j < x
  by_cases hc : cur < J.jobs
  · rw [dif_pos hc]
    have hmem : (⟨cur, hc⟩ : J.Job) ∈ Finset.univ.filter (fun x : J.Job => x ∉ X ∧ j < x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot hc, by rw [Fin.lt_def]; exact hge⟩
    have hne : (Finset.univ.filter fun x : J.Job => x ∉ X ∧ j < x).Nonempty := ⟨_, hmem⟩
    rw [dif_pos hne]
    congr 1
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem
    · have hm := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      by_contra hlt
      have h1 : ((Finset.min' _ hne : J.Job) : ℕ) < cur := by
        rw [not_le, Fin.lt_def] at hlt; exact hlt
      have h2 := hm.2.2
      rw [Fin.lt_def] at h2
      exact hm.2.1 (hcov _ (by omega) h1)
  · rw [dif_neg hc, dif_neg]
    intro hne
    obtain ⟨x, hx⟩ := hne
    have hx' := Finset.mem_filter.mp hx
    have h1 := x.isLt
    have h2 := hx'.2.2
    rw [Fin.lt_def] at h2
    exact hx'.2.1 (hcov x (by omega) (by omega))

/-- `j₂` is the first free index from `y0` on, when `y0` is where the start times clear `d j`. -/
theorem j2_spec (X : Finset J.Job) (j : J.Job) (y0 cur : ℕ) (hge : y0 ≤ cur)
    (hQ : ∀ x : J.Job, ((J.d j : ℤ) ≤ s x ↔ y0 ≤ (x : ℕ)))
    (hnot : ∀ hc : cur < J.jobs, (⟨cur, hc⟩ : J.Job) ∉ X)
    (hcov : ∀ x : J.Job, y0 ≤ (x : ℕ) → (x : ℕ) < cur → x ∈ X) :
    j2 J X j = if hc : cur < J.jobs then some ⟨cur, hc⟩ else none := by
  unfold j2
  let := Classical.decPred fun x : J.Job => x ∉ X ∧ (J.d j : ℤ) ≤ s x
  by_cases hc : cur < J.jobs
  · rw [dif_pos hc]
    have hmem : (⟨cur, hc⟩ : J.Job) ∈
        Finset.univ.filter (fun x : J.Job => x ∉ X ∧ (J.d j : ℤ) ≤ s x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot hc, (hQ _).mpr hge⟩
    have hne : (Finset.univ.filter fun x : J.Job => x ∉ X ∧ (J.d j : ℤ) ≤ s x).Nonempty :=
      ⟨_, hmem⟩
    rw [dif_pos hne]
    congr 1
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem
    · have hm := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      by_contra hlt
      have h1 : ((Finset.min' _ hne : J.Job) : ℕ) < cur := by
        rw [not_le, Fin.lt_def] at hlt; exact hlt
      exact hm.2.1 (hcov _ ((hQ _).mp hm.2.2) h1)
  · rw [dif_neg hc, dif_neg]
    intro hne
    obtain ⟨x, hx⟩ := hne
    have hx' := Finset.mem_filter.mp hx
    have h1 := x.isLt
    exact hx'.2.1 (hcov x ((hQ _).mp hx'.2.2) (by omega))

theorem erase_ofList {j : ℕ} {Zs : List ℕ} (hjn : j < J.jobs) (hjZ : ∀ z ∈ Zs, j < z) :
    (ofList J (j :: Zs)).erase ⟨j, hjn⟩ = ofList J Zs := by
  ext x
  simp only [Finset.mem_erase, mem_ofList, List.mem_cons]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd (Fin.ext h2) h1
    · exact h2
  · intro h
    refine ⟨fun hx => ?_, Or.inr h⟩
    have h3 := hjZ _ h
    have h4 : (x : ℕ) = j := congrArg Fin.val hx
    omega

theorem ofList_newL {Zs : List ℕ} {cur k : ℕ} :
    ofList J (newL J.jobs Zs cur k) =
      if hc : cur < J.jobs then insert ⟨cur, hc⟩ (ofList J Zs) else ofList J Zs := by
  unfold newL
  by_cases hc : cur < J.jobs
  · rw [if_pos hc, dif_pos hc]
    ext x
    simp only [Finset.mem_insert, mem_ofList, mem_ins, Fin.ext_iff]
  · rw [if_neg hc, dif_neg hc]

theorem X1_ofList {j : ℕ} {Zs : List ℕ} (hjn : j < J.jobs) (hjZ : ∀ z ∈ Zs, j < z)
    {cur k : ℕ} (hr : ScanOK J.jobs Zs (j + 1) (cur, k)) :
    X1 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur k) := by
  have hnot : ∀ hc : cur < J.jobs, (⟨cur, hc⟩ : J.Job) ∉ ofList J (j :: Zs) := by
    intro hc h
    rw [mem_ofList] at h
    rcases List.mem_cons.mp h with h | h
    · have := hr.ge; simp only at h this; omega
    · exact hr.notMem h
  have hcov : ∀ x : J.Job, ((⟨j, hjn⟩ : J.Job) : ℕ) + 1 ≤ x → (x : ℕ) < cur →
      x ∈ ofList J (j :: Zs) := fun x h1 h2 =>
    mem_ofList.mpr (List.mem_cons_of_mem _ (hr.cover x h1 h2))
  unfold X1
  rw [j1_spec _ _ cur hr.ge hnot hcov, ofList_newL, erase_ofList hjn hjZ]
  by_cases hc : cur < J.jobs
  · rw [dif_pos hc, dif_pos hc]
  · rw [dif_neg hc, dif_neg hc]

theorem X2_ofList {j : ℕ} {Zs : List ℕ} (hjn : j < J.jobs) (hjZ : ∀ z ∈ Zs, j < z)
    (hest : EstOrdered J) {y0 : ℕ} (hnx : IsNxt j hjn y0)
    {cur k : ℕ} (hr : ScanOK J.jobs Zs y0 (cur, k)) (hjy : j < y0) :
    X2 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur k) := by
  have hQ : ∀ x : J.Job, ((J.d ⟨j, hjn⟩ : ℤ) ≤ s x ↔ y0 ≤ (x : ℕ)) := by
    intro x
    constructor
    · intro h
      by_contra hlt
      have := hnx.2 x (by omega)
      omega
    · intro h
      rcases hnx.1 with ⟨hy, hd⟩ | rfl
      · have hle : (⟨y0, hy⟩ : J.Job) ≤ x := Fin.mk_le_mk.mpr h
        have := hest _ _ hle
        omega
      · have := x.isLt; omega
  have hnot : ∀ hc : cur < J.jobs, (⟨cur, hc⟩ : J.Job) ∉ ofList J (j :: Zs) := by
    intro hc h
    rw [mem_ofList] at h
    rcases List.mem_cons.mp h with h | h
    · have := hr.ge; simp only at h; omega
    · exact hr.notMem h
  have hcov : ∀ x : J.Job, y0 ≤ (x : ℕ) → (x : ℕ) < cur → x ∈ ofList J (j :: Zs) :=
    fun x h1 h2 => mem_ofList.mpr (List.mem_cons_of_mem _ (hr.cover x h1 h2))
  unfold X2
  rw [j2_spec _ _ y0 cur hr.ge hQ hnot hcov, ofList_newL, erase_ofList hjn hjZ]
  by_cases hc : cur < J.jobs
  · rw [dif_pos hc, dif_pos hc]
  · rw [dif_neg hc, dif_neg hc]

/-! ## One cell of the table -/

/-- **The recursion on codes.** If the entries for `X₁` and `X₂` are right, the entry for `X` is
the larger of the first and the image of the second under the job's `f`. -/
theorem cell_rep (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {inf : ℕ} (hi1 : 1 < inf)
    (hinf : ∀ j : J.Job, s j + 1 < inf) {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X)
    (hjmin : ∀ x ∈ X, j ≤ x) (W' t1 t2 : ℕ)
    (h1 : Rep inf t1 (fun P' => AchGe J (X1 J X j) W' P'))
    (h2 : Rep inf t2 (fun P' => AchGe J (X2 J X j) (W' - J.w j) P')) :
    Rep inf (max t1 (fNat inf t2 (J.d j) (J.q j) (J.p j))) (fun P' => AchGe J X W' P') := by
  have hsj : s j + 1 < inf := hinf j
  have hst := stepF_rep (s j) (J.p j) hsj hi1 h2
  have hf : stepF inf t2 (s j) (J.p j) ≤ inf := Dp1.stepF_le (s j) (J.p j) hsj hi1
  have hmx := max_rep hf h1 hst
  rw [fNat_eq_stepF]
  refine hmx.congr (fun P' hP => ?_)
  exact (achGe_rec hest hq hjX hjmin W' P').symm

end Lax496464Proofs.Ram.D2Ach
