import Lax496464Proofs.Ram.D2Tab

/-!
# Corollaries 2 and 3, pure layer 1: the dual table

The primal table of Theorem 2 records, for a weight `W'`, the latest instant `P'` from which a set
of weight `W'` compatible with `X` can be preprocessed.  The dual table records, for an instant `t`,
the largest weight attainable from it:

    `dualVal J X t = max { w(Z) | Z compatible with X, preprocessable from the instant t }`.

Here `t` is the instant at which the first-stage machine is free to begin, i.e. the paper's `P'`
(`PreprocessableFrom Z (t : ℤ)`).  Preprocessing from `0` is the read-off, and every recursive call
`(X₂, t + p_j)` starts at a partial sum of preprocessing times, so the rows that matter are
`t ≤ P = Σ p_j`.  `AchGe X W' t ↔ W' ≤ dualVal X t` (`le_dualVal_iff`): the dual is the same
predicate with its two numerical arguments exchanged.

The table the machine stores is *capped* at the threshold `W`: `dcap W X t = min W (dualVal X t)`,
so entries never exceed `W` and the weights (arbitrary numbers) never leave the word.

* recursion: `dcap_rec`, `dStep`/`dcell` (one cell from `(X₁, t)` and `(X₂, t + p_j)`);
* base case: `dcap_empty` (the row block of `∅` is all zero, so needs no initialisation);
* read-off: `hasWeight_iff_dcap : HasWeight J W ↔ dcap W (firstM J) 0 = W`;
* the guard `t + p_j ≤ R` of the machine is redundant on the *good* cells `GoodF J R X t`, which is
  what `(firstM, 0)` reaches (`goodF_firstM`, `goodF_X1`, `goodF_X2`).
-/

namespace Lax496464Proofs.Ram.D3Dual

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464.WordEncoding Lax496464.Problems
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.Dp1 (IsNxt)

variable {J : Instance}

open Classical in
/-- **The dual table's value.**  The largest weight of a set compatible with `X` that can be
preprocessed starting at the instant `t`. -/
noncomputable def dualVal (J : Instance) (X : Finset J.Job) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun Z : Finset J.Job =>
    CompatibleWith J X Z ∧ PreprocessableFrom J Z (t : ℤ)).sup (weight J)

/-- **The table the machine stores:** the dual value capped at the threshold `W`. -/
noncomputable def dcap (J : Instance) (W : ℕ) (X : Finset J.Job) (t : ℕ) : ℕ :=
  min W (dualVal J X t)

theorem le_dualVal_iff (X : Finset J.Job) (t W' : ℕ) :
    W' ≤ dualVal J X t ↔ AchGe J X W' (t : ℤ) := by
  classical
  by_cases h0 : W' = 0
  · subst h0
    exact ⟨fun _ => ⟨0, le_rfl, Dp1.achievable_zero X _⟩, fun _ => Nat.zero_le _⟩
  · unfold dualVal
    rw [Finset.le_sup_iff (Nat.pos_of_ne_zero h0 : (⊥ : ℕ) < W')]
    constructor
    · rintro ⟨Z, hZ, hle⟩
      rw [Finset.mem_filter] at hZ
      exact ⟨weight J Z, hle, Z, rfl, hZ.2.1, hZ.2.2⟩
    · rintro ⟨W'', hW, Z, hw, hc, hp⟩
      exact ⟨Z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hp⟩, by omega⟩

/-- The row block of the empty set of thresholds is zero. -/
theorem dualVal_empty (t : ℕ) : dualVal J ∅ t = 0 := by
  have h := (le_dualVal_iff (∅ : Finset J.Job) t (dualVal J ∅ t)).mp le_rfl
  exact (achGe_empty _ _).mp h

theorem dcap_empty (W t : ℕ) : dcap J W ∅ t = 0 := by
  unfold dcap; rw [dualVal_empty]; simp

/-! ## The recursion -/

/-- **Recursion (1), dual form, uncapped.** -/
theorem dualVal_rec (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) (t : ℕ) :
    dualVal J X t = max (dualVal J (X1 J X j) t)
      (if t + J.p j + J.q j ≤ J.d j then J.w j + dualVal J (X2 J X j) (t + J.p j) else 0) := by
  refine eq_of_forall_le_iff fun W' => ?_
  have hX2 : ∀ V, AchGe J (X2 J X j) V ((t : ℤ) + J.p j) ↔
      V ≤ dualVal J (X2 J X j) (t + J.p j) := by
    intro V
    rw [le_dualVal_iff]
    push_cast
    exact Iff.rfl
  rw [le_dualVal_iff, achGe_rec hest hq hjX hjmin W' (t : ℤ), ← le_dualVal_iff (X1 J X j) t W',
    le_max_iff, hX2]
  by_cases hg : t + J.p j + J.q j ≤ J.d j
  · have hg' : (t : ℤ) + J.p j ≤ s j := by unfold s; omega
    rw [if_pos hg]
    simp only [hg', true_and]
    exact Iff.or Iff.rfl (by omega)
  · have hg' : ¬ ((t : ℤ) + J.p j ≤ s j) := by unfold s; omega
    rw [if_neg hg]
    simp only [hg', false_and, or_false]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · omega

/-- Numerical core of the capped recursion. -/
theorem cap_arith (W a c w : ℕ) (g : Prop) [Decidable g] :
    min W (max a (if g then w + c else 0)) =
      max (min W a) (if g then min W (w + min W c) else 0) := by
  by_cases hg : g
  · simp only [hg, if_true]; omega
  · simp only [hg, if_false]; omega

/-- **The capped dual recursion**: `D[X,t] = max(D[X₁,t], w_j + D[X₂, t + p_j])`, capped at `W`,
the second term present when `t + p_j + q_j ≤ d_j` (that is `t + p_j ≤ s_j`). -/
theorem dcap_rec (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (W : ℕ) {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) (t : ℕ) :
    dcap J W X t = max (dcap J W (X1 J X j) t)
      (if t + J.p j + J.q j ≤ J.d j then
        min W (J.w j + dcap J W (X2 J X j) (t + J.p j)) else 0) := by
  unfold dcap
  rw [dualVal_rec hest hq hjX hjmin t]
  exact cap_arith W _ _ _ _

/-! ## The machine's cell -/

/-- **One cell** from the two it depends on: `v₁ = D[X₁, t]`, `v₂ = D[X₂, t + p_j]`.  `R` is the
last row; the guard `t + p ≤ R` keeps the read inside the block (redundant on good cells). -/
def dStep (W R p q d w t v1 v2 : ℕ) : ℕ :=
  max v1 (if t + p + q ≤ d ∧ t + p ≤ R then min W (w + v2) else 0)

/-! ### Which cells are reachable: the guard `t + p_j ≤ R` is redundant there -/

/-- Total preprocessing time of the jobs numbered at least `j0`. -/
def sufP (J : Instance) (j0 : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : J.Job => j0 ≤ (i : ℕ)), J.p i

theorem sufP_anti {a b : ℕ} (h : a ≤ b) : sufP J b ≤ sufP J a := by
  unfold sufP
  refine Finset.sum_le_sum_of_subset fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem sufP_succ (j : J.Job) : J.p j + sufP J (j + 1) ≤ sufP J j := by
  unfold sufP
  have hnot : j ∉ Finset.univ.filter (fun i : J.Job => (j : ℕ) + 1 ≤ (i : ℕ)) := by simp
  rw [← Finset.sum_insert hnot]
  refine Finset.sum_le_sum_of_subset fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with rfl | hi
  · exact le_rfl
  · omega

theorem sufP_zero (J : Instance) : sufP J 0 = ∑ i : J.Job, J.p i := by
  unfold sufP; simp

/-- A cell `(X, t)` is **good** for the last row `R`: every threshold is at least some `j0` and
even preprocessing all jobs `≥ j0` from `t` stays within `R`. -/
def GoodF (J : Instance) (R : ℕ) (X : Finset J.Job) (t : ℕ) : Prop :=
  ∃ j0 : ℕ, (∀ x ∈ X, j0 ≤ (x : ℕ)) ∧ t + sufP J j0 ≤ R

/-- The start `(firstM, 0)` is good as soon as `R ≥ P`. -/
theorem goodF_firstM {R : ℕ} (hR : ∑ i : J.Job, J.p i ≤ R) : GoodF J R (firstM J) 0 :=
  ⟨0, fun x _ => Nat.zero_le _, by rw [sufP_zero]; omega⟩

/-- Every element of `X₁` exceeds `j`. -/
theorem X1_gt {X : Finset J.Job} {j : J.Job} (hjmin : ∀ x ∈ X, j ≤ x) :
    ∀ x ∈ X1 J X j, j < x := by
  intro x hx
  have hne : ∀ y ∈ X.erase j, j < y := fun y hy => by
    rcases Finset.mem_erase.mp hy with ⟨h1, h2⟩
    exact lt_of_le_of_ne (hjmin y h2) (Ne.symm h1)
  unfold X1 at hx
  split at hx
  · next y hy =>
    rcases Finset.mem_insert.mp hx with rfl | hx
    · unfold j1 at hy
      let := Classical.decPred fun x : J.Job => x ∉ X ∧ j < x
      split_ifs at hy with hne'
      have hm := (Finset.mem_filter.mp (Finset.min'_mem _ hne')).2.2
      rw [← Option.some.inj hy]; exact hm
    · exact hne x hx
  · exact hne x hx

/-- Every element of `X₂` exceeds `j`. -/
theorem X2_gt (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {X : Finset J.Job}
    {j : J.Job} (hjmin : ∀ x ∈ X, j ≤ x) :
    ∀ x ∈ X2 J X j, j < x := by
  intro x hx
  have hne : ∀ y ∈ X.erase j, j < y := fun y hy => by
    rcases Finset.mem_erase.mp hy with ⟨h1, h2⟩
    exact lt_of_le_of_ne (hjmin y h2) (Ne.symm h1)
  unfold X2 at hx
  split at hx
  · next y hy =>
    rcases Finset.mem_insert.mp hx with rfl | hx
    · unfold j2 at hy
      let := Classical.decPred fun x : J.Job => x ∉ X ∧ (J.d j : ℤ) ≤ s x
      split_ifs at hy with hne'
      have hm := (Finset.mem_filter.mp (Finset.min'_mem _ hne')).2.2
      rw [← Option.some.inj hy] at *
      by_contra hlt
      have hle : _ ≤ j := not_lt.mp hlt
      have h1 := hest _ _ hle
      have h2 := hq j
      unfold s at h1 hm
      omega
    · exact hne x hx
  · exact hne x hx

theorem goodF_X1 {R : ℕ} {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X)
    (hjmin : ∀ x ∈ X, j ≤ x) {t : ℕ} (hg : GoodF J R X t) : GoodF J R (X1 J X j) t := by
  obtain ⟨j0, hj0, hb⟩ := hg
  refine ⟨j + 1, fun x hx => X1_gt hjmin x hx, ?_⟩
  have := sufP_anti (J := J) (hj0 j hjX)
  have h2 := sufP_anti (J := J) (Nat.le_add_right (j : ℕ) 1)
  omega

theorem goodF_X2 (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {R : ℕ} {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) {t : ℕ} (hg : GoodF J R X t) :
    GoodF J R (X2 J X j) (t + J.p j) := by
  obtain ⟨j0, hj0, hb⟩ := hg
  refine ⟨j + 1, fun x hx => X2_gt hest hq hjmin x hx, ?_⟩
  have h1 := sufP_anti (J := J) (hj0 j hjX)
  have h2 := sufP_succ j
  omega

/-- On a good cell the guard `t + p_j ≤ R` holds. -/
theorem goodF_step_le {R : ℕ} {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X)
    {t : ℕ} (hg : GoodF J R X t) : t + J.p j ≤ R := by
  obtain ⟨j0, hj0, hb⟩ := hg
  have h1 := sufP_anti (J := J) (hj0 j hjX)
  have h2 := sufP_succ j
  omega

/-- **The cell recursion.**  If `v₁`, `v₂` are the (capped) entries for `X₁` at `t` and for `X₂`
at `t + p_j` (the latter only when the guard holds), then `dStep` is the (capped) entry for `X`
at `t`. -/
theorem dcell (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {W R : ℕ} {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) {t : ℕ} (hg : GoodF J R X t)
    {v1 v2 : ℕ} (h1 : v1 = dcap J W (X1 J X j) t)
    (h2 : t + J.p j + J.q j ≤ J.d j → v2 = dcap J W (X2 J X j) (t + J.p j)) :
    dStep W R (J.p j) (J.q j) (J.d j) (J.w j) t v1 v2 = dcap J W X t := by
  have hR := goodF_step_le hjX hg
  rw [dcap_rec hest hq W hjX hjmin t]
  unfold dStep
  by_cases hgd : t + J.p j + J.q j ≤ J.d j
  · rw [if_pos hgd, if_pos ⟨hgd, hR⟩, h1, h2 hgd]
  · rw [if_neg hgd, if_neg (fun h => hgd h.1), h1]

/-- The same, for `X` given as a sorted list `j :: Zs` and `X₁`, `X₂` as the machine's scans
produce them (`D2Ach.X1_ofList`, `X2_ofList`). -/
theorem dcell_list (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {W R : ℕ} {j : ℕ}
    {Zs : List ℕ} (hjn : j < J.jobs) (hjZ : ∀ z ∈ Zs, j < z) {t : ℕ}
    (hg : GoodF J R (ofList J (j :: Zs)) t)
    {y0 cur1 k1 cur2 k2 : ℕ} (hnx : IsNxt j hjn y0)
    (hr1 : ScanOK J.jobs Zs (j + 1) (cur1, k1)) (hr2 : ScanOK J.jobs Zs y0 (cur2, k2))
    (hjy : j < y0) {v1 v2 : ℕ}
    (h1 : v1 = dcap J W (ofList J (newL J.jobs Zs cur1 k1)) t)
    (h2 : t + J.p ⟨j, hjn⟩ + J.q ⟨j, hjn⟩ ≤ J.d ⟨j, hjn⟩ →
      v2 = dcap J W (ofList J (newL J.jobs Zs cur2 k2)) (t + J.p ⟨j, hjn⟩)) :
    dStep W R (J.p ⟨j, hjn⟩) (J.q ⟨j, hjn⟩) (J.d ⟨j, hjn⟩) (J.w ⟨j, hjn⟩) t v1 v2 =
      dcap J W (ofList J (j :: Zs)) t := by
  have hjX : (⟨j, hjn⟩ : J.Job) ∈ ofList J (j :: Zs) := by
    rw [mem_ofList]; simp
  have hjmin : ∀ x ∈ ofList J (j :: Zs), (⟨j, hjn⟩ : J.Job) ≤ x := by
    intro x hx
    rw [mem_ofList] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact Fin.mk_le_mk.mpr (by omega)
    · exact Fin.mk_le_mk.mpr (hjZ _ h).le
  refine dcell hest hq hjX hjmin hg ?_ ?_
  · rw [X1_ofList hjn hjZ hr1]; exact h1
  · intro hgd; rw [X2_ofList hjn hjZ hest hnx hr2 hjy]; exact h2 hgd

/-! ## The read-off -/

theorem firstM_eq_ofList (J : Instance) :
    firstM J = ofList J (List.range (min J.machines J.jobs)) := by
  ext x
  simp only [firstM, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofList, List.mem_range]
  have := x.isLt
  omega

/-- **The answer.**  A feasible set of weight at least `W` exists exactly when the dual table,
started at instant `0` from the `m` smallest thresholds, reaches `W`. -/
theorem hasWeight_iff_dualVal (hest : EstOrdered J) (W : ℕ) :
    HasWeight J W ↔ W ≤ dualVal J (firstM J) 0 := by
  rw [le_dualVal_iff]
  have hread := fun W'' => Lax496464Proofs.Section3.achievable_readoff J hest W''
  constructor
  · rintro ⟨Z, hZ, hW⟩
    obtain ⟨P', hP', hA⟩ := (hread (weight J Z)).mpr ⟨Z, hZ, rfl⟩
    refine ⟨weight J Z, hW, ?_⟩
    obtain ⟨Z', hw, hc, hp⟩ := hA
    refine ⟨Z', hw, hc, fun j hj => ?_⟩
    have := hp j hj
    simp only [Nat.cast_zero]
    linarith
  · rintro ⟨W'', hW, hA⟩
    obtain ⟨Z, hZ, hw⟩ := (hread W'').mp ⟨(0 : ℕ), by simp, hA⟩
    exact ⟨Z, hZ, by omega⟩

/-- **The exact form the machine scans:** the decision is `Yes` iff the capped entry of the
`m`-smallest-thresholds block at row `0` equals `W`. -/
theorem hasWeight_iff_dcap (hest : EstOrdered J) (W : ℕ) :
    HasWeight J W ↔ dcap J W (firstM J) 0 = W := by
  rw [hasWeight_iff_dualVal hest]
  unfold dcap
  exact min_eq_left_iff.symm

/-! ## The table invariant, and how one step preserves it (mirrors `D2Tab`) -/

/-- The entries of the numbers `≥ thr` are right **on good cells** (`t ≤ R`, `GoodF`); those of
the numbers `< thr` are still zero.  Row `t` of number `c` is at `c * (R + 1) + t`. -/
def DTabOK (J : Instance) (n m W R N thr : ℕ) (T : List ℕ) : Prop :=
  T.length = N * (R + 1) ∧
  (∀ Zs, SL n m Zs → thr ≤ codeL n m Zs → ∀ t ≤ R, GoodF J R (ofList J Zs) t →
    T.getD (codeL n m Zs * (R + 1) + t) 0 = dcap J W (ofList J Zs) t) ∧
  (∀ i, i < N * (R + 1) → i / (R + 1) < thr → T.getD i 0 = 0)

/-- **A step**: only the cells of the number `c` change, and afterwards they are right on good
cells. -/
theorem dtab_step {J : Instance} {n m W R N c : ℕ} {T T' : List ℕ} (hN : N = (n + 1) ^ m)
    (hT : DTabOK J n m W R N (c + 1) T) (hlen : T'.length = N * (R + 1))
    (hout : ∀ i, i < N * (R + 1) → i / (R + 1) ≠ c → T'.getD i 0 = T.getD i 0)
    (hblock : ∀ Zs, SL n m Zs → codeL n m Zs = c → ∀ t ≤ R, GoodF J R (ofList J Zs) t →
      T'.getD (c * (R + 1) + t) 0 = dcap J W (ofList J Zs) t) :
    DTabOK J n m W R N c T' := by
  obtain ⟨hl, hrep, hzero⟩ := hT
  refine ⟨hlen, ?_, ?_⟩
  · intro Zs hsl hc t ht hgood
    by_cases hcc : codeL n m Zs = c
    · rw [hcc]; exact hblock Zs hsl hcc t ht hgood
    · have hgt : c + 1 ≤ codeL n m Zs := by omega
      have hlt : codeL n m Zs * (R + 1) + t < N * (R + 1) := by
        have h1 := hsl.codeL_lt
        rw [← hN] at h1
        nlinarith
      have hdiv := div_block (codeL n m Zs) R t ht
      rw [hout _ hlt (by rw [hdiv]; exact hcc)]
      exact hrep Zs hsl hgt t ht hgood
  · intro i hi hic
    have hne : i / (R + 1) ≠ c := by omega
    rw [hout i hi hne]
    exact hzero i hi (by omega)

/-- **A step at the empty set, or at a number that is not a code, changes nothing**: the block of
`∅` is zero, and that is its value. -/
theorem dtab_step_empty {J : Instance} {n m W R N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hc : c = N - 1) (hT : DTabOK J n m W R N (c + 1) T) :
    DTabOK J n m W R N c T := by
  refine dtab_step hN hT hT.1 (fun i _ _ => rfl) ?_
  intro Zs hsl hcode t ht _
  have hZs : Zs = [] := eq_nil_of_code_top hsl (by rw [hcode, hc, hN])
  subst hZs
  rw [ofList_nil, dcap_empty]
  have hlt : c * (R + 1) + t < N * (R + 1) := by
    have h1 : c < N := by
      have := hsl.codeL_lt
      rw [← hN] at this
      rw [hcode] at this
      exact this
    nlinarith
  exact hT.2.2 _ hlt (by rw [div_block c R t ht]; omega)

theorem dtab_step_invalid {J : Instance} {n m W R N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hnc : ¬ IsCode n m c) (hT : DTabOK J n m W R N (c + 1) T) :
    DTabOK J n m W R N c T := by
  refine dtab_step hN hT hT.1 (fun i _ _ => rfl) ?_
  intro Zs hsl hcode
  exact absurd ⟨Zs, hsl, hcode⟩ hnc

theorem sl_range (n m : ℕ) : SL n m (List.range (min m n)) :=
  ⟨List.sortedLT_iff_pairwise.mpr List.pairwise_lt_range,
    fun z hz => by rw [List.mem_range] at hz; omega, by simp⟩

/-- **The answer read from the finished table.**  With `R ≥ P`, the decision is whether the entry
of the `m`-smallest-thresholds block at row `0` is `W`. -/
theorem hasWeight_iff_tab (hest : EstOrdered J) {W R N : ℕ} {T : List ℕ}
    (hR : ∑ i : J.Job, J.p i ≤ R) (hT : DTabOK J J.jobs J.machines W R N 0 T) :
    HasWeight J W ↔ T.getD (codeL J.jobs J.machines (List.range (min J.machines J.jobs)) *
      (R + 1)) 0 = W := by
  have h := hT.2.1 _ (sl_range J.jobs J.machines) (Nat.zero_le _) 0 (Nat.zero_le _)
    (by rw [← firstM_eq_ofList]; exact goodF_firstM hR)
  rw [Nat.add_zero] at h
  rw [h, ← firstM_eq_ofList, hasWeight_iff_dcap hest]

/-! ## Counting the rows -/

/-- The word-level total preprocessing time is `Σ_j p_j`. -/
theorem preSum_eq {x : List ℕ} {I : Instance} (hj : jobCount x = I.jobs)
    (hp : ∀ j : I.Job, preTime x j = I.p j) : preSum x = ∑ i : I.Job, I.p i := by
  unfold preSum
  rw [hj]
  have h : ∀ n, ((List.range n).map (preTime x)).sum = ∑ i ∈ Finset.range n, preTime x i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [h, Finset.sum_range (fun i => preTime x i)]
  exact Finset.sum_congr rfl fun j _ => hp j

end Lax496464Proofs.Ram.D3Dual
