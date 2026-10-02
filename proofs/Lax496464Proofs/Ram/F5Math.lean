import Lax496464Proofs.Section7

/-!
# Theorem 5, the Pure Mathematical Layer of the Value the Schemes Write

The three schemes of Theorem 5 run an *exact* program on weights rescaled by `k` and then
write one number computed from the exact program's table. This file is that number and
the proof that it is an acceptable answer (`Fptas.Delivers`); no machine occurs here.

Notation: `n = I.jobs`, a job `j` is *fit* when `p_j + q_j ≤ d_j` (equivalently `p_j ≤ s_j`).

* `zeroUnfit I` is `I` with the weight of every unfit job set to `0`. An unfit job lies in no
  feasible set, so nothing about feasibility or the optimum changes (`optimum_zeroUnfit`).
* `wmaxFit I` is the largest weight among the fit jobs (`0` if none).
* `scaleK I e = max 1 (wmaxFit I / (e·n))`.
* `scaled I e = rescale (zeroUnfit I) (scaleK I e)`; its weights are, machine-friendly,
  `(w_j - 1)/k + 1` for a fit job with `w_j ≥ 1` and `0` otherwise (`scaled_w_eq`).
* `scaledOpt I e = optimum (scaled I e)`, what the exact program computes: the largest
  `c` with `HasWeight (scaled I e) c` (`hasWeight_scaled`), which is `≤ thr I e = 2·e·n·n`.
* `fptasOut I e = if 1 < k then k · (scaledOpt − n) else scaledOpt` (truncated subtraction).

Main theorem `fptas_value`: `HasWeight I (fptasOut I e) ∧ (e-1) * optimum I ≤ e * fptasOut I e`,
for every instance and every `e ≥ 1` (no assumption on the machines, and no assumption on `q`).
-/

namespace Lax496464Proofs.F5Math

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas Lax496464Proofs.Bridge

/-! ## 0. Instances with other weights -/

/-- The instance `I` with the weights replaced by `f`. -/
@[reducible] def withW (I : Instance) (f : Fin I.jobs → ℕ) : Instance where
  jobs := I.jobs
  machines := I.machines
  p := I.p
  q := I.q
  d := I.d
  w := f

theorem feasible_withW (I : Instance) (f : Fin I.jobs → ℕ) (Z : Finset (Fin I.jobs)) :
    Feasible (withW I f) Z ↔ Feasible I Z := by
  constructor
  · rintro ⟨σ⟩
    exact ⟨⟨σ.pre, σ.mach, σ.pre_nonneg, σ.pre_le_s, σ.pre_disjoint, σ.mach_lt, σ.mach_indep⟩⟩
  · rintro ⟨σ⟩
    exact ⟨⟨σ.pre, σ.mach, σ.pre_nonneg, σ.pre_le_s, σ.pre_disjoint, σ.mach_lt, σ.mach_indep⟩⟩

theorem hasWeight_withW (I : Instance) (f : Fin I.jobs → ℕ) (W : ℕ) :
    HasWeight (withW I f) W ↔ ∃ Z : Finset (Fin I.jobs), Feasible I Z ∧ W ≤ ∑ j ∈ Z, f j := by
  constructor
  · rintro ⟨Z, hZ, hW⟩
    exact ⟨Z, (feasible_withW I f Z).mp hZ, hW⟩
  · rintro ⟨Z, hZ, hW⟩
    exact ⟨Z, (feasible_withW I f Z).mpr hZ, hW⟩

theorem feasible_rescale (J : Instance) (k : ℕ) (Z : Finset (Fin J.jobs)) :
    Feasible (rescale J k) Z ↔ Feasible J Z := feasible_withW J _ Z

/-! ## 1. The optimum, attained and downward closed -/

theorem hasWeight_iff (I : Instance) (W : ℕ) : HasWeight I W ↔ W ≤ optimum I := by
  rw [Section7.optimum_eq, ← model_hasWeight]
  exact (model I).hasWeight_iff W

theorem le_optimum (I : Instance) {Z : Finset I.Job} (h : Feasible I Z) :
    weight I Z ≤ optimum I :=
  (hasWeight_iff I _).mp ⟨Z, h, le_rfl⟩

theorem exists_feasible_eq_optimum (I : Instance) :
    ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = optimum I := by
  obtain ⟨Z, hZ, hw⟩ := (model I).exists_feasible_weight_eq_opt
  exact ⟨Z, (feasible_iff_model Z).mpr hZ, by rw [Section7.optimum_eq]; exact hw⟩

theorem optimum_eq_of_hasWeight_iff {I J : Instance} (h : ∀ W, HasWeight I W ↔ HasWeight J W) :
    optimum I = optimum J := by
  apply le_antisymm
  · exact (hasWeight_iff J _).mp ((h _).mp ((hasWeight_iff I _).mpr le_rfl))
  · exact (hasWeight_iff I _).mp ((h _).mpr ((hasWeight_iff J _).mpr le_rfl))

theorem optimum_le_total (I : Instance) : optimum I ≤ ∑ j, I.w j := by
  obtain ⟨Z, _, hw⟩ := exists_feasible_eq_optimum I
  rw [← hw]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ Z)

/-- With no machine only `∅` is feasible. -/
theorem optimum_eq_zero_of_no_machines (I : Instance) (h : I.machines = 0) : optimum I = 0 := by
  obtain ⟨Z, ⟨σ⟩, hw⟩ := exists_feasible_eq_optimum I
  rw [← hw]
  have : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    have := σ.mach_lt j hj
    omega
  subst this
  simp [weight]

/-! ## 2. Fit jobs -/

/-- A job is fit when it can be preprocessed at all: `p ≤ s`, i.e. `p + q ≤ d`. -/
def Fit (I : Instance) (j : Fin I.jobs) : Prop := I.p j + I.q j ≤ I.d j

instance (I : Instance) (j : Fin I.jobs) : Decidable (Fit I j) :=
  inferInstanceAs (Decidable (I.p j + I.q j ≤ I.d j))

theorem fit_iff (I : Instance) (j : Fin I.jobs) : (I.p j : ℤ) ≤ s j ↔ Fit I j := by
  unfold Fit s
  omega

theorem fit_of_mem_feasible {I : Instance} {Z : Finset I.Job} (h : Feasible I Z) {j : I.Job}
    (hj : j ∈ Z) : Fit I j := by
  obtain ⟨σ⟩ := h
  have h1 := σ.pre_nonneg j hj
  have h2 := σ.pre_le_s j hj
  rw [← fit_iff]
  omega

/-- `I` with the weight of every unfit job set to `0`. -/
@[reducible] def zeroUnfit (I : Instance) : Instance :=
  withW I fun j => if Fit I j then I.w j else 0

theorem weight_zeroUnfit {I : Instance} {Z : Finset I.Job} (h : Feasible I Z) :
    weight (zeroUnfit I) Z = weight I Z := by
  refine Finset.sum_congr rfl fun j hj => ?_
  show (if Fit I j then I.w j else 0) = I.w j
  rw [if_pos (fit_of_mem_feasible h hj)]

theorem hasWeight_zeroUnfit (I : Instance) (W : ℕ) :
    HasWeight (zeroUnfit I) W ↔ HasWeight I W := by
  rw [zeroUnfit, hasWeight_withW]
  constructor
  · rintro ⟨Z, hZ, hW⟩
    refine ⟨Z, hZ, ?_⟩
    rw [← weight_zeroUnfit hZ]
    exact hW
  · rintro ⟨Z, hZ, hW⟩
    refine ⟨Z, hZ, ?_⟩
    exact hW.trans_eq (weight_zeroUnfit hZ).symm

theorem optimum_zeroUnfit (I : Instance) : optimum (zeroUnfit I) = optimum I :=
  optimum_eq_of_hasWeight_iff (hasWeight_zeroUnfit I)

/-! ## 3. The largest weight -/

theorem wmax_eq_sup (J : Instance) : wmax J = Finset.univ.sup J.w := Section7.wmax_eq.symm

theorem le_wmax (J : Instance) (j : Fin J.jobs) : J.w j ≤ wmax J := by
  rw [wmax_eq_sup]
  exact Finset.le_sup (f := J.w) (Finset.mem_univ j)

theorem wmax_le (J : Instance) {B : ℕ} (h : ∀ j, J.w j ≤ B) : wmax J ≤ B := by
  rw [wmax_eq_sup]
  exact Finset.sup_le fun j _ => h j

/-- The largest weight among the fit jobs (`0` if there are none). -/
def wmaxFit (I : Instance) : ℕ := wmax (zeroUnfit I)

theorem le_wmaxFit (I : Instance) {j : Fin I.jobs} (hj : Fit I j) : I.w j ≤ wmaxFit I := by
  have h := le_wmax (zeroUnfit I) j
  have e : (zeroUnfit I).w j = I.w j := if_pos hj
  rw [e] at h
  exact h

theorem wmaxFit_le (I : Instance) {B : ℕ} (h : ∀ j, Fit I j → I.w j ≤ B) : wmaxFit I ≤ B := by
  refine wmax_le _ fun j => ?_
  show (if Fit I j then I.w j else 0) ≤ B
  split_ifs with hj
  · exact h j hj
  · exact Nat.zero_le _

/-- On a machine, the largest fit weight is at most the optimum: a fit job alone is feasible. -/
theorem wmaxFit_le_optimum (I : Instance) (hm : 0 < I.machines) : wmaxFit I ≤ optimum I := by
  refine wmaxFit_le I fun j hj => ?_
  have hf : Feasible I {j} :=
    (feasible_iff_model _).mpr ((model I).feasible_singleton hm ((fit_iff I j).mpr hj))
  have := le_optimum I hf
  simpa [weight] using this

/-! ## 4. Rescaling -/

theorem ceil_bounds (w k : ℕ) (hk : 0 < k) :
    w ≤ k * ((w + (k - 1)) / k) ∧ k * ((w + (k - 1)) / k) ≤ w + k := by
  have h1 := Nat.div_add_mod (w + (k - 1)) k
  have h2 := Nat.mod_lt (w + (k - 1)) hk
  generalize (w + (k - 1)) / k = q at *
  generalize (w + (k - 1)) % k = r at *
  omega

theorem weight_le_rescale (J : Instance) {k : ℕ} (hk : 0 < k) (Z : Finset (Fin J.jobs)) :
    weight J Z ≤ k * weight (rescale J k) Z := by
  calc weight J Z ≤ ∑ j ∈ Z, k * ((J.w j + (k - 1)) / k) :=
        Finset.sum_le_sum fun j _ => (ceil_bounds (J.w j) k hk).1
    _ = k * weight (rescale J k) Z := (Finset.mul_sum Z (fun j => (J.w j + (k - 1)) / k) k).symm

theorem rescale_le_weight (J : Instance) {k : ℕ} (hk : 0 < k) (Z : Finset (Fin J.jobs)) :
    k * weight (rescale J k) Z ≤ weight J Z + k * J.jobs := by
  have hc : Z.card ≤ J.jobs := by simpa using Finset.card_le_univ Z
  calc k * weight (rescale J k) Z = ∑ j ∈ Z, k * ((J.w j + (k - 1)) / k) :=
        Finset.mul_sum Z (fun j => (J.w j + (k - 1)) / k) k
    _ ≤ ∑ j ∈ Z, (J.w j + k) := Finset.sum_le_sum fun j _ => (ceil_bounds (J.w j) k hk).2
    _ = weight J Z + k * Z.card := by
        rw [Finset.sum_add_distrib]
        simp [weight, mul_comm]
    _ ≤ weight J Z + k * J.jobs := Nat.add_le_add_left (Nat.mul_le_mul_left k hc) _

theorem hasWeight_rescale_one (J : Instance) (W : ℕ) :
    HasWeight (rescale J 1) W ↔ HasWeight J W := by
  have h : rescale J 1 = withW J (fun j => J.w j) := by
    unfold rescale withW
    congr
    funext j
    simp
  rw [h, hasWeight_withW]

/-! ## 5. The scheme -/

/-- The scaling factor `max 1 (w_max' / (e·n))`. -/
def scaleK (I : Instance) (e : ℕ) : ℕ := max 1 (wmaxFit I / (e * I.jobs))

/-- The instance the exact program is run on. -/
def scaled (I : Instance) (e : ℕ) : Instance := rescale (zeroUnfit I) (scaleK I e)

/-- The exact optimum of the rescaled instance. -/
noncomputable def scaledOpt (I : Instance) (e : ℕ) : ℕ := optimum (scaled I e)

/-- The number the scheme writes. -/
noncomputable def fptasOut (I : Instance) (e : ℕ) : ℕ :=
  if 1 < scaleK I e then scaleK I e * (scaledOpt I e - I.jobs) else scaledOpt I e

/-- The threshold the exact program is run with. -/
def thr (I : Instance) (e : ℕ) : ℕ := 2 * e * I.jobs * I.jobs

theorem one_le_scaleK (I : Instance) (e : ℕ) : 1 ≤ scaleK I e := le_max_left _ _

/-- The rescaled weights, in the ceiling form a machine computes. -/
theorem scaled_w_eq (I : Instance) (e : ℕ) (j : Fin I.jobs) :
    (scaled I e).w j =
      if Fit I j ∧ 1 ≤ I.w j then (I.w j - 1) / scaleK I e + 1 else 0 := by
  have hk := one_le_scaleK I e
  show ((if Fit I j then I.w j else 0) + (scaleK I e - 1)) / scaleK I e = _
  generalize scaleK I e = k at hk ⊢
  by_cases h : Fit I j ∧ 1 ≤ I.w j
  · rw [if_pos h.1, if_pos h]
    have : I.w j + (k - 1) = (I.w j - 1) + k := by omega
    rw [this, Nat.add_div_right _ hk]
  · rw [if_neg h]
    by_cases hf : Fit I j
    · rw [if_pos hf]
      have : I.w j = 0 := by
        by_contra hne
        exact h ⟨hf, Nat.one_le_iff_ne_zero.mpr hne⟩
      rw [this, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    · rw [if_neg hf, zero_add]
      exact Nat.div_eq_of_lt (by omega)

/-- Reading the exact table off: `c` is reached iff `c ≤ scaledOpt`, so the largest
`c ≤ thr` with `HasWeight (scaled I e) c` is `scaledOpt`, once `scaledOpt ≤ thr`. -/
theorem hasWeight_scaled (I : Instance) (e c : ℕ) :
    HasWeight (scaled I e) c ↔ c ≤ scaledOpt I e := hasWeight_iff _ _

theorem ceil_le (w k B : ℕ) (hk : 1 ≤ k) (hw : w < B * (k + 1)) :
    (w + (k - 1)) / k ≤ 2 * B := by
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : B ≤ B * k := Nat.le_mul_of_pos_right B hk
  have h2 : B * (k + 1) = B * k + B := by ring
  have h3 : k * (2 * B) = 2 * (B * k) := by ring
  omega

/-- Every rescaled weight is at most `2·e·n`. -/
theorem scaled_w_le (I : Instance) {e : ℕ} (he : 1 ≤ e) (j : Fin I.jobs) :
    (scaled I e).w j ≤ 2 * e * I.jobs := by
  have hn : 0 < I.jobs := Nat.pos_of_ne_zero fun h => by
    have := j.2
    omega
  have hb : 0 < e * I.jobs := Nat.mul_pos he hn
  have hk := one_le_scaleK I e
  have hq : wmaxFit I / (e * I.jobs) ≤ scaleK I e := le_max_right _ _
  have hlt := Nat.lt_mul_div_succ (wmaxFit I) hb
  have hw0 : (zeroUnfit I).w j ≤ wmaxFit I := le_wmax (zeroUnfit I) j
  have hlt2 : (zeroUnfit I).w j < e * I.jobs * (scaleK I e + 1) := by
    have : e * I.jobs * (wmaxFit I / (e * I.jobs) + 1) ≤ e * I.jobs * (scaleK I e + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have := ceil_le ((zeroUnfit I).w j) (scaleK I e) (e * I.jobs) hk hlt2
  show ((zeroUnfit I).w j + (scaleK I e - 1)) / scaleK I e ≤ 2 * e * I.jobs
  rw [mul_assoc]
  exact this

theorem scaledOpt_le_thr (I : Instance) {e : ℕ} (he : 1 ≤ e) : scaledOpt I e ≤ thr I e := by
  obtain ⟨Z, _, hw⟩ := exists_feasible_eq_optimum (scaled I e)
  unfold scaledOpt
  rw [← hw]
  have hc : Z.card ≤ (scaled I e).jobs := by simpa using Finset.card_le_univ Z
  calc weight (scaled I e) Z ≤ Z.card • (2 * e * I.jobs) :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ => scaled_w_le I he j
    _ = Z.card * (2 * e * I.jobs) := by simp
    _ ≤ I.jobs * (2 * e * I.jobs) := Nat.mul_le_mul_right _ hc
    _ = thr I e := by unfold thr; ring

/-! ## 6. The main theorem -/

theorem arith_guarantee {e opt V kn : ℕ} (he : 1 ≤ e) (h1 : opt ≤ V + kn) (h2 : e * kn ≤ opt) :
    (e - 1) * opt ≤ e * V := by
  obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
  have h3 : (a + 1) * opt ≤ (a + 1) * (V + kn) := Nat.mul_le_mul_left _ h1
  have h4 : (a + 1) * (V + kn) = (a + 1) * V + (a + 1) * kn := by ring
  have h5 : (a + 1 - 1) * opt = a * opt := by simp
  have h6 : (a + 1) * opt = a * opt + opt := by ring
  rw [h5]
  omega

theorem fptas_value (I : Instance) {e : ℕ} (he : 1 ≤ e) :
    HasWeight I (fptasOut I e) ∧ (e - 1) * optimum I ≤ e * fptasOut I e := by
  by_cases hm0 : I.machines = 0
  · have h0 : scaledOpt I e = 0 := optimum_eq_zero_of_no_machines _ hm0
    have hout : fptasOut I e = 0 := by
      unfold fptasOut
      rw [h0]
      simp
    rw [hout, optimum_eq_zero_of_no_machines I hm0]
    exact ⟨(hasWeight_iff I 0).mpr (Nat.zero_le _), by simp⟩
  have hm : 0 < I.machines := Nat.pos_of_ne_zero hm0
  have hk1 := one_le_scaleK I e
  by_cases hk : 1 < scaleK I e
  swap
  · -- k = 1: the rescaled instance is the instance with the unfit weights zeroed
    have hout : fptasOut I e = optimum I := by
      unfold fptasOut
      rw [if_neg hk]
      unfold scaledOpt
      have hk' : scaleK I e = 1 := by omega
      have : optimum (scaled I e) = optimum (zeroUnfit I) := by
        unfold scaled
        rw [hk']
        exact optimum_eq_of_hasWeight_iff (hasWeight_rescale_one _)
      rw [this, optimum_zeroUnfit]
    rw [hout]
    refine ⟨(hasWeight_iff I _).mpr le_rfl, ?_⟩
    exact Nat.mul_le_mul_right _ (Nat.sub_le e 1)
  · set k := scaleK I e with hkdef
    set n := I.jobs with hn
    set W' := scaledOpt I e with hW'
    have hout : fptasOut I e = k * (W' - n) := by
      unfold fptasOut
      rw [if_pos hk]
    -- (i) opt ≤ k * W'
    have hopt0 : optimum I ≤ k * W' := by
      obtain ⟨Z, hZ, hw⟩ := exists_feasible_eq_optimum (zeroUnfit I)
      rw [← optimum_zeroUnfit I, ← hw]
      calc weight (zeroUnfit I) Z ≤ k * weight (rescale (zeroUnfit I) k) Z :=
            weight_le_rescale (zeroUnfit I) (by omega) Z
        _ ≤ k * W' := by
            apply Nat.mul_le_mul_left
            exact le_optimum (scaled I e) ((feasible_rescale _ _ Z).mpr hZ)
    -- (ii) the optimal set of the rescaled instance
    obtain ⟨Zs, hZs, hwZs⟩ := exists_feasible_eq_optimum (scaled I e)
    have hZsI : Feasible I Zs := (feasible_withW I _ Zs).mp hZs
    have hkW : k * W' ≤ weight I Zs + k * n := by
      have := rescale_le_weight (zeroUnfit I) (k := k) (by omega) Zs
      rw [weight_zeroUnfit hZsI] at this
      have e1 : weight (scaled I e) Zs = W' := hwZs
      have e2 : weight (rescale (zeroUnfit I) k) Zs = W' := e1
      rw [e2] at this
      exact this
    have hV_le : k * (W' - n) ≤ weight I Zs := by
      rcases le_total n W' with h | h
      · have : k * (W' - n) + k * n = k * W' := by
          rw [← Nat.mul_add, Nat.sub_add_cancel h]
        omega
      · rw [Nat.sub_eq_zero_of_le h]
        simp
    have hopt1 : optimum I ≤ k * (W' - n) + k * n := by
      rcases le_total n W' with h | h
      · have : k * (W' - n) + k * n = k * W' := by
          rw [← Nat.mul_add, Nat.sub_add_cancel h]
        omega
      · rw [Nat.sub_eq_zero_of_le h]
        have : k * W' ≤ k * n := Nat.mul_le_mul_left _ h
        omega
    -- (iii) e * k * n ≤ wmax' ≤ opt
    have hq1 : 1 ≤ wmaxFit I / (e * n) := by
      have : scaleK I e = max 1 (wmaxFit I / (e * n)) := rfl
      omega
    have hkq : k = wmaxFit I / (e * n) := by
      have : scaleK I e = max 1 (wmaxFit I / (e * n)) := rfl
      rw [hkdef, this]
      exact max_eq_right hq1
    have hekn : e * (k * n) ≤ wmaxFit I := by
      have h := Nat.div_mul_le_self (wmaxFit I) (e * n)
      rw [← hkq] at h
      calc e * (k * n) = k * (e * n) := by ring
        _ ≤ wmaxFit I := h
    have hle := wmaxFit_le_optimum I hm
    refine ⟨?_, ?_⟩
    · rw [hout]
      exact ⟨Zs, hZsI, hV_le⟩
    · rw [hout]
      exact arith_guarantee he hopt1 (le_trans hekn hle)

/-! ## 7. What the machine needs, restated -/

theorem fptasOut_le_optimum (I : Instance) {e : ℕ} (he : 1 ≤ e) :
    fptasOut I e ≤ optimum I :=
  (hasWeight_iff I _).mp (fptas_value I he).1

theorem fptasOut_le_total (I : Instance) {e : ℕ} (he : 1 ≤ e) :
    fptasOut I e ≤ ∑ j, I.w j :=
  le_trans (fptasOut_le_optimum I he) (optimum_le_total I)

/-- The scheme's output is an acceptable answer on every presentation of `I` with accuracy `e`. -/
theorem delivers_fptasOut {I : Instance} {x : List ℕ} {e : ℕ} (h : EncodesApprox I x e) :
    Delivers x [fptasOut I e] := by
  obtain ⟨_, _, he, _⟩ := id h
  exact ⟨I, e, fptasOut I e, h, rfl, fptas_value I he⟩

end Lax496464Proofs.F5Math
