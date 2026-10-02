import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lax496464Proofs.Bridge
import Lax496464Proofs.Model.Theorem5_FPTAS
import Lax496464.Theorem5

/-!
# Section 7: the Rounding Argument

The approximation scheme divides every weight by `k` and rounds up, solves the rounded
instance exactly with one of the pseudo-polynomial algorithms — whose running times depend
on the *total weight*, now `n·w_max/k` instead of `n·w_max` — and reports the set it finds
with its *original* weight. Chain (8) is the guarantee: the loss is at most `k` per selected
job, so at most `k·n`, and the choice `k = w_max/(e·n)` makes that at most `w_max/e`, which
is at most `OPT/e` because some single job of weight `w_max` is schedulable on its own.

That last step is the paper's standing assumption of Section 7 — every job can be
preprocessed on its own, `p_j ≤ s_j`, jobs failing it being discarded — together with there
being a machine to run it on. Without them the claim is false: an instance whose heaviest
job cannot be scheduled has `w_max > OPT`, and the chain has nothing to end at.
-/

namespace Lax496464Proofs.Section7

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas Bridge

variable {I : Instance}

/-- The two readings of `w_max` — a fold over the jobs, and a `Finset` supremum — agree. -/
theorem wmax_eq : (model I).wmax = wmax I := by
  classical
  unfold FFJ.wmax wmax
  rfl

/-- The two readings of the optimum agree: the filters select the same sets. -/
theorem optimum_eq : optimum I = (model I).opt := by
  classical
  unfold Instance.optimum
  apply le_antisymm
  · refine Finset.sup_le fun Z hZ => ?_
    exact (model I).le_opt ((feasible_iff_model Z).mp (Finset.mem_filter.mp hZ).2)
  · obtain ⟨Z, hZ, hw⟩ := (model I).exists_feasible_weight_eq_opt
    rw [← hw]
    exact Finset.le_sup (f := weight I)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (feasible_iff_model Z).mpr hZ⟩)

/--
---
conclusion: Lax496464.Theorem5.rescale_approx
---
Chain (8). Rounding up loses less than `k` per selected job, so at most `k·n` in all;
`e·k·n ≤ w_max` turns that into `w_max/e`, and `w_max ≤ OPT` — the heaviest job is feasible
on its own — turns it into `OPT/e`.
-/
theorem rescale_approx (I : Instance) {e k : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k)
    (hm : 0 < I.machines) (hpre : ∀ j : I.Job, (I.p j : ℤ) ≤ s j)
    (hkn : e * k * I.jobs ≤ wmax I) (Zs : Finset I.Job) (_hZs : Feasible I Zs)
    (hopt : ∀ Z : Finset I.Job, Feasible I Z →
      weight (rescale I k) Z ≤ weight (rescale I k) Zs) :
    (e - 1) * optimum I ≤ e * weight I Zs := by
  classical
  have hepos : 0 < e := Nat.lt_of_lt_of_le Nat.zero_lt_one he
  have he' : (0 : ℚ) < (e : ℚ) := by exact_mod_cast hepos
  have hε : (0 : ℚ) ≤ 1 / (e : ℚ) := by positivity
  have hnum : (model I).numJobs = I.jobs := Fintype.card_fin _
  have hknQ : ((e : ℚ)) * ((k : ℚ) * (I.jobs : ℚ)) ≤ ((wmax I : ℕ) : ℚ) := by
    have h : ((e * k * I.jobs : ℕ) : ℚ) ≤ ((wmax I : ℕ) : ℚ) := by exact_mod_cast hkn
    push_cast at h
    linarith
  have hkn' : (k : ℚ) * ((model I).numJobs : ℚ) ≤ (1 / (e : ℚ)) * ((model I).wmax : ℚ) := by
    rw [hnum, wmax_eq, one_div, inv_mul_eq_div, le_div_iff₀ he']
    linarith
  have hwm : (((model I).wmax : ℕ) : ℚ) ≤ ((model I).opt : ℚ) := by
    exact_mod_cast (model I).wmax_le_opt hm hpre
  have key : (1 - 1 / (e : ℚ)) * ((model I).opt : ℚ) ≤ ((model I).weight Zs : ℚ) :=
    (model I).rescale_approx k hε hk Zs
      (fun Z hZ => hopt Z ((feasible_iff_model Z).mpr hZ)) hkn' hwm
  have hee : (e : ℚ) * (1 - 1 / (e : ℚ)) = (e : ℚ) - 1 := by
    field_simp
  have h2 : ((e : ℚ) - 1) * ((optimum I : ℕ) : ℚ) ≤ (e : ℚ) * ((weight I Zs : ℕ) : ℚ) := by
    rw [optimum_eq, ← hee, mul_assoc]
    exact mul_le_mul_of_nonneg_left key he'.le
  have h3 : (((e - 1 : ℕ) : ℚ)) * ((optimum I : ℕ) : ℚ)
      ≤ ((e : ℕ) : ℚ) * ((weight I Zs : ℕ) : ℚ) := by
    rwa [Nat.cast_sub he, Nat.cast_one]
  exact_mod_cast h3

end Lax496464Proofs.Section7
