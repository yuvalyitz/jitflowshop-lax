import Lax496464Proofs.EstBridge
import Lax496464Proofs.Model.Section4_Distinct
import Lax496464.Normalization
import Lax496464.Lemma2

/-!
# Section 4: the Normalization, and the Sweep over Endpoints

Sections 4 and 5 assume the `2n` endpoints `s_j` and `d_j` are pairwise distinct, so that a
sweep from left to right meets one event at a time. `scale` is the normalization that
arranges it — multiply every length by `n+1` and shift job `j`'s window right by `j` — and
`scale_feasible_iff` says it changes nothing.

The sweep itself keeps, for each instant `t`, the set `X` of selected jobs alive at `t`,
the weight accumulated and the preprocessing load spent. `reachable_due` and
`reachable_start` are its two steps, equations (4) and (3) of the paper.

Positive processing times are needed for the normalization, and the paper's standing
assumption gives them: with `q_j = 0` the window `[s_j, d_j)` is empty, the shift makes
`s_j` of the scaled instance equal to its own `d_j`, and the endpoints are not separated
after all.
-/

namespace Lax496464Proofs.Section4

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Sweep Bridge EstBridge

variable {I : Instance}

/-- The sweep's table means the same on both sides: only `Feasible` has to be converted. -/
theorem reachable_iff_model (t : ℤ) (X : Finset I.Job) (W' : ℕ) (P' : ℤ) :
    Reachable I t X W' P' ↔ (model I).Reachable t X W' P' :=
  exists_congr fun Z => and_congr_left fun _ => feasible_iff_model Z

/--
---
conclusion: Lax496464.Normalization.scale_feasible_iff
---
Scaling multiplies both sides of Condition 1 by `n+1` and leaves the shift `j < n+1` too
small to matter, and it preserves the conflict relation, hence Condition 2.
-/
theorem scale_feasible_iff (I : Instance) (h : EstOrdered I) (hq : ∀ i : I.Job, 0 < I.q i)
    (Z : Finset I.Job) :
    Feasible (scale I) Z ↔ Feasible I Z :=
  (feasible_iff_model (I := scale I) Z).trans
    (((estModel I h).scale_feasible_iff hq Z).trans (feasible_iff_model Z).symm)

/--
---
conclusion: Lax496464.Normalization.scale_weight
---
The weights are not touched.
-/
theorem scale_weight (I : Instance) (Z : Finset I.Job) :
    weight (scale I) Z = weight I Z := rfl

/--
---
conclusion: Lax496464.Normalization.scale_distinctEndpoints
---
After scaling, `s_j = (n+1)s_j + j` and `d_j = (n+1)d_j + j`, so two endpoints can coincide
only if they belong to the same job — and a job's own two endpoints differ because its
processing time is positive.
-/
theorem scale_distinctEndpoints (I : Instance) (h : EstOrdered I)
    (hq : ∀ i : I.Job, 0 < I.q i) :
    DistinctEndpoints (scale I) ∧ EstOrdered (scale I) :=
  let hd := (estModel I h).scale_distinctEndpoints hq
  ⟨⟨hd.1, hd.2.1, hd.2.2⟩, fun i j hij => (estModel I h).scale.est i j hij⟩

/--
---
conclusion: Lax496464.Lemma2.reachable_due
---
Equation (4). Nothing starts in `(t', t]`, so the alive set only loses `j`, and a state at
`t` comes from a state at `t'` that either contained `j` or did not.
-/
theorem reachable_due (I : Instance) (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (htt : t' < t) (hdj : (I.d j : ℤ) = t)
    (hnos : ∀ k : I.Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, k ≠ j → ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Reachable I t X W' P' ↔
      j ∉ X ∧ (Reachable I t' X W' P' ∨ Reachable I t' (insert j X) W' P') := by
  rw [reachable_iff_model, reachable_iff_model, reachable_iff_model]
  exact (model I).reachable_due hq htt hdj hnos hnod

/--
---
conclusion: Lax496464.Lemma2.reachable_start
---
Equation (3). Job `j` may be taken, which costs `p_j` of preprocessing and needs a free
machine at `t`, or passed over.
-/
theorem reachable_start (I : Instance) (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (htt : t' < t) (hsj : s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Reachable I t X W' P' ↔
      (j ∉ X ∧ Reachable I t' X W' P') ∨
      (j ∈ X ∧ (X.erase j).card < I.machines ∧
        ∃ (W'' : ℕ) (P'' : ℤ), W'' + I.w j = W' ∧ Reachable I t' (X.erase j) W'' P'' ∧
          P'' + I.p j ≤ s j ∧ P'' + I.p j ≤ P') := by
  simp only [reachable_iff_model]
  exact (model I).reachable_start hq htt hsj hnos hnod

/--
---
conclusion: Lax496464.Lemma2.exists_reachable_iff
---
Past the last start time the alive set and the load carry no further information, so the
states of weight `W'` are exactly the feasible sets of weight `W'`.
-/
theorem exists_reachable_iff (I : Instance) {t : ℤ} (ht : ∀ k : I.Job, s k ≤ t) (W' : ℕ) :
    (∃ (X : Finset I.Job) (P' : ℤ), Reachable I t X W' P') ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W' := by
  simp only [reachable_iff_model]
  refine ((model I).exists_reachable_iff ht W').trans (exists_congr fun Z => ?_)
  exact and_congr_left fun _ => (feasible_iff_model Z).symm

end Lax496464Proofs.Section4
