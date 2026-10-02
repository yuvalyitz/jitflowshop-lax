import Lax496464Proofs.Bridge
import Lax496464.Observation1

/-!
# Section 2: Feasibility Is Two Conditions, and the EST Normal Form

The paper's Section 2 replaces "the jobs of `Z` can all be completed just in time" by two
separate conditions — one about the single first-stage machine, one about the `m`
second-stage machines — and then works with those conditions throughout. `feasible_iff`
is that replacement.

Condition 2 is stated as a colouring, and every algorithm in the paper in fact tests it as
a *depth* condition: at most `m` of the selected jobs are alive at any instant. The paper
does not prove the two agree; `mSchedulable_iff_card_running_le` does, by the interval
colouring argument of `Model/IntervalColoring.lean`. Observation 2 is the decidable form
that follows, testing the depth only at the start times of the selected jobs.
-/

namespace Lax496464Proofs.Section2

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Conditions Bridge

/--
---
conclusion: Lax496464.Feasibility.feasible_iff
---
Transport `FFJ.feasible_iff` along the bridge. Both conditions are definitionally the same
on the two sides, so only the schedule structure has to be converted.
-/
theorem feasible_iff (I : Instance) (Z : Finset I.Job) :
    Feasible I Z ↔ Preprocessable I Z ∧ MSchedulable I Z :=
  (feasible_iff_model Z).trans ((model I).feasible_iff Z)

/--
---
conclusion: Lax496464.Feasibility.mSchedulable_iff_card_running_le
---
The interval colouring argument: a set of intervals of depth at most `m` is `m`-colourable,
by colouring in order of left endpoint and reusing the colour of an interval that has
already ended.
-/
theorem mSchedulable_iff_card_running_le (I : Instance) {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    MSchedulable I Z ↔ ∀ t : ℤ, (running I Z t).card ≤ I.machines :=
  (model I).mSchedulable_iff_card_running_le hq

/--
---
conclusion: Lax496464.Feasibility.feasible_iff_conditions
---
Condition 1 is a finite comparison of sums; Condition 2 need only be tested at the start
time of each selected job, since the busiest instant of a set of intervals is the left
endpoint of one of them.
-/
theorem feasible_iff_conditions (I : Instance) {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    Feasible I Z ↔
      Preprocessable I Z ∧ ∀ j ∈ Z, (running I Z (s j)).card ≤ I.machines :=
  (feasible_iff_model Z).trans ((model I).feasible_iff_conditions hq)

/--
---
conclusion: Lax496464.Observation1.exists_est_schedule
---
Rebuild the schedule from Condition 1 directly: preprocess the jobs in nondecreasing order
of start time, each as early as the previous one allows. Condition 1 is exactly what makes
every deadline met.
-/
theorem exists_est_schedule (I : Instance) (Z : Finset I.Job) (h : Feasible I Z) :
    ∃ σ : JITSchedule Z, ∀ i ∈ Z, ∀ j ∈ Z, s i < s j → σ.pre i + I.p i ≤ σ.pre j :=
  let ⟨σ, hσ⟩ := (model I).exists_est_schedule Z ((feasible_iff_model Z).mp h)
  ⟨ofModel σ, hσ⟩

end Lax496464Proofs.Section2
