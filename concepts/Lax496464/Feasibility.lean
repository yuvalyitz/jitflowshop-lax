import Lax496464.Conditions

/-!
---
title: A set of jobs is feasible exactly when it satisfies both conditions
type: theorem
---
A set $Z$ of jobs can be completed just in time if and only if it satisfies Condition 1
and Condition 2. The two stages therefore decouple: the first-stage machine and the
second-stage machines constrain $Z$ separately, and any pair of schedules meeting the two
conditions can be combined into one schedule of the shop.

Condition 2 is in turn a *depth* condition: $Z$ fits on $m$ second-stage machines exactly
when at most $m$ of its jobs are running at any one instant. One direction is immediate,
since jobs running at a common instant pairwise conflict; the other is the perfectness of
interval graphs.

# Formalization notes

The characterization is what every algorithm of the paper runs on, so it is stated about
the schedule itself rather than assumed. `Feasible` unfolds to the existence of a
`JITSchedule`, a piece of data with five conditions; the theorem is what licenses
replacing it by the two conditions on the set.

The depth condition is used throughout the paper and proved nowhere in it. It is not an
immediate consequence of the partition formulation: the content is that greedily
colouring the jobs in order of their start times never needs more colours than the
largest number of jobs alive at one instant. It is stated here because the algorithms of
Sections 4, 5 and 6 index their tables by the jobs alive at an instant, and that index is
only the right one because of this equivalence.

The depth statement carries the hypothesis that the processing times of $Z$ are positive.
It is not cosmetic. A job with $q_j = 0$ has an empty interval, is therefore running at no
instant at all, and conflicts with nothing; it is invisible to the left-hand side of the
equivalence, while the right-hand side still has to give it a machine — which is possible
only if there is one. The paper assumes positive processing times throughout.

Decidability of feasibility is recorded as a separate statement, in the form the paper's
Observation 2 needs: it is enough to test the counting condition at the start times of
the selected jobs, of which there are at most $n$.
-/

namespace Lax496464.Feasibility

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Conditions

/-- **Section 2.** A set of jobs is feasible exactly when it can be preprocessed in time
and can be scheduled on the `m` second-stage machines. -/
axiom feasible_iff (I : Instance) (Z : Finset I.Job) :
    Feasible I Z ↔ Preprocessable I Z ∧ MSchedulable I Z

/-- **Condition 2 is a depth condition.** A set of jobs with positive processing times
fits on the `m` second-stage machines exactly when at most `m` of them are running at any
one instant. -/
axiom mSchedulable_iff_card_running_le (I : Instance) {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    MSchedulable I Z ↔ ∀ t : ℤ, (running I Z t).card ≤ I.machines

/-- **Observation 2.** Feasibility is decided by Condition 1 together with a count, at
the start time of each selected job, of the selected jobs running then. -/
axiom feasible_iff_conditions (I : Instance) {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    Feasible I Z ↔
      Preprocessable I Z ∧ ∀ j ∈ Z, (running I Z (s j)).card ≤ I.machines

end Lax496464.Feasibility
