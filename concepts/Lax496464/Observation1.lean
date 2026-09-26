import Lax496464.Conditions

/-!
---
title: Observation 1
type: theorem
---
A feasible set of jobs admits a just-in-time schedule whose first stage runs the jobs in
nondecreasing order of their start times $s_j$ — earliest start time first. So nothing is
lost by looking only at schedules that preprocess in that order, and an algorithm that
decides which jobs to select need not also decide in which order to preprocess them.

# Formalization notes

The conclusion is stated as a property of one schedule of the given set rather than as a
claim about an optimal schedule of the instance. The two are the same: an optimal
solution is a feasible set of largest weight, and the statement replaces any schedule of
a feasible set by one in earliest-start-time order without changing the set. Phrased this
way the statement needs no notion of optimality and applies to every feasible set, which
is how the paper's algorithms use it.

The order is on start times rather than on indices, and jobs with equal start times are
left unordered: the exchange argument produces a schedule in which $s_i < s_j$ forces
$i$'s first operation to finish before $j$'s begins, and says nothing about ties.
-/

namespace Lax496464.Observation1

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- **Observation 1.** Every feasible set has a just-in-time schedule that preprocesses
in nondecreasing order of start times. -/
axiom exists_est_schedule (I : Instance) (Z : Finset I.Job) (h : Feasible I Z) :
    ∃ σ : JITSchedule Z, ∀ i ∈ Z, ∀ j ∈ Z, s i < s j → σ.pre i + I.p i ≤ σ.pre j

end Lax496464.Observation1
