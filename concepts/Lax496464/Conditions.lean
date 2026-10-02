import Lax496464.FlowShop

/-!
---
title: The Two Conditions on a Feasible Set
type: definition
---
Two conditions on a set $Z$ of jobs, one for each stage of the shop.

**Condition 1**, *$Z$ can be preprocessed in time*: for every $j \in Z$, the jobs of $Z$
whose second operations start no later than $j$'s fit, together, into $[0, s_j)$.

**Condition 2**, *$Z$ can be scheduled on $m$ machines*: the jobs of $Z$ can be
partitioned into $m$ sets, no one of which contains two conflicting jobs.

# Formalization Notes

The paper writes Condition 1 as $\sum_{i \in Z,\ i \le j} p_i \le s_j$ with the jobs
indexed in nondecreasing order of $s$. That phrasing pins the sum down only once ties are
broken, and where the $s$ values are not distinct the form used here is the one the paper
means: two jobs with the same $s$ must *both* have been preprocessed by that time, so
both lengths count. A prefix of an enumeration that stopped at the first of them would
not. Sections 4 and 6 arrange for the $s$ values to be distinct, and there the two
readings agree; that they do is a statement of this submission rather than a convention
of this file, and so is the fact that the reading below is equivalent to the existence of
an actual schedule.

Condition 2 is written as a colouring rather than as a partition. The data are the same —
a colour is the index of the part a job goes into — and a function is what the
formalization of a schedule uses; that a partition can be recovered is immediate. The
colour of a job outside $Z$ is unconstrained.

The sums are taken in $\mathbb{Z}$, where the start times live, so that no truncated
subtraction appears in the condition.
-/

namespace Lax496464.Conditions

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- **Condition 1.** `Z` can be preprocessed in time: for every `j ∈ Z`, the jobs of `Z`
starting no later than `j` fit together into `[0, s j)`. -/
def Preprocessable (Z : Finset I.Job) : Prop :=
  ∀ j ∈ Z, ∑ i ∈ Z.filter (fun i => s i ≤ s j), (I.p i : ℤ) ≤ s j

/-- **Condition 2.** `Z` can be scheduled on the `m` second-stage machines: its jobs can
be coloured with `m` colours so that no two conflicting jobs share a colour. -/
def MSchedulable (Z : Finset I.Job) : Prop :=
  ∃ c : I.Job → ℕ, (∀ j ∈ Z, c j < I.machines) ∧
    ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ Conflict i j

end Lax496464.Conditions
