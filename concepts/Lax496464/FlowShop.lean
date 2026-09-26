import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Just-in-time scheduling in a two-stage flexible flow shop
type: definition
---
An instance consists of $n$ jobs and $m$ identical second-stage machines. Job $j$ has a
preprocessing time $p_j \in \mathbb{N}$, a processing time $q_j \in \mathbb{N}$, a due
date $d_j \in \mathbb{N}$ and a weight $w_j \in \mathbb{N}$. It is run in two operations,
in this order and without preemption: a *preprocessing* operation of length $p_j$ on the
single first-stage machine, and a *processing* operation of length $q_j$ on one of the
$m$ identical second-stage machines. Job $j$ is completed *just in time* when its second
operation finishes exactly at $d_j$, and the objective is to maximize the total weight of
the just-in-time jobs. In the three-field notation the problem is
$FF(1,m) \mid\mid \sum_j w_j Z_j$.

Just-in-time completion pins the second operation of $j$ to the interval $[s_j, d_j)$,
where $s_j = d_j - q_j$; the first operation must therefore be finished by $s_j$, which
acts as a deadline for it. Two jobs *conflict* when those two intervals overlap, and
conflicting jobs cannot share a second-stage machine.

Since the objective counts only the just-in-time jobs, a *solution* is the set $Z$ of
jobs completed just in time, and $Z$ is *feasible* when its jobs — and no others — admit
a schedule completing every one of them exactly at its due date.

# Formalization notes

Jobs are `Fin n` rather than an abstract finite type: an instance is something a machine
is handed as a word, and a word presents its jobs in an order.

Start times are integers while the data are naturals, so that $s_j = d_j - q_j$ is a
genuine subtraction rather than a truncated one. A job with $q_j > d_j$ can never be
completed just in time, since its second operation would have to begin before time $0$;
the model excludes it by itself, and no side condition $q_j \le d_j$ appears anywhere.

The machine of a schedule is a number with a bound, rather than an element of
`Fin m`. The latter would make even the empty set unschedulable when $m = 0$, which is
wrong: scheduling nothing is always possible.

A schedule assigns a start time and a machine to every job, and its conditions are
imposed on the jobs of $Z$ only. What the jobs outside $Z$ are assigned is immaterial and
unconstrained, which is what the paper's convention — only the jobs of $Z$ are scheduled
— amounts to.
-/

namespace Lax496464.FlowShop

/-- An instance of the two-stage flexible flow shop: `jobs` jobs, `machines` identical
second-stage machines, and for each job a preprocessing time, a processing time, a due
date and a weight. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of identical second-stage machines. -/
  machines : ℕ
  /-- The first-stage (preprocessing) time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The second-stage (processing) time `q j` of job `j`. -/
  q : Fin jobs → ℕ
  /-- The due date `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

/-- A job of the instance. -/
abbrev Job : Type := Fin I.jobs

variable {I}

/-- `s j = d j - q j`: the time at which job `j`'s second operation must start if `j` is
to be completed just in time, and hence a deadline for its first operation. -/
def s (j : I.Job) : ℤ := (I.d j : ℤ) - I.q j

/-- Jobs `i` and `j` **conflict** when the intervals `[s i, d i)` and `[s j, d j)` of
their second operations overlap. Conflicting jobs cannot share a second-stage machine. -/
def Conflict (i j : I.Job) : Prop := s i < (I.d j : ℤ) ∧ s j < (I.d i : ℤ)

/-- A set of jobs is **independent** when no two of its members conflict, that is, when
it can be run on a single second-stage machine. -/
def Independent (Y : Finset I.Job) : Prop :=
  ∀ i ∈ Y, ∀ j ∈ Y, i ≠ j → ¬ Conflict i j

/-- A **just-in-time schedule of `Z`**: a schedule of the jobs in `Z` completing every
one of them exactly at its due date. `pre j` is the start time of `j`'s first operation
and `mach j` the second-stage machine running its second operation; the second operation
needs no start time, because just-in-time completion pins it to `[s j, d j)`. -/
structure JITSchedule (Z : Finset I.Job) where
  /-- The start time of the first operation of job `j`. -/
  pre : I.Job → ℤ
  /-- The second-stage machine of job `j`. -/
  mach : I.Job → ℕ
  /-- No operation starts before time `0`. -/
  pre_nonneg : ∀ j ∈ Z, 0 ≤ pre j
  /-- The preprocessing of `j` is finished by the time its second operation must start. -/
  pre_le_s : ∀ j ∈ Z, pre j + I.p j ≤ s j
  /-- The first stage is a single machine: its operations do not overlap. -/
  pre_disjoint : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
    pre i + I.p i ≤ pre j ∨ pre j + I.p j ≤ pre i
  /-- Only the `m` machines of the instance are used. -/
  mach_lt : ∀ j ∈ Z, mach j < I.machines
  /-- Conflicting jobs do not share a second-stage machine. -/
  mach_indep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → mach i = mach j → ¬ Conflict i j

variable (I)

/-- `Z` is **feasible**: its jobs can all be completed just in time. -/
def Feasible (Z : Finset I.Job) : Prop := Nonempty (JITSchedule Z)

/-- The objective value `w(Z) = ∑_{j ∈ Z} w j` of the solution `Z`. -/
def weight (Z : Finset I.Job) : ℕ := ∑ j ∈ Z, I.w j

/-- The decision version: some feasible set has weight at least `W`. -/
def HasWeight (W : ℕ) : Prop := ∃ Z : Finset I.Job, Feasible I Z ∧ W ≤ weight I Z

open Classical in
/-- The optimum: the largest weight of a feasible set. -/
noncomputable def optimum : ℕ :=
  (Finset.univ.filter fun Z : Finset I.Job => Feasible I Z).sup (weight I)

/-- The jobs of `Z` whose second operation is running at time `t`. -/
def running (Z : Finset I.Job) (t : ℤ) : Finset I.Job :=
  Z.filter fun i => s i ≤ t ∧ t < (I.d i : ℤ)

end Instance

end Lax496464.FlowShop
