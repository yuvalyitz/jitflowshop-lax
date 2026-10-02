import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

namespace Lax496464Proofs

/-!
# The Two-Stage Flexible Flow Shop `FF(1,m) || ∑ wⱼZⱼ`

The model of Heeger–Hermelin–Itzhaki–Schieber–Shabtay, *"Just-in-time scheduling in
two-stage flexible flow shops"*, EJOR 333 (2026) 652–664, Sections 1 and 2.

An instance has `n` jobs and `m` identical second-stage machines. Job `j` needs two
operations, run in this order and non-preemptively:

* a **preprocessing** operation of length `p j` on the *single* first-stage machine, and
* a **processing** operation of length `q j` on *one* of the `m` second-stage machines.

Job `j` also carries a due date `d j` and a weight `w j`, and is *completed just in time*
when its second operation finishes exactly at `d j`. The objective is to maximize the
total weight `∑ wⱼZⱼ` of the just-in-time jobs.

## What a Schedule Is Here

Because the objective counts only the just-in-time jobs, the paper adopts the convention
(Section 2, "we may assume that only jobs in `Z` are scheduled") that a solution *is* the
set `Z` of jobs completed just in time, and a set is **feasible** when the jobs in it —
and no others — admit a schedule completing every one of them exactly at its due date.
`JITSchedule` is that schedule, written out in full: a start time for each first
operation, a machine for each second operation, and the four constraints of the shop.

Just-in-time completion pins the second operation of `j` to the interval `[s j, d j)`,
where `s j = d j - q j` is its **start time**; the paper calls `s j` a deadline for the
first operation, since the first operation must be finished by then. Two jobs *conflict*
when those two intervals overlap, which is exactly when they cannot share a second-stage
machine. All of this is definitional here; `Section2.lean` proves the characterization
the paper's algorithms actually run on.

## Modelling Choices

* **Times are integers, magnitudes are naturals.** `p`, `q`, `d`, `w` are `ℕ`, as in the
  paper. Start times are `ℤ`, so `s j = d j - q j` is a genuine subtraction rather than a
  truncated one, and a job with `q j > d j` — which can never be just in time, since its
  second operation would have to begin before time `0` — is correctly excluded by the
  model rather than by a side condition. This is why `FFJ` carries no `q ≤ d` field.
* **Jobs are a `Fintype`, not `Fin n`.** As in `ISEM`, so that a gadget construction can
  name its jobs structurally — sums and subtypes of the objects they come from — instead
  of through an ad-hoc enumeration.
* **Machines are numbered by `ℕ`, with a bound.** `mach : Job → ℕ` plus
  `mach_lt : ∀ j ∈ Z, mach j < numMachines`, rather than `Job → Fin numMachines`. The
  latter would make a schedule of the *empty* job set impossible whenever `numMachines = 0`
  and `Job` is inhabited, which is wrong: scheduling nothing is always possible.
-/


/-! ## 1. Instances -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An instance of the two-stage flexible flow shop `FF(1,m) || ∑ wⱼZⱼ`.

`p j` is job `j`'s first-stage (preprocessing) time, `q j` its second-stage processing
time, `d j` its due date and `w j` its weight; `numMachines` is `m`, the number of
identical second-stage machines. The first stage is a single machine and is not counted
here. -/
structure FFJ where
  /-- The jobs. -/
  Job : Type
  /-- Finitely many of them. -/
  jobFintype : Fintype Job
  /-- With decidable equality. -/
  jobDecEq : DecidableEq Job
  /-- `m`, the number of identical second-stage machines. -/
  numMachines : ℕ
  /-- `p j`: the first-stage (preprocessing) time of job `j`. -/
  p : Job → ℕ
  /-- `q j`: the second-stage processing time of job `j`. -/
  q : Job → ℕ
  /-- `d j`: the due date of job `j`. -/
  d : Job → ℕ
  /-- `w j`: the weight of job `j`. -/
  w : Job → ℕ

attribute [instance] FFJ.jobFintype FFJ.jobDecEq

namespace FFJ

variable (I : FFJ)

/-- `n`, the number of jobs. -/
def numJobs : ℕ := Fintype.card I.Job

/-- `s j = d j − q j`: the time at which job `j`'s second operation must start if `j` is
to complete just in time — equivalently, a deadline for its first operation. -/
def s (j : I.Job) : ℤ := (I.d j : ℤ) - I.q j

/-! ## 2. Conflicts -/

/-- Jobs `i` and `j` **conflict** when their second operations' intervals `[s i, d i)` and
`[s j, d j)` overlap — the paper's Section 2 definition. Conflicting jobs cannot share a
second-stage machine. -/
def Conflict (i j : I.Job) : Prop := I.s i < (I.d j : ℤ) ∧ I.s j < (I.d i : ℤ)

lemma conflict_symm {i j : I.Job} (h : I.Conflict i j) : I.Conflict j i := ⟨h.2, h.1⟩

/-- Jobs whose intervals are separated do not conflict. -/
lemma not_conflict_of_le {i j : I.Job} (h : (I.d i : ℤ) ≤ I.s j) : ¬ I.Conflict i j :=
  fun hc => absurd hc.2 (not_lt.mpr h)

/-! ## 3. Schedules -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A **just-in-time schedule of `Z`**: a schedule of exactly the jobs in `Z` that
completes every one of them exactly at its due date.

`pre j` is the start time of `j`'s first operation and `mach j` the second-stage machine
running its second operation; the second operation itself needs no start time, because
just-in-time completion pins it to `[s j, d j)`. The five fields are, in order: first
operations start no earlier than time `0`; each first operation is finished by the time
its own second operation must start; the first operations do not overlap, since the first
stage is a single machine; the machines used exist; and conflicting jobs do not share a
machine. -/
structure JITSchedule (Z : Finset I.Job) where
  /-- The start time of job `j`'s first-stage operation. -/
  pre : I.Job → ℤ
  /-- The second-stage machine job `j` runs on. -/
  mach : I.Job → ℕ
  /-- Nothing starts before time `0`. -/
  pre_nonneg : ∀ j ∈ Z, 0 ≤ pre j
  /-- Job `j`'s preprocessing is finished by the time its second operation must start. -/
  pre_le_s : ∀ j ∈ Z, pre j + I.p j ≤ I.s j
  /-- The first stage is one machine: its operations do not overlap. -/
  pre_disjoint : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
    pre i + I.p i ≤ pre j ∨ pre j + I.p j ≤ pre i
  /-- Only the `m` available machines are used. -/
  mach_lt : ∀ j ∈ Z, mach j < I.numMachines
  /-- Conflicting jobs do not share a second-stage machine. -/
  mach_indep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → mach i = mach j → ¬ I.Conflict i j

/-- `Z` is **feasible**: its jobs can all be completed just in time. -/
def Feasible (Z : Finset I.Job) : Prop := Nonempty (I.JITSchedule Z)

/-- `w(Z) = ∑_{j ∈ Z} w j`, the objective value of the solution `Z`. -/
def weight (Z : Finset I.Job) : ℕ := ∑ j ∈ Z, I.w j

/-- The decision version: some feasible set has total weight at least `W`. -/
def HasWeight (W : ℕ) : Prop := ∃ Z : Finset I.Job, I.Feasible Z ∧ W ≤ I.weight Z

/-- The empty set is feasible. -/
theorem feasible_empty : I.Feasible ∅ :=
  ⟨{ pre := fun _ => 0, mach := fun _ => 0,
     pre_nonneg := by simp, pre_le_s := by simp, pre_disjoint := by simp,
     mach_lt := by simp, mach_indep := by simp }⟩

/-- A subset of a feasible set is feasible: drop the jobs, keep the schedule. -/
theorem Feasible.subset {Z Z' : Finset I.Job} (h : I.Feasible Z) (hsub : Z' ⊆ Z) :
    I.Feasible Z' := by
  obtain ⟨σ⟩ := h
  exact ⟨{ pre := σ.pre, mach := σ.mach,
           pre_nonneg := fun j hj => σ.pre_nonneg j (hsub hj),
           pre_le_s := fun j hj => σ.pre_le_s j (hsub hj),
           pre_disjoint := fun i hi j hj => σ.pre_disjoint i (hsub hi) j (hsub hj),
           mach_lt := fun j hj => σ.mach_lt j (hsub hj),
           mach_indep := fun i hi j hj => σ.mach_indep i (hsub hi) j (hsub hj) }⟩

/-! ## 4. The paper's two conditions

Section 2 reduces feasibility of a set `Z` to two separate conditions on it — one about
the first stage, one about the second. `Section2.lean` proves that the conjunction of
them is exactly `Feasible`. -/

/-- **Condition 1.** `Z` *can be preprocessed in time*: for every `j ∈ Z`, the jobs of `Z`
whose second operations start no later than `j`'s fit, together, into `[0, s j)`.

The paper writes this as `∑_{i ∈ Z, i ≤ j} pᵢ ≤ sⱼ` with the jobs indexed in
nondecreasing order of `s`. The two agree whenever the `s` values are distinct — which
the paper arranges in Sections 4 and 6 — and where they do not, the form below is the
correct one: two jobs with the same `s` must *both* be preprocessed by that time, so both
lengths count. `Section2.lean`'s `feasible_iff` is what certifies this reading, by
proving it equivalent to the existence of an actual schedule. -/
def Preprocessable (Z : Finset I.Job) : Prop :=
  ∀ j ∈ Z, ∑ i ∈ Z.filter (fun i => I.s i ≤ I.s j), (I.p i : ℤ) ≤ I.s j

instance decidablePreprocessable (Z : Finset I.Job) : Decidable (I.Preprocessable Z) :=
  inferInstanceAs (Decidable (∀ j ∈ Z,
    ∑ i ∈ Z.filter (fun i => I.s i ≤ I.s j), (I.p i : ℤ) ≤ I.s j))

/-- **Condition 2.** `Z` *can be scheduled on `m` machines*: its jobs can be coloured with
`m` colours so that no two conflicting jobs share one. The paper phrases this as a
partition of `Z` into `m` independent subsets `Z₁ ∪ ⋯ ∪ Z_m`; a colouring is the same
data, and `mSchedulable_iff_exists_partition` says so. -/
def MSchedulable (Z : Finset I.Job) : Prop :=
  ∃ c : I.Job → ℕ, (∀ j ∈ Z, c j < I.numMachines) ∧
    ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ I.Conflict i j

lemma Preprocessable.subset {Z Z' : Finset I.Job} (h : I.Preprocessable Z)
    (hsub : Z' ⊆ Z) : I.Preprocessable Z' := by
  intro j hj
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (h j (hsub hj))
  · exact Finset.filter_subset_filter _ hsub
  · intro i _ _; exact Int.natCast_nonneg _

/-- **Condition 1, applied to a sub-collection.** If every job of `D ⊆ Z` starts no later
than `j ∈ Z` does, then `D`'s jobs must all be preprocessed before `j`'s own start time,
so their total preprocessing time fits in `[0, s j]`.

This is the form Condition 1 gets used in: one picks the job of a prefix that starts last,
and reads off a bound on the whole prefix's preprocessing time. -/
lemma Preprocessable.sum_le {Z : Finset I.Job} (h : I.Preprocessable Z)
    {D : Finset I.Job} (hDZ : D ⊆ Z) {j : I.Job} (hj : j ∈ Z)
    (hmax : ∀ x ∈ D, I.s x ≤ I.s j) : ∑ x ∈ D, (I.p x : ℤ) ≤ I.s j := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => Int.natCast_nonneg _)
    (h j hj)
  intro x hx
  exact Finset.mem_filter.mpr ⟨hDZ hx, hmax x hx⟩

lemma MSchedulable.subset {Z Z' : Finset I.Job} (h : I.MSchedulable Z) (hsub : Z' ⊆ Z) :
    I.MSchedulable Z' := by
  obtain ⟨c, hlt, hindep⟩ := h
  exact ⟨c, fun j hj => hlt j (hsub hj),
    fun i hi j hj => hindep i (hsub hi) j (hsub hj)⟩

end FFJ

/-! ## 5. Ranking the elements of a finite set

A general utility, not about scheduling: the position of an element within a
`Finset (Fin n)`, counted from `0`. It is the cheapest way to turn a finite set into an
indexed family — no enumeration, no choice — and it is what both Section 8's machine
numbering and Section 3's compatibility relation use to fit `|X|` things into `|X|` slots. -/

namespace FlexFlowJIT

/-- The position of `i` among the elements of `H`, counting from `0`. -/
def rank {n : ℕ} (H : Finset (Fin n)) (i : Fin n) : ℕ := (H.filter (fun x => x < i)).card

lemma rank_lt {n : ℕ} {H : Finset (Fin n)} {i : Fin n} (hi : i ∈ H) : rank H i < H.card := by
  have hsub : H.filter (fun x => x < i) ⊆ H.erase i := by
    intro x hx
    obtain ⟨hxH, hxlt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxlt, hxH⟩
  have h1 : rank H i ≤ (H.erase i).card := Finset.card_le_card hsub
  have h2 : (H.erase i).card = H.card - 1 := Finset.card_erase_of_mem hi
  have h3 : 1 ≤ H.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

lemma rank_injOn {n : ℕ} {H : Finset (Fin n)} {i i' : Fin n} (hi : i ∈ H) (hi' : i' ∈ H)
    (h : rank H i = rank H i') : i = i' := by
  have key : ∀ a b : Fin n, a ∈ H → b ∈ H → a < b → rank H a < rank H b := by
    intro a b ha hb hab
    have hsub : H.filter (fun x => x < a) ⊆ H.filter (fun x => x < b) := by
      intro x hx
      obtain ⟨hxH, hxlt⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxH, lt_trans hxlt hab⟩
    have hss : H.filter (fun x => x < a) ⊂ H.filter (fun x => x < b) := by
      refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩, ?_⟩
      intro hcon
      exact absurd (Finset.mem_filter.mp hcon).2 (lt_irrefl a)
    exact Finset.card_lt_card hss
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (key i i' hi hi' hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (key i' i hi' hi hgt))


end FlexFlowJIT

end Lax496464Proofs
