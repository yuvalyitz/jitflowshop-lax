import Lax496464.Sweep

/-!
---
title: Lemma 2
type: theorem
---
The two recursions of Section 4 are correct.

At an instant $t$ at which job $j$ becomes due and nothing else happens, the entries at
$t$ are those at the previous endpoint with $j$ either present or absent: $j$ is no
longer alive, so it has left the state, and whether it was selected is what the two cases
record. Equation (4).

At an instant $t$ at which job $j$ starts and nothing else happens, either $j$ is not
selected and the state is unchanged, or $j$ is selected, in which case it joins the
state, the state must still be small enough to fit on the machines, and the first-stage
machine must be able to finish $j$ by $t$. Equation (3).

Past the last start time the table answers the question: some state carries weight $W'$
exactly when a feasible set of weight $W'$ exists.

# Formalization Notes

Both equations are stated as equivalences, so each says at once that the recursion
invents no entry and loses none.

The hypotheses spell out what "nothing else happens" means: no other start time and no
other due date lies in the half-open interval between the two endpoints. On an instance
with distinct endpoints, consecutive endpoints satisfy exactly one of the two patterns,
which is what turns the two equations into a sweep.

Positive processing times are assumed, as everywhere in the paper. Here they are what
makes a job alive at its own start time, so that selecting a job really does put it into
the state.
-/

namespace Lax496464.Lemma2

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep

variable (I : Instance)

/-- **Equation (4).** The step across an instant at which job `j` becomes due. -/
axiom reachable_due (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (htt : t' < t) (hdj : (I.d j : ℤ) = t)
    (hnos : ∀ k : I.Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, k ≠ j → ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Reachable I t X W' P' ↔
      j ∉ X ∧ (Reachable I t' X W' P' ∨ Reachable I t' (insert j X) W' P')

/-- **Equation (3).** The step across an instant at which job `j` starts. -/
axiom reachable_start (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (htt : t' < t) (hsj : s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Reachable I t X W' P' ↔
      (j ∉ X ∧ Reachable I t' X W' P') ∨
      (j ∈ X ∧ (X.erase j).card < I.machines ∧
        ∃ (W'' : ℕ) (P'' : ℤ), W'' + I.w j = W' ∧ Reachable I t' (X.erase j) W'' P'' ∧
          P'' + I.p j ≤ s j ∧ P'' + I.p j ≤ P')

/-- **The read-off.** Past the last start time, a state of weight `W'` is exactly a
feasible set of weight `W'`. -/
axiom exists_reachable_iff {t : ℤ} (ht : ∀ k : I.Job, s k ≤ t) (W' : ℕ) :
    (∃ (X : Finset I.Job) (P' : ℤ), Reachable I t X W' P') ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W'

end Lax496464.Lemma2
