import Lax496464.Conditions
import Lax496464.EstOrder
import Lax496464.ProperInstances

/-!
---
title: The Greedy of Section 6.1, and Its Domination Order
type: definition
---
The algorithm behind the first half of the fourth theorem, for the case in which all
preprocessing times are equal and every weight is one. The jobs are taken in
earliest-start-time order, and a set $A$ of already selected jobs is maintained. On
reaching job $j$:

* if the first stage can still preprocess $|A| + 1$ jobs by $s_j$, and fewer than $m$ of
  the selected jobs are alive at $s_j$, then $j$ joins $A$;
* otherwise one job of $A \cup \{j\}$ with the largest due date is dropped, and the rest
  becomes the new $A$.

The set kept is compared to others through a *domination* order: $S$ dominates $S'$ when,
below every threshold, $S'$ has no more due dates than $S$.

# Formalization Notes

The greedy is given as a relation between the set before a step and the set after it,
not as a function. Both rules leave a choice — which job with the largest due date to
drop — and a relation covers every way of resolving it at once, so the theorem is about
the rule and not about one implementation of it.

**The domination order is not the paper's, and the paper's will not do.** Section 6.1
defines: $S$ dominates $S'$ if $|S| > |S'|$, or $|S| = |S'|$ and the $i$-th largest due
date in $S$ is not greater than the $i$-th largest in $S'$. The first disjunct throws
away all information about the due dates whenever the cardinalities differ, and the
induction needs it exactly there: in the step that drops a job, the set compared against
has one element fewer, so the induction hypothesis says only that the greedy's set is
*larger*, and "the job removed is the one with the largest due date" has nothing left to
act on.

Dropping the disjunct repairs it. Counting, for each threshold $t$, how many due dates of
a set lie at or below $t$ gives an order that is the paper's pointwise condition when the
cardinalities agree, that implies $|S'| \le |S|$, and that every greedy step preserves —
which is what the induction needs. Stating it by counting rather than by listing the
sorted due dates also turns every step of the argument into arithmetic.
-/

namespace Lax496464.Greedy

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- How many jobs of `Z` are due at or before `t`. -/
def dueCount (Z : Finset I.Job) (t : ℤ) : ℕ := (Z.filter fun i => (I.d i : ℤ) ≤ t).card

/-- **Domination.** `S` dominates `S'` when, below every threshold, `S'` has no more due
dates than `S`. -/
def SDom (S S' : Finset I.Job) : Prop := ∀ t : ℤ, dueCount I S' t ≤ dueCount I S t

/-- The first `k` jobs in earliest-start-time order. -/
def firstJobs (k : ℕ) : Finset I.Job := Finset.univ.filter fun i : I.Job => (i : ℕ) < k

/-- **One greedy step**, with common preprocessing time `p`: from `A` to `next` on
reaching job `j`. Either `j` is added, or a job of largest due date is dropped from
`A ∪ {j}`. -/
def Step (p : ℕ) (A next : Finset I.Job) (j : I.Job) : Prop :=
  (((A.card : ℤ) + 1) * p ≤ s j ∧ (running I A (s j)).card < I.machines ∧
      next = insert j A) ∨
  ((s j < ((A.card : ℤ) + 1) * p ∨ I.machines ≤ (running I A (s j)).card) ∧
    ∃ c ∈ insert j A, (∀ i ∈ insert j A, (I.d i : ℤ) ≤ (I.d c : ℤ)) ∧
      next = (insert j A).erase c)

end Lax496464.Greedy
