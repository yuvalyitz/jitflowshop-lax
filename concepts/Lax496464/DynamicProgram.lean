import Lax496464.EstOrder
import Mathlib.Data.Finset.Max

/-!
---
title: The Dynamic Program of Section 3, and Its Table
type: definition
---
The algorithm behind the second theorem. The jobs are in earliest-start-time order and
are considered one at a time, from the last to the first. The state carried is a set $X$
of at most $m$ *thresholds*, one per second-stage machine: the smallest index a job on
that machine may have. The table entry
$$T[X, W']$$
is the earliest instant at which the first-stage machine may begin, if a set of jobs of
total weight $W'$ compatible with $X$ is still to be preprocessed in time. It is $-\infty$
when no such set exists, and $+\infty$ when the empty set will do.

A set $Z$ is *compatible with* $X$ when each of its jobs can be assigned a threshold in
$X$ not exceeding it, with no two conflicting jobs sharing a threshold. Taking $X$ to be
the first $m$ indices asks for nothing beyond schedulability on $m$ machines, which is
how the table is read off at the end.

The recursion removes the smallest threshold $j$ of $X$ and decides whether job $j$ is
selected. If it is not, $j$ is replaced by the smallest index above it that is not
already a threshold — the paper's $j_1$ — and the table is consulted at the resulting
$X_1$. If it is, the weight drops by $w_j$ and the budget by $p_j$, and $j$ is replaced by
the smallest index not already a threshold whose second operation starts at or after
$d_j$ — the paper's $j_2$ — giving $X_2$.

# Formalization Notes

The table is recorded as the predicate "a set of weight $W'$ compatible with $X$ can be
preprocessed starting from $P'$" rather than as a value in $\mathbb{Z}$ extended by two
infinities. The predicate is downward closed in $P'$, so it determines the value, and it
keeps the two infinities out of the statements: $-\infty$ is the predicate holding for no
$P'$ and $+\infty$ its holding for all of them, neither of which needs a name.

Compatibility is the paper's condition with the enumeration of machines removed. The
paper writes $X$ as a list $x_1 < \dots < x_m$ and assigns job $j$ to a machine index;
here a machine *is* its own threshold, so an assignment is a function into $X$. The two
carry the same information, and the second needs no bookkeeping to keep the list sorted.

$j_1$ and $j_2$ are `Option`-valued, since the paper's definitions do not always produce
an index, and $X_1$ and $X_2$ drop the threshold without replacement when they do not.
The paper does not treat these cases; they are exactly the cases in which no machine is
left waiting for a job above the one just decided, and dropping the threshold is what
that means.

The budget $P'$ is an integer, as start times are, and the preprocessing condition is
stated from an arbitrary starting instant rather than from zero, which is what makes it
the quantity a backwards recursion carries.
-/

namespace Lax496464.DynamicProgram

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- `Z` **is compatible with `X`**: every job of `Z` can be given a threshold in `X` not
exceeding it, no two conflicting jobs sharing a threshold. -/
def CompatibleWith (X Z : Finset I.Job) : Prop :=
  ∃ mach : I.Job → I.Job,
    (∀ j ∈ Z, mach j ∈ X) ∧ (∀ j ∈ Z, mach j ≤ j) ∧
      ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → mach i = mach j → ¬ Conflict i j

/-- `Z` **can be preprocessed from `P`**: starting at the instant `P`, the first-stage
machine finishes each job of `Z` by the time its second operation must start. -/
def PreprocessableFrom (Z : Finset I.Job) (P : ℤ) : Prop :=
  ∀ j ∈ Z, P + ∑ i ∈ Z.filter (fun i => i ≤ j), (I.p i : ℤ) ≤ s j

/-- The table: a set of weight `W'` compatible with `X` can be preprocessed from `P'`.
The paper's `T[X, W']` is the largest `P'` for which this holds. -/
def Achievable (X : Finset I.Job) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, weight I Z = W' ∧ CompatibleWith I X Z ∧ PreprocessableFrom I Z P'

/-- The paper's `j₁`: the smallest index above `j` that is not already a threshold. -/
noncomputable def j1 (X : Finset I.Job) (j : I.Job) : Option I.Job :=
  letI := Classical.decPred fun x : I.Job => x ∉ X ∧ j < x
  if h : (Finset.univ.filter fun x : I.Job => x ∉ X ∧ j < x).Nonempty then
    some ((Finset.univ.filter fun x : I.Job => x ∉ X ∧ j < x).min' h) else none

/-- The paper's `j₂`: the smallest index that is not already a threshold and whose second
operation starts at or after `d j`. -/
noncomputable def j2 (X : Finset I.Job) (j : I.Job) : Option I.Job :=
  letI := Classical.decPred fun x : I.Job => x ∉ X ∧ (I.d j : ℤ) ≤ s x
  if h : (Finset.univ.filter fun x : I.Job => x ∉ X ∧ (I.d j : ℤ) ≤ s x).Nonempty then
    some ((Finset.univ.filter fun x : I.Job => x ∉ X ∧ (I.d j : ℤ) ≤ s x).min' h) else none

/-- The paper's `X₁`: the thresholds after `j` is passed over. -/
noncomputable def X1 (X : Finset I.Job) (j : I.Job) : Finset I.Job :=
  match j1 I X j with
  | some y => insert y (X.erase j)
  | none => X.erase j

/-- The paper's `X₂`: the thresholds after `j` is selected. -/
noncomputable def X2 (X : Finset I.Job) (j : I.Job) : Finset I.Job :=
  match j2 I X j with
  | some y => insert y (X.erase j)
  | none => X.erase j

/-- The `m` smallest indices, the thresholds the table is read off at: a set compatible
with them is one that fits on `m` machines and nothing more. -/
def firstM : Finset I.Job := Finset.univ.filter fun i : I.Job => (i : ℕ) < I.machines

end Lax496464.DynamicProgram
