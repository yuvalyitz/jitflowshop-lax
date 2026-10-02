import Lax496464.Conditions
import Lax496464.EstOrder

/-!
---
title: The Endpoint Sweep of Section 4, and Its Table
type: definition
---
The algorithm behind the first half of the third theorem. The time axis is swept from
left to right through the $2n$ *endpoints* — the start times and the due dates — and the
state carried at an instant $t$ is the set $X$ of selected jobs alive then, together with
the weight selected so far and the preprocessing time spent. The table entry
$$T_t[X, W']$$
records whether a feasible selection of weight $W'$, all of whose jobs have started by
$t$, is alive at $t$ in exactly $X$ and costs at most $P'$ to preprocess.

Between two consecutive endpoints nothing happens, and at an endpoint exactly one thing
does: a job becomes due, or a job starts. The two recursions of Section 4 say what each
does to the table.

Since $X$ is a set of jobs alive at one instant, it has at most $\omega$ members, so the
table has $2^\omega$ columns — which is where the running time comes from.

# Formalization Notes

The table is again a predicate rather than a value, downward closed in the preprocessing
budget, for the reason given for the table of Section 3.

The state is the set of *selected* jobs alive at $t$, not a set of machines: which machine
runs which job never matters, because at most $m$ jobs alive at once is the whole of
Condition 2. That is the depth characterization, and it is what makes a subset of the
alive jobs the right index.

The preprocessing budget runs forwards here and backwards in Section 3, so the two
programs carry the same information in opposite directions. Nothing is claimed about
their relationship; each is proved against the definition of a feasible set.

The endpoints are collected as a finite set of integers, with no order imposed. The
sweep's step needs consecutive endpoints, and that two consecutive ones enclose exactly
one event is where the distinctness of the endpoints is used.
-/

namespace Lax496464.Sweep

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- The total preprocessing time of `Z`. -/
def pload (Z : Finset I.Job) : ℤ := ∑ i ∈ Z, (I.p i : ℤ)

/-- The table: a feasible set of weight `W'`, all of whose jobs have started by `t`, is
alive at `t` in exactly `X` and costs at most `P'` to preprocess. -/
def Reachable (t : ℤ) (X : Finset I.Job) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, Feasible I Z ∧ (∀ k ∈ Z, s k ≤ t) ∧
    running I Z t = X ∧ weight I Z = W' ∧ pload I Z ≤ P'

/-- The `2n` endpoints: the start times and the due dates. -/
def endpoints : Finset ℤ :=
  (Finset.univ.image fun k : I.Job => s k) ∪
    (Finset.univ.image fun k : I.Job => (I.d k : ℤ))

end Lax496464.Sweep
