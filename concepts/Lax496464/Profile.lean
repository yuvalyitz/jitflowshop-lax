import Lax496464.Sweep
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat

/-!
---
title: The Due-Date Profile of Section 5, and Recursion (5)
type: definition
---
The algorithm behind the second half of the third theorem. It sweeps the start times in
order, and at the start time of job $j$ it carries, instead of the set of selected jobs
alive then, only their *profile*: the vector $\vec{x}$ whose $i$-th coordinate counts the
selected jobs due at $s_j + i$. Since a job's second operation is at most $q_{\max}$ long,
only the coordinates $1, \dots, q_{\max}$ can be nonzero, and each is at most $m$; the
table therefore has $m^{q_{\max}}$ columns.

Stepping from the previous start time to $s_j$ moves the reference point by
$\delta_j = s_j - s_{j-1}$, so a profile at $s_{j-1}$ becomes a profile at $s_j$ shifted
down by $\delta_j$. The paper writes $\vec{x}[\delta]$ for the vectors that shift to
$\vec{x}$, and recursion (5) has the two branches of every such sweep: job $j$ is passed
over, or job $j$ is selected, in which case its own coordinate $q_j$ drops by one.

# Formalization Notes

The profile is carried as a function on all $i \ge 1$ rather than as a vector of length
$q_{\max}$. This is deliberate. The coordinates beyond $q_{\max}$ are not free: the jobs
counted by the profile at $s_j$ all have due dates in $(s_j, s_j + q_{\max}]$, so those
coordinates are zero, and a formulation that leaves them out has to say so separately —
which is exactly what the printed recursion fails to do.

**The printed recursion is stated here as well, unchanged.** The paper writes
$$\vec{x}[\delta] = \{\vec{y} \in \{0,\dots,m\}^{q_{\max}} :
  y_i = x_{i-\delta} \text{ for all } i \in \{\delta+1, \dots, q_{\max}\}\},$$
which pins $\vec{y}$ on the coordinates above $\delta$ and leaves the *last* $\delta$
coordinates of the shifted vector unconstrained. They are not free, for the reason just
given, and leaving them so lets the recursion reach entries that no selection realizes —
in both of its branches. The consequence for the algorithm is nothing at all, which is
the content of the third theorem's second half: a reachable entry is still witnessed by a
feasible selection, only with a profile no larger than the one recorded, and since the
capacity test $\sum_i x_i \le m$ is then applied to the larger vector it can only reject
more. The optimum read off at the end is exact.

Both versions are therefore defined: the one with the missing condition supplied, whose
correctness is the lemma the paper states, and the printed one, whose correctness is the
weaker invariant the algorithm actually maintains. Keeping them apart is what lets both
be stated.

The printed recursion is given as an inductively defined relation — the entries it
derives — rather than as a table of values, since that is what "the recursion reaches
this entry" means and it needs no order of evaluation. Its coordinates are numbered from
zero, so coordinate $c$ counts the jobs due at $s_j + c + 1$.
-/

namespace Lax496464.Profile

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep

variable (I : Instance)

/-- The **due-date profile** of `Z` at `t`: the number of jobs of `Z` due at `t + i`. -/
def dueProfile (Z : Finset I.Job) (t : ℤ) (i : ℕ) : ℕ :=
  (Z.filter fun k => (I.d k : ℤ) = t + i).card

/-- The repaired table: a feasible set of weight `W'`, all of whose jobs have started by
`t`, has profile exactly `x` at `t` and costs at most `P'` to preprocess. -/
def ReachableProfile (t : ℤ) (x : ℕ → ℕ) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, Feasible I Z ∧ (∀ k ∈ Z, s k ≤ t) ∧
    (∀ i, 1 ≤ i → dueProfile I Z t i = x i) ∧ weight I Z = W' ∧ pload I Z ≤ P'

/-- The start time of the job before `k`, and `0` before the first job. -/
def sBefore (k : I.Job) : ℤ :=
  if h : (k : ℕ) = 0 then 0 else s (⟨(k : ℕ) - 1, by omega⟩ : I.Job)

/-- The paper's `δⱼ`: how far the reference point moves at job `k`. -/
def delta (k : I.Job) : ℕ := (s k - sBefore I k).toNat

variable {I}

/-- The paper's `x⃗^{(q)}`: the vector `x` with coordinate `c` decremented. -/
def decAt {qmax : ℕ} (x : Fin qmax → ℕ) (c : Fin qmax) : Fin qmax → ℕ :=
  Function.update x c (x c - 1)

variable (I)

/-- **Recursion (5), exactly as printed.** The entries it derives: the base
`T₀[0⃗, 0] = 0`, the convention `Tⱼ[0⃗, 0] = 0`, the capacity test `∑ xᵢ ≤ m` and `W' > 0`
on every other entry, and the two branches, each through the printed shift — which
constrains the earlier vector only on the coordinates at or above `δ`. -/
inductive Printed (qmax : ℕ) : ℕ → (Fin qmax → ℕ) → ℕ → ℤ → Prop
  /-- Before the first job, the empty selection. -/
  | init : Printed qmax 0 0 0 0
  /-- At any stage, the empty selection. -/
  | zero (t : ℕ) : Printed qmax t 0 0 0
  /-- Job `k` is passed over. -/
  | skip {k : I.Job} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ}
      (hcap : ∑ i, x i ≤ I.machines) (hW : 0 < W)
      (hshift : ∀ i : Fin qmax, ∀ hi : delta I k ≤ (i : ℕ),
        y i = x ⟨(i : ℕ) - delta I k, by have := i.isLt; omega⟩)
      (h : Printed qmax (k : ℕ) y W P) : Printed qmax ((k : ℕ) + 1) x W P
  /-- Job `k` is selected. -/
  | take {k : I.Job} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ} (c : Fin qmax)
      (hc : (c : ℕ) + 1 = I.q k) (hxc : 1 ≤ x c)
      (hcap : ∑ i, x i ≤ I.machines) (hW : 0 < W) (hwW : I.w k ≤ W)
      (hshift : ∀ i : Fin qmax, ∀ hi : delta I k ≤ (i : ℕ),
        y i = decAt x c ⟨(i : ℕ) - delta I k, by have := i.isLt; omega⟩)
      (h : Printed qmax (k : ℕ) y (W - I.w k) P) (hfit : P + I.p k ≤ s k) :
      Printed qmax ((k : ℕ) + 1) x W (P + I.p k)

end Lax496464.Profile
