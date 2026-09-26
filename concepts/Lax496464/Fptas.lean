import Lax496464.Problems

/-!
---
title: Rounding the weights, and what an approximation scheme delivers
type: definition
---
The rounding behind the fifth theorem, and the shape of the guarantee it gives.

Rounding every weight up to a multiple of $k$ and dividing by $k$ leaves an instance with
the same jobs whose weights are smaller by a factor of about $k$. A set that is optimal
for the rounded weights loses, against the true optimum, at most $k$ per job selected,
hence at most $kn$ in total; and since the optimum is at least the largest single weight,
choosing $k$ so that $kn$ is a small fraction of the largest weight makes the loss a small
fraction of the optimum. That is the chain of inequalities (8), and what it delivers is
stated with the theorem that uses it.

An *approximation scheme* is a program that is handed an instance together with a
positive integer $e$ and returns a number $W$ that a feasible set reaches, and that is within
a factor $1 - 1/e$ of the optimum.

# Formalization notes

The accuracy is a positive integer $e$ rather than a rational $\varepsilon$, and the
guarantee is written as $(e-1)\,\mathrm{opt} \le e\,W$. This is the same statement as
$(1-\varepsilon)\,\mathrm{opt} \le W$ with $\varepsilon = 1/e$, in whole numbers, which
is what the input of a machine and the arithmetic of the bound both want. A scheme for
every $1/e$ is a scheme for every $\varepsilon$, since every positive rational exceeds
some $1/e$.

The program returns a *number* rather than the set: a value $W$ such that some feasible set
has weight at least $W$, and such that $(e-1)\,\mathrm{opt} \le e\,W$. Since $W$ never exceeds
the optimum either, this is the usual value form of an approximation guarantee, and there is
a feasible set whose weight is at least $W \ge (1-1/e)\,\mathrm{opt}$. The output is a single
number, as the decision programs' is. The program is not asked to name that set, nor to
return its exact weight: which is not something the exact algorithms it is built from
retain, and which the paper's guarantee does not constrain.

What a scheme delivers is not a function of its input — many sets meet the guarantee — so
it cannot be stated through the notion of computing a function within a time bound. It is
stated directly: on every admissible input the machine halts within the bound, having
written some output that meets the guarantee.

The instance is presented without a threshold, with the accuracy in the position the
threshold would occupy. An approximation instance is therefore a decision instance read
differently, which costs nothing and keeps one format.
-/

namespace Lax496464.Fptas

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.WordEncoding Lax496464.Problems
open Lax808846.Ram

variable (I : Instance)

/-- The largest weight of a single job. -/
def wmax : ℕ := ((List.finRange I.jobs).map I.w).foldr max 0

/-- The instance with every weight rounded up to a multiple of `k` and divided by it. -/
def rescale (k : ℕ) : Instance where
  jobs := I.jobs
  machines := I.machines
  p := I.p
  q := I.q
  d := I.d
  w j := (I.w j + (k - 1)) / k

variable {I}

variable (I)

/-- The word `x` presents the instance `I` together with the accuracy `e`. -/
def EncodesApprox (x : List ℕ) (e : ℕ) : Prop :=
  ∃ y, x = y ++ [e] ∧ 1 ≤ e ∧ EncodesInstance y I

variable {I}

/-- The words that present an instance together with an accuracy. -/
def ApproxInstances : Set (List ℕ) := {x | ∃ I e, EncodesApprox I x e}

/-- The output `y` is an acceptable answer on the input `x`: a number that some feasible set
reaches, within a factor `1 − 1/e` of the optimum. -/
def Delivers (x y : List ℕ) : Prop :=
  ∃ (I : Instance) (e W : ℕ), EncodesApprox I x e ∧ y = [W] ∧
    HasWeight I W ∧ (e - 1) * optimum I ≤ e * W

/-- At word length `w`, on every admissible input, the program halts within `T x`
instructions having written an acceptable answer. -/
def ApproximatesInTime (w : ℕ) (prog : Program) (D : Set (List ℕ))
    (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ (y : List ℕ) (t : ℕ), t ≤ T x ∧ RunsTo w prog x y t ∧ Delivers x y

end Lax496464.Fptas
