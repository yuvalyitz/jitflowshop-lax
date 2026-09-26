import Lax496464.DynamicProgram

/-!
---
title: Lemma 1
type: theorem
---
Recursion (1) is correct. Let $X$ be a set of thresholds whose smallest member is $j$.
A set of weight $W'$ compatible with $X$ can be preprocessed from $P'$ exactly when one
of the following holds:

* a set of weight $W'$ compatible with $X_1$ can be preprocessed from $P'$ — job $j$ is
  not selected; or
* $w_j \le W'$, the first-stage machine can finish job $j$ by $s_j$ when it starts at
  $P'$, and a set of weight $W' - w_j$ compatible with $X_2$ can be preprocessed from
  $P' + p_j$ — job $j$ is selected, and is preprocessed first.

# Formalization notes

The lemma is an equivalence, and both directions are needed: one says the recursion never
returns an entry no solution realizes, the other that it misses none.

The harder direction is the one that takes a solution compatible with $X$, in which $j$
is not selected, and re-assigns its jobs to the thresholds of $X_1$. The paper does this
by sliding the machines' assignments up by one, which is an application of Hall's marriage
theorem: the jobs that were on $j$ must move, and a threshold above them is free exactly
because the jobs alive at any instant are few enough.

The hypothesis that the processing times are positive is used, and only in this
direction. A job with $q_j = 0$ has an empty interval, conflicts with nothing, and may sit
on the threshold $j$ below the cutoff $d_j$ — which is exactly the configuration the
slide rules out. Soundness does not need it. The paper assumes positive processing times
throughout.

The two branches are stated with the paper's own $X_1$ and $X_2$, including the cases in
which $j_1$ or $j_2$ does not exist, where the threshold is dropped without replacement.
-/

namespace Lax496464.Lemma1

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.DynamicProgram

/-- **Lemma 1.** Recursion (1) computes the table. -/
axiom achievable_recursion (I : Instance) (hest : EstOrdered I) (hq : ∀ j : I.Job, 0 < I.q j)
    {X : Finset I.Job} {j : I.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x)
    (W' : ℕ) (P' : ℤ) :
    Achievable I X W' P' ↔
      Achievable I (X1 I X j) W' P' ∨
        (I.w j ≤ W' ∧ P' + I.p j ≤ s j ∧
          Achievable I (X2 I X j) (W' - I.w j) (P' + I.p j))

end Lax496464.Lemma1
