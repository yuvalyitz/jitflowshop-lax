import Lax496464.Problems

/-!
---
title: Theorem 3
type: theorem
---
Two further programs, each fast when one quantity of the instance is small.

The endpoint sweep of Section 4 carries a subset of the jobs alive at the current
instant, and so runs in $O(W \cdot 2^{\omega} \cdot n)$ time, where $\omega$ is the
largest number of jobs alive at one instant.

The profile sweep of Section 5 carries, instead of that subset, only how many of its jobs
are due at each of the next $q_{\max}$ instants, and so runs in
$O(W \cdot m^{q_{\max}} \cdot n)$ time.

Neither bound involves the number of machines in the exponent, so both are useful
precisely where the program of the second theorem is not.

# Formalization notes

Two statements, one per program, each with its own fitting condition for its own table,
and each restricted to no slice: both programs decide the problem on every instance, and
what changes from one to the other is only the bound.

The width $\omega$ and the largest processing time $q_{\max}$ are functions of the word.
No claim is made that a program computes them — neither program needs to, since neither
allocates a table indexed by them in advance — but a running time stated in terms of a
quantity that was not a function of the input would not be a statement about a program at
all.

The second bound is written with $m+1$ rather than $m$ in the base, and both with $n+1$
rather than $n$, for the reason the second theorem gives: at the extremes the bare
product collapses to zero and no program answers in no instructions. The forms agree up
to the constant as soon as there is a job and a machine.

The sweep of Section 4 assumes the endpoints distinct, which the rescaling of the same
section supplies; that is a step of the proof and not a hypothesis of the claim, since
the rescaling is computed by the program itself.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Theorem3

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

open Classical in
/-- **Theorem 3, the endpoint sweep.** The problem is decided within
`c · (W+1) · 2^ω · (n+1)` instructions, plus the cost of sorting. -/
axiom theorem3_width_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) +
          c * sortCost x)

open Classical in
/-- **Theorem 3, the profile sweep.** The problem is decided within
`c · (W+1) · (m+1)^q_max · (n+1)` instructions, plus the cost of sorting. -/
axiom theorem3_qmax_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1)
            ≤ 2 ^ w ∧ (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
          (jobCount x + 1) + c * sortCost x)

end Lax496464.Theorem3
