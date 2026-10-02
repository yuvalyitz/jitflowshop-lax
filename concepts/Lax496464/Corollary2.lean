import Lax496464.Problems

/-!
---
title: Corollary 2
type: theorem
---
The same table read the other way round solves the problem in $O(P \cdot n^m)$ time,
where $P = \sum_j p_j$ is the total preprocessing time: instead of recording, for each
weight, the latest instant at which the first stage may begin, record for each instant
the largest weight attainable from it. The recursion is the same and so is its
correctness; only the axis the table is indexed along changes.

This is the better of the two bounds whenever the preprocessing times are small and the
weights are not.

# Formalization Notes

No new combinatorial statement is needed. The dual table is the same predicate with its
two numerical arguments exchanged, so the correctness of recursion (1) is the correctness
of both programs, and only the running time is stated here.

The instants the table runs over are the partial sums of preprocessing times, of which
there are at most $P+1$; that is what makes $P$, rather than the largest due date, the
quantity in the bound.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Corollary2

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

open Classical in
/-- **Corollary 2.** The dual program decides the problem within `c · (P+1) · (n+1)^m`
instructions, plus the cost of sorting. -/
axiom corollary2_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (preSum x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (preSum x + 1) * (jobCount x + 1) ^ machineCount x +
          c * sortCost x)

end Lax496464.Corollary2
