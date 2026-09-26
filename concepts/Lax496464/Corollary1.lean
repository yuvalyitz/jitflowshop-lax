import Lax496464.Problems

/-!
---
title: Corollary 1
type: theorem
---
With a single second-stage machine and no weights, the problem is solved in $O(n^2)$
time. It is the program of the second theorem at $m = 1$: the table has $n$ columns, the
threshold is at most $n$ because every weight is one, and the two bounds multiply.

# Formalization notes

The claim is about the slice of instances with one machine and unit weights, so the
statement restricts the admissible words to those rather than asking a program to behave
on every input. A program is free to do anything outside the slice, which is what a claim
about a special case says.

No sorting term appears. Putting $n$ jobs into earliest-start-time order costs
$O(n \log n)$, which the bound already dominates.

The bound does not mention the length of the word, because the length of a word encoding
an instance is itself $\Theta(n)$ and the bound dominates it.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Corollary1

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

open Classical in
/-- **Corollary 1.** On one machine with unit weights, the problem is decided within
`c · (n+1)²` instructions. -/
axiom corollary1_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧ machineCount x = 1 ∧
          (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (jobCount x + 1) ^ 2)

end Lax496464.Corollary1
