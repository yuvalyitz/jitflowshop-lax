import Lax496464.Problems
import Lax496464.ProperInstances

/-!
---
title: Corollary 3
type: theorem
---
When all preprocessing times are equal, the problem is solved in $O(n^{m+1})$ time. With
$p_j = p$ the total preprocessing time a partial solution has spent is determined by how
many jobs it has selected, so the instant the dual table runs over takes only $n+1$
values, and the bound of the second corollary becomes $O(n \cdot n^m)$.

# Formalization notes

The slice is stated on the decoded instance, as the existence of a common preprocessing
time, rather than as a condition on the entries of the word. The two say the same thing
on an admissible word, and the first is the condition a reader checks the claim against.

The uniform case is a restriction on the instance only; no assumption is made about the
weights, which may be arbitrary. That is what distinguishes this corollary from the
unweighted case of the fourth theorem.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Corollary3

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax496464.ProperInstances
open Lax808846.Ram Lax808846.RamComputes

open Classical in
/-- **Corollary 3.** With equal preprocessing times the problem is decided within
`c · (n+1)^(m+1)` instructions, plus the cost of sorting. -/
axiom corollary3_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
          c * (jobCount x + 1) ^ (machineCount x + 1) ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (jobCount x + 1) ^ (machineCount x + 1) + c * sortCost x)

end Lax496464.Corollary3
