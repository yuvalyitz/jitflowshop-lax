import Lax496464.Problems
import Lax496464.ProperInstances

/-!
---
title: Theorem 4
type: theorem
---
Two results for the case of equal preprocessing times.

Without weights, the greedy of Section 6.1 solves the problem in $O(n \log n)$ time,
which is the cost of putting the jobs into earliest-start-time order; everything after
that is one pass.

With weights, on a proper instance, the integer program of Section 6.2 has a totally
unimodular constraint matrix and can therefore be solved as a linear program, in
polynomial time. That case is stated here only through its first half; see the notes.

# Formalization Notes

The first statement is the running time of the greedy, on the slice of instances with
equal preprocessing times and unit weights. Its bound is the sorting term alone, which is
what the paper's $O(n \log n)$ says.

The second bullet has **no running-time statement here**, and that is deliberate. The
$O(n^{2.5} L)$ the paper quotes is the running time of a particular linear programming
algorithm, cited and not proved there, and the route from total unimodularity to an
integral optimum is the theorem of Hoffman and Kruskal, also cited. A running-time
statement for this case would therefore rest on two results from outside, neither of them
available in the background library, and asserting it would say nothing this submission
could support.

What Section 6.2 does establish is stated in full elsewhere, and proved: the scheduling
problem *is* that integer program (`Lemma5.ilp_correct`, `Lemma5.ilp_optimum`), its
constraint matrix has the consecutive ones property on a proper instance
(`Lemma5.lemma5`), and such a matrix is totally unimodular
(`Lemma5.matrix_isTotallyUnimodular`, via `ConsecutiveOnes.isTotallyUnimodular`, which is
proved rather than assumed). That is the mathematical content of the bullet; the step from
it to a running time is the citation.

The statement that remains is about the decision problem with a threshold, as the others
are, so that the whole submission speaks about one problem.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Theorem4

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax496464.ProperInstances
open Lax808846.Ram Lax808846.RamComputes

open Classical in
/-- **Theorem 4, the unweighted case.** With equal preprocessing times and unit weights,
the problem is decided within `c · n log n` instructions. -/
axiom theorem4_greedy_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
          (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * sortCost x)

end Lax496464.Theorem4
