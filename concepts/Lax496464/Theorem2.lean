import Lax496464.DynamicProgram
import Lax496464.Problems

/-!
---
title: Theorem 2
type: theorem
---
Just-in-time scheduling in a two-stage flexible flow shop is solved in
$O(W \cdot n^m)$ time, where $W$ is the threshold, $n$ the number of jobs and $m$ the
number of second-stage machines: the table of Section 3 has $n^m$ columns and $W+1$ rows,
and recursion (1) fills each entry from two earlier ones.

The answer is read off the table at the $m$ smallest indices: a set of weight $W'$
compatible with them and preprocessable from the instant $0$ is exactly a feasible
solution of weight $W'$.

# Formalization notes

Two statements: the read-off, which is a combinatorial fact about the table, and the
running time, which is a claim about a program.

The read-off is what connects the recursion to the problem. Compatibility with the $m$
smallest indices is schedulability on $m$ machines and no more, and a budget of $0$ is
the first-stage machine starting at the beginning of time, so the two ends of the table
meet the definition of a feasible set. Without it the recursion would compute something
about a table and nothing about the shop.

The running time is stated with explicit constants rather than asymptotically, and with
the $+1$s the product needs to stay meaningful at the extremes: a threshold of zero, a
shop with no machines, and a shop with no jobs each drive the bare product to zero or
one, and no program answers in no instructions. The two forms agree up to the constant as
soon as there is a job and a machine.

The fitting condition carries a clause beyond the usual one, that the table itself fits
into memory. The table is indexed by a set of thresholds and a weight, and a machine
whose memory holds $2^w$ cells cannot address more than that; a statement that omitted it
would claim a running time the machine has no room to achieve.

The sorting term is the cost of putting the jobs into earliest-start-time order, which
Section 3 assumes done. It is the only place the input's own length enters the bound.

The domain also asks that every processing time be positive, $q_j \ge 1$. This is the paper's
standing assumption for the recursions behind the algorithms — a job with $q_j = 0$ has an
empty second operation, and the characterization of the feasible sets, on which everything
rests, is stated for jobs that have a genuine one — but the paper does not repeat it in each
claim, and a statement about a program that reads an arbitrary word has to.
-/

namespace Lax496464.Theorem2

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

/-- **The read-off.** A set of weight `W'` compatible with the `m` smallest indices that
can be preprocessed from a nonnegative instant is exactly a feasible set of weight `W'`. -/
axiom achievable_readoff (I : Instance) (hest : EstOrdered I) (W' : ℕ) :
    (∃ P' : ℤ, 0 ≤ P' ∧ Achievable I (firstM I) W' P') ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W'

open Classical in
/-- **Theorem 2.** One word RAM program decides the problem within
`c · (W+1) · (n+1)^m` instructions, plus the cost of sorting, at every word length
admitting the instance and its table. -/
axiom theorem2_time :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ DecisionInstances ∧ Fits c w x ∧
          c * (threshold x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j)}
        (fun x => if Yes x then [1] else [0])
        (fun x => c * (threshold x + 1) * (jobCount x + 1) ^ machineCount x +
          c * sortCost x)

end Lax496464.Theorem2
