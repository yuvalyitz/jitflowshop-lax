import Lax496464.Fptas

/-!
---
title: Theorem 5
type: theorem
---
The problem admits a fully polynomial-time approximation scheme whenever one of the
number of machines, the width and the largest processing time is bounded.

Rounding the weights as in (8) leaves a threshold of order $n^2 e$ to search, where $e$ is
the reciprocal of the accuracy, so each of the three exact programs — the table of
Section 3, the endpoint sweep and the profile sweep — becomes an approximation scheme
whose running time is that of the program with $W$ replaced by $n^2 e$.

# Formalization notes

Four statements. The first is the rounding argument itself, the chain of inequalities (8),
which is where the approximation guarantee comes from and which says nothing about any
machine. The other three are the schemes, one per program, differing only in the factor
each contributes: the
$n^m$ of the second theorem, the $2^\omega$ of the first half of the third, and the
$m^{q_{\max}}$ of its second half. In each the threshold is gone, replaced by the $n^2 e$
that the rounding leaves, which is what makes the scheme fully polynomial in $1/\epsilon$.

The guarantee is the one an approximation scheme gives, so the statements are about a
machine that halts within a bound having written *some* acceptable answer, rather than
about one computing a function.

The rounding argument assumes what Section 7 assumes of its input: that there is a machine
to run a job on, and that every job can be preprocessed on its own, $p_j \le s_j$, jobs
failing which are discarded. Both are needed, and the chain is false without them — an
instance whose heaviest job cannot be scheduled has $w_{\max} > \mathrm{OPT}$, and the
chain, which ends by replacing $w_{\max}$ by $\mathrm{OPT}$, has nothing to end at.

None of the three bounds is polynomial in the input alone: each carries the factor its
program carries, and what the theorem says is that the scheme is fully polynomial once
that factor is a constant. Stating the factor explicitly, rather than fixing the
parameter and hiding it in a constant, is what keeps the three statements comparable to
the theorems they come from.

The domain of each scheme also asks that the total weight of the jobs fit a word with room
for the constant, `c · ∑ wⱼ ≤ 2^w`: the scheme writes a number that a feasible set reaches,
which can be as large as the total weight, and the entries of the word are bounded
individually by the fitting condition but their sum is not, so without this clause an
instance of many heavy jobs has answers that no machine of that word length can write. The
factor `c` is the same constant as in the running time: the machine's memory layout needs
every value it writes to stay below a fixed fraction of `2^w`. Positive processing times are asked for as in the exact
programs the schemes are built from: the paper's standing assumption for the recursions behind
them.

What a scheme delivers is a number reached by a feasible set, not the exact weight of a set it
has in hand; see `Delivers`. That is what the rounding argument supports: the optimum for the
rounded weights gives a set whose true weight is within the guarantee, and the number written
is that weight less the rounding loss, which the set reaches.
-/

namespace Lax496464.Theorem5

open Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax496464.Fptas Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax808846.Ram

/-- **Chain (8).** If `e · k · n ≤ w_max` and `Zs` is optimal for the weights rounded by
`k`, then `Zs` is within a factor `1 − 1/e` of the true optimum. -/
axiom rescale_approx (I : Instance) {e k : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k)
    (hm : 0 < I.machines) (hpre : ∀ j : I.Job, (I.p j : ℤ) ≤ s j)
    (hkn : e * k * I.jobs ≤ wmax I) (Zs : Finset I.Job) (hZs : Feasible I Zs)
    (hopt : ∀ Z : Finset I.Job, Feasible I Z →
      weight (rescale I k) Z ≤ weight (rescale I k) Zs) :
    (e - 1) * optimum I ≤ e * weight I Zs

/-- **Theorem 5, from the table of Section 3.** An approximation scheme running within
`c · (n+1)² · (e+1) · (n+1)^m` instructions, plus the cost of sorting. -/
axiom theorem5_byMachines :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ApproximatesInTime w prog
        {x | x ∈ ApproxInstances ∧ Fits c w x ∧
          c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j) ∧
          c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
            (jobCount x + 1) ^ machineCount x ≤ 2 ^ w}
        (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
          (jobCount x + 1) ^ machineCount x + c * sortCost x)

/-- **Theorem 5, from the endpoint sweep.** An approximation scheme running within
`c · (n+1)² · (e+1) · 2^ω · (n+1)` instructions, plus the cost of sorting. -/
axiom theorem5_byWidth :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ApproximatesInTime w prog
        {x | x ∈ ApproxInstances ∧ Fits c w x ∧
          c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j) ∧
          c * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x *
            (jobCount x + 1) ≤ 2 ^ w}
        (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x *
          (jobCount x + 1) + c * sortCost x)

/-- **Theorem 5, from the profile sweep.** An approximation scheme running within
`c · (n+1)² · (e+1) · (m+1)^q_max · (n+1)` instructions, plus the cost of sorting. -/
axiom theorem5_byQmax :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ApproximatesInTime w prog
        {x | x ∈ ApproxInstances ∧ Fits c w x ∧
          c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j) ∧
          c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
            (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) ≤ 2 ^ w}
        (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
          (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) + c * sortCost x)

end Lax496464.Theorem5
