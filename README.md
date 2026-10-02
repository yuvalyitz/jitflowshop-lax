# Just-in-Time Scheduling in Two-Stage Flexible Flow Shops and the W-Hierarchy

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-496464`) formalizing the
paper of Heeger, Hermelin, Itzhaki, Schieber and Shabtay on the two-stage flexible flow shop
`FF(1,m) || ∑ w_j Z_j`: the characterization of the sets of jobs that can all be completed
just in time, the five algorithms built on it, and the hardness of the general case. See
`abstract.md` for the mathematics.

The submission also includes the W-hierarchy foundations used by parameterized hardness
proofs, following Flum and Grohe (2006): FPT-reductions, W[1] = A[1], W[1]-completeness of
Clique, Independent Set and Multicoloured Clique, and W[2]-completeness of Hitting Set and
Dominating Set. These are documented in the `WH_*` concept modules.

**Scope.** The annotated manuscript covers the flow-shop results. The W-hierarchy material
is documented in the archive's concept pages and Lean modules.

**Contents.** The merged submission contains 72 concepts and 133 proof entries. Its proofs
use Lean's standard axioms and explicitly declared statements from archive dependencies.
The archive's proof network records how those statements are discharged.

## What Is Proved

| Result | Statement | Concept |
|---|---|---|
| Observation 1, Section 2 | Feasibility characterization by the two conditions; earliest-start-time order; distinct endpoints | `Feasibility`, `Conditions`, `Observation1`, `Normalization` |
| Lemma 1, Theorem 2 | Recursion (1) is correct; the table is filled in `O(W n^m)` | `Lemma1`, `Theorem2` |
| Lemma 2, Theorem 3 | The endpoint sweeps are correct; running times `O(W 2^ω n)` and `O(W m^{q_max} n)` | `Lemma2`, `Theorem3` |
| Lemma 3 | Recursion (5) over due-date profiles, shown correct as printed | `Lemma3`, `Profile` |
| Lemma 4, Theorem 4 | The greedy for equal preprocessing times is optimal, in `O(n log n)` | `Lemma4`, `Theorem4` |
| Lemma 5, Theorem 4 | Proper instances: consecutive ones, hence a totally unimodular integer program | `Lemma5`, `ConsecutiveOnes` |
| Theorem 5 | Fully polynomial approximation scheme when `m`, the width or `q_max` is bounded | `Theorem5`, `Fptas` |
| Corollaries 1–3 | `O(n^2)` for `m = 1` unweighted; the dual table in `O(P n^m)`; `O(n^{m+1})` for equal preprocessing times | `Corollary1`, `Corollary2`, `Corollary3` |
| Theorem 1, Corollary 4 | Strong NP-hardness even with unit weights, and W[2]-hardness in `m`, by reduction from Hitting Set | `Theorem1`, `Corollary4`, `W2Hardness` |
| Karp (cited by the paper) | Hitting Set is NP-hard, by reduction from satisfiability; correctness and polynomial time of the reduction | `HittingSet`, `HittingSetFromSat`, `HittingSetHardness` |

Each running-time statement is proved as a word RAM program, written in IMP+, compiled by the
archive's verified compiler, and shown to compute the stated function within the stated number
of instructions on the word encoding of an instance.

## Deviations from the Printed Text

These are settled in the concept modules' formalization notes:

- The reduction from Hitting Set is carried out for `k ≥ 2`, and with `k(n-1)+2` segments.
- The greedy is ordered by a counting order it also maintains.
- The running-time statements assume positive processing times and that the numbers fit in the
  word (`c · (|x| + v + 1)^c ≤ 2^w`); Theorem 5 additionally requires `c · ∑ w_j ≤ 2^w`.
- `Fptas.Delivers` asks for a certified lower bound `W` on the optimum with
  `(e-1) · optimum ≤ e · W`, rather than an attained value.
- The Hitting Set hardness statement carries the clause `n ≤ 4 + m + ∑ |F_j|`, which costs
  nothing and keeps the universe writable in time bounded by the word.

## Prerequisites

Lean `v4.33.0` via [elan](https://github.com/leanprover/elan), and the
[`lax` CLI](https://github.com/lax-archive/lax). The mathlib revision is pinned in
`manifest.yaml`.

## Verifying It

    lax build .

The strict build checks all 72 concepts and 133 proof entries. External dependencies are
pinned to registered archive commits, including ISEM (`lax-888481`) and RJLMax
(`lax-391470`). Warnings about dependencies on proof packages describe the reuse of
verified implementations; they do not indicate missing proofs.

To audit axioms, write a scratch file **outside** the package, import `Lax496464Proofs`,
`#print axioms` a conclusion theorem (each is tagged `conclusion:`), and run
`lake env lean` from `proofs/`.

> Anything placed inside `proofs/Lax496464Proofs/` must also be imported by
> `Lax496464Proofs.lean`, or the build is rejected.

## Reading It

Start with `concepts/` for the mathematical statements and their formalization notes.
Lean's kernel checks the proofs; the definitions and hypotheses still require mathematical
review.

Suggested order: `abstract.md`; `concepts/Lax496464/FlowShop.lean` and `Problems.lean`
(the model and its word encoding); `Feasibility.lean`; then the theorem modules. In `proofs/`,
the mathematics is under `Section*.lean`, `Bridge.lean` and `Model/`; the programs are under
`Ram/`, one family of files per algorithm (`T4*` greedy, `W3*` and `Q3*` sweeps, `D2*`–`D5*`
dual tables and the main dynamic program, `F5*` approximation scheme, `Total*` and
`Corollary4.lean` the reduction); `HittingSet/` holds the reduction from satisfiability to
Hitting Set (`Correct.lean` the mathematics, `Words.lean` the reduction on words, `Front.lean`
through `Final.lean` its word RAM program and the transfer to a Turing machine, `Hardness.lean`
the composition with the Cook–Levin theorem).

For the W-hierarchy, read `WH_A1_FptTime.lean` and `WH_A2_FptReductions.lean` first,
then the `WH_B*` logic and hierarchy definitions, the `WH_C*` problem definitions, and
the `WH_D*`, `WH_E*` and `WH_F*` completeness and hardness results. Their implementations
are under `concepts/Lax496464/WHierarchy/` and `proofs/Lax496464Proofs/WHierarchy/`.
