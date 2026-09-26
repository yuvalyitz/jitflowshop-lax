# Just-in-time scheduling in two-stage flexible flow shops

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-496464`) formalizing the
paper of Heeger, Hermelin, Itzhaki, Schieber and Shabtay on the two-stage flexible flow shop
`FF(1,m) || ∑ w_j Z_j`: the characterization of the sets of jobs that can all be completed
just in time, the five algorithms built on it, and the hardness of the general case. See
`abstract.md` for the mathematics.

**Status: complete.** All 41 statements are proved, with no `sorry`. This includes the
NP-hardness of Hitting Set (Karp 1972; Garey and Johnson 1979, problem SP8), proved by the
standard reduction from satisfiability. Every conclusion depends only on Lean's three standard
axioms, except that the hardness statements (Theorem 1 and `HittingSetHardness`) additionally
use three statements of archive submissions they depend on: the Cook–Levin theorem
(`Lax429075.SATHard.hardness`), the round trip of its CNF encoding
(`Lax429075.EncodingCorrect.roundtrip`), and the equivalence of word RAM and Turing machine
polynomial time (`lax-759944`).

## What is proved

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

## Deviations from the printed text

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

## Verifying it

    lax build --nonstrict .

reports `38 concepts · 41 proofs`. `--nonstrict` is needed only because the proofs package
depends on `lax-391470` (One-machine `R_j, L_max`) through a local path; a strict build needs
that submission registered and required by its commit. The remaining warnings are structural
(four proof-package dependencies, two sibling paths) and unused-lemma notes for declarations
Lean generates itself, structure fields, and definitional `simp` lemmas that other proofs use
only through `simp`.

To audit axioms, write a scratch file **outside** the package, import `Lax496464Proofs`,
`#print axioms` a conclusion theorem (each is tagged `conclusion:`), and run
`lake env lean` from `proofs/`.

> Anything placed inside `proofs/Lax496464Proofs/` must also be imported by
> `Lax496464Proofs.lean`, or the build is rejected.

## Reading it

Read `concepts/` and let the build vouch for `proofs/`: the statements are short, the proofs
about 51,000 lines. Lean's kernel checks the proofs; only a reader can judge whether the
statements say what they claim.

Suggested order: `abstract.md`; `concepts/Lax496464/FlowShop.lean` and `Problems.lean`
(the model and its word encoding); `Feasibility.lean`; then the theorem modules. In `proofs/`,
the mathematics is under `Section*.lean`, `Bridge.lean` and `Model/`; the programs are under
`Ram/`, one family of files per algorithm (`T4*` greedy, `W3*` and `Q3*` sweeps, `D2*`–`D5*`
dual tables and the main dynamic program, `F5*` approximation scheme, `Total*` and
`Corollary4.lean` the reduction); `HittingSet/` holds the reduction from satisfiability to
Hitting Set (`Correct.lean` the mathematics, `Words.lean` the reduction on words, `Front.lean`
through `Final.lean` its word RAM program and the transfer to a Turing machine, `Hardness.lean`
the composition with the Cook–Levin theorem).
