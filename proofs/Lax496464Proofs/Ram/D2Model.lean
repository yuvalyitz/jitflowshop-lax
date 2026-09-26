import Lax496464Proofs.Ram.D2Ach

/-!
# Theorem 2 / Corollaries 2 and 3 on the word RAM: design and feasibility

**Feasibility verdict.**  The bound printed in `Theorem2.theorem2_time`,
`c·(W+1)·(n+1)^m + c·sortCost`, *is* attainable, with no factor `m`, so no repair of the concept
statement is needed beyond the positive-processing-time domain clause already approved (Corollary 1
and Theorem 4 precedent).  The "known problem" (a per-cell scan of `m` thresholds costs
`m·(W+1)·n^m`, and `m·n^m ≤ c(n+1)^m` fails uniformly in `m`) is avoided by charging the scan to the
*set*, not to the cell, and by the counting fact `Σ_{|X|≤m}(|X|+1) ≤ 2 (n+1)^m` (`D2Count`):

* a set `X` of at most `m` of the `n` indices is the number `c < (n+1)^m` whose digits (base `n+1`,
  most significant first) are its elements in increasing order, padded on the right with the digit
  `n` (`D2Digits`).  Only `C(n,≤m) ≤ (n+1)^m` of the `(n+1)^m` numbers are codes.
* `X₁`, `X₂` of recursion (1) replace the smallest threshold `j` by the first free index at or after
  `y = j+1`, respectively `y = nxt j`.  On the digit string that is one left-to-right scan of the
  tail (`D2Scan.scanF`, cost `O(|X|)`, **independent of `W`**) and one rotation of a prefix, in
  numbers `((c / b^q % b^k)·b + cur)·b^q + c % b^q` (`D2Scan.code_formula`).  The new code is larger
  than `c` (`D2Scan.code_lt`), so the codes are filled from `(n+1)^m - 1` downwards.
* which numbers are codes is decided in `O(1)` each by the recurrence `D2Valid.isCode_iff`
  (`VALID` array, filled in the same downward pass).
* per code: cost `O(|X|+1)` for the two scans, then `(W+1)` cells at `O(1)` each (two lookups,
  `Dp1.fNat`, a max, one store).  Total `O((n+1)^m + Σ(|X|+1) + (W+1)·#codes) = O((W+1)(n+1)^m)`.
* `m` large is harmless: for `n ≥ 1`, `m < 2^m ≤ (n+1)^m` pays for the `O(m)` set-up (powers of
  `n+1`, the code of the first `m` indices); `n = 0` is answered at once (`HasWeight` iff `W = 0`).

**The table is the monotone one.**  Weights are arbitrary numbers, so a table with a row for every
achievable weight cannot have `W+1` rows.  `D2Ach.AchGe X W' P'` ("some set of weight *at least*
`W'` compatible with `X` is preprocessable from `P'`") has recursion
`T[X,W'] = max(T[X₁,W'], f(T[X₂, W' ∸ w_j]))` with truncated subtraction (`D2Ach.achGe_rec`, from
Lemma 1), and the answer is the single entry `T[first m, W]` (`Theorem2.achievable_readoff`).  Entries
are coded by `DpCore.Rep`, exactly as in `Dp1`.

**Corollary 2 / 3** (dual table): not started.  Same set-indexing (`D2Digits`/`D2Scan`/`D2Valid`/
`D2Scan1`/`D2Valid1`); only the row block differs: `D[X,t] = max(D[X₁,t], w_j + D[X₂, t+π_j])` with
`min(W,·)` capping, rows `t ≤ R` (`R = P` with `π_j = p_j`, instant `t`; `R = n` with `π_j = 1`, instant
`t·p`), the dual recursion being `Lemma 1` on the exact-weight predicate maximised over weight, and the
guard `t+π_j ≤ R` redundant on cells reachable from `(firstM, 0)`.

## Status

**Theorem 2 is proved**: `D2Final.theorem2_time_proved` (tagged `conclusion:
Lax496464.Theorem2.theorem2_time`, type-checked against the axiom; the concept's `(m+1)` factor is
not needed, `D2Final.theorem2_time_printed` proves the bound as first printed).  File map:

* pure: `D2Digits` (codes), `D2Scan` (scan/rotation), `D2Valid` (`isCode_iff`), `D2Count`
  (`Σ(|X|+1) ≤ 2(n+1)^m`), `D2Ach` (monotone table, `X₁`/`X₂` on lists), `D2Tab` (table invariant),
  `D2StepPure` (what one step establishes), `D2Answer` (reading the answer, trivial cases);
* machine phases: `D2Scan1`, `D2Valid1`, `D2Rows`, `D2Setup` (powers, code of the first `m`
  indices), `D2Bsearch` (`NX` in `O(n log n)`), `D2Step` (one number, the loop);
* assembly: `D2Core` (**`core2`**, `core2_spec`: the whole column of the first `m` indices),
  `D2Prog` (`finishCom`, `prog2`), `D2Layout`, `D2Bound` (`cost2_le`), `D2Final`.

**Core / finish split (for reuse, e.g. the FPTAS).**  `D2Core.core2` reads the weights from the
sorted array `WS` and the threshold from the scalar `W`; `core2_spec` states, for every `r ≤ W`, that
the table entry of the first `m` indices at weight `r` is the `Rep` of `AchGe J (firstM J) r`.
`D2Prog.finishCom` is the only place the decision bit is formed.

The set-indexing files (`D2Digits` … `D2Scan1`, `D2Valid1`) do not mention the row block and are
reusable for the dual tables of Corollaries 2 and 3.
-/

namespace Lax496464Proofs.Ram.D2Model
end Lax496464Proofs.Ram.D2Model
