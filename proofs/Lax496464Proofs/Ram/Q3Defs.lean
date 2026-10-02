import Lax496464Proofs.Ram.Dp1
import Lax496464Proofs.Ram.DpMArr
import Lax496464Proofs.Model.Lemma2_Sweep
import Lax496464.Profile

/-!
# Theorem 3, the Profile Sweep on a Word RAM: Design and the Definitions Everything Shares

## The Algorithm Behind `theorem3_qmax_time`

Statement: decide `Yes x` within `c·(W+1)·(m+1)^qmax·(n+1) + c·sortCost` instructions, on words
that fit at word length `w` with `c·(W+1)·(m+1)^qmax·(n+1) ≤ 2^w`.  It *can* be met, with the
`q_j > 0` domain clause (the standing assumption of Lemma 3; same precedent as Cor. 1 / Thm. 4).

* **Table.**  `bb = m+1`, `qm = qmax`, `bt = bb^qm` profiles, `w1 = W+1` weights, `N = bt·w1`
  cells; the profile `x = (x_1..x_qm)` (coordinate `i` = number of selected jobs due at
  `t+i+1`) is the base-`bb` number `∑ x_i bb^i` (digits `≤ m` because a feasible set has at most
  `m` jobs alive at once).  The cell `(x, c)` sits at flat index `x·w1 + c` in the array `"T"`.
  Cell value = least preprocessing load `P` of a feasible set of weight **at least `c`** (the
  `Ge`-relaxation: makes the weight step O(1)), `INF = maxd + 1` if none.
* **Sweep.**  Jobs in earliest-start order (ties broken arbitrarily: NO rescaling; ties simply
  give `δ = 0`).  Stage `k` has reference time `trefN k = max(0, s_{k-1})` (`= d_{k-1} - q_{k-1}`
  in `ℕ`, `0` for `k = 0`).  Event for job `k` (`δ = trefN (k+1) - trefN k`, `δ' = min δ qm`):
  1. `S[b][c] := min over y<bt with y / bb^δ' = b of T[y][c]`   (pass 1, ONE flat pass; the
     shift of the profile by `δ` is division by `bb^δ'`, the top `δ'` digits become 0 and the low
     `δ'` digits are marginalised, all at once; no zeta transform is needed);
  2. `T'[x][c] := min(S[x][c], S[x - bb^(q_k-1)][c - w_k] + p_k)` when digit `q_k-1` of `x` is
     `≥ 1`, digit sum of `x` is `≤ m` and `S[..] + p_k ≤ s_k`   (pass 2, one flat pass).
  Both passes cost O(1) per cell (division by `w1`, `pwd`, `pwq`, `bb`; IMP+ has `div`, no `mod`,
  `x mod b = x - (x / b) * b`).  Per event: fill `S` with INF, pass 1, pass 2: `O(N)`.  The
  powers `bb^δ'`, `bb^(q_k-1)` cost `O(qm)` per event, `qm < 2^qm ≤ bb^qm` when `bb ≥ 2`, and
  are O(1) when `bb = 1` (`m = 0`): the loop is skipped.  Total `O(N·(n+1))`; init `O(N)`;
  qmax / max-due scans `O(n)`; sort `sortCost`.  Degenerate cases `qm = 0` (n = 0), `m = 0`
  (`bt = 1`), `W = 0` (`w1 = 1`) are all covered by the same code.
* **Read-off.**  After all jobs, `Yes` iff some `x < bt` has `T[x][W] < INF`.

## Structure (Reused by Theorem 5)

`core` = everything from the sorted arrays `PS QS DS WS` and the scalars `n m W` to the final
table, with a Spec that describes the WHOLE final table (`TabSem bt w1 INF (Rsem ..) T`: for
every `c ≤ W` and every profile, whether weight `≥ c` is reachable within load `P`); `finish` =
the answer scan.  The weight array and `W` are inputs of the core, not literals.

## Naming Convention Shared by Every File of the `Q3` Family

Live scalars (never used as temporaries by a loop): `"n" "m" "W" "qm" "bb" "bt" "w1" "N" "cinf"
"jj" "pt" "pj" "qj" "dj" "wj" "rf" "dl" "pwd" "pwq" "ex"`.
Temporary pool for loops: `"i" "u1" "u2" "u3" "u4" "u5" "u6"`.
Arrays: `"PS" "QS" "DS" "WS"` (length `n`, the sorted job data, entries `pv J k`, `qv J k`, `dv J k`,
`wv J k`), `"T" "S"` (length `N = bt·w1`), `"G"` (length `bt`, digit sums).
-/

namespace Lax496464Proofs.Ram.Q3Defs

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep Lax496464.Profile
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-! ## The flat table and its digits -/

/-- The cell `(x, c)` of a flat table with `w1` weights per profile. -/
def cell (w1 : ℕ) (T : List ℕ) (x c : ℕ) : ℕ := T.getD (x * w1 + c) 0

/-- Digit `i` of `x` in base `bb`. -/
def dig (bb x i : ℕ) : ℕ := x / bb ^ i % bb

/-- The digit sum of `x` over the first `qm` digits. -/
def digsum (bb qm x : ℕ) : ℕ := ∑ i ∈ Finset.range qm, dig bb x i

/-! ## What a table means -/

/-- The flat array `T` *is* the relation `R`: for every profile `x < bt` and weight `c < w1`
the cell is at most `INF` and, for every budget `P < INF`, `cell ≤ P` iff `R x c P`. -/
def TabSem (bt w1 INF : ℕ) (R : ℕ → ℕ → ℕ → Prop) (T : List ℕ) : Prop :=
  ∀ x < bt, ∀ c < w1, cell w1 T x c ≤ INF ∧ ∀ P < INF, (cell w1 T x c ≤ P ↔ R x c P)

/-- The relation of the initial table: only the empty selection, profile `0`, weight `0`. -/
def R0 : ℕ → ℕ → ℕ → Prop := fun x c _ => x = 0 ∧ c = 0

/-- **Pass 1** (marginalisation): `S` is, cell by cell, the minimum of the cells of `T` whose
profile divides down to the same `b`. -/
def MargOK (bt w1 pwd INF : ℕ) (T S : List ℕ) : Prop :=
  ∀ b < bt, ∀ c < w1, cell w1 S b c ≤ INF ∧
    ∀ P, (cell w1 S b c ≤ P ↔ INF ≤ P ∨ ∃ y < bt, y / pwd = b ∧ cell w1 T y c ≤ P)

/-- **Pass 2** (take job `k`): `T'` is `S` improved by taking the job. -/
def TakeOK (bt w1 bb m INF pwq pj qj dj wj : ℕ) (G S T' : List ℕ) : Prop :=
  ∀ x < bt, ∀ c < w1, cell w1 T' x c ≤ INF ∧ ∀ P,
    (cell w1 T' x c ≤ P ↔ cell w1 S x c ≤ P ∨
      (1 ≤ x / pwq % bb ∧ G.getD x 0 ≤ m ∧
        cell w1 S (x - pwq) (c - wj) + pj + qj ≤ dj ∧ cell w1 S (x - pwq) (c - wj) + pj ≤ P))

/-- The step relation of the sweep: what `R` becomes after job `k`, with `pwd = bb^δ'` and
`pwq = bb^(q_k - 1)`. -/
def Step (bt bb m qm pwd pwq pj qj dj wj : ℕ) (R : ℕ → ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop :=
  fun x c P =>
    (∃ y < bt, y / pwd = x ∧ R y c P) ∨
    (1 ≤ x / pwq % bb ∧ digsum bb qm x ≤ m ∧
      ∃ y < bt, y / pwd = x - pwq ∧ ∃ P'', R y (c - wj) P'' ∧ P'' + pj + qj ≤ dj ∧ P'' + pj ≤ P)

/-! ## The semantics of the sweep, on an instance -/

/-- The reference time of stage `k`: `0` for `k = 0`, else `d_{k-1} - q_{k-1}` (natural
subtraction, so `max 0 s_{k-1}`). -/
def trefN (I : Instance) (k : ℕ) : ℕ := if k = 0 then 0 else dv I (k - 1) - qv I (k - 1)

/-- **The table relation at stage `k`**: some feasible set of jobs among the first `k` has weight
at least `c`, load at most `P`, and its due-date profile at the reference time `trefN k` has the
digits of `x` (coordinate `i+1`, i.e. the jobs due at `trefN k + i + 1`, is digit `i`). -/
def Rsem (I : Instance) (bb qm k : ℕ) : ℕ → ℕ → ℕ → Prop := fun x c P =>
  ∃ Z : Finset I.Job, (∀ i ∈ Z, (i : ℕ) < k) ∧ Feasible I Z ∧ c ≤ weight I Z ∧
    pload I Z ≤ (P : ℤ) ∧
    ∀ i < qm, dueProfile I Z (trefN I k : ℤ) (i + 1) = dig bb x i

end Lax496464Proofs.Ram.Q3Defs
