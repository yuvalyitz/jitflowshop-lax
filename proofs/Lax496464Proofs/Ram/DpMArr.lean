import Lax496464Proofs.Ram.DpM
import Lax496464Proofs.Ram.Dp1

/-!
# The `m`-machine table, as a function of a plain list of thresholds

`Dp1.lean`'s "column form in natural numbers only" (`fNat`/`colStep`/`colAll`) works because with
one threshold, the paper's `j₁` is always the very next index — no gap to skip. With `m` thresholds
that is no longer true: `j₁`/`j₂` may have to jump past a whole run of the *other* thresholds. The
paper's own treatment of Theorem 2 takes `m` to be `O(1)`, so this file does not try to answer that
query for a whole row at once (`Ram/NextFree.lean`'s job, built for a design this file does not use
after all) — it instead pays `O(m)` per table entry, a single pass over the (at most `m`) other
thresholds, which `Dp1.lean`'s single-threshold table could not afford to pay per index but this one
can, `m` times over `n^m` entries still being `O(n^m)` for fixed `m`.

A threshold set is a plain `List ℕ`, sorted strictly ascending, one entry per threshold — no
sentinel for "removed": a threshold set of size `< m` is exactly a shorter list, matching
`DynamicProgram.X1`/`X2` dropping a threshold outright when `j₁`/`j₂` finds none. `dpArr k X W'` is
the same fuel-driven recursion as `DpM.dpKm`, with `j₁`/`j₂` computed by `j1Nat`/`j2Nat`'s single
fold over the list instead of a `Finset.min'` search, and correct exactly when `toFinset` carries `X`
to the `Finset` `dpKm` was proved correct for.
-/

namespace Lax496464Proofs.Ram.DpMArr

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore
open Lax496464Proofs.Ram.Dp1 (pv sv qv dv)

variable {I : Instance}

/-- The weight of job `j`; zero past the last job (never actually reached, by the same
convention as `Dp1.lean`'s `pv`/`sv`/`qv`/`dv`). -/
def wv (I : Instance) (j : ℕ) : ℕ := if h : j < I.jobs then I.w ⟨j, h⟩ else 0

/-- `j₁`, computed by a single left-to-right pass over the sorted list of the *other*
thresholds: `acc` starts at `v + 1` and advances past every one of them still exactly equal to
it, stopping at the first gap (or the end of the list). -/
def j1Nat (v : ℕ) (Y : List ℕ) : ℕ :=
  Y.foldl (fun acc y => if y = acc then acc + 1 else acc) (v + 1)

/-- `j₂`, the same single pass, started from an externally supplied `y₀` — the smallest job
index whose start time clears `v`'s due date, ignoring the other thresholds entirely (that
part of the query does not depend on `X` at all, so it is not this file's job to answer; a
caller supplies it, exactly as `Dp1.lean`'s `dpK`/`dpK_rep` take `nxt` as a parameter rather
than compute it). -/
def j2Nat (y0 : ℕ) (Y : List ℕ) : ℕ :=
  Y.foldl (fun acc y => if y = acc then acc + 1 else acc) y0

/-- Insert `v` into a sorted list, keeping it sorted. -/
def insertSorted (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | y :: ys => if v ≤ y then v :: y :: ys else y :: insertSorted v ys

/-- The thresholds after passing over `v` — `Y` with `j₁ v Y` inserted, or just `Y` if `j₁`
ran off the end of the instance (no replacement, matching `X1`'s `none` case). -/
def X1Nat (I : Instance) : List ℕ → List ℕ
  | [] => []
  | v :: Y => let y := j1Nat v Y; if y < I.jobs then insertSorted y Y else Y

/-- The thresholds after selecting `v`, given the precomputed `y₀ := nxt0 v`. -/
def X2Nat (I : Instance) (nxt0 : ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | v :: Y => let y := j2Nat (nxt0 v) Y; if y < I.jobs then insertSorted y Y else Y

/-- The table: `dpArr k X W'` is the code of the entry `T[X, W']`. Same fuel-driven recursion
as `DpM.dpKm`, over a list instead of a `Finset`. -/
def dpArr (I : Instance) (inf : ℕ) (nxt0 : ℕ → ℕ) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, W' => if W' = 0 then inf else 0
  | _ + 1, [], W' => if W' = 0 then inf else 0
  | k + 1, v :: Y, W' =>
    max (dpArr I inf nxt0 k (X1Nat I (v :: Y)) W')
      (if wv I v ≤ W' then
        stepF inf (dpArr I inf nxt0 k (X2Nat I nxt0 (v :: Y)) (W' - wv I v)) (sv I v) (pv I v)
      else 0)

end Lax496464Proofs.Ram.DpMArr
