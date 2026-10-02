import Lax496464Proofs.Ram.DpCore
import Lax496464Proofs.Section3

/-!
# The Dynamic Program for `m` Machines, as a Function of the Threshold Set

`Dp1.lean` codes the single-machine table, where a threshold set is `∅` or one job, as a
function of a plain natural number `j`. With `m` machines a threshold set is an arbitrary
`Finset I.Job` of size at most `m`, and this file is the same recursion — `dpKm k X W'` codes,
in the sense of `DpCore.Rep`, the predicate "a set of weight `W'` compatible with `X` can be
preprocessed from `P'`" — stated directly over `Finset I.Job` rather than through a
single-threshold wrapper, since `j1`/`j2` already give what `Dp1`'s `IsNxt`/`nxt_gt` had to be
built around: both always exceed the threshold they replace, with no assumption on `X`'s shape.

The recursion terminates because the *smallest* threshold strictly increases at every step
(`X1_min_gt`, `X2_min_gt`), so "how far the smallest threshold still has to travel" —
`I.jobs - minOrN X`, with the convention `minOrN ∅ = I.jobs` — is fuel enough, exactly as
`Dp1.lean`'s `dpK` uses `J.jobs ≤ j + k` as its own decreasing budget.
-/

namespace Lax496464Proofs.Ram.DpM

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore
open Lax496464Proofs.Section3 (achievable_recursion)

variable {I : Instance}

/-- The smallest job index not (yet) ruled out — `I.jobs` when `X` is empty, the convention
that makes "how far the smallest threshold has to travel" a single natural number throughout. -/
def minOrN (X : Finset I.Job) : ℕ := if h : X.Nonempty then (X.min' h : ℕ) else I.jobs

/-- The table: `dpKm k X W'` is the code of the entry `T[X, W']`, correct whenever there is
fuel enough for `X`'s smallest threshold to reach the end, `I.jobs ≤ minOrN X + k`. -/
noncomputable def dpKm (I : Instance) (inf : ℕ) : ℕ → Finset I.Job → ℕ → ℕ
  | 0, _, W' => if W' = 0 then inf else 0
  | k + 1, X, W' =>
    if h : X.Nonempty then
      max (dpKm I inf k (X1 I X (X.min' h)) W')
        (if I.w (X.min' h) ≤ W' then
          stepF inf (dpKm I inf k (X2 I X (X.min' h)) (W' - I.w (X.min' h))) (s (X.min' h))
            (I.p (X.min' h))
        else 0)
    else if W' = 0 then inf else 0

end Lax496464Proofs.Ram.DpM
