import Lax496464.Conditions
import Lax496464.EstOrder

/-!
---
title: Every instance may be assumed to have distinct endpoints
type: theorem
---
On an instance in earliest-start-time order, the rescaling of Section 4 changes neither
which sets of jobs are feasible nor what they weigh, and it makes the $2n$ endpoints
pairwise distinct. So an algorithm may assume distinct endpoints, which is what the
sweeps of Sections 4 and 5 do when they step from one endpoint to the next and treat each
step as carrying a single event.

# Formalization notes

Three statements, because the rescaling has three things to deliver: it preserves the
feasible sets, it preserves their weights, and it separates the endpoints. The first is
the one with content — a conflict must be created by the rescaling neither where there
was none nor destroyed where there was one — and it is where the hypothesis of
earliest-start-time order is used.

The order is preserved as well, so the rescaled instance is again an admissible input for
every algorithm. That is stated too, since an assumption discharged by a transformation
is of no use if the transformation breaks another.

Positive processing times are assumed, and the rescaling needs them: with $q_j = 0$ the
window $[s_j, d_j)$ is empty, the scaled instance has $s_j = d_j$ for that job, and the
endpoints are not separated after all. The paper's algorithms carry the same assumption
wherever they count jobs alive at an instant.
-/

namespace Lax496464.Normalization

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder

/-- **Section 4.** The rescaling preserves feasibility. -/
axiom scale_feasible_iff (I : Instance) (h : EstOrdered I) (hq : ∀ i : I.Job, 0 < I.q i)
    (Z : Finset I.Job) :
    Feasible (scale I) Z ↔ Feasible I Z

/-- The rescaling preserves weights. -/
axiom scale_weight (I : Instance) (Z : Finset I.Job) :
    weight (scale I) Z = weight I Z

/-- The rescaling separates the endpoints, and keeps the jobs in earliest-start-time
order. -/
axiom scale_distinctEndpoints (I : Instance) (h : EstOrdered I) (hq : ∀ i : I.Job, 0 < I.q i) :
    DistinctEndpoints (scale I) ∧ EstOrdered (scale I)

end Lax496464.Normalization
