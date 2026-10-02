import Lax496464.FlowShop

/-!
---
title: Uniform Preprocessing Times, and Proper Instances
type: definition
---
Two restrictions on an instance, both from Section 6 of the paper.

An instance has *uniform preprocessing times* when all $p_j$ are equal. It is *proper*
when no job's second-operation interval $[s_j, d_j)$ contains another's.

# Formalization Notes

Uniformity is stated as the existence of a common value rather than as a constant carried
by the instance, so that it is a property of an instance and not a different kind of
object.

Properness is stated as the impossibility of containment, with the degenerate case
excluded by the hypothesis that the two jobs are distinct: two jobs with the same
interval would otherwise make every instance improper. Containment is the wide reading —
$s_j \le s_i$ and $d_i \le d_j$, allowing either endpoint to coincide — which is the one
the paper's argument uses: on a proper instance the order by start time and the order by
due date agree, and that needs the non-strict form.
-/

namespace Lax496464.ProperInstances

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- All preprocessing times are equal. -/
def Uniform (I : Instance) : Prop := ∃ p : ℕ, ∀ j : I.Job, I.p j = p

/-- No job's second-operation interval contains another's. -/
def Proper (I : Instance) : Prop :=
  ∀ i j : I.Job, i ≠ j → ¬ (s j ≤ s i ∧ (I.d i : ℤ) ≤ (I.d j : ℤ))

end Lax496464.ProperInstances
