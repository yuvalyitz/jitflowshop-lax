import Lax496464Proofs.EstBridge
import Lax496464.Theorem2

/-!
# Section 3: the Dynamic Program over Sets of Thresholds

The table `T[X, W']` of Section 3 is indexed by a set `X` of `m` *thresholds* — one per
second-stage machine, the earliest job that machine may still take — and a weight `W'`,
and stores the latest instant from which a set of that weight, fitting those thresholds,
can still be preprocessed. Recursion (1) decides, for the smallest threshold `j`, whether
`j` is selected.

`Model/Sorted.lean` carries the work. Its `CompatibleWith` is the paper's condition with
the machine enumeration removed — each job is assigned the *threshold* it runs behind
rather than a machine index — which is what makes the recursion's two branches statable
without renumbering machines; the equivalence with `MSchedulable` is
`mSchedulable_iff_exists_compatible` there, and the hard direction of the recursion is a
Hall's-theorem argument.
-/

namespace Lax496464Proofs.Section3

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.DynamicProgram Bridge EstBridge

/--
---
conclusion: Lax496464.Lemma1.achievable_recursion
---
Recursion (1), proved in `Model/Sorted.lean` as `EstFFJ.lemma1`. The branch in which `j` is
passed over needs `X₁` to admit every set the old thresholds admitted, and the branch in
which `j` is taken needs the converse; both are Hall's theorem applied to the map sending a
job to the threshold it runs behind.
-/
theorem achievable_recursion (I : Instance) (hest : EstOrdered I) (hq : ∀ j : I.Job, 0 < I.q j)
    {X : Finset I.Job} {j : I.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x)
    (W' : ℕ) (P' : ℤ) :
    Achievable I X W' P' ↔
      Achievable I (X1 I X j) W' P' ∨
        (I.w j ≤ W' ∧ P' + I.p j ≤ s j ∧
          Achievable I (X2 I X j) (W' - I.w j) (P' + I.p j)) := by
  rw [X1_eq hest, X2_eq hest]
  exact (estModel I hest).lemma1 hq hjX hjmin

/--
---
conclusion: Lax496464.Theorem2.achievable_readoff
---
The `m` smallest indices are thresholds that constrain nothing beyond `|X| ≤ m`, so a set
compatible with them is one that fits on `m` machines; and being preprocessable from a
nonnegative instant is Condition 1.
-/
theorem achievable_readoff (I : Instance) (hest : EstOrdered I) (W' : ℕ) :
    (∃ P' : ℤ, 0 ≤ P' ∧ Achievable I (firstM I) W' P') ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W' := by
  rw [firstM_eq hest]
  refine ((estModel I hest).theorem2_readoff W').trans (exists_congr fun Z => ?_)
  exact and_congr_left fun _ => (feasible_iff_model Z).symm

end Lax496464Proofs.Section3
