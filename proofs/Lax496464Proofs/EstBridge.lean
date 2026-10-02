import Lax496464Proofs.Bridge
import Lax496464Proofs.Model.Sorted
import Lax496464.Lemma1

/-!
# Instances in Earliest-Start-Time Order

Sections 3 to 6 all work with the jobs numbered in nondecreasing order of start time. The
development carries that hypothesis in the instance itself (`EstFFJ`); the concepts state
it as a predicate `EstOrdered` on an ordinary instance, since a word does not come sorted
and the sorting is part of what an algorithm is charged for. `estModel I h` is the sorted
instance belonging to `I` and a proof that `I` is sorted.

The two vocabularies agree definitionally except in one place: the sets `X₁` and `X₂` of
recursion (1) are built with `Finset.filter`, and the concepts use the classical decidability
instance where the development uses the one inferred for `Fin n`. The instances are equal
because `Decidable` is a subsingleton, which is all `j1_eq` and `j2_eq` say.
-/

namespace Lax496464Proofs.EstBridge

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.DynamicProgram Bridge FlexFlowJIT

/-- The sorted instance belonging to a numbered instance in earliest-start-time order. -/
def estModel (I : Instance) (h : EstOrdered I) : EstFFJ where
  n := I.jobs
  numMachines := I.machines
  p := I.p
  q := I.q
  d := I.d
  w := I.w
  est := h

variable {I : Instance} (h : EstOrdered I)

theorem firstM_eq : firstM I = (estModel I h).firstM := rfl

/-- Two decidability instances for the same predicate filter the same set. -/
private theorem filter_univ_congr {α : Type*} [Fintype α] (p : α → Prop)
    (i₁ i₂ : DecidablePred p) :
    @Finset.filter α p i₁ Finset.univ = @Finset.filter α p i₂ Finset.univ := by
  rw [Subsingleton.elim i₁ i₂]

theorem j1_eq (X : Finset I.Job) (j : I.Job) :
    j1 I X j = (estModel I h).j1 X j := by
  unfold j1 EstFFJ.j1
  rw [filter_univ_congr (fun x : I.Job => x ∉ X ∧ j < x)
    (Classical.decPred _) (fun x => inferInstance)]
  rfl

theorem j2_eq (X : Finset I.Job) (j : I.Job) :
    j2 I X j = (estModel I h).j2 X j := by
  unfold j2 EstFFJ.j2
  rw [filter_univ_congr (fun x : I.Job => x ∉ X ∧ (I.d j : ℤ) ≤ s x)
    (Classical.decPred _) (fun x => inferInstance)]
  rfl

theorem X1_eq (X : Finset I.Job) (j : I.Job) :
    X1 I X j = (estModel I h).X1 X j := by
  unfold X1 EstFFJ.X1
  rw [j1_eq h]
  cases (estModel I h).j1 X j <;> rfl

theorem X2_eq (X : Finset I.Job) (j : I.Job) :
    X2 I X j = (estModel I h).X2 X j := by
  unfold X2 EstFFJ.X2
  rw [j2_eq h]
  cases (estModel I h).j2 X j <;> rfl

end Lax496464Proofs.EstBridge
