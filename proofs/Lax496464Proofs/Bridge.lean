import Lax496464Proofs.Model.IntervalColoring
import Lax496464.Feasibility

/-!
# The concepts' instances are the development's instances, numbered

The ported development of `Model/` takes the jobs of an instance to be an arbitrary finite
type, so that a gadget construction can name its jobs structurally. The concepts number
them, because an instance is something a machine is handed as a word and a word presents
its jobs in an order. `model I` is the development's instance belonging to the numbered
instance `I`, and this file carries the identification.

Everything except the schedule structure is definitionally the same on both sides — the
start times, the conflict relation, the two conditions of Section 2, the jobs running at
an instant, and the objective — so the bridge is a handful of `rfl`s. Only `JITSchedule`
is genuinely two structures with the same six fields, and `feasible_iff_model` converts
between them.
-/

namespace Lax496464Proofs.Bridge

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Conditions

/-- The development's instance belonging to a numbered instance. -/
def model (I : Instance) : FFJ where
  Job := Fin I.jobs
  jobFintype := inferInstance
  jobDecEq := inferInstance
  numMachines := I.machines
  p := I.p
  q := I.q
  d := I.d
  w := I.w

variable {I : Instance}

/-- A schedule of the concepts is a schedule of the development. -/
def toModel {Z : Finset I.Job} (σ : JITSchedule Z) : (model I).JITSchedule Z where
  pre := σ.pre
  mach := σ.mach
  pre_nonneg := σ.pre_nonneg
  pre_le_s := σ.pre_le_s
  pre_disjoint := σ.pre_disjoint
  mach_lt := σ.mach_lt
  mach_indep := σ.mach_indep

/-- And conversely. -/
def ofModel {Z : Finset I.Job} (σ : (model I).JITSchedule Z) : JITSchedule Z where
  pre := σ.pre
  mach := σ.mach
  pre_nonneg := σ.pre_nonneg
  pre_le_s := σ.pre_le_s
  pre_disjoint := σ.pre_disjoint
  mach_lt := σ.mach_lt
  mach_indep := σ.mach_indep

theorem feasible_iff_model (Z : Finset I.Job) : Feasible I Z ↔ (model I).Feasible Z :=
  ⟨fun ⟨σ⟩ => ⟨toModel σ⟩, fun ⟨σ⟩ => ⟨ofModel σ⟩⟩

theorem model_hasWeight (W : ℕ) : (model I).HasWeight W ↔ HasWeight I W := by
  unfold FFJ.HasWeight HasWeight
  exact exists_congr fun Z => and_congr_left fun _ => (feasible_iff_model Z).symm

end Lax496464Proofs.Bridge
