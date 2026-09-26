import Lax496464Proofs.Model.Section2
import Mathlib.Data.Fintype.Powerset

namespace Lax496464Proofs

/-!
# The optimum of an instance

`Feasible` says which sets of jobs can all be completed just in time; the problem asks
for the heaviest such set. This file gives that number a name and the three facts every
later section uses: it is an upper bound, it is attained, and — because feasibility does
not mention the weights at all — it is the only thing the weights influence.

That last point is what Section 7's rounding scheme rests on: `FFJ.rescale` changes the
weights and nothing else, so an optimal solution of the rounded instance is a *feasible*
solution of the original one, and the only question left is how much weight it loses.
-/


namespace FFJ

open Classical in
/-- The optimum `∑ wⱼZⱼ` of an instance: the largest weight of a feasible set. -/
noncomputable def opt (I : FFJ) : ℕ :=
  ((Finset.univ : Finset (Finset I.Job)).filter (fun Z => I.Feasible Z)).sup I.weight

variable (I : FFJ)

theorem le_opt {Z : Finset I.Job} (h : I.Feasible Z) : I.weight Z ≤ I.opt := by
  classical
  exact Finset.le_sup (f := I.weight) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- The optimum is attained: some feasible set has exactly that weight. -/
theorem exists_feasible_weight_eq_opt : ∃ Z : Finset I.Job, I.Feasible Z ∧ I.weight Z = I.opt := by
  classical
  obtain ⟨Z, hZ, hsup⟩ :=
    Finset.exists_mem_eq_sup
      ((Finset.univ : Finset (Finset I.Job)).filter (fun Z => I.Feasible Z))
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, I.feasible_empty⟩⟩ I.weight
  exact ⟨Z, (Finset.mem_filter.mp hZ).2, hsup.symm⟩

/-- The decision version asks exactly whether the optimum clears the threshold. -/
theorem hasWeight_iff (W : ℕ) : I.HasWeight W ↔ W ≤ I.opt := by
  constructor
  · rintro ⟨Z, hZ, hW⟩
    exact le_trans hW (I.le_opt hZ)
  · intro h
    obtain ⟨Z, hZ, hw⟩ := I.exists_feasible_weight_eq_opt
    exact ⟨Z, hZ, by omega⟩

/-- `w_max`, the largest weight in the instance. -/
def wmax : ℕ := Finset.univ.sup I.w

/-- A single job is feasible on its own as soon as it can be preprocessed at all — the
paper's standing assumption *"`p_j ≤ s_j` for all jobs `j` (as jobs not fulfilling this
requirement can be discarded)"* (Section 7). -/
theorem feasible_singleton {j : I.Job} (hm : 0 < I.numMachines) (hp : (I.p j : ℤ) ≤ I.s j) :
    I.Feasible {j} := by
  classical
  refine (I.feasible_iff _).mpr ⟨fun i hi => ?_, ⟨fun _ => 0, fun _ _ => hm, ?_⟩⟩
  · rw [Finset.mem_singleton] at hi
    subst hi
    have : ({i} : Finset I.Job).filter (fun x => I.s x ≤ I.s i) = {i} := by
      simp
    rw [this, Finset.sum_singleton]
    exact hp
  · intro a ha b hb hne
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hne

/-- **The optimum is at least the largest single weight** — the inequality Section 7's
approximation ratio is measured against (`w(Z) ≥ w_max`). -/
theorem wmax_le_opt (hm : 0 < I.numMachines) (hp : ∀ j, (I.p j : ℤ) ≤ I.s j) :
    I.wmax ≤ I.opt := by
  refine Finset.sup_le fun j _ => ?_
  have := I.le_opt (I.feasible_singleton hm (hp j))
  simpa [weight] using this

end FFJ

end Lax496464Proofs
