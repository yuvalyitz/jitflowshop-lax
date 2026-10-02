import Lax496464Proofs.Model.Defs

/-!
# Renaming the Jobs of an Instance

Section 8's construction names its jobs structurally — a selection job is a triple
(segment, set, element of that set) — while an instance handed to a machine numbers them
`0, …, n−1`. The two are the same shop under a bijection of job names, and this file says
what has to hold for such a bijection to preserve the answer: the four data of a job, and
the number of machines.

Nothing here is specific to Section 8; it is the general statement that the problem does
not depend on how the jobs are named.
-/

namespace Lax496464Proofs.Transport

open FFJ

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A renaming of the jobs of `I` as the jobs of `J`, preserving all the data. -/
structure Iso (I J : FFJ) where
  /-- The bijection between job names. -/
  e : I.Job ≃ J.Job
  /-- The two shops have the same number of second-stage machines. -/
  machines : J.numMachines = I.numMachines
  /-- Preprocessing times agree. -/
  pre : ∀ x, J.p (e x) = I.p x
  /-- Processing times agree. -/
  proc : ∀ x, J.q (e x) = I.q x
  /-- Due dates agree. -/
  due : ∀ x, J.d (e x) = I.d x
  /-- Weights agree. -/
  wt : ∀ x, J.w (e x) = I.w x

namespace Iso

variable {I J : FFJ} (h : Iso I J)

theorem s_eq (x : I.Job) : J.s (h.e x) = I.s x := by
  simp only [FFJ.s, h.due, h.proc]

theorem conflict_iff (x y : I.Job) : J.Conflict (h.e x) (h.e y) ↔ I.Conflict x y := by
  simp only [FFJ.Conflict, h.s_eq, h.due]

/-- The inverse renaming. -/
def symm : Iso J I where
  e := h.e.symm
  machines := h.machines.symm
  pre y := by rw [← h.pre (h.e.symm y), Equiv.apply_symm_apply]
  proc y := by rw [← h.proc (h.e.symm y), Equiv.apply_symm_apply]
  due y := by rw [← h.due (h.e.symm y), Equiv.apply_symm_apply]
  wt y := by rw [← h.wt (h.e.symm y), Equiv.apply_symm_apply]

theorem weight_image (Z : Finset I.Job) : J.weight (Z.image h.e) = I.weight Z := by
  classical
  rw [FFJ.weight, Finset.sum_image fun x _ y _ hxy => h.e.injective hxy]
  exact Finset.sum_congr rfl fun x _ => h.wt x

theorem feasible_image {Z : Finset I.Job} (hZ : I.Feasible Z) : J.Feasible (Z.image h.e) := by
  classical
  obtain ⟨σ⟩ := hZ
  have hmem : ∀ y ∈ Z.image h.e, h.e.symm y ∈ Z := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rwa [Equiv.symm_apply_apply]
  have hback : ∀ y : J.Job, h.e (h.e.symm y) = y := fun y => h.e.apply_symm_apply y
  refine ⟨{ pre := fun y => σ.pre (h.e.symm y)
            mach := fun y => σ.mach (h.e.symm y)
            pre_nonneg := fun y hy => σ.pre_nonneg _ (hmem y hy)
            pre_le_s := ?_
            pre_disjoint := ?_
            mach_lt := ?_
            mach_indep := ?_ }⟩
  · intro y hy
    have := σ.pre_le_s _ (hmem y hy)
    rwa [← h.pre (h.e.symm y), ← h.s_eq (h.e.symm y), hback] at this
  · intro y hy z hz hyz
    have hne : h.e.symm y ≠ h.e.symm z := fun hc => hyz (by
      rw [← hback y, ← hback z, hc])
    have := σ.pre_disjoint _ (hmem y hy) _ (hmem z hz) hne
    rwa [← h.pre (h.e.symm y), ← h.pre (h.e.symm z), hback, hback] at this
  · intro y hy
    rw [h.machines]
    exact σ.mach_lt _ (hmem y hy)
  · intro y hy z hz hyz hmm
    have hne : h.e.symm y ≠ h.e.symm z := fun hc => hyz (by
      rw [← hback y, ← hback z, hc])
    have := σ.mach_indep _ (hmem y hy) _ (hmem z hz) hne hmm
    rwa [← h.conflict_iff (h.e.symm y) (h.e.symm z), hback, hback] at this

/-- **Renaming the jobs does not change the answer.** -/
theorem hasWeight_iff (iso : Iso I J) (W : ℕ) : I.HasWeight W ↔ J.HasWeight W := by
  classical
  constructor
  · rintro ⟨Z, hZ, hW⟩
    exact ⟨Z.image iso.e, iso.feasible_image hZ, by rwa [iso.weight_image]⟩
  · rintro ⟨Z, hZ, hW⟩
    exact ⟨Z.image iso.symm.e, iso.symm.feasible_image hZ, by rwa [iso.symm.weight_image]⟩

end Iso

end Lax496464Proofs.Transport
