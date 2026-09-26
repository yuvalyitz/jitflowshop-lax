import Lax496464Proofs.Model.Defs
import Lax496464Proofs.Model.Packing
import Mathlib.Data.Fintype.EquivFin

namespace Lax496464Proofs

/-!
# Section 2: what a feasible set is

The paper's Section 2 replaces the shop — two stages, one preprocessing machine, `m`
parallel processing machines, non-preemption — by two independent conditions on the set
`Z` of jobs to be completed just in time:

> It follows from the above analysis that if subset of jobs `Z ⊆ J` satisfy Conditions 1
> and 2 below, then there exists a feasible schedule for `J` where `Z` is precisely the
> subset of jobs that complete just-in-time. Moreover, the converse is also true.

`feasible_iff` is that sentence. Everything downstream — the dynamic programs of
Sections 3–5, the greedy algorithm of Section 6, the ILP of Section 6.2, and the gadget
analysis of Section 8 — reasons about `Preprocessable` and `MSchedulable` and never again
about `JITSchedule`, exactly as the paper does.

## The two halves

*Necessity* is `FlexFlowJIT.sum_len_le`: in any schedule, the first operations of the jobs
whose second operations start no later than `s j` are pairwise non-overlapping intervals
inside `[0, s j]`, so their lengths sum to at most `s j`. That is Condition 1; Condition 2
is the machine assignment, read off the schedule.

*Sufficiency* is the paper's **Observation 1**, made concrete: preprocess the jobs of `Z`
back to back from time `0` in Early Start Time order (`Before` below — nondecreasing `s`,
ties broken arbitrarily but consistently). Condition 1 says exactly that this puts each
job's preprocessing entirely before its own `s`, and back-to-back operations never
overlap. `exists_est_schedule_of` produces that schedule together with the EST property
itself, so Observation 1 is not merely used but stated.

The tie-break is the only place a choice is made, and it is where this development is
more careful than the paper: with two jobs at the same `s`, the paper's prefix-sum
reading of Condition 1 charges only one of them, while a schedule must fit both. `Defs`'s
`Preprocessable` therefore sums over `{i ∈ Z : s i ≤ s j}`, ties included, and the theorem
below is what certifies that this is the right condition rather than a guess.
-/


namespace FFJ

variable (I : FFJ)

/-! ## 1. The EST tie-break order -/

/-- Early Start Time order with a fixed tie-break: `i` comes before `j` when `s i < s j`,
or when the two are equal and `idx i < idx j`. Any injective `idx` will do; the proof
below takes one from `Fintype.equivFin`. -/
private def Before (idx : I.Job → ℕ) (i j : I.Job) : Prop :=
  I.s i < I.s j ∨ (I.s i = I.s j ∧ idx i < idx j)

private instance instDecidableBefore (idx : I.Job → ℕ) (i j : I.Job) :
    Decidable (I.Before idx i j) :=
  inferInstanceAs (Decidable (I.s i < I.s j ∨ (I.s i = I.s j ∧ idx i < idx j)))

variable {I}

private lemma before_irrefl (idx : I.Job → ℕ) (i : I.Job) : ¬ I.Before idx i i := by
  unfold Before; omega

private lemma before_s_le {idx : I.Job → ℕ} {i j : I.Job} (h : I.Before idx i j) :
    I.s i ≤ I.s j := by
  unfold Before at h; omega

private lemma before_trans {idx : I.Job → ℕ} {i j k : I.Job}
    (h₁ : I.Before idx i j) (h₂ : I.Before idx j k) : I.Before idx i k := by
  unfold Before at *; omega

private lemma before_total {idx : I.Job → ℕ} (hidx : Function.Injective idx) {i j : I.Job}
    (hne : i ≠ j) : I.Before idx i j ∨ I.Before idx j i := by
  have h : idx i ≠ idx j := fun h => hne (hidx h)
  unfold Before; omega

/-! ## 2. The EST schedule

`estPre idx Z j` is the time at which job `j`'s preprocessing starts when the jobs of `Z`
are preprocessed back to back from time `0` in the order `Before idx`: the total
preprocessing time of everything strictly ahead of `j`. -/

/-- The start time the EST schedule gives job `j`'s first operation. -/
private def estPre (I : FFJ) (idx : I.Job → ℕ) (Z : Finset I.Job) (j : I.Job) : ℤ :=
  ∑ i ∈ Z.filter (fun i => I.Before idx i j), (I.p i : ℤ)

private lemma estPre_nonneg (I : FFJ) (idx : I.Job → ℕ) (Z : Finset I.Job) (j : I.Job) :
    0 ≤ estPre I idx Z j :=
  Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

/-- The one estimate the construction needs: everything ahead of `i`, plus `i` itself,
fits inside any set containing both. -/
private lemma estPre_add_le {I : FFJ} {idx : I.Job → ℕ} {Z : Finset I.Job} {i : I.Job}
    {S : Finset I.Job} (hsub : Z.filter (fun k => I.Before idx k i) ⊆ S) (hiS : i ∈ S) :
    estPre I idx Z i + I.p i ≤ ∑ k ∈ S, (I.p k : ℤ) := by
  have hinot : i ∉ Z.filter (fun k => I.Before idx k i) := by
    simp only [Finset.mem_filter, not_and]
    exact fun _ => before_irrefl idx i
  have hins : insert i (Z.filter (fun k => I.Before idx k i)) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hiS
    · exact hsub hx
  calc estPre I idx Z i + I.p i
      = ∑ k ∈ insert i (Z.filter (fun k => I.Before idx k i)), (I.p k : ℤ) := by
        rw [Finset.sum_insert hinot, estPre]; ring
    _ ≤ ∑ k ∈ S, (I.p k : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hins fun k _ _ => Int.natCast_nonneg _

/-- Back-to-back operations never overlap: an earlier job finishes before a later one
starts. -/
private lemma estPre_step {I : FFJ} {idx : I.Job → ℕ} {Z : Finset I.Job} {i : I.Job}
    (hi : i ∈ Z) {j : I.Job} (hij : I.Before idx i j) :
    estPre I idx Z i + I.p i ≤ estPre I idx Z j :=
  estPre_add_le
    (fun _ hk => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
      before_trans (Finset.mem_filter.mp hk).2 hij⟩)
    (Finset.mem_filter.mpr ⟨hi, hij⟩)

/-- Condition 1 is exactly what makes the EST schedule finish each job's preprocessing by
that job's own start time. -/
private lemma estPre_le_s {I : FFJ} {idx : I.Job → ℕ} {Z : Finset I.Job}
    (hpre : I.Preprocessable Z) {j : I.Job} (hj : j ∈ Z) :
    estPre I idx Z j + I.p j ≤ I.s j :=
  le_trans
    (estPre_add_le (S := Z.filter (fun i => I.s i ≤ I.s j))
      (fun _ hk => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
        before_s_le (Finset.mem_filter.mp hk).2⟩)
      (Finset.mem_filter.mpr ⟨hj, le_rfl⟩))
    (hpre j hj)

variable (I)

/-- **Observation 1, constructively.** A set satisfying the paper's two conditions admits
a just-in-time schedule, and one whose first stage runs in Early Start Time order.

The schedule preprocesses the jobs of `Z` back to back from time `0`, in nondecreasing
order of `s`: the start time of `j` is the total preprocessing time of everything ahead
of it. Condition 1 is exactly what makes that finish by `s j`; Condition 2 supplies the
machine assignment unchanged. -/
theorem exists_est_schedule_of (Z : Finset I.Job) (hpre : I.Preprocessable Z)
    (hm : I.MSchedulable Z) :
    ∃ σ : I.JITSchedule Z,
      ∀ i ∈ Z, ∀ j ∈ Z, I.s i < I.s j → σ.pre i + I.p i ≤ σ.pre j := by
  obtain ⟨c, hlt, hindep⟩ := hm
  obtain ⟨idx, hidx⟩ : ∃ idx : I.Job → ℕ, Function.Injective idx :=
    ⟨fun j => ((Fintype.equivFin I.Job) j).val,
      fun _ _ h => (Fintype.equivFin I.Job).injective (Fin.val_injective h)⟩
  refine ⟨⟨estPre I idx Z, c, fun j _ => estPre_nonneg I idx Z j,
    fun j hj => estPre_le_s hpre hj, fun i hi j hj hne => ?_, hlt, hindep⟩,
    fun i hi j _ hs => estPre_step hi (Or.inl hs)⟩
  rcases before_total hidx hne with h | h
  · exact Or.inl (estPre_step hi h)
  · exact Or.inr (estPre_step hj h)

/-! ## 3. The characterization -/

/-- **Section 2's reduction of the shop to two conditions.** A set of jobs can all be
completed just in time exactly when it can be preprocessed in time (Condition 1) and can
be scheduled on the `m` second-stage machines (Condition 2).

Necessity of Condition 1 is `FlexFlowJIT.sum_len_le`; sufficiency of the pair is
`exists_est_schedule_of`. Condition 2 is read off, and written back into, the machine
assignment directly. -/
theorem feasible_iff (Z : Finset I.Job) :
    I.Feasible Z ↔ I.Preprocessable Z ∧ I.MSchedulable Z := by
  constructor
  · rintro ⟨σ⟩
    refine ⟨fun j hj => ?_, ⟨σ.mach, σ.mach_lt, σ.mach_indep⟩⟩
    have h0 := σ.pre_nonneg j hj
    have h1 := σ.pre_le_s j hj
    have h2 : (0:ℤ) ≤ I.p j := Int.natCast_nonneg _
    refine FlexFlowJIT.sum_len_le _ σ.pre (fun i => (I.p i : ℤ)) (I.s j) (by omega)
      (fun i _ => Int.natCast_nonneg _)
      (fun i hi => σ.pre_nonneg i (Finset.mem_filter.mp hi).1)
      (fun i hi => le_trans (σ.pre_le_s i (Finset.mem_filter.mp hi).1)
        (Finset.mem_filter.mp hi).2)
      (fun i hi j' hj' => σ.pre_disjoint i (Finset.mem_filter.mp hi).1 j'
        (Finset.mem_filter.mp hj').1)
  · rintro ⟨hpre, hm⟩
    exact ⟨(exists_est_schedule_of I Z hpre hm).choose⟩

/-- **Observation 1.** Every feasible set admits a feasible schedule that preprocesses in
Early Start Time order — so restricting attention to EST schedules loses nothing. -/
theorem exists_est_schedule (Z : Finset I.Job) (h : I.Feasible Z) :
    ∃ σ : I.JITSchedule Z,
      ∀ i ∈ Z, ∀ j ∈ Z, I.s i < I.s j → σ.pre i + I.p i ≤ σ.pre j :=
  let ⟨hpre, hm⟩ := (I.feasible_iff Z).mp h
  exists_est_schedule_of I Z hpre hm

/-! ## 4. Condition 2 as a partition

The paper states Condition 2 as a partition of `Z` into `m` independent subsets
`Z₁ ∪ ⋯ ∪ Z_m` (allowing empty classes). `MSchedulable` states it as a colouring, which
is the same data; this is the translation. -/

end FFJ

end Lax496464Proofs
