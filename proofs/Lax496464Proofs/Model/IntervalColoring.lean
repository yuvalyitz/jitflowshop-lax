import Lax496464Proofs.Model.Defs
import Lax496464Proofs.Model.Section2
import Mathlib.Data.Finset.Max

namespace Lax496464Proofs

/-!
# Condition 2 is a depth condition

The paper never states this, but uses it everywhere: a set of jobs fits on `m` machines
exactly when no *instant* is covered by more than `m` of their second operations. It is
what makes Condition 2 checkable at all — the paper discharges it by citing
*"the algorithm of Carlisle and Lloyd (1995)"* — and it is what Section 6.1's second stopping
rule (*"there are `j₁, …, j_m ∈ Z_{j-1}` with `s_{j_i} ≤ s_j < d_{j_i}`"*) and Section 6.2's ILP
constraint (7) (*"the number of jobs `i ∈ J` with `s_i ≤ s_j < d_i` selected is at most `m`"*)
are both instances of.

Mathematically it is the perfectness of interval graphs, in the only form used here: the
minimum number of machines equals the maximum number of jobs alive at one time. The
`≤` direction is trivial — jobs alive together pairwise conflict, so they get distinct
machines. The `≥` direction is the greedy argument: process the jobs in order of start
time, and when the last one starts, every already-placed job that conflicts with it is
still running *at that instant*, so at most `m − 1` machines are busy and one is free.
`FairRIS/Proofs-FairRIS/IntervalColoring.lean` proves the same fact for that paper's
daily conflict graphs, by the same "take the job that starts last" argument.

## The one side condition

`m_schedulable_iff_card_running_le` assumes `0 < q j` for the jobs involved. A job with
`q j = 0` occupies the empty interval `[d j, d j)`: it conflicts with nothing, so it is
invisible to the depth condition — yet it still needs a machine to sit on, and when
`m = 0` there is none. That single degenerate case is the whole content of the
hypothesis, and every instance the paper builds has positive processing times.
-/


namespace FFJ

variable (I : FFJ)

/-! ## 1. Which jobs are running when -/

/-- The jobs of `Z` whose second operation is running at time `t`, i.e. those with
`t ∈ [s i, d i)`. -/
def running (Z : Finset I.Job) (t : ℤ) : Finset I.Job :=
  Z.filter (fun i => I.s i ≤ t ∧ t < (I.d i : ℤ))

variable {I}

lemma mem_running {Z : Finset I.Job} {t : ℤ} {i : I.Job} :
    i ∈ I.running Z t ↔ i ∈ Z ∧ I.s i ≤ t ∧ t < (I.d i : ℤ) := Finset.mem_filter

/-- Two distinct jobs alive at the same instant conflict. -/
lemma conflict_of_mem_running {Z : Finset I.Job} {t : ℤ} {i j : I.Job}
    (hi : i ∈ I.running Z t) (hj : j ∈ I.running Z t) : I.Conflict i j := by
  obtain ⟨-, hi1, hi2⟩ := mem_running.mp hi
  obtain ⟨-, hj1, hj2⟩ := mem_running.mp hj
  exact ⟨by omega, by omega⟩

/-- A job that conflicts with one starting no earlier is alive when that one starts. -/
lemma mem_running_s {Z : Finset I.Job} {i j : I.Job} (hi : i ∈ Z)
    (hle : I.s i ≤ I.s j) (hc : I.Conflict i j) : i ∈ I.running Z (I.s j) :=
  mem_running.mpr ⟨hi, hle, hc.2⟩

/-- A job with a nonzero processing time is alive when it starts. -/
lemma self_mem_running {Z : Finset I.Job} {j : I.Job} (hj : j ∈ Z) (hq : 0 < I.q j) :
    j ∈ I.running Z (I.s j) := by
  refine mem_running.mpr ⟨hj, le_rfl, ?_⟩
  simp only [FFJ.s]
  omega

lemma running_subset {Z Z' : Finset I.Job} (h : Z' ⊆ Z) (t : ℤ) :
    I.running Z' t ⊆ I.running Z t := Finset.filter_subset_filter _ h

/-! ## 2. The characterization -/

/-- The easy direction: distinct jobs alive together occupy distinct machines, and there
are only `m` of those. -/
theorem card_running_le_of_mSchedulable {Z : Finset I.Job} (h : I.MSchedulable Z)
    (t : ℤ) : (I.running Z t).card ≤ I.numMachines := by
  classical
  obtain ⟨c, hlt, hindep⟩ := h
  rw [show I.numMachines = (Finset.range I.numMachines).card from (Finset.card_range _).symm]
  refine Finset.card_le_card_of_injOn c
    (fun i hi => Finset.mem_range.mpr (hlt i (mem_running.mp hi).1)) ?_
  intro i hi j hj heq
  simp only [Finset.mem_coe] at hi hj
  by_contra hne
  exact hindep i (mem_running.mp hi).1 j (mem_running.mp hj).1 hne heq
    (conflict_of_mem_running hi hj)

/-- The greedy argument, as an induction on the number of jobs. -/
private theorem mSchedulable_of_card_running (I : FFJ) :
    ∀ (n : ℕ) (Z : Finset I.Job), Z.card ≤ n → (∀ j ∈ Z, 0 < I.q j) →
      (∀ t : ℤ, (I.running Z t).card ≤ I.numMachines) → I.MSchedulable Z := by
  classical
  intro n
  induction n with
  | zero =>
      intro Z hcard _ _
      have : Z = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst this
      exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
      intro Z hcard hq hdepth
      rcases Z.eq_empty_or_nonempty with rfl | hne
      · exact ⟨fun _ => 0, by simp, by simp⟩
      -- The job that starts last.
      obtain ⟨j, hjZ, hmax⟩ := Z.exists_max_image I.s hne
      have hcard' : (Z.erase j).card ≤ n := by
        have h := Finset.card_erase_of_mem hjZ
        have : 1 ≤ Z.card := Finset.card_pos.mpr hne
        omega
      obtain ⟨c, hlt, hindep⟩ := ih (Z.erase j) hcard'
        (fun i hi => hq i (Finset.mem_of_mem_erase hi))
        (fun t => le_trans (Finset.card_le_card (running_subset (Finset.erase_subset _ _) t))
          (hdepth t))
      -- Everything already placed that conflicts with `j` is alive when `j` starts.
      set N : Finset I.Job := (Z.erase j).filter (fun i => I.Conflict i j) with hN
      have hNsub : insert j N ⊆ I.running Z (I.s j) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact self_mem_running hjZ (hq x hjZ)
        · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
          exact mem_running_s (Finset.mem_of_mem_erase hx1)
            (hmax x (Finset.mem_of_mem_erase hx1)) hx2
      have hjN : j ∉ N := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
      have hNcard : N.card + 1 ≤ I.numMachines := by
        have h1 : (insert j N).card = N.card + 1 := Finset.card_insert_of_notMem hjN
        have h2 := Finset.card_le_card hNsub
        have h3 := hdepth (I.s j)
        omega
      -- so some machine is free for `j`.
      obtain ⟨a, ha, hanot⟩ : ∃ a, a ∈ Finset.range I.numMachines ∧ a ∉ N.image c := by
        refine Finset.exists_mem_notMem_of_card_lt_card ?_
        have := Finset.card_image_le (s := N) (f := c)
        simp only [Finset.card_range]
        omega
      refine ⟨fun x => if x = j then a else c x, fun x hx => ?_, fun x hx y hy hxy heq => ?_⟩
      · by_cases h : x = j
        · simpa [h] using Finset.mem_range.mp ha
        · simpa [h] using hlt x (Finset.mem_erase.mpr ⟨h, hx⟩)
      · -- No conflicting pair shares a machine: the old ones by induction, `j` by choice.
        have hkey : ∀ u ∈ Z, u ≠ j → c u = a → ¬ I.Conflict u j := by
          intro u hu hne' hcu hconf
          exact hanot (Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne', hu⟩, hconf⟩, hcu⟩)
        by_cases hxj : x = j
        · subst hxj
          have hyj : y ≠ x := fun h => hxy h.symm
          simp only [if_neg hyj] at heq
          exact fun hconf => hkey y hy hyj heq.symm (I.conflict_symm hconf)
        · by_cases hyj : y = j
          · subst hyj
            simp only [if_neg hxj] at heq
            exact hkey x hx hxj heq
          · simp only [if_neg hxj, if_neg hyj] at heq
            exact hindep x (Finset.mem_erase.mpr ⟨hxj, hx⟩) y
              (Finset.mem_erase.mpr ⟨hyj, hy⟩) hxy heq

/-- **Condition 2 is a depth condition.** A set of jobs can be scheduled on the `m`
second-stage machines exactly when at most `m` of them are running at any one instant.

This is the perfectness of interval graphs, in the form the paper's algorithms use it;
see the module doc for the role of `hq`. -/
theorem mSchedulable_iff_card_running_le {Z : Finset I.Job} (hq : ∀ j ∈ Z, 0 < I.q j) :
    I.MSchedulable Z ↔ ∀ t : ℤ, (I.running Z t).card ≤ I.numMachines :=
  ⟨fun h => card_running_le_of_mSchedulable h,
   fun h => mSchedulable_of_card_running I Z.card Z le_rfl hq h⟩

/-- The form Section 6.1's stopping rule and Section 6.2's constraint (7) use: it is
enough to count, at each job's own start time, how many selected jobs are running. -/
theorem mSchedulable_iff_card_running_start_le {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    I.MSchedulable Z ↔ ∀ j ∈ Z, (I.running Z (I.s j)).card ≤ I.numMachines := by
  refine ⟨fun h j _ => card_running_le_of_mSchedulable h _, fun h => ?_⟩
  rw [mSchedulable_iff_card_running_le hq]
  intro t
  rcases (I.running Z t).eq_empty_or_nonempty with he | hne
  · simp [he]
  · -- at any busy instant, the job alive there that started last sees the same set
    obtain ⟨j, hj, hmax⟩ := (I.running Z t).exists_max_image I.s hne
    refine le_trans (Finset.card_le_card ?_) (h j (mem_running.mp hj).1)
    intro x hx
    obtain ⟨hxZ, hx1, hx2⟩ := mem_running.mp hx
    have hjt := mem_running.mp hj
    exact mem_running.mpr ⟨hxZ, hmax x hx, by omega⟩

/-! ## 3. Observation 2, and the one-machine case

Section 2's **Observation 2** — *"Given `Z ⊆ J`, one can determine in `O(n log n)` time
whether there is a feasible schedule where exactly the jobs from `Z` are scheduled"* — has
two halves. The running time rests on Carlisle and Lloyd's algorithm, which this
development does not formalize. The *decidability* is the part with mathematical content,
and it is exactly what `feasible_iff` plus the depth characterization deliver: Condition 1
is a finite comparison of sums, and Condition 2 need only be tested at the start time of
each selected job. -/

/-- **Observation 2, its content.** Feasibility is equivalent to a pair of manifestly
decidable finite conditions. -/
theorem feasible_iff_conditions {Z : Finset I.Job} (hq : ∀ j ∈ Z, 0 < I.q j) :
    I.Feasible Z ↔
      (I.Preprocessable Z ∧ ∀ j ∈ Z, (I.running Z (I.s j)).card ≤ I.numMachines) := by
  rw [I.feasible_iff Z, mSchedulable_iff_card_running_start_le hq]

/-- **Observation 2.** Feasibility of a job set is decidable. -/
def decidableFeasible {Z : Finset I.Job} (hq : ∀ j ∈ Z, 0 < I.q j) :
    Decidable (I.Feasible Z) :=
  decidable_of_iff _ (feasible_iff_conditions hq).symm

end FFJ

end Lax496464Proofs
