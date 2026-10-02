import Lax496464Proofs.Model.Sorted
import Lax496464Proofs.Model.Lemma2_Sweep
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Lax496464Proofs

/-!
# Section 4's Normalization: Making All Endpoints Distinct

Sections 4 and 5 open with a *without loss of generality*:

> we may assume that all endpoints of the second-operation intervals are distinct. If this
> is not the case, we can scale up the due-dates and processing times by setting
> `d'ⱼ = (n+1)·dⱼ + j`, `q'ⱼ = (n+1)·qⱼ` and `p'ⱼ = (n+1)·pⱼ` for each job `j`. In this way,
> we obtain an equivalent instance in which no pair of jobs have the same starting time or
> due date.

`scale` is that instance and this file proves the claim: the endpoints really are distinct
(`scale_st_injective`, `scale_d_injective`, `scale_st_ne_d`) and the two instances have the
same feasible sets and the same weights (`scale_feasible_iff`, `scale_wt`).

**The normalization depends on the standing EST assumption**, and not only for tidiness.
Offsetting job `i`'s whole interval by `i` moves both its endpoints together, so two
intervals that merely *touch* — `s_i = d_j`, no conflict — end up overlapping when `i < j`,
which would manufacture a conflict that the original instance does not have. Under the EST
order that cannot happen: `s_i = d_j > s_j` forces `s_j < s_i` and hence `j < i`. So the
scaling is sound exactly because the jobs are indexed in EST order, and
`scale_conflict_iff` is where that is used.

A second thing worth noting: Condition 1 transfers through
`Sorted.lean`'s `preprocessable_iff_from_zero`. Scaling makes the start times *strictly*
increasing, so the scaled instance's Condition 1 sums over an index prefix, while the
original's sums over the tie-inclusive set. Those are the two readings that lemma reconciles.
-/

namespace FlexFlowJIT

namespace EstFFJ

variable {E : EstFFJ}

/-! ## 1. Arithmetic of the offset -/

/-- Comparing `N·A + a` and `N·B + b` when the offsets are smaller than `N`: the scale
decides unless it ties, and then the offset does. -/
private lemma scaled_le_iff {N A B a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haN : a < N) (hbN : b < N) :
    N * A + a ≤ N * B + b ↔ (A < B ∨ (A = B ∧ a ≤ b)) := by
  have hN : 0 < N := lt_of_le_of_lt ha haN
  constructor
  · intro h
    rcases lt_trichotomy A B with hAB | rfl | hAB
    · exact Or.inl hAB
    · exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h2 : N * (B + 1) ≤ N * A :=
        Int.mul_le_mul_of_nonneg_left (by omega) (le_of_lt hN)
      have h3 : N * (B + 1) = N * B + N := by ring
      omega
  · rintro (hAB | ⟨rfl, hab⟩)
    · have h2 : N * (A + 1) ≤ N * B :=
        Int.mul_le_mul_of_nonneg_left (by omega) (le_of_lt hN)
      have h3 : N * (A + 1) = N * A + N := by ring
      omega
    · omega

private lemma scaled_lt_iff {N A B a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haN : a < N) (hbN : b < N) :
    N * A + a < N * B + b ↔ (A < B ∨ (A = B ∧ a < b)) := by
  have hN : 0 < N := lt_of_le_of_lt ha haN
  constructor
  · intro h
    rcases lt_trichotomy A B with hAB | rfl | hAB
    · exact Or.inl hAB
    · exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h2 : N * (B + 1) ≤ N * A :=
        Int.mul_le_mul_of_nonneg_left (by omega) (le_of_lt hN)
      have h3 : N * (B + 1) = N * B + N := by ring
      omega
  · rintro (hAB | ⟨rfl, hab⟩)
    · have h2 : N * (A + 1) ≤ N * B :=
        Int.mul_le_mul_of_nonneg_left (by omega) (le_of_lt hN)
      have h3 : N * (A + 1) = N * A + N := by ring
      omega
    · omega

/-- Two scaled-and-offset values agree only if both parts do. -/
private lemma scaled_inj {N A B a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haN : a < N) (hbN : b < N) (h : N * A + a = N * B + b) : A = B ∧ a = b := by
  have h1 := (scaled_le_iff ha hb haN hbN).mp (le_of_eq h)
  have h2 := (scaled_le_iff hb ha hbN haN).mp (le_of_eq h.symm)
  have hAB : A = B := by
    rcases h1 with h1 | ⟨h1, -⟩ <;> rcases h2 with h2 | ⟨h2, -⟩ <;> omega
  subst hAB
  exact ⟨rfl, by omega⟩

/-! ## 2. The scaled instance -/

variable (E) in
/-- **Section 4's normalization.** Every time is multiplied by `n + 1` and job `i`'s whole
second-operation interval is then shifted by `i`, which separates endpoints that coincided
without disturbing their order. -/
def scale : EstFFJ where
  n := E.n
  numMachines := E.numMachines
  p := fun i => (E.n + 1) * E.p i
  q := fun i => (E.n + 1) * E.q i
  d := fun i => (E.n + 1) * E.d i + (i : ℕ)
  w := E.w
  est := by
    intro i j hij
    have h := E.est i j hij
    have hij' : (i : ℕ) ≤ (j : ℕ) := hij
    have h2 := Int.mul_le_mul_of_nonneg_left h
      (show (0 : ℤ) ≤ (E.n : ℤ) + 1 by omega)
    have e1 : ((E.n : ℤ) + 1) * ((E.d i : ℤ) - E.q i)
        = ((E.n : ℤ) + 1) * (E.d i : ℤ) - ((E.n : ℤ) + 1) * (E.q i : ℤ) := by ring
    have e2 : ((E.n : ℤ) + 1) * ((E.d j : ℤ) - E.q j)
        = ((E.n : ℤ) + 1) * (E.d j : ℤ) - ((E.n : ℤ) + 1) * (E.q j : ℤ) := by ring
    push_cast
    omega

lemma scale_d (i : Fin E.n) :
    (E.scale.d i : ℤ) = ((E.n : ℤ) + 1) * (E.d i : ℤ) + (i : ℕ) := by
  simp only [scale]
  push_cast
  ring

lemma scale_st (i : Fin E.n) : E.scale.st i = ((E.n : ℤ) + 1) * E.st i + (i : ℕ) := by
  simp only [scale, st]
  push_cast
  ring

/-! ## 3. The order is unchanged, and now strict -/

/-- **Start times now order exactly as the indices do.** In particular they are distinct. -/
lemma scale_st_le_iff {i j : Fin E.n} : E.scale.st i ≤ E.scale.st j ↔ i ≤ j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [scale_st, scale_st, scaled_le_iff (by omega) (by omega) (by omega) (by omega)]
  constructor
  · rintro (h | ⟨-, h⟩)
    · by_contra hc
      exact absurd (E.st_mono (le_of_lt (not_le.mp hc))) (not_le.mpr h)
    · exact Fin.le_def.mpr (by exact_mod_cast h)
  · intro h
    rcases lt_or_eq_of_le (E.st_mono h) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by exact_mod_cast Fin.le_def.mp h⟩

lemma scale_st_injective {i j : Fin E.n} (h : E.scale.st i = E.scale.st j) : i = j :=
  le_antisymm (scale_st_le_iff.mp (le_of_eq h)) (scale_st_le_iff.mp (le_of_eq h.symm))

lemma scale_d_injective {i j : Fin E.n} (h : E.scale.d i = E.scale.d j) : i = j := by
  have hi := i.isLt
  have hj := j.isLt
  have h' : ((E.n : ℤ) + 1) * (E.d i : ℤ) + ((i : ℕ) : ℤ)
      = ((E.n : ℤ) + 1) * (E.d j : ℤ) + ((j : ℕ) : ℤ) := by
    rw [← scale_d, ← scale_d, h]
  have h2 := (scaled_inj (by omega) (by omega) (by omega) (by omega) h').2
  exact Fin.ext (by omega)

/-- **No start time coincides with a due date**, since every job has positive second-stage
time. -/
lemma scale_st_ne_d (hq : ∀ i, 0 < E.q i) (i j : Fin E.n) :
    E.scale.st i ≠ (E.scale.d j : ℤ) := by
  intro h
  have hi := i.isLt
  have hj := j.isLt
  rw [scale_st, scale_d] at h
  obtain ⟨h1, h2⟩ := scaled_inj (by omega) (by omega) (by omega) (by omega) h
  have hij : i = j := Fin.ext (by omega)
  subst hij
  have hst : E.st i = (E.d i : ℤ) - E.q i := rfl
  have := hq i
  omega

/-! ## 4. The two instances are equivalent

Conflicts are unchanged, and this is where the EST order does real work: offsetting job
`i`'s whole interval by `i` moves both endpoints together, so intervals that merely touch
would start to overlap if the later-starting job had the smaller index. EST order rules
that out. -/

lemma scale_st_lt_d_iff {i j : Fin E.n} :
    E.scale.st i < (E.scale.d j : ℤ) ↔
      (E.st i < (E.d j : ℤ) ∨ (E.st i = (E.d j : ℤ) ∧ (i : ℕ) < (j : ℕ))) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [scale_st, scale_d, scaled_lt_iff (by omega) (by omega) (by omega) (by omega)]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by exact_mod_cast h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by exact_mod_cast h2⟩

/-- **Scaling preserves conflicts** — the step that needs the EST order. -/
theorem scale_conflict_iff (hq : ∀ i, 0 < E.q i) {i j : Fin E.n} :
    E.scale.toFFJ.Conflict i j ↔ E.toFFJ.Conflict i j := by
  have key : ∀ a b : Fin E.n, E.scale.st a < (E.scale.d b : ℤ) → E.st a < (E.d b : ℤ) := by
    intro a b h
    rcases scale_st_lt_d_iff.mp h with h1 | ⟨h1, h2⟩
    · exact h1
    · -- `s_a = d_b` with `a` before `b` cannot happen: `d_b > s_b`, so `a` starts later
      exfalso
      have hbb : E.st b < (E.d b : ℤ) := by
        have hst : E.st b = (E.d b : ℤ) - E.q b := rfl
        have := hq b
        omega
      have hab : E.st a ≤ E.st b := E.st_mono (Fin.le_def.mpr (le_of_lt h2))
      omega
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨key i j h1, key j i h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨scale_st_lt_d_iff.mpr (Or.inl h1), scale_st_lt_d_iff.mpr (Or.inl h2)⟩

/-- Condition 2 is unchanged: same machines, same conflicts. -/
theorem scale_mSchedulable_iff (hq : ∀ i, 0 < E.q i) (Z : Finset (Fin E.n)) :
    E.scale.toFFJ.MSchedulable Z ↔ E.toFFJ.MSchedulable Z := by
  constructor
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, h1, fun i hi j hj hij hc hcon =>
      h2 i hi j hj hij hc ((scale_conflict_iff hq).mpr hcon)⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, h1, fun i hi j hj hij hc hcon =>
      h2 i hi j hj hij hc ((scale_conflict_iff hq).mp hcon)⟩

/-- **Condition 1 is unchanged.** Scaling makes the start times strictly increasing, so the
scaled instance's Condition 1 sums over an *index prefix* while the original's sums over the
tie-inclusive set — the two readings `preprocessable_iff_from_zero` reconciles. The offset
`j < n+1` is then absorbed because the left-hand side is a multiple of `n+1`. -/
theorem scale_preprocessable_iff (Z : Finset (Fin E.n)) :
    E.scale.toFFJ.Preprocessable Z ↔ E.toFFJ.Preprocessable Z := by
  classical
  -- the offset `j < n+1` is absorbed because the left-hand side is a multiple of `n+1`
  have hkey : ∀ (S T : ℤ) (jv : ℕ), jv < E.n →
      (((E.n : ℤ) + 1) * S ≤ ((E.n : ℤ) + 1) * T + jv ↔ S ≤ T) := by
    intro S T jv hjv
    constructor
    · intro h
      by_contra hc
      have h2 : ((E.n : ℤ) + 1) * (T + 1) ≤ ((E.n : ℤ) + 1) * S :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h3 : ((E.n : ℤ) + 1) * (T + 1) = ((E.n : ℤ) + 1) * T + ((E.n : ℤ) + 1) := by ring
      omega
    · intro h
      have h2 : ((E.n : ℤ) + 1) * S ≤ ((E.n : ℤ) + 1) * T :=
        Int.mul_le_mul_of_nonneg_left h (by omega)
      omega
  have main : ∀ j : Fin E.n,
      ((∑ i ∈ Z.filter (fun i => E.scale.toFFJ.s i ≤ E.scale.toFFJ.s j),
          (E.scale.toFFJ.p i : ℤ)) ≤ E.scale.toFFJ.s j
        ↔ 0 + ∑ i ∈ Z.filter (fun i => i ≤ j), (E.p i : ℤ) ≤ E.st j) := by
    intro j
    have hset : Z.filter (fun i => E.scale.toFFJ.s i ≤ E.scale.toFFJ.s j)
        = Z.filter (fun i => i ≤ j) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxZ, hxs⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxZ, (scale_st_le_iff (E := E)).mp hxs⟩
      · intro hx
        obtain ⟨hxZ, hxs⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxZ, (scale_st_le_iff (E := E)).mpr hxs⟩
    have hsum : ∑ i ∈ Z.filter (fun i => E.scale.toFFJ.s i ≤ E.scale.toFFJ.s j),
          (E.scale.toFFJ.p i : ℤ)
        = ((E.n : ℤ) + 1) * ∑ i ∈ Z.filter (fun i => i ≤ j), (E.p i : ℤ) := by
      rw [hset, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hp : E.scale.toFFJ.p x = (E.n + 1) * E.p x := rfl
      rw [hp]
      push_cast
      ring
    have hst : E.scale.toFFJ.s j = ((E.n : ℤ) + 1) * E.st j + (j : ℕ) := scale_st j
    rw [hsum, hst]
    have := hkey (∑ i ∈ Z.filter (fun i => i ≤ j), (E.p i : ℤ)) (E.st j) (j : ℕ) j.isLt
    omega
  rw [preprocessable_iff_from_zero]
  exact ⟨fun h j hj => (main j).mp (h j hj), fun h j hj => (main j).mpr (h j hj)⟩

/-- **The normalization is faithful.** -/
theorem scale_feasible_iff (hq : ∀ i, 0 < E.q i) (Z : Finset (Fin E.n)) :
    E.scale.toFFJ.Feasible Z ↔ E.toFFJ.Feasible Z := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (E.scale.toFFJ.feasible_iff Z).mp h
    exact (E.toFFJ.feasible_iff Z).mpr
      ⟨(scale_preprocessable_iff Z).mp h1, (scale_mSchedulable_iff hq Z).mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (E.toFFJ.feasible_iff Z).mp h
    exact (E.scale.toFFJ.feasible_iff Z).mpr
      ⟨(scale_preprocessable_iff Z).mpr h1, (scale_mSchedulable_iff hq Z).mpr h2⟩

/-- **The normalization delivers exactly what the sweep of Sections 4 and 5 assumes.** -/
theorem scale_distinctEndpoints (hq : ∀ i, 0 < E.q i) :
    E.scale.toFFJ.DistinctEndpoints :=
  ⟨fun _ _ h => scale_st_injective (E := E) h,
   fun _ _ h => scale_d_injective (E := E) (by exact_mod_cast h),
   fun i j => scale_st_ne_d (E := E) hq i j⟩


end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
