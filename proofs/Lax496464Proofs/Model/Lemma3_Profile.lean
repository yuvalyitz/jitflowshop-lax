import Lax496464Proofs.Model.Lemma2_Sweep
import Mathlib.Order.Interval.Finset.Nat

namespace Lax496464Proofs

/-!
# Section 5: the due-date profile behind Theorem 3's second program

Section 5's program replaces Section 4's *set* `X` of running jobs by a *count vector*
`x⃗ = (x₁, …, x_{q_max}) ∈ {0, …, m}^{q_max}`, where `xᵢ` is the number of second-stage
machines whose last job completes at `sⱼ + i`. That is what makes the table
`O(m^{q_max})` wide instead of `O(2^ω)`.

**The vector is a function of `Z` and the time alone.** On a machine, the assigned jobs have
pairwise disjoint second-operation intervals; since every job of `Z ⊆ Jⱼ` starts at or before
`sⱼ`, a job still running at `sⱼ` cannot be followed by another on its machine, so it *is*
its machine's last job — and conversely a machine whose last job completes after `sⱼ` has
that job running at `sⱼ`. Hence

`xᵢ = #{k ∈ Z : d_k = sⱼ + i}`,

with no reference to a schedule. `dueProfile` is that count and `card_running_eq_sum` is the
bridge to Section 4: summing the profile recovers `|running Z t|`, which is what the
`m`-machine bound constrains.

**One difference from the paper, in the encoding.** The paper's shift
`x⃗[δ] = {y⃗ : yᵢ = x_{i−δ} for i ∈ {δ+1, …, q_max}}` leaves the *last* `δ` coordinates of
the shifted vector unconstrained — `x⃗` in the branch that skips job `j`, `x⃗^{(qⱼ)}` in the
branch that takes it. They are not free: either way the vector is the profile of a subset
of `J_{j−1}`, all due by `s_{j−1} + q_max = sⱼ + q_max − δⱼ`. Without that condition Lemma 3's
invariant is **false**, in both branches — `Lemma3_Literal.lean` machine-checks a
counterexample for each. This development carries the profile as a function on all `i ≥ 1`
rather than a truncated vector, which constrains every coordinate and so proves the repaired
recursion; `dueProfile_eq_zero` is the fact the truncated encoding needs.
The algorithm's *final optimum* appears unaffected (never wrong on 5,200 random instances,
`scripts/lemma3_check.py`), but that is evidence, not a proof.
-/

namespace FFJ

variable {I : FFJ}

/-! ## 1. The profile -/

variable (I) in
/-- `dueProfile Z t i` is the number of jobs of `Z` due exactly at `t + i` — the paper's
`xᵢ`, read off the job set instead of a schedule. -/
def dueProfile (Z : Finset I.Job) (t : ℤ) (i : ℕ) : ℕ :=
  (Z.filter (fun k => (I.d k : ℤ) = t + i)).card

/-- Moving the reference time back by `δ` shifts the profile by `δ`. -/
lemma dueProfile_shift {Z : Finset I.Job} {t' t : ℤ} {δ : ℕ} (hδ : (δ : ℤ) = t - t')
    (i : ℕ) : I.dueProfile Z t i = I.dueProfile Z t' (δ + i) := by
  unfold dueProfile
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, by push_cast; omega⟩
  · rintro ⟨hx, h⟩; exact ⟨hx, by push_cast at h; omega⟩

/-- **Nothing is due beyond `t + q_max`.** This is the fact the paper's truncation at
`q_max` rests on, and the reason the shifted vector's tail must vanish. -/
lemma dueProfile_eq_zero {Z : Finset I.Job} {t : ℤ} {qmax i : ℕ}
    (hb : ∀ k ∈ Z, I.s k ≤ t) (hqmax : ∀ k ∈ Z, I.q k ≤ qmax) (hi : qmax < i) :
    I.dueProfile Z t i = 0 := by
  rw [dueProfile, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨hxZ, hxd⟩ := Finset.mem_filter.mp hx
  have h1 : I.s x = (I.d x : ℤ) - I.q x := rfl
  have h2 := hb x hxZ
  have h3 := hqmax x hxZ
  omega

/-- **The bridge to Section 4.** Summing the profile counts the jobs still running. -/
lemma card_running_eq_sum {Z : Finset I.Job} {t : ℤ} {N : ℕ}
    (hb : ∀ k ∈ Z, I.s k ≤ t) (hN : ∀ k ∈ Z, (I.d k : ℤ) ≤ t + N) :
    (I.running Z t).card = ∑ i ∈ Finset.Icc 1 N, I.dueProfile Z t i := by
  classical
  have hmem : ∀ k ∈ I.running Z t, ((I.d k : ℤ) - t).toNat ∈ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨hkZ, -, hk2⟩ := mem_running.mp hk
    have := hN k hkZ
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  congr 1
  ext x
  simp only [running, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hxZ, -, hx2⟩, hfib⟩
    exact ⟨hxZ, by omega⟩
  · rintro ⟨hxZ, hxd⟩
    exact ⟨⟨hxZ, hb x hxZ, by omega⟩, by omega⟩

/-! ## 2. The table -/

variable (I) in
/-- **Section 5's table entry**, as a predicate: some feasible `Z`, all of whose jobs have
started by `t`, has weight `W'`, due-date profile `x` at `t`, and load at most `P'`. -/
def ReachableProfile (t : ℤ) (x : ℕ → ℕ) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, I.Feasible Z ∧ (∀ k ∈ Z, I.s k ≤ t) ∧
    (∀ i, 1 ≤ i → I.dueProfile Z t i = x i) ∧ I.weight Z = W' ∧ I.pload Z ≤ P'

/-! ## 3. Adding a job to the profile -/

lemma dueProfile_insert {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) (t : ℤ) (i : ℕ) :
    I.dueProfile (insert j Z) t i
      = I.dueProfile Z t i + (if (I.d j : ℤ) = t + i then 1 else 0) := by
  classical
  rw [dueProfile, dueProfile, Finset.filter_insert]
  by_cases h : (I.d j : ℤ) = t + i
  · rw [if_pos h, if_pos h,
      Finset.card_insert_of_notMem (fun hc => hj (Finset.mem_filter.mp hc).1)]
  · rw [if_neg h, if_neg h]
    omega

/-- A job starting exactly at the reference time lands in coordinate `qⱼ`. -/
lemma dueProfile_insert_start {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) {t : ℤ}
    (hsj : I.s j = t) (i : ℕ) :
    I.dueProfile (insert j Z) t i
      = I.dueProfile Z t i + (if i = I.q j then 1 else 0) := by
  rw [dueProfile_insert hj]
  congr 1
  have hs : I.s j = (I.d j : ℤ) - I.q j := rfl
  by_cases h : i = I.q j
  · have h1 : (I.d j : ℤ) = t + i := by rw [h]; omega
    rw [if_pos h1, if_pos h]
  · have h1 : ¬ ((I.d j : ℤ) = t + i) := fun hc => h (by omega)
    rw [if_neg h1, if_neg h]

/-- Decrementing one coordinate of a profile drops its total by one. -/
lemma sum_ite_sub_one {N q : ℕ} (x : ℕ → ℕ) (hq : q ∈ Finset.Icc 1 N) (hx : 1 ≤ x q) :
    (∑ i ∈ Finset.Icc 1 N, (if i = q then x i - 1 else x i)) + 1
      = ∑ i ∈ Finset.Icc 1 N, x i := by
  classical
  have h1 : ∑ i ∈ Finset.Icc 1 N, (if i = q then x i - 1 else x i)
      = (x q - 1) + ∑ i ∈ (Finset.Icc 1 N).erase q, x i := by
    rw [← Finset.add_sum_erase _ (fun i => if i = q then x i - 1 else x i) hq, if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_erase.mp hi).1)
  have h2 : ∑ i ∈ Finset.Icc 1 N, x i
      = x q + ∑ i ∈ (Finset.Icc 1 N).erase q, x i :=
    (Finset.add_sum_erase _ (fun i => x i) hq).symm
  omega

/-! ## 4. Recursion (5)

The step from `s_{j−1}` to `sⱼ`. As in `Lemma2_Sweep.lean` it is stated between two times
rather than between two positions in an enumeration: all that is used is that `j` is the
only job starting in `(t', t]`. The paper's `x⃗[δ]` appears as the shift condition
`x i = y (δ + i)`, and `x⃗^{(qⱼ)}` as the same condition on the profile with coordinate `qⱼ`
decremented. -/

/-- **Equation (5).** Job `j` either stays out — the profile is just the previous one,
shifted — or joins, which costs `wⱼ`, adds `pⱼ` to the load (so must fit before `sⱼ`), and
occupies coordinate `qⱼ` of the profile. -/
theorem reachableProfile_start {t' t : ℤ} {δ qmax : ℕ} {j : I.Job}
    {x : ℕ → ℕ} {W' : ℕ} {P' : ℤ}
    (hq : ∀ i, 0 < I.q i) (hqmax : ∀ k : I.Job, I.q k ≤ qmax)
    (hδ : (δ : ℤ) = t - t') (htt : t' < t) (hsj : I.s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < I.s k ∧ I.s k ≤ t)) :
    I.ReachableProfile t x W' P' ↔
      (∃ y : ℕ → ℕ, (∀ i, 1 ≤ i → x i = y (δ + i)) ∧
        I.ReachableProfile t' y W' P') ∨
      (0 < x (I.q j) ∧ (∑ i ∈ Finset.Icc 1 qmax, x i) ≤ I.numMachines ∧
        ∃ (W'' : ℕ) (P'' : ℤ) (y : ℕ → ℕ),
          W'' + I.w j = W' ∧
          (∀ i, 1 ≤ i → (if i = I.q j then x i - 1 else x i) = y (δ + i)) ∧
          I.ReachableProfile t' y W'' P'' ∧
          P'' + I.p j ≤ I.s j ∧ P'' + I.p j ≤ P') := by
  classical
  have hqjmem : I.q j ∈ Finset.Icc 1 qmax :=
    Finset.mem_Icc.mpr ⟨hq j, hqmax j⟩
  -- every job due by `t + qmax`, for any set whose jobs have started
  have hdb : ∀ (Y : Finset I.Job), (∀ k ∈ Y, I.s k ≤ t) →
      ∀ k ∈ Y, (I.d k : ℤ) ≤ t + qmax := by
    intro Y hY k hk
    have h1 : I.s k = (I.d k : ℤ) - I.q k := rfl
    have h2 := hY k hk
    have h3 := hqmax k
    omega
  constructor
  · rintro ⟨Z, hf, hb, hprof, hw, hp⟩
    obtain ⟨hpre, hsch⟩ := (I.feasible_iff Z).mp hf
    have hbZ : ∀ k ∈ Z, k ≠ j → I.s k ≤ t' := by
      intro k hk hkj
      have := hnos k hkj
      have := hb k hk
      omega
    by_cases hjZ : j ∈ Z
    · right
      have hbZ' : ∀ k ∈ Z.erase j, I.s k ≤ t' :=
        fun k hk => hbZ k (Finset.mem_of_mem_erase hk) (Finset.mem_erase.mp hk).1
      have hbZ'' : ∀ k ∈ Z.erase j, I.s k ≤ t :=
        fun k hk => le_trans (hbZ' k hk) (le_of_lt htt)
      have hins : ∀ i : ℕ, I.dueProfile Z t i
          = I.dueProfile (Z.erase j) t i + (if i = I.q j then 1 else 0) := by
        intro i
        conv_lhs => rw [← Finset.insert_erase hjZ]
        exact dueProfile_insert_start (Finset.notMem_erase _ _) hsj i
      have hxq : 0 < x (I.q j) := by
        have h1 := hprof (I.q j) (hq j)
        have h2 := hins (I.q j)
        rw [if_pos rfl] at h2
        omega
      -- the machine bound, read off the profile
      have hcap : (∑ i ∈ Finset.Icc 1 qmax, x i) ≤ I.numMachines := by
        have hsum := card_running_eq_sum hb (hdb Z hb)
        have hcong : ∑ i ∈ Finset.Icc 1 qmax, I.dueProfile Z t i
            = ∑ i ∈ Finset.Icc 1 qmax, x i :=
          Finset.sum_congr rfl fun i hi => hprof i (Finset.mem_Icc.mp hi).1
        have := card_running_le_of_mSchedulable hsch t
        omega
      -- Condition 1 read at `j`, which starts last
      have hall : Z.filter (fun i => I.s i ≤ I.s j) = Z :=
        Finset.filter_true_of_mem (fun y hy => by have := hb y hy; omega)
      have hfit : I.pload Z ≤ I.s j := by
        have := hpre j hjZ
        rwa [hall] at this
      have hploadZ : I.pload Z = I.pload (Z.erase j) + I.p j := by
        conv_lhs => rw [← Finset.insert_erase hjZ]
        rw [pload_insert (Finset.notMem_erase _ _)]
      have hwZ : I.weight (Z.erase j) + I.w j = I.weight Z := Finset.sum_erase_add Z _ hjZ
      refine ⟨hxq, hcap, I.weight (Z.erase j), I.pload (Z.erase j),
        I.dueProfile (Z.erase j) t', by omega, ?_,
        ⟨Z.erase j, Feasible.subset (h := hf) (hsub := Finset.erase_subset _ _), hbZ',
          fun i _ => rfl, rfl, le_rfl⟩, by omega, by omega⟩
      intro i hi
      rw [← dueProfile_shift hδ]
      have h1 := hprof i hi
      have h2 := hins i
      by_cases hij : i = I.q j
      · rw [if_pos hij]; rw [if_pos hij] at h2; omega
      · rw [if_neg hij]; rw [if_neg hij] at h2; omega
    · left
      have hbZ' : ∀ k ∈ Z, I.s k ≤ t' :=
        fun k hk => hbZ k hk (fun hc => hjZ (hc ▸ hk))
      exact ⟨I.dueProfile Z t', fun i hi => by
        rw [← dueProfile_shift hδ]; exact (hprof i hi).symm,
        Z, hf, hbZ', fun i _ => rfl, hw, hp⟩
  · rintro (⟨y, hxy, Z, hf, hb, hprof, hw, hp⟩ |
      ⟨hxq, hcap, W'', P'', y, hW, hxy, ⟨Z, hf, hb, hprof, hw, hp⟩, hfit, hbud⟩)
    · refine ⟨Z, hf, fun k hk => le_trans (hb k hk) (le_of_lt htt), fun i hi => ?_, hw, hp⟩
      rw [dueProfile_shift hδ, hprof _ (by omega), ← hxy i hi]
    · have hjZ : j ∉ Z := fun hc => by have := hb j hc; omega
      have hlast : ∀ i ∈ Z, I.s i < I.s j := fun i hi => by have := hb i hi; omega
      have hbt : ∀ k ∈ Z, I.s k ≤ t := fun k hk => le_trans (hb k hk) (le_of_lt htt)
      -- the profile of `Z` at `t` is `x` with coordinate `qⱼ` decremented
      have hZprof : ∀ i, 1 ≤ i →
          I.dueProfile Z t i = (if i = I.q j then x i - 1 else x i) := by
        intro i hi
        rw [dueProfile_shift hδ, hprof _ (by omega), ← hxy i hi]
      -- hence a machine is free at `sⱼ`
      have hroom : (I.running Z (I.s j)).card < I.numMachines := by
        rw [hsj, card_running_eq_sum hbt (hdb Z hbt)]
        have hcong : ∑ i ∈ Finset.Icc 1 qmax, I.dueProfile Z t i
            = ∑ i ∈ Finset.Icc 1 qmax, (if i = I.q j then x i - 1 else x i) :=
          Finset.sum_congr rfl fun i hi => hZprof i (Finset.mem_Icc.mp hi).1
        have := sum_ite_sub_one x hqjmem hxq
        omega
      refine ⟨insert j Z,
        feasible_insert hq hjZ hf hlast (by have := pload_nonneg Z; omega) hroom,
        ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · omega
        · exact hbt k hk
      · intro i hi
        rw [dueProfile_insert_start hjZ hsj, hZprof i hi]
        by_cases hij : i = I.q j
        · subst hij
          rw [if_pos rfl, if_pos rfl]
          omega
        · rw [if_neg hij, if_neg hij]
          omega
      · rw [weight, Finset.sum_insert hjZ]
        have hsum : ∑ i ∈ Z, I.w i = W'' := hw
        omega
      · rw [pload_insert hjZ]
        omega


/-! ## 5. The two ends of the sweep -/

/-- **The final read-off, `T_n`.** Once every job has started, some profile is reachable at
weight `W'` exactly when a feasible solution of that weight exists. -/
theorem exists_reachableProfile_iff {t : ℤ} (ht : ∀ k : I.Job, I.s k ≤ t) (W' : ℕ) :
    (∃ (x : ℕ → ℕ) (P' : ℤ), I.ReachableProfile t x W' P') ↔
      ∃ Z : Finset I.Job, I.Feasible Z ∧ I.weight Z = W' := by
  constructor
  · rintro ⟨x, P', Z, hf, -, -, hw, -⟩
    exact ⟨Z, hf, hw⟩
  · rintro ⟨Z, hf, hw⟩
    exact ⟨I.dueProfile Z t, I.pload Z, Z, hf, fun k _ => ht k, fun _ _ => rfl, hw, le_rfl⟩


end FFJ

end Lax496464Proofs
