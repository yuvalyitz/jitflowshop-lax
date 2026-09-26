import Lax496464Proofs.Model.IntervalColoring

namespace Lax496464Proofs

/-!
# Section 4: the endpoint sweep behind Theorem 3's first program

Section 4's dynamic program sweeps the `2n` endpoints `t₁ < ⋯ < t_{2n}` of the jobs'
second-operation intervals (assumed distinct, which the paper arranges by scaling), keeping
a table

`Tᵢ[X, W'] = the least total preprocessing time of a feasible `Z ⊆ Jᵢ` of weight `W'` whose
selected jobs still running at `tᵢ` are exactly `X`,`

where `Jᵢ = {k : s_k ≤ tᵢ}`. Since `|X| ≤ ω`, the table is small.

**This file indexes the sweep by the time itself, not by the endpoint's position.** All the
recursion ever uses of "`tᵢ` and `t_{i−1}` are consecutive endpoints" is that no start time
and no due date lies in the half-open interval `(t_{i−1}, tᵢ]` other than the one event at
`tᵢ`; stating that directly removes the sorted enumeration of endpoints entirely, and with
it the index arithmetic that would otherwise dominate the development.

`Reachable t X W' P'` is the table entry as a *predicate* — upward closed in `P'`, since a
larger budget is easier — exactly as `Sorted.lean` records `T[X, W']` as `Achievable`. The
two recursion steps are `reachable_due` (Eq. (4)) and `reachable_start` (Eq. (3)); together
they are Lemma 2.

`hq` (positive second-stage times) is the paper's standing assumption on the input.
-/

namespace FFJ

variable {I : FFJ}

/-! ## 1. Preprocessing load, and Condition 1 at the last job -/

variable (I) in
/-- The paper's `p(Z)`: the total preprocessing time of `Z`. -/
def pload (Z : Finset I.Job) : ℤ := ∑ i ∈ Z, (I.p i : ℤ)

lemma pload_nonneg (Z : Finset I.Job) : 0 ≤ I.pload Z :=
  Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

lemma pload_insert {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) :
    I.pload (insert j Z) = I.pload Z + I.p j := by
  rw [pload, pload, Finset.sum_insert hj]
  ring

/-- **Condition 1 splits at the last job.** When `j` starts strictly after everything in
`Z`, preprocessing `Z ∪ {j}` in time is preprocessing `Z` in time and fitting `j`'s own
operation before `sⱼ`. -/
theorem preprocessable_insert_iff {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z)
    (hlast : ∀ i ∈ Z, I.s i < I.s j) :
    I.Preprocessable (insert j Z) ↔
      I.Preprocessable Z ∧ I.pload Z + I.p j ≤ I.s j := by
  classical
  have hall : (insert j Z).filter (fun i => I.s i ≤ I.s j) = insert j Z := by
    refine Finset.filter_true_of_mem ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt (hlast x hx)
  have hj_sum : ∑ i ∈ insert j Z, (I.p i : ℤ) = I.pload Z + I.p j := by
    rw [← pload_insert hj, pload]
  constructor
  · intro h
    refine ⟨Preprocessable.subset (h := h) (hsub := Finset.subset_insert _ _), ?_⟩
    have := h j (Finset.mem_insert_self _ _)
    rwa [hall, hj_sum] at this
  · rintro ⟨hZ, hfit⟩ j' hj'
    rw [Finset.filter_insert]
    rcases Finset.mem_insert.mp hj' with rfl | hj'Z
    · rw [if_pos le_rfl]
      have : Z.filter (fun i => I.s i ≤ I.s j') = Z := Finset.filter_true_of_mem
        (fun x hx => le_of_lt (hlast x hx))
      rw [this, Finset.sum_insert hj]
      have := hfit
      rw [pload] at this
      omega
    · rw [if_neg (not_le.mpr (hlast j' hj'Z))]
      exact hZ j' hj'Z

/-! ## 2. Adding the latest job -/

/-- **A job that starts after everything selected so far may join**, provided its own
preprocessing fits before `sⱼ` and a machine is free when it starts. This is the general
form of `Section6_Greedy.lean`'s `feasible_insert_of_uniform`, with the uniform count
replaced by the actual load. -/
theorem feasible_insert {Z : Finset I.Job} {j : I.Job} (hq : ∀ i, 0 < I.q i)
    (hjZ : j ∉ Z) (hfeas : I.Feasible Z) (hlast : ∀ i ∈ Z, I.s i < I.s j)
    (hcount : I.pload Z + I.p j ≤ I.s j)
    (hroom : (I.running Z (I.s j)).card < I.numMachines) :
    I.Feasible (insert j Z) := by
  classical
  obtain ⟨hpre, hsch⟩ := (I.feasible_iff Z).mp hfeas
  refine (I.feasible_iff _).mpr ⟨(preprocessable_insert_iff hjZ hlast).mpr ⟨hpre, hcount⟩, ?_⟩
  rw [mSchedulable_iff_card_running_le (fun i _ => hq i)]
  have hZle : ∀ t : ℤ, (I.running Z t).card ≤ I.numMachines :=
    (mSchedulable_iff_card_running_le (fun i _ => hq i)).mp hsch
  intro t
  by_cases hja : I.s j ≤ t ∧ t < (I.d j : ℤ)
  · have hrun : I.running (insert j Z) t = insert j (I.running Z t) := by
      unfold running
      rw [Finset.filter_insert, if_pos hja]
    rw [hrun]
    have hsub : I.running Z t ⊆ I.running Z (I.s j) := by
      intro x hx
      obtain ⟨hxZ, hx1, hx2⟩ := mem_running.mp hx
      exact mem_running.mpr ⟨hxZ, le_of_lt (hlast x hxZ), by omega⟩
    have h1 := Finset.card_insert_le j (I.running Z t)
    have h2 := Finset.card_le_card hsub
    omega
  · have hrun : I.running (insert j Z) t = I.running Z t := by
      unfold running
      rw [Finset.filter_insert, if_neg hja]
    rw [hrun]
    exact hZle t

/-! ## 3. The table, as a predicate -/

variable (I) in
/-- **The sweep's table entry.** Some feasible `Z`, all of whose jobs have started by `t`,
has weight `W'`, is running exactly `X` at `t`, and can be preprocessed within `P'`. -/
def Reachable (t : ℤ) (X : Finset I.Job) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, I.Feasible Z ∧ (∀ k ∈ Z, I.s k ≤ t) ∧
    I.running Z t = X ∧ I.weight Z = W' ∧ I.pload Z ≤ P'

/-! ## 4. Between consecutive endpoints nothing changes -/

/-- If no due date of `Z` falls in `(t', t]` and every job of `Z` has started by `t'`, the
set of jobs running is the same at both times. -/
lemma running_eq_of_no_event {Z : Finset I.Job} {t' t : ℤ} (htt : t' ≤ t)
    (hZ : ∀ k ∈ Z, I.s k ≤ t')
    (hno : ∀ k ∈ Z, ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    I.running Z t = I.running Z t' := by
  ext x
  simp only [mem_running]
  constructor
  · rintro ⟨hxZ, -, hx2⟩
    exact ⟨hxZ, hZ x hxZ, by have := hno x hxZ; omega⟩
  · rintro ⟨hxZ, -, hx2⟩
    exact ⟨hxZ, le_trans (hZ x hxZ) htt, by have := hno x hxZ; omega⟩

/-! ## 5. The two steps of recursion (3) and (4) -/

/-- **Equation (4): a due date passes.** Crossing `dⱼ` either leaves the running set alone
(job `j` was not selected) or drops `j` from it. -/
theorem reachable_due {t' t : ℤ} {j : I.Job} {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (hq : ∀ i, 0 < I.q i) (htt : t' < t) (hdj : (I.d j : ℤ) = t)
    (hnos : ∀ k : I.Job, ¬ (t' < I.s k ∧ I.s k ≤ t))
    (hnod : ∀ k : I.Job, k ≠ j → ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    I.Reachable t X W' P' ↔
      j ∉ X ∧ (I.Reachable t' X W' P' ∨ I.Reachable t' (insert j X) W' P') := by
  classical
  -- job `j` has started by `t'`: its own start time is below `dⱼ = t`
  have hsj : I.s j ≤ t' := by
    have h1 : I.s j < (I.d j : ℤ) := by simp only [FFJ.s]; have := hq j; omega
    have := hnos j
    omega
  constructor
  · rintro ⟨Z, hf, hb, rfl, hw, hp⟩
    have hbZ : ∀ k ∈ Z, I.s k ≤ t' := fun k hk => by have := hnos k; have := hb k hk; omega
    refine ⟨fun hc => by have := (mem_running.mp hc).2.2; omega, ?_⟩
    by_cases hjZ : j ∈ Z
    · -- `j` was selected: it is running at `t'` and not at `t`
      right
      refine ⟨Z, hf, hbZ, ?_, hw, hp⟩
      ext x
      simp only [mem_running, Finset.mem_insert]
      constructor
      · rintro ⟨hxZ, -, hx2⟩
        by_cases hxj : x = j
        · exact Or.inl hxj
        · exact Or.inr ⟨hxZ, le_trans (hbZ x hxZ) (le_of_lt htt),
            by have := hnod x hxj; omega⟩
      · rintro (rfl | ⟨hxZ, -, hx2⟩)
        · exact ⟨hjZ, hsj, by omega⟩
        · exact ⟨hxZ, hbZ x hxZ, by omega⟩
    · left
      exact ⟨Z, hf, hbZ,
        (running_eq_of_no_event (le_of_lt htt) hbZ
          (fun k hk => hnod k (fun hc => hjZ (hc ▸ hk)))).symm, hw, hp⟩
  · rintro ⟨hjX, hcase | hcase⟩
    · obtain ⟨Z, hf, hb, rfl, hw, hp⟩ := hcase
      have hjZ : j ∉ Z := by
        intro hc
        exact hjX (mem_running.mpr ⟨hc, hsj, by omega⟩)
      exact ⟨Z, hf, fun k hk => le_trans (hb k hk) (le_of_lt htt),
        running_eq_of_no_event (le_of_lt htt) hb
          (fun k hk => hnod k (fun hc => hjZ (hc ▸ hk))), hw, hp⟩
    · obtain ⟨Z, hf, hb, hr, hw, hp⟩ := hcase
      have hjZ : j ∈ Z := (mem_running.mp (hr ▸ Finset.mem_insert_self j X)).1
      refine ⟨Z, hf, fun k hk => le_trans (hb k hk) (le_of_lt htt), ?_, hw, hp⟩
      ext x
      simp only [mem_running]
      constructor
      · rintro ⟨hxZ, -, hx2⟩
        have hxj : x ≠ j := fun hc => by rw [hc] at hx2; omega
        have : x ∈ insert j X := hr ▸ mem_running.mpr ⟨hxZ, hb x hxZ, by
          have := hnod x hxj; omega⟩
        exact (Finset.mem_insert.mp this).resolve_left hxj
      · intro hx
        have hx' : x ∈ I.running Z t' := hr ▸ Finset.mem_insert_of_mem hx
        obtain ⟨hxZ, -, hx2⟩ := mem_running.mp hx'
        have hxj : x ≠ j := fun hc => hjX (hc ▸ hx)
        exact ⟨hxZ, le_trans (hb x hxZ) (le_of_lt htt), by have := hnod x hxj; omega⟩

/-- **Equation (3): a start time passes.** Crossing `sⱼ`, job `j` either stays out — the
running set is unchanged — or joins, which costs `wⱼ`, adds `pⱼ` to the load (and so must
fit before `sⱼ`), and needs a machine free at `sⱼ`. -/
theorem reachable_start {t' t : ℤ} {j : I.Job} {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (hq : ∀ i, 0 < I.q i) (htt : t' < t) (hsj : I.s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < I.s k ∧ I.s k ≤ t))
    (hnod : ∀ k : I.Job, ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    I.Reachable t X W' P' ↔
      (j ∉ X ∧ I.Reachable t' X W' P') ∨
      (j ∈ X ∧ (X.erase j).card < I.numMachines ∧
        ∃ (W'' : ℕ) (P'' : ℤ), W'' + I.w j = W' ∧ I.Reachable t' (X.erase j) W'' P'' ∧
          P'' + I.p j ≤ I.s j ∧ P'' + I.p j ≤ P') := by
  classical
  have hjalive : I.s j ≤ t ∧ t < (I.d j : ℤ) := by
    have : I.s j < (I.d j : ℤ) := by simp only [FFJ.s]; have := hq j; omega
    omega
  constructor
  · rintro ⟨Z, hf, hb, rfl, hw, hp⟩
    obtain ⟨hpre, hsch⟩ := (I.feasible_iff Z).mp hf
    have hbZ : ∀ k ∈ Z, k ≠ j → I.s k ≤ t' := by
      intro k hk hkj
      have := hnos k hkj
      have := hb k hk
      omega
    by_cases hjZ : j ∈ Z
    · -- `j` was selected
      right
      have hjX : j ∈ I.running Z t := mem_running.mpr ⟨hjZ, hjalive.1, hjalive.2⟩
      have hbZ' : ∀ k ∈ Z.erase j, I.s k ≤ t' :=
        fun k hk => hbZ k (Finset.mem_of_mem_erase hk) (Finset.mem_erase.mp hk).1
      have herase : ∀ u : ℤ, I.running (Z.erase j) u = (I.running Z u).erase j := by
        intro u
        ext x
        simp only [running, Finset.mem_filter, Finset.mem_erase]
        tauto
      have hrun' : I.running (Z.erase j) t' = (I.running Z t).erase j := by
        rw [← running_eq_of_no_event (le_of_lt htt) hbZ' (fun k hk => hnod k), herase]
      -- Condition 1 read at `j`, which starts last
      have hall : Z.filter (fun i => I.s i ≤ I.s j) = Z :=
        Finset.filter_true_of_mem (fun x hx => by have := hb x hx; omega)
      have hfit : I.pload Z ≤ I.s j := by
        have := hpre j hjZ
        rwa [hall] at this
      have hploadZ : I.pload Z = I.pload (Z.erase j) + I.p j := by
        conv_lhs => rw [← Finset.insert_erase hjZ]
        rw [pload_insert (Finset.notMem_erase _ _)]
      have hwZ : I.weight (Z.erase j) + I.w j = I.weight Z := Finset.sum_erase_add Z _ hjZ
      have hmcard : (I.running Z t).card ≤ I.numMachines :=
        card_running_le_of_mSchedulable hsch t
      have hpos : 0 < (I.running Z t).card := Finset.card_pos.mpr ⟨j, hjX⟩
      refine ⟨hjX, ?_, I.weight (Z.erase j), I.pload (Z.erase j), by omega,
        ⟨Z.erase j, Feasible.subset (h := hf) (hsub := Finset.erase_subset _ _), hbZ',
          hrun', rfl, le_rfl⟩, by omega, by omega⟩
      rw [Finset.card_erase_of_mem hjX]
      omega
    · -- `j` was not selected
      left
      have hbZ' : ∀ k ∈ Z, I.s k ≤ t' :=
        fun k hk => hbZ k hk (fun hc => hjZ (hc ▸ hk))
      exact ⟨fun hc => hjZ (mem_running.mp hc).1,
        Z, hf, hbZ',
        (running_eq_of_no_event (le_of_lt htt) hbZ' (fun k _ => hnod k)).symm, hw, hp⟩
  · rintro (hleft | hright)
    · obtain ⟨hjX, Z, hf, hb, rfl, hw, hp⟩ := hleft
      have hjZ : j ∉ Z := fun hc => by have := hb j hc; omega
      exact ⟨Z, hf, fun k hk => le_trans (hb k hk) (le_of_lt htt),
        running_eq_of_no_event (le_of_lt htt) hb (fun k _ => hnod k), hw, hp⟩
    · obtain ⟨hjX, hcard, W'', P'', hW, ⟨Z, hf, hb, hr, hw, hp⟩, hfit, hbud⟩ := hright
      have hjZ : j ∉ Z := fun hc => by have := hb j hc; omega
      have hlast : ∀ i ∈ Z, I.s i < I.s j := fun i hi => by have := hb i hi; omega
      have hrunt : I.running Z (I.s j) = X.erase j := by
        rw [hsj, running_eq_of_no_event (le_of_lt htt) hb (fun k _ => hnod k), hr]
      refine ⟨insert j Z,
        feasible_insert hq hjZ hf hlast (by have := pload_nonneg Z; omega)
          (by rw [hrunt]; exact hcard),
        ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · omega
        · exact le_trans (hb k hk) (le_of_lt htt)
      · have hins : I.running (insert j Z) t = insert j (I.running Z t) := by
          unfold running
          rw [Finset.filter_insert, if_pos hjalive]
        rw [hins, running_eq_of_no_event (le_of_lt htt) hb (fun k _ => hnod k), hr,
          Finset.insert_erase hjX]
      · rw [weight, Finset.sum_insert hjZ]
        have hsum : ∑ i ∈ Z, I.w i = W'' := hw
        omega
      · rw [pload_insert hjZ]
        omega


/-! ## 6. The two ends of the sweep -/

/-- **The base case, `T₀`.** Before any job has started, the only reachable entry is the
empty solution. -/
theorem reachable_of_lt_all {t : ℤ} (ht : ∀ k : I.Job, t < I.s k)
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ} :
    I.Reachable t X W' P' ↔ X = ∅ ∧ W' = 0 ∧ 0 ≤ P' := by
  constructor
  · rintro ⟨Z, hf, hb, hr, hw, hp⟩
    have hZ : Z = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by
      have := hb x hx; have := ht x; omega
    subst hZ
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr]; simp [running]
    · rw [← hw]; simp [weight]
    · simpa [pload] using hp
  · rintro ⟨rfl, rfl, hP⟩
    exact ⟨∅, I.feasible_empty, by simp, by simp [running], by simp [weight],
      by simpa [pload] using hP⟩

/-- **The final read-off, `T_{2n}`.** Once every job has started, some entry of the table is
reachable at weight `W'` exactly when a feasible solution of that weight exists — which is
what the paper's *"find the maximum `W'` such that there exists an `X ⊆ X_{2n}` with
`T_{2n}[X, W'] ≠ ∞`"* reads off. -/
theorem exists_reachable_iff {t : ℤ} (ht : ∀ k : I.Job, I.s k ≤ t) (W' : ℕ) :
    (∃ (X : Finset I.Job) (P' : ℤ), I.Reachable t X W' P') ↔
      ∃ Z : Finset I.Job, I.Feasible Z ∧ I.weight Z = W' := by
  constructor
  · rintro ⟨X, P', Z, hf, -, -, hw, -⟩
    exact ⟨Z, hf, hw⟩
  · rintro ⟨Z, hf, hw⟩
    exact ⟨I.running Z t, I.pload Z, Z, hf, fun k _ => ht k, rfl, hw, le_rfl⟩


/-! ## 7. Consecutive endpoints

The two steps above ask that `j` be the *only* event in `(t', t]`. That is what "`t'` and
`t` are consecutive endpoints of an instance whose endpoints are distinct" delivers, and
this section says so — which is the only part of the sweep's assembly with any content. -/

variable (I) in
/-- Every endpoint of a second-operation interval. -/
def endpoints : Finset ℤ :=
  (Finset.univ.image I.s) ∪ (Finset.univ.image (fun k => (I.d k : ℤ)))

variable (I) in
/-- The standing assumption of Sections 4 and 5: no two of the `2n` endpoints coincide.
`Section4_Distinct.lean` shows every instance can be normalized to one of these. -/
def DistinctEndpoints : Prop :=
  (∀ i j : I.Job, I.s i = I.s j → i = j) ∧
  (∀ i j : I.Job, (I.d i : ℤ) = (I.d j : ℤ) → i = j) ∧
  (∀ i j : I.Job, I.s i ≠ (I.d j : ℤ))

/-! ## 8. The sweep, assembled: the tables the recursion builds are the true tables

Recursions (3) and (4) as operators on the previous table. Any family of tables that starts
from the base case and, at every endpoint, is obtained from the table at the previous endpoint
by the event there, *is* `Reachable` at every endpoint. That is Lemma 2 for all `i` at once —
the recursion correctly computes every `Tᵢ` — and with `exists_reachable_iff` it gives
Theorem 3's first algorithm. -/

/-- Recursion (4)'s right-hand side: job `j`'s due date passes. -/
def dueStep (j : I.Job) (R : Finset I.Job → ℕ → ℤ → Prop)
    (X : Finset I.Job) (W : ℕ) (P : ℤ) : Prop :=
  j ∉ X ∧ (R X W P ∨ R (insert j X) W P)

/-- Recursion (3)'s right-hand side: job `j` starts. -/
def startStep (j : I.Job) (R : Finset I.Job → ℕ → ℤ → Prop)
    (X : Finset I.Job) (W : ℕ) (P : ℤ) : Prop :=
  (j ∉ X ∧ R X W P) ∨
    (j ∈ X ∧ (X.erase j).card < I.numMachines ∧
      ∃ (W'' : ℕ) (P'' : ℤ), W'' + I.w j = W ∧ R (X.erase j) W'' P'' ∧
        P'' + I.p j ≤ I.s j ∧ P'' + I.p j ≤ P)

end FFJ

end Lax496464Proofs
