import Lax496464Proofs.Model.Section6_Uniform

namespace Lax496464Proofs

/-!
# Section 6.1: the two steps of the greedy algorithm

Section 6.1's algorithm for the *unweighted* `FF(1,m)|pⱼ = p|∑Zⱼ` problem sweeps the jobs
in EST order, maintaining a feasible set `Sⱼ ⊆ {1, …, j}`. At step `j` it tests the two
ways adding job `j` could break feasibility:

* `sⱼ < (|S_{j−1}| + 1)·p` — Condition 1 fails, there is no room to preprocess one more job
  before `sⱼ`;
* `m` jobs of `S_{j−1}` are running at `sⱼ` — Condition 2 fails, every machine is busy.

If neither fires, `Sⱼ = S_{j−1} ∪ {j}`. Otherwise `Sⱼ` is `S_{j−1} ∪ {j}` with **the job of
largest due date removed**.

This file proves that both steps land on feasible sets. Together they are the paper's
*"Note that if neither cases occur, the set `S_{j−1} ∪ {j}` is a feasible solution, since
the jobs are ordered according to the EST rule"* and *"The resulting subset `Sⱼ` is feasible
since `S_{j−1}` is feasible, and since `s_{jᵢ} ≤ sⱼ < d_{jᵢ}` for the removed job"*. They
are what Lemma 4's induction needs before it can talk about domination at all.

Both are stated for an arbitrary job type with `hlast : ∀ i ∈ Z, s i ≤ s j` in place of "the
jobs are in EST order and `j` comes last" — that is all either argument uses, and it keeps
the statements independent of any chosen enumeration.

`hq` (positive second-stage times) is the paper's standing assumption on the input; it is
what `mSchedulable_iff_card_running_le` needs, and `Sorted.lean` §7 needs it too.
-/

namespace FFJ

variable {I : FFJ} {p : ℕ}

/-! ## 1. Adding the new job -/

/-- **The greedy's first step.** If job `j` starts no earlier than every job of the feasible
set `Z`, there is room to preprocess one more job before `sⱼ`, and fewer than `m` jobs of
`Z` are running at `sⱼ`, then `Z ∪ {j}` is feasible. -/
theorem feasible_insert_of_uniform (hp : ∀ i, I.p i = p) (hq : ∀ i, 0 < I.q i)
    {Z : Finset I.Job} {j : I.Job} (hjZ : j ∉ Z) (hfeas : I.Feasible Z)
    (hlast : ∀ i ∈ Z, I.s i ≤ I.s j)
    (hcount : ((Z.card : ℤ) + 1) * p ≤ I.s j)
    (hroom : (I.running Z (I.s j)).card < I.numMachines) :
    I.Feasible (insert j Z) := by
  classical
  obtain ⟨hpre, hsch⟩ := (I.feasible_iff Z).mp hfeas
  refine (I.feasible_iff _).mpr ⟨?_, ?_⟩
  · -- Condition 1
    rw [preprocessable_of_uniform I hp] at hpre ⊢
    intro j' hj'
    rw [Finset.filter_insert]
    rcases Finset.mem_insert.mp hj' with rfl | hj'Z
    · -- at `j` itself the prefix is all of `Z ∪ {j}`
      have hall : Z.filter (fun i => I.s i ≤ I.s j') = Z :=
        Finset.filter_true_of_mem hlast
      rw [if_pos le_rfl, hall, Finset.card_insert_of_notMem hjZ]
      push_cast
      exact hcount
    · by_cases hsj : I.s j ≤ I.s j'
      · -- a tie: `j`'s own bound is the strongest one
        have heq : I.s j' = I.s j := le_antisymm (hlast j' hj'Z) hsj
        rw [if_pos hsj]
        have h1 := Finset.card_insert_le j (Z.filter (fun i => I.s i ≤ I.s j'))
        have h2 := Finset.card_filter_le Z (fun i => I.s i ≤ I.s j')
        have hcard : ((insert j (Z.filter (fun i => I.s i ≤ I.s j'))).card : ℤ)
            ≤ (Z.card : ℤ) + 1 := by exact_mod_cast by omega
        calc ((insert j (Z.filter (fun i => I.s i ≤ I.s j'))).card : ℤ) * p
            ≤ ((Z.card : ℤ) + 1) * p :=
              Int.mul_le_mul_of_nonneg_right hcard (Int.natCast_nonneg p)
          _ ≤ I.s j := hcount
          _ = I.s j' := heq.symm
      · rw [if_neg hsj]
        exact hpre j' hj'Z
  · -- Condition 2
    rw [mSchedulable_iff_card_running_le (fun i _ => hq i)]
    have hZle : ∀ t : ℤ, (I.running Z t).card ≤ I.numMachines :=
      (mSchedulable_iff_card_running_le (fun i _ => hq i)).mp hsch
    intro t
    by_cases hja : I.s j ≤ t ∧ t < (I.d j : ℤ)
    · have hrun : I.running (insert j Z) t = insert j (I.running Z t) := by
        unfold running
        rw [Finset.filter_insert, if_pos hja]
      rw [hrun]
      -- everything alive at `t ≥ sⱼ` was already alive at `sⱼ`
      have hsub : I.running Z t ⊆ I.running Z (I.s j) := by
        intro x hx
        obtain ⟨hxZ, hx1, hx2⟩ := mem_running.mp hx
        exact mem_running.mpr ⟨hxZ, hlast x hxZ, by omega⟩
      have h1 := Finset.card_insert_le j (I.running Z t)
      have h2 := Finset.card_le_card hsub
      omega
    · have hrun : I.running (insert j Z) t = I.running Z t := by
        unfold running
        rw [Finset.filter_insert, if_neg hja]
      rw [hrun]
      exact hZle t

/-! ## 2. Swapping out the job of largest due date -/

/-- **The greedy's second step.** If job `j` starts no earlier than every job of the
feasible set `Z`, some `k ∈ Z` has due date at least `dⱼ`, and there is room to preprocess
`|Z|` jobs before `sⱼ`, then `(Z \ {k}) ∪ {j}` is feasible.

Condition 2 is where the choice of `k` matters: at any instant `j` is alive, so is `k`, so
the swap does not raise the load. -/
theorem feasible_swap_of_uniform (hp : ∀ i, I.p i = p) (hq : ∀ i, 0 < I.q i)
    {Z : Finset I.Job} {j k : I.Job} (hjZ : j ∉ Z) (hk : k ∈ Z)
    (hfeas : I.Feasible Z) (hlast : ∀ i ∈ Z, I.s i ≤ I.s j)
    (hdk : (I.d j : ℤ) ≤ (I.d k : ℤ))
    (hcount : (Z.card : ℤ) * p ≤ I.s j) :
    I.Feasible (insert j (Z.erase k)) := by
  classical
  obtain ⟨hpre, hsch⟩ := (I.feasible_iff Z).mp hfeas
  have hpre' : I.Preprocessable (Z.erase k) :=
    Preprocessable.subset (h := hpre) (hsub := Finset.erase_subset _ _)
  have hjZ' : j ∉ Z.erase k := fun hc => hjZ (Finset.mem_of_mem_erase hc)
  have hlast' : ∀ i ∈ Z.erase k, I.s i ≤ I.s j :=
    fun i hi => hlast i (Finset.mem_of_mem_erase hi)
  have hcard' : (Z.erase k).card + 1 = Z.card := by
    rw [Finset.card_erase_of_mem hk]
    have := Finset.card_pos.mpr ⟨k, hk⟩
    omega
  refine (I.feasible_iff _).mpr ⟨?_, ?_⟩
  · -- Condition 1: the swap keeps the cardinality, and `j` is the binding index
    rw [preprocessable_of_uniform I hp] at hpre' ⊢
    intro j' hj'
    rw [Finset.filter_insert]
    rcases Finset.mem_insert.mp hj' with rfl | hj'Z
    · have hall : (Z.erase k).filter (fun i => I.s i ≤ I.s j') = Z.erase k :=
        Finset.filter_true_of_mem hlast'
      rw [if_pos le_rfl, hall, Finset.card_insert_of_notMem hjZ', hcard']
      exact hcount
    · by_cases hsj : I.s j ≤ I.s j'
      · have heq : I.s j' = I.s j := le_antisymm (hlast' j' hj'Z) hsj
        rw [if_pos hsj]
        have h1 := Finset.card_insert_le j ((Z.erase k).filter (fun i => I.s i ≤ I.s j'))
        have h2 := Finset.card_filter_le (Z.erase k) (fun i => I.s i ≤ I.s j')
        have hcard : ((insert j ((Z.erase k).filter (fun i => I.s i ≤ I.s j'))).card : ℤ)
            ≤ (Z.card : ℤ) := by exact_mod_cast by omega
        calc ((insert j ((Z.erase k).filter (fun i => I.s i ≤ I.s j'))).card : ℤ) * p
            ≤ (Z.card : ℤ) * p :=
              Int.mul_le_mul_of_nonneg_right hcard (Int.natCast_nonneg p)
          _ ≤ I.s j := hcount
          _ = I.s j' := heq.symm
      · rw [if_neg hsj]
        exact hpre' j' hj'Z
  · -- Condition 2: whenever `j` is alive, so was `k`
    rw [mSchedulable_iff_card_running_le (fun i _ => hq i)]
    have hZle : ∀ t : ℤ, (I.running Z t).card ≤ I.numMachines :=
      (mSchedulable_iff_card_running_le (fun i _ => hq i)).mp hsch
    intro t
    by_cases hja : I.s j ≤ t ∧ t < (I.d j : ℤ)
    · have hkrun : k ∈ I.running Z t :=
        mem_running.mpr ⟨hk, le_trans (hlast k hk) hja.1, by omega⟩
      have hrun : I.running (insert j (Z.erase k)) t
          = insert j ((I.running Z t).erase k) := by
        unfold running
        rw [Finset.filter_insert, if_pos hja]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      rw [hrun]
      have h1 := Finset.card_insert_le j ((I.running Z t).erase k)
      have h2 := Finset.card_erase_of_mem hkrun
      have h3 := hZle t
      have h4 := Finset.card_pos.mpr ⟨k, hkrun⟩
      omega
    · have hrun : I.running (insert j (Z.erase k)) t = I.running (Z.erase k) t := by
        unfold running
        rw [Finset.filter_insert, if_neg hja]
      rw [hrun]
      exact le_trans (Finset.card_le_card (running_subset (Finset.erase_subset _ _) t))
        (hZle t)

/-! ## 3. The domination order

Section 6.1 compares feasible solutions by *domination*: `S` dominates `S'` when `|S| > |S'|`,
or `|S| = |S'|` and the `i`-th largest due date in `S` is no greater than the `i`-th largest
in `S'`.

**That order is too weak to carry Lemma 4's own induction.** Its first disjunct discards all
due-date information whenever the cardinalities differ, and case 2/3 needs it: with
`A = S_{j-1}`, `Sⱼ = (A ∪ {j}) \ {k}`, and a feasible `S'` containing `j` with `|S'| = |A|`,
the set `A' = S' \ {j}` has `|A'| = |A| − 1`, so the induction hypothesis "`A` dominates `A'`"
says only that `A` is larger — and "the job removed is the one with the largest due date" has
nothing to act on.

Dropping the disjunct repairs it. Counting due dates below each threshold,

`SDom S S' := ∀ t, #{i ∈ S' : dᵢ ≤ t} ≤ #{i ∈ S : dᵢ ≤ t}`,

is *exactly* the paper's pointwise condition when the cardinalities agree, and it implies
`|S'| ≤ |S|`, so it is strictly stronger. It is also what the induction actually preserves,
and every step below is arithmetic on `dueCount` rather than on sorted lists. Nothing the
paper claims is false — the lemma holds in this stronger form; it is the proof that needs the
stronger invariant. -/

variable (I) in
/-- How many jobs of `Z` are due by time `t`. -/
def dueCount (Z : Finset I.Job) (t : ℤ) : ℕ := (Z.filter (fun i => (I.d i : ℤ) ≤ t)).card

variable (I) in
/-- **Domination.** `S` dominates `S'` when, below every threshold, `S'` has no more due
dates than `S`. See the section doc for why this is the paper's order with its cardinality
disjunct dropped. -/
def SDom (S S' : Finset I.Job) : Prop := ∀ t : ℤ, I.dueCount S' t ≤ I.dueCount S t

lemma dueCount_le_card (Z : Finset I.Job) (t : ℤ) : I.dueCount Z t ≤ Z.card :=
  Finset.card_filter_le _ _

lemma dueCount_mono {Z Z' : Finset I.Job} (h : Z' ⊆ Z) (t : ℤ) :
    I.dueCount Z' t ≤ I.dueCount Z t :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma dueCount_eq_card {Z : Finset I.Job} {t : ℤ} (h : ∀ i ∈ Z, (I.d i : ℤ) ≤ t) :
    I.dueCount Z t = Z.card := by
  rw [dueCount, Finset.filter_true_of_mem h]

lemma dueCount_insert {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) (t : ℤ) :
    I.dueCount (insert j Z) t
      = I.dueCount Z t + (if (I.d j : ℤ) ≤ t then 1 else 0) := by
  classical
  rw [dueCount, dueCount, Finset.filter_insert]
  by_cases h : (I.d j : ℤ) ≤ t
  · rw [if_pos h, if_pos h,
      Finset.card_insert_of_notMem (fun hc => hj (Finset.mem_filter.mp hc).1)]
  · rw [if_neg h, if_neg h]
    omega

lemma dueCount_erase {Z : Finset I.Job} {k : I.Job} (hk : k ∈ Z) (t : ℤ) :
    I.dueCount (Z.erase k) t + (if (I.d k : ℤ) ≤ t then 1 else 0) = I.dueCount Z t := by
  classical
  have h : (Z.erase k).filter (fun i => (I.d i : ℤ) ≤ t)
      = (Z.filter (fun i => (I.d i : ℤ) ≤ t)).erase k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [dueCount, dueCount, h]
  by_cases hd : (I.d k : ℤ) ≤ t
  · have hmem : k ∈ Z.filter (fun i => (I.d i : ℤ) ≤ t) := Finset.mem_filter.mpr ⟨hk, hd⟩
    rw [if_pos hd, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.mpr ⟨k, hmem⟩
    omega
  · have hnm : k ∉ Z.filter (fun i => (I.d i : ℤ) ≤ t) :=
      fun hc => hd (Finset.mem_filter.mp hc).2
    rw [if_neg hd, Finset.erase_eq_of_notMem hnm]
    omega

/-- Splitting off `j` can only lose due dates. -/
lemma dueCount_le_erase (S : Finset I.Job) (j : I.Job) (t : ℤ) :
    I.dueCount S t ≤ I.dueCount (S.erase j) t + (if (I.d j : ℤ) ≤ t then 1 else 0) := by
  classical
  have hsub : S ⊆ insert j (S.erase j) := by
    intro x hx
    by_cases hxj : x = j
    · exact Finset.mem_insert.mpr (Or.inl hxj)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxj, hx⟩)
  have h := dueCount_mono hsub t
  rwa [dueCount_insert (Finset.notMem_erase j S) t] at h

/-- Domination bounds cardinality: read it at a threshold past every due date of `S'`. -/
theorem card_le_of_sdom {S S' : Finset I.Job} (h : I.SDom S S') : S'.card ≤ S.card := by
  have h1 : I.dueCount S' ((S'.sup I.d : ℕ) : ℤ) = S'.card :=
    dueCount_eq_card (fun i hi => by exact_mod_cast Finset.le_sup (f := I.d) hi)
  have h2 := dueCount_le_card S ((S'.sup I.d : ℕ) : ℤ)
  have h3 := h ((S'.sup I.d : ℕ) : ℤ)
  omega

/-- **Running at `sⱼ` is "not yet due".** When every job of `Z` starts by `sⱼ`, the jobs of
`Z` alive at `sⱼ` are exactly those not due by then. -/
lemma card_running_add_dueCount {Z : Finset I.Job} {j : I.Job}
    (hlast : ∀ i ∈ Z, I.s i ≤ I.s j) :
    (I.running Z (I.s j)).card + I.dueCount Z (I.s j) = Z.card := by
  classical
  have h : I.running Z (I.s j) = Z.filter (fun i => ¬ ((I.d i : ℤ) ≤ I.s j)) := by
    ext x
    simp only [running, Finset.mem_filter, not_le]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hlast x hx.1, hx.2⟩⟩
  rw [h, dueCount, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-! ## 4. Why neither stopping rule leaves room for a bigger solution

Both branches of Lemma 4's case 2/3 open by showing that no feasible solution for
`{1, …, j}` beats `|S_{j−1}|`. Each stopping rule gives this for its own reason. -/

/-- **Rule 1 caps the cardinality.** If there is no room to preprocess `|A| + 1` jobs before
`sⱼ`, then no feasible set whose jobs all start by `sⱼ` has more than `|A|` jobs — read
Condition 1 at the latest-starting job of that set. -/
theorem card_le_of_rule1 {p : ℕ} (hp : ∀ i, I.p i = p) {A S' : Finset I.Job} {j : I.Job}
    (hS' : I.Preprocessable S') (hlast : ∀ i ∈ S', I.s i ≤ I.s j)
    (hrule : I.s j < ((A.card : ℤ) + 1) * p) : S'.card ≤ A.card := by
  classical
  rcases S'.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨j'', hj'', hmax⟩ := S'.exists_max_image I.s hne
  rw [preprocessable_of_uniform I hp] at hS'
  have h1 := hS' j'' hj''
  rw [Finset.filter_true_of_mem hmax] at h1
  by_contra hcon
  have hge : (A.card : ℤ) + 1 ≤ (S'.card : ℤ) := by
    have : A.card + 1 ≤ S'.card := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
    exact_mod_cast this
  have h2 : ((A.card : ℤ) + 1) * p ≤ (S'.card : ℤ) * p :=
    Int.mul_le_mul_of_nonneg_right hge (Int.natCast_nonneg p)
  have h3 : I.s j'' ≤ I.s j := hlast j'' hj''
  exact absurd (lt_of_le_of_lt (le_trans (le_trans h2 h1) h3) hrule) (lt_irrefl _)

/-- **Rule 2 caps the cardinality.** If `m` jobs of `A` are running at `sⱼ`, no feasible set
whose jobs all start by `sⱼ` beats `|A|`: a strictly larger one would have to match `|A|`
after dropping `j`, hence — by domination — still carry `m` jobs across `sⱼ`, and job `j`
itself would make `m + 1`. -/
theorem card_le_of_rule2 (hq : ∀ i, 0 < I.q i) {A S' : Finset I.Job} {j : I.Job}
    (hAlast : ∀ i ∈ A, I.s i ≤ I.s j) (hS'last : ∀ i ∈ S'.erase j, I.s i ≤ I.s j)
    (hdom : I.SDom A (S'.erase j)) (hS'sch : I.MSchedulable S')
    (hrule : I.numMachines ≤ (I.running A (I.s j)).card) : S'.card ≤ A.card := by
  classical
  by_contra hc
  have hlt : A.card < S'.card := Nat.lt_of_not_le hc
  have hA'le : (S'.erase j).card ≤ A.card := card_le_of_sdom hdom
  have hjS' : j ∈ S' := by
    by_contra hj
    rw [Finset.erase_eq_of_notMem hj] at hA'le
    omega
  have hA'card : (S'.erase j).card = A.card := by
    have := Finset.card_erase_of_mem hjS'
    have := Finset.card_pos.mpr ⟨j, hjS'⟩
    omega
  have hAeq := card_running_add_dueCount hAlast
  have hA'eq := card_running_add_dueCount hS'last
  have hdc := hdom (I.s j)
  -- job `j` joins the `m` jobs already running at `sⱼ`
  have hjrun : j ∈ I.running S' (I.s j) := self_mem_running hjS' (hq j)
  have hsub : I.running (S'.erase j) (I.s j) ⊆ I.running S' (I.s j) :=
    running_subset (Finset.erase_subset _ _) _
  have hjnot : j ∉ I.running (S'.erase j) (I.s j) := fun hcc =>
    (Finset.mem_erase.mp (mem_running.mp hcc).1).1 rfl
  have hbig : (insert j (I.running (S'.erase j) (I.s j))).card ≤ (I.running S' (I.s j)).card :=
    Finset.card_le_card (Finset.insert_subset hjrun hsub)
  rw [Finset.card_insert_of_notMem hjnot] at hbig
  have hm := card_running_le_of_mSchedulable hS'sch (I.s j)
  omega

/-! ## 5. Lemma 4's two induction steps -/

/-- **Case 1.** When neither rule fires and job `j` simply joins, domination is inherited:
`j` contributes the same due date to both sides. No cardinality argument is involved. -/
theorem sdom_insert {A S' : Finset I.Job} {j : I.Job} (hjA : j ∉ A)
    (h : I.SDom A (S'.erase j)) : I.SDom (insert j A) S' := by
  intro t
  have h1 := dueCount_le_erase S' j t
  have h2 := dueCount_insert hjA (Z := A) t
  have h3 := h t
  omega

/-- **Cases 2 and 3.** When a rule fires, `Sⱼ` is `A ∪ {j}` with the largest due date `k`
removed. Below `d_k` the swap only helps, since `dⱼ ≤ d_k`; at or above `d_k` every job of
`A` is already counted, so `Sⱼ` reaches `|A|`, which caps `S'`. -/
theorem sdom_swap {A S' : Finset I.Job} {j k : I.Job} (hjA : j ∉ A) (hk : k ∈ A)
    (hkmax : ∀ i ∈ A, (I.d i : ℤ) ≤ (I.d k : ℤ)) (hdjk : (I.d j : ℤ) ≤ (I.d k : ℤ))
    (hcard : S'.card ≤ A.card) (h : I.SDom A (S'.erase j)) :
    I.SDom (insert j (A.erase k)) S' := by
  intro t
  have hjA' : j ∉ A.erase k := fun hcc => hjA (Finset.mem_of_mem_erase hcc)
  have hIns := dueCount_insert hjA' (Z := A.erase k) t
  have hEr := dueCount_erase hk t
  by_cases hkt : (I.d k : ℤ) ≤ t
  · -- every due date of `A ∪ {j}` is already past, so the swap costs nothing
    have hjt : (I.d j : ℤ) ≤ t := le_trans hdjk hkt
    have haA : I.dueCount A t = A.card := dueCount_eq_card (fun i hi => le_trans (hkmax i hi) hkt)
    have h3 := dueCount_le_card S' t
    rw [if_pos hkt] at hEr
    rw [if_pos hjt] at hIns
    omega
  · -- `k` is not counted on either side; domination transfers directly
    have h1 := dueCount_le_erase S' j t
    have h3 := h t
    rw [if_neg hkt] at hEr
    omega

/-- **Condition 1 read at the last job.** A nonempty feasible set whose jobs all start by
`sⱼ` needs `|A|·p` time before `sⱼ`. This is what licenses the swap step. -/
theorem card_mul_le_of_feasible {p : ℕ} (hp : ∀ i, I.p i = p) {A : Finset I.Job} {j : I.Job}
    (hA : I.Preprocessable A) (hlast : ∀ i ∈ A, I.s i ≤ I.s j) (hne : A.Nonempty) :
    (A.card : ℤ) * p ≤ I.s j := by
  classical
  obtain ⟨j'', hj'', hmax⟩ := A.exists_max_image I.s hne
  rw [preprocessable_of_uniform I hp] at hA
  have h1 := hA j'' hj''
  rw [Finset.filter_true_of_mem hmax] at h1
  exact le_trans h1 (hlast j'' hj'')

/-- **The degenerate swap.** When the largest due date of `A ∪ {j}` is `dⱼ` itself, the
greedy drops `j` and keeps `A` — and `A` still dominates. -/
theorem sdom_drop {A S' : Finset I.Job} {j : I.Job}
    (hjmax : ∀ i ∈ A, (I.d i : ℤ) ≤ (I.d j : ℤ))
    (hcard : S'.card ≤ A.card) (h : I.SDom A (S'.erase j)) : I.SDom A S' := by
  intro t
  by_cases hjt : (I.d j : ℤ) ≤ t
  · have haA : I.dueCount A t = A.card := dueCount_eq_card (fun i hi => le_trans (hjmax i hi) hjt)
    have h3 := dueCount_le_card S' t
    omega
  · have h1 := dueCount_le_erase S' j t
    have h3 := h t
    rw [if_neg hjt] at h1
    omega

end FFJ

end Lax496464Proofs
