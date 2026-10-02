import Lax496464Proofs.Model.Section2
import Lax496464Proofs.Model.IntervalColoring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.Hall.Finite

namespace Lax496464Proofs

/-!
# Section 3: Jobs in EST Order, and the State Space of the Dynamic Program

Sections 3 to 6 of the paper all begin from the same standing assumption — *"we will assume
henceforth that the input set of jobs `J` is sorted by the EST order, so that
`s₁ ≤ ⋯ ≤ sₙ`"* — and the dynamic program of Section 3 is indexed by *subsets of at most
`m` jobs*. This file supplies both: `EstFFJ`, an instance whose jobs are `Fin n` already in
EST order, and `CompatibleWith`, the relation the table's first index means.

## What "Compatible with `X`" Says, and How It Is Written Here

The paper takes `X = {x₁ < ⋯ < x_{|X|}}` and calls a schedule *compatible with `X`* when
only jobs from `{x_i, …, n}` run on machine `i`, and machines `|X|+1, …, m` run nothing.
Formalizing that literally needs `X`'s elements enumerated in increasing order, and every
statement then carries an index-arithmetic obligation.

`CompatibleWith` says the same thing without an enumeration: **name each machine by its own
threshold**. A schedule assigns every selected job an element `mach j ∈ X` with
`mach j ≤ j`, and jobs sharing a threshold must not conflict. Since `X` is a set, naming
machines by thresholds is a bijection onto the machines actually used, "machine `i` runs
only jobs `≥ xᵢ`" becomes `mach j ≤ j`, and "nothing runs on the surplus machines" is
automatic — no machine outside `X` exists to run anything.

`mSchedulable_iff_exists_compatible` is the theorem that justifies the DP's state space:
scheduling `Z` on `m` machines at all is the same as being compatible with *some* `X` of at
most `m` jobs. Left to right takes each used machine's earliest job as its threshold; right
to left ranks `X` (`FlexFlowJIT.rank`) to turn thresholds back into machine numbers.
-/


namespace FlexFlowJIT

/-! ## 1. Instances with their jobs in EST order -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An `FF(1,m)` instance whose jobs are `Fin n`, indexed in Early Start Time order. -/
structure EstFFJ where
  /-- `n`, the number of jobs. -/
  n : ℕ
  /-- `m`, the number of second-stage machines. -/
  numMachines : ℕ
  /-- First-stage processing times. -/
  p : Fin n → ℕ
  /-- Second-stage processing times. -/
  q : Fin n → ℕ
  /-- Due dates. -/
  d : Fin n → ℕ
  /-- Weights. -/
  w : Fin n → ℕ
  /-- The jobs are sorted: `s₁ ≤ ⋯ ≤ sₙ`. -/
  est : ∀ i j : Fin n, i ≤ j → (d i : ℤ) - q i ≤ (d j : ℤ) - q j

namespace EstFFJ

/-- The underlying shop, so that every result of `Section2.lean` and
`IntervalColoring.lean` applies unchanged. -/
def toFFJ (E : EstFFJ) : FFJ where
  Job := Fin E.n
  jobFintype := inferInstance
  jobDecEq := inferInstance
  numMachines := E.numMachines
  p := E.p
  q := E.q
  d := E.d
  w := E.w

variable (E : EstFFJ)

@[simp] lemma toFFJ_Job : E.toFFJ.Job = Fin E.n := rfl

/-- The start time `sⱼ = dⱼ − qⱼ`, written at the index type `Fin n`. Everything in this
file uses this rather than `E.toFFJ.s`: the two are definitionally equal, but the latter is
stated at `E.toFFJ.Job`, and instance search does not see through that to find
`LinearOrder (Fin n)` or the decidability of a comparison. -/
def st (i : Fin E.n) : ℤ := (E.d i : ℤ) - E.q i

lemma st_mono {i j : Fin E.n} (h : i ≤ j) : E.st i ≤ E.st j := E.est i j h

/-- Total weight, at the index type — same reason as `st`. -/
def wt (Z : Finset (Fin E.n)) : ℕ := ∑ x ∈ Z, E.w x

@[simp] lemma wt_eq (Z : Finset (Fin E.n)) : E.wt Z = E.toFFJ.weight Z := rfl

/-- The index order really is the EST order. -/
lemma s_mono {i j : Fin E.n} (h : i ≤ j) : E.toFFJ.s i ≤ E.toFFJ.s j := E.est i j h

/-! ## 2. Compatibility with a set of thresholds -/

/-- `Z` **is compatible with `X`**: it can be scheduled with every job assigned a threshold
in `X` that does not exceed it, no two conflicting jobs sharing a threshold.

See the module doc for why this is the paper's condition with the enumeration removed. -/
def CompatibleWith (X Z : Finset (Fin E.n)) : Prop :=
  ∃ mach : Fin E.n → Fin E.n,
    (∀ j ∈ Z, mach j ∈ X) ∧ (∀ j ∈ Z, mach j ≤ j) ∧
      ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → mach i = mach j → ¬ E.toFFJ.Conflict i j

variable {E}

/-- Compatibility with a small `X` is a way of being schedulable on `m` machines. -/
theorem mSchedulable_of_compatible {X Z : Finset (Fin E.n)} (hX : X.card ≤ E.numMachines)
    (h : E.CompatibleWith X Z) : E.toFFJ.MSchedulable Z := by
  obtain ⟨mach, hmem, -, hindep⟩ := h
  refine ⟨fun j => rank X (mach j), fun j hj => ?_, fun i hi j hj hne heq => ?_⟩
  · exact lt_of_lt_of_le (rank_lt (hmem j hj)) hX
  · exact hindep i hi j hj hne (rank_injOn (hmem i hi) (hmem j hj) heq)

/-- ... and conversely, every schedule on `m` machines is compatible with the set of its
machines' earliest jobs, which has at most `m` elements. -/
theorem exists_compatible_of_mSchedulable {Z : Finset (Fin E.n)}
    (h : E.toFFJ.MSchedulable Z) :
    ∃ X : Finset (Fin E.n), X.card ≤ E.numMachines ∧ E.CompatibleWith X Z := by
  -- read the machine assignment at the index type, so instances resolve
  have h' : ∃ c : Fin E.n → ℕ, (∀ j ∈ Z, c j < E.numMachines) ∧
      ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ E.toFFJ.Conflict i j := h
  obtain ⟨c, hlt, hindep⟩ := h'
  have hmin : ∀ (s t : Finset (Fin E.n)) (hs : s.Nonempty) (ht : t.Nonempty),
      s = t → s.min' hs = t.min' ht := by
    rintro s t hs ht rfl; rfl
  set fib : Fin E.n → Finset (Fin E.n) :=
    fun j => Z.filter (fun x : Fin E.n => c x = c j) with hfib
  set mach : Fin E.n → Fin E.n :=
    fun j => if hne : (fib j).Nonempty then (fib j).min' hne else j with hmachdef
  have hne : ∀ j ∈ Z, (fib j).Nonempty :=
    fun j hj => ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
  have hmem : ∀ j ∈ Z, mach j ∈ fib j := by
    intro j hj
    rw [hmachdef]
    simp only [dif_pos (hne j hj)]
    exact Finset.min'_mem _ _
  have hle : ∀ j ∈ Z, mach j ≤ j := by
    intro j hj
    rw [hmachdef]
    simp only [dif_pos (hne j hj)]
    have hjmem : j ∈ fib j := Finset.mem_filter.mpr ⟨hj, rfl⟩
    exact Finset.min'_le _ _ hjmem
  have hcmach : ∀ j ∈ Z, c (mach j) = c j := fun j hj => (Finset.mem_filter.mp (hmem j hj)).2
  -- two jobs share a threshold exactly when they share a machine
  have hsame : ∀ i ∈ Z, ∀ j ∈ Z, mach i = mach j → c i = c j := by
    intro i hi j hj heq
    rw [← hcmach i hi, ← hcmach j hj, heq]
  have hback : ∀ i ∈ Z, ∀ j ∈ Z, c i = c j → mach i = mach j := by
    intro i hi j hj heq
    have hfe : fib i = fib j := by rw [hfib]; simp only [heq]
    rw [hmachdef]
    simp only [dif_pos (hne i hi), dif_pos (hne j hj)]
    exact hmin _ _ _ _ hfe
  refine ⟨Z.image mach, ?_, mach, fun j hj => Finset.mem_image_of_mem _ hj, hle,
    fun i hi j hj hij heq => hindep i hi j hj hij (hsame i hi j hj heq)⟩
  -- the thresholds are as few as the machines
  have hcard : (Z.image mach).card ≤ (Finset.range E.numMachines).card := by
    refine Finset.card_le_card_of_injOn c (fun x hx => ?_) (fun x hx y hy heq => ?_)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hlt _ (Finset.mem_filter.mp (hmem j hj)).1)
    · simp only [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      rw [hcmach i hi, hcmach j hj] at heq
      exact hback i hi j hj heq
  simpa using hcard

/-! ## 3. Preprocessing from a given start time

Section 3's table records, for each `(X, W')`, the largest `P'` such that some solution can
be *preprocessed starting at `P'`* — the paper's
`P' + ∑_{i ∈ Z, i ≤ j} pᵢ ≤ sⱼ`, summing over an **index prefix**.

`Defs.lean`'s `Preprocessable` instead sums over `{i ∈ Z : sᵢ ≤ sⱼ}`, ties included, because
that is the condition `feasible_iff` proves equivalent to an actual schedule. The two are
*not* the same sum — with `sᵢ = sⱼ` and `i > j` the index prefix omits `i` — so the bridge
below is not a triviality. It holds because both are quantified over **every** `j ∈ Z`: the
binding index prefix is the one ending at the *last* job tied with `j`, and there the prefix
has caught up with the tie-inclusive set. `preprocessable_iff_from_zero` is that argument,
and it is what lets Section 3's formulation and Section 2's characterization be used
interchangeably. -/

variable (E)

/-- `Z` can be preprocessed starting at `P` — the paper's index-prefix form. -/
def PreprocessableFrom (Z : Finset (Fin E.n)) (P : ℤ) : Prop :=
  ∀ j ∈ Z, P + ∑ i ∈ Z.filter (fun i => i ≤ j), (E.p i : ℤ) ≤ E.st j

variable {E}

/-- Starting earlier is easier. -/
lemma PreprocessableFrom.mono {Z : Finset (Fin E.n)} {P P' : ℤ} (hPP : P' ≤ P)
    (h : E.PreprocessableFrom Z P) : E.PreprocessableFrom Z P' :=
  fun j hj => by have := h j hj; omega

/-- `Defs.lean`'s Condition 1, written at the index type. -/
lemma preprocessable_iff_st (Z : Finset (Fin E.n)) :
    E.toFFJ.Preprocessable Z ↔
      ∀ j ∈ Z, ∑ i ∈ Z.filter (fun i => E.st i ≤ E.st j), (E.p i : ℤ) ≤ E.st j := Iff.rfl

/-- **The index prefix and the tie-inclusive set agree, once quantified over all of `Z`.** -/
theorem preprocessable_iff_from_zero (Z : Finset (Fin E.n)) :
    E.toFFJ.Preprocessable Z ↔ E.PreprocessableFrom Z 0 := by
  rw [preprocessable_iff_st]
  constructor
  · -- the prefix is contained in the tie-inclusive set
    intro h j hj
    have hsub : Z.filter (fun i => i ≤ j) ⊆ Z.filter (fun i => E.st i ≤ E.st j) := by
      intro x hx
      obtain ⟨hxZ, hxj⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxZ, E.st_mono hxj⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Int.natCast_nonneg (E.p i))
    have hj' := h j hj
    omega
  · -- the binding prefix is the one ending at the last job tied with `j`
    intro h j hj
    set S : Finset (Fin E.n) := Z.filter (fun i => E.st i ≤ E.st j) with hS
    have hSne : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl⟩⟩
    have htS : S.max' hSne ∈ S := S.max'_mem hSne
    obtain ⟨htZ, hts⟩ := Finset.mem_filter.mp htS
    have hSeq : S = Z.filter (fun i => i ≤ S.max' hSne) := by
      ext x
      simp only [hS, Finset.mem_filter]
      constructor
      · rintro ⟨hxZ, hxs⟩
        exact ⟨hxZ, S.le_max' x (Finset.mem_filter.mpr ⟨hxZ, hxs⟩)⟩
      · rintro ⟨hxZ, hxt⟩
        exact ⟨hxZ, le_trans (E.st_mono hxt) hts⟩
    have hprefix := h (S.max' hSne) htZ
    rw [← hSeq] at hprefix
    omega

variable (E)

/-! ## 4. The dynamic programming table, as a predicate

The paper's `T[X, W']` is the largest `P'` for which a solution of weight `W'` compatible
with `X` can be preprocessed starting at `P'`, with `−∞` when there is none and `+∞` at
`W' = 0`. Rather than carry a `WithBot (WithTop ℤ)`, this development records the
*predicate* the table summarizes: `Achievable X W' P'` says that such a solution exists for
this particular `P'`. Since starting earlier is easier (`PreprocessableFrom.mono`), the
predicate is downward closed in `P'` and determines the table entry, and recursion (1)
becomes an equivalence between predicates with no infinities in sight. -/

/-- Some solution of weight exactly `W'`, compatible with `X`, can be preprocessed starting
at `P'`. -/
def Achievable (E : EstFFJ) (X : Finset (Fin E.n)) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset (Fin E.n),
    E.wt Z = W' ∧ E.CompatibleWith X Z ∧ E.PreprocessableFrom Z P'

variable {E}

/-- At the top level: a nonnegative achievable start time is exactly a feasible solution of
that weight. -/
theorem feasible_of_achievable {X : Finset (Fin E.n)} {W' : ℕ} {P' : ℤ}
    (hX : X.card ≤ E.numMachines) (hP : 0 ≤ P') (h : E.Achievable X W' P') :
    ∃ Z : Finset (Fin E.n), E.toFFJ.Feasible Z ∧ E.toFFJ.weight Z = W' := by
  obtain ⟨Z, hw, hc, hp⟩ := h
  exact ⟨Z, (E.toFFJ.feasible_iff Z).mpr
    ⟨(preprocessable_iff_from_zero Z).mpr (hp.mono hP), mSchedulable_of_compatible hX hc⟩,
    (E.wt_eq Z) ▸ hw⟩

/-! ## 5. Recursion (1), soundness

Section 3's recursion decides the fate of `j = min X`, the earliest threshold:

```
T[X, W'] = max { T[X₁, W'],  min(T[X₂, W' − wⱼ], sⱼ) − pⱼ }
```

where `X₁` replaces `j` by the next index not already a threshold (job `j` is *not* taken,
so that machine's earliest possible job moves up by one) and `X₂` replaces `j` by the next
such index whose start time is at or after `dⱼ` (job `j` *is* taken, so that machine is
busy until `dⱼ`).

In the predicate form of §4 the recursion reads: `P'` is achievable for `(X, W')` iff it is
achievable for `(X₁, W')`, or `P' + pⱼ` is achievable for `(X₂, W' − wⱼ)` and fits before
`sⱼ`. **This section proves the `←` half** — every branch really does produce an achievable
solution, so the recursion never overshoots. The `→` half — that the recursion misses
nothing — is §7 below.

The two branches are stated against `X₁` and `X₂` abstractly — all that is used of them is
that each is `X.erase j` plus **at most one** new threshold, lying above `j` (and, for `X₂`,
at or after `dⱼ`). Both `(X \ {j}) ∪ {j₁}` and `X \ {j}` instantiate the first, and likewise
for the second; that the recursion's own `j₁`, `j₂` satisfy these is immediate from their
definitions as minima over `J \ X`. Keeping them abstract avoids carrying an existence
hypothesis for `j₁`/`j₂` through the proof. -/

/-- **Lowering thresholds is always safe.** If each threshold of `X'` can be sent to a
*distinct* threshold of `X` that is no larger, then compatibility transfers from `X'` to
`X`: relabel each job's threshold along the map. Injectivity is what stops two machines
being merged into one.

This is the workhorse behind branch 1 below, and it subsumes the obvious monotonicity
`X ⊆ X' → CompatibleWith X' Z → CompatibleWith X Z`... in the direction that matters:
*fewer or lower* thresholds are harder to satisfy, so a solution for the harder `X'`
serves for the easier `X`. -/
theorem compatible_of_relabel {X X' Z : Finset (Fin E.n)} (f : Fin E.n → Fin E.n)
    (hf : ∀ y ∈ X', f y ∈ X) (hinj : ∀ y ∈ X', ∀ y' ∈ X', f y = f y' → y = y')
    (hle : ∀ y ∈ X', f y ≤ y) (h : E.CompatibleWith X' Z) : E.CompatibleWith X Z := by
  obtain ⟨mach, hmem, hlem, hindep⟩ := h
  exact ⟨fun x => f (mach x), fun z hz => hf _ (hmem z hz),
    fun z hz => le_trans (hle _ (hmem z hz)) (hlem z hz),
    fun a ha b hb hab heq =>
      hindep a ha b hb hab (hinj _ (hmem a ha) _ (hmem b hb) heq)⟩

/-- **Branch 1: job `j` is not taken.** A solution compatible with `X₁` is compatible with
`X` — the jobs on the new threshold move down onto `j`, which is free. -/
theorem achievable_of_branch_not_taken {X X₁ : Finset (Fin E.n)} {j y₁ : Fin E.n}
    {W' : ℕ} {P' : ℤ} (hjX : j ∈ X) (hy₁ : j ≤ y₁)
    (hX₁ : X₁ ⊆ insert y₁ (X.erase j)) (h : E.Achievable X₁ W' P') :
    E.Achievable X W' P' := by
  classical
  obtain ⟨Z, hw, hc, hp⟩ := h
  -- send the one new threshold down to `j`, and keep the rest of `X`
  have hj₁ : j ∈ X₁ → j = y₁ := by
    intro hjm
    rcases Finset.mem_insert.mp (hX₁ hjm) with h1 | h1
    · exact h1
    · exact absurd (Finset.mem_erase.mp h1).1 (by simp)
  refine ⟨Z, hw, compatible_of_relabel (fun v => if v = y₁ then j else v) ?_ ?_ ?_ hc, hp⟩
  · intro y hy
    by_cases hyy : y = y₁
    · simpa [hyy] using hjX
    · simp only [if_neg hyy]
      rcases Finset.mem_insert.mp (hX₁ hy) with h1 | h1
      · exact absurd h1 hyy
      · exact Finset.mem_of_mem_erase h1
  · intro y hy y' hy' heq
    by_cases hyy : y = y₁ <;> by_cases hyy' : y' = y₁
    · rw [hyy, hyy']
    · simp only [if_pos hyy, if_neg hyy'] at heq
      exact absurd (heq.symm.trans (hj₁ (heq ▸ hy'))) hyy'
    · simp only [if_neg hyy, if_pos hyy'] at heq
      exact absurd (heq.trans (hj₁ (heq ▸ hy))) hyy
    · simpa [hyy, hyy'] using heq
  · intro y hy
    by_cases hyy : y = y₁
    · simpa [hyy] using hyy ▸ hy₁
    · simp [hyy]

/-- **Branch 2: job `j` is taken.** A solution compatible with `X₂` that starts late enough
gains job `j` on machine `j`: the jobs on the new threshold begin at or after `dⱼ`, so they
follow `j` on that machine without conflict. -/
theorem achievable_of_branch_taken {X X₂ : Finset (Fin E.n)} {j y₂ : Fin E.n}
    {W' W'' : ℕ} {P' : ℤ} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x)
    (hy₂ : y₂ ∈ X₂ → j < y₂ ∧ (E.d j : ℤ) ≤ E.st y₂)
    (hX₂ : X₂ ⊆ insert y₂ (X.erase j)) (hW : W'' + E.w j = W')
    (hfit : P' + E.p j ≤ E.st j) (h : E.Achievable X₂ W'' (P' + E.p j)) :
    E.Achievable X W' P' := by
  classical
  obtain ⟨Z, hw, ⟨mach, hmem, hle, hindep⟩, hp⟩ := h
  -- every threshold of `X₂` lies strictly above `j`, so `j ∉ Z` and all of `Z` is above `j`
  have habove : ∀ y ∈ X₂, j < y := by
    intro y hy
    rcases Finset.mem_insert.mp (hX₂ hy) with h1 | h1
    · subst h1
      exact (hy₂ hy).1
    · obtain ⟨hne, hyX⟩ := Finset.mem_erase.mp h1
      exact lt_of_le_of_ne (hjmin y hyX) (Ne.symm hne)
  have hZgt : ∀ z ∈ Z, j < z := fun z hz =>
    lt_of_lt_of_le (habove _ (hmem z hz)) (hle z hz)
  have hjZ : j ∉ Z := fun hc => absurd (hZgt j hc) (lt_irrefl j)
  have hafter : ∀ z ∈ Z, mach z = y₂ → (E.d j : ℤ) ≤ E.st z := fun z hz hy =>
    le_trans (hy₂ (hy ▸ hmem z hz)).2 (E.st_mono (hy ▸ hle z hz))
  have hmachne : ∀ z ∈ Z, ¬ mach z = j := fun z hz hc =>
    absurd (hc ▸ habove _ (hmem z hz)) (lt_irrefl j)
  -- the new assignment: `j` and the former `y₂` jobs share machine `j`
  refine ⟨insert j Z, ?_,
    ⟨fun x => if x ∈ Z then (if mach x = y₂ then j else mach x) else j, ?_, ?_, ?_⟩, ?_⟩
  · have hsum : E.wt (insert j Z) = E.w j + E.wt Z := by
      simp only [wt]
      exact Finset.sum_insert hjZ
    omega
  · intro z hz
    by_cases hzZ : z ∈ Z
    · simp only [if_pos hzZ]
      by_cases hy : mach z = y₂
      · simpa [hy] using hjX
      · simp only [if_neg hy]
        rcases Finset.mem_insert.mp (hX₂ (hmem z hzZ)) with h1 | h1
        · exact absurd h1 hy
        · exact Finset.mem_of_mem_erase h1
    · simpa [hzZ] using hjX
  · intro z hz
    by_cases hzZ : z ∈ Z
    · simp only [if_pos hzZ]
      by_cases hy : mach z = y₂
      · simpa [hy] using le_of_lt (hZgt z hzZ)
      · simpa [hy] using hle z hzZ
    · have hzj : z = j := by
        rcases Finset.mem_insert.mp hz with h1 | h1
        · exact h1
        · exact absurd h1 hzZ
      subst hzj
      simp only [if_neg hzZ]
      exact le_rfl
  · intro a ha b hb hab heq
    by_cases haZ : a ∈ Z <;> by_cases hbZ : b ∈ Z
    · -- both were already scheduled
      simp only [if_pos haZ, if_pos hbZ] at heq
      refine hindep a haZ b hbZ hab ?_
      by_cases hya : mach a = y₂ <;> by_cases hyb : mach b = y₂
      · rw [hya, hyb]
      · simp only [if_pos hya, if_neg hyb] at heq
        exact absurd (heq.symm) (hmachne b hbZ)
      · simp only [if_neg hya, if_pos hyb] at heq
        exact absurd heq (hmachne a haZ)
      · simpa [hya, hyb] using heq
    · -- `b` is the newly added job `j`
      have hbj : b = j := by
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact h1
        · exact absurd h1 hbZ
      simp only [if_pos haZ, if_neg hbZ] at heq
      by_cases hya : mach a = y₂
      · subst hbj
        exact fun hc => E.toFFJ.not_conflict_of_le (hafter a haZ hya)
          (E.toFFJ.conflict_symm hc)
      · simp only [if_neg hya] at heq
        exact absurd heq (hmachne a haZ)
    · have haj : a = j := by
        rcases Finset.mem_insert.mp ha with h1 | h1
        · exact h1
        · exact absurd h1 haZ
      simp only [if_neg haZ, if_pos hbZ] at heq
      by_cases hyb : mach b = y₂
      · subst haj
        exact E.toFFJ.not_conflict_of_le (hafter b hbZ hyb)
      · simp only [if_neg hyb] at heq
        exact absurd heq.symm (hmachne b hbZ)
    · have haj : a = j := by
        rcases Finset.mem_insert.mp ha with h1 | h1
        · exact h1
        · exact absurd h1 haZ
      have hbj : b = j := by
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact h1
        · exact absurd h1 hbZ
      exact absurd (haj.trans hbj.symm) hab
  · -- `j` is the earliest job, so every prefix simply gains `pⱼ`
    intro z hz
    by_cases hzZ : z ∈ Z
    · have hfil : (insert j Z).filter (fun i => i ≤ z)
          = insert j (Z.filter (fun i => i ≤ z)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hxZ, hxz⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxZ, hxz⟩
        · rintro (rfl | ⟨hxZ, hxz⟩)
          · exact ⟨Or.inl rfl, le_of_lt (hZgt z hzZ)⟩
          · exact ⟨Or.inr hxZ, hxz⟩
      have hjnot : j ∉ Z.filter (fun i => i ≤ z) := fun hc =>
        hjZ (Finset.mem_filter.mp hc).1
      rw [hfil, Finset.sum_insert hjnot]
      have := hp z hzZ
      omega
    · have hzj : z = j := by
        rcases Finset.mem_insert.mp hz with h1 | h1
        · exact h1
        · exact absurd h1 hzZ
      subst hzj
      have hfil : (insert z Z).filter (fun i => i ≤ z) = {z} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hxZ, hxz⟩
          · rfl
          · exact absurd (lt_of_lt_of_le (hZgt x hxZ) hxz) (lt_irrefl z)
        · rintro rfl
          exact ⟨Or.inl rfl, le_rfl⟩
      rw [hfil, Finset.sum_singleton]
      exact hfit

/-! ## 6. The slide

Lemma 1's other half — that the recursion misses nothing — needs the shift the paper
performs on page 655: the whole "low block" of thresholds ending just below the new
threshold `y` slides up one position, `j` drops out, and `y` comes in.

What makes that work is a fact about the machines' earliest jobs alone: they are **distinct
and all above `j`**, so a family of `ℓ` machines whose earliest jobs all fall at or below
some bound `M` cannot outnumber the thresholds of `X₁` below `M`. That is Hall's condition,
and Hall's marriage theorem turns it into the reassignment. -/

/-- **Distinct representatives below a bound.** If `g` is injective on `S`, lands in `X`,
and stays at or below `M`, then `S` is no larger than the part of `X` below `M`. This is
the shape Hall's condition wants. -/
lemma card_le_card_filter_of_injOn {n : ℕ} {S X : Finset (Fin n)} {g : Fin n → Fin n}
    {M : Fin n} (hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b)
    (hmem : ∀ u ∈ S, g u ∈ X) (hle : ∀ u ∈ S, g u ≤ M) :
    S.card ≤ (X.filter (fun y => y ≤ M)).card :=
  Finset.card_le_card_of_injOn g
    (fun u hu => Finset.mem_filter.mpr ⟨hmem u hu, hle u hu⟩)
    (fun a ha b hb h => hinj a (by simpa using ha) b (by simpa using hb) h)

/-! ### The two regimes of `X₁ ∩ [0, M]`

`X₁` is `X` with its least element `j` removed and one new element `y` added, where `y` is
the least index that `X` misses among those at or above a cutoff `t > j` — so `X` contains
the whole block `t, t+1, …, y−1`. (For the branch where job `j` is not selected the cutoff
is `t = j+1`, and the block is `j+1, …, y−1`; for the branch where it *is* selected the
cutoff is the first index whose start time reaches `dⱼ`.)

Counting `X₁` below a bound `M` therefore splits on where `M` sits relative to `y`:

* `y ≤ M`: the machine at `j` can be sent to the new threshold `y` itself, every other
  machine to its own index, and all of these land in `X₁ ∩ [0, M]`.
* `M < y`: split the machines instead by whether their earliest job reaches the cutoff.
  Those below `t` are not the machine at `j` (whose jobs are all at or above `t`), so they
  keep their own index, which lies in `X₁` below `t`. Those at or above `t` are sent to
  their earliest jobs, which lie in the block `[t, M] ⊆ X₁`. The two ranges are disjoint,
  so the counts add. -/

/-- **Hall's condition for `X₁`.** A family `S` of machines — each an index of `X`, each no
later than its own earliest job `mn u`, with those earliest jobs distinct, all above `j`,
and all at or below `M` — fits below `M` in `X₁ = (X \ {j}) ∪ {y}` as well, provided the
machine at `j` has all its jobs at or above the cutoff `t`.

This is the hypothesis Hall's marriage theorem consumes in `compatible_shift`. -/
lemma hall_condition {n : ℕ} {S X : Finset (Fin n)} {mn : Fin n → Fin n} {j y t M : Fin n}
    (hyX : y ∉ X)
    (hyblock : ∀ x : Fin n, t ≤ x → x < y → x ∈ X)
    (hSX : ∀ u ∈ S, u ∈ X) (hSmn : ∀ u ∈ S, u ≤ mn u)
    (hmninj : ∀ a ∈ S, ∀ b ∈ S, mn a = mn b → a = b)
    (hmngt : ∀ u ∈ S, j < mn u) (hmnle : ∀ u ∈ S, mn u ≤ M)
    (hlowt : ∀ u ∈ S, u = j → t ≤ mn u) :
    S.card ≤ ((insert y (X.erase j)).filter (fun x => x ≤ M)).card := by
  classical
  rcases le_or_gt y M with hyM | hMy
  · -- at or above `y`: machine `j` takes the new threshold, everyone else keeps their own
    refine card_le_card_filter_of_injOn (g := fun u => if u = j then y else u) ?_ ?_ ?_
    · intro a ha b hb hab
      by_cases haj : a = j <;> by_cases hbj : b = j
      · rw [haj, hbj]
      · simp only [if_pos haj, if_neg hbj] at hab
        exact absurd (hSX b hb) (hab ▸ hyX)
      · simp only [if_neg haj, if_pos hbj] at hab
        exact absurd (hab ▸ hSX a ha) hyX
      · simpa [haj, hbj] using hab
    · intro u hu
      by_cases huj : u = j
      · simp [huj]
      · simp only [if_neg huj]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨huj, hSX u hu⟩)
    · intro u hu
      by_cases huj : u = j
      · simpa [huj] using hyM
      · simpa [huj] using le_trans (hSmn u hu) (hmnle u hu)
  · -- below `y`: split by whether the machine's earliest job reaches the cutoff
    set A := (insert y (X.erase j)).filter (fun x => x ≤ M) with hA
    have hlow : (S.filter (fun u => mn u < t)).card
        ≤ (A.filter (fun x => x < t)).card := by
      refine Finset.card_le_card_of_injOn id ?_ (fun a _ b _ h => h)
      intro u hu
      obtain ⟨huS, hut⟩ := Finset.mem_filter.mp hu
      have huj : u ≠ j := fun hc => absurd (hlowt u huS hc) (not_le.mpr hut)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨huj, hSX u huS⟩),
            le_trans (hSmn u huS) (hmnle u huS)⟩,
          lt_of_le_of_lt (hSmn u huS) hut⟩
    have hhigh : (S.filter (fun u => ¬ mn u < t)).card
        ≤ (A.filter (fun x => ¬ x < t)).card := by
      refine Finset.card_le_card_of_injOn mn ?_ ?_
      · intro u hu
        obtain ⟨huS, hut⟩ := Finset.mem_filter.mp hu
        have hmnX : mn u ∈ X :=
          hyblock _ (not_lt.mp hut) (lt_of_le_of_lt (hmnle u huS) hMy)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨(hmngt u huS).ne', hmnX⟩), hmnle u huS⟩, hut⟩
      · intro a ha b hb hab
        exact hmninj a (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1 b
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1 hab
    have hS := Finset.card_filter_add_card_filter_not (s := S) (fun u => mn u < t)
    have hAc := Finset.card_filter_add_card_filter_not (s := A) (fun x => x < t)
    omega

/-! ### The slide itself

With Hall's condition in hand, the reassignment is a matching. The machines are the fibres
of `mach`; each has an earliest job `mn u`, and because `j = min X` is unselected these
minima are distinct and all exceed `j`. Feeding `hall_condition` to Mathlib's marriage
theorem produces an injection sending each machine to a threshold of `X₁` below its earliest
job — which is exactly a schedule compatible with `X₁`. -/

/-- **The slide, for any target satisfying Hall's condition.** If `j = min X` is not
selected, every machine's earliest job lies above `j`; any target `Y` that can host each
family of machines below its latest earliest job — Hall's condition, `hY` — receives the
whole schedule. `compatible_shift` and `compatible_erase` are the two targets Lemma 1 uses. -/
theorem compatible_via_hall {X Z Y : Finset (Fin E.n)} {j t : Fin E.n}
    {mach : Fin E.n → Fin E.n} (hmem : ∀ z ∈ Z, mach z ∈ X)
    (hle : ∀ z ∈ Z, mach z ≤ z)
    (hindep : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → mach a = mach b → ¬ E.toFFJ.Conflict a b)
    (hjmin : ∀ x ∈ X, j ≤ x) (hjZ : j ∉ Z) (hhigh : ∀ z ∈ Z, mach z = j → t ≤ z)
    (hY : ∀ (S : Finset (Fin E.n)) (mn : Fin E.n → Fin E.n) (M : Fin E.n),
      (∀ u ∈ S, u ∈ X) → (∀ u ∈ S, u ≤ mn u) →
      (∀ a ∈ S, ∀ b ∈ S, mn a = mn b → a = b) → (∀ u ∈ S, j < mn u) →
      (∀ u ∈ S, mn u ≤ M) → (∀ u ∈ S, u = j → t ≤ mn u) →
      S.card ≤ (Y.filter (fun x => x ≤ M)).card) :
    E.CompatibleWith Y Z := by
  have hZgt : ∀ z ∈ Z, j < z := by
    intro z hz
    refine lt_of_le_of_ne (le_trans (hjmin _ (hmem z hz)) (hle z hz)) ?_
    rintro rfl
    exact hjZ hz
  set U : Finset (Fin E.n) := Z.image mach with hU
  have hUX : ∀ u ∈ U, u ∈ X := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    exact hmem z hz
  set F : Fin E.n → Finset (Fin E.n) := fun u => Z.filter (fun z => mach z = u) with hF
  have hFne : ∀ u ∈ U, (F u).Nonempty := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  set mn : Fin E.n → Fin E.n :=
    fun u => if hne : (F u).Nonempty then (F u).min' hne else u with hmn
  have hmnmem : ∀ u ∈ U, mn u ∈ F u := by
    intro u hu
    rw [hmn]; simp only [dif_pos (hFne u hu)]
    exact Finset.min'_mem _ _
  have hmnmin : ∀ u ∈ U, ∀ z ∈ F u, mn u ≤ z := by
    intro u hu z hz
    rw [hmn]; simp only [dif_pos (hFne u hu)]
    exact Finset.min'_le _ _ hz
  have hmnZ : ∀ u ∈ U, mn u ∈ Z := fun u hu => (Finset.mem_filter.mp (hmnmem u hu)).1
  have hmachmn : ∀ u ∈ U, mach (mn u) = u := fun u hu =>
    (Finset.mem_filter.mp (hmnmem u hu)).2
  have hmninj : ∀ a ∈ U, ∀ b ∈ U, mn a = mn b → a = b := by
    intro a ha b hb hab
    rw [← hmachmn a ha, ← hmachmn b hb, hab]
  have hule : ∀ u ∈ U, u ≤ mn u := by
    intro u hu
    have h1 := hle _ (hmnZ u hu)
    rw [hmachmn u hu] at h1
    exact h1
  have hmnmin' : ∀ u ∈ U, ∀ z ∈ Z, mach z = u → mn u ≤ z := by
    intro u hu z hz hmz
    exact hmnmin u hu z (Finset.mem_filter.mpr ⟨hz, hmz⟩)
  have hmachU : ∀ z ∈ Z, mach z ∈ U := fun z hz => Finset.mem_image_of_mem _ hz
  -- the definitions have served their purpose; make them opaque so that unification in the
  -- Hall application below does not keep unfolding them
  clear_value U F mn
  clear hU hF hmn hFne hmnmem hmnmin
  -- Hall's condition, machine by machine
  have hHall : ∀ s : Finset {u : Fin E.n // u ∈ U},
      s.card ≤ (s.biUnion (fun u =>
        Y.filter (fun x => x ≤ mn u.val))).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    obtain ⟨u₀, hu₀, hmax⟩ := s.exists_max_image (fun u => mn u.val) hs
    refine le_trans ?_ (Finset.card_le_card
      (fun x hx => Finset.mem_biUnion.mpr ⟨u₀, hu₀, hx⟩))
    have hcard : s.card = (s.image (fun u => u.val)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    have hSmem : ∀ u ∈ s.image (fun u : {u : Fin E.n // u ∈ U} => u.val), u ∈ U := by
      intro u hu
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hu
      exact w.2
    have hSle : ∀ u ∈ s.image (fun u : {u : Fin E.n // u ∈ U} => u.val),
        mn u ≤ mn u₀.val := by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      exact hmax w hw
    rw [hcard]
    exact hY _ mn (mn u₀.val)
      (fun u hu => hUX u (hSmem u hu)) (fun u hu => hule u (hSmem u hu))
      (fun a ha b hb hab => hmninj a (hSmem a ha) b (hSmem b hb) hab)
      (fun u hu => hZgt _ (hmnZ u (hSmem u hu))) hSle
      (fun u hu huj => hhigh _ (hmnZ u (hSmem u hu))
        ((hmachmn u (hSmem u hu)).trans huj))
  -- the matching Hall provides is the new schedule
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun u : {u : Fin E.n // u ∈ U} =>
        Y.filter (fun x => x ≤ mn u.val))).mp hHall
  refine ⟨fun z => if hz : mach z ∈ U then f ⟨mach z, hz⟩ else j, ?_, ?_, ?_⟩
  · intro z hz
    simp only [dif_pos (hmachU z hz)]
    exact (Finset.mem_filter.mp (hfmem ⟨mach z, hmachU z hz⟩)).1
  · intro z hz
    simp only [dif_pos (hmachU z hz)]
    refine le_trans (Finset.mem_filter.mp (hfmem ⟨mach z, hmachU z hz⟩)).2 ?_
    exact hmnmin' _ (hmachU z hz) z hz rfl
  · intro a ha b hb hab heq
    simp only [dif_pos (hmachU a ha), dif_pos (hmachU b hb)] at heq
    exact hindep a ha b hb hab (congrArg Subtype.val (hfinj heq))


/-- **The slide.** If `j = min X` is not selected, a schedule compatible with `X` is
compatible with `X₁ = (X \ {j}) ∪ {y}`, where `y` is the least index at or above the cutoff
`t` that `X` misses. This is the geometric content of Lemma 1's completeness direction. -/
theorem compatible_shift {X Z : Finset (Fin E.n)} {j y t : Fin E.n}
    {mach : Fin E.n → Fin E.n} (hmem : ∀ z ∈ Z, mach z ∈ X)
    (hle : ∀ z ∈ Z, mach z ≤ z)
    (hindep : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → mach a = mach b → ¬ E.toFFJ.Conflict a b)
    (hjmin : ∀ x ∈ X, j ≤ x) (hyX : y ∉ X)
    (hyblock : ∀ x : Fin E.n, t ≤ x → x < y → x ∈ X)
    (hjZ : j ∉ Z) (hhigh : ∀ z ∈ Z, mach z = j → t ≤ z) :
    E.CompatibleWith (insert y (X.erase j)) Z :=
  compatible_via_hall hmem hle hindep hjmin hjZ hhigh
    (fun S mn M => hall_condition (S := S) (mn := mn) (M := M) (j := j) hyX hyblock)

/-- **Hall's condition when there is nothing to slide into.** If `X` already contains every
index from the cutoff `t` on, dropping `j` alone leaves room. -/
lemma hall_condition_erase {n : ℕ} {S X : Finset (Fin n)} {mn : Fin n → Fin n}
    {j t M : Fin n} (hblock : ∀ x : Fin n, t ≤ x → x ∈ X)
    (hSX : ∀ u ∈ S, u ∈ X) (hSmn : ∀ u ∈ S, u ≤ mn u)
    (hmninj : ∀ a ∈ S, ∀ b ∈ S, mn a = mn b → a = b)
    (hmngt : ∀ u ∈ S, j < mn u) (hmnle : ∀ u ∈ S, mn u ≤ M)
    (hlowt : ∀ u ∈ S, u = j → t ≤ mn u) :
    S.card ≤ ((X.erase j).filter (fun x => x ≤ M)).card := by
  classical
  set A := (X.erase j).filter (fun x => x ≤ M) with hA
  have hlow : (S.filter (fun u => mn u < t)).card ≤ (A.filter (fun x => x < t)).card := by
    refine Finset.card_le_card_of_injOn id ?_ (fun a _ b _ h => h)
    intro u hu
    obtain ⟨huS, hut⟩ := Finset.mem_filter.mp hu
    have huj : u ≠ j := fun hc => absurd (hlowt u huS hc) (not_le.mpr hut)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huj, hSX u huS⟩,
          le_trans (hSmn u huS) (hmnle u huS)⟩,
        lt_of_le_of_lt (hSmn u huS) hut⟩
  have hhigh : (S.filter (fun u => ¬ mn u < t)).card
      ≤ (A.filter (fun x => ¬ x < t)).card := by
    refine Finset.card_le_card_of_injOn mn ?_ ?_
    · intro u hu
      obtain ⟨huS, hut⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨(hmngt u huS).ne', hblock _ (not_lt.mp hut)⟩,
            hmnle u huS⟩, hut⟩
    · intro a ha b hb hab
      exact hmninj a (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1 b
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1 hab
  have hS := Finset.card_filter_add_card_filter_not (s := S) (fun u => mn u < t)
  have hAc := Finset.card_filter_add_card_filter_not (s := A) (fun x => x < t)
  omega

/-- **The degenerate slide.** If `X` already contains every index from the cutoff `t` on,
a schedule compatible with `X` in which `j` is unselected is compatible with `X \ {j}`. This
covers the paper's cases where `j₁` or `j₂` does not exist. -/
theorem compatible_erase {X Z : Finset (Fin E.n)} {j t : Fin E.n}
    {mach : Fin E.n → Fin E.n} (hmem : ∀ z ∈ Z, mach z ∈ X)
    (hle : ∀ z ∈ Z, mach z ≤ z)
    (hindep : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → mach a = mach b → ¬ E.toFFJ.Conflict a b)
    (hjmin : ∀ x ∈ X, j ≤ x) (hblock : ∀ x : Fin E.n, t ≤ x → x ∈ X)
    (hjZ : j ∉ Z) (hhigh : ∀ z ∈ Z, mach z = j → t ≤ z) :
    E.CompatibleWith (X.erase j) Z :=
  compatible_via_hall hmem hle hindep hjmin hjZ hhigh
    (fun S mn M => hall_condition_erase (S := S) (mn := mn) (M := M) (j := j) hblock)


/-! ## 7. Recursion (1), completeness

The `→` half of Lemma 1: every achievable `(X, W', P')` is *reached* by one of the two
branches, according to whether the earliest threshold's job `j = min X` is selected.

* **Not selected.** Machine `j` is free, so `compatible_shift` slides the low block of
  thresholds up one place and the solution is achievable for `X₁` at the same `P'`.
* **Selected.** Job `j` must sit on machine `j` (it is the only threshold at or below `j`),
  so the rest of `Z` is preprocessed after `pⱼ` and job `j` itself must fit before `sⱼ`.
  Every other job on machine `j` avoids conflicting with `j`, which — since second-stage
  times are positive — puts its start time at or after `dⱼ`; those jobs are therefore at or
  above the cutoff `t`, and `compatible_shift` slides the block up to `y₂`.

Positivity of the second-stage times is the paper's standing assumption on the input and is
carried explicitly as `hq`; it is exactly what rules out zero-length second-stage intervals,
which would conflict with nothing and could sit anywhere on machine `j`. -/

/-- **Completeness, branch 1.** If `j = min X` is not selected, the solution is achievable
for `X₁ = (X \ {j}) ∪ {y₁}`, where `y₁` is the least index above `j` that `X` misses. -/
theorem achievable_branch_not_taken_of {X Z : Finset (Fin E.n)} {j y₁ : Fin E.n}
    {W' : ℕ} {P' : ℤ} (hjmin : ∀ x ∈ X, j ≤ x)
    (hy₁j : j < y₁) (hy₁X : y₁ ∉ X)
    (hy₁block : ∀ x : Fin E.n, j < x → x < y₁ → x ∈ X)
    (hjZ : j ∉ Z) (hw : E.wt Z = W') (hc : E.CompatibleWith X Z)
    (hp : E.PreprocessableFrom Z P') :
    E.Achievable (insert y₁ (X.erase j)) W' P' := by
  obtain ⟨mach, hmem, hle, hindep⟩ := hc
  have hZgt : ∀ z ∈ Z, j < z := by
    intro z hz
    refine lt_of_le_of_ne (le_trans (hjmin _ (hmem z hz)) (hle z hz)) ?_
    rintro rfl
    exact hjZ hz
  -- the cutoff for this branch is `j + 1`: every job of `Z` already lies above `j`
  set t : Fin E.n := ⟨(j : ℕ) + 1, lt_of_le_of_lt (Fin.lt_def.mp hy₁j) y₁.isLt⟩ with ht
  have htx : ∀ x : Fin E.n, t ≤ x ↔ j < x := by
    intro x
    simp only [ht, Fin.le_def, Fin.lt_def]
    omega
  exact ⟨Z, hw, compatible_shift hmem hle hindep hjmin hy₁X
    (fun x hx => hy₁block x ((htx x).mp hx)) hjZ
    (fun z hz _ => (htx z).mpr (hZgt z hz)), hp⟩

/-- **Completeness, branch 2, for any target.** If `j = min X` is selected, job `j` sits
alone at the front of its machine and is preprocessed first, so it fits before `sⱼ`, its
weight is part of the total, and the rest of `Z` is preprocessed `pⱼ` later. Every other job
on machine `j` starts at or after `dⱼ` (second-stage times are positive), which is exactly
what `hslide` needs to move that machine to the recursion's target `Y`. -/
theorem achievable_branch_taken_of_slide {X Z Y : Finset (Fin E.n)} {j : Fin E.n}
    {W' : ℕ} {P' : ℤ} (hq : ∀ i, 0 < E.q i) (hjmin : ∀ x ∈ X, j ≤ x)
    (hjZ : j ∈ Z) (hw : E.wt Z = W') (hc : E.CompatibleWith X Z)
    (hp : E.PreprocessableFrom Z P')
    (hslide : ∀ mach : Fin E.n → Fin E.n, (∀ z ∈ Z.erase j, mach z ∈ X) →
      (∀ z ∈ Z.erase j, mach z ≤ z) →
      (∀ a ∈ Z.erase j, ∀ b ∈ Z.erase j, a ≠ b → mach a = mach b →
        ¬ E.toFFJ.Conflict a b) →
      (∀ z ∈ Z.erase j, mach z = j → (E.d j : ℤ) ≤ E.st z) →
      E.CompatibleWith Y (Z.erase j)) :
    P' + E.p j ≤ E.st j ∧ E.w j ≤ W' ∧ E.Achievable Y (W' - E.w j) (P' + E.p j) := by
  classical
  obtain ⟨mach, hmem, hle, hindep⟩ := hc
  have hjle : ∀ z ∈ Z, j ≤ z := fun z hz => le_trans (hjmin _ (hmem z hz)) (hle z hz)
  -- job `j` sits on machine `j`: no threshold of `X` is below `j`
  have hmachj : mach j = j := le_antisymm (hle j hjZ) (hjmin _ (hmem j hjZ))
  -- the index prefix at `j` is `{j}`
  have hfj : Z.filter (fun i => i ≤ j) = {j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact le_antisymm h.2 (hjle x h.1)
    · rintro rfl
      exact ⟨hjZ, le_rfl⟩
  have hfit : P' + (E.p j : ℤ) ≤ E.st j := by
    have h1 := hp j hjZ
    rw [hfj, Finset.sum_singleton] at h1
    exact h1
  -- weights
  have hwt : E.wt (Z.erase j) + E.w j = W' := by
    rw [← hw]
    exact Finset.sum_erase_add Z _ hjZ
  -- the rest of `Z` is preprocessed after `p j`
  have hp2 : E.PreprocessableFrom (Z.erase j) (P' + E.p j) := by
    intro z hz
    obtain ⟨hzj, hzZ⟩ := Finset.mem_erase.mp hz
    have hfilter : Z.filter (fun i => i ≤ z)
        = insert j ((Z.erase j).filter (fun i => i ≤ z)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hx, hxz⟩
        by_cases hxj : x = j
        · exact Or.inl hxj
        · exact Or.inr ⟨⟨hxj, hx⟩, hxz⟩
      · rintro (rfl | ⟨⟨-, hx⟩, hxz⟩)
        · exact ⟨hjZ, hjle z hzZ⟩
        · exact ⟨hx, hxz⟩
    have hnot : j ∉ (Z.erase j).filter (fun i => i ≤ z) := by simp
    have h1 := hp z hzZ
    rw [hfilter, Finset.sum_insert hnot] at h1
    omega
  -- every other job on machine `j` starts at or after `d j`
  have hhigh : ∀ z ∈ Z.erase j, mach z = j → (E.d j : ℤ) ≤ E.st z := by
    intro z hz hmz
    obtain ⟨hzj, hzZ⟩ := Finset.mem_erase.mp hz
    by_contra hcon
    have hcon' : E.st z < (E.d j : ℤ) := not_le.mp hcon
    have hnc : ¬ E.toFFJ.Conflict j z :=
      hindep j hjZ z hzZ (Ne.symm hzj) (hmachj.trans hmz.symm)
    have hdz : (E.d z : ℤ) ≤ E.st j := by
      by_contra h2
      exact hnc ⟨not_le.mp h2, hcon'⟩
    have hmono : E.st j ≤ E.st z := E.st_mono (hjle z hzZ)
    have hsz : E.st z = (E.d z : ℤ) - (E.q z : ℤ) := rfl
    have hqz := hq z
    omega
  refine ⟨hfit, by omega, Z.erase j, by omega, ?_, hp2⟩
  exact hslide mach (fun z hz => hmem z (Finset.mem_of_mem_erase hz))
    (fun z hz => hle z (Finset.mem_of_mem_erase hz))
    (fun a ha b hb hab => hindep a (Finset.mem_of_mem_erase ha) b
      (Finset.mem_of_mem_erase hb) hab) hhigh

/-! ## 8. Lemma 1, with `X₁` and `X₂` exactly as the paper defines them

The paper defines `j₁ = min{j* ∉ X : j < j*}` and `j₂ = min{j* ∉ X : dⱼ ≤ sⱼ*}`, and sets
`X₁ = (X \ {j}) ∪ {j₁}` if `j₁` exists and `X₁ = X \ {j}` otherwise, likewise `X₂`. The
theorems above take the existing indices as hypotheses; this section defines them and proves
the recursion for all four combinations of existence, which is Lemma 1 as stated. -/

variable (E) in
/-- The paper's `j₁`, when it exists. -/
def j1 (X : Finset (Fin E.n)) (j : Fin E.n) : Option (Fin E.n) :=
  if h : (Finset.univ.filter fun x => x ∉ X ∧ j < x).Nonempty then
    some ((Finset.univ.filter fun x => x ∉ X ∧ j < x).min' h) else none

variable (E) in
/-- The paper's `j₂`, when it exists. -/
def j2 (X : Finset (Fin E.n)) (j : Fin E.n) : Option (Fin E.n) :=
  if h : (Finset.univ.filter fun x => x ∉ X ∧ (E.d j : ℤ) ≤ E.st x).Nonempty then
    some ((Finset.univ.filter fun x => x ∉ X ∧ (E.d j : ℤ) ≤ E.st x).min' h) else none

variable (E) in
/-- The paper's `X₁`. -/
def X1 (X : Finset (Fin E.n)) (j : Fin E.n) : Finset (Fin E.n) :=
  match E.j1 X j with
  | some y => insert y (X.erase j)
  | none => X.erase j

variable (E) in
/-- The paper's `X₂`. -/
def X2 (X : Finset (Fin E.n)) (j : Fin E.n) : Finset (Fin E.n) :=
  match E.j2 X j with
  | some y => insert y (X.erase j)
  | none => X.erase j

lemma compatibleWith_empty (Y : Finset (Fin E.n)) : E.CompatibleWith Y ∅ :=
  ⟨id, fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _),
    fun _ h => absurd h (Finset.notMem_empty _)⟩

/-- **Completeness, branch 1, when `j₁` does not exist.** Every index above `j` is already a
threshold, so dropping `j` leaves room for every machine. -/
theorem achievable_branch_not_taken_erase_of {X Z : Finset (Fin E.n)} {j : Fin E.n}
    {W' : ℕ} {P' : ℤ} (hjmin : ∀ x ∈ X, j ≤ x) (hall : ∀ x : Fin E.n, j < x → x ∈ X)
    (hjZ : j ∉ Z) (hw : E.wt Z = W') (hc : E.CompatibleWith X Z)
    (hp : E.PreprocessableFrom Z P') :
    E.Achievable (X.erase j) W' P' := by
  obtain ⟨mach, hmem, hle, hindep⟩ := hc
  have hZgt : ∀ z ∈ Z, j < z := by
    intro z hz
    refine lt_of_le_of_ne (le_trans (hjmin _ (hmem z hz)) (hle z hz)) ?_
    rintro rfl
    exact hjZ hz
  rcases Z.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨∅, hw, compatibleWith_empty _, hp⟩
  · set t : Fin E.n := ⟨(j : ℕ) + 1, lt_of_le_of_lt (Fin.lt_def.mp (hZgt z₀ hz₀)) z₀.isLt⟩
      with ht
    have htx : ∀ x : Fin E.n, t ≤ x ↔ j < x := by
      intro x
      simp only [ht, Fin.le_def, Fin.lt_def]
      omega
    exact ⟨Z, hw, compatible_erase hmem hle hindep hjmin (fun x hx => hall x ((htx x).mp hx))
      hjZ (fun z hz _ => (htx z).mpr (hZgt z hz)), hp⟩

/-- **Lemma 1.** For `j = min X`, recursion (1) holds with `X₁` and `X₂` defined exactly as
in the paper, whether or not `j₁` and `j₂` exist: `P'` is achievable for `(X, W')` iff it is
achievable for `(X₁, W')`, or job `j` fits before `sⱼ` and `W' − wⱼ` is achievable for `X₂`
starting at `P' + pⱼ`. -/
theorem lemma1 (hq : ∀ i, 0 < E.q i) {X : Finset (Fin E.n)} {j : Fin E.n}
    (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) {W' : ℕ} {P' : ℤ} :
    E.Achievable X W' P' ↔
      E.Achievable (E.X1 X j) W' P' ∨
        (E.w j ≤ W' ∧ P' + E.p j ≤ E.st j ∧
          E.Achievable (E.X2 X j) (W' - E.w j) (P' + E.p j)) := by
  classical
  have hsj : E.st j < (E.d j : ℤ) := by
    have h1 : E.st j = (E.d j : ℤ) - E.q j := rfl
    have := hq j
    omega
  constructor
  · rintro ⟨Z, hw, hc, hp⟩
    by_cases hjZ : j ∈ Z
    · -- `j` is selected
      obtain ⟨hfit, hwle, hach⟩ := achievable_branch_taken_of_slide (Y := E.X2 X j)
        hq hjmin hjZ hw hc hp fun mach hmem hle hindep hhigh => by
          unfold X2 j2
          split_ifs with h2
          · set y := (Finset.univ.filter fun x => x ∉ X ∧ (E.d j : ℤ) ≤ E.st x).min' h2
            obtain ⟨-, hyX, hyd⟩ := Finset.mem_filter.mp (Finset.min'_mem _ h2)
            have hymin : ∀ x, x ∉ X → (E.d j : ℤ) ≤ E.st x → y ≤ x := fun x hx hd =>
              Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hd⟩)
            have hT : (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x).Nonempty :=
              ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyd⟩⟩
            set t := (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x).min' hT
            have htd : (E.d j : ℤ) ≤ E.st t := (Finset.mem_filter.mp (Finset.min'_mem _ hT)).2
            have ht : ∀ x : Fin E.n, t ≤ x ↔ (E.d j : ℤ) ≤ E.st x := fun x =>
              ⟨fun h => le_trans htd (E.st_mono h),
               fun h => Finset.min'_le
                 (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x) x
                 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)⟩
            exact compatible_shift hmem hle hindep hjmin hyX
              (fun x htx hxy => by
                by_contra hxX
                exact absurd (hymin x hxX ((ht x).mp htx)) (not_le.mpr hxy))
              (Finset.notMem_erase j Z) fun z hz hmz => (ht z).mpr (hhigh z hz hmz)
          · have hnone : ∀ x : Fin E.n, (E.d j : ℤ) ≤ E.st x → x ∈ X := fun x hd => by
              by_contra hxX
              exact h2 ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxX, hd⟩⟩
            by_cases hT : (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x).Nonempty
            · set t := (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x).min' hT
              have htd : (E.d j : ℤ) ≤ E.st t :=
                (Finset.mem_filter.mp (Finset.min'_mem _ hT)).2
              have ht : ∀ x : Fin E.n, t ≤ x ↔ (E.d j : ℤ) ≤ E.st x := fun x =>
                ⟨fun h => le_trans htd (E.st_mono h),
                 fun h => Finset.min'_le
                 (Finset.univ.filter fun x : Fin E.n => (E.d j : ℤ) ≤ E.st x) x
                 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)⟩
              exact compatible_erase hmem hle hindep hjmin
                (fun x htx => hnone x ((ht x).mp htx)) (Finset.notMem_erase j Z)
                fun z hz hmz => (ht z).mpr (hhigh z hz hmz)
            · -- no job starts after `dⱼ`: machine `j` carries `j` alone
              refine ⟨mach, fun z hz => Finset.mem_erase.mpr ⟨fun hmz => hT ?_, hmem z hz⟩,
                hle, hindep⟩
              exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh z hz hmz⟩⟩
      exact Or.inr ⟨hwle, hfit, hach⟩
    · -- `j` is not selected
      left
      unfold X1 j1
      split_ifs with h1
      · set y := (Finset.univ.filter fun x => x ∉ X ∧ j < x).min' h1
        obtain ⟨-, hyX, hyj⟩ := Finset.mem_filter.mp (Finset.min'_mem _ h1)
        exact achievable_branch_not_taken_of hjmin hyj hyX
          (fun x hjx hxy => by
            by_contra hxX
            exact absurd (Finset.min'_le _ _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxX, hjx⟩)) (not_le.mpr hxy))
          hjZ hw hc hp
      · exact achievable_branch_not_taken_erase_of hjmin
          (fun x hjx => by
            by_contra hxX
            exact h1 ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxX, hjx⟩⟩)
          hjZ hw hc hp
  · rintro (h | ⟨hwle, hfit, hach⟩)
    · unfold X1 j1 at h
      split_ifs at h with h1
      · obtain ⟨-, -, hyj⟩ := Finset.mem_filter.mp (Finset.min'_mem _ h1)
        exact achievable_of_branch_not_taken hjX (le_of_lt hyj) (Finset.Subset.refl _) h
      · exact achievable_of_branch_not_taken hjX le_rfl (Finset.subset_insert _ _) h
    · unfold X2 j2 at hach
      split_ifs at hach with h2
      · obtain ⟨-, -, hyd⟩ := Finset.mem_filter.mp (Finset.min'_mem _ h2)
        refine achievable_of_branch_taken hjX hjmin (fun _ => ⟨?_, hyd⟩)
          (Finset.Subset.refl _) (by omega) hfit hach
        by_contra hle
        have := E.st_mono (not_lt.mp hle)
        omega
      · exact achievable_of_branch_taken (y₂ := j) hjX hjmin
          (fun h => absurd h (Finset.notMem_erase j X)) (Finset.subset_insert _ _)
          (by omega) hfit hach


/-! ## 9. Theorem 2 end to end, and Corollary 2

The paper's base cases are `T[X, 0] = +∞` and `T[∅, W'] = −∞` for `W' ≠ 0`; the optimum is the
largest `W'` with `T[{1, …, m}, W'] ≥ 0`. Corollary 2's dual table — the largest `W'` for a
given start `P'` — is the *same* relation `Achievable X W' P'` read with the roles of `W'` and
`P'` exchanged, so its recursion (2) is `lemma1` again and its base case `T[∅, P'] = 0` is
`achievable_empty_iff`. -/

variable (E) in
/-- The paper's `{1, …, m}`: the first `m` indices (all of them, if `m ≥ n`). -/
def firstM : Finset (Fin E.n) := Finset.univ.filter fun i => (i : ℕ) < E.numMachines

@[simp] lemma mem_firstM {i : Fin E.n} : i ∈ E.firstM ↔ (i : ℕ) < E.numMachines := by
  simp [firstM]

lemma rank_le_self {n : ℕ} (H : Finset (Fin n)) (i : Fin n) : rank H i ≤ (i : ℕ) := by
  have h : (H.filter fun x => x < i).card ≤ (Finset.range i).card :=
    Finset.card_le_card_of_injOn (fun x => (x : ℕ))
      (fun x hx => Finset.mem_range.mpr (Fin.lt_def.mp (Finset.mem_filter.mp hx).2))
      (fun a _ b _ hab => Fin.ext hab)
  simpa [rank] using h

/-- **Every `m`-schedulable set is compatible with `{1, …, m}`**, the set that dominates all
others: send each threshold to its rank. -/
theorem compatible_firstM {X Z : Finset (Fin E.n)} (hX : X.card ≤ E.numMachines)
    (h : E.CompatibleWith X Z) : E.CompatibleWith (E.firstM) Z := by
  have hXn : X.card ≤ E.n := by simpa using Finset.card_le_univ X
  refine compatible_of_relabel
    (fun y => if hy : y ∈ X then ⟨rank X y, lt_of_lt_of_le (rank_lt hy) hXn⟩ else y)
    (fun y hy => ?_) (fun y hy y' hy' heq => ?_) (fun y hy => ?_) h
  · simp only [dif_pos hy, firstM, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_lt_of_le (rank_lt hy) hX
  · simp only [dif_pos hy, dif_pos hy'] at heq
    exact rank_injOn hy hy' (congrArg Fin.val heq)
  · simp only [dif_pos hy]
    exact Fin.le_def.mpr (rank_le_self X y)

/-- **Theorem 2, its read-off.** A feasible solution of weight `W'` exists exactly when
`T[{1, …, m}, W'] ≥ 0` — some start `P' ≥ 0` is achievable with the first `m` indices as
thresholds. With `lemma1`, `achievable_zero` and `achievable_empty_iff` this is the whole
correctness of Theorem 2's dynamic program; the `O(W·n^m)` bound is a running-time claim. -/
theorem theorem2_readoff (W' : ℕ) :
    (∃ P' : ℤ, 0 ≤ P' ∧ E.Achievable (E.firstM) W' P') ↔
      ∃ Z : Finset (Fin E.n), E.toFFJ.Feasible Z ∧ E.wt Z = W' := by
  constructor
  · rintro ⟨P', hP, hach⟩
    have hcard : (E.firstM).card ≤ E.numMachines := by
      have h := Finset.card_le_card_of_injOn (s := E.firstM) (t := Finset.range E.numMachines)
        (fun i : Fin E.n => (i : ℕ))
        (fun i hi => Finset.mem_range.mpr (mem_firstM.mp hi))
        (fun a _ b _ hab => Fin.ext hab)
      simpa using h
    obtain ⟨Z, hZ, hw⟩ := feasible_of_achievable hcard hP hach
    exact ⟨Z, hZ, (E.wt_eq Z) ▸ hw⟩
  · rintro ⟨Z, hZ, hw⟩
    obtain ⟨hpre, hsch⟩ := (E.toFFJ.feasible_iff Z).mp hZ
    obtain ⟨X, hX, hc⟩ := exists_compatible_of_mSchedulable hsch
    exact ⟨0, le_rfl, Z, hw, compatible_firstM hX hc, (preprocessable_iff_from_zero Z).mp hpre⟩

end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
