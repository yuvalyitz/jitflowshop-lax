import Lax496464Proofs.Model.Theorem1_FromHittingSet
import Lax496464Proofs.Model.Section2

namespace Lax496464Proofs

/-!
# Section 8, Lemma 6: a Hitting Set Yields a Schedule

The forward direction of Theorem 1's correctness. Given a hitting set `H` of size `k`,
this file builds an explicit `FFJ.JITSchedule` of `R·m·(2k−1)` jobs of `Theorem1.inst`.

## The Schedule, in One Picture

Write `g = g(r,j)` for an epoch's position and `o = i + 1` for an element's offset. The
construction has two independent tilings, and the whole proof is that both of them are
exact.

**The second stage tiles by machine.** Every job of element `i` — selection or dummy —
lives inside `[g²Q + o, (g+1)²Q + o)`, and machine `k'` runs only jobs of the *single*
element `i(k')`, so consecutive epochs abut exactly: `(g+1)²Q + o` is the next epoch's
start. Within an epoch a machine runs either the selection job (which fills
`[g²Q+o, (g+1)²Q+o)` alone) or the pair `A, B`, which meet at `s(B) = d(A)`. So no machine
ever double-books.

**The first stage tiles by epoch.** Only dummies need preprocessing, `g·(n+1)` each, and
epoch `g` contributes `2(k−1)` of them — total `2(k−1)·g·(n+1) = 2gQ`, since
`Q = (k−1)(n+1)`. Lay them back to back in `[g(g−1)·Q, g(g+1)·Q)`, the `A`s first: that
block has length exactly `2gQ`, the `A`s finish by `g²Q` (before the earliest `s(A) = g²Q + o`)
and the `B`s by `g(g+1)Q` (before the earliest `s(B) = g(g+1)Q + o`), and epoch `g`'s block
ends exactly where epoch `g+1`'s begins, because `g(g+1) = (g+1)((g+1)−1)`.

That both tilings are *exact* — no slack anywhere — is what forces the `R·m·(2k−1)` target
in the converse direction, which is Lemmas 7–9 and is **not** in this file.

## Notes on the Formalization

* Positions are carried as `gp = g − 1 = r·m + j` rather than `g`, purely so that no
  natural-number subtraction appears: every bound is then a polynomial identity `ring` can
  check. `g_eq_gp_succ` is the bridge.
* `rank H i` is `i`'s position among the elements of `H`, defined as
  `#{x ∈ H : x < i}` — no enumeration of `H` is needed, and its two properties
  (`rank_lt`, `rank_injOn`) are three lines each. Machine numbers are `rank H i`, and a
  dummy's slot inside its epoch's block is `rank (H.erase (hit j)) i`, the same function
  one level down.
* `k ≥ 1` is never assumed: it follows from `hit j ∈ H` wherever it is needed, and if
  `m = 0` the target size is `0` and the empty schedule works.
-/


namespace FlexFlowJIT

namespace Theorem1

-- `rank`, the position of an element within a `Finset (Fin n)`, is shared with
-- `Sorted.lean` and lives in `Defs.lean`.

/-! ## 2. Epoch positions without subtraction -/

/-- `gp(r,j) = g(r,j) − 1 = r·m + j`, the epoch position counted from `0`. Every bound
below is stated in `gp`, so that `g² − g = gp·(gp+1)` is a `ring` identity rather than a
truncated subtraction. -/
def gp (P : HSInstance) (r : ℕ) (j : Fin P.m) : ℕ := r * P.m + j.val

variable (P : HSInstance) (k : ℕ)

lemma g_eq_gp_succ (r : ℕ) (j : Fin P.m) : g P r j = gp P r j + 1 := by unfold g gp; omega

/-- Distinct epochs have distinct positions: `(r, j) ↦ r·m + j` is injective because
`j < m`. -/
lemma gp_inj {r r' : ℕ} {j j' : Fin P.m} (h : gp P r j = gp P r' j') : r = r' ∧ j = j' := by
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [gp] at h
  constructor
  · rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
    · exfalso
      have : (r + 1) * P.m ≤ r' * P.m := Nat.mul_le_mul_right _ hlt
      simp only [Nat.add_mul, one_mul] at this
      omega
    · exact heq
    · exfalso
      have : (r' + 1) * P.m ≤ r * P.m := Nat.mul_le_mul_right _ hgt
      simp only [Nat.add_mul, one_mul] at this
      omega
  · rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
    · exfalso
      have : (r + 1) * P.m ≤ r' * P.m := Nat.mul_le_mul_right _ hlt
      simp only [Nat.add_mul, one_mul] at this
      omega
    · subst heq; exact Fin.ext (by omega)
    · exfalso
      have : (r' + 1) * P.m ≤ r * P.m := Nat.mul_le_mul_right _ hgt
      simp only [Nat.add_mul, one_mul] at this
      omega

/-! ## 3. The job set the schedule serves

`H` is the hitting set and `hit j` the element of it chosen to hit `F j` — carried as a
member of the subtype `{i // i ∈ P.F j}` so that no proof argument appears inside the
definitions below. In each epoch, the machine of `hit j` runs a selection job and every
other machine of `H` runs its two dummies. -/

variable (H : Finset (Fin P.n)) (hit : ∀ j : Fin P.m, {i : Fin P.n // i ∈ P.F j})

/-- The `2k − 1` jobs the schedule puts in the epoch `T^r_j`: one selection job for the
element hitting `F j`, and both dummies for each of the other `k − 1` elements of `H`. -/
def epochJobs (r : Fin (R P k)) (j : Fin P.m) : Finset (Jobs P k) :=
  insert (Sum.inl (r, ⟨j, hit j⟩))
    ((H.erase (hit j).val).image (fun i => Sum.inr (Sum.inl (r, j, i))) ∪
      (H.erase (hit j).val).image (fun i => Sum.inr (Sum.inr (r, j, i))))

/-- The whole solution: every epoch's jobs. -/
def sched : Finset (Jobs P k) :=
  (Finset.univ : Finset (Fin (R P k) × Fin P.m)).biUnion
    (fun rj => epochJobs P k H hit rj.1 rj.2)

/-- The epoch a job belongs to, read off its index. -/
def jobEpoch : Jobs P k → Fin (R P k) × Fin P.m
  | .inl (r, ⟨j, _⟩) => (r, j)
  | .inr (.inl (r, j, _)) => (r, j)
  | .inr (.inr (r, j, _)) => (r, j)

variable {P k H hit}

lemma jobEpoch_of_mem_epochJobs {r : Fin (R P k)} {j : Fin P.m} {x : Jobs P k}
    (hx : x ∈ epochJobs P k H hit r j) : jobEpoch P k x = (r, j) := by
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · rfl
  rcases Finset.mem_union.mp hx' with hx'' | hx''
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx''; rfl
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx''; rfl

/-- Everything in `sched` has one of the three shapes it was built from. This is the only
way membership is ever used below. -/
lemma mem_sched_elim {x : Jobs P k} (hx : x ∈ sched P k H hit) :
    (∃ r j, x = Sum.inl (r, ⟨j, hit j⟩)) ∨
    (∃ r j i, i ∈ H.erase (hit j).val ∧ x = Sum.inr (Sum.inl (r, j, i))) ∨
    (∃ r j i, i ∈ H.erase (hit j).val ∧ x = Sum.inr (Sum.inr (r, j, i))) := by
  obtain ⟨rj, -, hrj⟩ := Finset.mem_biUnion.mp hx
  rcases Finset.mem_insert.mp hrj with rfl | hrj'
  · exact Or.inl ⟨rj.1, rj.2, rfl⟩
  rcases Finset.mem_union.mp hrj' with hrj'' | hrj''
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hrj''
    exact Or.inr (Or.inl ⟨rj.1, rj.2, i, hi, rfl⟩)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hrj''
    exact Or.inr (Or.inr ⟨rj.1, rj.2, i, hi, rfl⟩)

variable (P k H hit)

/-! ## 4. There are `R·m·(2k−1)` of them -/

lemma card_epochJobs (hH : H.card = k) (hhit : ∀ j, (hit j).val ∈ H)
    (r : Fin (R P k)) (j : Fin P.m) : (epochJobs P k H hit r j).card = 2 * k - 1 := by
  have hk : 1 ≤ k := by
    have := Finset.card_pos.mpr ⟨(hit j).val, hhit j⟩
    omega
  have herase : (H.erase (hit j).val).card = k - 1 := by
    rw [Finset.card_erase_of_mem (hhit j), hH]
  have hinjA : Function.Injective
      (fun i : Fin P.n => (Sum.inr (Sum.inl (r, j, i)) : Jobs P k)) := by
    intro a b h; simpa using h
  have hinjB : Function.Injective
      (fun i : Fin P.n => (Sum.inr (Sum.inr (r, j, i)) : Jobs P k)) := by
    intro a b h; simpa using h
  have hdisj : Disjoint ((H.erase (hit j).val).image
        (fun i => (Sum.inr (Sum.inl (r, j, i)) : Jobs P k)))
      ((H.erase (hit j).val).image (fun i => (Sum.inr (Sum.inr (r, j, i)) : Jobs P k))) := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hx'
    simp at hb
  have hnot : (Sum.inl (r, ⟨j, hit j⟩) : Jobs P k) ∉
      ((H.erase (hit j).val).image (fun i => (Sum.inr (Sum.inl (r, j, i)) : Jobs P k)) ∪
        (H.erase (hit j).val).image (fun i => (Sum.inr (Sum.inr (r, j, i)) : Jobs P k))) := by
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists]
    constructor <;> (intro i; simp)
  change (insert (Sum.inl (r, ⟨j, hit j⟩))
      ((H.erase (hit j).val).image (fun i => (Sum.inr (Sum.inl (r, j, i)) : Jobs P k)) ∪
        (H.erase (hit j).val).image
          (fun i => (Sum.inr (Sum.inr (r, j, i)) : Jobs P k)))).card = 2 * k - 1
  rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinjA, Finset.card_image_of_injective _ hinjB, herase]
  omega

/-- **The solution has exactly the target cardinality** `R·m·(2k−1)`: `2k − 1` jobs in each
of the `R·m` epochs. -/
theorem card_sched (hH : H.card = k) (hhit : ∀ j, (hit j).val ∈ H) :
    (sched P k H hit).card = targetSize P k := by
  rw [sched, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun rj _ => card_epochJobs P k H hit hH hhit rj.1 rj.2)]
    simp [Finset.card_univ, targetSize, Nat.mul_comm]
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun x hx hx' => hab ?_
    have h1 := jobEpoch_of_mem_epochJobs hx
    have h2 := jobEpoch_of_mem_epochJobs hx'
    rw [h1] at h2
    exact Prod.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)

/-! ## 5. The two tilings, as arithmetic

Everything below is stated in `gp = g − 1`, so each bound is a `ring` identity. Write
`a` for an epoch's `gp`. The epoch's **preprocessing block** is `[a(a+1)Q, (a+1)(a+2)Q)`,
which has length `2(a+1)Q = 2(k−1)·(a+1)(n+1)` — room for exactly the `2(k−1)` dummies of
that epoch, each of length `(a+1)(n+1)`. Consecutive blocks abut, since `(a+1)(a+2)` is
the next epoch's `a(a+1)`. -/

/-- The start of the `t`-th dummy slot in the preprocessing block of the epoch at
position `gp(r,j)`. -/
def dumPre (r : ℕ) (j : Fin P.m) (t : ℕ) : ℕ :=
  gp P r j * (gp P r j + 1) * Q P k + t * ((gp P r j + 1) * (P.n + 1))

lemma dumPre_mono (r : ℕ) (j : Fin P.m) {t t' : ℕ} (h : t ≤ t') :
    dumPre P k r j t ≤ dumPre P k r j t' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

lemma dumPre_succ (r : ℕ) (j : Fin P.m) (t : ℕ) :
    dumPre P k r j t + (gp P r j + 1) * (P.n + 1) = dumPre P k r j (t + 1) := by
  simp only [dumPre]; ring

/-- A dummy slot numbered below `k − 1` finishes by `G(r,j) = (a+1)²Q`, the earliest start
time of any `A` job of the epoch. -/
lemma dumPre_le_G (r : ℕ) (j : Fin P.m) {t : ℕ} (ht : t ≤ k - 1) :
    dumPre P k r j t ≤ (gp P r j + 1) ^ 2 * Q P k := by
  have h1 : dumPre P k r j t ≤ dumPre P k r j (k - 1) := dumPre_mono P k r j ht
  have h2 : dumPre P k r j (k - 1) = (gp P r j + 1) ^ 2 * Q P k := by
    simp only [dumPre, Q]; ring
  omega

/-- A dummy slot numbered below `2(k − 1)` finishes by `(a+1)(a+2)Q`, the end of its
epoch's block — and the earliest start time of any `B` job of the epoch. -/
lemma dumPre_le_blockEnd (r : ℕ) (j : Fin P.m) {t : ℕ} (ht : t ≤ 2 * (k - 1)) :
    dumPre P k r j t ≤ (gp P r j + 1) * (gp P r j + 2) * Q P k := by
  have h1 : dumPre P k r j t ≤ dumPre P k r j (2 * (k - 1)) := dumPre_mono P k r j ht
  have h2 : dumPre P k r j (2 * (k - 1)) = (gp P r j + 1) * (gp P r j + 2) * Q P k := by
    simp only [dumPre, Q]; ring
  omega

/-- Consecutive epochs' preprocessing blocks abut. -/
lemma blockEnd_le_blockStart {r r' : ℕ} {j j' : Fin P.m} (h : gp P r j < gp P r' j') :
    (gp P r j + 1) * (gp P r j + 2) * Q P k ≤ gp P r' j' * (gp P r' j' + 1) * Q P k :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))

lemma blockStart_le_dumPre (r : ℕ) (j : Fin P.m) (t : ℕ) :
    gp P r j * (gp P r j + 1) * Q P k ≤ dumPre P k r j t := Nat.le_add_right _ _

/-! ## 6. Due dates and start times as naturals

`FFJ.s` lands in `ℤ`; every value it takes on this instance is a natural, and `sN` is
that natural. Working in `ℕ` keeps `omega` and `ring` usable throughout. -/

/-- `FFJ.s` of a job of the constructed instance, as a natural number. -/
def sN : Jobs P k → ℕ
  | .inl (r, ⟨j, i⟩) => G P k r.val j + (i.val.val + 1)
  | .inr (.inl (r, j, i)) => G P k r.val j + (i.val + 1)
  | .inr (.inr (r, j, i)) => G P k r.val j + g P r.val j * Q P k + (i.val + 1)

lemma s_eq_sN (x : Jobs P k) : (inst P k).s x = (sN P k x : ℤ) := by
  match x with
  | .inl (r, ⟨j, i⟩) => rw [s_sel]; simp only [sN]; push_cast; ring
  | .inr (.inl (r, j, i)) => rw [s_dumA]; simp only [sN]; push_cast; ring
  | .inr (.inr (r, j, i)) => rw [s_dumB]; simp only [sN]; push_cast; ring

/-- The element of the universe a job belongs to. Machine numbers are read off this. -/
def elemOf : Jobs P k → Fin P.n
  | .inl (_, ⟨_, i⟩) => i.val
  | .inr (.inl (_, _, i)) => i
  | .inr (.inr (_, _, i)) => i

/-- The position `gp` of the epoch a job lives in. -/
def epochIdx : Jobs P k → ℕ
  | .inl (r, ⟨j, _⟩) => gp P r.val j
  | .inr (.inl (r, j, _)) => gp P r.val j
  | .inr (.inr (r, j, _)) => gp P r.val j

/-- Every job of an epoch starts no earlier than the epoch's own start, shifted by the
element's offset. -/
lemma le_sN (x : Jobs P k) :
    (epochIdx P k x + 1) ^ 2 * Q P k + ((elemOf P k x).val + 1) ≤ sN P k x := by
  match x with
  | .inl (r, ⟨j, i⟩) =>
      simp only [sN, elemOf, epochIdx, G, g_eq_gp_succ]
      omega
  | .inr (.inl (r, j, i)) =>
      simp only [sN, elemOf, epochIdx, G, g_eq_gp_succ]
      omega
  | .inr (.inr (r, j, i)) =>
      simp only [sN, elemOf, epochIdx, G, g_eq_gp_succ]
      omega

/-- ... and is due no later than the epoch's end, shifted the same way. -/
lemma jd_le_epoch (x : Jobs P k) :
    jd P k x ≤ (epochIdx P k x + 2) ^ 2 * Q P k + ((elemOf P k x).val + 1) := by
  match x with
  | .inl (r, ⟨j, i⟩) =>
      have h : (gp P r.val j + 1) ^ 2 * Q P k + (2 * (gp P r.val j + 1) + 1) * Q P k
          = (gp P r.val j + 2) ^ 2 * Q P k := by ring
      simp only [jd, elemOf, epochIdx, G, g_eq_gp_succ]
      omega
  | .inr (.inl (r, j, i)) =>
      have h : (gp P r.val j + 1) ^ 2 * Q P k + (gp P r.val j + 1) * Q P k
            + (gp P r.val j + 2) * Q P k = (gp P r.val j + 2) ^ 2 * Q P k := by ring
      simp only [jd, elemOf, epochIdx, G, g_eq_gp_succ]
      omega
  | .inr (.inr (r, j, i)) =>
      have h : (gp P r.val j + 1) ^ 2 * Q P k + (2 * (gp P r.val j + 1) + 1) * Q P k
          = (gp P r.val j + 2) ^ 2 * Q P k := by ring
      simp only [jd, elemOf, epochIdx, G, g_eq_gp_succ]
      omega

/-- Two jobs of the same element in different epochs never overlap: the earlier one is due
before the later one starts. -/
lemma jd_le_sN_of_epoch_lt {x y : Jobs P k} (helem : elemOf P k x = elemOf P k y)
    (h : epochIdx P k x < epochIdx P k y) : jd P k x ≤ sN P k y := by
  have h1 := jd_le_epoch P k x
  have h2 := le_sN P k y
  rw [helem] at h1
  have h3 : (epochIdx P k x + 2) ^ 2 * Q P k ≤ (epochIdx P k y + 1) ^ 2 * Q P k :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
  omega

/-- Inside one epoch, an `A` job is due exactly when its `B` partner starts. -/
lemma jd_A_eq_sN_B (r : Fin (R P k)) (j : Fin P.m) (i : Fin P.n) :
    jd P k (.inr (.inl (r, j, i))) = sN P k (.inr (.inr (r, j, i))) := rfl

/-! ## 7. The schedule

`preN` lays the dummies out inside their epochs' blocks — the `A`s in slots
`0, …, k−2` and the `B`s in slots `k−1, …, 2k−3` — and `machOf` sends every job to the
machine of its own element. Selection jobs need no preprocessing, so they sit at `0`,
where their zero-length first operation is disjoint from everything by default. -/

/-- Where a job's first operation starts. -/
def preN : Jobs P k → ℕ
  | .inl _ => 0
  | .inr (.inl (r, j, i)) => dumPre P k r.val j (rank (H.erase (hit j).val) i)
  | .inr (.inr (r, j, i)) => dumPre P k r.val j ((k - 1) + rank (H.erase (hit j).val) i)

/-- The second-stage machine a job runs on: the one belonging to its own element. -/
def machOf : Jobs P k → ℕ := fun x => rank H (elemOf P k x)

variable {P k H hit}

lemma elemOf_mem (hhit : ∀ j, (hit j).val ∈ H) {x : Jobs P k} (hx : x ∈ sched P k H hit) :
    elemOf P k x ∈ H := by
  rcases mem_sched_elim hx with ⟨r, j, rfl⟩ | ⟨r, j, i, hi, rfl⟩ | ⟨r, j, i, hi, rfl⟩
  · exact hhit j
  · exact Finset.mem_of_mem_erase hi
  · exact Finset.mem_of_mem_erase hi

lemma dumPre_congr {r r' : ℕ} {j j' : Fin P.m} (h : gp P r j = gp P r' j') (t : ℕ) :
    dumPre P k r j t = dumPre P k r' j' t := by simp only [dumPre, h]

/-- Two dummy slots that differ — in epoch or in slot number — occupy disjoint
preprocessing intervals. Both tilings are used: distinct epochs are separated by
`blockEnd_le_blockStart`, and distinct slots inside one epoch by `dumPre_succ`. -/
lemma dum_disjoint {r r' : Fin (R P k)} {j j' : Fin P.m} {t t' : ℕ}
    (ht : t < 2 * (k - 1)) (ht' : t' < 2 * (k - 1))
    (hne : ¬ (gp P r.val j = gp P r'.val j' ∧ t = t')) :
    dumPre P k r.val j t + (gp P r.val j + 1) * (P.n + 1) ≤ dumPre P k r'.val j' t'
      ∨ dumPre P k r'.val j' t' + (gp P r'.val j' + 1) * (P.n + 1)
          ≤ dumPre P k r.val j t := by
  rcases Nat.lt_trichotomy (gp P r.val j) (gp P r'.val j') with h | h | h
  · refine Or.inl ?_
    calc dumPre P k r.val j t + (gp P r.val j + 1) * (P.n + 1)
        = dumPre P k r.val j (t + 1) := dumPre_succ P k r.val j t
      _ ≤ (gp P r.val j + 1) * (gp P r.val j + 2) * Q P k :=
          dumPre_le_blockEnd P k r.val j (by omega)
      _ ≤ gp P r'.val j' * (gp P r'.val j' + 1) * Q P k := blockEnd_le_blockStart P k h
      _ ≤ dumPre P k r'.val j' t' := blockStart_le_dumPre P k _ _ _
  · have htt : t ≠ t' := fun hc => hne ⟨h, hc⟩
    rw [dumPre_congr h t, h]
    rcases Nat.lt_or_ge t t' with hlt | hge
    · refine Or.inl ?_
      rw [dumPre_succ P k r'.val j' t]
      exact dumPre_mono P k r'.val j' (by omega)
    · refine Or.inr ?_
      rw [dumPre_succ P k r'.val j' t']
      exact dumPre_mono P k r'.val j' (by omega)
  · refine Or.inr ?_
    calc dumPre P k r'.val j' t' + (gp P r'.val j' + 1) * (P.n + 1)
        = dumPre P k r'.val j' (t' + 1) := dumPre_succ P k r'.val j' t'
      _ ≤ (gp P r'.val j' + 1) * (gp P r'.val j' + 2) * Q P k :=
          dumPre_le_blockEnd P k r'.val j' (by omega)
      _ ≤ gp P r.val j * (gp P r.val j + 1) * Q P k := blockEnd_le_blockStart P k h
      _ ≤ dumPre P k r.val j t := blockStart_le_dumPre P k _ _ _

/-- A dummy of `sched` has a slot number below `k − 1`: there is room for it. -/
lemma rank_erase_lt {j : Fin P.m} {i : Fin P.n} (hH : H.card = k)
    (hhit : ∀ j, (hit j).val ∈ H) (hi : i ∈ H.erase (hit j).val) :
    rank (H.erase (hit j).val) i < k - 1 := by
  have h := rank_lt hi
  rwa [Finset.card_erase_of_mem (hhit j), hH] at h

/-- **The first stage, part one.** Every job's preprocessing is finished by the time its
second operation must start. -/
lemma preN_add_jp_le_sN (hH : H.card = k) (hhit : ∀ j, (hit j).val ∈ H)
    {x : Jobs P k} (hx : x ∈ sched P k H hit) :
    preN P k H hit x + jp P k x ≤ sN P k x := by
  rcases mem_sched_elim hx with ⟨r, j, rfl⟩ | ⟨r, j, i, hi, rfl⟩ | ⟨r, j, i, hi, rfl⟩
  · simp only [preN, jp, sN]
    omega
  · have hr := rank_erase_lt hH hhit hi
    have hbound : dumPre P k r.val j (rank (H.erase (hit j).val) i + 1)
        ≤ (gp P r.val j + 1) ^ 2 * Q P k := dumPre_le_G P k r.val j (by omega)
    have hG : G P k r.val j = (gp P r.val j + 1) ^ 2 * Q P k := by
      simp only [G, g_eq_gp_succ]
    rw [← dumPre_succ] at hbound
    simp only [preN, jp, sN, g_eq_gp_succ]
    omega
  · have hr := rank_erase_lt hH hhit hi
    have hbound : dumPre P k r.val j (k - 1 + rank (H.erase (hit j).val) i + 1)
        ≤ (gp P r.val j + 1) * (gp P r.val j + 2) * Q P k :=
      dumPre_le_blockEnd P k r.val j (by omega)
    have hG : G P k r.val j + (gp P r.val j + 1) * Q P k
        = (gp P r.val j + 1) * (gp P r.val j + 2) * Q P k := by
      simp only [G, g_eq_gp_succ]; ring
    rw [← dumPre_succ] at hbound
    simp only [preN, jp, sN, g_eq_gp_succ]
    omega

/-- **The first stage, part two.** No two first operations overlap. -/
lemma preN_disjoint (hH : H.card = k) (hhit : ∀ j, (hit j).val ∈ H)
    {x y : Jobs P k} (hx : x ∈ sched P k H hit) (hy : y ∈ sched P k H hit) (hxy : x ≠ y) :
    preN P k H hit x + jp P k x ≤ preN P k H hit y
      ∨ preN P k H hit y + jp P k y ≤ preN P k H hit x := by
  rcases mem_sched_elim hx with ⟨r, j, rfl⟩ | ⟨r, j, i, hi, rfl⟩ | ⟨r, j, i, hi, rfl⟩
  · exact Or.inl (by simp only [preN, jp]; omega)
  · have hrk := rank_erase_lt hH hhit hi
    rcases mem_sched_elim hy with ⟨r', j', rfl⟩ | ⟨r', j', i', hi', rfl⟩ |
      ⟨r', j', i', hi', rfl⟩
    · exact Or.inr (by simp only [preN, jp]; omega)
    · have hrk' := rank_erase_lt hH hhit hi'
      refine dum_disjoint (by omega) (by omega) (fun hc => hxy ?_)
      obtain ⟨hrr, hjj⟩ := gp_inj P hc.1
      subst hjj
      have hii : i = i' := rank_injOn hi hi' hc.2
      subst hii
      have hrr' : r = r' := Fin.ext hrr
      subst hrr'
      rfl
    · have hrk' := rank_erase_lt hH hhit hi'
      exact dum_disjoint (by omega) (by omega) (fun hc => absurd hc.2 (by omega))
  · have hrk := rank_erase_lt hH hhit hi
    rcases mem_sched_elim hy with ⟨r', j', rfl⟩ | ⟨r', j', i', hi', rfl⟩ |
      ⟨r', j', i', hi', rfl⟩
    · exact Or.inr (by simp only [preN, jp]; omega)
    · have hrk' := rank_erase_lt hH hhit hi'
      exact dum_disjoint (by omega) (by omega) (fun hc => absurd hc.2 (by omega))
    · have hrk' := rank_erase_lt hH hhit hi'
      refine dum_disjoint (by omega) (by omega) (fun hc => hxy ?_)
      obtain ⟨hrr, hjj⟩ := gp_inj P hc.1
      subst hjj
      have hii : i = i' := rank_injOn hi hi' (by omega)
      subst hii
      have hrr' : r = r' := Fin.ext hrr
      subst hrr'
      rfl

/-! ## 8. The second stage

A machine runs the jobs of one element only, so all its jobs share an offset `o` and each
of them lies inside its own epoch's window `[g²Q + o, (g+1)²Q + o)`. Consecutive windows
abut, and inside one window a machine holds either the selection job alone or the pair
`A, B`, which meet at `s(B) = d(A)`. -/

lemma machOf_indep (hhit : ∀ j, (hit j).val ∈ H)
    {x y : Jobs P k} (hx : x ∈ sched P k H hit) (hy : y ∈ sched P k H hit) (hxy : x ≠ y)
    (hm : machOf P k H x = machOf P k H y) : ¬ (inst P k).Conflict x y := by
  have helem : elemOf P k x = elemOf P k y :=
    rank_injOn (elemOf_mem hhit hx) (elemOf_mem hhit hy) hm
  rcases Nat.lt_trichotomy (epochIdx P k x) (epochIdx P k y) with h | h | h
  · refine (inst P k).not_conflict_of_le ?_
    rw [s_eq_sN P k y]
    exact_mod_cast jd_le_sN_of_epoch_lt P k helem h
  · rcases mem_sched_elim hx with ⟨r, j, rfl⟩ | ⟨r, j, i, hi, rfl⟩ | ⟨r, j, i, hi, rfl⟩ <;>
      rcases mem_sched_elim hy with ⟨r', j', rfl⟩ | ⟨r', j', i', hi', rfl⟩ |
        ⟨r', j', i', hi', rfl⟩ <;>
      simp only [elemOf] at helem <;>
      obtain ⟨hrr, hjj⟩ := gp_inj P h <;> subst hjj
    · exact absurd (congrArg (fun z => (Sum.inl (z, ⟨j, hit j⟩) : Jobs P k)) (Fin.ext hrr))
        hxy
    · exact absurd helem.symm (Finset.mem_erase.mp hi').1
    · exact absurd helem.symm (Finset.mem_erase.mp hi').1
    · exact absurd helem (Finset.mem_erase.mp hi).1
    · subst helem
      exact absurd
        (congrArg (fun z => (Sum.inr (Sum.inl (z, j, i)) : Jobs P k)) (Fin.ext hrr)) hxy
    · -- an `A` job is due exactly when its `B` partner starts
      subst helem
      have hrr' : r = r' := Fin.ext hrr
      subst hrr'
      refine (inst P k).not_conflict_of_le ?_
      rw [s_eq_sN P k (Sum.inr (Sum.inr (r, j, i)))]
      exact_mod_cast le_of_eq (jd_A_eq_sN_B P k r j i)
    · exact absurd helem (Finset.mem_erase.mp hi).1
    · -- the same pair, the other way round
      subst helem
      have hrr' : r = r' := Fin.ext hrr
      subst hrr'
      refine fun hc =>
        (inst P k).not_conflict_of_le ?_ ((inst P k).conflict_symm hc)
      rw [s_eq_sN P k (Sum.inr (Sum.inr (r, j, i)))]
      exact_mod_cast le_of_eq (jd_A_eq_sN_B P k r j i)
    · subst helem
      exact absurd
        (congrArg (fun z => (Sum.inr (Sum.inr (z, j, i)) : Jobs P k)) (Fin.ext hrr)) hxy
  · refine fun hc => (inst P k).not_conflict_of_le ?_ ((inst P k).conflict_symm hc)
    rw [s_eq_sN P k x]
    exact_mod_cast jd_le_sN_of_epoch_lt P k helem.symm h

/-! ## 9. Lemma 6 -/

/-- **Lemma 6.** A hitting set of size `k` yields a feasible set of `R·m·(2k−1)`
just-in-time jobs.

Both halves of `FFJ.JITSchedule` are exact tilings, and that is the whole proof: the first
stage fills each epoch's preprocessing block with the epoch's `2(k−1)` dummies
(`preN_add_jp_le_sN`, `preN_disjoint`), and the second stage gives every element its own
machine, on which its jobs tile the time axis window by window (`machOf_indep`). -/
theorem lemma6 (hH : H.card = k) (hhit : ∀ j, (hit j).val ∈ H) :
    (inst P k).HasWeight (targetSize P k) := by
  refine ⟨sched P k H hit, ⟨{
    pre := fun x => (preN P k H hit x : ℤ)
    mach := machOf P k H
    pre_nonneg := fun x _ => Int.natCast_nonneg _
    pre_le_s := fun x hx => by
      rw [s_eq_sN P k x]
      exact_mod_cast preN_add_jp_le_sN hH hhit hx
    pre_disjoint := fun x hx y hy hxy => by
      rcases preN_disjoint hH hhit hx hy hxy with hcase | hcase
      · exact Or.inl (by exact_mod_cast hcase)
      · exact Or.inr (by exact_mod_cast hcase)
    mach_lt := fun x hx => by
      have hlt := rank_lt (elemOf_mem hhit hx)
      rwa [hH] at hlt
    mach_indep := fun x hx y hy hxy hmm => machOf_indep hhit hx hy hxy hmm }⟩, ?_⟩
  have hw : (inst P k).weight (sched P k H hit) = (sched P k H hit).card := by
    simp [FFJ.weight, inst]
  rw [hw, card_sched P k H hit hH hhit]

/-- **Lemma 6, as the forward half of Theorem 1's correctness.** -/
theorem hasWeight_of_hasHittingSet (h : P.HasHittingSet k) :
    (inst P k).HasWeight (targetSize P k) := by
  obtain ⟨H, hH, hhit⟩ := h
  exact lemma6 (H := H) (hit := fun j => ⟨(hhit j).choose, (hhit j).choose_spec.2⟩) hH
    (fun j => (hhit j).choose_spec.1)

end Theorem1

end FlexFlowJIT

end Lax496464Proofs
