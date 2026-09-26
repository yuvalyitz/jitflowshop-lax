import Lax496464Proofs.Model.Section6_Greedy
import Lax496464Proofs.Model.Sorted

namespace Lax496464Proofs

/-!
# Lemma 4: the greedy of Section 6.1 dominates every feasible solution

Section 6.1 sweeps the jobs in EST order, maintaining a feasible `Sⱼ ⊆ Jⱼ = {1, …, j}`. At
step `j` it adds job `j` outright unless one of the two stopping rules fires, in which case
it adds `j` and drops the job of largest due date from `S_{j−1} ∪ {j}`. Lemma 4 says the
result dominates every feasible solution of `Jⱼ`.

**The greedy is formalized as a relation, not a function.** `GreedyStep` says what a legal
successor is; the tie-breaking choice of *which* largest-due-date job to drop is left open,
so the theorem covers every implementation of the algorithm at once and needs no choice
principle in a definition. `Dominating A k` is the invariant, and `lemma4_step` is its
preservation — the whole content of the paper's induction. `lemma4` iterates it.

Domination here is `FFJ.SDom`, the paper's order with its cardinality disjunct dropped; see
`Section6_Greedy.lean` §3 for why the stated order cannot carry this induction and this one
can. `hq` (positive second-stage times) is the paper's standing assumption on the input.
-/

namespace FlexFlowJIT

namespace EstFFJ

variable {E : EstFFJ}

/-! ## 1. Prefixes -/

variable (E) in
/-- The paper's `J_k = {1, …, k}`, as a set of indices. -/
def pre (k : ℕ) : Finset (Fin E.n) := Finset.univ.filter (fun i => (i : ℕ) < k)

@[simp] lemma mem_pre {k : ℕ} {i : Fin E.n} : i ∈ E.pre k ↔ (i : ℕ) < k := by
  simp [pre]

lemma pre_n : E.pre E.n = Finset.univ := by
  ext i
  simp [i.isLt]

lemma pre_succ {k : ℕ} (hk : k < E.n) :
    E.pre (k + 1) = insert (⟨k, hk⟩ : Fin E.n) (E.pre k) := by
  ext i
  simp only [mem_pre, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h)
    · simp
    · omega

/-- Every job of a prefix starts no later than the job that closes it. -/
lemma s_le_of_mem_pre {k : ℕ} (hk : k < E.n) {i : Fin E.n} (hi : i ∈ E.pre (k + 1)) :
    E.toFFJ.s i ≤ E.toFFJ.s (⟨k, hk⟩ : Fin E.n) := by
  refine E.s_mono (Fin.le_def.mpr ?_)
  change (i : ℕ) ≤ k
  have := mem_pre.mp hi
  omega

/-! ## 2. The greedy step, and the invariant it maintains -/

variable (E) in
/-- **One step of Section 6.1's algorithm.** Either neither stopping rule fires and job `j`
joins, or one of them does and the job of largest due date leaves `A ∪ {j}`.

Which largest-due-date job leaves is left unspecified: any choice satisfies this, so every
tie-breaking rule is covered. -/
def GreedyStep (p : ℕ) (A next : Finset (Fin E.n)) (j : Fin E.n) : Prop :=
  (((A.card : ℤ) + 1) * p ≤ E.toFFJ.s j ∧
      (E.toFFJ.running A (E.toFFJ.s j)).card < E.numMachines ∧ next = insert j A) ∨
  ((E.toFFJ.s j < ((A.card : ℤ) + 1) * p ∨
      E.numMachines ≤ (E.toFFJ.running A (E.toFFJ.s j)).card) ∧
    ∃ c ∈ insert j A, (∀ i ∈ insert j A, (E.d i : ℤ) ≤ (E.d c : ℤ)) ∧
      next = (insert j A).erase c)

variable (E) in
/-- **Lemma 4's invariant.** `A` is a feasible solution for the prefix `J_k` that dominates
every feasible solution of `J_k`. -/
def Dominating (A : Finset (Fin E.n)) (k : ℕ) : Prop :=
  E.toFFJ.Feasible A ∧ A ⊆ E.pre k ∧
    ∀ B : Finset (Fin E.n), B ⊆ E.pre k → E.toFFJ.Feasible B → E.toFFJ.SDom A B

/-- The greedy starts dominating: at `k = 0` the only feasible solution is `∅`. -/
theorem dominating_zero : E.Dominating ∅ 0 := by
  refine ⟨?_, by simp, ?_⟩
  · exact (E.toFFJ.feasible_iff ∅).mpr
      ⟨fun x hx => absurd hx (Finset.notMem_empty x),
        ⟨fun _ => 0, fun x hx => absurd hx (Finset.notMem_empty x),
          fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩
  · intro B hB _
    have : B = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by
      have := mem_pre.mp (hB hx); omega)
    subst this
    intro t
    exact le_rfl

/-! ## 3. The induction step -/

/-- **Lemma 4, one step.** Every legal greedy successor of a dominating solution for `J_k`
is a dominating solution for `J_{k+1}`. -/
theorem lemma4_step {p : ℕ} (hp : ∀ i, E.p i = p) (hq : ∀ i, 0 < E.q i)
    {A next : Finset (Fin E.n)} {k : ℕ} (hk : k < E.n)
    (hinv : E.Dominating A k) (hstep : E.GreedyStep p A next ⟨k, hk⟩) :
    E.Dominating next (k + 1) := by
  classical
  obtain ⟨hAfeas, hAsub, hAdom⟩ := hinv
  obtain ⟨hApre, hAsch⟩ := (E.toFFJ.feasible_iff A).mp hAfeas
  set j : Fin E.n := ⟨k, hk⟩ with hjdef
  have hjnot : j ∉ E.pre k := by simp [hjdef]
  have hjA : j ∉ A := fun hc => hjnot (hAsub hc)
  have hAlast : ∀ i ∈ A, E.toFFJ.s i ≤ E.toFFJ.s j := fun i hi =>
    s_le_of_mem_pre hk (by rw [pre_succ hk]; exact Finset.mem_insert_of_mem (hAsub hi))
  -- the two facts every feasible `B ⊆ J_{k+1}` supplies
  have hBerase : ∀ {B : Finset (Fin E.n)}, B ⊆ E.pre (k + 1) → B.erase j ⊆ E.pre k := by
    intro B hB x hx
    obtain ⟨hxj, hxB⟩ := Finset.mem_erase.mp hx
    have := mem_pre.mp (hB hxB)
    refine mem_pre.mpr ?_
    rcases Nat.lt_succ_iff_lt_or_eq.mp this with h | h
    · exact h
    · exact absurd (Fin.ext h) hxj
  have hBdom : ∀ {B : Finset (Fin E.n)}, B ⊆ E.pre (k + 1) → E.toFFJ.Feasible B →
      E.toFFJ.SDom A (B.erase j) := fun hB hF =>
    hAdom _ (hBerase hB)
      (FFJ.Feasible.subset (h := hF) (hsub := Finset.erase_subset _ _))
  rcases hstep with ⟨hrule1, hrule2, rfl⟩ | ⟨hfired, c, hcmem, hcmax, rfl⟩
  · -- neither rule fires: job `j` simply joins
    refine ⟨FFJ.feasible_insert_of_uniform hp hq hjA hAfeas hAlast hrule1 hrule2, ?_, ?_⟩
    · rw [pre_succ hk]
      exact Finset.insert_subset_insert _ hAsub
    · exact fun B hB hF => FFJ.sdom_insert hjA (hBdom hB hF)
  · -- a rule fires: the largest due date leaves
    have hcardB : ∀ {B : Finset (Fin E.n)}, B ⊆ E.pre (k + 1) → E.toFFJ.Feasible B →
        B.card ≤ A.card := by
      intro B hB hF
      obtain ⟨hBpre, hBsch⟩ := (E.toFFJ.feasible_iff B).mp hF
      rcases hfired with h1 | h2
      · exact FFJ.card_le_of_rule1 hp hBpre (fun i hi => s_le_of_mem_pre hk (hB hi)) h1
      · exact FFJ.card_le_of_rule2 hq hAlast
          (fun i hi => s_le_of_mem_pre hk (hB (Finset.mem_of_mem_erase hi)))
          (hBdom hB hF) hBsch h2
    have hsub : (insert j A).erase c ⊆ E.pre (k + 1) := by
      refine le_trans (Finset.erase_subset _ _) ?_
      rw [pre_succ hk]
      exact Finset.insert_subset_insert _ hAsub
    by_cases hcj : c = j
    · -- the new job has the largest due date: the greedy keeps `A`
      subst hcj
      rw [Finset.erase_insert hjA]
      refine ⟨hAfeas,
        hAsub.trans (by rw [pre_succ hk]; exact Finset.subset_insert _ _), ?_⟩
      exact fun B hB hF =>
        FFJ.sdom_drop (fun i hi => hcmax i (Finset.mem_insert_of_mem hi))
          (hcardB hB hF) (hBdom hB hF)
    · -- an old job leaves; `A` is nonempty because it contains `c`
      have hcA : c ∈ A := (Finset.mem_insert.mp hcmem).resolve_left hcj
      have hswap : (insert j A).erase c = insert j (A.erase c) :=
        Finset.erase_insert_of_ne (Ne.symm hcj)
      have hcount : (A.card : ℤ) * p ≤ E.toFFJ.s j :=
        FFJ.card_mul_le_of_feasible hp hApre hAlast ⟨c, hcA⟩
      have hdjc : (E.d j : ℤ) ≤ (E.d c : ℤ) := hcmax j (Finset.mem_insert_self _ _)
      rw [hswap]
      refine ⟨FFJ.feasible_swap_of_uniform hp hq hjA hcA hAfeas hAlast hdjc hcount, ?_, ?_⟩
      · rw [← hswap]; exact hsub
      · exact fun B hB hF =>
          FFJ.sdom_swap hjA hcA (fun i hi => hcmax i (Finset.mem_insert_of_mem hi)) hdjc
            (hcardB hB hF) (hBdom hB hF)

/-! ## 4. Lemma 4, and what it gives Theorem 4 -/

/-- **Lemma 4.** Every run of Section 6.1's greedy dominates, at each prefix, all feasible
solutions of that prefix. -/
theorem lemma4 {p : ℕ} (hp : ∀ i, E.p i = p) (hq : ∀ i, 0 < E.q i)
    (S : ℕ → Finset (Fin E.n)) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < E.n, E.GreedyStep p (S k) (S (k + 1)) ⟨k, hk⟩) :
    ∀ k ≤ E.n, E.Dominating (S k) k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0]
    exact dominating_zero
  | succ k ih =>
    intro hk
    exact lemma4_step hp hq (by omega) (ih (by omega)) (hrun k (by omega))

/-- **Theorem 4's first bullet, its mathematical content.** The greedy's output is a
feasible solution of maximum cardinality — which, unweighted, is an optimal solution.

The `O(n log n)` bound the paper attaches to it is a running-time claim about a particular
implementation (a binary heap over the `2n` endpoints) and is not stated here; see
`README.md` on why such claims are vacuous in this cost model. -/
theorem greedy_card_max {p : ℕ} (hp : ∀ i, E.p i = p) (hq : ∀ i, 0 < E.q i)
    (S : ℕ → Finset (Fin E.n)) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < E.n, E.GreedyStep p (S k) (S (k + 1)) ⟨k, hk⟩) :
    E.toFFJ.Feasible (S E.n) ∧
      ∀ B : Finset (Fin E.n), E.toFFJ.Feasible B → B.card ≤ (S E.n).card := by
  obtain ⟨hfeas, -, hdom⟩ := lemma4 hp hq S h0 hrun E.n le_rfl
  refine ⟨hfeas, fun B hB => FFJ.card_le_of_sdom (hdom B ?_ hB)⟩
  rw [pre_n]
  exact Finset.subset_univ _

end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
