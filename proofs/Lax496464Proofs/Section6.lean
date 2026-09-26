import Lax496464Proofs.EstBridge
import Lax496464Proofs.Model.Lemma4_Greedy
import Lax496464Proofs.Model.Section6_ILP
import Lax496464.Lemma4
import Lax496464.Lemma5

/-!
# Section 6: uniform preprocessing times

With `p_j = p` for every job, Condition 1 stops depending on *which* jobs are selected and
counts only *how many*, and the problem becomes tractable in two different ways.

Section 6.1's greedy walks the jobs in earliest-start-time order, adding each one and, when
either stopping rule fires, dropping a job of largest due date. Lemma 4 is the invariant
that makes it optimal: after `k` steps the set held *dominates* every feasible subset of the
first `k` jobs, in the sense that below every threshold it has at least as many due dates.

Section 6.2 writes the problem as an integer program — constraint (6) is Condition 1 read
as a count, constraint (7) is Condition 2 tested at each start time — and observes that on a
*proper* instance the constraint matrix has the consecutive ones property, hence is totally
unimodular, so the linear relaxation is integral.

## An erratum in Lemma 4's proof

The paper's proof of Lemma 4 drops "a job with the largest due date" from `A ∪ {j}` and
argues that domination is preserved. That step needs the dropped job to have the largest due
date in `A ∪ {j}` *and* the domination inequality to be read at every threshold, not only at
the thresholds where the two sets differ; the printed argument checks it at one threshold.
`Model/Section6_Greedy.lean` proves the three cases separately (`sdom_insert`, `sdom_swap`,
`sdom_drop`), which is what `greedy_dominating` rests on.
-/

namespace Lax496464Proofs.Section6

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Greedy Lax496464.ProperInstances
open Lax496464.IntegerProgram Bridge EstBridge FlexFlowJIT FlexFlowJIT.EstFFJ
open _root_.Matrix Lax496464Proofs.Matrix


variable {I : Instance}

/-- The concepts' constraint matrix is the development's. Both are defined by cases on the
row, and a matcher does not reduce under `Iff.rfl`, so the equality is spelled out. -/
theorem matrix_eq (hest : EstOrdered I) : matrix I = (estModel I hest).ilpMatrix := by
  funext r i; cases r <;> rfl

theorem rhs_eq (hest : EstOrdered I) (p : ℕ) : rhs I p = (estModel I hest).ilpRhs p := by
  funext r; cases r <;> rfl

theorem indicator_eq (hest : EstOrdered I) (Z : Finset I.Job) :
    indicator I Z = EstFFJ.indicator (E := estModel I hest) Z := rfl

/--
---
conclusion: Lax496464.ConsecutiveOnes.isTotallyUnimodular
---
Fulkerson–Gross. Sort the chosen columns, which changes the determinant only by a sign;
each row of the sorted submatrix is then an interval of ones, and the determinant of such a
matrix is `0`, `1` or `−1` by induction on subtracting consecutive rows.
-/
theorem isTotallyUnimodular {m n : Type*} [LinearOrder n] {A : _root_.Matrix m n ℤ}
    (h : Lax496464.ConsecutiveOnes.HasConsecutiveOnes A) : A.IsTotallyUnimodular :=
  Lax496464Proofs.Matrix.HasConsecutiveOnes.isTotallyUnimodular h

/--
---
conclusion: Lax496464.Lemma4.greedy_dominating
---
Lemma 4, by induction along the run. Three cases: the job is added, the job is added and
another dropped, or the job is added and itself dropped again.
-/
theorem greedy_dominating (I : Instance) (hest : EstOrdered I) {p : ℕ}
    (hp : ∀ i : I.Job, I.p i = p) (hq : ∀ i : I.Job, 0 < I.q i)
    (S : ℕ → Finset I.Job) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < I.jobs, Step I p (S k) (S (k + 1)) ⟨k, hk⟩) :
    ∀ k ≤ I.jobs,
      Feasible I (S k) ∧ S k ⊆ firstJobs I k ∧
        ∀ B : Finset I.Job, B ⊆ firstJobs I k → Feasible I B → SDom I (S k) B := by
  intro k hk
  obtain ⟨hfeas, hsub, hdom⟩ := (estModel I hest).lemma4 hp hq S h0 hrun k hk
  exact ⟨(feasible_iff_model _).mpr hfeas, hsub,
    fun B hB hfB => hdom B hB ((feasible_iff_model B).mp hfB)⟩

/--
---
conclusion: Lax496464.Lemma4.greedy_card_max
---
Domination at the last prefix is domination against every feasible set, and a dominating
set is at least as large.
-/
theorem greedy_card_max (I : Instance) (hest : EstOrdered I) {p : ℕ}
    (hp : ∀ i : I.Job, I.p i = p) (hq : ∀ i : I.Job, 0 < I.q i)
    (S : ℕ → Finset I.Job) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < I.jobs, Step I p (S k) (S (k + 1)) ⟨k, hk⟩) :
    Feasible I (S I.jobs) ∧
      ∀ B : Finset I.Job, Feasible I B → B.card ≤ (S I.jobs).card := by
  obtain ⟨hfeas, hmax⟩ := (estModel I hest).greedy_card_max hp hq S h0 hrun
  exact ⟨(feasible_iff_model _).mpr hfeas,
    fun B hB => hmax B ((feasible_iff_model B).mp hB)⟩

/--
---
conclusion: Lax496464.Lemma5.ilp_correct
---
With a common preprocessing time, the prefix sum of constraint (6) counts the selected jobs
up to `j` and Condition 1 becomes `|{i ≤ j} ∩ Z| ≤ ⌊s_j/p⌋`; constraint (7) is Condition 2
tested at the start times, which is enough by the depth characterization.
-/
theorem ilp_correct (I : Instance) (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p)
    (hp0 : 0 < p) (hq : ∀ i : I.Job, 0 < I.q i) (hs : ∀ j : I.Job, 0 ≤ s j)
    (Z : Finset I.Job) :
    Feasible I Z ↔ ∀ r, (matrix I *ᵥ indicator I Z) r ≤ rhs I p r := by
  rw [matrix_eq hest, rhs_eq hest, indicator_eq hest]
  exact (feasible_iff_model Z).trans ((estModel I hest).ilp_correct hp hp0 hq hs Z)

/--
---
conclusion: Lax496464.Lemma5.ilp_optimum
---
A `0/1` vector is the indicator of the set it marks, and the objective is that set's weight.
-/
theorem ilp_optimum (I : Instance) (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p)
    (hp0 : 0 < p) (hq : ∀ i : I.Job, 0 < I.q i) (hs : ∀ j : I.Job, 0 ≤ s j) (W : ℕ) :
    (∃ x : I.Job → ℤ, (∀ i, x i = 0 ∨ x i = 1) ∧
        (∀ r, (matrix I *ᵥ x) r ≤ rhs I p r) ∧ ∑ i, (I.w i : ℤ) * x i = W) ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W := by
  rw [matrix_eq hest, rhs_eq hest]
  refine ((estModel I hest).ilp_optimum hp hp0 hq hs W).trans (exists_congr fun Z => ?_)
  exact and_congr_left fun _ => (feasible_iff_model Z).symm

/--
---
conclusion: Lax496464.Lemma5.lemma5
---
Rows `(6)` are prefixes of the index order, so their ones are consecutive outright. Rows
`(7)` list the jobs alive at `s_j`, and on a proper instance those are consecutive in the
earliest-start-time order — an interval strictly inside another cannot occur, so the alive
set at any instant is a block.
-/
theorem lemma5 (I : Instance) (hest : EstOrdered I) (h : Proper I) :
    Lax496464.ConsecutiveOnes.HasConsecutiveOnes (matrix I) := by
  rw [matrix_eq hest]; exact (estModel I hest).lemma5 h

/--
---
conclusion: Lax496464.Lemma5.matrix_isTotallyUnimodular
---
Lemma 5 followed by Fulkerson–Gross.
-/
theorem matrix_isTotallyUnimodular (I : Instance) (hest : EstOrdered I) (h : Proper I) :
    (matrix I).IsTotallyUnimodular := by
  rw [matrix_eq hest]
  exact Lax496464Proofs.Matrix.HasConsecutiveOnes.isTotallyUnimodular ((estModel I hest).lemma5 h)

end Lax496464Proofs.Section6
