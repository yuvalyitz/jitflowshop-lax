import Lax496464Proofs.Ram.F5MBound
import Lax496464Proofs.Ram.F5WFinal

/-!
# Theorem 5, table of Section 3: the running time statement

`prog5m` solves, on the words that present an instance and an accuracy `e`, the function
`x ↦ [fptasOut I e]`, within `cost5mX`, at every word length at which the admissibility clauses
hold; the scheme's guarantee follows from `F5Math.delivers_fptasOut`.
-/

namespace Lax496464Proofs.F5MFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QFinal Lax496464Proofs.F5MRun Lax496464Proofs.F5MRest
  Lax496464Proofs.F5MOk Lax496464Proofs.F5MBound
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts fits_mono)

/-- Words that present an instance and an accuracy, with positive processing times, that fit at
word length `w` with constant `c`, whose total weight and table are words. -/
def Dom5M (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ ApproxInstances ∧ Fits c w x ∧ c * sumwt x ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j) ∧
    c * (jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w}

set_option maxHeartbeats 8000000 in
open Classical in
theorem prog5m_solves (cc w : ℕ) :
    Solves L5M prog5m (Dom5M cc w) f5 (fun x => bound x (T5m x)) cost5mX where
  ok := prog5m_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxAI, -, -, hxQ, -⟩ := hx
    obtain ⟨σ', hr, hout⟩ := prog5m_run hxAI hxQ
    exact ⟨ext5m x, σ', hr, hout⟩

/-! ## The arithmetic -/

theorem const_L5M : Layout.const L5M = 10 := rfl
theorem fconst_L5M : const L5M = 2 * (12 + 2 + 83 + 11) := by decide

/-- The constant. -/
def cc5m : ℕ := 200000

theorem hne5m (w : ℕ) : ∀ x ∈ Dom5M cc5m w, x ≠ [] := by
  rintro x ⟨⟨I, e, y, hxy, he, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits5m (w : ℕ) : ∀ x ∈ Dom5M cc5m w, Fits (const L5M) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact fits_mono hxFits (by rw [fconst_L5M]; unfold cc5m; omega)

theorem tab_arith5m (κ c pw len M P Q S : ℕ) (hc : 160 * κ ≤ c) (hP : P ≤ 2 * Q)
    (h1 : c * Q ≤ pw) (h2 : c * (len + M + 1) ≤ pw) (h3 : c * S ≤ pw) :
    κ * (8 * M + 4 * P + 40 + S) ≤ pw := by
  have a1 : 4 * (4 * (κ * P)) ≤ pw := by
    have e1 : κ * P ≤ κ * (2 * Q) := Nat.mul_le_mul_left _ hP
    have e2 : 16 * (κ * (2 * Q)) = (32 * κ) * Q := by ring
    have e3 : (32 * κ) * Q ≤ c * Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have a2 : 4 * (κ * (8 * M + 40)) ≤ pw := by
    have e1 : 4 * (κ * (8 * M + 40)) ≤ (160 * κ) * (len + M + 1) := by
      have : 4 * (κ * (8 * M + 40)) = κ * (32 * M + 160) := by ring
      rw [this]
      have : (160 * κ) * (len + M + 1) = κ * (160 * len + 160 * M + 160) := by ring
      rw [this]
      exact Nat.mul_le_mul_left _ (by omega)
    have e2 : (160 * κ) * (len + M + 1) ≤ c * (len + M + 1) := Nat.mul_le_mul_right _ hc
    omega
  have a3 : 4 * (κ * S) ≤ pw := by
    have e1 : (4 * κ) * S ≤ c * S := Nat.mul_le_mul_right _ (by omega)
    have : 4 * (κ * S) = (4 * κ) * S := by ring
    omega
  have e : κ * (8 * M + 4 * P + 40 + S) = 4 * (κ * P) + κ * (8 * M + 40) + κ * S := by ring
  rw [e]
  omega

theorem dom5m_facts {x : List ℕ} (hx : x ∈ ApproxInstances) :
    jobCount x ≤ x.length ∧
      (thrX x + 1) * (jobCount x + 1) ^ machineCount x ≤
        2 * ((jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x) := by
  obtain ⟨I, e, y, hxy, he, hEnc⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := e) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hthr : threshold x = e := by
    rw [hxy]; exact (Lax496464Proofs.Ram.W3Final.threshold_eq' e hEnc)
  refine ⟨by rw [hjc, hxlen]; omega, ?_⟩
  have h1 := thr_le (jobCount x) e
  have hT : thrX x = 2 * e * jobCount x * jobCount x := by unfold thrX; rw [hthr]
  rw [hT, hthr]
  calc (2 * e * jobCount x * jobCount x + 1) * (jobCount x + 1) ^ machineCount x
      ≤ (2 * ((jobCount x + 1) ^ 2 * (e + 1))) * (jobCount x + 1) ^ machineCount x :=
        Nat.mul_le_mul_right _ h1
    _ = 2 * ((jobCount x + 1) ^ 2 * (e + 1) * (jobCount x + 1) ^ machineCount x) := by ring

theorem hTab5m (w : ℕ) : ∀ x ∈ Dom5M cc5m w, const L5M * T5m x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne5m w x hx
  have hfa := dom5m_facts hx.1
  obtain ⟨-, hxFits, hsum, -, hbig⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  obtain ⟨-, hP⟩ := hfa
  unfold T5m
  rw [fconst_L5M]
  have hQ : cc5m * (jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x =
      cc5m * ((jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x) := by
    ring
  rw [hQ] at hbig
  exact tab_arith5m (2 * (12 + 2 + 83 + 11)) cc5m (2 ^ w) x.length (maxEntry x)
    ((thrX x + 1) * (jobCount x + 1) ^ machineCount x)
    ((jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x) (sumwt x)
    (by unfold cc5m; omega) hP hbig hf hsum

theorem hT5m (w : ℕ) : ∀ x ∈ Dom5M cc5m w, Layout.const L5M * cost5mX x + 1 ≤
    cc5m * (jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x +
      cc5m * sortCost x := by
  intro x hx
  have hfa := dom5m_facts hx.1
  obtain ⟨hnl, hP⟩ := hfa
  have hb := cost5m_le (m := machineCount x) (W := thrX x) hnl
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  rw [const_L5M]
  unfold cost5mX
  have hQ : cc5m * (jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x =
      cc5m * ((jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x) := by
    ring
  rw [hQ, hsc]
  generalize (jobCount x + 1) ^ 2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x = Q at *
  generalize (thrX x + 1) * (jobCount x + 1) ^ machineCount x = PP at *
  generalize (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) = Sc at *
  unfold cc5m
  omega

/-! ## From computing the number to approximating -/

open Classical in
/--
---
conclusion: Lax496464.Theorem5.theorem5_byMachines
---
The table of Section 3 as a word RAM approximation scheme.  Read the instance and the accuracy `e`
(in the place of the threshold), sort the jobs by start time, build the sorted arrays (as in the
exact program), zero the weight of every unfit job, take `k = max 1 (w_max' / (e n))`, replace
every weight `w ≥ 1` by `(w - 1)/k + 1`, set the threshold `W = 2 e n²`, run the exact table
program of Theorem 2 (`D2Core.core2`, unchanged) on the rescaled weights, scan the finished column of
the first `m` indices for the last non-zero cell `W'` (for no job or no machine, `W' = 0`), and write
`k (W' - n)` if `k > 1` and `W'` otherwise (`F5Math.fptasOut`).  The cost is that of the exact
program with threshold `2 e n²`, that is `O((n+1)² (e+1) (n+1)^m)`, plus the sort; the guarantee is
`F5Math.fptas_value`.
-/
theorem theorem5_byMachines_proved : ∃ (prog : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ApproximatesInTime w prog
      {x | x ∈ ApproxInstances ∧ Fits c w x ∧
        c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j) ∧
        c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
          (jobCount x + 1) ^ machineCount x ≤ 2 ^ w}
      (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
        (jobCount x + 1) ^ machineCount x + c * sortCost x) :=
  ⟨compileProgram L5M prog5m, cc5m, fun w =>
    approximatesInTime_of_computes
      (computesInTime_of_solves_fits (hne5m w) (hfits5m w) (hTab5m w) (prog5m_solves cc5m w)
        (hT5m w))
      (fun x hx => delivers_f5 x hx.1)⟩

example : type_of% @Lax496464.Theorem5.theorem5_byMachines := theorem5_byMachines_proved

end Lax496464Proofs.F5MFinal

open Lax496464Proofs.F5MFinal in
#print axioms theorem5_byMachines_proved
