import Lax496464Proofs.Ram.F5WRun

/-!
# Theorem 5, endpoint sweep: the running time statement

`prog5w` solves, on the words that present an instance and an accuracy `e`, the function
`x ↦ [fptasOut I e]`, within `cost5wX`, at every word length at which the admissibility clauses
hold; the scheme's guarantee follows from `F5Math.delivers_fptasOut`.
-/

namespace Lax496464Proofs.F5WFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QFinal Lax496464Proofs.F5WRun Lax496464Proofs.F5WRest
  Lax496464Proofs.F5WOk
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts fits_mono)
open Lax496464Proofs.Ram.W3Sweep (Kcore)

/-- Words that present an instance and an accuracy, with positive processing times, that fit at
word length `w` with constant `c`, whose total weight and sweep table are words. -/
def Dom5W (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ ApproxInstances ∧ Fits c w x ∧ c * sumwt x ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j) ∧
    c * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) ≤ 2 ^ w}

set_option maxHeartbeats 8000000 in
open Classical in
theorem prog5w_solves (cc w : ℕ) :
    Solves L5W prog5w (Dom5W cc w) f5 (fun x => bound x (T5w x)) cost5wX where
  ok := prog5w_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxAI, -, -, hxQ, -⟩ := hx
    obtain ⟨σ', hr, hout⟩ := prog5w_run hxAI hxQ
    exact ⟨ext5w x, σ', hr, hout⟩

/-! ## The arithmetic -/

theorem const_L5W : Layout.const L5W = 10 := rfl
theorem fconst_L5W : const L5W = 2 * (12 + 2 + 60 + 12) := by decide

/-- The constant. -/
def cc5w : ℕ := 200000

theorem hne5w (w : ℕ) : ∀ x ∈ Dom5W cc5w w, x ≠ [] := by
  rintro x ⟨⟨I, e, y, hxy, he, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits5w (w : ℕ) : ∀ x ∈ Dom5W cc5w w, Fits (const L5W) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact fits_mono hxFits (by rw [fconst_L5W]; unfold cc5w; omega)

theorem tab_arith5 (κ c pw len M P Q S : ℕ) (hc : 160 * κ ≤ c) (hP : P ≤ 2 * Q)
    (h1 : c * Q ≤ pw) (h2 : c * (len + M + 1) ≤ pw) (h3 : c * S ≤ pw) :
    κ * (P + 8 * M + 40 + S) ≤ pw := by
  have a1 : 4 * (κ * P) ≤ pw := by
    have e1 : κ * P ≤ κ * (2 * Q) := Nat.mul_le_mul_left _ hP
    have e2 : 4 * (κ * (2 * Q)) = (8 * κ) * Q := by ring
    have e3 : (8 * κ) * Q ≤ c * Q := Nat.mul_le_mul_right _ (by omega)
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
  have e : κ * (P + 8 * M + 40 + S) = κ * P + κ * (8 * M + 40) + κ * S := by ring
  rw [e]
  omega

theorem dom5w_facts {x : List ℕ} (hx : x ∈ ApproxInstances) :
    jobCount x ≤ x.length ∧
      2 ^ widthOf x * (thrX x + 1) ≤
        2 * ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) ∧ 1 ≤ thrX x + 1 := by
  obtain ⟨I, e, y, hxy, he, hEnc⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := e) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hthr : threshold x = e := by
    rw [hxy]; exact (Lax496464Proofs.Ram.W3Final.threshold_eq' e hEnc)
  refine ⟨by rw [hjc, hxlen]; omega, ?_, by omega⟩
  have h1 := thr_le (jobCount x) e
  have hT : thrX x = 2 * e * jobCount x * jobCount x := by unfold thrX; rw [hthr]
  rw [hT, hthr]
  calc 2 ^ widthOf x * (2 * e * jobCount x * jobCount x + 1)
      ≤ 2 ^ widthOf x * (2 * ((jobCount x + 1) ^ 2 * (e + 1))) := Nat.mul_le_mul_left _ h1
    _ = 2 * ((jobCount x + 1) ^ 2 * (e + 1) * 2 ^ widthOf x) := by ring

theorem hTab5w (w : ℕ) : ∀ x ∈ Dom5W cc5w w, const L5W * T5w x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne5w w x hx
  have hfa := dom5w_facts hx.1
  obtain ⟨-, hxFits, hsum, -, hbig⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  obtain ⟨-, hP, -⟩ := hfa
  unfold T5w
  rw [fconst_L5W]
  have hQ : cc5w * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
      cc5w * ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) * (jobCount x + 1) := by
    ring
  rw [hQ] at hbig
  have hbig' : cc5w * ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) ≤ 2 ^ w :=
    le_trans (Nat.le_mul_of_pos_right _ (by omega)) hbig
  exact tab_arith5 (2 * (12 + 2 + 60 + 12)) cc5w (2 ^ w) x.length (maxEntry x)
    (2 ^ widthOf x * (thrX x + 1))
    ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) (sumwt x)
    (by unfold cc5w; omega) hP hbig' hf hsum

theorem cost_arith5 (n w1 p S sK : ℕ) (hS : n + 1 ≤ S) (hw1 : 1 ≤ w1) (hp : 1 ≤ p)
    (hsK : sK ≤ 390 * S) :
    10 * ((2 * sK + 1000 * n + 2000) + (((44 * n + 10) + 20 + (44 * n + 10) + 10) +
      ((54 * n + 24 * w1 + 120) + ((108 * (p * w1) + 306) * (2 * n) + 6)) + (34 * w1 + 10) + 12))
      + 1 ≤ 60000 * (w1 * p * (n + 1)) + 60000 * S := by
  have e1 : (108 * (p * w1) + 306) * (2 * n) = 216 * (p * w1 * n) + 612 * n := by ring
  have e2 : w1 * p * (n + 1) = p * w1 * n + p * w1 := by ring
  have hpw : 1 ≤ p * w1 := Nat.mul_le_mul hp hw1
  have h3 : w1 ≤ p * w1 := Nat.le_mul_of_pos_left _ hp
  have h4 : n ≤ p * w1 * n := Nat.le_mul_of_pos_left _ hpw
  rw [e1, e2]
  generalize p * w1 * n = R at *
  generalize p * w1 = Z at *
  omega

theorem hT5w (w : ℕ) : ∀ x ∈ Dom5W cc5w w, Layout.const L5W * cost5wX x + 1 ≤
    cc5w * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) +
      cc5w * sortCost x := by
  intro x hx
  have hfa := dom5w_facts hx.1
  obtain ⟨hnl, hP, hw1⟩ := hfa
  have hsK := Lax496464Proofs.Ram.Sort.sortK_le 90 (jobCount x) x.length hnl
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  have hS : jobCount x + 1 ≤ sortCost x := by
    rw [hsc]
    calc jobCount x + 1 ≤ x.length + 1 := by omega
      _ ≤ (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
  have hp : 1 ≤ 2 ^ widthOf x := Nat.one_le_two_pow
  have key := cost_arith5 (jobCount x) (thrX x + 1) (2 ^ widthOf x) (sortCost x)
    (Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x)) hS hw1 hp (by rw [← hsc] at hsK; omega)
  unfold cost5wX cost5w Kcore
  rw [const_L5W]
  have hQ : cc5w * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
      cc5w * (((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) * (jobCount x + 1)) := by
    ring
  rw [hQ]
  have h1 : (thrX x + 1) * 2 ^ widthOf x * (jobCount x + 1) ≤
      2 * (((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) * (jobCount x + 1)) := by
    have := Nat.mul_le_mul_right (jobCount x + 1) hP
    rw [Nat.mul_comm (thrX x + 1) (2 ^ widthOf x)]
    calc 2 ^ widthOf x * (thrX x + 1) * (jobCount x + 1)
        ≤ 2 * ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) * (jobCount x + 1) := this
      _ = _ := by ring
  have e : (thrX x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
      (thrX x + 1) * 2 ^ widthOf x * (jobCount x + 1) := rfl
  have hcc : 200000 = cc5w := rfl
  generalize ((jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x) * (jobCount x + 1) = Qn at *
  generalize (thrX x + 1) * 2 ^ widthOf x * (jobCount x + 1) = Wn at *
  generalize sortCost x = Sc at *
  unfold cc5w at *
  omega

/-! ## From computing the number to approximating -/

open Classical in
/--
---
conclusion: Lax496464.Theorem5.theorem5_byWidth
---
The endpoint sweep of Section 4 as a word RAM approximation scheme.  Read the instance and the
accuracy `e` (in the place of the threshold), sort the jobs by start time, build the sorted arrays
and the due-date order (as in the exact program), zero the weight of every unfit job, take
`k = max 1 (w_max' / (e n))`, replace every weight `w ≥ 1` by `(w - 1)/k + 1`, set the threshold
`W = 2 e n²`, run the exact endpoint sweep (`W3Sweep.core`, unchanged) on the rescaled weights,
scan the finished row `TB[0 … W]` for the last finite cell `W'`, and write `k (W' - n)` if `k > 1`
and `W'` otherwise (`F5Math.fptasOut`).  The cost is that of the exact program with threshold
`2 e n²`, that is `O((n+1)² (e+1) · 2^ω · (n+1))`, plus the sort; the guarantee is
`F5Math.fptas_value`.
-/
theorem theorem5_byWidth_proved : ∃ (prog : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ApproximatesInTime w prog
      {x | x ∈ ApproxInstances ∧ Fits c w x ∧
        c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j) ∧
        c * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x *
          (jobCount x + 1) ≤ 2 ^ w}
      (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) * 2 ^ widthOf x *
        (jobCount x + 1) + c * sortCost x) :=
  ⟨compileProgram L5W prog5w, cc5w, fun w =>
    approximatesInTime_of_computes
      (computesInTime_of_solves_fits (hne5w w) (hfits5w w) (hTab5w w) (prog5w_solves cc5w w)
        (hT5w w))
      (fun x hx => delivers_f5 x hx.1)⟩

example : type_of% @Lax496464.Theorem5.theorem5_byWidth := theorem5_byWidth_proved

end Lax496464Proofs.F5WFinal

open Lax496464Proofs.F5WFinal in
#print axioms theorem5_byWidth_proved
