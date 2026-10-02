import Lax496464Proofs.Ram.T4Tail

/-!
# Theorem 4's Machine, Part 8: the Whole Program, Correct

`prog4` reads the instance, sorts the jobs by start time, and runs the greedy of Section 6.1.
-/

namespace Lax496464Proofs.Ram.T4Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Decode (readInstance)
open Lax496464Proofs.Ram.EstSort (estSortCom)
open Lax496464Proofs.Ram.BuildSorted (buildSorted)
open Lax496464Proofs.Ram.T4Tail Lax496464Proofs.Ram.T4Front
open Lax496464Proofs.Ram.Dp1 (pv qv dv)

/-- **The whole program.** -/
def prog4 : Com :=
  .seq readInstance
    (.seq (.read "W")
      (.seq (.assign "en" (V "n"))
        (.seq (.assign "sn" (V "n"))
          (.seq estSortCom (.seq buildSorted tail4)))))

/-- Glue the front end's `Run` to the tail's `Run` (the two nestings differ). -/
theorem run_prog4_of_parts {B : ℕ} {σA σ6 σF : Env} {K1 K2 : ℕ}
    (h1 : Run B (.seq readInstance (.seq (.read "W") (.seq (.assign "en" (V "n"))
      (.seq (.assign "sn" (V "n")) (.seq estSortCom buildSorted))))) σA σ6 K1)
    (h2 : Run B tail4 σ6 σF K2) : Run B prog4 σA σF (K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  cases hbs1 with
  | seq hRI hbs1' =>
    cases hbs1' with
    | seq hRW hbs1'' =>
      cases hbs1'' with
      | seq hAE hbs1''' =>
        cases hbs1''' with
        | seq hAS hbs1'''' =>
          cases hbs1'''' with
          | seq hES hBS =>
            refine ⟨_, ?_, BigStepB.seq hRI (BigStepB.seq hRW (BigStepB.seq hAE (BigStepB.seq hAS
              (BigStepB.seq hES (BigStepB.seq hBS hbs2)))))⟩
            omega

open Lax496464Proofs.Ram.Reduction (encodesDecisionInstance_unique)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The whole program, correct.** `prog4` decides `Yes x` for a decision word of an instance
with a common preprocessing time, unit weights and positive processing times. -/
theorem prog4_spec {x : List ℕ} {I : Instance} {W p : ℕ}
    (hdec : EncodesDecisionInstance x I W) (hpu : ∀ j : I.Job, I.p j = p)
    (hp0 : I.jobs = 0 → p = 0) (hw1 : ∀ j : I.Job, I.w j = 1) (hqpos : ∀ j : I.Job, 0 < I.q j)
    {B : ℕ} (hB2 : 2 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 8 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B) (hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B)
    (hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B) (hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B)
    (hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B) (hWB : W < B) (hpB : p < B)
    (hmB : I.machines < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1 ∧
        σ.arrs "TX" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0 ∧
        σ.arrs "TY" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0)
      prog4 (fun _ σ' => σ'.out = if Yes x then [1] else [0])
      (Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000 + tailK I.jobs) := by
  have hYesIff : Yes x ↔ HasWeight I W := by
    constructor
    · rintro ⟨I', W', hdec', hHW'⟩
      obtain ⟨hI, hW⟩ := encodesDecisionInstance_unique hdec' hdec
      exact hI ▸ hW ▸ hHW'
    · intro hHW
      exact ⟨I, W, hdec, hHW⟩
  refine Spec.of_exists fun σ0 hP0 => ?_
  obtain ⟨hP1, hP2⟩ : (σ0.inp = x ∧ σ0.out = [] ∧ (σ0.arrs "A").length = 4 * I.jobs ∧
        (σ0.arrs "SA").length = I.jobs ∧ (σ0.arrs "SB").length = I.jobs ∧
        (σ0.arrs "PS").length = I.jobs ∧ (σ0.arrs "QS").length = I.jobs ∧
        (σ0.arrs "DS").length = I.jobs ∧ (σ0.arrs "NX").length = I.jobs ∧
        (σ0.arrs "CC").length = I.jobs + 1 ∧ (σ0.arrs "PC").length = I.jobs + 1) ∧
      (σ0.arrs "TX" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0 ∧
        σ0.arrs "TY" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0) :=
    ⟨⟨hP0.1, hP0.2.1, hP0.2.2.1, hP0.2.2.2.1, hP0.2.2.2.2.1, hP0.2.2.2.2.2.1,
      hP0.2.2.2.2.2.2.1, hP0.2.2.2.2.2.2.2.1, hP0.2.2.2.2.2.2.2.2.1, hP0.2.2.2.2.2.2.2.2.2.1,
      hP0.2.2.2.2.2.2.2.2.2.2.1⟩, hP0.2.2.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨σ6, hr6, hQ6, hfv6, hfa6, -, -⟩ :=
    (sortSetup4_spec hdec hpu hw1 hqpos hB2 hxB (by omega) hpqB hdq hd2B hdd hdq2).frame.run hP1
  obtain ⟨J, hEstJ, hJjobs, hJm, hJp, hJw1, hJqpos, hJpqB, hJdqB, hJd2B, hJdd, hJdq2, hHWJ,
    hPSJ, hQSJ, hDSJ, hnJ, hmJ, hsnJ, hWJ, hinpJ, houtJ, hNXJl, hCCJl, hPCJl⟩ := hQ6
  have hPSJ' : σ6.arrs "PS" = (List.range J.jobs).map (pv J) := by rw [hJjobs]; exact hPSJ
  have hQSJ' : σ6.arrs "QS" = (List.range J.jobs).map (qv J) := by rw [hJjobs]; exact hQSJ
  have hDSJ' : σ6.arrs "DS" = (List.range J.jobs).map (dv J) := by rw [hJjobs]; exact hDSJ
  have hnJ' : σ6.vars "n" = J.jobs := by rw [hJjobs]; exact hnJ
  have hmJ' : σ6.vars "m" = J.machines := by rw [hJm]; exact hmJ
  have hsnJ' : σ6.vars "sn" = J.jobs := by rw [hJjobs]; exact hsnJ
  have hTX6 : σ6.arrs "TX" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hJjobs, hfa6 "TX" (by decide)]; exact hP2.1
  have hTY6 : σ6.arrs "TY" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hJjobs, hfa6 "TY" (by decide)]; exact hP2.2
  obtain ⟨σF, hrF, hQF⟩ :=
    (tail4_spec (W := W) hEstJ hJqpos hJw1 hJp (by rw [hJjobs]; exact hp0) hB2
      (by rw [hJjobs]; exact hnB) hpB (by rw [hJm]; exact hmB) hWB hJd2B hJdd hJdq2).run
      ⟨hPSJ', hQSJ', hDSJ', hnJ', hmJ', hsnJ', hWJ, houtJ, hTX6, hTY6⟩
  refine ⟨σF, _, run_prog4_of_parts hr6 hrF, ?_, ?_⟩
  · rw [hJjobs]
  · rw [hQF]
    by_cases h : HasWeight I W
    · have h1 : HasWeight J W := (hHWJ W).mpr h
      have h2 : Yes x := hYesIff.mpr h
      simp [h1, h2]
    · have h1 : ¬ HasWeight J W := fun hh => h ((hHWJ W).mp hh)
      have h2 : ¬ Yes x := fun hh => h (hYesIff.mp hh)
      simp [h1, h2]

end Lax496464Proofs.Ram.T4Prog
