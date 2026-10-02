import Lax496464.ProperInstances
import Lax496464.Corollary3
import Lax496464Proofs.Ram.D5Layout
import Lax496464Proofs.Ram.D5Bound
import Lax496464Proofs.Ram.D5Front
import Lax496464Proofs.Ram.D2Final
import Lax496464Proofs.Ram.D2Answer
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.Reduction

/-!
# Corollary 3: the Running Time

`Corollary3.corollary3_time`, by the dual table of Section 3 with equal preprocessing times: the
rows are the `n + 1` instants `u · p`, so the table has `(n+1)^m · (n+1)` entries and the running
time is `O((n+1)^(m+1) + sortCost)`.
-/

namespace Lax496464Proofs.Ram.D5Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.ProperInstances
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D5Prog Lax496464Proofs.Ram.D5Core Lax496464Proofs.Ram.D5Layout
open Lax496464Proofs.Ram.D5Loop Lax496464Proofs.Ram.D5Step Lax496464Proofs.Ram.D5Row
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1 Lax496464Proofs.Ram.D2Bound
open Lax496464Proofs.Ram.W3Front2 (sortSetup3_warrs)
open Lax496464Proofs.Ram.D5Bound Lax496464Proofs.Ram.D5Pure Lax496464Proofs.Ram.D5Front
open Lax496464Proofs.Ram.D2Prog (writeW writeW_spec)
open Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Answer Lax496464Proofs.Ram.D2Digits
open Lax496464Proofs.Ram.D2Final (yes_iff)
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext5 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "NX" then
    jobCount x
  else if a = "PW" then machineCount x + 1
  else if a = "VALID" then (jobCount x + 1) ^ machineCount x
  else if a = "TAB" then (jobCount x + 1) ^ machineCount x * (jobCount x + 1)
  else 0

/-- Room for every intermediate value: the table, and the entries of the word. -/
def T5 (x : List ℕ) : ℕ :=
  4 * maxEntry x + 4 * (jobCount x + 1) ^ (machineCount x + 1) + 20

/-- The domain of `corollary3_time`, at constant `c` and word length `w`. -/
def Dom5 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
    c * (jobCount x + 1) ^ (machineCount x + 1) ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j)}

set_option maxHeartbeats 8000000 in
theorem core5_noWrite : core5.NoWrite := by
  simp [core5, setup2, loopComU, bodyComU, topComU, stepComU, stepIsCodeU, limCom, rowsLoopU,
    rowBodyU, pwSetup, pwBody, code0Loop, codeBody,
    Lax496464Proofs.Ram.Corollary1Init.maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody, nxLoop, nxBody, bsLoop, bsBody, scanCom, scanInit,
    scanLoop, scanBody, scanFin, vphase, Com.NoWrite]

theorem switchCom_run {B : ℕ} (σ : Env) (W n : ℕ) (hW : σ.vars "W" = W) (hn : σ.vars "n" = n)
    (hWB : W < B) (hnB : n < B) :
    Run B switchCom σ ((σ.setVar "Wc" W).setVar "W" n) 10 := by
  have hvW : (V "W").evalB B σ = some W := hW ▸ evalB_var (by rw [hW]; exact hWB)
  have r1 := Run.assign (B := B) (σ := σ) (x := "Wc") (e := V "W") (v := W) hvW
  have hvn : (V "n").evalB B (σ.setVar "Wc" W) = some n := by
    have : (σ.setVar "Wc" W).vars "n" = n := by simp [hn]
    exact this ▸ evalB_var (by rw [this]; exact hnB)
  have r2 := Run.assign (B := B) (σ := σ.setVar "Wc" W) (x := "W") (e := V "n") (v := n) hvn
  exact (r1.seq r2).mono (by simp only [Expr.size]; omega)

open Classical in
set_option maxHeartbeats 16000000 in
theorem prog5_solves (cc w : ℕ) :
    Solves L5 prog5 (Dom5 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T5 x))
      (fun x => cost5 (jobCount x) (machineCount x)) where
  ok := prog5_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, hUnif, hTabHyp, hxQ⟩ := hx
    obtain ⟨I, W, hdec0⟩ := hxDI
    have hdec := hdec0
    obtain ⟨y, hxy, hEnc⟩ := hdec0
    subst hxy
    obtain ⟨p, hpU⟩ : ∃ p, ∀ j : I.Job, I.p j = p := by
      obtain ⟨I', W', h', hu⟩ := hUnif
      obtain ⟨hI, hW⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique h' hdec
      subst hI; subst hW; exact hu
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    have hlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
    set B : ℕ := bound (y ++ [W]) (T5 (y ++ [W])) with hBdef
    have hxB : ∀ v ∈ (y ++ [W]), v < B := fun v hv => lt_bound hv
    have hBeq : B = (y ++ [W]).length + maxEntry (y ++ [W]) + 1 +
        (4 * maxEntry (y ++ [W]) + 4 * (I.jobs + 1) ^ (I.machines + 1) + 20) := by
      rw [hBdef]; unfold bound T5; rw [hjc, hmc]
    have hmem_of_idx : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 ∈ (y ++ [W]) :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ (j : ℕ) (by rw [hjc]; exact j.isLt)
    set P : ℕ := (I.jobs + 1) ^ (I.machines + 1) with hPdef
    have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    have hIjm : (I.jobs : ℕ) ≤ maxEntry (y ++ [W]) := by
      rw [← hjc]; exact le_maxEntry (hmem_of_idx 0 (by omega))
    have hB2 : 2 < B := by rw [hBeq]; omega
    have hnB : 4 * I.jobs + 5 < B := by rw [hBeq]; omega
    have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hpe j]; exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
    have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hqe j]
      exact le_maxEntry (hmem_of_idx (2 + jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hde j]
      exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hwB : ∀ j : I.Job, (I.w j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hwe j]
      exact le_maxEntry (hmem_of_idx (2 + 3 * jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hmach : I.machines ≤ maxEntry (y ++ [W]) := by
      rw [← hmc]; exact le_maxEntry (hmem_of_idx 1 (by omega))
    have hWle : W ≤ maxEntry (y ++ [W]) := le_maxEntry (by simp)
    have hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B := fun j => by
      have h1 := hpB j; have h2 := hqB j; rw [hBeq]; omega
    have hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B := fun a b => by
      have h1 := hdB a; have h2 := hqB b; rw [hBeq]; omega
    have hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B := fun j => by
      have h1 := hdB j; rw [hBeq]; omega
    have hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B := fun a b => by
      have h1 := hdB a; have h2 := hdB b; rw [hBeq]; omega
    have hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B := fun a b => by
      have h1 := hdB a; have h2 := hqB b; rw [hBeq]; omega
    have hWB : W + 2 < B := by rw [hBeq]; omega
    have hmB : I.machines < B := by rw [hBeq]; omega
    have hPB : P < B := by rw [hBeq]; omega
    have hpre : (fun σ => σ.inp = y ++ [W] ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs)
        (initEnv (ext5 (y ++ [W])) (y ++ [W])) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext5, hjc]
    obtain ⟨σ1, hr1, ⟨J, hJest, hJn, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW, hPS, hQS,
        hDS, hWS, -, -, hn1, hm1, hsn1, hW1, hinp1, hout1, -, hJpw⟩, hfv1, hfa1, -, -⟩ :=
      (Lax496464Proofs.Ram.D5Front.sortSetup3_spec_p ⟨y, rfl, hEnc⟩ hqpos hB2 hxB hnB hpqB hdq hd2B hdd hdq2).frame.run hpre
    have hK : cost5 (jobCount (y ++ [W])) (machineCount (y ++ [W])) =
        cost5 I.jobs I.machines := by rw [hjc, hmc]
    have hYes := yes_iff hdec
    have hIB : I.jobs < B := by rw [hBeq]; omega
    have hMB : I.machines < B := by rw [hBeq]; omega
    have hvn : (V "n").evalB B σ1 = some I.jobs := by
      have : σ1.vars "n" = I.jobs := hn1
      exact this ▸ evalB_var (by rw [this]; exact hIB)
    have hvm : (V "m").evalB B σ1 = some I.machines := by
      have : σ1.vars "m" = I.machines := hm1
      exact this ▸ evalB_var (by rw [this]; exact hMB)
    have hcondN := evalB_condLt hvn (evalB_lit (show 1 < B by omega))
    have hcondM := evalB_condLt hvm (evalB_lit (show 1 < B by omega))
    have hcost1 : 2 * Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 1000 * I.jobs + 2000 ≤
        2 * Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 1000 * I.jobs + 2000 := le_rfl
    by_cases hn0 : I.jobs < 1
    · -- no job
      have hc1 : (Cond.lt (V "n") (Expr.lit 1)).evalB B σ1 = some true := by
        rw [hcondN]; simp [hn0]
      obtain ⟨σ2, hr2, hout2⟩ := (writeW_spec hB2 W [] (by omega)).run ⟨hW1, hout1⟩
      refine ⟨ext5 (y ++ [W]), σ2, ?_, ?_⟩
      · refine (hr1.seq (Run.ite_true hc1 hr2)).mono ?_
        rw [hK]; unfold cost5 cost2; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
      · rw [hout2]
        have htr := hasWeight_trivial (I := I) (Or.inl (by omega)) W
        by_cases hW0 : W = 0
        · have hy1 : Yes (y ++ [W]) := hYes.mpr (htr.mpr hW0)
          rw [if_pos hy1, List.nil_append, if_pos hW0]
        · have hy1 : ¬ Yes (y ++ [W]) := fun h => hW0 (htr.mp (hYes.mp h))
          rw [if_neg hy1, List.nil_append, if_neg hW0]
    · have hc1 : (Cond.lt (V "n") (Expr.lit 1)).evalB B σ1 = some false := by
        rw [hcondN]; simp [hn0]
      by_cases hm0 : I.machines < 1
      · have hc2 : (Cond.lt (V "m") (Expr.lit 1)).evalB B σ1 = some true := by
          rw [hcondM]; simp [hm0]
        obtain ⟨σ2, hr2, hout2⟩ := (writeW_spec hB2 W [] (by omega)).run ⟨hW1, hout1⟩
        refine ⟨ext5 (y ++ [W]), σ2, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_true hc2 hr2))).mono ?_
          rw [hK]; unfold cost5 cost2; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
        · rw [hout2]
          have htr := hasWeight_trivial (I := I) (Or.inr (by omega)) W
          by_cases hW0 : W = 0
          · have hy1 : Yes (y ++ [W]) := hYes.mpr (htr.mpr hW0)
            rw [if_pos hy1, List.nil_append, if_pos hW0]
          · have hy1 : ¬ Yes (y ++ [W]) := fun h => hW0 (htr.mp (hYes.mp h))
            rw [if_neg hy1, List.nil_append, if_neg hW0]
      · have hc2 : (Cond.lt (V "m") (Expr.lit 1)).evalB B σ1 = some false := by
          rw [hcondM]; simp [hm0]
        -- the main case
        have hn1' : 1 ≤ I.jobs := by omega
        have hm1' : 1 ≤ I.machines := by omega
        have hpow : (I.jobs + 1) ^ I.machines * (I.jobs + 1) = P := by rw [hPdef, pow_succ]
        have hNP : (I.jobs + 1) ^ I.machines ≤ P := by
          rw [← hpow]; exact Nat.le_mul_of_pos_right _ (by omega)
        have hCI : CI J B I.jobs I.machines I.jobs := by
          refine ⟨hB2, hJn, hJm, hn1', hm1', hJest, hJq, ?_, by omega, by rw [hBeq]; omega,
            by omega, by rw [hpow]; exact hPB, ?_, ?_, ?_, ?_⟩
          · intro i hi
            have := Nat.pow_le_pow_right (show 0 < I.jobs + 1 by omega) hi
            omega
          · intro k hk
            have hk' : k < J.jobs := by omega
            have := hJd2 ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.Dp1.dv; rw [dif_pos hk']; exact this
          · intro k hk
            have hk' : k < J.jobs := by omega
            have := hJpq ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.Dp1.pv Lax496464Proofs.Ram.Dp1.qv
            rw [dif_pos hk', dif_pos hk']; exact this
          · intro a b ha hb
            have ha' : a < J.jobs := by omega
            have hb' : b < J.jobs := by omega
            have := hJdq ⟨a, ha'⟩ ⟨b, hb'⟩
            unfold Lax496464Proofs.Ram.Dp1.dv Lax496464Proofs.Ram.Dp1.qv
            rw [dif_pos ha', dif_pos hb']; exact this
          · intro k hk
            have hk' : k < J.jobs := by omega
            have := hJw ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.DpMArr.wv; rw [dif_pos hk']; exact this
        have hWB' : W < B := by rw [hBeq]; omega
        have hwW : ∀ k < I.jobs, Lax496464Proofs.Ram.DpMArr.wv J k + W < B := by
          intro k hk
          have hk' : k < J.jobs := by omega
          obtain ⟨i, -, hwi⟩ := hJpw ⟨k, hk'⟩
          have hwv : Lax496464Proofs.Ram.DpMArr.wv J k = (J.w ⟨k, hk'⟩ : ℕ) := by
            unfold Lax496464Proofs.Ram.DpMArr.wv; rw [dif_pos hk']
          rw [hwv, hwi]
          have h1 := hwB i
          rw [hBeq]; omega
        have hp : ∀ i : J.Job, J.p i = p := fun i => by
          obtain ⟨i', hp', -⟩ := hJpw i
          rw [hp']; exact hpU i'
        have hsw := switchCom_run σ1 W I.jobs hW1 hn1 hWB' hIB
        set σs : Env := (σ1.setVar "Wc" W).setVar "W" I.jobs with hσs
        clear_value σs
        have hfa1' : ∀ a, a ∉ ["A", "SA", "SB", "PS", "QS", "DS", "WS"] →
            σ1.arrs a = (initEnv (ext5 (y ++ [W])) (y ++ [W])).arrs a :=
          fun a ha => hfa1 a (fun h => ha (sortSetup3_warrs a h))
        have hArrs : σs.arrs = σ1.arrs := by rw [hσs]; simp
        have hCPre : CPre J I.jobs I.machines I.jobs σs := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hArrs]; simp only [PSL, hJn]; exact hPS
          · rw [hArrs]; simp only [QSL, hJn]; exact hQS
          · rw [hArrs]; simp only [DSL, hJn]; exact hDS
          · rw [hArrs]; simp only [WSL, hJn]; exact hWS
          · simp [hσs, hn1]
          · simp [hσs, hm1]
          · simp [hσs, hsn1]
          · simp [hσs]
          · rw [hArrs, hfa1' "NX" (by decide)]; simp [initEnv, ext5, hjc]
          · rw [hArrs, hfa1' "PW" (by decide)]; simp [initEnv, ext5, hmc]
          · rw [hArrs, hfa1' "VALID" (by decide)]; simp [initEnv, ext5, hjc, hmc]
          · rw [hArrs, hfa1' "TAB" (by decide)]; simp [initEnv, ext5, hjc, hmc]
        have hWcs : σs.vars "Wc" = W := by simp [hσs]
        have houts : σs.out = [] := by rw [hσs]; simp [hout1]
        obtain ⟨σ2, hr2, ⟨hzk, hR2, hWc2, hT2⟩, hfv2, hfa2, -, hout2⟩ :=
          (core5_spec hCI hWB' hwW hp).frame.run (σ := σs) ⟨hCPre, hWcs⟩
        have hout2' : σ2.out = [] := by rw [hout2 core5_noWrite]; exact houts
        set code := codeL I.jobs I.machines (List.range (min I.machines I.jobs)) with hcode
        have hcodeN : code < (I.jobs + 1) ^ I.machines :=
          (Lax496464Proofs.Ram.D2Core.sl_range I.jobs I.machines).codeL_lt
        have hcm : code * (I.jobs + 1) < (I.jobs + 1) ^ I.machines * (I.jobs + 1) :=
          Nat.mul_lt_mul_of_pos_right hcodeN (Nat.succ_pos _)
        have hcm' : code * (I.jobs + 1) < B := lt_trans hcm (by rw [hpow]; exact hPB)
        have hcodeB : code < B :=
          lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hcm'
        have htab : Lax496464Proofs.Ram.D3Cor3.UTabOK J J.jobs J.machines W p
            ((I.jobs + 1) ^ I.machines) 0 (σ2.arrs "TAB") := by
          rw [hJn, hJm]; exact hT2.1
        have hiff := Lax496464Proofs.Ram.D3Cor3.hasWeight_iff_utab hJest htab
        rw [hJn, hJm] at hiff
        have hval : (σ2.arrs "TAB").getD (code * (I.jobs + 1)) 0 < B :=
          lt_of_le_of_lt (hT2.2 _) hWB'
        obtain ⟨σ3, hr3, hout3⟩ :=
          (finish5_spec hB2 code W I.jobs (σ2.arrs "TAB") [] (by rw [hT2.1.1]; exact hcm) hval
            hcm' hcodeB (by omega) hWB').run ⟨hzk, hR2, hWc2, rfl, hout2'⟩
        refine ⟨ext5 (y ++ [W]), σ3, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_false hc2 (hsw.seq (hr2.seq hr3))))).mono ?_
          rw [hK]; unfold cost5 cost2; rw [if_pos ⟨hn1', hm1'⟩]
          simp only [Cond.size, Expr.size]; omega
        · rw [hout3, List.nil_append]
          have hyes : Yes (y ++ [W]) ↔ (σ2.arrs "TAB").getD (code * (I.jobs + 1)) 0 = W :=
            hYes.trans ((hHW W).symm.trans hiff)
          by_cases h0 : (σ2.arrs "TAB").getD (code * (I.jobs + 1)) 0 = W
          · rw [if_pos h0, if_pos (hyes.mpr h0)]
          · rw [if_neg h0, if_neg (fun h => h0 (hyes.mp h))]

open Lax496464Proofs.Ram.Fits (maxEntry_mem)

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc5 : ℕ := 64 * Lax496464Proofs.Ram.Fits.const L5 + 200000

theorem cc5_ge : 64 * Lax496464Proofs.Ram.Fits.const L5 ≤ cc5 := by unfold cc5; omega

theorem hne5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, Fits (Lax496464Proofs.Ram.Fits.const L5) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact Lax496464Proofs.Ram.Corollary1Prog.fits_mono hxFits (by have := cc5_ge; omega)

theorem hTab5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, Lax496464Proofs.Ram.Fits.const L5 * T5 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne5 w x hx
  obtain ⟨-, hxFits, -, hTabHyp, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  set κ := Lax496464Proofs.Ram.Fits.const L5 with hκ
  set M := x.length + maxEntry x + 1 with hM
  set RN := (jobCount x + 1) ^ (machineCount x + 1) with hRN
  have hRN1 : 1 ≤ RN := Nat.one_le_pow _ _ (by omega)
  have hcc : 64 * κ ≤ cc5 := cc5_ge
  have hM1 : 1 ≤ M := by omega
  have hA : κ * (4 * maxEntry x + 20) ≤ 24 * κ * M := by
    have : 4 * maxEntry x + 20 ≤ 24 * M := by omega
    calc κ * (4 * maxEntry x + 20) ≤ κ * (24 * M) := Nat.mul_le_mul_left _ this
      _ = 24 * κ * M := by ring
  have hA2 : 2 * (24 * κ * M) ≤ 2 ^ w := by
    calc 2 * (24 * κ * M) = (48 * κ) * M := by ring
      _ ≤ cc5 * M := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ w := hf
  have hB : 16 * (4 * κ * RN) ≤ 2 ^ w := by
    calc 16 * (4 * κ * RN) = (64 * κ) * RN := by ring
      _ ≤ cc5 * RN := Nat.mul_le_mul_right _ hcc
      _ ≤ 2 ^ w := hTabHyp
  have hsplit : κ * T5 x = κ * (4 * maxEntry x + 20) + 4 * κ * RN := by
    unfold T5; rw [← hRN]; ring
  rw [hsplit]
  omega

theorem hT5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w,
    Layout.const L5 * cost5 (jobCount x) (machineCount x) + 1 ≤
      cc5 * (jobCount x + 1) ^ (machineCount x + 1) + cc5 * sortCost x := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hb := cost5_le (m := machineCount x) hnl
  have hc : Layout.const L5 = 10 := rfl
  rw [hc]
  have hcc : 200000 ≤ cc5 := by unfold cc5; omega
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  rw [hsc]
  have h1 : 200000 * (jobCount x + 1) ^ (machineCount x + 1) ≤
      cc5 * (jobCount x + 1) ^ (machineCount x + 1) := Nat.mul_le_mul_right _ hcc
  have h2 := Nat.mul_le_mul_right ((x.length + 1) * (Nat.log 2 (x.length + 2) + 1)) hcc
  omega

open Classical in
/--
---
conclusion: Lax496464.Corollary3.corollary3_time
---
Corollary 3 as a word RAM program: the dual table of Section 3 for equal preprocessing times.
Read the word, sort the jobs by start time, and fill the table over sets of thresholds written as
base-`(n+1)` numbers exactly as for Theorem 2, but with rows the `n + 1` instants `u · p` (the
instant a partial solution has spent after selecting `u` jobs) instead of the `W + 1` weights: the
cell for the instant `u · p` is `max (T[X₁, u]) (min W (w_j + T[X₂, u + 1]))`, the second term
present when `(u+1) p + q_j ≤ d_j`.  The guard is tested as `u < lim_j`, where `lim_j` is computed
once per job by a division, so the machine never forms the product `u · p` (only the entries of
the word are bounded by the word length).  The table has `(n+1)^m · (n+1)` entries, filled from
the largest number down, and the answer is one entry.  The domain restricts to positive processing
times, the paper's standing assumption for Lemma 1's recursion.
-/
theorem corollary3_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
        c * (jobCount x + 1) ^ (machineCount x + 1) ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (jobCount x + 1) ^ (machineCount x + 1) + c * sortCost x) :=
  ⟨compileProgram L5 prog5, cc5, fun w =>
    computesInTime_of_solves_fits (hne5 w) (hfits5 w) (hTab5 w) (prog5_solves cc5 w) (hT5 w)⟩

example : type_of% @Lax496464.Corollary3.corollary3_time := corollary3_time_proved


end Lax496464Proofs.Ram.D5Final
