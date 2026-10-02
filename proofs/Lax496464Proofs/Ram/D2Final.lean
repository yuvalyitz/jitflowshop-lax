import Lax496464Proofs.Ram.D2Bound
import Lax496464Proofs.Ram.D2Answer
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.Reduction

/-!
# Theorem 2: the Running Time
-/

namespace Lax496464Proofs.Ram.D2Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D2Prog Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Layout
open Lax496464Proofs.Ram.D2Bound Lax496464Proofs.Ram.D2Answer Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1 Lax496464Proofs.Ram.D2Rows Lax496464Proofs.Ram.D2Digits
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464Proofs.Ram.W3Front2 (sortSetup3_spec sortSetup3_warrs)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext2 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "NX" then
    jobCount x
  else if a = "PW" then machineCount x + 1
  else if a = "VALID" then (jobCount x + 1) ^ machineCount x
  else if a = "TAB" then (jobCount x + 1) ^ machineCount x * (threshold x + 1)
  else 0

/-- Room for every intermediate value: the table, and the entries of the word. -/
def T2 (x : List ℕ) : ℕ :=
  4 * maxEntry x + 4 * ((threshold x + 1) * (jobCount x + 1) ^ machineCount x) + 20

/-- The domain of `theorem2_time`, at constant `c` and word length `w`. -/
def Dom2 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    c * (threshold x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j)}

theorem threshold_append {y : List ℕ} {I : Instance} (W : ℕ) (hEnc : EncodesInstance y I) :
    threshold (y ++ [W]) = W := by
  have hjc : jobCount (y ++ [W]) = I.jobs := (decision_word_facts (W := W) hEnc).1
  unfold threshold
  rw [hjc, ← hEnc.length_eq]
  simp

set_option maxHeartbeats 8000000 in
theorem core2_noWrite : core2.NoWrite := by
  simp [core2, setup2, loopCom, bodyCom, topCom, stepCom, stepIsCode, pwSetup, pwBody, code0Loop,
    codeBody, Lax496464Proofs.Ram.Corollary1Init.maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody, nxLoop, nxBody, bsLoop, bsBody, scanCom, scanInit,
    scanLoop, scanBody, scanFin, vphase, rowsLoop, rowBody, Lax496464Proofs.Ram.Col1.fCom,
    Com.NoWrite]


theorem yes_iff {y : List ℕ} {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance (y ++ [W]) I W) :
    Yes (y ++ [W]) ↔ HasWeight I W := by
  constructor
  · rintro ⟨I', W', h', hw⟩
    obtain ⟨hI, hW⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique h' hdec
    subst hI; subst hW; exact hw
  · intro hw; exact ⟨I, W, hdec, hw⟩

open Classical in
set_option maxHeartbeats 16000000 in
theorem prog2_solves (cc w : ℕ) :
    Solves L2 prog2 (Dom2 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T2 x))
      (fun x => cost2 (jobCount x) (machineCount x) (threshold x)) where
  ok := prog2_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, hTabHyp, hxQ⟩ := hx
    obtain ⟨I, W, hdec0⟩ := hxDI
    have hdec := hdec0
    obtain ⟨y, hxy, hEnc⟩ := hdec0
    subst hxy
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    have hth := threshold_append W hEnc
    have hlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
    set B : ℕ := bound (y ++ [W]) (T2 (y ++ [W])) with hBdef
    have hxB : ∀ v ∈ (y ++ [W]), v < B := fun v hv => lt_bound hv
    have hBeq : B = (y ++ [W]).length + maxEntry (y ++ [W]) + 1 +
        (4 * maxEntry (y ++ [W]) + 4 * ((W + 1) * (I.jobs + 1) ^ I.machines) + 20) := by
      rw [hBdef]; unfold bound T2; rw [hth, hjc, hmc]
    have hmem_of_idx : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 ∈ (y ++ [W]) :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ (j : ℕ) (by rw [hjc]; exact j.isLt)
    set P : ℕ := (W + 1) * (I.jobs + 1) ^ I.machines with hPdef
    have hP1 : 1 ≤ P := Nat.mul_pos (by omega) (pow_pos (by omega) _)
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
        (initEnv (ext2 (y ++ [W])) (y ++ [W])) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext2, hjc]
    obtain ⟨σ1, hr1, ⟨J, hJest, hJn, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW, hPS, hQS,
        hDS, hWS, -, -, hn1, hm1, hsn1, hW1, hinp1, hout1, -⟩, hfv1, hfa1, -, -⟩ :=
      (sortSetup3_spec ⟨y, rfl, hEnc⟩ hqpos hB2 hxB hnB hpqB hdq hd2B hdd hdq2).frame.run hpre
    have hK : cost2 (jobCount (y ++ [W])) (machineCount (y ++ [W])) (threshold (y ++ [W])) =
        cost2 I.jobs I.machines W := by rw [hjc, hmc, hth]
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
      refine ⟨ext2 (y ++ [W]), σ2, ?_, ?_⟩
      · refine (hr1.seq (Run.ite_true hc1 hr2)).mono ?_
        rw [hK]; unfold cost2; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
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
        refine ⟨ext2 (y ++ [W]), σ2, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_true hc2 hr2))).mono ?_
          rw [hK]; unfold cost2; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
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
        have hNP : (I.jobs + 1) ^ I.machines ≤ P := Nat.le_mul_of_pos_left _ (by omega)
        have hCI : CI J B I.jobs I.machines W := by
          refine ⟨hB2, hJn, hJm, hn1', hm1', hJest, hJq, ?_, by omega, by rw [hBeq]; omega,
            by omega, by rw [Nat.mul_comm]; exact hPB, ?_, ?_, ?_, ?_⟩
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
        have hfa1' : ∀ a, a ∉ ["A", "SA", "SB", "PS", "QS", "DS", "WS"] →
            σ1.arrs a = (initEnv (ext2 (y ++ [W])) (y ++ [W])).arrs a :=
          fun a ha => hfa1 a (fun h => ha (sortSetup3_warrs a h))
        have hCPre : CPre J I.jobs I.machines W σ1 := by
          refine ⟨?_, ?_, ?_, ?_, hn1, hm1, hsn1, hW1, ?_, ?_, ?_, ?_⟩
          · simp only [PSL, hJn]; exact hPS
          · simp only [QSL, hJn]; exact hQS
          · simp only [DSL, hJn]; exact hDS
          · simp only [WSL, hJn]; exact hWS
          · rw [hfa1' "NX" (by decide)]; simp [initEnv, ext2, hjc]
          · rw [hfa1' "PW" (by decide)]; simp [initEnv, ext2, hmc]
          · rw [hfa1' "VALID" (by decide)]; simp [initEnv, ext2, hjc, hmc]
          · rw [hfa1' "TAB" (by decide)]; simp [initEnv, ext2, hjc, hmc, hth]
        obtain ⟨σ2, hr2, ⟨inf, hi1, hinfB, hinf, hzk, hR2, hW2, hlenT, hcol⟩, hfv2, hfa2, -, hout2⟩ :=
          (core2_spec hCI).frame.run (σ := σ1) hCPre
        have hout2' : σ2.out = [] := by rw [hout2 core2_noWrite]; exact hout1
        set code := codeL I.jobs I.machines (List.range (min I.machines I.jobs)) with hcode
        have hcodeN : code < (I.jobs + 1) ^ I.machines :=
          (sl_range I.jobs I.machines).codeL_lt
        have hcm : code * (W + 1) + W < (I.jobs + 1) ^ I.machines * (W + 1) := by
          have : (code + 1) * (W + 1) ≤ (I.jobs + 1) ^ I.machines * (W + 1) :=
            Nat.mul_le_mul_right _ hcodeN
          rw [Nat.add_mul, Nat.one_mul] at this; omega
        have hNB' : (I.jobs + 1) ^ I.machines * (W + 1) < B := by rw [Nat.mul_comm]; exact hPB
        have hentry := hcol W le_rfl
        have hval : (σ2.arrs "TAB").getD (code * (W + 1) + W) 0 < B :=
          lt_of_le_of_lt (Lax496464Proofs.Ram.D2Tab.rep_le hentry) hinfB
        obtain ⟨σ3, hr3, hout3⟩ :=
          (finishCom_spec hB2 code W (σ2.arrs "TAB") [] (by rw [hlenT]; exact hcm) hval
            (by omega) (by omega) (by omega) (by omega) (by omega)).run
            ⟨hzk, hR2, hW2, rfl, hout2'⟩
        refine ⟨ext2 (y ++ [W]), σ3, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_false hc2 (hr2.seq hr3)))).mono ?_
          rw [hK]; unfold cost2; rw [if_pos ⟨hn1', hm1'⟩]; simp only [Cond.size, Expr.size]; omega
        · rw [hout3, List.nil_append]
          have hne := entry_ne_zero_iff hJest (by omega) hentry
          by_cases h0 : (σ2.arrs "TAB").getD (code * (W + 1) + W) 0 = 0
          · have hy1 : ¬ Yes (y ++ [W]) := fun h => hne.mpr ((hHW W).mpr (hYes.mp h)) h0
            rw [if_pos h0, if_neg hy1]
          · have hy1 : Yes (y ++ [W]) := hYes.mpr ((hHW W).mp (hne.mp h0))
            rw [if_neg h0, if_pos hy1]


open Lax496464Proofs.Ram.Fits (maxEntry_mem)

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc2 : ℕ := 64 * Lax496464Proofs.Ram.Fits.const L2 + 100000

theorem cc2_ge : 64 * Lax496464Proofs.Ram.Fits.const L2 ≤ cc2 := by unfold cc2; omega

theorem hne2 (w : ℕ) : ∀ x ∈ Dom2 cc2 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits2 (w : ℕ) : ∀ x ∈ Dom2 cc2 w, Fits (Lax496464Proofs.Ram.Fits.const L2) w x := by
  rintro x ⟨-, hxFits, -, -⟩
  exact Lax496464Proofs.Ram.Corollary1Prog.fits_mono hxFits (by have := cc2_ge; omega)

theorem hTab2 (w : ℕ) : ∀ x ∈ Dom2 cc2 w, Lax496464Proofs.Ram.Fits.const L2 * T2 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne2 w x hx
  obtain ⟨-, hxFits, hTabHyp, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  set κ := Lax496464Proofs.Ram.Fits.const L2 with hκ
  set M := x.length + maxEntry x + 1 with hM
  set RN := (threshold x + 1) * (jobCount x + 1) ^ machineCount x with hRN
  have hRN1 : 1 ≤ RN := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hcc : 64 * κ ≤ cc2 := cc2_ge
  have hM1 : 1 ≤ M := by omega
  have hA : κ * (4 * maxEntry x + 20) ≤ 24 * κ * M := by
    have : 4 * maxEntry x + 20 ≤ 24 * M := by omega
    calc κ * (4 * maxEntry x + 20) ≤ κ * (24 * M) := Nat.mul_le_mul_left _ this
      _ = 24 * κ * M := by ring
  have hA2 : 2 * (24 * κ * M) ≤ 2 ^ w := by
    calc 2 * (24 * κ * M) = (48 * κ) * M := by ring
      _ ≤ cc2 * M := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ w := hf
  have hB : 16 * (4 * κ * RN) ≤ 2 ^ w := by
    calc 16 * (4 * κ * RN) = (64 * κ) * RN := by ring
      _ ≤ cc2 * RN := Nat.mul_le_mul_right _ hcc
      _ = cc2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x := by rw [hRN]; ring
      _ ≤ 2 ^ w := hTabHyp
  have hsplit : κ * T2 x = κ * (4 * maxEntry x + 20) + 4 * κ * RN := by
    unfold T2; rw [← hRN]; ring
  rw [hsplit]
  omega

theorem hT2 (w : ℕ) : ∀ x ∈ Dom2 cc2 w,
    Layout.const L2 * cost2 (jobCount x) (machineCount x) (threshold x) + 1 ≤
      cc2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x + cc2 * sortCost x := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hb := cost2_le (m := machineCount x) (W := threshold x) hnl
  have hc : Layout.const L2 = 10 := rfl
  rw [hc]
  have hcc : 100000 ≤ cc2 := by unfold cc2; omega
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  rw [hsc]
  have h1 : 100000 * ((threshold x + 1) * (jobCount x + 1) ^ machineCount x) ≤
      cc2 * (threshold x + 1) * (jobCount x + 1) ^ machineCount x := by
    rw [mul_assoc]; exact Nat.mul_le_mul_right _ hcc
  have h2 := Nat.mul_le_mul_right ((x.length + 1) * (Nat.log 2 (x.length + 2) + 1)) hcc
  omega


open Classical in
/--
---
conclusion: Lax496464.Theorem2.theorem2_time
---
Theorem 2 as a word RAM program. Read the word, sort the jobs by start time, and fill the table of
Section 3 over sets of thresholds written as base-`(n+1)` numbers: the numbers are visited from the
top, each is decided to be a code of a set or not by a recurrence, and the two sets `X₁`, `X₂` of
recursion (1) are found by one scan of its digits (`O(|X|)`, independent of `W`), after which its
`W+1` cells cost `O(1)` each. The sets contribute `Σ(|X|+1) ≤ 2 (n+1)^m` in all. The table is the
monotone one ("weight at least `W'`"), so it has `W+1` rows whatever the weights are, and the
answer is one entry of the column of the first `m` indices. The domain restricts to positive
processing times, the paper's standing assumption for Lemma 1's recursion. The running time is
`c (W+1) (n+1)^m + c · sortCost`: no work per machine beyond the `O(|X|)` scan of a set.
-/
theorem theorem2_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        c * (threshold x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (threshold x + 1) * (jobCount x + 1) ^ machineCount x + c * sortCost x) :=
  ⟨compileProgram L2 prog2, cc2, fun w =>
    computesInTime_of_solves_fits (hne2 w) (hfits2 w) (hTab2 w) (prog2_solves cc2 w) (hT2 w)⟩

end Lax496464Proofs.Ram.D2Final
