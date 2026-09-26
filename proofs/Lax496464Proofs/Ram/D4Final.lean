import Lax496464Proofs.Ram.D4Bound
import Lax496464Proofs.Ram.D4Front
import Lax496464Proofs.Ram.D2Answer
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.Reduction
import Lax496464.Corollary2

/-!
# Corollary 2: the running time

The dual table of Section 3: for each instant `t = 0 … P` the largest weight attainable from it,
capped at the threshold.  The program is `D4Prog.prog4`; the table has `P + 1` rows per set of
thresholds, `P = Σ p_j` (found by the program itself), and the answer is one entry.
-/

namespace Lax496464Proofs.Ram.D4Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D4Prog Lax496464Proofs.Ram.D4Core Lax496464Proofs.Ram.D4Layout
open Lax496464Proofs.Ram.D4Bound Lax496464Proofs.Ram.D2Answer Lax496464Proofs.Ram.D4Step
open Lax496464Proofs.Ram.D4Sum Lax496464Proofs.Ram.D4Row Lax496464Proofs.Ram.D4Tab
open Lax496464Proofs.Ram.D2Prog (writeW writeW_spec)
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D3Dual
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1
open Lax496464Proofs.Ram.D2Core (PSL QSL DSL WSL)
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464Proofs.Ram.W3Front2 (sortSetup3_warrs)
open Lax496464Proofs.Ram.D4Front (sortSetup3_spec_sum)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext4 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "NX" then
    jobCount x
  else if a = "PW" then machineCount x + 1
  else if a = "VALID" then (jobCount x + 1) ^ machineCount x
  else if a = "TAB" then (jobCount x + 1) ^ machineCount x * (preSum x + 1)
  else 0

/-- Room for every intermediate value: the table, and the entries of the word. -/
def T4 (x : List ℕ) : ℕ :=
  4 * maxEntry x + 4 * ((preSum x + 1) * (jobCount x + 1) ^ machineCount x) + 20

/-- The domain of `corollary2_time`, at constant `c` and word length `w`. -/
def Dom4 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    c * (preSum x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j)}

set_option maxHeartbeats 8000000 in
theorem core4_noWrite : core4.NoWrite := by
  simp [core4, setup4, loopCom4, bodyCom4, topCom4, stepCom4, stepIsCode4, sumCom, sumLoop, sumBody,
    pwSetup, pwBody, code0Loop, codeBody, nxLoop, nxBody, bsLoop, bsBody, scanCom, scanInit,
    scanLoop, scanBody, scanFin, vphase, rowsLoop4, rowBody4, Com.NoWrite]

theorem yes_iff {y : List ℕ} {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance (y ++ [W]) I W) :
    Yes (y ++ [W]) ↔ HasWeight I W := by
  constructor
  · rintro ⟨I', W', h', hw⟩
    obtain ⟨hI, hW⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique h' hdec
    subst hI; subst hW; exact hw
  · intro hw; exact ⟨I, W, hdec, hw⟩

theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sum of the machine's `PS` array is the total preprocessing time of the sorted instance. -/
theorem psl_sum (J : Instance) : (PSL J).sum = ∑ i : J.Job, (J.p i : ℕ) := by
  unfold PSL
  rw [sum_map_range, Finset.sum_range (fun i => Lax496464Proofs.Ram.Dp1.pv J i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Lax496464Proofs.Ram.Dp1.pv
  rw [dif_pos j.isLt]


open Classical in
set_option maxHeartbeats 16000000 in
theorem prog4_solves (cc w : ℕ) :
    Solves L4 prog4 (Dom4 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T4 x))
      (fun x => cost4 (jobCount x) (machineCount x) (preSum x)) where
  ok := prog4_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, hTabHyp, hxQ⟩ := hx
    obtain ⟨I, W, hdec0⟩ := hxDI
    have hdec := hdec0
    obtain ⟨y, hxy, hEnc⟩ := hdec0
    subst hxy
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    have hlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
    set Ps : ℕ := ∑ i : I.Job, (I.p i : ℕ) with hPsdef
    have hps : preSum (y ++ [W]) = Ps := preSum_eq hjc hpe
    set B : ℕ := bound (y ++ [W]) (T4 (y ++ [W])) with hBdef
    have hxB : ∀ v ∈ (y ++ [W]), v < B := fun v hv => lt_bound hv
    have hBeq : B = (y ++ [W]).length + maxEntry (y ++ [W]) + 1 +
        (4 * maxEntry (y ++ [W]) + 4 * ((Ps + 1) * (I.jobs + 1) ^ I.machines) + 20) := by
      rw [hBdef]; unfold bound T4; rw [hps, hjc, hmc]
    have hmem_of_idx : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 ∈ (y ++ [W]) :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ (j : ℕ) (by rw [hjc]; exact j.isLt)
    set NP : ℕ := (Ps + 1) * (I.jobs + 1) ^ I.machines with hNPdef
    have hNP1 : 1 ≤ NP := Nat.mul_pos (by omega) (pow_pos (by omega) _)
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
    have hNPB : NP < B := by rw [hBeq]; omega
    have hpre : (fun σ => σ.inp = y ++ [W] ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs)
        (initEnv (ext4 (y ++ [W])) (y ++ [W])) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext4, hjc]
    obtain ⟨σ1, hr1, ⟨J, hJest, hJn, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW, hsumJ,
        hpermJ, hPS, hQS, hDS, hWS, -, -, hn1, hm1, hsn1, hW1, hinp1, hout1, -⟩, hfv1, hfa1, -, -⟩ :=
      (sortSetup3_spec_sum ⟨y, rfl, hEnc⟩ hqpos hB2 hxB hnB hpqB hdq hd2B hdd hdq2).frame.run hpre
    have hK : cost4 (jobCount (y ++ [W])) (machineCount (y ++ [W])) (preSum (y ++ [W])) =
        cost4 I.jobs I.machines Ps := by rw [hjc, hmc, hps]
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
    by_cases hn0 : I.jobs < 1
    · -- no job
      have hc1 : (Cond.lt (V "n") (Expr.lit 1)).evalB B σ1 = some true := by
        rw [hcondN]; simp [hn0]
      obtain ⟨σ2, hr2, hout2⟩ := (writeW_spec hB2 W [] (by omega)).run ⟨hW1, hout1⟩
      refine ⟨ext4 (y ++ [W]), σ2, ?_, ?_⟩
      · refine (hr1.seq (Run.ite_true hc1 hr2)).mono ?_
        rw [hK]; unfold cost4; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
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
        refine ⟨ext4 (y ++ [W]), σ2, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_true hc2 hr2))).mono ?_
          rw [hK]; unfold cost4; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
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
        have hNP' : (I.jobs + 1) ^ I.machines ≤ NP := Nat.le_mul_of_pos_left _ (by omega)
        have hPsNP : Ps + 1 ≤ NP := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
        have hJpB : ∀ j : J.Job, (J.p j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
          obtain ⟨i, h1, -, -⟩ := hpermJ j; rw [h1]; exact hpB i
        have hJqB : ∀ j : J.Job, (J.q j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
          obtain ⟨i, -, h1, -⟩ := hpermJ j; rw [h1]; exact hqB i
        have hJwB : ∀ j : J.Job, (J.w j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
          obtain ⟨i, -, -, h1⟩ := hpermJ j; rw [h1]; exact hwB i
        have hJR : (PSL J).sum = Ps := by rw [psl_sum, hsumJ]
        have hCI : CI4 J B I.jobs I.machines W Ps := by
          refine ⟨hB2, hJn, hJm, hn1', hm1', hJest, hJq, hJR, ?_, hmB, by rw [hBeq]; omega,
            by omega, by rw [Nat.mul_comm]; exact hNPB, ?_, ?_, ?_, ?_⟩
          · intro i hi
            have := Nat.pow_le_pow_right (show 0 < I.jobs + 1 by omega) hi
            omega
          · intro k hk
            have hk' : k < J.jobs := by omega
            have := hJd2 ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.Dp1.dv; rw [dif_pos hk']; exact this
          · intro k hk
            have hk' : k < J.jobs := by omega
            have h1 := hJpB ⟨k, hk'⟩
            have h2 := hJqB ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.Dp1.pv Lax496464Proofs.Ram.Dp1.qv
            rw [dif_pos hk', dif_pos hk']
            rw [hBeq]; omega
          · intro a b ha hb
            have ha' : a < J.jobs := by omega
            have hb' : b < J.jobs := by omega
            have := hJdq ⟨a, ha'⟩ ⟨b, hb'⟩
            unfold Lax496464Proofs.Ram.Dp1.dv Lax496464Proofs.Ram.Dp1.qv
            rw [dif_pos ha', dif_pos hb']; exact this
          · intro k hk
            have hk' : k < J.jobs := by omega
            have h1 := hJwB ⟨k, hk'⟩
            unfold Lax496464Proofs.Ram.DpMArr.wv; rw [dif_pos hk']
            rw [hBeq]; omega
        have hfa1' : ∀ a, a ∉ ["A", "SA", "SB", "PS", "QS", "DS", "WS"] →
            σ1.arrs a = (initEnv (ext4 (y ++ [W])) (y ++ [W])).arrs a :=
          fun a ha => hfa1 a (fun h => ha (sortSetup3_warrs a h))
        have hCPre : CPre4 J I.jobs I.machines W Ps σ1 := by
          refine ⟨?_, ?_, ?_, ?_, hn1, hm1, hsn1, hW1, ?_, ?_, ?_, ?_⟩
          · simp only [PSL, hJn]; exact hPS
          · simp only [QSL, hJn]; exact hQS
          · simp only [DSL, hJn]; exact hDS
          · simp only [WSL, hJn]; exact hWS
          · rw [hfa1' "NX" (by decide)]; simp [initEnv, ext4, hjc]
          · rw [hfa1' "PW" (by decide)]; simp [initEnv, ext4, hmc]
          · rw [hfa1' "VALID" (by decide)]; simp [initEnv, ext4, hjc, hmc]
          · rw [hfa1' "TAB" (by decide)]; simp [initEnv, ext4, hjc, hmc, hps]
        obtain ⟨σ2, hr2, ⟨hzk, hR2, hW2, hlenT, hDI⟩, hfv2, hfa2, -, hout2⟩ :=
          (core4_spec hCI).frame.run (σ := σ1) hCPre
        have hout2' : σ2.out = [] := by rw [hout2 core4_noWrite]; exact hout1
        set code := codeL I.jobs I.machines (List.range (min I.machines I.jobs)) with hcode
        have hcodeN : code < (I.jobs + 1) ^ I.machines :=
          (Lax496464Proofs.Ram.D2Core.sl_range I.jobs I.machines).codeL_lt
        have hcm : code * (Ps + 1) < (I.jobs + 1) ^ I.machines * (Ps + 1) :=
          Nat.mul_lt_mul_of_pos_right hcodeN (Nat.succ_pos Ps)
        have hNB' : (I.jobs + 1) ^ I.machines * (Ps + 1) < B := by rw [Nat.mul_comm]; exact hNPB
        have hval : (σ2.arrs "TAB").getD (code * (Ps + 1)) 0 ≤ W := hDI.2 _
        obtain ⟨σ3, hr3, hout3⟩ :=
          (finishCom4_spec hB2 code Ps W (σ2.arrs "TAB") [] (by rw [hlenT]; exact hcm) hval
            (by omega) (by omega) (by omega) (by omega)).run
            ⟨hzk, hR2, hW2, rfl, hout2'⟩
        refine ⟨ext4 (y ++ [W]), σ3, ?_, ?_⟩
        · refine (hr1.seq (Run.ite_false hc1 (Run.ite_false hc2 (hr2.seq hr3)))).mono ?_
          rw [hK]; unfold cost4; rw [if_pos ⟨hn1', hm1'⟩]; simp only [Cond.size, Expr.size]; omega
        · rw [hout3, List.nil_append]
          have hDI' : DTabOK J J.jobs J.machines W Ps ((I.jobs + 1) ^ I.machines) 0
              (σ2.arrs "TAB") := by rw [hJn, hJm]; exact hDI.1
          have hiff := hasWeight_iff_tab (J := J) hJest (W := W) (R := Ps)
            (N := (I.jobs + 1) ^ I.machines) (T := σ2.arrs "TAB") (le_of_eq hsumJ) hDI'
          rw [hJn, hJm] at hiff
          have hsame : HasWeight I W ↔ (σ2.arrs "TAB").getD (code * (Ps + 1)) 0 = W :=
            (hHW W).symm.trans hiff
          by_cases h0 : (σ2.arrs "TAB").getD (code * (Ps + 1)) 0 = W
          · have hy1 : Yes (y ++ [W]) := hYes.mpr (hsame.mpr h0)
            rw [if_pos h0, if_pos hy1]
          · have hy1 : ¬ Yes (y ++ [W]) := fun h => h0 (hsame.mp (hYes.mp h))
            rw [if_neg h0, if_neg hy1]


open Lax496464Proofs.Ram.Fits (maxEntry_mem)

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc4 : ℕ := 64 * Lax496464Proofs.Ram.Fits.const L4 + 100000

theorem cc4_ge : 64 * Lax496464Proofs.Ram.Fits.const L4 ≤ cc4 := by unfold cc4; omega

theorem hne4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, Fits (Lax496464Proofs.Ram.Fits.const L4) w x := by
  rintro x ⟨-, hxFits, -, -⟩
  exact Lax496464Proofs.Ram.Corollary1Prog.fits_mono hxFits (by have := cc4_ge; omega)

theorem hTab4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, Lax496464Proofs.Ram.Fits.const L4 * T4 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne4 w x hx
  obtain ⟨-, hxFits, hTabHyp, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  set κ := Lax496464Proofs.Ram.Fits.const L4 with hκ
  set M := x.length + maxEntry x + 1 with hM
  set RN := (preSum x + 1) * (jobCount x + 1) ^ machineCount x with hRN
  have hRN1 : 1 ≤ RN := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hcc : 64 * κ ≤ cc4 := cc4_ge
  have hM1 : 1 ≤ M := by omega
  have hA : κ * (4 * maxEntry x + 20) ≤ 24 * κ * M := by
    have : 4 * maxEntry x + 20 ≤ 24 * M := by omega
    calc κ * (4 * maxEntry x + 20) ≤ κ * (24 * M) := Nat.mul_le_mul_left _ this
      _ = 24 * κ * M := by ring
  have hA2 : 2 * (24 * κ * M) ≤ 2 ^ w := by
    calc 2 * (24 * κ * M) = (48 * κ) * M := by ring
      _ ≤ cc4 * M := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ w := hf
  have hB : 16 * (4 * κ * RN) ≤ 2 ^ w := by
    calc 16 * (4 * κ * RN) = (64 * κ) * RN := by ring
      _ ≤ cc4 * RN := Nat.mul_le_mul_right _ hcc
      _ = cc4 * (preSum x + 1) * (jobCount x + 1) ^ machineCount x := by rw [hRN]; ring
      _ ≤ 2 ^ w := hTabHyp
  have hsplit : κ * T4 x = κ * (4 * maxEntry x + 20) + 4 * κ * RN := by
    unfold T4; rw [← hRN]; ring
  rw [hsplit]
  omega

theorem hT4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w,
    Layout.const L4 * cost4 (jobCount x) (machineCount x) (preSum x) + 1 ≤
      cc4 * (preSum x + 1) * (jobCount x + 1) ^ machineCount x + cc4 * sortCost x := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hb := cost4_le (m := machineCount x) (R := preSum x) hnl
  have hc : Layout.const L4 = 10 := rfl
  rw [hc]
  have hcc : 100000 ≤ cc4 := by unfold cc4; omega
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  rw [hsc]
  have h1 : 100000 * ((preSum x + 1) * (jobCount x + 1) ^ machineCount x) ≤
      cc4 * (preSum x + 1) * (jobCount x + 1) ^ machineCount x := by
    rw [mul_assoc]; exact Nat.mul_le_mul_right _ hcc
  have h2 := Nat.mul_le_mul_right ((x.length + 1) * (Nat.log 2 (x.length + 2) + 1)) hcc
  omega

open Classical in
/--
---
conclusion: Lax496464.Corollary2.corollary2_time
---
Corollary 2 as a word RAM program. Read the word, sort the jobs by start time, sum the
preprocessing times into `P`, and fill the dual table of Section 3 over sets of thresholds written
as base-`(n+1)` numbers: the numbers are visited from the top, each is decided to be a code of a
set or not by a recurrence, and the two sets `X₁`, `X₂` of recursion (1) are found by one scan of
its digits (`O(|X|)`, independent of `P`), after which its `P+1` cells cost `O(1)` each. The table
records, for each instant `t = 0 … P`, the largest weight attainable from `t`, capped at the
threshold (so its entries never leave the word); the block of the empty set is zero, and the answer
is the entry of the first `m` indices at instant `0`. The sets contribute `Σ(|X|+1) ≤ 2 (n+1)^m` in
all. The domain restricts to positive processing times, the paper's standing assumption for
Lemma 1's recursion. The running time is `c (P+1) (n+1)^m + c · sortCost`: no work per machine beyond the `O(|X|)`
scan of a set.
-/
theorem corollary2_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        c * (preSum x + 1) * (jobCount x + 1) ^ machineCount x ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (preSum x + 1) * (jobCount x + 1) ^ machineCount x + c * sortCost x) :=
  ⟨compileProgram L4 prog4, cc4, fun w =>
    computesInTime_of_solves_fits (hne4 w) (hfits4 w) (hTab4 w) (prog4_solves cc4 w) (hT4 w)⟩

example : type_of% @Lax496464.Corollary2.corollary2_time := corollary2_time_proved

end Lax496464Proofs.Ram.D4Final
