import Lax496464Proofs.Ram.T4Prog
import Lax496464.Theorem4

/-!
# Theorem 4: the greedy on the word RAM
-/

namespace Lax496464Proofs.Ram.T4Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity
open Lax496464Proofs.Ram.T4Prog Lax496464Proofs.Ram.T4Tail Lax496464Proofs.Ram.T4Job
open Lax496464Proofs.Ram.T4Step Lax496464Proofs.Ram.T4Expire Lax496464Proofs.Ram.T4Defs
open Lax496464Proofs.Ram.SegProg (tset tfind downLoop descend upLoop recomp halve)

/-- The layout: every scalar and array every part of the program mentions. -/
def L4 : Layout :=
  ⟨["n", "m", "v", "i", "len", "en", "sn", "sc", "si", "sx", "sy", "ct1", "ct2", "shi", "sj",
    "sk", "slo", "smid", "snp", "spc", "stl", "sw", "bi", "boff", "bt", "bv", "W", "ans",
    "cinf", "mi", "mv", "tN", "th", "tc", "ti", "t1", "t2", "tp", "tv", "jj", "sz", "run",
    "ok", "ta", "p0"],
   ["A", "SA", "SB", "PS", "QS", "DS", "TX", "TY"], 12⟩

set_option maxHeartbeats 4000000 in
theorem prog4_ok : Com.Ok L4 prog4 := by
  simp [prog4, tail4, Lax496464Proofs.Ram.Decode.readInstance,
    Lax496464Proofs.Ram.Decode.readLoop, Lax496464Proofs.Ram.Decode.readBody, Lax496464Proofs.Ram.EstSort.estSortCom,
    Lax496464Proofs.Ram.EstSort.fillIdent, Lax496464Proofs.Ram.EstSort.estCmp,
    Lax496464Proofs.Ram.EstSort.estSums, Lax496464Proofs.Ram.EstSort.estDecide,
    Lax496464Proofs.Ram.Sort.tlSetup, Lax496464Proofs.Ram.Sort.moveK,
    Lax496464Proofs.Ram.Sort.mergeBody, Lax496464Proofs.Ram.Sort.mergeLoop,
    Lax496464Proofs.Ram.Sort.blockSetup, Lax496464Proofs.Ram.Sort.blockBody,
    Lax496464Proofs.Ram.Sort.blockLoop, Lax496464Proofs.Ram.Sort.copyLoop,
    Lax496464Proofs.Ram.Sort.npLoop, Lax496464Proofs.Ram.Sort.passCom,
    Lax496464Proofs.Ram.Sort.passBody, Lax496464Proofs.Ram.Sort.sortCom, Lax496464Proofs.Ram.BuildSorted.buildSorted,
    Lax496464Proofs.Ram.BuildSorted.buildRow, Lax496464Proofs.Ram.Corollary1Init.maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody,
    Lax496464Proofs.Ram.T4Setup.sizeLoop, initScalars, mainLoop, stepJob, expire, expireBody, expireCond, tfind, downLoop,
    descend, dropLeaf, tset, upLoop, recomp, halve, okCom, okRun, insertJ, branch, dropMax,
    finalOut, Com.Ok, Expr.Ok, Cond.Ok, L4, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump, Lax496464Proofs.Ram.SegProg.V, Lax496464Proofs.Ram.SegProg.bump]

open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464.ProperInstances (Uniform)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext4 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "NX" then jobCount x
  else if a = "CC" ∨ a = "PC" then jobCount x + 1
  else if a = "TX" ∨ a = "TY" then 2 * 2 ^ (jobCount x - 1).size
  else 0

/-- Room for every intermediate value. -/
def T4 (x : List ℕ) : ℕ := 4 * maxEntry x + 20

/-- The cost bound, as it comes out of `prog4_spec`. -/
def cost4 (x : List ℕ) : ℕ :=
  Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x) + 500 * jobCount x + 1000 + tailK (jobCount x)

/-- Decision words of an instance with a common preprocessing time, unit weights and positive
processing times, that fit at word length `w` with constant `c`. -/
def Dom4 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
    (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}

open Classical in
theorem prog4_solves (cc w : ℕ) :
    Solves L4 prog4 (Dom4 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T4 x)) cost4 where
  ok := prog4_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, ⟨I0, W0, hdec0, hUn⟩, hxW1, hxQ1⟩ := hx
    obtain ⟨I, W, hdecx⟩ := hxDI
    obtain ⟨hI0, hW0⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique hdec0 hdecx
    have hI0' : I = I0 := hI0.symm
    have hW0' : W = W0 := hW0.symm
    subst hI0'
    subst hW0'
    obtain ⟨y, hxy, hEnc⟩ := hdecx
    subst hxy
    obtain ⟨p0, hp0⟩ := hUn
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    set B : ℕ := bound (y ++ [W]) (T4 (y ++ [W])) with hBdef
    have hxB : ∀ v ∈ (y ++ [W]), v < B := fun v hv => lt_bound hv
    have hxlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
    have hmem_of_idx : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 ∈ (y ++ [W]) :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hw1 : ∀ j : I.Job, I.w j = 1 := fun j => by
      rw [← hwe j]; exact hxW1 (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ1 (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hBeq : B = (y ++ [W]).length + maxEntry (y ++ [W]) + 1 +
        (4 * maxEntry (y ++ [W]) + 20) := by rw [hBdef]; rfl
    have hIjm : (I.jobs : ℕ) ≤ maxEntry (y ++ [W]) := by
      rw [← hjc]
      exact le_maxEntry (hmem_of_idx 0 (by omega))
    have hB2 : 2 < B := by rw [hBeq]; omega
    have hnB : 4 * I.jobs + 8 < B := by rw [hBeq]; omega
    have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hpe j]
      exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
    have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hqe j]
      exact le_maxEntry (hmem_of_idx (2 + jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hde j]
      exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount (y ++ [W]) + j) (by
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
    have hWB : W < B := by have h1 := hWle; rw [hBeq]; omega
    have hmB : I.machines < B := by have h1 := hmach; rw [hBeq]; omega
    -- the common preprocessing time
    obtain ⟨p, hpu, hp0'⟩ : ∃ p, (∀ j : I.Job, I.p j = p) ∧ (I.jobs = 0 → p = 0) := by
      by_cases hj : I.jobs = 0
      · exact ⟨0, fun j => absurd j.isLt (by omega), fun _ => rfl⟩
      · exact ⟨p0, hp0, fun h => absurd h hj⟩
    have hpB' : p < B := by
      by_cases hj : I.jobs = 0
      · rw [hp0' hj]; omega
      · have := hpB ⟨0, by omega⟩; rw [← hpu ⟨0, by omega⟩]; rw [hBeq]; omega
    have hpre : (fun σ => σ.inp = y ++ [W] ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1 ∧
        σ.arrs "TX" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0 ∧
        σ.arrs "TY" = List.replicate (2 * 2 ^ (I.jobs - 1).size) 0)
        (initEnv (ext4 (y ++ [W])) (y ++ [W])) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [initEnv, ext4, hjc]
    obtain ⟨σ6, hr6, hout6⟩ :=
      (prog4_spec ⟨y, rfl, hEnc⟩ hpu hp0' hw1 hqpos hB2 hxB hnB hpqB hdq hd2B hdd hdq2 hWB
        hpB' hmB).run hpre
    refine ⟨ext4 (y ++ [W]), σ6, ?_, hout6⟩
    have hKeq : cost4 (y ++ [W]) = Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs +
        1000 + tailK I.jobs := by
      unfold cost4; rw [hjc]
    rw [hKeq]
    exact hr6

/-! ## The running time -/

theorem expireCond_size : expireCond.size = 12 := by decide

theorem Kbody_le (h : ℕ) : Kbody h ≤ 500 * h + 420 := by
  unfold Kbody Kpop Kb
  rw [expireCond_size]; omega

theorem size_le_log {n len : ℕ} (hn : n ≤ len) : (n - 1).size ≤ Nat.log 2 (len + 2) + 1 := by
  apply Nat.size_le.mpr
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (len + 2)
  omega

/-- **The tail costs `O(n log n)`.** -/
theorem tailK_le {n len : ℕ} (hn : n ≤ len) :
    tailK n ≤ 1200 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  unfold tailK
  set A := len + 1 with hA
  set Lg := Nat.log 2 (len + 2) + 1 with hLg
  have hh : (n - 1).size ≤ Lg := size_le_log hn
  set h := (n - 1).size with hhdef
  have hK := Kbody_le h
  have hLg1 : 1 ≤ Lg := by omega
  have hAL : 1 ≤ A * Lg := Nat.mul_pos (by omega) (by omega)
  have h1 : n ≤ A * Lg := le_trans (by omega) (Nat.le_mul_of_pos_right A hLg1)
  have h2 : h ≤ A * Lg := le_trans hh (Nat.le_mul_of_pos_left Lg (by omega))
  have h3 : n * h ≤ A * Lg := Nat.mul_le_mul (by omega) hh
  have h4 : (Kbody h + 4) * n ≤ (500 * h + 424) * n := Nat.mul_le_mul_right _ (by omega)
  have h5 : (500 * h + 424) * n = 500 * (n * h) + 424 * n := by ring
  omega

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc4 : ℕ := 64 * Lax496464Proofs.Ram.Fits.const L4 + 100000

theorem cc4_ge : 64 * Lax496464Proofs.Ram.Fits.const L4 ≤ cc4 := by unfold cc4; omega

theorem hne4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, Fits (Lax496464Proofs.Ram.Fits.const L4) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact Lax496464Proofs.Ram.Corollary1Prog.fits_mono hxFits (by have := cc4_ge; omega)

theorem hTab4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w, Lax496464Proofs.Ram.Fits.const L4 * T4 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne4 w x hx
  obtain ⟨hxDI, hxFits, -, -, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  have hge : maxEntry x + 1 ≤ x.length + maxEntry x + 1 := by omega
  calc Lax496464Proofs.Ram.Fits.const L4 * T4 x
      = Lax496464Proofs.Ram.Fits.const L4 * (4 * maxEntry x + 20) := rfl
    _ ≤ Lax496464Proofs.Ram.Fits.const L4 * (20 * (x.length + maxEntry x + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = (20 * Lax496464Proofs.Ram.Fits.const L4) * (x.length + maxEntry x + 1) := by ring
    _ ≤ cc4 * (x.length + maxEntry x + 1) := by
        have := cc4_ge; exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ w := hf

theorem hT4 (w : ℕ) : ∀ x ∈ Dom4 cc4 w,
    Layout.const L4 * cost4 x + 1 ≤ cc4 * sortCost x := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (Lax496464Proofs.Ram.Corollary1Prog.decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hsK := Lax496464Proofs.Ram.Sort.sortK_le 90 (jobCount x) x.length hnl
  have htail := tailK_le hnl
  set A := x.length + 1 with hA
  set Lg := Nat.log 2 (x.length + 2) + 1 with hLg
  have hLg1 : 1 ≤ Lg := by omega
  have hAL : 1 ≤ A * Lg := Nat.mul_pos (by omega) (by omega)
  have h1 : jobCount x ≤ A * Lg := le_trans (by omega) (Nat.le_mul_of_pos_right A hLg1)
  have hcc : 100000 ≤ cc4 := by unfold cc4; omega
  have hc : Layout.const L4 = 10 := rfl
  have hsc : sortCost x = A * Lg := rfl
  rw [hsc]
  unfold cost4
  rw [hc]
  have := Nat.mul_le_mul_right (A * Lg) hcc
  omega

open Classical in
/--
---
conclusion: Lax496464.Theorem4.theorem4_greedy_time
---
The greedy of Section 6.1 as a word RAM program: read the word, sort the jobs by start time
(`O(n log n)`), then consider the jobs in that order, keeping the running jobs in two maximum
trees over the job numbers — one keyed by due date (whose root gives the job to drop) and one by
`BIG - d` (whose root gives the next job to end) — and counting the members of the set that have
already ended. Every step costs `O(log n)`, so the whole run is within `c · sortCost`. The
statement is exactly the concept's, including its positive-processing-time clause (the paper's
standing assumption for Lemma 4).
-/
theorem theorem4_greedy_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        (∃ I W, EncodesDecisionInstance x I W ∧ Uniform I) ∧
        (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * sortCost x) :=
  ⟨compileProgram L4 prog4, cc4, fun w =>
    computesInTime_of_solves_fits (hne4 w) (hfits4 w) (hTab4 w) (prog4_solves cc4 w) (hT4 w)⟩

end Lax496464Proofs.Ram.T4Final
