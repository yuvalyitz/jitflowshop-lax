import Lax496464Proofs.Ram.Q3Prog
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.Corollary1Prog
import Lax496464.Theorem3

/-!
# Theorem 3, the Profile Sweep: the Running Time Statement

`prog3` (front end, core, read-off) solves the decision problem within `cost3`, at every word length
at which the concept's two admissibility clauses hold, and `cost3` is `O(N (n+1) + sortCost)` with
`N = (W+1)(m+1)^qmax`.  This is `Lax496464.Theorem3.theorem3_qmax_time`, on the domain that also
carries the standing assumption of Lemma 3: positive processing times.
-/

namespace Lax496464Proofs.Ram.Q3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity
open Lax496464Proofs.Ram.Q3Prog Lax496464Proofs.Ram.Q3Core Lax496464Proofs.Ram.Q3Loop
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts fits_mono)

/-- The layout: every scalar and array every part of the program mentions. -/
def L3 : Layout :=
  ⟨["n", "m", "len", "i", "v", "W", "en", "sn", "boff", "bi", "bt", "bv", "si", "sw", "snp", "spc",
    "slo", "smid", "shi", "sj", "sk", "sx", "sy", "ct1", "ct2", "sc", "stl",
    "qm", "bb", "w1", "N", "cinf", "jj", "pt", "pj", "qj", "dj", "wj", "rf", "dl", "pwd", "pwq",
    "ex", "ok", "u1", "u2", "u3", "u4", "u5", "u6"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "T", "S", "G"], 12⟩

set_option maxHeartbeats 8000000 in
theorem prog3_ok : Com.Ok L3 prog3 := by
  simp [prog3, Lax496464Proofs.Ram.Q3Front.frontQ, Lax496464Proofs.Ram.Decode.readInstance,
    Lax496464Proofs.Ram.Decode.readLoop, Lax496464Proofs.Ram.Decode.readBody,
    Lax496464Proofs.Ram.EstSort.estSortCom,
    Lax496464Proofs.Ram.EstSort.fillIdent, Lax496464Proofs.Ram.EstSort.estCmp,
    Lax496464Proofs.Ram.EstSort.estSums, Lax496464Proofs.Ram.EstSort.estDecide,
    Lax496464Proofs.Ram.Sort.tlSetup, Lax496464Proofs.Ram.Sort.moveK,
    Lax496464Proofs.Ram.Sort.mergeBody, Lax496464Proofs.Ram.Sort.mergeLoop,
    Lax496464Proofs.Ram.Sort.blockSetup, Lax496464Proofs.Ram.Sort.blockBody,
    Lax496464Proofs.Ram.Sort.blockLoop, Lax496464Proofs.Ram.Sort.copyLoop,
    Lax496464Proofs.Ram.Sort.npLoop, Lax496464Proofs.Ram.Sort.passCom,
    Lax496464Proofs.Ram.Sort.passBody, Lax496464Proofs.Ram.Sort.sortCom,
    Lax496464Proofs.Ram.BuildSorted.buildSorted, Lax496464Proofs.Ram.BuildSorted.buildRow,
    Lax496464Proofs.Ram.W3Front.buildW,
    coreCom, mainLoop, eventCom, Lax496464Proofs.Ram.Q3Event.prepCom,
    Lax496464Proofs.Ram.Q3Event.loadCom, Lax496464Proofs.Ram.Q3Event.refCom,
    Lax496464Proofs.Ram.Q3Init.powCom, Lax496464Proofs.Ram.Q3Init.powBody,
    Lax496464Proofs.Ram.Q3Init.maxCom, Lax496464Proofs.Ram.Q3Init.maxBody,
    Lax496464Proofs.Ram.Q3Init.gInitCom, Lax496464Proofs.Ram.Q3Init.gBody,
    Lax496464Proofs.Ram.Q3Init.gCalc, Lax496464Proofs.Ram.Q3Init.gWrite,
    Lax496464Proofs.Ram.Q3Passes.fillCom, Lax496464Proofs.Ram.Q3Passes.fillBody,
    Lax496464Proofs.Ram.Q3Passes.margCom, Lax496464Proofs.Ram.Q3Passes.margBody,
    Lax496464Proofs.Ram.Q3Passes.takeCom, Lax496464Proofs.Ram.Q3Passes.takeBody,
    Lax496464Proofs.Ram.Q3Passes.takeCond, Lax496464Proofs.Ram.Q3Passes.takeP1,
    Lax496464Proofs.Ram.Q3Passes.takeP2, Lax496464Proofs.Ram.Q3Passes.takeP3,
    Lax496464Proofs.Ram.Q3Finish.finishCom, Lax496464Proofs.Ram.Q3Finish.finScan,
    Lax496464Proofs.Ram.Q3Finish.finBody,
    Com.Ok, Expr.Ok, Cond.Ok, L3, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

/-! ## The table sizes, as functions of the word -/

/-- The number of profiles `(m+1)^qmax`. -/
def btX (x : List ℕ) : ℕ := (machineCount x + 1) ^ qmaxOf x

/-- The number of table cells `(m+1)^qmax · (W+1)`. -/
def NX (x : List ℕ) : ℕ := btX x * (threshold x + 1)

/-- Room for every intermediate value: the table, plus the word's own numbers. -/
def T3 (x : List ℕ) : ℕ := NX x + 5 * maxEntry x + 40

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext3 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" then jobCount x
  else if a = "T" ∨ a = "S" then NX x
  else if a = "G" then btX x
  else 0

/-- The cost bound, as it comes out of `prog3_spec`. -/
def cost3X (x : List ℕ) : ℕ :=
  cost3 (jobCount x) (NX x) (qmaxOf x) (btX x) (machineCount x + 1)

/-- Decision words of an instance with positive processing times, that fit at word length `w`
with constant `c` and whose profile table `c · (W+1) · (m+1)^qmax · (n+1)` is a word. -/
def Dom3 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    c * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j)}

theorem foldr_max_le' {l : List ℕ} {M : ℕ} (h : ∀ v ∈ l, v ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

open Classical in
set_option maxHeartbeats 8000000 in
theorem prog3_solves (cc w : ℕ) :
    Solves L3 prog3 (Dom3 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T3 x)) cost3X where
  ok := prog3_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, hbig, hxQ⟩ := hx
    obtain ⟨I, W, hdecx⟩ := hxDI
    have hdec := hdecx
    obtain ⟨y, hxy, hEnc⟩ := hdecx
    subst hxy
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    obtain ⟨hthr, -, -⟩ := Lax496464Proofs.Ram.Q3Front.threshold_eq (W := W) hEnc
    set x : List ℕ := y ++ [W] with hxdef
    set B : ℕ := bound x (T3 x) with hBdef
    have hxlen : x.length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [hxdef, List.length_append, List.length_singleton]; omega
    have hmem_of_idx : ∀ k, k < x.length → x.getD k 0 ∈ x :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hBeq : B = x.length + maxEntry x + 1 + (NX x + 5 * maxEntry x + 40) := by
      rw [hBdef]; rfl
    have hIjm : (I.jobs : ℕ) ≤ maxEntry x := by
      rw [← hjc]; exact le_maxEntry (hmem_of_idx 0 (by omega))
    have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hpe j]; exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
    have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hqe j]
      exact le_maxEntry (hmem_of_idx (2 + jobCount x + j) (by rw [hjc]; have := j.isLt; omega))
    have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hde j]
      exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount x + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hwB : ∀ j : I.Job, (I.w j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hwe j]
      exact le_maxEntry (hmem_of_idx (2 + 3 * jobCount x + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hmach : I.machines ≤ maxEntry x := by
      rw [← hmc]; exact le_maxEntry (hmem_of_idx 1 (by omega))
    have hWle : W ≤ maxEntry x := le_maxEntry (by simp [hxdef])
    have hqmle : qmaxOf x ≤ maxEntry x := by
      unfold qmaxOf
      refine foldr_max_le' (fun v hv => ?_)
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      have hk' : k < I.jobs := by have := List.mem_range.mp hk; rwa [hjc] at this
      have := hqB ⟨k, hk'⟩
      rw [hqe ⟨k, hk'⟩] at *
      exact this
    have hbtN : btX x ≤ NX x := by
      unfold NX; exact Nat.le_mul_of_pos_right _ (by omega)
    have hbtpos : 1 ≤ btX x := by
      unfold btX; exact Nat.one_le_pow _ _ (by omega)
    have hNpos : 1 ≤ NX x := by omega
    have hB20 : 20 < B := by rw [hBeq]; omega
    have hxB : ∀ v ∈ x, v < B := fun v hv => lt_bound hv
    have hnB : 4 * I.jobs + 8 < B := by rw [hBeq]; omega
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
    have hT3 : ∀ a b c : I.Job, (I.d a : ℕ) + I.p b + I.q c + 9 < B := fun a b c => by
      have h1 := hdB a; have h2 := hpB b; have h3 := hqB c; rw [hBeq]; omega
    have hwB' : ∀ j : I.Job, (I.w j : ℕ) + 8 < B := fun j => by
      have h1 := hwB j; rw [hBeq]; omega
    have hmB : I.machines + 8 < B := by rw [hBeq]; omega
    have hWB : W + 8 < B := by rw [hBeq]; omega
    have hqmB : qmaxOf x + 8 < B := by rw [hBeq]; omega
    have hbtB : btX x + 8 < B := by rw [hBeq]; omega
    have hNB : NX x + 8 < B := by rw [hBeq]; omega
    have hpre : (fun σ : Env => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs ∧
        (σ.arrs "T").length = NX x ∧ (σ.arrs "S").length = NX x ∧
        σ.arrs "G" = List.replicate (btX x) 0) (initEnv (ext3 x) x) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext3, hjc]
    obtain ⟨σ', hr, hout⟩ :=
      (prog3_spec (bb := machineCount x + 1) (bt := btX x) (w1 := threshold x + 1) (N := NX x)
        (qm := qmaxOf x) hdec hqpos hB20 hxB hnB hpqB hdq hd2B hdd hdq2 hmB hWB rfl
        (by rw [hmc]) rfl (by rw [hthr]) rfl hqmB hbtB hNB hT3 hwB').run hpre
    refine ⟨ext3 x, σ', ?_, hout⟩
    have hKeq : cost3X x = cost3 I.jobs (NX x) (qmaxOf x) (btX x) (machineCount x + 1) := by
      unfold cost3X; rw [hjc]
    rw [hKeq]
    exact hr


/-! ## The running time -/

/-- The cost of the whole program is `O(N (n+1) + n log n)`. -/
theorem cost3_le {n N qm bt bb len : ℕ} (hbt : bt = bb ^ qm) (hbb : 1 ≤ bb) (hbtN : bt ≤ N)
    (hN1 : 1 ≤ N) (hnl : n ≤ len) :
    cost3 n N qm bt bb ≤ 390 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) + 2000 * (N * (n + 1)) := by
  have hsK := Lax496464Proofs.Ram.Sort.sortK_le 90 n len hnl
  have hpow : powK bb qm ≤ 12 * N + 12 := by
    unfold powK
    split_ifs with h
    · omega
    · have h2 : 2 ≤ bb := by omega
      have : qm < bb ^ qm := Nat.lt_pow_self (by omega)
      omega
  have hev : evK N qm bb ≤ 112 + 306 * N := by unfold evK takeK; omega
  have hE : (evK N qm bb + 4 + 4) * n ≤ (120 + 306 * N) * n :=
    Nat.mul_le_mul_right _ (by omega)
  have hQ : (120 + 306 * N) * n = 120 * n + 306 * (N * n) := by ring
  have hNn : n ≤ N * n := Nat.le_mul_of_pos_left _ (by omega)
  have hP : N * (n + 1) = N * n + N := by ring
  unfold cost3 coreK finK
  omega

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc3 : ℕ := 100000

theorem const_L3 : const L3 = 148 := by decide

theorem hne3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, Fits (const L3) w x := by
  rintro x ⟨-, hxFits, -, -⟩
  exact fits_mono hxFits (by rw [const_L3]; unfold cc3; omega)

theorem hTab3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, const L3 * T3 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne3 w x hx
  obtain ⟨-, hxFits, hbig, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  have hP : cc3 * (NX x * (jobCount x + 1)) ≤ 2 ^ w := by
    have : cc3 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) =
        cc3 * (NX x * (jobCount x + 1)) := by unfold NX btX; ring
    rw [← this]; exact hbig
  have hNN : NX x ≤ NX x * (jobCount x + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold T3
  rw [const_L3]
  unfold cc3 at hf hP
  omega

theorem hT3c (w : ℕ) : ∀ x ∈ Dom3 cc3 w, Layout.const L3 * cost3X x + 1 ≤
    cc3 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) +
      cc3 * sortCost x := by
  intro x hx
  have hx0 := hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hbtpos : 1 ≤ btX x := by unfold btX; exact Nat.one_le_pow _ _ (by omega)
  have hbtN : btX x ≤ NX x := by unfold NX; exact Nat.le_mul_of_pos_right _ (by omega)
  have hc := cost3_le (n := jobCount x) (N := NX x) (qm := qmaxOf x) (bt := btX x)
    (bb := machineCount x + 1) (len := x.length) rfl (by omega) hbtN (by omega) hnl
  have hP : cc3 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) =
      cc3 * (NX x * (jobCount x + 1)) := by unfold NX btX; ring
  have hLc : Layout.const L3 = 10 := rfl
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  have hcc : cc3 = 100000 := rfl
  have hpos : 1 ≤ NX x * (jobCount x + 1) := Nat.mul_pos (by omega) (by omega)
  rw [hP, hsc, hLc, hcc]
  unfold cost3X
  omega

open Classical in
/--
---
conclusion: Lax496464.Theorem3.theorem3_qmax_time
---
The profile sweep of Section 5 as a word RAM program.  Read the word, sort the jobs by start time
(`O(n log n)`), compute `q_max` and a sentinel, then sweep the jobs in that order, carrying for
every profile `x` (how many selected jobs are due at each of the next `q_max` instants, a base
`m+1` number of `q_max` digits) and every weight `c ≤ W` the least preprocessing load of a feasible
selection of weight at least `c`.  One job is one marginalisation pass (the shift of the profile is
a division by a power of `m+1`, the low digits being minimised away) and one take pass, each
`O(1)` per table cell, so a job costs `O((m+1)^q_max (W+1))` and the whole run is within
`c · (W+1) · (m+1)^q_max · (n+1) + c · sortCost`.  The answer is read off the profiles at weight
`W`.  The correctness is that of recursion (5) in its repaired form (`Q3Model`); jobs may tie in
start time (`δ = 0`), no rescaling is needed.  The domain restricts to positive processing times,
the paper's standing assumption for Lemma 3, exactly as the concept's statement now says.
-/
theorem theorem3_qmax_time_proved : ∃ (prog : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        c * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1)
          ≤ 2 ^ w ∧ (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
        (jobCount x + 1) + c * sortCost x) :=
  ⟨compileProgram L3 prog3, cc3, fun w =>
    computesInTime_of_solves_fits (hne3 w) (hfits3 w) (hTab3 w) (prog3_solves cc3 w) (hT3c w)⟩

end Lax496464Proofs.Ram.Q3Final
