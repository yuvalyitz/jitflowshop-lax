import Lax496464Proofs.Ram.W3Sweep
import Lax496464Proofs.Ram.W3FrontX
import Lax496464Proofs.Ram.W3Width
import Lax496464Proofs.Ram.W3BMono
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.T4Final
import Lax496464.Theorem3

/-!
# Theorem 3, the Endpoint Sweep, on the Word RAM
-/

namespace Lax496464Proofs.Ram.W3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity
open Lax496464Proofs.Ram.W3Loops (V)
open Lax496464Proofs.Ram.W3Sweep Lax496464Proofs.Ram.W3SweepEv Lax496464Proofs.Ram.W3Loops

/-- The answer: `1` iff `TB[W] < cinf`, i.e. iff `TB[0 * W1 + W]` is finite. -/
def finish : Com :=
  .ite (.lt (.get "TB" (V "W")) (V "cinf")) (.write (.lit 1)) (.write (.lit 0))

/-- **The whole program.** -/
def prog3 : Com := .seq Lax496464Proofs.Ram.W3Front2.sortSetup3 (.seq core finish)

/-- The layout. -/
def L3 : Layout :=
  ⟨["n", "m", "v", "i", "len", "en", "sn", "sc", "si", "sx", "sy", "ct1", "ct2", "shi", "sj",
    "sk", "slo", "smid", "snp", "spc", "stl", "sw", "bi", "boff", "bt", "bv", "W", "cinf", "mi",
    "mv", "N", "sh", "X", "c", "ri", "tv", "gx", "sp", "sq", "sd", "b2", "W1", "MK", "n2", "ci",
    "nx", "fp", "ip", "kp", "ist", "jj", "bb", "p0", "ck", "ans"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "TB", "PC", "FS", "SLT", "P2"], 12⟩

set_option maxHeartbeats 4000000 in
theorem prog3_ok : Com.Ok L3 prog3 := by
  simp [prog3, finish, core, initCore, sweepLoop, stepBody, decideCom, startEv, dueEv, dueSetup,
    dueTail, pickRecycle, pickFresh, setParams, startTail, startCommon, fillTB, fillBody,
    Lax496464Proofs.Ram.W3Front2.sortSetup3, Lax496464Proofs.Ram.W3Front.buildW,
    Lax496464Proofs.Ram.W3Front.dueSortCom, Lax496464Proofs.Ram.W3Front.dueCmp,
    Lax496464Proofs.Ram.W3Front.dueLoad,
    dueLoop, dueBody, startLoop, startBody, startSet, growPC, growBody,
    Lax496464Proofs.Ram.Decode.readInstance,
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
    Lax496464Proofs.Ram.BuildSorted.buildSorted,
    Lax496464Proofs.Ram.BuildSorted.buildRow, Lax496464Proofs.Ram.Corollary1Init.maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody,
    condExpr, Com.Ok, Expr.Ok, Cond.Ok, L3, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

theorem finish_spec {B : ℕ} (hB : 1 < B) (W INF t : ℕ) (TB : List ℕ) (hWl : W < TB.length)
    (hWB : W < B) (htB : t < B) (hINF : INF < B) :
    Spec B (fun σ => σ.vars "W" = W ∧ σ.vars "cinf" = INF ∧ σ.arrs "TB" = TB ∧
        TB.getD W 0 = t) finish
      (fun σ σ' => σ'.out = σ.out ++ [if t < INF then 1 else 0]) 12 := by
  run_vcg
  all_goals simp_all

open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464Proofs.Ram.W3Model (infOf maxd d_le_maxd)
open Lax496464Proofs.Ram.W3Width (widthJ_le_widthOf sa_eq)
open Lax496464Proofs.Ram.W3FrontX (sortSetup3_spec')
open Lax496464Proofs.Ram.Dp1 (pv qv dv)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext3 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "FS" ∨
      a = "SLT" then jobCount x
  else if a = "TB" then 2 ^ widthOf x * (threshold x + 1)
  else if a = "PC" then 2 ^ widthOf x
  else if a = "P2" then widthOf x
  else 0

/-- Room for every intermediate value. -/
def T3 (x : List ℕ) : ℕ := 2 ^ widthOf x * (threshold x + 1) + 8 * maxEntry x + 40

/-- The cost bound. -/
def cost3 (x : List ℕ) : ℕ :=
  (2 * Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x) + 1000 * jobCount x + 2000) +
    Kcore (jobCount x) (widthOf x) (threshold x + 1) + 12

theorem threshold_eq' {y : List ℕ} {I : Instance} (W : ℕ) (hEnc : EncodesInstance y I) :
    threshold (y ++ [W]) = W := by
  obtain ⟨hjc, -⟩ := decision_word_facts (W := W) hEnc
  unfold threshold
  rw [hjc]
  have : 2 + 4 * I.jobs = y.length := hEnc.length_eq.symm
  rw [this, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem maxd_lt {J : Instance} {B : ℕ} (h : ∀ j : J.Job, J.d j + 2 < B) (hB : 2 < B) :
    maxd J + 2 < B := by
  unfold maxd
  refine Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt (fun v hv => ?_) hB
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
  exact h j

open Classical in
set_option maxHeartbeats 8000000 in
theorem prog3_run {x : List ℕ} (hxD : x ∈ DecisionInstances)
    (hqp : ∀ j < jobCount x, 0 < procTime x j) :
    ∃ σ', Run (bound x (T3 x)) prog3 (initEnv (ext3 x) x) σ' (cost3 x) ∧
      σ'.out = if Yes x then [1] else [0] := by
  obtain ⟨I, W, y, hxy, hEnc⟩ := hxD
  subst hxy
  obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
  have hthr : threshold (y ++ [W]) = W := threshold_eq' W hEnc
  set X : List ℕ := y ++ [W] with hXdef
  have hdec : EncodesDecisionInstance X I W := ⟨y, rfl, hEnc⟩
  have hXlen : X.length = 3 + 4 * I.jobs := by
    have := hEnc.length_eq; simp only [hXdef, List.length_append, List.length_singleton]; omega
  have hmem_of_idx : ∀ k, k < X.length → X.getD k 0 ∈ X := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  set M : ℕ := maxEntry X with hMdef
  have hIjm : I.jobs ≤ M := by
    rw [← hjc]; exact le_maxEntry (hmem_of_idx 0 (by omega))
  have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ M := fun j => by
    rw [← hpe j]; exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
  have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ M := fun j => by
    rw [← hqe j]
    exact le_maxEntry (hmem_of_idx (2 + jobCount X + j) (by rw [hjc]; have := j.isLt; omega))
  have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ M := fun j => by
    rw [← hde j]
    exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount X + j) (by rw [hjc]; have := j.isLt; omega))
  have hmach : I.machines ≤ M := by rw [← hmc]; exact le_maxEntry (hmem_of_idx 1 (by omega))
  have hWle : W ≤ M := le_maxEntry (by simp [hXdef])
  have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
    rw [← hqe j]; exact hqp j (by rw [hjc]; exact j.isLt)
  -- the bounds
  set wd : ℕ := widthOf X with hwddef
  set P : ℕ := 2 ^ wd * (W + 1) with hPdef
  have hBeq : bound X (T3 X) = X.length + M + 1 + (P + 8 * M + 40) := by
    show X.length + maxEntry X + 1 + (2 ^ widthOf X * (threshold X + 1) + 8 * maxEntry X + 40) = _
    rw [hthr]
  rw [hBeq]
  set B : ℕ := X.length + M + 1 + (P + 8 * M + 40) with hBdef
  set B0 : ℕ := 4 * M + 10 with hB0def
  have hB0B : 2 * B0 ≤ B := by omega
  have hB0B' : B0 ≤ B := by omega
  have hxB : ∀ v ∈ X, v < B0 := fun v hv => by have := le_maxEntry hv; omega
  have hnB : 4 * I.jobs + 5 < B0 := by omega
  -- the front end
  have hpre : (fun σ : Env => σ.inp = X ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs)
      (initEnv (ext3 X) X) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext3, hjc]
  obtain ⟨σ1, hr1, ⟨J, ⟨f, hJf⟩, hEst, hJjobs, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW,
      hPS, hQS, hDS, hWS, hperm, hlex, hn, hm, hsn, hW, hinp, hout, hlen⟩, hfv1, hfa1, -, -⟩ :=
    (sortSetup3_spec' (B := B0) hdec hqpos (by omega) hxB hnB
      (fun j => by have := hpB j; have := hqB j; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)
      (fun j => by have := hdB j; omega)
      (fun a b => by have := hdB a; have := hdB b; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)).frame.run hpre
  have hr1' : Run B Lax496464Proofs.Ram.W3Front2.sortSetup3 (initEnv (ext3 X) X) σ1 _ :=
    Lax496464Proofs.Ram.W3BMono.Run.mono_bound hB0B' hr1
  -- the sweep
  have hwd : Lax496464Proofs.Ram.W3Model.widthJ J ≤ wd := by
    subst hJf
    exact widthJ_le_widthOf W hEnc f
  have hJd2' : ∀ j : J.Job, J.d j + 2 < B0 := hJd2
  have hmaxd : maxd J + 2 < B0 := maxd_lt hJd2' (by omega)
  have hlenA : ∀ a, (σ1.arrs a).length = ext3 X a := fun a => by
    rw [hlen a]; simp [initEnv]
  have hTBl : (σ1.arrs "TB").length = P := by
    rw [hlenA "TB"]; simp [ext3, hthr, hPdef, hwddef]
  have hPCl : (σ1.arrs "PC").length = 2 ^ wd := by
    rw [hlenA "PC"]; simp [ext3, hwddef]
  have hFSl : (σ1.arrs "FS").length = I.jobs := by
    rw [hlenA "FS"]; simp [ext3, hjc]
  have hSLTl : (σ1.arrs "SLT").length = I.jobs := by
    rw [hlenA "SLT"]; simp [ext3, hjc]
  have hP2l : (σ1.arrs "P2").length = wd := by
    rw [hlenA "P2"]; simp [ext3, hwddef]
  have hTB1 : σ1.arrs "TB" = List.replicate P 0 := by
    have : "TB" ∉ Lax496464Proofs.Ram.W3Front2.sortSetup3.warrs := fun h => by
      have := Lax496464Proofs.Ram.W3Front2.sortSetup3_warrs _ h
      simp at this
    rw [hfa1 "TB" this]
    simp [initEnv, ext3, hthr, hPdef, hwddef]
  have hPos : 0 < P := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have hN : Lax496464Proofs.Ram.W3SweepEv.Nums J wd (W + 1) (infOf J) B P (2 ^ wd) I.jobs I.jobs wd := by
    have hJp : ∀ j : J.Job, (J.p j : ℕ) + J.q j < B0 := hJpq
    have hjj : J.jobs = I.jobs := hJjobs
    refine ⟨by omega, by omega, le_rfl, le_rfl, by omega, by omega, le_rfl, by omega, by
        show maxd J + 2 < B; omega, by omega, by omega, fun j => ?_, fun j => ?_, fun j => ?_,
      fun a b => ?_, fun j => ?_, by show 0 < maxd J + 2; omega⟩
    · have := hJp j; have : infOf J < B0 := hmaxd; omega
    · have := hJd2' j; omega
    · have := hJw j; omega
    · have := hJdq a b; omega
    · have := d_le_maxd (J := J) j; show J.d j ≤ maxd J + 2; omega
  have hjj : J.jobs = I.jobs := hJjobs
  have hPS' : σ1.arrs "PS" = (List.range J.jobs).map (pv J) := by rw [hjj]; exact hPS
  have hQS' : σ1.arrs "QS" = (List.range J.jobs).map (qv J) := by rw [hjj]; exact hQS
  have hDS' : σ1.arrs "DS" = (List.range J.jobs).map (dv J) := by rw [hjj]; exact hDS
  have hWS' : σ1.arrs "WS" = (List.range J.jobs).map (Lax496464Proofs.Ram.DpMArr.wv J) := by
    rw [hjj]; exact hWS
  have hSA' : σ1.arrs "SA" = (Lax496464Proofs.Ram.W3Model.dueOrder J).map Fin.val := by
    refine Lax496464Proofs.Ram.W3Width.sa_eq J _ ?_ ?_
    · rw [hjj]; exact hperm
    · exact hlex
  obtain ⟨σ2, hr2, hc1, hc2, hc3, hc4, hc5, hc6, hctab, hcle, hclen, hcfr⟩ :=
    (core_spec (B := B) (J := J) (wd := wd) (W := W) (W1 := W + 1) (LTB := P) (LPC := 2 ^ wd)
      (LFS := I.jobs) (LSLT := I.jobs) (LP2 := wd) rfl hN hEst hJq hwd (by omega)).run
      ⟨by rw [hn, hjj], by rw [hsn, hjj], by rw [hm, hJm], hW, hPS', hQS', hDS', hWS', hSA',
        hTBl, hPCl, hFSl, hSLTl, hP2l, by rw [hTB1]; intro j; simp⟩
  have hTB2l : (σ2.arrs "TB").length = P := by rw [hclen, hTBl]
  have hWl : W < (σ2.arrs "TB").length := by rw [hTB2l]; have := Nat.mul_le_mul_left (2 ^ wd) (show 1 ≤ 1 from le_rfl); 
                                              have h1 : W + 1 ≤ P := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _); omega
  have hINFB : infOf J < B := by have : infOf J < B0 := hmaxd; omega
  obtain ⟨σ3, hr3, hout3⟩ :=
    (finish_spec (B := B) (by omega) W (infOf J) ((σ2.arrs "TB").getD W 0) (σ2.arrs "TB") hWl
      (by omega)
      (lt_of_le_of_lt (hcle W) hINFB) hINFB).run ⟨hc3, hc1, rfl, rfl⟩
  have hout2 : σ2.out = [] := by
    rw [hr2.out_eq (by decide), hout]
  have hrall : Run B prog3 (initEnv (ext3 X) X) σ3
      ((2 * Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 1000 * I.jobs + 2000) +
        (Kcore J.jobs wd (W + 1) + 12)) := by
    unfold prog3
    exact hr1'.seq (hr2.seq hr3)
  refine ⟨σ3, hrall.mono ?_, ?_⟩
  · unfold cost3
    rw [hjc, hthr, hjj]
    have : widthOf X = wd := rfl
    rw [this]
    omega
  · rw [hout3, hout2]
    have hiff : (σ2.arrs "TB").getD W 0 < infOf J ↔ Yes X := by
      rw [hctab W le_rfl, hHW W]
      constructor
      · intro h; exact ⟨I, W, hdec, h⟩
      · rintro ⟨I', W', hdec', hh⟩
        obtain ⟨h1, h2⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique hdec' hdec
        subst h1; subst h2; exact hh
    by_cases h : Yes X
    · rw [if_pos h, if_pos (hiff.mpr h)]; rfl
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]; rfl

/-! ## The arithmetic -/

theorem cost_arith (n w1 p S sK : ℕ) (hS : n + 1 ≤ S) (hw1 : 1 ≤ w1) (hp : 1 ≤ p)
    (hsK : sK ≤ 390 * S) :
    10 * (((2 * sK + 1000 * n + 2000) + ((54 * n + 24 * w1 + 120) +
      ((108 * (p * w1) + 306) * (2 * n) + 6)) + 12)) + 1 ≤ 50000 * (w1 * p * (n + 1)) + 50000 * S := by
  have e1 : (108 * (p * w1) + 306) * (2 * n) = 216 * (p * w1 * n) + 612 * n := by ring
  have e2 : w1 * p * (n + 1) = p * w1 * n + p * w1 := by ring
  have hpw : 1 ≤ p * w1 := Nat.mul_le_mul hp hw1
  have h3 : w1 ≤ p * w1 := Nat.le_mul_of_pos_left _ hp
  have h4 : n ≤ p * w1 * n := Nat.le_mul_of_pos_left _ hpw
  rw [e1, e2]
  generalize p * w1 * n = R at *
  generalize p * w1 = Z at *
  omega

theorem tab_arith (κ c pw len M W1 p n : ℕ) (hc1 : 80 * κ ≤ c)
    (h1 : c * W1 * p * (n + 1) ≤ pw) (h2 : c * (len + M + 1) ≤ pw) :
    κ * (p * W1 + 8 * M + 40) ≤ pw := by
  have a1 : c * (p * W1) ≤ pw := by
    refine le_trans ?_ h1
    have : c * W1 * p * (n + 1) = c * (p * W1) * (n + 1) := by ring
    rw [this]; exact Nat.le_mul_of_pos_right _ (by omega)
  have a2 : 2 * κ * (p * W1) ≤ c * (p * W1) := Nat.mul_le_mul_right _ (by omega)
  have a3 : 80 * κ * (len + M + 1) ≤ c * (len + M + 1) := Nat.mul_le_mul_right _ hc1
  have a4 : κ * (8 * M + 40) * 2 ≤ 80 * κ * (len + M + 1) := by
    have : κ * (8 * M + 40) * 2 = κ * (16 * M + 80) := by ring
    rw [this]
    have : 80 * κ * (len + M + 1) = κ * (80 * len + 80 * M + 80) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (by omega)
  have e : κ * (p * W1 + 8 * M + 40) = κ * (p * W1) + κ * (8 * M + 40) := by ring
  rw [e]
  have b1 : 2 * (κ * (p * W1)) ≤ pw := by
    have : 2 * (κ * (p * W1)) = 2 * κ * (p * W1) := by ring
    omega
  omega

/-- The constant. -/
def cc3 : ℕ := 80 * Lax496464Proofs.Ram.Fits.const L3 + 50000

theorem cc3_ge : 80 * Lax496464Proofs.Ram.Fits.const L3 ≤ cc3 := by unfold cc3; omega

/-- Decision words of an instance with positive processing times that fit and whose sweep
table fits. -/
def Dom3 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧
    c * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j)}

open Classical in
theorem prog3_solves (cc w : ℕ) :
    Solves L3 prog3 (Dom3 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T3 x)) cost3 where
  ok := prog3_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxD, -, -, hqp⟩ := hx
    obtain ⟨σ', hr, hout⟩ := prog3_run hxD hqp
    exact ⟨ext3 x, σ', hr, hout⟩

theorem hne3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, Fits (Lax496464Proofs.Ram.Fits.const L3) w x := by
  rintro x ⟨-, hxFits, -, -⟩
  exact Lax496464Proofs.Ram.Corollary1Prog.fits_mono hxFits (by have := cc3_ge; omega)

theorem hTab3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, Lax496464Proofs.Ram.Fits.const L3 * T3 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne3 w x hx
  obtain ⟨-, hxFits, hpw, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  unfold T3
  have := tab_arith (Lax496464Proofs.Ram.Fits.const L3) cc3 (2 ^ w) x.length (maxEntry x)
    (threshold x + 1) (2 ^ widthOf x) (jobCount x) cc3_ge (by
      have : cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
        cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) := rfl
      calc cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1)
          = cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) := rfl
        _ ≤ 2 ^ w := hpw) hf
  have e : 2 ^ widthOf x * (threshold x + 1) = 2 ^ widthOf x * (threshold x + 1) := rfl
  rw [Nat.mul_comm (2 ^ widthOf x) (threshold x + 1)] at this ⊢
  exact this

theorem hT3 (w : ℕ) : ∀ x ∈ Dom3 cc3 w, Layout.const L3 * cost3 x + 1 ≤
    cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) + cc3 * sortCost x := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hnl : jobCount x ≤ x.length := by rw [hjc, hxlen]; omega
  have hsK := Lax496464Proofs.Ram.Sort.sortK_le 90 (jobCount x) x.length hnl
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  have hS : jobCount x + 1 ≤ sortCost x := by
    rw [hsc]
    calc jobCount x + 1 ≤ x.length + 1 := by omega
      _ ≤ (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
  have hc : Layout.const L3 = 10 := rfl
  have hcc : 50000 ≤ cc3 := by unfold cc3; omega
  have hp : 1 ≤ 2 ^ widthOf x := Nat.one_le_two_pow
  have key := cost_arith (jobCount x) (threshold x + 1) (2 ^ widthOf x) (sortCost x)
    (Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x)) hS (by omega) hp (by rw [← hsc] at hsK; omega)
  unfold cost3 Kcore
  rw [hc]
  have h1 := Nat.mul_le_mul_right ((threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1)) hcc
  have h2 := Nat.mul_le_mul_right (sortCost x) hcc
  have e : cc3 * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
      cc3 * ((threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1)) := by ring
  rw [e]
  have e2 : (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) =
      (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) := rfl
  omega

open Classical in
/--
---
conclusion: Lax496464.Theorem3.theorem3_width_time
---
The endpoint sweep of Section 4 as a word RAM program: read the word, sort the jobs by start
time (`O(n log n)`), build the arrays of the sorted instance and the order of the due dates, then
sweep the `2n` events — the start of a job takes a free slot (or a fresh one, doubling the mask
range `MK = 2^next`), the due date frees it — updating a table with one entry for every set of
occupied slots and every weight up to `W`, by a flat pass of `MK · (W+1)` cells per event. The
number of slots is at most the width `ω`, so every event costs `O(2^ω · (W+1))` and the run is
within `c · (W+1) · 2^ω · (n+1) + c · sortCost`. The domain restricts to positive processing
times, the paper's standing assumption for the sweep.
-/
theorem theorem3_width_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧
        c * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (threshold x + 1) * 2 ^ widthOf x * (jobCount x + 1) +
        c * sortCost x) :=
  ⟨compileProgram L3 prog3, cc3, fun w =>
    computesInTime_of_solves_fits (hne3 w) (hfits3 w) (hTab3 w) (prog3_solves cc3 w) (hT3 w)⟩

end Lax496464Proofs.Ram.W3Final
