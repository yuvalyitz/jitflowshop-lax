import Lax496464Proofs.Ram.F5WOk
import Lax496464Proofs.Ram.F5QFinal
import Lax496464Proofs.Ram.W3Final

/-!
# Theorem 5 (Endpoint Sweep): `prog5w` Runs

`prog5w_run`: on a word presenting an instance and an accuracy, with positive processing times,
`prog5w` writes `[fptasOut I e]` (`= f5 x`) below the value bound `bound x (T5w x)`, within
`cost5wX x`.
-/

namespace Lax496464Proofs.F5WRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QFinal
open Lax496464Proofs.F5WRest Lax496464Proofs.F5WOk
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464Proofs.Ram.W3Model (infOf maxd d_le_maxd)
open Lax496464Proofs.Ram.W3Width (widthJ_le_widthOf sa_eq)
open Lax496464Proofs.Ram.W3FrontX (sortSetup3_spec')
open Lax496464Proofs.Ram.W3Final (ext3 threshold_eq' maxd_lt)
open Lax496464Proofs.Ram.W3Sweep (Kcore)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext5w (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "FS" ∨
      a = "SLT" then jobCount x
  else if a = "TB" then 2 ^ widthOf x * (thrX x + 1)
  else if a = "PC" then 2 ^ widthOf x
  else if a = "P2" then widthOf x
  else 0

/-- Room for every intermediate value. -/
def T5w (x : List ℕ) : ℕ := 2 ^ widthOf x * (thrX x + 1) + 8 * maxEntry x + 40 + sumwt x

/-- The cost bound. -/
def cost5wX (x : List ℕ) : ℕ :=
  (2 * Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x) + 1000 * jobCount x + 2000) +
    cost5w (jobCount x) (widthOf x) (thrX x + 1)

set_option maxHeartbeats 16000000 in
open Classical in
theorem prog5w_run {x : List ℕ} (hxA : x ∈ ApproxInstances)
    (hqp : ∀ j < jobCount x, 0 < procTime x j) :
    ∃ σ', Run (bound x (T5w x)) prog5w (initEnv (ext5w x) x) σ' (cost5wX x) ∧
      σ'.out = f5 x := by
  obtain ⟨I, e, hAppr⟩ := hxA
  have hf5 := f5_eq hAppr
  obtain ⟨y, hxy, he, hEnc⟩ := hAppr
  have hdec0 : EncodesDecisionInstance x I e := ⟨y, hxy, hEnc⟩
  subst hxy
  obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := e) hEnc
  have hthr : threshold (y ++ [e]) = e := threshold_eq' e hEnc
  set X : List ℕ := y ++ [e] with hXdef
  have hdec : EncodesDecisionInstance X I e := ⟨y, rfl, hEnc⟩
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
  have heM : e ≤ M := le_maxEntry (by simp [hXdef])
  have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
    rw [← hqe j]; exact hqp j (by rw [hjc]; exact j.isLt)
  have hthrX : thrX X = thr I e := by unfold thrX thr; rw [hthr, hjc]
  -- the bounds
  set wd : ℕ := widthOf X with hwddef
  set P : ℕ := 2 ^ wd * (thr I e + 1) with hPdef
  set S : ℕ := sumwt X with hSdef
  have hBeq : bound X (T5w X) = X.length + M + 1 + (P + 8 * M + 40 + S) := by
    show X.length + maxEntry X + 1 + (2 ^ widthOf X * (thrX X + 1) + 8 * maxEntry X + 40 +
      sumwt X) = _
    rw [hthrX]
  rw [hBeq]
  set B : ℕ := X.length + M + 1 + (P + 8 * M + 40 + S) with hBdef
  set B0 : ℕ := 4 * M + 10 with hB0def
  have hB0B : 2 * B0 + 10 ≤ B := by omega
  have hB0B' : B0 ≤ B := by omega
  have hxB : ∀ v ∈ X, v < B0 := fun v hv => by have := le_maxEntry hv; omega
  have hnB : 4 * I.jobs + 5 < B0 := by omega
  have hPpos : thr I e + 1 ≤ P := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  -- the front end
  have hpre : (fun σ : Env => σ.inp = X ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs)
      (initEnv (ext5w X) X) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext5w, hjc]
  obtain ⟨σ1, hr1, ⟨J, ⟨f, hJf⟩, hEst, hJjobs, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW,
      hPS, hQS, hDS, hWS, hperm, hlex, hn, hm, hsn, hW, hinp, hout, hlen⟩, hfv1, hfa1, -, -⟩ :=
    (sortSetup3_spec' (B := B0) hdec hqpos (by omega) hxB hnB
      (fun j => by have := hpB j; have := hqB j; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)
      (fun j => by have := hdB j; omega)
      (fun a b => by have := hdB a; have := hdB b; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)).frame.run hpre
  have hr1' : Run B Lax496464Proofs.Ram.W3Front2.sortSetup3 (initEnv (ext5w X) X) σ1 _ :=
    Lax496464Proofs.Ram.W3BMono.Run.mono_bound hB0B' hr1
  have hwd : Lax496464Proofs.Ram.W3Model.widthJ J ≤ wd := by
    subst hJf
    exact widthJ_le_widthOf e hEnc f
  have hJd2' : ∀ j : J.Job, J.d j + 2 < B0 := hJd2
  have hmaxd : maxd J + 2 < B0 := maxd_lt hJd2' (by omega)
  have hlenA : ∀ a, (σ1.arrs a).length = ext5w X a := fun a => by
    rw [hlen a]; simp [initEnv]
  have hTBl : (σ1.arrs "TB").length = P := by
    rw [hlenA "TB"]; simp [ext5w, hthrX, hPdef, hwddef]
  have hPCl : (σ1.arrs "PC").length = 2 ^ wd := by
    rw [hlenA "PC"]; simp [ext5w, hwddef]
  have hFSl : (σ1.arrs "FS").length = I.jobs := by
    rw [hlenA "FS"]; simp [ext5w, hjc]
  have hSLTl : (σ1.arrs "SLT").length = I.jobs := by
    rw [hlenA "SLT"]; simp [ext5w, hjc]
  have hP2l : (σ1.arrs "P2").length = wd := by
    rw [hlenA "P2"]; simp [ext5w, hwddef]
  have hTB1 : σ1.arrs "TB" = List.replicate P 0 := by
    have : "TB" ∉ Lax496464Proofs.Ram.W3Front2.sortSetup3.warrs := fun h => by
      have := Lax496464Proofs.Ram.W3Front2.sortSetup3_warrs _ h
      simp at this
    rw [hfa1 "TB" this]
    simp [initEnv, ext5w, hthrX, hPdef, hwddef]
  have hjj : J.jobs = I.jobs := hJjobs
  have hPS' : σ1.arrs "PS" = PSl J := by rw [PSl, hjj]; exact hPS
  have hQS' : σ1.arrs "QS" = QSl J := by rw [QSl, hjj]; exact hQS
  have hDS' : σ1.arrs "DS" = DSl J := by rw [DSl, hjj]; exact hDS
  have hWS' : σ1.arrs "WS" = WSl J := by rw [WSl, hjj]; exact hWS
  have hSA' : σ1.arrs "SA" = (Lax496464Proofs.Ram.W3Model.dueOrder J).map Fin.val := by
    refine Lax496464Proofs.Ram.W3Width.sa_eq J _ ?_ ?_
    · rw [hjj]; exact hperm
    · exact hlex
  -- the values of `J`
  have hfoe : fptasOut J e = fptasOut I e := by
    subst hJf
    exact Lax496464Proofs.F5QMath.fptasOut_permute I f e
  have hthrJ : thr J e = thr I e := by unfold thr; rw [hjj]
  have hSw : fptasOut I e ≤ S := by
    rw [hSdef, sumwt_eq hEnc rfl]; exact fptasOut_le_total I he
  have hoB : fptasOut J e + 8 < B := by rw [hfoe]; omega
  obtain ⟨σ2, hr2, hout2⟩ :=
    (rest5w_spec (J := J) (e := e) (B := B) (wd := wd) (LTB := P) (LPC := 2 ^ wd) (LFS := I.jobs)
      (LSLT := I.jobs) (LP2 := wd) he hEst hJq hwd (by omega) (by omega) (by omega) (by omega)
      (fun j => by have := hJpq j; omega) (fun j => by have := hJd2 j; omega)
      (fun j => by have := hJw j; omega) (by rw [hthrJ]; omega) (by rw [hthrJ]; omega)
      (by unfold Lax496464Proofs.Ram.W3Model.infOf; omega)
      (fun j => by have := hJpq j; unfold Lax496464Proofs.Ram.W3Model.infOf; omega)
      (fun a b => by have := hJdq a b; omega) hoB (by rw [hthrJ]) (by omega) (by omega)
      (by omega) le_rfl).run
      ⟨by rw [hn, hjj], by rw [hsn, hjj], by rw [hm, hJm], hW, hPS', hQS', hDS', hWS', hSA',
        by rw [← hout], hTBl, hPCl, hFSl, hSLTl, hP2l,
        by rw [hTB1]; intro j; simp⟩
  have hrall : Run B prog5w (initEnv (ext5w X) X) σ2
      ((2 * Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 1000 * I.jobs + 2000) +
        cost5w J.jobs wd (thr J e + 1)) := by
    unfold prog5w
    exact hr1'.seq hr2
  refine ⟨σ2, hrall.mono ?_, ?_⟩
  · unfold cost5wX
    rw [hjc, hthrX, hjj, hthrJ]
  · rw [hout2, hfoe, hf5]

end Lax496464Proofs.F5WRun
