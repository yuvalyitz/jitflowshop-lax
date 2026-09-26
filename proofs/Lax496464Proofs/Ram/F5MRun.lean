import Lax496464Proofs.Ram.F5MOk
import Lax496464Proofs.Ram.F5WFinal

/-!
# Theorem 5 (table of Section 3): `prog5m` runs

`prog5m_run`: on a word presenting an instance and an accuracy, with positive processing times,
`prog5m` writes `[fptasOut I e]` (`= f5 x`) below the value bound `bound x (T5m x)`, within
`cost5mX x`.
-/

namespace Lax496464Proofs.F5MRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QFinal
open Lax496464Proofs.F5MRest Lax496464Proofs.F5MOk
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)
open Lax496464Proofs.Ram.W3FrontX (sortSetup3_spec')

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext5m (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" ∨ a = "NX" then
    jobCount x
  else if a = "PW" then machineCount x + 1
  else if a = "VALID" then (jobCount x + 1) ^ machineCount x
  else if a = "TAB" then (jobCount x + 1) ^ machineCount x * (thrX x + 1)
  else 0

/-- Room for every intermediate value. -/
def T5m (x : List ℕ) : ℕ :=
  8 * maxEntry x + 4 * ((thrX x + 1) * (jobCount x + 1) ^ machineCount x) + 40 + sumwt x

/-- The cost bound. -/
noncomputable def cost5mX (x : List ℕ) : ℕ :=
  (2 * Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x) + 1000 * jobCount x + 2000) +
    cost5m (jobCount x) (machineCount x) (thrX x)

set_option maxHeartbeats 16000000 in
open Classical in
theorem prog5m_run {x : List ℕ} (hxA : x ∈ ApproxInstances)
    (hqp : ∀ j < jobCount x, 0 < procTime x j) :
    ∃ σ', Run (bound x (T5m x)) prog5m (initEnv (ext5m x) x) σ' (cost5mX x) ∧
      σ'.out = f5 x := by
  obtain ⟨I, e, hAppr⟩ := hxA
  have hf5 := f5_eq hAppr
  obtain ⟨y, hxy, he, hEnc⟩ := hAppr
  have hdec0 : EncodesDecisionInstance x I e := ⟨y, hxy, hEnc⟩
  subst hxy
  obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := e) hEnc
  have hthr : threshold (y ++ [e]) = e :=
    Lax496464Proofs.Ram.W3Final.threshold_eq' e hEnc
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
  set P : ℕ := (thr I e + 1) * (I.jobs + 1) ^ I.machines with hPdef
  set S : ℕ := sumwt X with hSdef
  have hBeq : bound X (T5m X) = X.length + M + 1 + (8 * M + 4 * P + 40 + S) := by
    show X.length + maxEntry X + 1 + (8 * maxEntry X + 4 * ((thrX X + 1) *
      (jobCount X + 1) ^ machineCount X) + 40 + sumwt X) = _
    rw [hthrX, hjc, hmc]
  rw [hBeq]
  set B : ℕ := X.length + M + 1 + (8 * M + 4 * P + 40 + S) with hBdef
  set B0 : ℕ := 4 * M + 10 with hB0def
  have hB0B : 2 * B0 + 10 ≤ B := by omega
  have hB0B' : B0 ≤ B := by omega
  have hxB : ∀ v ∈ X, v < B0 := fun v hv => by have := le_maxEntry hv; omega
  have hnB : 4 * I.jobs + 5 < B0 := by omega
  have hPpos : thr I e + 1 ≤ P := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hPB' : (I.jobs + 1) ^ I.machines * (thr I e + 1) = P := by rw [hPdef, Nat.mul_comm]
  -- the front end
  have hpre : (fun σ : Env => σ.inp = X ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs)
      (initEnv (ext5m X) X) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext5m, hjc]
  obtain ⟨σ1, hr1, ⟨J, ⟨f, hJf⟩, hEst, hJjobs, hJm, hJq, hJpq, hJdq, hJd2, hJdd, hJdq2, hJw, hHW,
      hPS, hQS, hDS, hWS, hperm, hlex, hn, hm, hsn, hW, hinp, hout, hlen⟩, hfv1, hfa1, -, -⟩ :=
    (sortSetup3_spec' (B := B0) hdec hqpos (by omega) hxB hnB
      (fun j => by have := hpB j; have := hqB j; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)
      (fun j => by have := hdB j; omega)
      (fun a b => by have := hdB a; have := hdB b; omega)
      (fun a b => by have := hdB a; have := hqB b; omega)).frame.run hpre
  have hr1' : Run B Lax496464Proofs.Ram.W3Front2.sortSetup3 (initEnv (ext5m X) X) σ1 _ :=
    Lax496464Proofs.Ram.W3BMono.Run.mono_bound hB0B' hr1
  have hjj : J.jobs = I.jobs := hJjobs
  have hwarr : ∀ a, a ∈ ["NX", "PW", "VALID", "TAB"] →
      a ∉ Lax496464Proofs.Ram.W3Front2.sortSetup3.warrs := by
    intro a ha h
    have := Lax496464Proofs.Ram.W3Front2.sortSetup3_warrs _ h
    simp at ha this
    rcases ha with rfl | rfl | rfl | rfl <;> simp at this
  have hNX1 : (σ1.arrs "NX").length = J.jobs := by
    rw [hfa1 "NX" (hwarr _ (by simp))]; simp [initEnv, ext5m, hjj, hjc]
  have hPW1 : (σ1.arrs "PW").length = J.machines + 1 := by
    rw [hfa1 "PW" (hwarr _ (by simp))]; simp [initEnv, ext5m, hJm, hmc]
  have hV1 : σ1.arrs "VALID" = List.replicate ((J.jobs + 1) ^ J.machines) 0 := by
    rw [hfa1 "VALID" (hwarr _ (by simp))]; simp [initEnv, ext5m, hjj, hjc, hJm, hmc]
  have hthrJ : thr J e = thr I e := by unfold thr; rw [hjj]
  have hT1 : σ1.arrs "TAB" = List.replicate ((J.jobs + 1) ^ J.machines * (thr J e + 1)) 0 := by
    rw [hfa1 "TAB" (hwarr _ (by simp))]
    simp [initEnv, ext5m, hjj, hjc, hJm, hmc, hthrX, hthrJ]
  have hPS' : σ1.arrs "PS" = PSl J := by rw [PSl, hjj]; exact hPS
  have hQS' : σ1.arrs "QS" = QSl J := by rw [QSl, hjj]; exact hQS
  have hDS' : σ1.arrs "DS" = DSl J := by rw [DSl, hjj]; exact hDS
  have hWS' : σ1.arrs "WS" = WSl J := by rw [WSl, hjj]; exact hWS
  -- the values of `J`
  have hfoe : fptasOut J e = fptasOut I e := by
    subst hJf
    exact Lax496464Proofs.F5QMath.fptasOut_permute I f e
  have hSw : fptasOut I e ≤ S := by
    rw [hSdef, sumwt_eq hEnc rfl]; exact fptasOut_le_total I he
  have hoB : fptasOut J e + 8 < B := by rw [hfoe]; omega
  have hPBJ : (J.jobs + 1) ^ J.machines * (thr J e + 1) + 8 < B := by
    rw [hjj, hJm, hthrJ, hPB']; omega
  obtain ⟨σ2, hr2, hout2⟩ :=
    (rest5m_spec (J := J) (e := e) (B := B) he hEst hJq (by omega) (by omega) (by omega)
      (fun j => by have := hJpq j; omega) (fun j => by have := hJd2 j; omega)
      (fun j => by have := hJw j; omega) (by rw [hthrJ]; omega) hPBJ
      (fun a b => by have := hJdq a b; omega) hoB).run
      ⟨by rw [hn, hjj], by rw [hsn, hjj], by rw [hm, hJm], hW, hPS', hQS', hDS', hWS',
        by rw [← hout], hNX1, hPW1, hV1, hT1⟩
  have hrall : Run B prog5m (initEnv (ext5m X) X) σ2
      ((2 * Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 1000 * I.jobs + 2000) +
        cost5m J.jobs J.machines (thr J e)) := by
    unfold prog5m
    exact hr1'.seq hr2
  refine ⟨σ2, hrall.mono ?_, ?_⟩
  · unfold cost5mX
    rw [hjc, hmc, hthrX, hjj, hJm, hthrJ]
  · rw [hout2, hfoe, hf5]

end Lax496464Proofs.F5MRun
