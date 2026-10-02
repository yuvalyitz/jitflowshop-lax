import Lax496464Proofs.Ram.F5MPre

/-!
# Theorem 5 (Table of Section 3): Everything After the Front End

`rest5m = pre5w ; if n < 1 then write 0 else if m < 1 then write 0 else core2 ; scanM ; outCom`.
Given the sorted arrays of `J` and the accuracy `e` in `W`, it writes `fptasOut J e`: the exact table
program (`D2Core.core2`, unchanged) is run on the rescaled weights with threshold `2 e n²`, and the
last non-zero cell of the column of the first `m` indices is `scaledOpt`.
-/

namespace Lax496464Proofs.F5MRest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.Fptas
open Lax496464.DynamicProgram (firstM)
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QRest Lax496464Proofs.F5WPre
open Lax496464Proofs.F5MPre
open Lax496464Proofs.Ram.F5QFit (V)
open Lax496464Proofs.Ram.F5QScan (outCom outCom_spec)
open Lax496464Proofs.Ram.F5MScan (scanM scanM_spec)
open Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Step Lax496464Proofs.Ram.D2Answer
open Lax496464Proofs.Ram.D2Digits
open Lax496464Proofs.Ram.D2Tab (rep_le)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The passes after the guard. -/
def mainM : Com := .seq core2 (.seq scanM outCom)

/-- The guard: no job, or no machine, writes `0`. -/
def guardM : Com :=
  .ite (.lt (V "n") (.lit 1)) (.write (.lit 0))
    (.ite (.lt (V "m") (.lit 1)) (.write (.lit 0)) mainM)

/-- Everything after the front end. -/
def rest5m : Com := .seq pre5w guardM

/-- The cost of `rest5m`. -/
noncomputable def cost5m (n m W : ℕ) : ℕ :=
  ((44 * n + 10) + 20 + (44 * n + 10) + 10) + 30 +
    (if 1 ≤ n ∧ 1 ≤ m then
      setupCost n m + (loopWork n m W ((n + 1) ^ m) + 4) + (34 * (W + 1) + 20) + 12 + 20
    else 10)

theorem kk_not_core2 : "kk" ∉ core2.wvars := by decide
theorem n_not_core2 : "n" ∉ core2.wvars := by decide

theorem pow_lt_of_le {n m i B P : ℕ} (hi : i ≤ m) (hP : (n + 1) ^ m * P + 8 < B) (hP1 : 1 ≤ P) :
    (n + 1) ^ i < B := by
  have h1 : (n + 1) ^ i ≤ (n + 1) ^ m := Nat.pow_le_pow_right (by omega) hi
  have h2 : (n + 1) ^ m ≤ (n + 1) ^ m * P := Nat.le_mul_of_pos_right _ hP1
  omega


set_option maxHeartbeats 8000000 in
open Classical in
/-- **`rest5m` is correct**: it writes `fptasOut J e`. -/
theorem rest5m_spec {J : Instance} {e B : ℕ} (he : 1 ≤ e)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j)
    (hnB : 2 * J.jobs + 8 < B) (hmB : J.machines + 8 < B) (heB : 2 * e + 8 < B)
    (hpqB : ∀ j : J.Job, (J.p j : ℕ) + J.q j + 8 < B) (hdB : ∀ j : J.Job, (J.d j : ℕ) + 8 < B)
    (hwB : ∀ j : J.Job, (J.w j : ℕ) + 8 < B) (hthrB : thr J e + 8 < B)
    (hPB : (J.jobs + 1) ^ J.machines * (thr J e + 1) + 8 < B)
    (hdq : ∀ a b : J.Job, (J.d a : ℕ) + J.q b + 8 < B)
    (hoB : fptasOut J e + 8 < B) :
    Spec B
      (fun σ => σ.vars "n" = J.jobs ∧ σ.vars "sn" = J.jobs ∧ σ.vars "m" = J.machines ∧
        σ.vars "W" = e ∧
        σ.arrs "PS" = PSl J ∧ σ.arrs "QS" = QSl J ∧ σ.arrs "DS" = DSl J ∧
        σ.arrs "WS" = WSl J ∧ σ.out = [] ∧
        (σ.arrs "NX").length = J.jobs ∧ (σ.arrs "PW").length = J.machines + 1 ∧
        σ.arrs "VALID" = List.replicate ((J.jobs + 1) ^ J.machines) 0 ∧
        σ.arrs "TAB" = List.replicate ((J.jobs + 1) ^ J.machines * (thr J e + 1)) 0)
      rest5m (fun _ σ' => σ'.out = [fptasOut J e]) (cost5m J.jobs J.machines (thr J e)) := by
  refine Spec.of_exists fun σ0 ⟨hn0, hsn0, hm0, hW0, hPS0, hQS0, hDS0, hWS0, hout0, hNX0, hPW0,
    hV0, hT0⟩ => ?_
  have hB1 : 1 < B := by omega
  -- 1. the passes before the core
  obtain ⟨σ4, hr4, ⟨hW4, hkk4, hWS4⟩, hfv4, hfa4, hfi4, hfo4⟩ :=
    (pre5w_spec (J := J) (e := e) (B := B) he hB1 (by omega) heB hpqB hdB hwB hthrB).frame.run
      (σ := σ0) ⟨hn0, hW0, hPS0, hQS0, hDS0, hWS0⟩
  have hn4 : σ4.vars "n" = J.jobs := by rw [hfv4 "n" (by decide)]; exact hn0
  have hsn4 : σ4.vars "sn" = J.jobs := by rw [hfv4 "sn" (by decide)]; exact hsn0
  have hm4 : σ4.vars "m" = J.machines := by rw [hfv4 "m" (by decide)]; exact hm0
  have hout4 : σ4.out = [] := by rw [hfo4 (by decide)]; exact hout0
  have hvn : (V "n").evalB B σ4 = some J.jobs :=
    hn4 ▸ evalB_var (by rw [hn4]; omega)
  have hvm : (V "m").evalB B σ4 = some J.machines :=
    hm4 ▸ evalB_var (by rw [hm4]; omega)
  have hcondN := evalB_condLt hvn (evalB_lit (show 1 < B by omega))
  have hcondM := evalB_condLt hvm (evalB_lit (show 1 < B by omega))
  by_cases hn0' : J.jobs < 1
  · have hc1 : (Cond.lt (V "n") (Expr.lit 1)).evalB B σ4 = some true := by
      rw [hcondN]; simp [hn0']
    have r2 := Run.write (B := B) (σ := σ4) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    refine ⟨{ σ4 with out := σ4.out ++ [0] }, _, (hr4.seq (Run.ite_true hc1 r2)).mono ?_,
      le_rfl, ?_⟩
    · unfold cost5m; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
    · show σ4.out ++ [0] = _
      rw [hout4, fptasOut_trivial J e (Or.inl (by omega))]; simp
  have hc1 : (Cond.lt (V "n") (Expr.lit 1)).evalB B σ4 = some false := by
    rw [hcondN]; simp [hn0']
  by_cases hm0' : J.machines < 1
  · have hc2 : (Cond.lt (V "m") (Expr.lit 1)).evalB B σ4 = some true := by
      rw [hcondM]; simp [hm0']
    have r2 := Run.write (B := B) (σ := σ4) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    refine ⟨{ σ4 with out := σ4.out ++ [0] }, _,
      (hr4.seq (Run.ite_false hc1 (Run.ite_true hc2 r2))).mono ?_, le_rfl, ?_⟩
    · unfold cost5m; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega
    · show σ4.out ++ [0] = _
      rw [hout4, fptasOut_trivial J e (Or.inr (by omega))]; simp
  have hc2 : (Cond.lt (V "m") (Expr.lit 1)).evalB B σ4 = some false := by
    rw [hcondM]; simp [hm0']
  -- the main case
  have hn1' : 1 ≤ J.jobs := by omega
  have hm1' : 1 ≤ J.machines := by omega
  have hW1pos : 1 ≤ thr J e + 1 := by omega
  have hPS4 : σ4.arrs "PS" = (List.range (scaled J e).jobs).map (pv (scaled J e)) := by
    rw [hfa4 "PS" (by decide), hPS0, PSl, pv_scaled]; rfl
  have hQS4 : σ4.arrs "QS" = (List.range (scaled J e).jobs).map (qv (scaled J e)) := by
    rw [hfa4 "QS" (by decide), hQS0, QSl, qv_scaled]; rfl
  have hDS4 : σ4.arrs "DS" = (List.range (scaled J e).jobs).map (dv (scaled J e)) := by
    rw [hfa4 "DS" (by decide), hDS0, DSl, dv_scaled]; rfl
  have hestS : EstOrdered (scaled J e) := hest
  have hCI : CI (scaled J e) B J.jobs J.machines (thr J e) := by
    refine ⟨by omega, rfl, rfl, hn1', hm1', hestS, hq, ?_, by omega, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have := pow_lt_of_le (n := J.jobs) hi hPB hW1pos
      exact this
    · intro k hk
      have hk' : k < J.jobs := hk
      have := hdB ⟨k, hk'⟩
      unfold Lax496464Proofs.Ram.Dp1.dv; rw [dif_pos (show k < (scaled J e).jobs from hk')]
      show (J.d ⟨k, hk'⟩ : ℕ) + 2 < B
      omega
    · intro k hk
      have hk' : k < J.jobs := hk
      have := hpqB ⟨k, hk'⟩
      unfold Lax496464Proofs.Ram.Dp1.pv Lax496464Proofs.Ram.Dp1.qv
      rw [dif_pos (show k < (scaled J e).jobs from hk'), dif_pos (show k < (scaled J e).jobs from hk')]
      show (J.p ⟨k, hk'⟩ : ℕ) + J.q ⟨k, hk'⟩ < B
      omega
    · intro a b ha hb
      have ha' : a < J.jobs := ha
      have hb' : b < J.jobs := hb
      have := hdq ⟨a, ha'⟩ ⟨b, hb'⟩
      unfold Lax496464Proofs.Ram.Dp1.dv Lax496464Proofs.Ram.Dp1.qv
      rw [dif_pos (show a < (scaled J e).jobs from ha'), dif_pos (show b < (scaled J e).jobs from hb')]
      show (J.d ⟨a, ha'⟩ : ℕ) + J.q ⟨b, hb'⟩ < B
      omega
    · intro k hk
      have hk' : k < J.jobs := hk
      have := scaled_w_lt he hthrB ⟨k, hk'⟩
      unfold Lax496464Proofs.Ram.DpMArr.wv; rw [dif_pos (show k < (scaled J e).jobs from hk')]
      exact lt_of_le_of_lt (Nat.le_add_right _ 8) this
  have hCPre : CPre (scaled J e) J.jobs J.machines (thr J e) σ4 := by
    refine ⟨hPS4, hQS4, hDS4, ?_, hn4, hm4, hsn4, hW4, ?_, ?_, ?_, ?_⟩
    · rw [hWS4]; rfl
    · rw [hfa4 "NX" (by decide)]; exact hNX0
    · rw [hfa4 "PW" (by decide)]; exact hPW0
    · rw [hfa4 "VALID" (by decide)]; exact hV0
    · rw [hfa4 "TAB" (by decide)]; exact hT0
  obtain ⟨σ5, hr5, ⟨inf, hi1, hinfB, hinf, hzk, hR5, hW5, hlenT, hcol⟩, hfv5, hfa5, hfi5, hfo5⟩ :=
    (core2_spec hCI).frame.run (σ := σ4) hCPre
  have hkk5 : σ5.vars "kk" = scaleK J e := by rw [hfv5 "kk" kk_not_core2]; exact hkk4
  have hn5 : σ5.vars "n" = J.jobs := by rw [hfv5 "n" n_not_core2]; exact hn4
  have hout5 : σ5.out = [] := by rw [hfo5 Lax496464Proofs.Ram.D2Final.core2_noWrite]; exact hout4
  set code := codeL J.jobs J.machines (List.range (min J.machines J.jobs)) with hcode
  have hcodeN : code < (J.jobs + 1) ^ J.machines :=
    (sl_range J.jobs J.machines).codeL_lt
  have hcm : code * (thr J e + 1) + (thr J e + 1) ≤ (J.jobs + 1) ^ J.machines * (thr J e + 1) := by
    have : (code + 1) * (thr J e + 1) ≤ (J.jobs + 1) ^ J.machines * (thr J e + 1) :=
      Nat.mul_le_mul_right _ hcodeN
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  -- 3. the scan
  have hTl : code * (thr J e + 1) + (thr J e + 1) ≤ (σ5.arrs "TAB").length := by
    rw [hlenT]; exact hcm
  have hTB : ∀ k < thr J e + 1, (σ5.arrs "TAB").getD (code * (thr J e + 1) + k) 0 < B := by
    intro k hk
    have := rep_le (hcol k (by omega))
    omega
  have hcmB : code * (thr J e + 1) + (thr J e + 1) < B := by omega
  have hNB : (J.jobs + 1) ^ J.machines < B := by
    have := Nat.le_mul_of_pos_right ((J.jobs + 1) ^ J.machines) hW1pos
    omega
  have hcB : code < B := by omega
  obtain ⟨σ6, hr6, ⟨hub, hatt, hn6, hkk6⟩, hfv6, hfa6, hfi6, hfo6⟩ :=
    (scanM_spec (B := B) (W1 := thr J e + 1) (code := code) (σ5.arrs "TAB") hB1 hcB
      (by omega) (by omega) hcmB hTl hTB).frame.run (σ := σ5) ⟨hzk, hR5, rfl⟩
  have hout6 : σ6.out = [] := by rw [hfo6 (by decide)]; exact hout5
  have hopt : scaledOpt J e < thr J e + 1 := by
    have := scaledOpt_le_thr J he
    omega
  have hfin : ∀ c < thr J e + 1,
      0 < (σ5.arrs "TAB").getD (code * (thr J e + 1) + c) 0 ↔ c ≤ scaledOpt J e := by
    intro c hc
    have hent := hcol c (by omega)
    have h1 := entry_ne_zero_iff hestS (by omega : 0 < inf) hent
    rw [← hasWeight_scaled J e c, ← h1]
    exact Nat.pos_iff_ne_zero
  have hbest : σ6.vars "best" = scaledOpt J e := best_eq_m hopt hfin hub hatt
  -- 4. the output
  have hwmB : wmaxFit J < B := by
    have := wmaxFit_le J (B := B - 1) (fun j _ => by have := hwB j; omega)
    omega
  have hkB : scaleK J e < B := by
    have : scaleK J e ≤ max 1 (wmaxFit J) := by
      unfold scaleK; exact max_le_max le_rfl (Nat.div_le_self _ _)
    have := max_lt (show 1 < B by omega) hwmB
    omega
  have hoB' : (scaleK J e) * (scaledOpt J e - J.jobs) < B := by
    by_cases hk : 1 < scaleK J e
    · have : fptasOut J e = scaleK J e * (scaledOpt J e - J.jobs) := by
        unfold fptasOut; rw [if_pos hk]
      omega
    · have hk1' : scaleK J e = 1 := by have := one_le_scaleK J e; omega
      rw [hk1']
      have := scaledOpt_le_thr J he
      omega
  obtain ⟨σ7, hr7, hout7⟩ :=
    (outCom_spec (B := B) (k := scaleK J e) (b := scaledOpt J e) (n := J.jobs) hB1 hkB
      (by have := scaledOpt_le_thr J he; omega) (by omega) hoB').run (σ := σ6)
      ⟨by rw [hkk6, hkk5], hbest, by rw [hn6]; exact hn5⟩
  refine ⟨σ7, _, (hr4.seq (Run.ite_false hc1 (Run.ite_false hc2 (hr5.seq (hr6.seq hr7))))).mono ?_,
    le_rfl, ?_⟩
  · unfold cost5m; rw [if_pos ⟨hn1', hm1'⟩]; simp only [Cond.size, Expr.size]; omega
  · rw [hout7, hout6]
    unfold fptasOut
    simp

end Lax496464Proofs.F5MRest
