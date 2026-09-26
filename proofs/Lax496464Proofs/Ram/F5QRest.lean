import Lax496464Proofs.Ram.F5QLift
import Lax496464Proofs.Ram.Q3Core

/-!
# Theorem 5 (profile sweep): everything after the front end

`rest5` takes the sorted arrays of an instance `J` and the accuracy `e` (in the scalar `W`) and
writes `fptasOut J e`: fit pass, scale factor, rescaling, threshold `W := 2 e n²`, the exact core
(`Q3Core.coreCom`, unchanged) on the rescaled weights, the scan for the largest reachable
column, and the output.
-/

namespace Lax496464Proofs.F5QRest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift
open Lax496464Proofs.Ram.F5QFit (fitCom fitCom_spec fitArr fitVal)
open Lax496464Proofs.Ram.F5QScale (kCom kCom_spec wCom wCom_spec rescaleCom rescaleCom_spec)
open Lax496464Proofs.Ram.F5QScan (scanCom scanCom_spec outCom outCom_spec)
open Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Loop Lax496464Proofs.Ram.Q3Core
open Lax496464Proofs.Ram.Q3Aux
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- **Everything after the front end.** -/
def rest5 : Com :=
  .seq fitCom (.seq kCom (.seq rescaleCom (.seq wCom (.seq coreCom (.seq scanCom outCom)))))

/-- The cost of `rest5`. -/
def cost5r (n N qm bt bb : ℕ) : ℕ :=
  (44 * n + 10) + 20 + (44 * n + 10) + 10 + coreK N qm n bt bb + (64 * N + 10) + 12

theorem two_e_n_le_thr (J : Instance) (e : ℕ) (hn : 1 ≤ J.jobs) : 2 * e * J.jobs ≤ thr J e := by
  unfold thr
  exact Nat.le_mul_of_pos_right _ hn

theorem scaled_w_lt {J : Instance} {e B : ℕ} (he : 1 ≤ e) (hthrB : thr J e + 8 < B)
    (j : Fin J.jobs) : (scaled J e).w j + 8 < B := by
  have h1 := scaled_w_le J he j
  have h2 := two_e_n_le_thr J e (by have := j.isLt; omega)
  omega

theorem en_le_thr (J : Instance) (e : ℕ) : e * J.jobs ≤ thr J e := by
  unfold thr
  rcases Nat.eq_zero_or_pos J.jobs with h | h
  · rw [h]; simp
  · have h1 : e * J.jobs ≤ e * J.jobs * J.jobs := Nat.le_mul_of_pos_right _ h
    have h2 : e * J.jobs * J.jobs ≤ 2 * e * J.jobs * J.jobs := by
      have : e * J.jobs * J.jobs * 1 ≤ e * J.jobs * J.jobs * 2 := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    omega

theorem pv_scaled (J : Instance) (e : ℕ) : pv (scaled J e) = pv J := by funext j; rfl
theorem qv_scaled (J : Instance) (e : ℕ) : qv (scaled J e) = qv J := by funext j; rfl
theorem dv_scaled (J : Instance) (e : ℕ) : dv (scaled J e) = dv J := by funext j; rfl

theorem fitVal_le (J : Instance) (k : ℕ) (hk : k < J.jobs) :
    fitVal (PSl J) (QSl J) (DSl J) (WSl J) k ≤ J.w ⟨k, hk⟩ := by
  rw [fitVal_eq J k hk]
  show (if Fit J ⟨k, hk⟩ then J.w ⟨k, hk⟩ else 0) ≤ _
  split_ifs <;> omega

set_option maxHeartbeats 8000000 in
open Classical in
/-- **`rest5` is correct**: it writes `fptasOut J e`. -/
theorem rest5_spec {J : Instance} {e qm INF bb bt w1 N B : ℕ} (he : 1 ≤ e)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j)
    (hqmd : qm = ((List.range J.jobs).map (qv J)).foldr max 0)
    (hINFd : INF = ((List.range J.jobs).map (dv J)).foldr max 0 + 1)
    (hbb : bb = J.machines + 1) (hbt : bt = bb ^ qm) (hw1 : w1 = thr J e + 1) (hN : N = bt * w1)
    (hB20 : 20 < B) (hnB : J.jobs + 8 < B) (hmB : J.machines + 8 < B) (heB : 2 * e + 8 < B)
    (hpqB : ∀ j : J.Job, (J.p j : ℕ) + J.q j + 8 < B) (hdB : ∀ j : J.Job, (J.d j : ℕ) + 8 < B)
    (hwB : ∀ j : J.Job, (J.w j : ℕ) + 8 < B) (hthrB : thr J e + 8 < B)
    (hqmB : qm + 8 < B) (hbtB : bt + 8 < B) (hNB : N + 8 < B) (hINF8 : INF + 8 < B)
    (hINFpq : ∀ j : J.Job, INF + (J.p j : ℕ) + J.q j + 8 < B)
    (hoB : fptasOut J e + 8 < B) :
    Spec B
      (fun σ => σ.vars "n" = J.jobs ∧ σ.vars "m" = J.machines ∧ σ.vars "W" = e ∧
        σ.arrs "PS" = PSl J ∧ σ.arrs "QS" = QSl J ∧ σ.arrs "DS" = DSl J ∧
        σ.arrs "WS" = WSl J ∧ σ.out = [] ∧ (σ.arrs "T").length = N ∧ (σ.arrs "S").length = N ∧
        σ.arrs "G" = List.replicate bt 0)
      rest5 (fun _ σ' => σ'.out = [fptasOut J e]) (cost5r J.jobs N qm bt bb) := by
  refine Spec.of_exists fun σ0 ⟨hn0, hm0, hW0, hPS0, hQS0, hDS0, hWS0, hout0, hT0, hS0, hG0⟩ => ?_
  have hB1 : 1 < B := by omega
  -- 1. the fit pass
  have hWl : ∀ k < J.jobs, (WSl J).getD k 0 < B := fun k hk => by
    rw [WSl_getD J k hk]; have := hwB ⟨k, hk⟩; omega
  have hPQ : ∀ k < J.jobs, (PSl J).getD k 0 + (QSl J).getD k 0 < B := fun k hk => by
    rw [PSl_getD J k hk, QSl_getD J k hk]; have := hpqB ⟨k, hk⟩; omega
  have hDl : ∀ k < J.jobs, (DSl J).getD k 0 < B := fun k hk => by
    rw [DSl_getD J k hk]; have := hdB ⟨k, hk⟩; omega
  obtain ⟨σ1, hr1, ⟨hWS1, hwm1⟩, hfv1, hfa1, hfi1, hfo1⟩ :=
    (fitCom_spec (B := B) (n := J.jobs) (PSl J) (QSl J) (DSl J) (WSl J) hB1 (PSl_length J)
      (QSl_length J) (DSl_length J) (WSl_length J) (by omega) hPQ hWl hDl).frame.run (σ := σ0)
      ⟨hn0, hPS0, hQS0, hDS0, hWS0⟩
  have hn1 : σ1.vars "n" = J.jobs := by rw [hfv1 "n" (by decide)]; exact hn0
  have hm1 : σ1.vars "m" = J.machines := by rw [hfv1 "m" (by decide)]; exact hm0
  have hW1 : σ1.vars "W" = e := by rw [hfv1 "W" (by decide)]; exact hW0
  have hPS1 : σ1.arrs "PS" = PSl J := by rw [hfa1 "PS" (by decide)]; exact hPS0
  have hQS1 : σ1.arrs "QS" = QSl J := by rw [hfa1 "QS" (by decide)]; exact hQS0
  have hDS1 : σ1.arrs "DS" = DSl J := by rw [hfa1 "DS" (by decide)]; exact hDS0
  have hout1 : σ1.out = [] := by rw [hfo1 (by decide)]; exact hout0
  have hT1 : (σ1.arrs "T").length = N := by rw [hfa1 "T" (by decide)]; exact hT0
  have hS1 : (σ1.arrs "S").length = N := by rw [hfa1 "S" (by decide)]; exact hS0
  have hG1 : σ1.arrs "G" = List.replicate bt 0 := by rw [hfa1 "G" (by decide)]; exact hG0
  -- 2. the scale factor
  have hen : e * J.jobs < B := by have := en_le_thr J e; omega
  have hwmB : wmaxFit J < B := by
    have := wmaxFit_le J (B := B - 1) (fun j _ => by have := hwB j; omega)
    omega
  obtain ⟨σ2, hr2, hkk2, hfv2, hfa2, hfi2, hfo2⟩ :=
    (kCom_spec (B := B) (e := e) (n := J.jobs) (wmv := wmaxFit J) hB1 (by omega) (by omega) hen
      hwmB).frame.run (σ := σ1) ⟨hW1, hn1, by rw [hwm1, wm_eq]⟩
  have hkk2' : σ2.vars "kk" = scaleK J e := hkk2
  have hk1 : 1 ≤ scaleK J e := one_le_scaleK J e
  have hkB : scaleK J e < B := by
    have : scaleK J e ≤ max 1 (wmaxFit J) := by
      unfold scaleK; exact max_le_max le_rfl (Nat.div_le_self _ _)
    have := max_lt (show 1 < B by omega) hwmB
    omega
  have hn2 : σ2.vars "n" = J.jobs := by rw [hfv2 "n" (by decide)]; exact hn1
  have hm2 : σ2.vars "m" = J.machines := by rw [hfv2 "m" (by decide)]; exact hm1
  have hW2 : σ2.vars "W" = e := by rw [hfv2 "W" (by decide)]; exact hW1
  have hPS2 : σ2.arrs "PS" = PSl J := by rw [hfa2 "PS" (by decide)]; exact hPS1
  have hQS2 : σ2.arrs "QS" = QSl J := by rw [hfa2 "QS" (by decide)]; exact hQS1
  have hDS2 : σ2.arrs "DS" = DSl J := by rw [hfa2 "DS" (by decide)]; exact hDS1
  have hWS2 : σ2.arrs "WS" = fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs := by
    rw [hfa2 "WS" (by decide)]; exact hWS1
  have hout2 : σ2.out = [] := by rw [hfo2 (by decide)]; exact hout1
  have hT2 : (σ2.arrs "T").length = N := by rw [hfa2 "T" (by decide)]; exact hT1
  have hS2 : (σ2.arrs "S").length = N := by rw [hfa2 "S" (by decide)]; exact hS1
  have hG2 : σ2.arrs "G" = List.replicate bt 0 := by rw [hfa2 "G" (by decide)]; exact hG1
  -- 3. the rescaling pass
  have hFl : (fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs).length = J.jobs := by simp [fitArr]
  have hFB : ∀ k < J.jobs, (fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs).getD k 0 < B := by
    intro k hk
    unfold fitArr
    rw [getD_map_range' _ _ _ hk]
    have := fitVal_le J k hk
    have := hwB ⟨k, hk⟩
    omega
  obtain ⟨σ3, hr3, hWS3, hfv3, hfa3, hfi3, hfo3⟩ :=
    (rescaleCom_spec (B := B) (n := J.jobs) (kk := scaleK J e)
      (fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs) hB1 hk1 hFl (by omega) hkB hFB).frame.run
      (σ := σ2) ⟨hn2, hkk2', hWS2⟩
  rw [rescArr_eq] at hWS3
  have hn3 : σ3.vars "n" = J.jobs := by rw [hfv3 "n" (by decide)]; exact hn2
  have hm3 : σ3.vars "m" = J.machines := by rw [hfv3 "m" (by decide)]; exact hm2
  have hW3 : σ3.vars "W" = e := by rw [hfv3 "W" (by decide)]; exact hW2
  have hkk3 : σ3.vars "kk" = scaleK J e := by rw [hfv3 "kk" (by decide)]; exact hkk2'
  have hPS3 : σ3.arrs "PS" = PSl J := by rw [hfa3 "PS" (by decide)]; exact hPS2
  have hQS3 : σ3.arrs "QS" = QSl J := by rw [hfa3 "QS" (by decide)]; exact hQS2
  have hDS3 : σ3.arrs "DS" = DSl J := by rw [hfa3 "DS" (by decide)]; exact hDS2
  have hout3 : σ3.out = [] := by rw [hfo3 (by decide)]; exact hout2
  have hT3 : (σ3.arrs "T").length = N := by rw [hfa3 "T" (by decide)]; exact hT2
  have hS3 : (σ3.arrs "S").length = N := by rw [hfa3 "S" (by decide)]; exact hS2
  have hG3 : σ3.arrs "G" = List.replicate bt 0 := by rw [hfa3 "G" (by decide)]; exact hG2
  -- 4. the threshold
  have hn2B : 2 * e * J.jobs < B := by
    rcases Nat.eq_zero_or_pos J.jobs with h | h
    · rw [h]; omega
    · have := two_e_n_le_thr J e h; omega
  have hthrB' : 2 * e * J.jobs * J.jobs < B := by unfold thr at hthrB; omega
  obtain ⟨σ4, hr4, hW4, hfv4, hfa4, hfi4, hfo4⟩ :=
    (wCom_spec (B := B) (e := e) (n := J.jobs) hB1 (by omega) (by omega) (by omega) (by omega)
      hn2B hthrB').frame.run (σ := σ3) ⟨hW3, hn3⟩
  have hn4 : σ4.vars "n" = J.jobs := hW4.2
  have hW4' : σ4.vars "W" = thr J e := hW4.1
  have hm4 : σ4.vars "m" = J.machines := by rw [hfv4 "m" (by decide)]; exact hm3
  have hkk4 : σ4.vars "kk" = scaleK J e := by rw [hfv4 "kk" (by decide)]; exact hkk3
  have hPS4 : σ4.arrs "PS" = PSl J := by rw [hfa4 "PS" (by decide)]; exact hPS3
  have hQS4 : σ4.arrs "QS" = QSl J := by rw [hfa4 "QS" (by decide)]; exact hQS3
  have hDS4 : σ4.arrs "DS" = DSl J := by rw [hfa4 "DS" (by decide)]; exact hDS3
  have hWS4 : σ4.arrs "WS" = (List.range J.jobs).map (wv (scaled J e)) := by
    rw [hfa4 "WS" (by decide)]; exact hWS3
  have hout4 : σ4.out = [] := by rw [hfo4 (by decide)]; exact hout3
  have hT4 : (σ4.arrs "T").length = N := by rw [hfa4 "T" (by decide)]; exact hT3
  have hS4 : (σ4.arrs "S").length = N := by rw [hfa4 "S" (by decide)]; exact hS3
  have hG4 : σ4.arrs "G" = List.replicate bt 0 := by rw [hfa4 "G" (by decide)]; exact hG3
  -- 5. the exact core, on the rescaled instance
  have hd : Dims (scaled J e) (thr J e) qm bb bt w1 N := ⟨hbb, hbt, hw1, hN⟩
  have hBd : Bds (scaled J e) (thr J e) qm INF bt N B :=
    ⟨hB1, hnB, hmB, hthrB, hqmB, hbtB, hNB, hINF8, fun j => hINFpq j,
      fun j => scaled_w_lt he hthrB j⟩
  have hBase : Base (scaled J e) (thr J e) σ4 := by
    refine ⟨hn4, hm4, hW4', ?_, ?_, ?_, hWS4, hout4⟩
    · rw [hPS4, PSl, pv_scaled]; rfl
    · rw [hQS4, QSl, qv_scaled]; rfl
    · rw [hDS4, DSl, dv_scaled]; rfl
  have hINF0 : 0 < INF := by omega
  obtain ⟨σ5, hr5, hcore, hfv5, hfa5, hfi5, hfo5⟩ :=
    (coreCom_spec (J := scaled J e) hd hqmd hINFd hest hq hBd).frame.run (σ := σ4)
      ⟨hBase, hT4, hS4, hG4⟩
  have hkk5 : σ5.vars "kk" = scaleK J e := by rw [hfv5 "kk" (by decide)]; exact hkk4
  -- 6. the scan
  have hw1pos : 0 < w1 := by omega
  have hTB : ∀ k < N, (σ5.arrs "T").getD k 0 < B := by
    intro k hk
    have := getD_le_of_cells (bt := bt) (w1 := w1) (INF := INF) (T := σ5.arrs "T") hw1pos
      (by rw [hcore.Tl, hN]) (fun x hx c hc => (hcore.T x hx c hc).1) k
    omega
  obtain ⟨σ6, hr6, ⟨hub, hatt, hn6, hkk6⟩, hfv6, hfa6, hfi6, hfo6⟩ :=
    (scanCom_spec (B := B) (N := N) (w1 := w1) (INF := INF) (σ5.arrs "T") hB1 hw1pos (by omega)
      (by omega) (by rw [hcore.Tl]) hTB (by omega)).frame.run (σ := σ5)
      ⟨hcore.ctx.N, hcore.ctx.w1, hcore.ctx.cinf, rfl⟩
  have hout5 : σ5.out = [] := hcore.ctx.out
  have hout6 : σ6.out = [] := by rw [hfo6 (by decide)]; exact hout5
  -- the table means what it says
  have hopt : scaledOpt J e < w1 := by
    have := scaledOpt_le_thr J he
    omega
  have hfin : ∀ c < w1, (∃ x < bt, cell w1 (σ5.arrs "T") x c < INF) ↔ c ≤ scaledOpt J e := by
    intro c hc
    rw [tab_col hINF0 hcore.T hc]
    have hfin := Lax496464Proofs.Ram.Q3Model.Rsem_final (scaled J e) hq (q_le_qm _ hqmd) hINF0
      (d_lt_INF _ hINFd) c
    have hbt' : ((scaled J e).machines + 1) ^ qm = bt := by rw [hbt, hbb]; rfl
    have hbb' : (scaled J e).machines + 1 = bb := by rw [hbb]; rfl
    rw [hbt', hbb'] at hfin
    rw [← hfin, hasWeight_scaled]
  have hbest : σ6.vars "best" = scaledOpt J e :=
    best_eq hw1pos hN hopt hfin hub hatt
  -- 7. the output
  have hoB' : (scaleK J e) * (scaledOpt J e - J.jobs) < B := by
    by_cases hk : 1 < scaleK J e
    · have : fptasOut J e = scaleK J e * (scaledOpt J e - J.jobs) := by
        unfold fptasOut; rw [if_pos hk]
      omega
    · have hk1' : scaleK J e = 1 := by omega
      rw [hk1']
      have := scaledOpt_le_thr J he
      omega
  obtain ⟨σ7, hr7, hout7⟩ :=
    (outCom_spec (B := B) (k := scaleK J e) (b := scaledOpt J e) (n := J.jobs) hB1 hkB
      (by omega) (by omega) hoB').run (σ := σ6) ⟨by rw [hkk6, hkk5], hbest, by rw [hn6]; exact hcore.ctx.n⟩
  refine ⟨σ7, _, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq hr7)))))).mono ?_, le_rfl, ?_⟩
  · have hj : coreK N qm (scaled J e).jobs bt bb = coreK N qm J.jobs bt bb := rfl
    exact le_of_eq (by unfold cost5r; rw [hj]; ring)
  · rw [hout7, hout6]
    unfold fptasOut
    simp

end Lax496464Proofs.F5QRest
