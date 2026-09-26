import Lax496464Proofs.Ram.F5WPre
import Lax496464Proofs.Ram.W3Width
import Lax496464Proofs.Ram.W3Final

/-!
# Theorem 5 (endpoint sweep): everything after the front end

`rest5w = pre5w ; core ; scanW ; outCom`.  Given the sorted arrays of `J`, the accuracy `e` in `W`
and the auxiliary arrays of the sweep, it writes `fptasOut J e`: the exact endpoint-sweep core
(`W3Sweep.core`, unchanged) is run on the rescaled weights with threshold `2 e n²`, and the last
finite cell of the row `TB[0 … W]` is `scaledOpt`.
-/

namespace Lax496464Proofs.F5WRest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QRest Lax496464Proofs.F5WPre
open Lax496464Proofs.Ram.F5QScan (outCom outCom_spec)
open Lax496464Proofs.Ram.F5WScan (scanW scanW_spec)
open Lax496464Proofs.Ram.W3Model (infOf maxd d_le_maxd dueOrder widthJ)
open Lax496464Proofs.Ram.W3Sweep (core core_spec Kcore core_warrs core_wvars_n)
open Lax496464Proofs.Ram.W3SweepEv (Nums)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- Everything after the front end. -/
def rest5w : Com := .seq pre5w (.seq core (.seq scanW outCom))

/-- The cost of `rest5w`. -/
def cost5w (n wd W1 : ℕ) : ℕ :=
  ((44 * n + 10) + 20 + (44 * n + 10) + 10) + Kcore n wd W1 + (34 * W1 + 10) + 12

theorem best_eq_w {W1 INF opt best : ℕ} {T : List ℕ} (hopt : opt < W1)
    (hfin : ∀ c < W1, T.getD c 0 < INF ↔ c ≤ opt)
    (hub : ∀ idx < W1, T.getD idx 0 < INF → idx ≤ best)
    (hatt : best = 0 ∨ (best < W1 ∧ T.getD best 0 < INF)) : best = opt := by
  apply le_antisymm
  · rcases hatt with h | ⟨h1, h2⟩
    · omega
    · exact (hfin best h1).mp h2
  · exact hub opt hopt ((hfin opt hopt).mpr le_rfl)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **`rest5w` is correct**: it writes `fptasOut J e`. -/
theorem rest5w_spec {J : Instance} {e B wd LTB LPC LFS LSLT LP2 : ℕ} (he : 1 ≤ e)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hwd : widthJ J ≤ wd)
    (hB20 : 20 < B) (hnB : 2 * J.jobs + 8 < B) (hmB : J.machines + 8 < B) (heB : 2 * e + 8 < B)
    (hpqB : ∀ j : J.Job, (J.p j : ℕ) + J.q j + 8 < B) (hdB : ∀ j : J.Job, (J.d j : ℕ) + 8 < B)
    (hwB : ∀ j : J.Job, (J.w j : ℕ) + 8 < B) (hthrB : thr J e + 8 < B)
    (htbB : 2 ^ wd * (thr J e + 1) + 8 < B) (hINF8 : infOf J + 8 < B)
    (hINFpq : ∀ j : J.Job, infOf J + (J.p j : ℕ) + J.q j + 8 < B)
    (hdq : ∀ a b : J.Job, (J.d a : ℕ) + J.q b + 8 < B)
    (hoB : fptasOut J e + 8 < B)
    (tbL : 2 ^ wd * (thr J e + 1) ≤ LTB) (pcL : 2 ^ wd ≤ LPC) (fsL : J.jobs ≤ LFS)
    (sltL : J.jobs ≤ LSLT) (p2L : wd ≤ LP2) :
    Spec B
      (fun σ => σ.vars "n" = J.jobs ∧ σ.vars "sn" = J.jobs ∧ σ.vars "m" = J.machines ∧
        σ.vars "W" = e ∧
        σ.arrs "PS" = PSl J ∧ σ.arrs "QS" = QSl J ∧ σ.arrs "DS" = DSl J ∧
        σ.arrs "WS" = WSl J ∧ σ.arrs "SA" = (dueOrder J).map Fin.val ∧ σ.out = [] ∧
        (σ.arrs "TB").length = LTB ∧ (σ.arrs "PC").length = LPC ∧ (σ.arrs "FS").length = LFS ∧
        (σ.arrs "SLT").length = LSLT ∧ (σ.arrs "P2").length = LP2 ∧
        ∀ j, (σ.arrs "TB").getD j 0 ≤ infOf J)
      rest5w (fun _ σ' => σ'.out = [fptasOut J e]) (cost5w J.jobs wd (thr J e + 1)) := by
  refine Spec.of_exists fun σ0 ⟨hn0, hsn0, hm0, hW0, hPS0, hQS0, hDS0, hWS0, hSA0, hout0, hltb0,
    hlpc0, hlfs0, hlslt0, hlp20, hTBle0⟩ => ?_
  have hB1 : 1 < B := by omega
  -- 1. the passes before the core
  obtain ⟨σ4, hr4, ⟨hW4, hkk4, hWS4⟩, hfv4, hfa4, hfi4, hfo4⟩ :=
    (pre5w_spec (J := J) (e := e) (B := B) he hB1 (by omega) heB hpqB hdB hwB hthrB).frame.run
      (σ := σ0) ⟨hn0, hW0, hPS0, hQS0, hDS0, hWS0⟩
  have hn4 : σ4.vars "n" = J.jobs := by rw [hfv4 "n" (by decide)]; exact hn0
  have hsn4 : σ4.vars "sn" = J.jobs := by rw [hfv4 "sn" (by decide)]; exact hsn0
  have hm4 : σ4.vars "m" = J.machines := by rw [hfv4 "m" (by decide)]; exact hm0
  have hPS4 : σ4.arrs "PS" = (List.range (scaled J e).jobs).map (pv (scaled J e)) := by
    rw [hfa4 "PS" (by decide), hPS0, PSl, pv_scaled]; rfl
  have hQS4 : σ4.arrs "QS" = (List.range (scaled J e).jobs).map (qv (scaled J e)) := by
    rw [hfa4 "QS" (by decide), hQS0, QSl, qv_scaled]; rfl
  have hDS4 : σ4.arrs "DS" = (List.range (scaled J e).jobs).map (dv (scaled J e)) := by
    rw [hfa4 "DS" (by decide), hDS0, DSl, dv_scaled]; rfl
  have hSA4 : σ4.arrs "SA" = (dueOrder (scaled J e)).map Fin.val := by
    rw [hfa4 "SA" (by decide)]; exact hSA0
  have hout4 : σ4.out = [] := by rw [hfo4 (by decide)]; exact hout0
  have hltb4 : (σ4.arrs "TB").length = LTB := by rw [hfa4 "TB" (by decide)]; exact hltb0
  have hlpc4 : (σ4.arrs "PC").length = LPC := by rw [hfa4 "PC" (by decide)]; exact hlpc0
  have hlfs4 : (σ4.arrs "FS").length = LFS := by rw [hfa4 "FS" (by decide)]; exact hlfs0
  have hlslt4 : (σ4.arrs "SLT").length = LSLT := by rw [hfa4 "SLT" (by decide)]; exact hlslt0
  have hlp24 : (σ4.arrs "P2").length = LP2 := by rw [hfa4 "P2" (by decide)]; exact hlp20
  have hTBle4 : ∀ j, (σ4.arrs "TB").getD j 0 ≤ infOf (scaled J e) := by
    intro j; rw [hfa4 "TB" (by decide)]; exact hTBle0 j
  -- 2. the exact core, on the rescaled instance
  have hW1pos : 0 < thr J e + 1 := by omega
  have hN : Nums (scaled J e) wd (thr J e + 1) (infOf J) B LTB LPC LFS LSLT LP2 := by
    refine ⟨hB1, hW1pos, tbL, pcL, fsL, sltL, p2L, by omega, by omega, by
      show 2 * J.jobs + 5 < B; omega, by
      show J.machines < B; omega, fun j => ?_, fun j => ?_, fun j => ?_, fun a b => ?_,
      fun j => ?_, by show 0 < maxd J + 2; omega⟩
    · have := hINFpq j; show infOf J + (J.p j : ℕ) + J.q j < B; omega
    · have := hdB j; show (J.d j : ℕ) + 1 < B; omega
    · have := scaled_w_lt he hthrB j; omega
    · have := hdq a b; show (J.d a : ℕ) + J.q b < B; omega
    · have := d_le_maxd (J := J) j; show J.d j ≤ maxd J + 2; omega
  have hWB : thr J e + 2 < B := by omega
  obtain ⟨σ5, hr5, ⟨hc1, hc2, hc3, hc4, hc5, hc6, hctab, hcle, hclen, hcfr⟩, hfv5, hfa5, hfi5,
      hfo5⟩ :=
    (core_spec (B := B) (J := scaled J e) (wd := wd) (W := thr J e) (W1 := thr J e + 1)
      (LTB := LTB) (LPC := LPC) (LFS := LFS) (LSLT := LSLT) (LP2 := LP2) rfl hN hest hq hwd
      hWB).frame.run (σ := σ4)
      ⟨hn4, hsn4, hm4, hW4, hPS4, hQS4, hDS4, hWS4, hSA4, hltb4, hlpc4, hlfs4, hlslt4, hlp24,
        hTBle4⟩
  have hkk5 : σ5.vars "kk" = scaleK J e := by rw [hfv5 "kk" (by decide)]; exact hkk4
  have hout5 : σ5.out = [] := by rw [hfo5 (by decide)]; exact hout4
  -- 3. the scan
  have hINFB : infOf J < B := by omega
  have hTl : thr J e + 1 ≤ (σ5.arrs "TB").length := by
    rw [hclen "TB", hltb4]
    have h2 : thr J e + 1 ≤ 2 ^ wd * (thr J e + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have hTB : ∀ k < thr J e + 1, (σ5.arrs "TB").getD k 0 < B := fun k _ => by
    have := hcle k
    have h2 : infOf (scaled J e) = infOf J := rfl
    omega
  obtain ⟨σ6, hr6, ⟨hub, hatt, hn6, hkk6⟩, hfv6, hfa6, hfi6, hfo6⟩ :=
    (scanW_spec (B := B) (W1 := thr J e + 1) (INF := infOf J) (σ5.arrs "TB") hB1 (by omega) hTl
      hTB hINFB).frame.run (σ := σ5) ⟨hc2, hc1, rfl⟩
  have hout6 : σ6.out = [] := by rw [hfo6 (by decide)]; exact hout5
  have hopt : scaledOpt J e < thr J e + 1 := by
    have := scaledOpt_le_thr J he
    omega
  have hfin : ∀ c < thr J e + 1, (σ5.arrs "TB").getD c 0 < infOf J ↔ c ≤ scaledOpt J e := by
    intro c hc
    have h1 := hctab c (by omega)
    have h2 : infOf (scaled J e) = infOf J := rfl
    rw [h2] at h1
    rw [h1, hasWeight_scaled]
  have hbest : σ6.vars "best" = scaledOpt J e := best_eq_w hopt hfin hub hatt
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
      ⟨by rw [hkk6, hkk5], hbest, by rw [hn6]; exact hc4⟩
  refine ⟨σ7, _, (hr4.seq (hr5.seq (hr6.seq hr7))).mono ?_, le_rfl, ?_⟩
  · have hj : Kcore (scaled J e).jobs wd (thr J e + 1) = Kcore J.jobs wd (thr J e + 1) := rfl
    exact le_of_eq (by unfold cost5w; rw [hj]; ring)
  · rw [hout7, hout6]
    unfold fptasOut
    simp

end Lax496464Proofs.F5WRest
