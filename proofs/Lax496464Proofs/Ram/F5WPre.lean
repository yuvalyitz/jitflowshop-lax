import Lax496464Proofs.Ram.F5QRest
import Lax496464Proofs.Ram.F5WScan

/-!
# Theorem 5 (endpoint sweep): the passes before the exact core

`pre5w = fit ; k ; rescale ; W := 2 e n²`.  Run on the sorted arrays of `J` with the accuracy `e` in
the scalar `W`, it leaves in `WS` the weights of `scaled J e`, in `kk` the factor `scaleK J e` and in
`W` the threshold `thr J e`.
-/

namespace Lax496464Proofs.F5WPre

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QRest
open Lax496464Proofs.Ram.F5QFit (fitCom fitCom_spec fitArr fitVal)
open Lax496464Proofs.Ram.F5QScale (kCom kCom_spec wCom wCom_spec rescaleCom rescaleCom_spec)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The passes before the core. -/
def pre5w : Com := .seq fitCom (.seq kCom (.seq rescaleCom wCom))

set_option maxHeartbeats 8000000 in
open Classical in
theorem pre5w_spec {J : Instance} {e B : ℕ} (he : 1 ≤ e) (hB1 : 1 < B)
    (hnB : J.jobs + 8 < B) (heB : 2 * e + 8 < B)
    (hpqB : ∀ j : J.Job, (J.p j : ℕ) + J.q j + 8 < B) (hdB : ∀ j : J.Job, (J.d j : ℕ) + 8 < B)
    (hwB : ∀ j : J.Job, (J.w j : ℕ) + 8 < B) (hthrB : thr J e + 8 < B) :
    Spec B
      (fun σ => σ.vars "n" = J.jobs ∧ σ.vars "W" = e ∧
        σ.arrs "PS" = PSl J ∧ σ.arrs "QS" = QSl J ∧ σ.arrs "DS" = DSl J ∧
        σ.arrs "WS" = WSl J)
      pre5w
      (fun _ σ' => σ'.vars "W" = thr J e ∧ σ'.vars "kk" = scaleK J e ∧
        σ'.arrs "WS" = (List.range J.jobs).map (wv (scaled J e)))
      ((44 * J.jobs + 10) + 20 + (44 * J.jobs + 10) + 10) := by
  refine Spec.of_exists fun σ0 ⟨hn0, hW0, hPS0, hQS0, hDS0, hWS0⟩ => ?_
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
  have hW1 : σ1.vars "W" = e := by rw [hfv1 "W" (by decide)]; exact hW0
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
  have hW2 : σ2.vars "W" = e := by rw [hfv2 "W" (by decide)]; exact hW1
  have hWS2 : σ2.arrs "WS" = fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs := by
    rw [hfa2 "WS" (by decide)]; exact hWS1
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
  have hW3 : σ3.vars "W" = e := by rw [hfv3 "W" (by decide)]; exact hW2
  have hkk3 : σ3.vars "kk" = scaleK J e := by rw [hfv3 "kk" (by decide)]; exact hkk2'
  -- 4. the threshold
  have hn2B : 2 * e * J.jobs < B := by
    rcases Nat.eq_zero_or_pos J.jobs with h | h
    · rw [h]; omega
    · have := two_e_n_le_thr J e h; omega
  have hthrB' : 2 * e * J.jobs * J.jobs < B := by unfold thr at hthrB; omega
  obtain ⟨σ4, hr4, hW4, hfv4, hfa4, hfi4, hfo4⟩ :=
    (wCom_spec (B := B) (e := e) (n := J.jobs) hB1 (by omega) (by omega) (by omega) (by omega)
      hn2B hthrB').frame.run (σ := σ3) ⟨hW3, hn3⟩
  have hkk4 : σ4.vars "kk" = scaleK J e := by rw [hfv4 "kk" (by decide)]; exact hkk3
  have hWS4 : σ4.arrs "WS" = (List.range J.jobs).map (wv (scaled J e)) := by
    rw [hfa4 "WS" (by decide)]; exact hWS3
  refine ⟨σ4, _, (hr1.seq (hr2.seq (hr3.seq hr4))).mono ?_, le_rfl, hW4.1, hkk4, hWS4⟩
  exact le_of_eq (by ring)

end Lax496464Proofs.F5WPre
