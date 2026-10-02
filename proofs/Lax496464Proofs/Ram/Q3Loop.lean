import Lax496464Proofs.Ram.Q3Defs
import Lax496464Proofs.Ram.Q3Digits
import Lax496464Proofs.Ram.Q3Tab
import Lax496464Proofs.Ram.Q3Model
import Lax496464Proofs.Ram.Q3Aux
import Lax496464Proofs.Ram.Q3Event
import Lax496464Proofs.Ram.Q3Init
import Lax496464Proofs.Ram.Q3Passes

/-!
# Theorem 3, Profile Sweep: One Event, Then the Loop over the Jobs

`eventCom` processes job `jj`: `prepCom` (data, reference time, shift), the two powers
`pwd = bb^δ'`, `pwq = bb^(q-1)`, then fill `S` with INF, marginalise `T` into `S`, take into `T`.
`Core j σ` says the state stands after `j` jobs: the constants, `pt = trefN j`, and the flat
table `T` *means* `Rsem J bb qm j`.  `eventCom_spec` moves `Core j` to `Core (j+1)` at cost
`O(N)`, `mainLoop_spec` iterates it.
-/

namespace Lax496464Proofs.Ram.Q3Loop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Model Lax496464Proofs.Ram.Q3Aux
open Lax496464Proofs.Ram.Q3Event (prepCom loadCom refCom loadCom_spec refCom_spec)
open Lax496464Proofs.Ram.Q3Init (powCom powCom_spec)
open Lax496464Proofs.Ram.Q3Passes (fillCom fillCom_spec margCom margCom_spec takeCom takeCom_spec)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

abbrev V (s : String) : Expr := .var s

/-- One event: job `jj`. -/
def eventCom : Com :=
  .seq prepCom
    (.seq (powCom "pwd" "bb" "dl")
      (.seq (powCom "pwq" "bb" "ex")
        (.seq (fillCom "S") (.seq margCom takeCom))))

/-- The loop over the jobs. -/
def mainLoop : Com :=
  .seq (.assign "jj" (.lit 0))
    (.while (.lt (V "jj") (V "n"))
      (.seq eventCom (.assign "jj" (.bin .add (V "jj") (.lit 1)))))

/-- The dimensions of the table, as equations (so that proofs may treat `bb bt w1 N` as atoms). -/
structure Dims (J : Instance) (W qm bb0 bt0 w10 N0 : ℕ) : Prop where
  bb : bb0 = J.machines + 1
  bt : bt0 = bb0 ^ qm
  w1 : w10 = W + 1
  N : N0 = bt0 * w10

/-- What never changes during the sweep. -/
structure Ctx (J : Instance) (W0 qm0 INF0 bb0 bt0 w10 N0 : ℕ) (σ : Env) : Prop where
  n : σ.vars "n" = J.jobs
  m : σ.vars "m" = J.machines
  W : σ.vars "W" = W0
  qm : σ.vars "qm" = qm0
  bb : σ.vars "bb" = bb0
  bt : σ.vars "bt" = bt0
  w1 : σ.vars "w1" = w10
  N : σ.vars "N" = N0
  cinf : σ.vars "cinf" = INF0
  PS : σ.arrs "PS" = (List.range J.jobs).map (pv J)
  QS : σ.arrs "QS" = (List.range J.jobs).map (qv J)
  DS : σ.arrs "DS" = (List.range J.jobs).map (dv J)
  WS : σ.arrs "WS" = (List.range J.jobs).map (wv J)
  Gl : (σ.arrs "G").length = bt0
  Gd : ∀ x < bt0, (σ.arrs "G").getD x 0 = digsum bb0 qm0 x ∧ (σ.arrs "G").getD x 0 ≤ x
  Sl : (σ.arrs "S").length = N0
  out : σ.out = []

/-- The state after `j` jobs. -/
structure Core (J : Instance) (W qm INF bb bt w1 N j : ℕ) (σ : Env) : Prop where
  ctx : Ctx J W qm INF bb bt w1 N σ
  pt : σ.vars "pt" = trefN J j
  Tl : (σ.arrs "T").length = N
  T : TabSem bt w1 INF (Rsem J bb qm j) (σ.arrs "T")

/-- The numeric side conditions: everything the sweep computes stays below the word bound. -/
structure Bds (J : Instance) (W0 qm0 INF0 bt0 N0 B0 : ℕ) : Prop where
  B1 : 1 < B0
  n : J.jobs + 8 < B0
  m : J.machines + 8 < B0
  W : W0 + 8 < B0
  qm : qm0 + 8 < B0
  bt : bt0 + 8 < B0
  N : N0 + 8 < B0
  INF : INF0 + 8 < B0
  pq : ∀ j : J.Job, INF0 + J.p j + J.q j + 8 < B0
  w : ∀ j : J.Job, J.w j + 8 < B0

/-- The cost of the take pass. -/
def takeK (N : ℕ) : ℕ := 204 * N + 6

/-- The cost of a power `bb ^ e`, `e ≤ qm`: constant when the base is `1`. -/
def powK (bb qm : ℕ) : ℕ := if bb = 1 then 10 else 12 * qm + 12

/-- The cost of one event (`takeK` is the take pass's). -/
def evK (N qm bb : ℕ) : ℕ := 70 + 2 * powK bb qm + (14 * N + 6) + (64 * N + 6) + takeK N

/-- The cost of a power is at most `powK`, whatever the exponent up to `qm`. -/
theorem powCost_le {bb e qm : ℕ} (h : e ≤ qm) :
    (if bb = 1 then 10 else 12 * e + 12) ≤ powK bb qm := by
  unfold powK; split_ifs <;> omega

set_option maxHeartbeats 8000000 in
/-- **One event.** -/
theorem eventCom_spec {J : Instance} {W qm INF bb bt w1 N B : ℕ} (hd : Dims J W qm bb bt w1 N)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hqm : ∀ j : J.Job, J.q j ≤ qm)
    (hINF : ∀ j : J.Job, J.d j < INF) (hBd : Bds J W qm INF bt N B) (j : ℕ) (hj : j < J.jobs) :
    Spec B (fun σ => Core J W qm INF bb bt w1 N j σ ∧ σ.vars "jj" = j) eventCom
      (fun _ σ' => Core J W qm INF bb bt w1 N (j + 1) σ' ∧ σ'.vars "jj" = j) (evK N qm bb) := by
  refine Spec.of_exists fun σ0 ⟨hC, hjj⟩ => ?_
  have hd' := hd
  have hbbd := hd.bb
  have hbtd := hd.bt
  have hw1d := hd.w1
  have hNd := hd.N
  have hB1 := hBd.B1
  have hnB := hBd.n
  have hmB := hBd.m
  have hqmB := hBd.qm
  have hbtB := hBd.bt
  have hNB := hBd.N
  have hINFB := hBd.INF
  have hc := hC.ctx
  have hbb1 : 1 ≤ bb := by omega
  have hbtpos : 1 ≤ bt := by rw [hbtd]; exact Nat.one_le_pow _ _ hbb1
  have hw1pos : 1 ≤ w1 := by omega
  have hbtN : bt ≤ N := by rw [hNd]; exact Nat.le_mul_of_pos_right _ hw1pos
  have hw1N : w1 ≤ N := by rw [hNd]; exact Nat.le_mul_of_pos_left _ hbtpos
  have hbbB : bb < B := by omega
  have hw1B : w1 < B := by omega
  have hjB : j < B := by omega
  obtain ⟨jb, hjb⟩ : ∃ jb : J.Job, (jb : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨hpv, hqv, hdv, hwv⟩ := job_facts (I := J) jb
  rw [hjb] at hpv hqv hdv hwv
  have hpq := hBd.pq jb
  have hwB := hBd.w jb
  have hdINF := hINF jb
  have hqle := hqm jb
  have hqpos := hq jb
  have hpjB : pv J j < B := by omega
  have hqjB : qv J j < B := by omega
  have hdjB : dv J j < B := by omega
  have hwjB : wv J j < B := by omega
  have hPSj : (σ0.arrs "PS").getD j 0 = pv J j := by
    rw [hc.PS]; exact getD_map_range _ _ _ hj
  have hQSj : (σ0.arrs "QS").getD j 0 = qv J j := by
    rw [hc.QS]; exact getD_map_range _ _ _ hj
  have hDSj : (σ0.arrs "DS").getD j 0 = dv J j := by
    rw [hc.DS]; exact getD_map_range _ _ _ hj
  have hWSj : (σ0.arrs "WS").getD j 0 = wv J j := by
    rw [hc.WS]; exact getD_map_range _ _ _ hj
  have hlens : ∀ (a : String) (f : ℕ → ℕ), σ0.arrs a = (List.range J.jobs).map f → j < (σ0.arrs a).length := by
    intro a f h; rw [h]; simpa using hj
  -- 1. load
  obtain ⟨σ1, hr1, ⟨hpj1, hqj1, hdj1, hwj1⟩, hfv1, hfa1, hfi1, hfo1⟩ :=
    (loadCom_spec (B := B) (j := j) (pj0 := pv J j) (qj0 := qv J j) (dj0 := dv J j)
      (wj0 := wv J j) hB1 hjB hpjB hqjB hdjB hwjB).frame.run (σ := σ0)
      ⟨hjj, hlens _ _ hc.PS, hlens _ _ hc.QS, hlens _ _ hc.DS, hlens _ _ hc.WS, hPSj, hQSj, hDSj,
        hWSj⟩
  have hptB : trefN J j < B := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, trefN_zero']; omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [trefN_succ k (by omega)]
      have := hINF ⟨k, by omega⟩
      omega
  -- 2. reference time and shift
  obtain ⟨σ2, hr2, ⟨hrf2, hdl2, hpt2, hex2⟩, hfv2, hfa2, hfi2, hfo2⟩ :=
    (refCom_spec (B := B) (qj0 := qv J j) (dj0 := dv J j) (qm := qm) (pt := trefN J j) hB1 hqjB hdjB
      (by omega) hptB).frame.run (σ := σ1)
      ⟨hqj1, hdj1, by rw [hfv1 "qm" (by decide)]; exact hc.qm, by rw [hfv1 "pt" (by decide)]; exact hC.pt⟩
  have hrfv : dv J j - qv J j = trefN J (j + 1) := by
    rw [trefN_succ j hj]; simp [dv, qv, hj]
  -- exponents are at most `qm`
  have hdl_le : min (dv J j - qv J j - trefN J j) qm ≤ qm := Nat.min_le_right _ _
  have hex_le : qv J j - 1 ≤ qm := by omega
  have hpwd_le : bb ^ (min (dv J j - qv J j - trefN J j) qm) ≤ bt := by
    rw [hbtd]; exact Nat.pow_le_pow_right hbb1 hdl_le
  have hpwq_le : bb ^ (qv J j - 1) ≤ bt := by
    rw [hbtd]; exact Nat.pow_le_pow_right hbb1 hex_le
  have hpwdpos : 0 < bb ^ (min (dv J j - qv J j - trefN J j) qm) := Nat.pow_pos hbb1
  have hpwqpos : 0 < bb ^ (qv J j - 1) := Nat.pow_pos hbb1
  -- 3. `pwd`
  have hbb2 : σ2.vars "bb" = bb := by
    rw [hfv2 "bb" (by decide), hfv1 "bb" (by decide)]; exact hc.bb
  obtain ⟨σ3, hr3, hpwd3, hfv3, hfa3, hfi3, hfo3⟩ :=
    (powCom_spec (B := B) (b := bb) (e := min (dv J j - qv J j - trefN J j) qm) "pwd" "bb" "dl"
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 (by omega) hbbB (by omega)).frame.run
      (σ := σ2) ⟨hbb2, hdl2⟩
  -- 4. `pwq`
  have hbb3 : σ3.vars "bb" = bb := by rw [hfv3 "bb" (by decide)]; exact hbb2
  have hex3 : σ3.vars "ex" = qv J j - 1 := by rw [hfv3 "ex" (by decide)]; exact hex2
  obtain ⟨σ4, hr4, hpwq4, hfv4, hfa4, hfi4, hfo4⟩ :=
    (powCom_spec (B := B) (b := bb) (e := qv J j - 1) "pwq" "bb" "ex"
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 (by omega) hbbB (by omega)).frame.run
      (σ := σ3) ⟨hbb3, hex3⟩
  -- 5. fill `S`
  have hN4 : σ4.vars "N" = N := by
    rw [hfv4 "N" (by decide), hfv3 "N" (by decide), hfv2 "N" (by decide), hfv1 "N" (by decide)]
    exact hc.N
  have hcinf4 : σ4.vars "cinf" = INF := by
    rw [hfv4 "cinf" (by decide), hfv3 "cinf" (by decide), hfv2 "cinf" (by decide),
      hfv1 "cinf" (by decide)]
    exact hc.cinf
  have hS4 : σ4.arrs "S" = σ0.arrs "S" := by
    rw [hfa4 "S" (by decide), hfa3 "S" (by decide), hfa2 "S" (by decide), hfa1 "S" (by decide)]
  have hT4 : σ4.arrs "T" = σ0.arrs "T" := by
    rw [hfa4 "T" (by decide), hfa3 "T" (by decide), hfa2 "T" (by decide), hfa1 "T" (by decide)]
  obtain ⟨σ5, hr5, hS5, hfv5, hfa5, hfi5, hfo5⟩ :=
    (fillCom_spec (B := B) (N := N) (INF := INF) "S" (σ4.arrs "S") hB1
      (by rw [hS4]; exact hc.Sl) (by omega) (by omega)).frame.run (σ := σ4) ⟨hN4, hcinf4, rfl⟩
  -- 6. marginalise
  have hTle : ∀ i, (σ0.arrs "T").getD i 0 ≤ INF :=
    getD_le_of_cells (bt := bt) (w1 := w1) hw1pos (by rw [hC.Tl, hNd])
      (fun x hx c hc' => (hC.T x hx c hc').1)
  have hpwd5 : σ5.vars "pwd" = bb ^ (min (dv J j - qv J j - trefN J j) qm) := by
    rw [hfv5 "pwd" (by decide), hfv4 "pwd" (by decide)]; exact hpwd3
  obtain ⟨σ6, hr6, ⟨hMarg, hSl6⟩, hfv6, hfa6, hfi6, hfo6⟩ :=
    (margCom_spec (B := B) (bt := bt) (w1 := w1) (pwd := bb ^ (min (dv J j - qv J j - trefN J j) qm))
      (INF := INF) (σ0.arrs "T") hB1 hw1pos hpwdpos (by rw [hC.Tl, hNd]) hTle (by omega) hw1B
      (by omega) (by omega)).frame.run (σ := σ5)
      ⟨by rw [hfv5 "N" (by decide), hN4, hNd], by
        rw [hfv5 "w1" (by decide), hfv4 "w1" (by decide), hfv3 "w1" (by decide),
          hfv2 "w1" (by decide), hfv1 "w1" (by decide)]; exact hc.w1,
        hpwd5, by rw [hfa5 "T" (by decide), hT4], by rw [hS5, hNd]⟩
  -- 7. take
  have hSle6 : ∀ i, (σ6.arrs "S").getD i 0 ≤ INF :=
    getD_le_of_cells (bt := bt) (w1 := w1) hw1pos hSl6 (fun x hx c hc' => (hMarg x hx c hc').1)
  have hTle6 : (σ6.arrs "T").length = bt * w1 := by
    rw [hfa6 "T" (by decide), hfa5 "T" (by decide), hT4, hC.Tl, hNd]
  have hG6 : σ6.arrs "G" = σ0.arrs "G" := by
    rw [hfa6 "G" (by decide), hfa5 "G" (by decide), hfa4 "G" (by decide), hfa3 "G" (by decide),
      hfa2 "G" (by decide), hfa1 "G" (by decide)]
  have hGB : ∀ x, (σ0.arrs "G").getD x 0 < B := by
    intro x
    by_cases hx : x < bt
    · have := (hc.Gd x hx).2; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hc.Gl]; omega)]
      simp; omega
  have hR46 := hr5.seq hr6
  have hR26 := hr3.seq (hr4.seq hR46)
  have hR06 := hr1.seq (hr2.seq hR26)
  have hN6 : σ6.vars "N" = N := (hR06.frame_var "N" (by decide)).trans hc.N
  have hw16 : σ6.vars "w1" = w1 := (hR06.frame_var "w1" (by decide)).trans hc.w1
  have hbb6 : σ6.vars "bb" = bb := (hR06.frame_var "bb" (by decide)).trans hc.bb
  have hm6 : σ6.vars "m" = J.machines := (hR06.frame_var "m" (by decide)).trans hc.m
  have hpwq6 : σ6.vars "pwq" = bb ^ (qv J j - 1) := (hR46.frame_var "pwq" (by decide)).trans hpwq4
  have hpj6 : σ6.vars "pj" = pv J j :=
    (hR26.frame_var "pj" (by decide)).trans ((hfv2 "pj" (by decide)).trans hpj1)
  have hqj6 : σ6.vars "qj" = qv J j :=
    (hR26.frame_var "qj" (by decide)).trans ((hfv2 "qj" (by decide)).trans hqj1)
  have hdj6 : σ6.vars "dj" = dv J j :=
    (hR26.frame_var "dj" (by decide)).trans ((hfv2 "dj" (by decide)).trans hdj1)
  have hwj6 : σ6.vars "wj" = wv J j :=
    (hR26.frame_var "wj" (by decide)).trans ((hfv2 "wj" (by decide)).trans hwj1)
  obtain ⟨σ7, hr7, ⟨hTake, hTl7⟩, hfv7, hfa7, hfi7, hfo7⟩ :=
    (takeCom_spec (B := B) (bt := bt) (w1 := w1) (bb := bb) (m := J.machines) (INF := INF)
      (pwq := bb ^ (qv J j - 1)) (pj := pv J j) (qj := qv J j) (dj := dv J j) (wj := wv J j)
      (σ0.arrs "G") (σ6.arrs "S") (σ6.arrs "T") hB1 hw1pos (by omega) hpwqpos hc.Gl hSl6 hSle6
      hTle6 (by omega) hw1B hbbB (by omega) (by omega) hpjB (by omega) hwjB hqjB (by omega) hGB).frame.run
      (σ := σ6) ⟨hN6.trans hNd, hw16, hbb6, hm6, hpwq6, hpj6, hqj6, hdj6, hwj6, hG6, rfl, rfl⟩
  have hRall := (hr1.seq hr2).seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq hr7))))
  have hR27 := hr3.seq (hr4.seq (hr5.seq (hr6.seq hr7)))
  refine ⟨σ7, evK N qm bb, hRall.mono ?_, le_rfl, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · have h1 := powCost_le (bb := bb) hdl_le
    have h2 := powCost_le (bb := bb) hex_le
    unfold evK takeK
    rw [← hNd]
    omega
  · exact (hRall.frame_var "n" (by decide)).trans hc.n
  · exact (hRall.frame_var "m" (by decide)).trans hc.m
  · exact (hRall.frame_var "W" (by decide)).trans hc.W
  · exact (hRall.frame_var "qm" (by decide)).trans hc.qm
  · exact (hRall.frame_var "bb" (by decide)).trans hc.bb
  · exact (hRall.frame_var "bt" (by decide)).trans hc.bt
  · exact (hRall.frame_var "w1" (by decide)).trans hc.w1
  · exact (hRall.frame_var "N" (by decide)).trans hc.N
  · exact (hRall.frame_var "cinf" (by decide)).trans hc.cinf
  · exact (hRall.frame_arr "PS" (by decide)).trans hc.PS
  · exact (hRall.frame_arr "QS" (by decide)).trans hc.QS
  · exact (hRall.frame_arr "DS" (by decide)).trans hc.DS
  · exact (hRall.frame_arr "WS" (by decide)).trans hc.WS
  · rw [hRall.frame_arr "G" (by decide)]; exact hc.Gl
  · intro x hx
    rw [hRall.frame_arr "G" (by decide)]
    exact hc.Gd x hx
  · rw [hfa7 "S" (by decide), hSl6, hNd]
  · exact (hRall.out_eq (by decide)).trans hc.out
  · rw [hR27.frame_var "pt" (by decide), hpt2, hrfv]
  · rw [hTl7, hNd]
  · have hstep := Lax496464Proofs.Ram.Q3Tab.tab_step (bt := bt) (w1 := w1) (bb := bb)
      (m := J.machines) (qm := qm) (INF := INF)
      (pwd := bb ^ (min (dv J j - qv J j - trefN J j) qm)) (pwq := bb ^ (qv J j - 1))
      (pj := pv J j) (qj := qv J j) (dj := dv J j) (wj := wv J j) (R := Rsem J bb qm j)
      (T := σ0.arrs "T") (S := σ6.arrs "S") (T' := σ7.arrs "T") (G := σ0.arrs "G")
      (by omega) (fun x hx => (hc.Gd x hx).1) hC.T hMarg hTake
    rw [hrfv] at hstep
    refine tabSem_congr (fun x hx c P => ?_) hstep
    have key := Rsem_succ J hest hq hqm j hj x c P (by rw [← hbbd, ← hbtd]; exact hx)
    rw [← hbbd, ← hbtd] at key
    exact key.symm
  · exact (hRall.frame_var "jj" (by decide)).trans hjj


/-! ## The loop -/

theorem Core.setVar_jj {J : Instance} {W qm INF bb bt w1 N j : ℕ} {σ : Env}
    (h : Core J W qm INF bb bt w1 N j σ) (v : ℕ) :
    Core J W qm INF bb bt w1 N j (σ.setVar "jj" v) := by
  have harr : (σ.setVar "jj" v).arrs = σ.arrs := rfl
  have hc := h.ctx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [Env.setVar, hc.n]
  · simp [Env.setVar, hc.m]
  · simp [Env.setVar, hc.W]
  · simp [Env.setVar, hc.qm]
  · simp [Env.setVar, hc.bb]
  · simp [Env.setVar, hc.bt]
  · simp [Env.setVar, hc.w1]
  · simp [Env.setVar, hc.N]
  · simp [Env.setVar, hc.cinf]
  · rw [harr]; exact hc.PS
  · rw [harr]; exact hc.QS
  · rw [harr]; exact hc.DS
  · rw [harr]; exact hc.WS
  · rw [harr]; exact hc.Gl
  · intro x hx; rw [harr]; exact hc.Gd x hx
  · rw [harr]; exact hc.Sl
  · exact hc.out
  · simp [Env.setVar, h.pt]
  · rw [harr]; exact h.Tl
  · rw [harr]; exact h.T

/-- The loop invariant: the counter is `j ≤ n` and the state stands after `j` jobs. -/
def LInv (J : Instance) (W qm INF bb bt w1 N : ℕ) (σ : Env) : Prop :=
  σ.vars "jj" ≤ J.jobs ∧ Core J W qm INF bb bt w1 N (σ.vars "jj") σ

theorem mainBody_spec {J : Instance} {W qm INF bb bt w1 N B : ℕ} (hd : Dims J W qm bb bt w1 N)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hqm : ∀ j : J.Job, J.q j ≤ qm)
    (hINF : ∀ j : J.Job, J.d j < INF) (hBd : Bds J W qm INF bt N B) :
    Spec B (fun σ => LInv J W qm INF bb bt w1 N σ ∧ σ.vars "jj" < J.jobs)
      (.seq eventCom (.assign "jj" (.bin .add (V "jj") (.lit 1))))
      (fun σ σ' => LInv J W qm INF bb bt w1 N σ' ∧ σ'.vars "jj" = σ.vars "jj" + 1)
      (evK N qm bb + 4) := by
  intro σ ⟨⟨hle, hCore⟩, hlt⟩
  obtain ⟨σ1, hr1, hC1, hj1⟩ :=
    (eventCom_spec hd hest hq hqm hINF hBd (σ.vars "jj") hlt) σ ⟨hCore, rfl⟩
  have hjB : σ1.vars "jj" + 1 < B := by rw [hj1]; have := hBd.n; omega
  have hv1 : (V "jj").evalB B σ1 = some (σ1.vars "jj") := evalB_var (by omega)
  have hv2 : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit hBd.B1
  have hr2 := Run.assign (B := B) (σ := σ1) (x := "jj") (e := .bin .add (V "jj") (.lit 1))
    (v := σ1.vars "jj" + 1) (evalB_bin hv1 hv2 hjB)
  refine ⟨_, (hr1.seq hr2).mono ?_, ⟨?_, ?_⟩, ?_⟩
  · simp only [Expr.size]; omega
  · simp [Env.setVar, hj1]; omega
  · simp only [Env.setVar, if_true, hj1]
    exact hC1.setVar_jj _
  · simp [Env.setVar, hj1]

/-- **The loop over the jobs.** -/
theorem mainLoop_spec {J : Instance} {W qm INF bb bt w1 N B : ℕ} (hd : Dims J W qm bb bt w1 N)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hqm : ∀ j : J.Job, J.q j ≤ qm)
    (hINF : ∀ j : J.Job, J.d j < INF) (hBd : Bds J W qm INF bt N B) :
    Spec B (fun σ => Core J W qm INF bb bt w1 N 0 σ) mainLoop
      (fun _ σ' => Core J W qm INF bb bt w1 N J.jobs σ' ∧ σ'.vars "jj" = J.jobs)
      ((evK N qm bb + 4 + 4) * J.jobs + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := .seq eventCom (.assign "jj" (.bin .add (V "jj") (.lit 1))))
    "jj" "n" (LInv J W qm INF bb bt w1 N) J.jobs (evK N qm bb + 4) (by have := hBd.n; omega)
    (fun σ h => h.1) (fun σ h => h.2.ctx.n) (mainBody_spec hd hest hq hqm hINF hBd)
  refine ((hloop.pre (P' := fun σ => Core J W qm INF bb bt w1 N 0 σ) ?_).post ?_)
  · intro σ hσ
    refine ⟨by simp [Env.setVar], ?_⟩
    simpa [Env.setVar] using hσ.setVar_jj 0
  · intro σ σ' _ ⟨⟨_, hC⟩, hjj⟩
    exact ⟨by rw [hjj] at hC; exact hC, hjj⟩

end Lax496464Proofs.Ram.Q3Loop
