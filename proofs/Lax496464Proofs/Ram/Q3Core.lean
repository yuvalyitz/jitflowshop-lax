import Lax496464Proofs.Ram.Q3Loop

/-!
# Theorem 3, profile sweep: the core

`coreCom` takes the sorted arrays `PS QS DS WS`, the scalars `n m W`, and leaves the final table in
`T`: `qm` and the sentinel `cinf = INF` are computed by scans, `bb = m+1`, `bt = bb^qm`,
`w1 = W+1`, `N = bt·w1`, the digit-sum table `G`, the initial table, then the loop over the jobs.

`coreCom_spec` describes the WHOLE final table: `TabSem bt w1 INF (Rsem J bb qm n) T` — for every
weight `c ≤ W` and every profile, whether weight `≥ c` is reachable within a load `P` — and not only
the decision bit at `c = W`; the answer scan (`Q3Finish`) is a separate, small `finish`.
-/

namespace Lax496464Proofs.Ram.Q3Core

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Model Lax496464Proofs.Ram.Q3Aux
open Lax496464Proofs.Ram.Q3Loop
open Lax496464Proofs.Ram.Q3Init (powCom powCom_spec maxCom maxCom_spec gInitCom gInitCom_spec)
open Lax496464Proofs.Ram.Q3Passes (fillCom fillCom_spec)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

abbrev V (s : String) : Expr := .var s

/-- The core program. -/
def coreCom : Com :=
  .seq (maxCom "QS" "qm")
    (.seq (.assign "bb" (.bin .add (V "m") (.lit 1)))
      (.seq (powCom "bt" "bb" "qm")
        (.seq (.assign "w1" (.bin .add (V "W") (.lit 1)))
          (.seq (.assign "N" (.bin .mul (V "bt") (V "w1")))
            (.seq gInitCom
              (.seq (maxCom "DS" "cinf")
                (.seq (.assign "cinf" (.bin .add (V "cinf") (.lit 1)))
                  (.seq (fillCom "T")
                    (.seq (.store "T" (.lit 0) (.lit 0))
                      (.seq (.assign "pt" (.lit 0)) mainLoop))))))))))

/-- The inputs the core reads and never changes. -/
structure Base (J : Instance) (W : ℕ) (σ : Env) : Prop where
  n : σ.vars "n" = J.jobs
  m : σ.vars "m" = J.machines
  W : σ.vars "W" = W
  PS : σ.arrs "PS" = (List.range J.jobs).map (pv J)
  QS : σ.arrs "QS" = (List.range J.jobs).map (qv J)
  DS : σ.arrs "DS" = (List.range J.jobs).map (dv J)
  WS : σ.arrs "WS" = (List.range J.jobs).map (wv J)
  out : σ.out = []

/-- A command that touches none of the inputs preserves them. -/
def Keeps (c : Com) : Prop :=
  "n" ∉ c.wvars ∧ "m" ∉ c.wvars ∧ "W" ∉ c.wvars ∧ "PS" ∉ c.warrs ∧ "QS" ∉ c.warrs ∧
    "DS" ∉ c.warrs ∧ "WS" ∉ c.warrs ∧ c.NoWrite

theorem Base.of_frame {J : Instance} {W : ℕ} {σ σ' : Env} {c : Com} (h : Base J W σ)
    (hk : Keeps c) (hfv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (hfa : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) (hfo : c.NoWrite → σ'.out = σ.out) :
    Base J W σ' := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hk
  exact ⟨(hfv _ k1).trans h.n, (hfv _ k2).trans h.m, (hfv _ k3).trans h.W,
    (hfa _ k4).trans h.PS, (hfa _ k5).trans h.QS, (hfa _ k6).trans h.DS, (hfa _ k7).trans h.WS,
    (hfo k8).trans h.out⟩

theorem foldr_max_lt' {l : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ v ∈ l, v < B) :
    l.foldr max 0 < B := by
  induction l with
  | nil => simpa using hB
  | cons a l ih =>
    simp only [List.foldr_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    omega

theorem le_foldr_max'' (l : List ℕ) (v : ℕ) (hv : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hv
  | cons a t ih =>
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp only [List.foldr_cons]; omega
    · simp only [List.foldr_cons]; exact le_trans (ih hv') (le_max_right _ _)

/-- `qm` bounds every processing time. -/
theorem q_le_qm (J : Instance) {qm : ℕ} (hqmd : qm = ((List.range J.jobs).map (qv J)).foldr max 0)
    (j : J.Job) : J.q j ≤ qm := by
  rw [hqmd]
  refine le_trans (le_of_eq ?_) (le_foldr_max'' _ (J.q j) ?_)
  · rfl
  · exact List.mem_map.mpr ⟨j, List.mem_range.mpr j.isLt, by simp [qv, j.isLt]⟩

/-- `INF` exceeds every due date. -/
theorem d_lt_INF (J : Instance) {INF : ℕ}
    (hINFd : INF = ((List.range J.jobs).map (dv J)).foldr max 0 + 1) (j : J.Job) : J.d j < INF := by
  rw [hINFd]
  have := le_foldr_max'' ((List.range J.jobs).map (dv J)) (J.d j)
    (List.mem_map.mpr ⟨j, List.mem_range.mpr j.isLt, by simp [dv, j.isLt]⟩)
  omega

/-- The cost of the core. -/
def coreK (N qm n bt bb : ℕ) : ℕ :=
  (20 * n + 8) + 4 + powK bb qm + 4 + 4 + (30 * bt + 6) + (20 * n + 8) + 4 + (14 * N + 6) +
    3 + 2 + ((evK N qm bb + 4 + 4) * n + 6)

set_option maxHeartbeats 4000000 in
/-- **The core is correct**: from the sorted arrays it leaves the whole final table in `T`. -/
theorem coreCom_spec {J : Instance} {W qm INF bb bt w1 N B : ℕ} (hd : Dims J W qm bb bt w1 N)
    (hqmd : qm = ((List.range J.jobs).map (qv J)).foldr max 0)
    (hINFd : INF = ((List.range J.jobs).map (dv J)).foldr max 0 + 1)
    (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) (hBd : Bds J W qm INF bt N B) :
    Spec B (fun σ => Base J W σ ∧ (σ.arrs "T").length = N ∧ (σ.arrs "S").length = N ∧
        σ.arrs "G" = List.replicate bt 0) coreCom
      (fun _ σ' => Core J W qm INF bb bt w1 N J.jobs σ') (coreK N qm J.jobs bt bb) := by
  refine Spec.of_exists fun σ0 ⟨hB0, hTl0, hSl0, hG0⟩ => ?_
  have hB1 := hBd.B1
  have hd' := hd
  obtain ⟨hbbd, hbtd, hw1d, hNd⟩ := hd
  have hnB := hBd.n
  have hmB := hBd.m
  have hWB := hBd.W
  have hqmB := hBd.qm
  have hbtB := hBd.bt
  have hNB := hBd.N
  have hINFB := hBd.INF
  have hbb1 : 1 ≤ bb := by omega
  have hbtpos : 1 ≤ bt := by rw [hbtd]; exact Nat.one_le_pow _ _ hbb1
  have hw1pos : 1 ≤ w1 := by omega
  have hNpos : 1 ≤ N := by rw [hNd]; exact Nat.mul_pos hbtpos hw1pos
  have hbbB : bb < B := by omega
  have hw1B : w1 < B := by omega
  have hqB : ∀ v ∈ (List.range J.jobs).map (qv J), v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hk' := List.mem_range.mp hk
    have := hBd.pq ⟨k, hk'⟩
    simp only [qv, hk', dif_pos]
    omega
  have hdB : ∀ v ∈ (List.range J.jobs).map (dv J), v + 2 < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hk' := List.mem_range.mp hk
    have := d_lt_INF J hINFd ⟨k, hk'⟩
    simp only [dv, hk', dif_pos]
    omega
  -- 1. `qm`
  obtain ⟨σ1, hr1, hq1, hfv1, hfa1, hfi1, hfo1⟩ :=
    (maxCom_spec (B := B) "QS" "qm" ((List.range J.jobs).map (qv J)) (by decide) hB1
      (by simp) hqB (by omega)).frame.run (σ := σ0) ⟨hB0.n, hB0.QS⟩
  have hqm1 : σ1.vars "qm" = qm := by rw [hq1, hqmd]
  have hBase1 : Base J W σ1 :=
    hB0.of_frame (by unfold Keeps; decide) hfv1 hfa1 hfo1
  have hm1 : σ1.vars "m" = J.machines := hBase1.m
  -- 2. `bb := m + 1`
  have hv2 : (Expr.bin .add (V "m") (.lit 1)).evalB B σ1 = some bb := by
    have hvm : (V "m").evalB B σ1 = some J.machines := by
      have := RunStep.eval_var B σ1 "m" (by rw [hm1]; omega)
      rwa [hm1] at this
    have := RunStep.eval_add B σ1 (V "m") (.lit 1) J.machines 1 hvm
      (RunStep.eval_lit B 1 σ1 hB1) (by omega)
    rw [← hbbd] at this
    exact this
  have r2 := Run.assign (B := B) (σ := σ1) (x := "bb") (e := .bin .add (V "m") (.lit 1)) (v := bb) hv2
  set σ2 : Env := σ1.setVar "bb" bb with hσ2
  clear_value σ2
  have hqm2 : σ2.vars "qm" = qm := by rw [hσ2]; simp [Env.setVar, hqm1]
  have hbb2 : σ2.vars "bb" = bb := by rw [hσ2]; simp [Env.setVar]
  have hAr2 : σ2.arrs = σ1.arrs := by rw [hσ2]; simp [Env.setVar]
  have hBase2 : Base J W σ2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ2]; simp [Env.setVar, hBase1.n]
    · rw [hσ2]; simp [Env.setVar, hBase1.m]
    · rw [hσ2]; simp [Env.setVar, hBase1.W]
    · rw [hAr2]; exact hBase1.PS
    · rw [hAr2]; exact hBase1.QS
    · rw [hAr2]; exact hBase1.DS
    · rw [hAr2]; exact hBase1.WS
    · rw [hσ2]; simpa [Env.setVar] using hBase1.out
  -- 3. `bt := bb ^ qm`
  obtain ⟨σ3, hr3, hbt3, hfv3, hfa3, hfi3, hfo3⟩ :=
    (powCom_spec (B := B) (b := bb) (e := qm) "bt" "bb" "qm" (by decide) (by decide) (by decide)
      (by decide) (by decide) hB1 (by rw [← hbtd]; omega) hbbB (by omega)).frame.run (σ := σ2)
      ⟨hbb2, hqm2⟩
  have hbt3' : σ3.vars "bt" = bt := by rw [hbt3, ← hbtd]
  have hBase3 : Base J W σ3 := hBase2.of_frame (by unfold Keeps; decide) hfv3 hfa3 hfo3
  have hbb3 : σ3.vars "bb" = bb := by rw [hfv3 "bb" (by decide)]; exact hbb2
  have hqm3 : σ3.vars "qm" = qm := by rw [hfv3 "qm" (by decide)]; exact hqm2
  -- 4. `w1 := W + 1`
  have hv4 : (Expr.bin .add (V "W") (.lit 1)).evalB B σ3 = some w1 := by
    have hvW : (V "W").evalB B σ3 = some W := by
      have := RunStep.eval_var B σ3 "W" (by rw [hBase3.W]; omega)
      rwa [hBase3.W] at this
    have := RunStep.eval_add B σ3 (V "W") (.lit 1) W 1 hvW (RunStep.eval_lit B 1 σ3 hB1) (by omega)
    rw [← hw1d] at this
    exact this
  have r4 := Run.assign (B := B) (σ := σ3) (x := "w1") (e := .bin .add (V "W") (.lit 1)) (v := w1) hv4
  set σ4 : Env := σ3.setVar "w1" w1 with hσ4
  clear_value σ4
  have hAr4 : σ4.arrs = σ3.arrs := by rw [hσ4]; simp [Env.setVar]
  have hbt4 : σ4.vars "bt" = bt := by rw [hσ4]; simp [Env.setVar, hbt3']
  have hbb4 : σ4.vars "bb" = bb := by rw [hσ4]; simp [Env.setVar, hbb3]
  have hqm4 : σ4.vars "qm" = qm := by rw [hσ4]; simp [Env.setVar, hqm3]
  have hw14 : σ4.vars "w1" = w1 := by rw [hσ4]; simp [Env.setVar]
  have hBase4 : Base J W σ4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ4]; simp [Env.setVar, hBase3.n]
    · rw [hσ4]; simp [Env.setVar, hBase3.m]
    · rw [hσ4]; simp [Env.setVar, hBase3.W]
    · rw [hAr4]; exact hBase3.PS
    · rw [hAr4]; exact hBase3.QS
    · rw [hAr4]; exact hBase3.DS
    · rw [hAr4]; exact hBase3.WS
    · rw [hσ4]; simpa [Env.setVar] using hBase3.out
  -- 5. `N := bt * w1`
  have hv5 : (Expr.bin .mul (V "bt") (V "w1")).evalB B σ4 = some N := by
    have hvb : (V "bt").evalB B σ4 = some bt := by
      have := RunStep.eval_var B σ4 "bt" (by rw [hbt4]; omega)
      rwa [hbt4] at this
    have hvw : (V "w1").evalB B σ4 = some w1 := by
      have := RunStep.eval_var B σ4 "w1" (by rw [hw14]; omega)
      rwa [hw14] at this
    have := RunStep.eval_mul B σ4 (V "bt") (V "w1") bt w1 hvb hvw (by rw [← hNd]; omega)
    rw [← hNd] at this
    exact this
  have r5 := Run.assign (B := B) (σ := σ4) (x := "N") (e := .bin .mul (V "bt") (V "w1")) (v := N) hv5
  set σ5 : Env := σ4.setVar "N" N with hσ5
  clear_value σ5
  have hAr5 : σ5.arrs = σ4.arrs := by rw [hσ5]; simp [Env.setVar]
  have hbt5 : σ5.vars "bt" = bt := by rw [hσ5]; simp [Env.setVar, hbt4]
  have hbb5 : σ5.vars "bb" = bb := by rw [hσ5]; simp [Env.setVar, hbb4]
  have hqm5 : σ5.vars "qm" = qm := by rw [hσ5]; simp [Env.setVar, hqm4]
  have hw15 : σ5.vars "w1" = w1 := by rw [hσ5]; simp [Env.setVar, hw14]
  have hN5 : σ5.vars "N" = N := by rw [hσ5]; simp [Env.setVar]
  have hBase5 : Base J W σ5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ5]; simp [Env.setVar, hBase4.n]
    · rw [hσ5]; simp [Env.setVar, hBase4.m]
    · rw [hσ5]; simp [Env.setVar, hBase4.W]
    · rw [hAr5]; exact hBase4.PS
    · rw [hAr5]; exact hBase4.QS
    · rw [hAr5]; exact hBase4.DS
    · rw [hAr5]; exact hBase4.WS
    · rw [hσ5]; simpa [Env.setVar] using hBase4.out
  -- the arrays `T S G` are untouched so far
  have hT5 : σ5.arrs "T" = σ0.arrs "T" := by
    rw [hAr5, hAr4, hfa3 "T" (by decide), hAr2, hfa1 "T" (by decide)]
  have hS5 : σ5.arrs "S" = σ0.arrs "S" := by
    rw [hAr5, hAr4, hfa3 "S" (by decide), hAr2, hfa1 "S" (by decide)]
  have hG5 : σ5.arrs "G" = σ0.arrs "G" := by
    rw [hAr5, hAr4, hfa3 "G" (by decide), hAr2, hfa1 "G" (by decide)]
  -- 6. the digit sums
  obtain ⟨σ6, hr6, ⟨hGl6, hGd6, hGle6⟩, hfv6, hfa6, hfi6, hfo6⟩ :=
    (gInitCom_spec (B := B) (bt := bt) (bb := bb) (qm := qm) hB1 hbb1 hbtd (by omega) hbbB).frame.run
      (σ := σ5) ⟨hbt5, hbb5, by rw [hG5, hG0]⟩
  have hBase6 : Base J W σ6 := hBase5.of_frame (by unfold Keeps; decide) hfv6 hfa6 hfo6
  have hN6 : σ6.vars "N" = N := by rw [hfv6 "N" (by decide)]; exact hN5
  have hT6 : σ6.arrs "T" = σ0.arrs "T" := by rw [hfa6 "T" (by decide)]; exact hT5.trans rfl
  have hS6 : σ6.arrs "S" = σ0.arrs "S" := by rw [hfa6 "S" (by decide)]; exact hS5
  -- 7. the largest due date
  have hDl : ((List.range J.jobs).map (dv J)).length = J.jobs := by simp
  obtain ⟨σ7, hr7, hq7, hfv7, hfa7, hfi7, hfo7⟩ :=
    (maxCom_spec (B := B) "DS" "cinf" ((List.range J.jobs).map (dv J)) (by decide) hB1 hDl
      (fun v hv => by have := hdB v hv; omega) (by omega)).frame.run (σ := σ6)
      ⟨by rw [hBase6.n], hBase6.DS⟩
  have hBase7 : Base J W σ7 := hBase6.of_frame (by unfold Keeps; decide) hfv7 hfa7 hfo7
  -- 8. `cinf := cinf + 1`
  have hcB : σ7.vars "cinf" + 1 < B := by
    rw [hq7]; have := foldr_max_lt' (l := (List.range J.jobs).map (dv J)) (B := B) (by omega)
      (fun v hv => by have := hdB v hv; omega)
    omega
  have hv8 : (Expr.bin .add (V "cinf") (.lit 1)).evalB B σ7 = some INF := by
    have hvc : (V "cinf").evalB B σ7 = some (σ7.vars "cinf") := RunStep.eval_var B σ7 "cinf" (by omega)
    have := RunStep.eval_add B σ7 (V "cinf") (.lit 1) (σ7.vars "cinf") 1 hvc
      (RunStep.eval_lit B 1 σ7 hB1) hcB
    rw [hq7, ← hINFd] at this
    exact this
  have r8 := Run.assign (B := B) (σ := σ7) (x := "cinf") (e := .bin .add (V "cinf") (.lit 1))
    (v := INF) hv8
  set σ8 : Env := σ7.setVar "cinf" INF with hσ8
  clear_value σ8
  have hAr8 : σ8.arrs = σ7.arrs := by rw [hσ8]; simp [Env.setVar]
  have hcinf8 : σ8.vars "cinf" = INF := by rw [hσ8]; simp [Env.setVar]
  have hN8 : σ8.vars "N" = N := by rw [hσ8]; simp [Env.setVar, hfv7 "N" (by decide), hN6]
  have hT8 : σ8.arrs "T" = σ0.arrs "T" := by rw [hAr8, hfa7 "T" (by decide)]; exact hT6
  have hS8 : σ8.arrs "S" = σ0.arrs "S" := by rw [hAr8, hfa7 "S" (by decide)]; exact hS6
  have hBase8 : Base J W σ8 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ8]; simp [Env.setVar, hBase7.n]
    · rw [hσ8]; simp [Env.setVar, hBase7.m]
    · rw [hσ8]; simp [Env.setVar, hBase7.W]
    · rw [hAr8]; exact hBase7.PS
    · rw [hAr8]; exact hBase7.QS
    · rw [hAr8]; exact hBase7.DS
    · rw [hAr8]; exact hBase7.WS
    · rw [hσ8]; simpa [Env.setVar] using hBase7.out
  -- 9. fill `T`
  obtain ⟨σ9, hr9, hT9, hfv9, hfa9, hfi9, hfo9⟩ :=
    (fillCom_spec (B := B) (N := N) (INF := INF) "T" (σ8.arrs "T") hB1
      (by rw [hT8]; exact hTl0) (by omega) (by omega)).frame.run (σ := σ8)
      ⟨hN8, hcinf8, rfl⟩
  have hBase9 : Base J W σ9 := hBase8.of_frame (by unfold Keeps; decide) hfv9 hfa9 hfo9
  -- 10. `T[0] := 0`
  have hl0 : (Expr.lit 0).evalB B σ9 = some 0 := evalB_lit (by omega)
  have hT9l : 0 < (σ9.arrs "T").length := by rw [hT9]; simp; omega
  have r10 := Run.store (B := B) (σ := σ9) (a := "T") (i := .lit 0) (e := .lit 0) (idx := 0) (v := 0)
    hl0 hl0 hT9l
  set σ10 : Env := σ9.setArr "T" 0 0 with hσ10
  clear_value σ10
  -- 11. `pt := 0`
  have hl0' : (Expr.lit 0).evalB B σ10 = some 0 := evalB_lit (by omega)
  have r11 := Run.assign (B := B) (σ := σ10) (x := "pt") (e := .lit 0) (v := 0) hl0'
  set σ11 : Env := σ10.setVar "pt" 0 with hσ11
  clear_value σ11
  -- the state before the loop
  have hR511 := hr6.seq (hr7.seq (r8.seq (hr9.seq (r10.seq r11))))
  have hR611 := hr7.seq (r8.seq (hr9.seq (r10.seq r11)))
  have hR811 := hr9.seq (r10.seq r11)
  have hBase11 : Base J W σ11 := hBase5.of_frame (c := _) (σ := σ5) (by unfold Keeps; decide)
    (fun y hy => hR511.frame_var y hy) (fun a ha => hR511.frame_arr a ha)
    (fun h => hR511.out_eq h)
  have hcore0 : Core J W qm INF bb bt w1 N 0 σ11 := by
    have hT11 : σ11.arrs "T" = (List.replicate (bt * w1) INF).set 0 0 := by
      rw [hσ11, hσ10]
      simp only [Env.setVar, Env.setArr, if_true]
      rw [hT9, ← hNd]
    refine ⟨⟨hBase11.n, hBase11.m, hBase11.W, ?_, ?_, ?_, ?_, ?_, ?_, hBase11.PS, hBase11.QS,
      hBase11.DS, hBase11.WS, ?_, ?_, ?_, hBase11.out⟩, ?_, ?_, ?_⟩
    · rw [hR511.frame_var "qm" (by decide)]; exact hqm5
    · rw [hR511.frame_var "bb" (by decide)]; exact hbb5
    · rw [hR511.frame_var "bt" (by decide)]; exact hbt5
    · rw [hR511.frame_var "w1" (by decide)]; exact hw15
    · rw [hR511.frame_var "N" (by decide)]; exact hN5
    · rw [hR811.frame_var "cinf" (by decide)]; exact hcinf8
    · rw [hR611.frame_arr "G" (by decide)]; exact hGl6
    · intro x hx
      rw [hR611.frame_arr "G" (by decide)]
      exact ⟨hGd6 x hx, hGle6 x hx⟩
    · rw [hR511.frame_arr "S" (by decide), hS5]; exact hSl0
    · rw [hσ11]; simp [Env.setVar, trefN]
    · rw [hT11]; simp [hNd]
    · rw [hT11]
      refine tabSem_congr (fun x hx c P => ?_) (Lax496464Proofs.Ram.Q3Tab.tab_init (bt := bt)
        (w1 := w1) (INF := INF) rfl)
      have hx' : x < (J.machines + 1) ^ qm := by rw [← hbbd, ← hbtd]; exact hx
      have := Rsem_zero J (qm := qm) x c P hx'
      rw [← hbbd] at this
      exact this.symm
  have hDimsE : Dims J W qm bb bt w1 N := hd'
  obtain ⟨σ12, hr12, hcore12, hjj12⟩ :=
    (mainLoop_spec hDimsE hest hq (q_le_qm J hqmd) (d_lt_INF J hINFd) hBd).run (σ := σ11) hcore0
  refine ⟨σ12, _, hr1.seq (r2.seq (hr3.seq (r4.seq (r5.seq (hr6.seq (hr7.seq (r8.seq
    (hr9.seq (r10.seq (r11.seq hr12)))))))))), ?_, hcore12⟩
  simp only [Expr.size]
  unfold coreK powK
  split_ifs <;> omega

end Lax496464Proofs.Ram.Q3Core
