import Lax496464Proofs.Ram.Q3Core
import Lax496464Proofs.Ram.Q3Finish
import Lax496464Proofs.Ram.Q3Front

/-!
# Theorem 3, profile sweep: the whole program, correct

`prog3 = frontQ ; coreCom ; finishCom`.  The front end reads and sorts, the core builds the whole
final table, the finish reads the answer off it.
-/

namespace Lax496464Proofs.Ram.Q3Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.EstOrder Lax496464Proofs.Ram.EstPermute
open Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Model Lax496464Proofs.Ram.Q3Aux
open Lax496464Proofs.Ram.Q3Loop Lax496464Proofs.Ram.Q3Core
open Lax496464Proofs.Ram.Q3Front (frontQ frontQ_spec qmaxOf_eq yes_iff)
open Lax496464Proofs.Ram.Q3Finish (finishCom finishCom_spec)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

theorem dv_permute {I : Instance} (e : Fin I.jobs ≃ Fin I.jobs) (k : ℕ) (hk : k < I.jobs) :
    dv (permute I e) k = I.d (e ⟨k, hk⟩) := by
  have hk2 : k < (permute I e).jobs := hk
  unfold dv
  rw [dif_pos hk2]
  rfl

/-- **The whole program.** -/
def prog3 : Com := .seq frontQ (.seq coreCom finishCom)

/-- The cost of the read-off. -/
def finK (bt : ℕ) : ℕ := (40 + 4) * bt + 6 + 20

/-- The cost of the whole program. -/
def cost3 (n N qm bt bb : ℕ) : ℕ :=
  (Lax496464Proofs.Ram.Sort.sortK 90 n + 1000 * n + 1000) + coreK N qm n bt bb + finK bt

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The whole program, correct.** -/
theorem prog3_spec {x : List ℕ} {I : Instance} {W B : ℕ}
    (hdec : EncodesDecisionInstance x I W) (hqpos : ∀ j : I.Job, 0 < I.q j)
    (hB2 : 20 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 8 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B) (hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B)
    (hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B)
    (hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B)
    (hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B)
    (hmB : I.machines + 8 < B) (hWB : W + 8 < B)
    {qm bb bt w1 N : ℕ} (hqm : qm = qmaxOf x) (hbb : bb = I.machines + 1) (hbt : bt = bb ^ qm)
    (hw1 : w1 = W + 1) (hN : N = bt * w1)
    (hqmB : qm + 8 < B) (hbtB : bt + 8 < B) (hNB : N + 8 < B)
    (hT3 : ∀ a b c : I.Job, (I.d a : ℕ) + I.p b + I.q c + 9 < B)
    (hwB : ∀ j : I.Job, (I.w j : ℕ) + 8 < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs ∧
        (σ.arrs "T").length = N ∧ (σ.arrs "S").length = N ∧
        σ.arrs "G" = List.replicate bt 0)
      prog3 (fun _ σ' => σ'.out = if Yes x then [1] else [0]) (cost3 I.jobs N qm bt bb) := by
  refine Spec.of_exists fun σ0 ⟨hinp0, hout0, hA0, hSA0, hSB0, hPS0, hQS0, hDS0, hWS0, hT0, hS0, hG0⟩ => ?_
  have hB1 : 1 < B := by omega
  -- the front end
  obtain ⟨σ1, hr1, ⟨J, hest, hjobs, hmach, ⟨e, hJe⟩, hqJ, hpqJ, hdqJ, hd2J, hddJ, hdq2J, hwJ, hHW,
      hPS1, hQS1, hDS1, hWS1, hn1, hm1, hsn1, hW1, hinp1, hout1, hlens1⟩, hfv1, hfa1, hfi1, hfo1⟩ :=
    (frontQ_spec hdec hqpos (by omega) hxB (by omega) hpqB hdq hd2B hdd hdq2).frame.run (σ := σ0)
      ⟨hinp0, hout0, hA0, hSA0, hSB0, hPS0, hQS0, hDS0, hWS0⟩
  have hqmd : qm = ((List.range J.jobs).map (qv J)).foldr max 0 := by
    rw [hqm, qmaxOf_eq hdec e hJe, hjobs]
  have hyes := yes_iff hdec hHW
  subst hJe
  have hBase : Base (permute I e) W σ1 :=
    ⟨hn1, hm1, hW1, hPS1, hQS1, hDS1, hWS1, hout1⟩
  have hd : Dims (permute I e) W qm bb bt w1 N := ⟨hbb, hbt, hw1, hN⟩
  obtain ⟨INF, hINFd⟩ : ∃ INF, INF = ((List.range I.jobs).map (dv (permute I e))).foldr max 0 + 1 :=
    ⟨_, rfl⟩
  have hdJ : ∀ k ∈ (List.range I.jobs).map (dv (permute I e)), k + 9 < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hk' := List.mem_range.mp hk
    have := hT3 (e ⟨k, hk'⟩) (e ⟨k, hk'⟩) (e ⟨k, hk'⟩)
    rw [dv_permute e k hk']
    omega
  have hBd : Bds (permute I e) W qm INF bt N B := by
    refine ⟨hB1, by show I.jobs + 8 < B; omega, hmB, hWB, hqmB, hbtB, hNB, ?_, ?_, ?_⟩
    · have := Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt (l := (List.range I.jobs).map (dv (permute I e)))
        (B := B) (c := 9) hdJ (by omega)
      rw [hINFd]; show _ + 1 + 8 < B; omega
    · intro j
      have hc := hT3 (e j) (e j) (e j)
      have := Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt (l := (List.range I.jobs).map (dv (permute I e)))
        (B := B) (c := I.p (e j) + I.q (e j) + 9)
        (fun v hv => by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
          have hk' := List.mem_range.mp hk
          have := hT3 (e ⟨k, hk'⟩) (e j) (e j)
          rw [dv_permute e k hk']
          omega) (by omega)
      rw [hINFd]; show _ + 1 + I.p (e j) + I.q (e j) + 8 < B; omega
    · intro j; exact hwB (e j)
  have hTl1 : (σ1.arrs "T").length = N := by rw [hfa1 "T" (by decide)]; exact hT0
  have hSl1 : (σ1.arrs "S").length = N := by rw [hfa1 "S" (by decide)]; exact hS0
  have hG1 : σ1.arrs "G" = List.replicate bt 0 := by rw [hfa1 "G" (by decide)]; exact hG0
  -- the core
  obtain ⟨σ2, hr2, hcore⟩ :=
    (coreCom_spec hd hqmd hINFd hest hqJ hBd).run (σ := σ1) ⟨hBase, hTl1, hSl1, hG1⟩
  -- the read-off
  have hINF0 : 0 < INF := by rw [hINFd]; omega
  have hTB : ∀ v ∈ σ2.arrs "T", v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hcell := getD_le_of_cells (bt := bt) (w1 := w1) (INF := INF) (T := σ2.arrs "T")
      (by omega) (by rw [hcore.Tl, hN]) (fun x hx c hc => (hcore.T x hx c hc).1) k
    rw [List.getD_eq_getElem _ _ hk] at hcell
    have := hBd.INF
    omega
  obtain ⟨σ3, hr3, hout3⟩ :=
    (finishCom_spec (B := B) (bt := bt) (w1 := w1) (W := W) (INF := INF) (σ2.arrs "T") hB1 hw1
      (by rw [hcore.Tl, hN]) hTB (by omega) (by have := hBd.INF; omega)
      (by rw [← hN]; omega)).run (σ := σ2)
      ⟨hcore.ctx.bt, hcore.ctx.w1, hcore.ctx.W, hcore.ctx.cinf, rfl, hcore.ctx.out⟩
  refine ⟨σ3, _, hr1.seq (hr2.seq hr3), ?_, ?_⟩
  · unfold cost3 finK
    have hj : (permute I e).jobs = I.jobs := rfl
    rw [hj]
    omega
  · rw [hout3]
    have hfin := Lax496464Proofs.Ram.Q3Model.Rsem_final (permute I e) hqJ (q_le_qm _ hqmd) hINF0
      (d_lt_INF _ hINFd) W
    have htab := Lax496464Proofs.Ram.Q3Tab.tab_final (bt := bt) (w1 := w1) (INF := INF) (W := W) hw1
      hINF0 hcore.T
    have hbt' : ((permute I e).machines + 1) ^ qm = bt := by rw [hbt, hbb]; rfl
    have hbb' : (permute I e).machines + 1 = bb := by rw [hbb]; rfl
    rw [hbt', hbb'] at hfin
    have hiff : Yes x ↔ ∃ y < bt, cell w1 (σ2.arrs "T") y W < INF :=
      hyes.trans (hfin.trans htab.symm)
    by_cases hy : Yes x
    · rw [if_pos hy, if_pos (hiff.mp hy)]
    · rw [if_neg hy, if_neg (fun h => hy (hiff.mpr h))]

end Lax496464Proofs.Ram.Q3Prog
