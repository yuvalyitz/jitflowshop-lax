import Lax496464Proofs.Ram.F5QRest
import Lax496464Proofs.Ram.Q3Prog

/-!
# Theorem 5, Profile Sweep: the Whole Program

`prog5 = frontQ ; rest5`.  The front end of the exact program (`Q3Front.frontQ`) reads the
instance and puts the accuracy `e` in the threshold's place `W`, sorts by start time and builds the
sorted arrays; `rest5` does the rest.  `prog5_spec` says it writes `fptasOut I e`.
-/

namespace Lax496464Proofs.F5QProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.EstOrder Lax496464.Fptas Lax496464Proofs.Ram.EstPermute
open Lax496464Proofs.F5Math Lax496464Proofs.F5QLift Lax496464Proofs.F5QRest
open Lax496464Proofs.Ram.Q3Front (frontQ frontQ_spec qmaxOf_eq)
open Lax496464Proofs.Ram.Q3Core Lax496464Proofs.Ram.Q3Loop Lax496464Proofs.F5QMath
open Lax496464Proofs.Ram.Dp1 (pv qv dv)

/-- **The whole program.** -/
def prog5 : Com := .seq frontQ rest5

/-- The cost of the whole program. -/
def cost5 (n N qm bt bb : ℕ) : ℕ :=
  (Lax496464Proofs.Ram.Sort.sortK 90 n + 1000 * n + 1000) + cost5r n N qm bt bb

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The whole program is correct**: it writes `fptasOut I e`. -/
theorem prog5_spec {x : List ℕ} {I : Instance} {e B : ℕ}
    (hdec : EncodesDecisionInstance x I e) (he : 1 ≤ e) (hqpos : ∀ j : I.Job, 0 < I.q j)
    (hB20 : 20 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 8 < B)
    (hmB : I.machines + 8 < B) (heB : 2 * e + 8 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j + 8 < B)
    (hd8 : ∀ j : I.Job, (I.d j : ℕ) + 8 < B)
    (hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B)
    (hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B)
    (hT3 : ∀ a b c : I.Job, (I.d a : ℕ) + I.p b + I.q c + 9 < B)
    (hwB : ∀ j : I.Job, (I.w j : ℕ) + 8 < B) (hthrB : thr I e + 8 < B)
    {qm bb bt w1 N : ℕ} (hqm : qm = qmaxOf x) (hbb : bb = I.machines + 1) (hbt : bt = bb ^ qm)
    (hw1 : w1 = thr I e + 1) (hN : N = bt * w1)
    (hqmB : qm + 8 < B) (hbtB : bt + 8 < B) (hNB : N + 8 < B) (hoB : fptasOut I e + 8 < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs ∧
        (σ.arrs "T").length = N ∧ (σ.arrs "S").length = N ∧
        σ.arrs "G" = List.replicate bt 0)
      prog5 (fun _ σ' => σ'.out = [fptasOut I e]) (cost5 I.jobs N qm bt bb) := by
  refine Spec.of_exists fun σ0 ⟨hinp0, hout0, hA0, hSA0, hSB0, hPS0, hQS0, hDS0, hWS0, hT0, hS0, hG0⟩ => ?_
  have hB1 : 1 < B := by omega
  have hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B := fun a b => by have := hdq2 a b; omega
  have hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B := fun j => by have := hd8 j; omega
  have hpq' : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B := fun j => by have := hpqB j; omega
  obtain ⟨σ1, hr1, ⟨J, hest, hjobs, hmach, ⟨e', hJe⟩, hqJ, -, -, -, -, -, hwJ, hHW,
      hPS1, hQS1, hDS1, hWS1, hn1, hm1, hsn1, hW1, hinp1, hout1, hlens1⟩, hfv1, hfa1, hfi1, hfo1⟩ :=
    (frontQ_spec hdec hqpos (by omega) hxB (by omega) hpq' hdq hd2B hdd hdq2).frame.run (σ := σ0)
      ⟨hinp0, hout0, hA0, hSA0, hSB0, hPS0, hQS0, hDS0, hWS0⟩
  have hqmd : qm = ((List.range J.jobs).map (qv J)).foldr max 0 := by
    rw [hqm, qmaxOf_eq hdec e' hJe, hjobs]
  have hTl1 : (σ1.arrs "T").length = N := by rw [hfa1 "T" (by decide)]; exact hT0
  have hSl1 : (σ1.arrs "S").length = N := by rw [hfa1 "S" (by decide)]; exact hS0
  have hG1 : σ1.arrs "G" = List.replicate bt 0 := by rw [hfa1 "G" (by decide)]; exact hG0
  subst hJe
  -- the sentinel
  obtain ⟨INF, hINFd⟩ : ∃ INF, INF = ((List.range I.jobs).map (dv (permute I e'))).foldr max 0 + 1 :=
    ⟨_, rfl⟩
  have hdJ : ∀ v ∈ (List.range I.jobs).map (dv (permute I e')), v + 9 < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hk' := List.mem_range.mp hk
    have := hT3 (e' ⟨k, hk'⟩) (e' ⟨k, hk'⟩) (e' ⟨k, hk'⟩)
    have hdv : dv (permute I e') k = I.d (e' ⟨k, hk'⟩) :=
      Lax496464Proofs.Ram.Q3Prog.dv_permute e' k hk'
    rw [hdv]
    omega
  have hINF8 : INF + 8 < B := by
    have := Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt
      (l := (List.range I.jobs).map (dv (permute I e'))) (B := B) (c := 9) hdJ (by omega)
    rw [hINFd]; omega
  have hINFpq : ∀ j : (permute I e').Job, INF + ((permute I e').p j : ℕ) + (permute I e').q j + 8 < B := by
    intro j
    have := Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt
      (l := (List.range I.jobs).map (dv (permute I e')))
      (B := B) (c := I.p (e' j) + I.q (e' j) + 9)
      (fun v hv => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
        have hk' := List.mem_range.mp hk
        have := hT3 (e' ⟨k, hk'⟩) (e' j) (e' j)
        have hdv : dv (permute I e') k = I.d (e' ⟨k, hk'⟩) :=
          Lax496464Proofs.Ram.Q3Prog.dv_permute e' k hk'
        rw [hdv]
        omega) (by have := hT3 (e' j) (e' j) (e' j); omega)
    rw [hINFd]
    show _ + 1 + I.p (e' j) + I.q (e' j) + 8 < B
    omega
  -- the rest
  obtain ⟨σ2, hr2, hout2⟩ :=
    (rest5_spec (J := permute I e') (e := e) (qm := qm) (INF := INF) (bb := bb) (bt := bt)
      (w1 := w1) (N := N) (B := B) he hest hqJ hqmd hINFd hbb hbt hw1 hN hB20 (by
        show I.jobs + 8 < B; omega) hmB heB (fun j => hpqB (e' j)) (fun j => hd8 (e' j))
      (fun j => hwB (e' j)) hthrB hqmB hbtB hNB hINF8 hINFpq
      (by rw [fptasOut_permute]; exact hoB)).run (σ := σ1)
      ⟨hn1, hm1, hW1, hPS1, hQS1, hDS1, hWS1, hout1, hTl1, hSl1, hG1⟩
  refine ⟨σ2, _, hr1.seq hr2, ?_, ?_⟩
  · exact le_rfl
  · rw [hout2, fptasOut_permute]

end Lax496464Proofs.F5QProg
