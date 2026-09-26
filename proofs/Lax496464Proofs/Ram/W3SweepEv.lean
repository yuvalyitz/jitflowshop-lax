import Lax496464Proofs.Ram.W3Loops
import Lax496464Proofs.Ram.Corollary1Prog
import Lax496464Proofs.Ram.DpMArr
import Lax496464Proofs.Ram.W3SweepModel

/-!
# The sweep loop's events, on the machine

The two kinds of event, as IMP+ commands, each proved to move the machine's state along the
model's `step` (`startEv_spec`, `dueEv_spec`), and the test that chooses between them
(`decideCom_spec`).
-/

namespace Lax496464Proofs.Ram.W3SweepEv

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464.FlowShop Lax496464.EstOrder
open Lax496464Proofs.Ram.W3Bits Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3Model
open Lax496464Proofs.Ram.W3SweepModel
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)
open Lax496464Proofs.Ram.W3Loops (V dueLoop startLoop growPC tabOf dueLoop_table startLoop_table
  growPC_table lt_of_bit_clear)

/-- Close what `run_vcg` leaves: substitute the state variables, collapse the `setVar` towers,
normalise, and try arithmetic. -/
macro "vcg_fin" : tactic => `(tactic| (
  all_goals (try subst_vars)
  all_goals (try simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar] at *)
  all_goals (try simp at *)
  all_goals (try omega)))

/-- Like `vcg_fin`, for blocks that step over a loop: the loop's frame facts are used by
`simp_all`. -/
macro "vcg_fin2" : tactic => `(tactic| (
  all_goals (try simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar] at *)
  all_goals (try simp_all)
  all_goals (try omega)))

/-! ## Which event comes next -/

/-- `ist := 1` iff the next event is the start of job `ip`:
`ip < n ∧ (n ≤ kp ∨ DS[ip] < DS[SA[kp]] + QS[ip] ∨ (DS[ip] = DS[SA[kp]] + QS[ip] ∧ ip < SA[kp]))`. -/
def decideCom : Com :=
  .seq (.assign "ist" (.lit 0))
    (.ite (.lt (V "ip") (V "n"))
      (.ite (.lt (V "kp") (V "n"))
        (.seq (.assign "jj" (.get "SA" (V "kp")))
          (.ite (.lt (.get "DS" (V "ip")) (.bin .add (.get "DS" (V "jj")) (.get "QS" (V "ip"))))
            (.assign "ist" (.lit 1))
            (.ite (.eq (.get "DS" (V "ip")) (.bin .add (.get "DS" (V "jj")) (.get "QS" (V "ip"))))
              (.ite (.lt (V "ip") (V "jj")) (.assign "ist" (.lit 1)) .skip)
              .skip)))
        (.assign "ist" (.lit 1)))
      .skip)

theorem decideCom_spec {B : ℕ} (hB : 1 < B) (DS QS SA : List ℕ) (N i k : ℕ)
    (hDSl : DS.length = N) (hQSl : QS.length = N) (hSAl : SA.length = N)
    (hSAN : ∀ t < N, SA.getD t 0 < N) (hDSB : ∀ v ∈ DS, v < B)
    (hsum : ∀ a b, a < N → b < N → DS.getD a 0 + QS.getD b 0 < B) (hNB : N < B)
    (hiB : i < B) (hkB : k < B) :
    Spec B (fun σ => σ.arrs "DS" = DS ∧ σ.arrs "QS" = QS ∧ σ.arrs "SA" = SA ∧
        σ.vars "n" = N ∧ σ.vars "ip" = i ∧ σ.vars "kp" = k)
      decideCom
      (fun _σ σ' => σ'.vars "ist" = (if i < N ∧ (N ≤ k ∨
          DS.getD i 0 < DS.getD (SA.getD k 0) 0 + QS.getD i 0 ∨
          (DS.getD i 0 = DS.getD (SA.getD k 0) 0 + QS.getD i 0 ∧ i < SA.getD k 0)) then 1 else 0))
      60 := by
  have hDSB' : ∀ t, t < N → DS.getD t 0 < B := fun t ht =>
    hDSB _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have e1 : k < N → SA.getD k 0 < N := fun h => hSAN k h
  have e2 : i < N → DS.getD i 0 < B := fun h => hDSB' i h
  have e3 : k < N → DS.getD (SA.getD k 0) 0 < B := fun h => hDSB' _ (hSAN k h)
  have e4 : i < N → k < N → DS.getD (SA.getD k 0) 0 + QS.getD i 0 < B := fun h h' =>
    hsum _ _ (hSAN k h') h
  have e5 : i < N → QS.getD i 0 < B := fun h => by
    have := hsum i i h h; omega
  clear hSAN hDSB hsum hDSB'
  run_vcg
  vcg_fin

/-! ## The phases of the two events -/

/-- The due event's set-up: the job `jj = SA[kp]`, its slot `bb = SLT[jj]`, the bit `b2 = P2[bb]`. -/
def dueSetup : Com :=
  .seq (.assign "jj" (.get "SA" (V "kp")))
    (.seq (.assign "bb" (.get "SLT" (V "jj"))) (.assign "b2" (.get "P2" (V "bb"))))

theorem dueSetup_spec {B : ℕ} (SA SLT P2 : List ℕ) (k : ℕ)
    (hk : k < SA.length) (hkB : k < B) (hjB : SA.getD k 0 < B) (hjL : SA.getD k 0 < SLT.length)
    (hbB : SLT.getD (SA.getD k 0) 0 < B) (hbL : SLT.getD (SA.getD k 0) 0 < P2.length)
    (hpB : P2.getD (SLT.getD (SA.getD k 0) 0) 0 < B) :
    Spec B (fun σ => σ.arrs "SA" = SA ∧ σ.arrs "SLT" = SLT ∧ σ.arrs "P2" = P2 ∧
        σ.vars "kp" = k)
      dueSetup
      (fun _ σ' => σ'.vars "jj" = SA.getD k 0 ∧ σ'.vars "bb" = SLT.getD (SA.getD k 0) 0 ∧
        σ'.vars "b2" = P2.getD (SLT.getD (SA.getD k 0) 0) 0) 20 := by
  run_vcg
  vcg_fin

/-- The tail of a due event: push the slot on the free stack, count the event. -/
def dueTail : Com :=
  .seq (.store "FS" (V "fp") (V "bb"))
    (.seq (.assign "fp" (.bin .add (V "fp") (.lit 1))) (.assign "kp" (.bin .add (V "kp") (.lit 1))))

theorem dueTail_spec {B : ℕ} (hB : 1 < B) (FS : List ℕ) (f b k : ℕ) (hf : f < FS.length)
    (hbB : b < B) (hfB : f + 1 < B) (hkB : k + 1 < B) :
    Spec B (fun σ => σ.arrs "FS" = FS ∧ σ.vars "fp" = f ∧ σ.vars "bb" = b ∧ σ.vars "kp" = k)
      dueTail
      (fun _ σ' => σ'.arrs "FS" = FS.set f b ∧ σ'.vars "fp" = f + 1 ∧ σ'.vars "kp" = k + 1)
      20 := by
  run_vcg
  vcg_fin

/-- **A due event.** -/
def dueEv : Com := .seq dueSetup (.seq dueLoop dueTail)

/-! ## The machine's state -/

/-- Everything that stays put during the sweep: the constants, and the arrays of the sorted
instance, and the lengths of the arrays the sweep writes. -/
structure Static (J : Instance) (INF W1 LTB LPC LFS LSLT LP2 : ℕ) (σ : Env) : Prop where
  n : σ.vars "n" = J.jobs
  n2 : σ.vars "n2" = 2 * J.jobs
  m : σ.vars "m" = J.machines
  cinf : σ.vars "cinf" = INF
  w1 : σ.vars "W1" = W1
  ps : σ.arrs "PS" = (List.range J.jobs).map (pv J)
  qs : σ.arrs "QS" = (List.range J.jobs).map (qv J)
  ds : σ.arrs "DS" = (List.range J.jobs).map (dv J)
  ws : σ.arrs "WS" = (List.range J.jobs).map (wv J)
  sa : σ.arrs "SA" = (dueOrder J).map Fin.val
  ltb : (σ.arrs "TB").length = LTB
  lpc : (σ.arrs "PC").length = LPC
  lfs : (σ.arrs "FS").length = LFS
  lslt : (σ.arrs "SLT").length = LSLT
  lp2 : (σ.arrs "P2").length = LP2

/-- The scalars `Static` speaks of. -/
def SV : List String := ["n", "n2", "m", "cinf", "W1"]
/-- The arrays `Static` speaks of, apart from lengths. -/
def SAr : List String := ["PS", "QS", "DS", "WS", "SA"]

theorem Static.of_run {J : Instance} {INF W1 LTB LPC LFS LSLT LP2 B : ℕ} {c : Com} {σ σ' : Env}
    {K : ℕ} (h : Static J INF W1 LTB LPC LFS LSLT LP2 σ) (hr : Run B c σ σ' K)
    (hv : ∀ y ∈ SV, y ∉ c.wvars) (ha : ∀ a ∈ SAr, a ∉ c.warrs) :
    Static J INF W1 LTB LPC LFS LSLT LP2 σ' := by
  have hl := Lax496464Proofs.Ram.Corollary1Prog.run_arrs_length_eq hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.frame_var "n" (hv "n" (by simp [SV]))]; exact h.n
  · rw [hr.frame_var "n2" (hv "n2" (by simp [SV]))]; exact h.n2
  · rw [hr.frame_var "m" (hv "m" (by simp [SV]))]; exact h.m
  · rw [hr.frame_var "cinf" (hv "cinf" (by simp [SV]))]; exact h.cinf
  · rw [hr.frame_var "W1" (hv "W1" (by simp [SV]))]; exact h.w1
  · rw [hr.frame_arr "PS" (ha "PS" (by simp [SAr]))]; exact h.ps
  · rw [hr.frame_arr "QS" (ha "QS" (by simp [SAr]))]; exact h.qs
  · rw [hr.frame_arr "DS" (ha "DS" (by simp [SAr]))]; exact h.ds
  · rw [hr.frame_arr "WS" (ha "WS" (by simp [SAr]))]; exact h.ws
  · rw [hr.frame_arr "SA" (ha "SA" (by simp [SAr]))]; exact h.sa
  · rw [hl]; exact h.ltb
  · rw [hl]; exact h.lpc
  · rw [hl]; exact h.lfs
  · rw [hl]; exact h.lslt
  · rw [hl]; exact h.lp2

/-- The part of the machine's state that follows the model's state `S` after `i` starts and
`k` dues. -/
structure Dyn (J : Instance) (INF W1 : ℕ) (S : St J) (i k : ℕ) (σ : Env) : Prop where
  ip : σ.vars "ip" = i
  kp : σ.vars "kp" = k
  nx : σ.vars "nx" = S.next
  fp : σ.vars "fp" = S.free.length
  mkK : σ.vars "MK" = 2 ^ S.next
  fs : S.free = ((σ.arrs "FS").take S.free.length).reverse
  slt : ∀ j : (scale J).Job, j.val < i → (σ.arrs "SLT").getD j 0 = S.sl j
  p2 : ∀ b < S.next, (σ.arrs "P2").getD b 0 = 2 ^ b
  pc : ∀ X < 2 ^ S.next, (σ.arrs "PC").getD X 0 = pcnt X
  tb : ∀ X < 2 ^ S.next, ∀ c < W1, tabOf W1 (σ.arrs "TB") X c = S.T X c
  tbLe : ∀ j, (σ.arrs "TB").getD j 0 ≤ INF

/-- The numeric side conditions of the sweep: sizes of the arrays, and that every value the
events produce stays below the bound `B`. -/
structure Nums (J : Instance) (wd W1 INF B LTB LPC LFS LSLT LP2 : ℕ) : Prop where
  hB : 1 < B
  hW1 : 0 < W1
  tbL : 2 ^ wd * W1 ≤ LTB
  pcL : 2 ^ wd ≤ LPC
  fsL : J.jobs ≤ LFS
  sltL : J.jobs ≤ LSLT
  p2L : wd ≤ LP2
  tbB : 2 ^ wd * W1 < B
  infB : INF < B
  nB : 2 * J.jobs + 5 < B
  mB : J.machines < B
  pq : ∀ j : J.Job, INF + J.p j + J.q j < B
  dB : ∀ j : J.Job, J.d j + 1 < B
  wB : ∀ j : J.Job, J.w j < B
  dq : ∀ a b : J.Job, J.d a + J.q b < B
  dINF : ∀ j : J.Job, J.d j ≤ INF
  infPos : 0 < INF

theorem Nums.pow_le {J : Instance} {wd W1 INF B LTB LPC LFS LSLT LP2 : ℕ}
    (h : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) {a : ℕ} (ha : a ≤ wd) : 2 ^ a ≤ 2 ^ wd * W1 :=
  le_trans (Nat.pow_le_pow_right (by norm_num) ha) (Nat.le_mul_of_pos_right _ h.hW1)

theorem Nums.pow_lt {J : Instance} {wd W1 INF B LTB LPC LFS LSLT LP2 : ℕ}
    (h : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) {a : ℕ} (ha : a ≤ wd) : 2 ^ a < B :=
  lt_of_le_of_lt (h.pow_le ha) h.tbB

theorem Nums.wd_lt {J : Instance} {wd W1 INF B LTB LPC LFS LSLT LP2 : ℕ}
    (h : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) : wd < B :=
  lt_of_le_of_lt (le_of_lt (Nat.lt_two_pow_self (n := wd))) (h.pow_lt le_rfl)

theorem dueT_congr {b M INF W1 : ℕ} (T1 T2 : ℕ → ℕ → ℕ) (hd : 2 * 2 ^ b ∣ M)
    (h : ∀ X < M, ∀ c < W1, T1 X c = T2 X c) {X c : ℕ} (hX : X < M) (hc : c < W1) :
    dueT b INF T1 X c = dueT b INF T2 X c := by
  unfold dueT
  by_cases hbit : X / 2 ^ b % 2 = 1
  · rw [if_pos hbit, if_pos hbit]
  · rw [if_neg hbit, if_neg hbit]
    have := lt_of_bit_clear (by positivity) hd hX hbit
    rw [h X hX c hc, h (X + 2 ^ b) this c hc]

theorem startT_congr {b w p q d m INF : ℕ} (T1 T2 : ℕ → ℕ → ℕ) {X c : ℕ}
    (h1 : X / 2 ^ b % 2 = 1 → T1 (X - 2 ^ b) (c - w) = T2 (X - 2 ^ b) (c - w))
    (h2 : ¬ X / 2 ^ b % 2 = 1 → T1 X c = T2 X c) :
    startT b w p q d m INF T1 X c = startT b w p q d m INF T2 X c := by
  unfold startT
  by_cases hbit : X / 2 ^ b % 2 = 1
  · rw [if_pos hbit, if_pos hbit, h1 hbit]
  · rw [if_neg hbit, if_neg hbit, h2 hbit]

theorem take_succ_set (FS : List ℕ) (f b : ℕ) (hf : f < FS.length) :
    (FS.set f b).take (f + 1) = FS.take f ++ [b] := by
  rw [List.take_add_one]
  have h1 : (FS.set f b).take f = FS.take f := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_set]
      have : i < f := by simp at h1; exact h1.1
      simp [Nat.ne_of_gt this]
  rw [h1]
  simp [hf]

theorem take_pop (FS : List ℕ) (f : ℕ) (hf : f + 1 ≤ FS.length) :
    (FS.take (f + 1)).reverse = FS[f] :: (FS.take f).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
  simp

set_option maxHeartbeats 4000000 in
/-- **A due event on the machine**: the model's `step` with the due of the next job in due order. -/
theorem dueEv_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (S : St J) (i k : ℕ) (hg : Good J S i k)
    (hnext : S.next ≤ wd) (hdue : k < (dueOrder J).length) (hyi : dueAt J k < i) :
    Spec B (fun σ => Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧ Dyn J INF W1 S i k σ) dueEv
      (fun _ σ' => Static J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        Dyn J INF W1 (step J INF S (Ev.due ((dueOrder J)[k]))) i (k + 1) σ')
      (44 * (2 ^ wd * W1) + 80) := by
  refine Spec.of_exists fun σ ⟨hSt, hDy⟩ => ?_
  set y : (scale J).Job := (dueOrder J)[k] with hydef
  have hyv : y.val = dueAt J k := (dueAt_eq k hdue).symm
  have hyi' : y.val < i := by rw [hyv]; exact hyi
  have hb : S.sl y < S.next := hg.sl y hyi'
  have hnJ : k < J.jobs := by rw [length_dueOrder] at hdue; exact hdue
  have hwdB := hN.wd_lt
  have hnB := hN.nB
  have hyJ : y.val < J.jobs := y.isLt
  have hSAk : (σ.arrs "SA").getD k 0 = y.val := by rw [hSt.sa, hyv]; rfl
  have hSLTy : (σ.arrs "SLT").getD y.val 0 = S.sl y := hDy.slt y hyi'
  have hP2b : (σ.arrs "P2").getD (S.sl y) 0 = 2 ^ (S.sl y) := hDy.p2 _ hb
  have hfree := hg.len
  have hbwd : S.sl y < wd := lt_of_lt_of_le hb hnext
  -- phase 1: the set-up
  obtain ⟨σ1, hr1, ⟨hj1, hb1, hb21⟩, hfv1, hfa1, -, -⟩ :=
    (dueSetup_spec (B := B) (σ.arrs "SA") (σ.arrs "SLT") (σ.arrs "P2") k
      (by rw [hSt.sa, List.length_map]; exact hdue) (by omega)
      (by rw [hSAk]; omega) (by rw [hSAk, hSt.lslt]; have := hN.sltL; omega)
      (by rw [hSAk, hSLTy]; omega) (by rw [hSAk, hSLTy, hSt.lp2]; have := hN.p2L; omega)
      (by rw [hSAk, hSLTy, hP2b]; exact hN.pow_lt (by omega))).frame.run ⟨rfl, rfl, rfl, hDy.kp⟩
  rw [hSAk, hSLTy, hP2b] at hb21
  rw [hSAk, hSLTy] at hb1
  have hTB1 : σ1.arrs "TB" = σ.arrs "TB" := hfa1 "TB" (by decide)
  -- phase 2: the due pass
  have hMKpos : 0 < 2 ^ S.next := by positivity
  have hdvd : 2 * 2 ^ (S.sl y) ∣ 2 ^ S.next := by
    rw [← pow_succ']; exact pow_dvd_pow 2 (by omega)
  have hNL : 2 ^ S.next * W1 ≤ (σ1.arrs "TB").length := by
    rw [hTB1, hSt.ltb]
    exact le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hnext)) hN.tbL
  have hNB : 2 ^ S.next * W1 < B := lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hnext)) hN.tbB
  obtain ⟨σ2, hr2, ⟨hl2, htab2, -, hle2, -⟩, hfv2, hfa2, -, -⟩ :=
    (dueLoop_table (B := B) (S.sl y) (2 ^ (S.sl y)) W1 (2 ^ S.next) INF (σ1.arrs "TB") rfl hN.hW1
      hMKpos hdvd hNL hNB hN.infB (by rw [hTB1]; exact hDy.tbLe)).frame.run
      ⟨hb21, by rw [hfv1 "W1" (by decide)]; exact hSt.w1,
       by rw [hfv1 "MK" (by decide)]; exact hDy.mkK,
       by rw [hfv1 "cinf" (by decide)]; exact hSt.cinf, rfl⟩
  have hTB2 : σ2.arrs "FS" = σ.arrs "FS" := by
    rw [hfa2 "FS" (by decide), hfa1 "FS" (by decide)]
  -- phase 3: the tail
  have hf2 : σ2.vars "fp" = S.free.length := by
    rw [hfv2 "fp" (by decide), hfv1 "fp" (by decide)]
    exact hDy.fp
  have hbb2 : σ2.vars "bb" = S.sl y := by
    rw [hfv2 "bb" (by decide)]; exact hb1
  have hkp2 : σ2.vars "kp" = k := by
    rw [hfv2 "kp" (by decide), hfv1 "kp" (by decide)]
    exact hDy.kp
  have hFSl : S.free.length < (σ2.arrs "FS").length := by
    rw [hfa2 "FS" (by decide), hfa1 "FS" (by decide), hSt.lfs]; have := hN.fsL; omega
  obtain ⟨σ3, hr3, ⟨hFS3, hfp3, hkp3⟩, hfv3, hfa3, -, -⟩ :=
    (dueTail_spec (B := B) hN.hB (σ2.arrs "FS") S.free.length (S.sl y) k hFSl (by omega)
      (by omega) (by omega)).frame.run ⟨rfl, hf2, hbb2, hkp2⟩
  have hrall : Run B dueEv σ σ3 _ := hr1.seq (hr2.seq hr3)
  have hS' : step J INF S (Ev.due y) = (St.mk (S.sl y :: S.free) S.next S.sl
      (dueT (S.sl y) INF S.T) : St J) := step_due INF S y
  refine ⟨σ3, _, hrall.mono ?_, le_rfl, Static.of_run hSt hrall (by decide) (by decide), ?_⟩
  · have := Nat.mul_le_mul_right W1 (le_refl (2 ^ wd))
    have h2 : 2 ^ S.next * W1 ≤ 2 ^ wd * W1 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hnext)
    omega
  · rw [hS']
    have hTB3 : σ3.arrs "TB" = σ2.arrs "TB" := hfa3 "TB" (by decide)
    have hvar : ∀ v, v ∉ dueEv.wvars → σ3.vars v = σ.vars v := fun v hv => hrall.frame_var v hv
    have harr : ∀ v, v ∉ dueEv.warrs → σ3.arrs v = σ.arrs v := fun v hv => hrall.frame_arr v hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ3.vars "ip" = i
      rw [hvar "ip" (by decide)]; exact hDy.ip
    · show σ3.vars "kp" = k + 1
      exact hkp3
    · show σ3.vars "nx" = S.next
      rw [hvar "nx" (by decide)]; exact hDy.nx
    · show σ3.vars "fp" = (S.sl y :: S.free).length
      rw [hfp3]; simp
    · show σ3.vars "MK" = 2 ^ S.next
      rw [hvar "MK" (by decide)]; exact hDy.mkK
    · show S.sl y :: S.free = ((σ3.arrs "FS").take (S.sl y :: S.free).length).reverse
      rw [hFS3, hTB2, List.length_cons, take_succ_set _ _ _ (by rw [← hTB2]; exact hFSl)]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [← hDy.fs]
    · intro j hj
      show (σ3.arrs "SLT").getD j 0 = S.sl j
      rw [harr "SLT" (by decide)]; exact hDy.slt j hj
    · intro b' hb'
      show (σ3.arrs "P2").getD b' 0 = 2 ^ b'
      rw [harr "P2" (by decide)]; exact hDy.p2 b' hb'
    · intro X hX
      show (σ3.arrs "PC").getD X 0 = pcnt X
      rw [harr "PC" (by decide)]; exact hDy.pc X hX
    · intro X hX c hc
      show tabOf W1 (σ3.arrs "TB") X c = dueT (S.sl y) INF S.T X c
      rw [hTB3, htab2 X hX c hc]
      refine dueT_congr (b := S.sl y) _ _ hdvd ?_ hX hc
      intro X' hX' c' hc'
      rw [hTB1]; exact hDy.tb X' hX' c' hc'
    · intro j
      show (σ3.arrs "TB").getD j 0 ≤ INF
      rw [hTB3]; exact hle2 j

/-! ## A start event -/

theorem getD_range_map (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- The recycled slot: pop the free stack. -/
def pickRecycle : Com :=
  .seq (.assign "fp" (.bin .sub (V "fp") (.lit 1)))
    (.seq (.assign "bb" (.get "FS" (V "fp"))) (.assign "b2" (.get "P2" (V "bb"))))

theorem pickRecycle_spec {B : ℕ} (hB : 1 < B) (FS P2 : List ℕ) (f : ℕ) (hfB : f < B)
    (hfL : f - 1 < FS.length) (hbB : FS.getD (f - 1) 0 < B)
    (hbL : FS.getD (f - 1) 0 < P2.length) (hpB : P2.getD (FS.getD (f - 1) 0) 0 < B) :
    Spec B (fun σ => σ.arrs "FS" = FS ∧ σ.arrs "P2" = P2 ∧ σ.vars "fp" = f) pickRecycle
      (fun _ σ' => σ'.vars "fp" = f - 1 ∧ σ'.vars "bb" = FS.getD (f - 1) 0 ∧
        σ'.vars "b2" = P2.getD (FS.getD (f - 1) 0) 0) 20 := by
  run_vcg
  vcg_fin

/-- The fresh slot: `bb := nx`, its bit `P2[nx] := MK`, the popcounts grown, `MK` doubled. -/
def pickFresh : Com :=
  .seq (.assign "bb" (V "nx"))
    (.seq (.store "P2" (V "bb") (V "MK"))
      (.seq (.assign "b2" (V "MK"))
        (.seq (.assign "nx" (.bin .add (V "nx") (.lit 1)))
          (.seq growPC (.assign "MK" (.bin .add (V "MK") (V "MK")))))))

theorem pickFresh_spec {B : ℕ} (hB : 1 < B) (P2 PC0 : List ℕ) (b : ℕ) (hb : b < P2.length)
    (hL : 2 * 2 ^ b ≤ PC0.length) (hMKB : 2 * 2 ^ b < B) (hbB : b + 1 < B)
    (hPC : ∀ j < 2 ^ b, PC0.getD j 0 = pcnt j) :
    Spec B (fun σ => σ.arrs "P2" = P2 ∧ σ.arrs "PC" = PC0 ∧ σ.vars "nx" = b ∧
        σ.vars "MK" = 2 ^ b) pickFresh
      (fun _ σ' => σ'.vars "bb" = b ∧ σ'.arrs "P2" = P2.set b (2 ^ b) ∧ σ'.vars "b2" = 2 ^ b ∧
        σ'.vars "nx" = b + 1 ∧ σ'.vars "MK" = 2 * 2 ^ b ∧
        (σ'.arrs "PC").length = PC0.length ∧
        (∀ j, j < 2 * 2 ^ b → (σ'.arrs "PC").getD j 0 = pcnt j)) (24 * 2 ^ b + 40) := by
  have hgrow := growPC_table (B := B) b (2 ^ b) PC0 rfl hL hMKB hPC
  run_vcg [hgrow]
  vcg_fin2

/-- Load the job's weight, preprocessing time, processing time and due date. -/
def setParams : Com :=
  .seq (.assign "sw" (.get "WS" (V "ip")))
    (.seq (.assign "sp" (.get "PS" (V "ip")))
      (.seq (.assign "sq" (.get "QS" (V "ip"))) (.assign "sd" (.get "DS" (V "ip")))))

/-- Record the slot of the started job, count the event. -/
def startTail : Com :=
  .seq (.store "SLT" (V "ip") (V "bb")) (.assign "ip" (.bin .add (V "ip") (.lit 1)))

/-- What every start event does once the slot `bb` (with `b2 = 2^bb`) and the mask count `MK`
are settled. -/
def startCommon : Com := .seq setParams (.seq startLoop startTail)

theorem startCommon_spec {B : ℕ} (hB : 1 < B) (b W1 M i w p q d m INF : ℕ)
    (WS PS QS DS SLT TB PC : List ℕ) (hW1 : 0 < W1) (hM : 0 < M) (hdvd : 2 * 2 ^ b ∣ M)
    (hNL : M * W1 ≤ TB.length) (hNB : M * W1 < B) (hINF : INF < B)
    (hle : ∀ j, TB.getD j 0 ≤ INF) (hpq : INF + p + q < B) (hd1 : d + 1 < B) (hw : w < B)
    (hm : m < B) (hPCL : M ≤ PC.length) (hPC : ∀ j < M, PC.getD j 0 = pcnt j)
    (hi1 : i < WS.length) (hi2 : i < PS.length) (hi3 : i < QS.length) (hi4 : i < DS.length)
    (hiS : i < SLT.length) (hiB : i + 1 < B) (hbB : b < B)
    (hwS : WS.getD i 0 = w) (hpS : PS.getD i 0 = p) (hqS : QS.getD i 0 = q)
    (hdS : DS.getD i 0 = d) :
    Spec B (fun σ => σ.arrs "WS" = WS ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧
        σ.arrs "DS" = DS ∧ σ.arrs "SLT" = SLT ∧ σ.arrs "TB" = TB ∧ σ.arrs "PC" = PC ∧
        σ.vars "ip" = i ∧ σ.vars "bb" = b ∧ σ.vars "b2" = 2 ^ b ∧ σ.vars "W1" = W1 ∧
        σ.vars "MK" = M ∧ σ.vars "cinf" = INF ∧ σ.vars "m" = m) startCommon
      (fun _ σ' => (σ'.arrs "TB").length = TB.length ∧
        (∀ X < M, ∀ c < W1, tabOf W1 (σ'.arrs "TB") X c =
          startT b w p q d m INF (tabOf W1 TB) X c) ∧
        (∀ j, M * W1 ≤ j → (σ'.arrs "TB").getD j 0 = TB.getD j 0) ∧
        (d ≤ INF → ∀ j, j < M * W1 → (σ'.arrs "TB").getD j 0 ≤ INF) ∧
        σ'.arrs "SLT" = SLT.set i b ∧ σ'.vars "ip" = i + 1) (84 * (M * W1) + 60) := by
  have hloop := startLoop_table (B := B) b (2 ^ b) W1 M w p q d m INF TB PC rfl hW1 hM hdvd hNL
    hNB hINF (fun j _ => hle j) hpq hd1 hw hm hPCL hPC
  run_vcg [hloop]
  vcg_fin2

theorem slt_update {J : Instance} (S : St J) (SLT : List ℕ) (i b : ℕ) (hi : i < (scale J).jobs)
    (hiS : i < SLT.length) (h : ∀ j : (scale J).Job, j.val < i → SLT.getD j 0 = S.sl j) :
    ∀ j : (scale J).Job, j.val < i + 1 →
      (SLT.set i b).getD j 0 = Function.update S.sl ⟨i, hi⟩ b j := by
  intro j hj
  by_cases hji : j = ⟨i, hi⟩
  · subst hji
    rw [Function.update_self]
    exact getD_set_self _ _ _ hiS
  · have hne : j.val ≠ i := fun h' => hji (Fin.ext h')
    rw [Function.update_of_ne hji, getD_set_ne _ _ _ _ hne]
    exact h j (by omega)

theorem tb_start {W1 b w p q d m INF M0 M : ℕ} (TB0 : List ℕ) (T : ℕ → ℕ → ℕ)
    (hagree : ∀ X < M0, ∀ c < W1, tabOf W1 TB0 X c = T X c)
    (hreach : ∀ X < M, (X / 2 ^ b % 2 = 1 → X - 2 ^ b < M0) ∧ (¬ X / 2 ^ b % 2 = 1 → X < M0)) :
    ∀ X < M, ∀ c < W1,
      startT b w p q d m INF (tabOf W1 TB0) X c = startT b w p q d m INF T X c := by
  intro X hX c hc
  refine startT_congr _ _ (fun hbit => ?_) (fun hbit => ?_)
  · exact hagree _ ((hreach X hX).1 hbit) _ (by omega)
  · exact hagree _ ((hreach X hX).2 hbit) _ hc

set_option maxHeartbeats 4000000 in
/-- **A start event, on a recycled slot.** -/
theorem startRec_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (S : St J) (i k : ℕ) (hg : Good J S i k)
    (hnext : S.next ≤ wd) (hk : k ≤ J.jobs) (hi : i < (scale J).jobs) (b : ℕ) (r : List ℕ)
    (hf : S.free = b :: r) :
    Spec B (fun σ => Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧ Dyn J INF W1 S i k σ)
      (.seq pickRecycle startCommon)
      (fun _ σ' => Static J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        Dyn J INF W1 (step J INF S (Ev.start ⟨i, hi⟩)) (i + 1) k σ')
      (84 * (2 ^ wd * W1) + 80) := by
  refine Spec.of_exists fun σ ⟨hSt, hDy⟩ => ?_
  have hiJ : i < J.jobs := hi
  set y : (scale J).Job := ⟨i, hi⟩ with hydef
  have hwdB := hN.wd_lt
  have hnB := hN.nB
  have hfree := hg.len
  have hbn : b < S.next := hg.free b (by simp [hf])
  have hrl : r.length + 1 = S.free.length := by rw [hf]; simp
  -- the stack
  have hFS := hDy.fs
  rw [hf, List.length_cons, take_pop _ _ (by rw [hSt.lfs]; have := hN.fsL; omega)] at hFS
  obtain ⟨hFSb, hFSr⟩ := List.cons.inj hFS
  have hFSb' : (σ.arrs "FS").getD r.length 0 = b := by
    rw [List.getD_eq_getElem _ _ (by rw [hSt.lfs]; have := hN.fsL; omega)]; exact hFSb.symm
  have hfp : σ.vars "fp" = r.length + 1 := by rw [hDy.fp, hf]; simp
  have hP2b : (σ.arrs "P2").getD b 0 = 2 ^ b := hDy.p2 b hbn
  -- phase 1
  obtain ⟨σ1, hr1, ⟨hfp1, hbb1, hb21⟩, hfv1, hfa1, -, -⟩ :=
    (pickRecycle_spec (B := B) hN.hB (σ.arrs "FS") (σ.arrs "P2") (r.length + 1)
      (by omega) (by rw [hSt.lfs]; have := hN.fsL; omega)
      (by simp only [Nat.add_sub_cancel]; rw [hFSb']; omega)
      (by simp only [Nat.add_sub_cancel]; rw [hFSb', hSt.lp2]; have := hN.p2L; omega)
      (by simp only [Nat.add_sub_cancel]; rw [hFSb', hP2b]; exact hN.pow_lt (by omega))).frame.run
      ⟨rfl, rfl, hfp⟩
  simp only [Nat.add_sub_cancel] at hfp1 hbb1 hb21
  rw [hFSb'] at hbb1 hb21
  rw [hP2b] at hb21
  have hTB1 : σ1.arrs "TB" = σ.arrs "TB" := hfa1 "TB" (by decide)
  -- phase 2
  have hMpos : 0 < 2 ^ S.next := by positivity
  have hdvd : 2 * 2 ^ b ∣ 2 ^ S.next := by
    rw [← pow_succ']; exact pow_dvd_pow 2 (by omega)
  have hMW : 2 ^ S.next * W1 ≤ 2 ^ wd * W1 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hnext)
  have hNL : 2 ^ S.next * W1 ≤ (σ.arrs "TB").length := by
    rw [hSt.ltb]; exact le_trans hMW hN.tbL
  have hNB : 2 ^ S.next * W1 < B := lt_of_le_of_lt hMW hN.tbB
  have hnJ : i < J.jobs := hiJ
  have hlenW : (σ.arrs "WS").length = J.jobs := by rw [hSt.ws]; simp
  have hlenP : (σ.arrs "PS").length = J.jobs := by rw [hSt.ps]; simp
  have hlenQ : (σ.arrs "QS").length = J.jobs := by rw [hSt.qs]; simp
  have hlenD : (σ.arrs "DS").length = J.jobs := by rw [hSt.ds]; simp
  have hwS : (σ.arrs "WS").getD i 0 = J.w y := by
    rw [hSt.ws, getD_range_map _ _ _ hnJ]; simp [wv, hnJ, hydef]
  have hpS : (σ.arrs "PS").getD i 0 = J.p y := by
    rw [hSt.ps, getD_range_map _ _ _ hnJ]; simp [pv, hnJ, hydef]
  have hqS : (σ.arrs "QS").getD i 0 = J.q y := by
    rw [hSt.qs, getD_range_map _ _ _ hnJ]; simp [qv, hnJ, hydef]
  have hdS : (σ.arrs "DS").getD i 0 = J.d y := by
    rw [hSt.ds, getD_range_map _ _ _ hnJ]; simp [dv, hnJ, hydef]
  obtain ⟨σ2, hr2, ⟨hl2, htab2, hbey2, hle2, hSLT2, hip2⟩, hfv2, hfa2, -, -⟩ :=
    (startCommon_spec (B := B) hN.hB b W1 (2 ^ S.next) i (J.w y) (J.p y) (J.q y) (J.d y)
      J.machines INF (σ.arrs "WS") (σ.arrs "PS") (σ.arrs "QS") (σ.arrs "DS") (σ.arrs "SLT")
      (σ.arrs "TB") (σ.arrs "PC") hN.hW1 hMpos hdvd hNL hNB hN.infB
      (fun j => hDy.tbLe j) (hN.pq y) (hN.dB y) (hN.wB y) hN.mB
      (by rw [hSt.lpc]; have := hN.pcL; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hnext
          omega)
      (fun j hj => hDy.pc j hj) (by omega) (by omega) (by omega) (by omega)
      (by rw [hSt.lslt]; have := hN.sltL; omega) (by omega) (by omega) hwS hpS hqS hdS).frame.run
      ⟨by rw [hfa1 "WS" (by decide)], by rw [hfa1 "PS" (by decide)],
       by rw [hfa1 "QS" (by decide)], by rw [hfa1 "DS" (by decide)],
       by rw [hfa1 "SLT" (by decide)], hTB1, by rw [hfa1 "PC" (by decide)],
       by rw [hfv1 "ip" (by decide)]; exact hDy.ip, hbb1, hb21,
       by rw [hfv1 "W1" (by decide)]; exact hSt.w1,
       by rw [hfv1 "MK" (by decide)]; exact hDy.mkK,
       by rw [hfv1 "cinf" (by decide)]; exact hSt.cinf,
       by rw [hfv1 "m" (by decide)]; exact hSt.m⟩
  have hrall : Run B (.seq pickRecycle startCommon) σ σ2 _ := hr1.seq hr2
  refine ⟨σ2, _, hrall.mono ?_, le_rfl, Static.of_run hSt hrall (by decide) (by decide), ?_⟩
  · omega
  · rw [step_start_cons INF S y b r hf]
    have hvar : ∀ v, v ∉ (Com.seq pickRecycle startCommon).wvars → σ2.vars v = σ.vars v :=
      fun v hv => hrall.frame_var v hv
    have harr : ∀ v, v ∉ (Com.seq pickRecycle startCommon).warrs → σ2.arrs v = σ.arrs v :=
      fun v hv => hrall.frame_arr v hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hip2
    · show σ2.vars "kp" = k
      rw [hvar "kp" (by decide)]; exact hDy.kp
    · show σ2.vars "nx" = S.next
      rw [hvar "nx" (by decide)]; exact hDy.nx
    · show σ2.vars "fp" = r.length
      rw [hfv2 "fp" (by decide), hfp1]
    · show σ2.vars "MK" = 2 ^ S.next
      rw [hvar "MK" (by decide)]; exact hDy.mkK
    · show r = ((σ2.arrs "FS").take r.length).reverse
      rw [harr "FS" (by decide)]; exact hFSr
    · rw [hSLT2]
      exact slt_update S (σ.arrs "SLT") i b hi (by rw [hSt.lslt]; have := hN.sltL; omega)
        (fun j hj => hDy.slt j hj)
    · intro b' hb'
      show (σ2.arrs "P2").getD b' 0 = 2 ^ b'
      rw [harr "P2" (by decide)]; exact hDy.p2 b' hb'
    · intro X hX
      show (σ2.arrs "PC").getD X 0 = pcnt X
      rw [harr "PC" (by decide)]; exact hDy.pc X hX
    · intro X hX c hc
      show tabOf W1 (σ2.arrs "TB") X c = startT b (J.w y) (J.p y) (J.q y) (J.d y) J.machines INF S.T X c
      rw [htab2 X hX c hc]
      refine tb_start (M0 := 2 ^ S.next) (M := 2 ^ S.next) _ S.T
        (fun X' hX' c' hc' => hDy.tb X' hX' c' hc') ?_ X hX c hc
      intro X' hX'
      exact ⟨fun _ => by have := Nat.two_pow_pos b; omega,
        fun _ => hX'⟩
    · intro j
      show (σ2.arrs "TB").getD j 0 ≤ INF
      by_cases hj : j < 2 ^ S.next * W1
      · exact hle2 (hN.dINF y) j hj
      · rw [hbey2 j (by omega)]; exact hDy.tbLe j

theorem reach_fresh (b : ℕ) : ∀ X < 2 * 2 ^ b,
    (X / 2 ^ b % 2 = 1 → X - 2 ^ b < 2 ^ b) ∧ (¬ X / 2 ^ b % 2 = 1 → X < 2 ^ b) := by
  intro X hX
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  refine ⟨fun _ => by omega, fun hbit => ?_⟩
  have h1 : X / 2 ^ b < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
  exact Nat.lt_of_not_le fun h => by have := Nat.div_pos h hP; omega

set_option maxHeartbeats 4000000 in
/-- **A start event, on a fresh slot.** -/
theorem startFresh_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (S : St J) (i k : ℕ) (_hg : Good J S i k)
    (hnext : S.next + 1 ≤ wd) (_hk : k ≤ J.jobs) (hi : i < (scale J).jobs)
    (hf : S.free = []) :
    Spec B (fun σ => Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧ Dyn J INF W1 S i k σ)
      (.seq pickFresh startCommon)
      (fun _ σ' => Static J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        Dyn J INF W1 (step J INF S (Ev.start ⟨i, hi⟩)) (i + 1) k σ')
      (108 * (2 ^ wd * W1) + 120) := by
  refine Spec.of_exists fun σ ⟨hSt, hDy⟩ => ?_
  have hiJ : i < J.jobs := hi
  set y : (scale J).Job := ⟨i, hi⟩ with hydef
  have hwdB := hN.wd_lt
  have hnB := hN.nB
  have hfp : σ.vars "fp" = 0 := by rw [hDy.fp, hf]; rfl
  set b := S.next with hbdef
  have h2b : 2 * 2 ^ b = 2 ^ (b + 1) := by rw [pow_succ]; ring
  have hMpow : 2 ^ (b + 1) ≤ 2 ^ wd := Nat.pow_le_pow_right (by norm_num) hnext
  have hMW : 2 ^ (b + 1) * W1 ≤ 2 ^ wd * W1 := Nat.mul_le_mul_right _ hMpow
  have hbwd : b + 1 < B := by omega
  -- phase 1
  obtain ⟨σ1, hr1, ⟨hbb1, hP21, hb21, hnx1, hMK1, hPCl1, hPC1⟩, hfv1, hfa1, -, -⟩ :=
    (pickFresh_spec (B := B) hN.hB (σ.arrs "P2") (σ.arrs "PC") b
      (by rw [hSt.lp2]; have := hN.p2L; omega)
      (by rw [hSt.lpc, h2b]; have := hN.pcL; omega)
      (by rw [h2b]; exact hN.pow_lt hnext) hbwd
      (fun j hj => hDy.pc j hj)).frame.run ⟨rfl, rfl, hDy.nx, hDy.mkK⟩
  have hTB1 : σ1.arrs "TB" = σ.arrs "TB" := hfa1 "TB" (by decide)
  -- phase 2
  have hMpos : 0 < 2 * 2 ^ b := by have := Nat.two_pow_pos b; omega
  have hNL : 2 * 2 ^ b * W1 ≤ (σ.arrs "TB").length := by
    rw [hSt.ltb, h2b]; exact le_trans hMW hN.tbL
  have hNB : 2 * 2 ^ b * W1 < B := by rw [h2b]; exact lt_of_le_of_lt hMW hN.tbB
  have hlenW : (σ.arrs "WS").length = J.jobs := by rw [hSt.ws]; simp
  have hlenP : (σ.arrs "PS").length = J.jobs := by rw [hSt.ps]; simp
  have hlenQ : (σ.arrs "QS").length = J.jobs := by rw [hSt.qs]; simp
  have hlenD : (σ.arrs "DS").length = J.jobs := by rw [hSt.ds]; simp
  have hwS : (σ.arrs "WS").getD i 0 = J.w y := by
    rw [hSt.ws, getD_range_map _ _ _ hiJ]; simp [wv, hiJ, hydef]
  have hpS : (σ.arrs "PS").getD i 0 = J.p y := by
    rw [hSt.ps, getD_range_map _ _ _ hiJ]; simp [pv, hiJ, hydef]
  have hqS : (σ.arrs "QS").getD i 0 = J.q y := by
    rw [hSt.qs, getD_range_map _ _ _ hiJ]; simp [qv, hiJ, hydef]
  have hdS : (σ.arrs "DS").getD i 0 = J.d y := by
    rw [hSt.ds, getD_range_map _ _ _ hiJ]; simp [dv, hiJ, hydef]
  obtain ⟨σ2, hr2, ⟨hl2, htab2, hbey2, hle2, hSLT2, hip2⟩, hfv2, hfa2, -, -⟩ :=
    (startCommon_spec (B := B) hN.hB b W1 (2 * 2 ^ b) i (J.w y) (J.p y) (J.q y) (J.d y)
      J.machines INF (σ.arrs "WS") (σ.arrs "PS") (σ.arrs "QS") (σ.arrs "DS") (σ.arrs "SLT")
      (σ.arrs "TB") (σ1.arrs "PC") hN.hW1 hMpos dvd_rfl hNL hNB hN.infB
      (fun j => hDy.tbLe j) (hN.pq y) (hN.dB y) (hN.wB y) hN.mB
      (by rw [hPCl1, hSt.lpc, h2b]; have := hN.pcL; omega)
      (fun j hj => hPC1 j hj) (by omega) (by omega) (by omega) (by omega)
      (by rw [hSt.lslt]; have := hN.sltL; omega) (by omega) (by omega) hwS hpS hqS hdS).frame.run
      ⟨by rw [hfa1 "WS" (by decide)], by rw [hfa1 "PS" (by decide)],
       by rw [hfa1 "QS" (by decide)], by rw [hfa1 "DS" (by decide)],
       by rw [hfa1 "SLT" (by decide)], hTB1, rfl,
       by rw [hfv1 "ip" (by decide)]; exact hDy.ip, hbb1, hb21,
       by rw [hfv1 "W1" (by decide)]; exact hSt.w1, hMK1,
       by rw [hfv1 "cinf" (by decide)]; exact hSt.cinf,
       by rw [hfv1 "m" (by decide)]; exact hSt.m⟩
  have hrall : Run B (.seq pickFresh startCommon) σ σ2 _ := hr1.seq hr2
  refine ⟨σ2, _, hrall.mono ?_, le_rfl, Static.of_run hSt hrall (by decide) (by decide), ?_⟩
  · have := Nat.two_pow_pos b
    have h3 : 24 * 2 ^ b ≤ 24 * (2 ^ wd * W1) := by
      have := hN.hW1
      have : 2 ^ b ≤ 2 ^ wd * W1 := hN.pow_le (by omega)
      omega
    rw [h2b] at *
    omega
  · rw [step_start_nil INF S y hf]
    have hvar : ∀ v, v ∉ (Com.seq pickFresh startCommon).wvars → σ2.vars v = σ.vars v :=
      fun v hv => hrall.frame_var v hv
    have harr : ∀ v, v ∉ (Com.seq pickFresh startCommon).warrs → σ2.arrs v = σ.arrs v :=
      fun v hv => hrall.frame_arr v hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hip2
    · show σ2.vars "kp" = k
      rw [hvar "kp" (by decide)]; exact hDy.kp
    · show σ2.vars "nx" = b + 1
      rw [hfv2 "nx" (by decide)]; exact hnx1
    · show σ2.vars "fp" = ([] : List ℕ).length
      rw [hvar "fp" (by decide)]; exact hfp
    · show σ2.vars "MK" = 2 ^ (b + 1)
      rw [hfv2 "MK" (by decide), hMK1, h2b]
    · show ([] : List ℕ) = ((σ2.arrs "FS").take ([] : List ℕ).length).reverse
      simp
    · rw [hSLT2]
      exact slt_update S (σ.arrs "SLT") i b hi (by rw [hSt.lslt]; have := hN.sltL; omega)
        (fun j hj => hDy.slt j hj)
    · intro b' hb'
      show (σ2.arrs "P2").getD b' 0 = 2 ^ b'
      rw [hfa2 "P2" (by decide), hP21]
      by_cases hbb : b' = b
      · subst hbb
        exact getD_set_self _ _ _ (by rw [hSt.lp2]; have := hN.p2L; omega)
      · rw [getD_set_ne _ _ _ _ hbb]
        exact hDy.p2 b' (by have h : b' < b + 1 := hb'; omega)
    · intro X hX
      show (σ2.arrs "PC").getD X 0 = pcnt X
      rw [hfa2 "PC" (by decide)]
      exact hPC1 X (by have h : X < 2 ^ (b + 1) := hX; omega)
    · intro X hX c hc
      show tabOf W1 (σ2.arrs "TB") X c = startT b (J.w y) (J.p y) (J.q y) (J.d y) J.machines INF S.T X c
      have hX2 : X < 2 * 2 ^ b := by have h : X < 2 ^ (b + 1) := hX; omega
      rw [htab2 X hX2 c hc]
      exact tb_start (M0 := 2 ^ b) (M := 2 * 2 ^ b) _ S.T
        (fun X' hX' c' hc' => hDy.tb X' hX' c' hc') (reach_fresh b) X hX2 c hc
    · intro j
      show (σ2.arrs "TB").getD j 0 ≤ INF
      by_cases hj : j < 2 * 2 ^ b * W1
      · exact hle2 (hN.dINF y) j hj
      · rw [hbey2 j (by omega)]; exact hDy.tbLe j

theorem cond_fp_true {B : ℕ} {σ : Env}
    (h : (Cond.lt (.lit 0) (V "fp")).evalB B σ = some true) : 0 < σ.vars "fp" := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem cond_fp_false {B : ℕ} {σ : Env}
    (h : (Cond.lt (.lit 0) (V "fp")).evalB B σ = some false) : σ.vars "fp" = 0 := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  have := hr.symm
  simp only [decide_eq_false_iff_not, not_lt] at this
  omega

/-- **A start event**: recycle the top of the free stack if there is one, else take a fresh slot. -/
def startEv : Com :=
  .ite (.lt (.lit 0) (V "fp")) (.seq pickRecycle startCommon) (.seq pickFresh startCommon)

/-- **A start event on the machine**: the model's `step` with the start of job `i`. -/
theorem startEv_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (S : St J) (i k : ℕ) (hg : Good J S i k)
    (hk : k ≤ J.jobs) (hi : i < (scale J).jobs)
    (hnext : (step J INF S (Ev.start ⟨i, hi⟩)).next ≤ wd) :
    Spec B (fun σ => Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧ Dyn J INF W1 S i k σ) startEv
      (fun _ σ' => Static J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        Dyn J INF W1 (step J INF S (Ev.start ⟨i, hi⟩)) (i + 1) k σ')
      (108 * (2 ^ wd * W1) + 130) := by
  have hnB := hN.nB
  have hdef : ∀ σ : Env, (Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧ Dyn J INF W1 S i k σ) →
      ∃ v, (Cond.lt (.lit 0) (V "fp")).evalB B σ = some v := by
    intro σ ⟨hSt, hDy⟩
    have hf : σ.vars "fp" < B := by rw [hDy.fp]; have := hg.len; omega
    exact evalB_condLt_isSome (evalB_lit (by have := hN.hB; omega)) (evalB_var hf) |>.imp
      fun v hv => hv.1
  have hcost : 1 + (Cond.lt (.lit 0) (V "fp")).size + (108 * (2 ^ wd * W1) + 120)
      ≤ 108 * (2 ^ wd * W1) + 130 := by simp [Cond.size, Expr.size]; omega
  refine (Spec.ite (K := 108 * (2 ^ wd * W1) + 120) hdef ?_ ?_).mono hcost
  · cases hfr : S.free with
    | nil =>
      intro σ ⟨⟨hSt, hDy⟩, hc⟩
      have := cond_fp_true hc
      rw [hDy.fp, hfr] at this
      simp at this
    | cons b r =>
      refine (startRec_spec hN S i k hg (by rw [step_start_cons INF S _ b r hfr] at hnext; exact hnext) hk hi b r hfr).mono ?_ |>.pre ?_
      · omega
      · exact fun σ h => h.1
  · cases hfr : S.free with
    | nil =>
      refine (startFresh_spec hN S i k hg (by rw [step_start_nil INF S _ hfr] at hnext; exact hnext) hk hi hfr).pre ?_
      exact fun σ h => h.1
    | cons b r =>
      intro σ ⟨⟨hSt, hDy⟩, hc⟩
      have := cond_fp_false hc
      rw [hDy.fp, hfr] at this
      simp at this

/-! ## One turn of the loop -/

/-- The scalars `Dyn` speaks of. -/
def DV : List String := ["ip", "kp", "nx", "fp", "MK"]
/-- The arrays `Dyn` speaks of. -/
def DA : List String := ["FS", "SLT", "P2", "PC", "TB"]

theorem Dyn.of_run {J : Instance} {INF W1 B : ℕ} {S : St J} {i k : ℕ} {c : Com} {σ σ' : Env}
    {K : ℕ} (h : Dyn J INF W1 S i k σ) (hr : Run B c σ σ' K) (hv : ∀ y ∈ DV, y ∉ c.wvars)
    (ha : ∀ a ∈ DA, a ∉ c.warrs) : Dyn J INF W1 S i k σ' := by
  have hV : ∀ y ∈ DV, σ'.vars y = σ.vars y := fun y hy => hr.frame_var y (hv y hy)
  have hA : ∀ a ∈ DA, σ'.arrs a = σ.arrs a := fun a hy => hr.frame_arr a (ha a hy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV "ip" (by simp [DV])]; exact h.ip
  · rw [hV "kp" (by simp [DV])]; exact h.kp
  · rw [hV "nx" (by simp [DV])]; exact h.nx
  · rw [hV "fp" (by simp [DV])]; exact h.fp
  · rw [hV "MK" (by simp [DV])]; exact h.mkK
  · rw [hA "FS" (by simp [DA])]; exact h.fs
  · rw [hA "SLT" (by simp [DA])]; exact h.slt
  · rw [hA "P2" (by simp [DA])]; exact h.p2
  · rw [hA "PC" (by simp [DA])]; exact h.pc
  · rw [hA "TB" (by simp [DA])]; exact h.tb
  · rw [hA "TB" (by simp [DA])]; exact h.tbLe

/-- The sweep loop's invariant. -/
def Mach (J : Instance) (INF W1 LTB LPC LFS LSLT LP2 : ℕ) (σ : Env) : Prop :=
  ∃ i k pre, Pos J i k pre ∧ Static J INF W1 LTB LPC LFS LSLT LP2 σ ∧
    Dyn J INF W1 (tab J INF pre) i k σ

theorem getD_dv (J : Instance) (j : ℕ) : ((List.range J.jobs).map (dv J)).getD j 0 = dv J j := by
  by_cases hj : j < J.jobs
  · exact getD_range_map _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [dv, hj]

theorem getD_qv (J : Instance) (j : ℕ) : ((List.range J.jobs).map (qv J)).getD j 0 = qv J j := by
  by_cases hj : j < J.jobs
  · exact getD_range_map _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [qv, hj]

/-- One turn of the loop. -/
def stepBody : Com :=
  .seq decideCom (.ite (.eq (V "ist") (.lit 1)) startEv dueEv)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **One turn of the sweep loop**: the machine moves from the model's state after `pre` to its
state after `pre` and the next event. -/
theorem body_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (hE : EstOrdered J)
    (hq : ∀ i : J.Job, 0 < J.q i) (hwd : widthJ J ≤ wd) :
    Spec B (fun σ => Mach J INF W1 LTB LPC LFS LSLT LP2 σ ∧
        σ.vars "ip" + σ.vars "kp" < 2 * J.jobs) stepBody
      (fun σ σ' => Mach J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        σ'.vars "ip" + σ'.vars "kp" = σ.vars "ip" + σ.vars "kp" + 1)
      (108 * (2 ^ wd * W1) + 300) := by
  refine Spec.of_exists fun σ ⟨⟨i, k, pre, hpos, hSt, hDy⟩, hlt⟩ => ?_
  obtain ⟨hev, hin, hkn⟩ := pos_evs hpos
  have hnB := hN.nB
  have hlt' : i + k < 2 * J.jobs := by rw [hDy.ip, hDy.kp] at hlt; exact hlt
  have hg := pos_good hE hq INF hpos
  have hnextF : (tab J INF (evs J)).next ≤ wd :=
    le_trans (sweep_next_le hE hq hN.dINF hN.infPos) hwd
  have hnextS : (tab J INF pre).next ≤ wd := le_trans (pos_next_le INF hpos) hnextF
  have hdsl : (σ.arrs "DS").length = J.jobs := by rw [hSt.ds]; simp
  have hqsl : (σ.arrs "QS").length = J.jobs := by rw [hSt.qs]; simp
  have hsal : (σ.arrs "SA").length = J.jobs := by
    rw [hSt.sa, List.length_map, length_dueOrder]
  have hsaN : ∀ t < J.jobs, (σ.arrs "SA").getD t 0 < J.jobs := by
    intro t ht
    have ht' : t < (dueOrder J).length := by rw [length_dueOrder]; exact ht
    rw [hSt.sa]
    show dueAt J t < J.jobs
    rw [dueAt_eq t ht']; exact ((dueOrder J)[t]).isLt
  have hdsB : ∀ v ∈ σ.arrs "DS", v < B := by
    intro v hv
    rw [hSt.ds] at hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    have hj' : j < J.jobs := List.mem_range.mp hj
    have := hN.dB ⟨j, hj'⟩
    simp only [dv, hj', dif_pos]; omega
  have hsum : ∀ a b, a < J.jobs → b < J.jobs →
      (σ.arrs "DS").getD a 0 + (σ.arrs "QS").getD b 0 < B := by
    intro a b ha hb
    rw [hSt.ds, hSt.qs, getD_dv, getD_qv]
    have := hN.dq ⟨a, ha⟩ ⟨b, hb⟩
    simp only [dv, qv, ha, hb, dif_pos]; exact this
  obtain ⟨σ1, hr1, hist, hfv1, hfa1, -, -⟩ :=
    (decideCom_spec (B := B) hN.hB (σ.arrs "DS") (σ.arrs "QS") (σ.arrs "SA") J.jobs i k hdsl
      hqsl hsal hsaN hdsB hsum (by omega) (by omega) (by omega)).frame.run
      ⟨rfl, rfl, rfl, hSt.n, hDy.ip, hDy.kp⟩
  have hspIff : (i < J.jobs ∧ (J.jobs ≤ k ∨
      (σ.arrs "DS").getD i 0 < (σ.arrs "DS").getD ((σ.arrs "SA").getD k 0) 0 +
        (σ.arrs "QS").getD i 0 ∨
      ((σ.arrs "DS").getD i 0 = (σ.arrs "DS").getD ((σ.arrs "SA").getD k 0) 0 +
        (σ.arrs "QS").getD i 0 ∧ i < (σ.arrs "SA").getD k 0))) ↔ spOf J i k := by
    unfold spOf
    rw [hSt.ds, hSt.qs, hSt.sa, getD_dv, getD_dv, getD_qv]
    rfl
  replace hist : σ1.vars "ist" = if spOf J i k then 1 else 0 := by
    rw [hist]; exact if_congr hspIff rfl rfl
  have hSt1 : Static J INF W1 LTB LPC LFS LSLT LP2 σ1 :=
    Static.of_run hSt hr1 (by decide) (by decide)
  have hDy1 : Dyn J INF W1 (tab J INF pre) i k σ1 :=
    Dyn.of_run hDy hr1 (by decide) (by decide)
  have hB1 := hN.hB
  by_cases hsp : spOf J i k
  · -- a start
    rw [if_pos hsp] at hist
    have hi' : i < (scale J).jobs := by have := hsp.1; simpa using this
    have hpos' := Pos.start hpos hsp hi'
    have hnext' : (step J INF (tab J INF pre) (Ev.start ⟨i, hi'⟩)).next ≤ wd := by
      have := pos_next_le INF hpos'
      rw [tab_append] at this
      exact le_trans this hnextF
    have hc : (Cond.eq (V "ist") (.lit 1)).evalB B σ1 = some true := by
      rw [evalB_condEq (evalB_var (by rw [hist]; omega)) (evalB_lit hB1)]
      simp [hist]
    obtain ⟨σ2, hr2, hSt2, hDy2⟩ :=
      (startEv_spec hN (tab J INF pre) i k hg hkn hi' hnext').run ⟨hSt1, hDy1⟩
    refine ⟨σ2, _, (hr1.seq (Run.ite_true hc hr2)).mono ?_, le_rfl, ⟨i + 1, k, _, hpos', hSt2, ?_⟩, ?_⟩
    · simp [Cond.size, Expr.size]; omega
    · rw [tab_append]; exact hDy2
    · rw [hDy2.ip, hDy2.kp, hDy.ip, hDy.kp]; omega
  · -- a due
    rw [if_neg hsp] at hist
    have hk' : k < (dueOrder J).length := by
      rw [length_dueOrder]
      by_contra hcon
      by_cases hin' : i < J.jobs
      · exact hsp ⟨hin', Or.inl (by omega)⟩
      · omega
    have hyi : dueAt J k < i := by
      rw [dueAt_eq k hk']; exact due_started hE hq hin hsp hk'
    have hpos' := Pos.due hpos hsp hk'
    have hc : (Cond.eq (V "ist") (.lit 1)).evalB B σ1 = some false := by
      rw [evalB_condEq (evalB_var (by rw [hist]; omega)) (evalB_lit hB1)]
      simp [hist]
    obtain ⟨σ2, hr2, hSt2, hDy2⟩ :=
      (dueEv_spec hN (tab J INF pre) i k hg hnextS hk' hyi).run ⟨hSt1, hDy1⟩
    refine ⟨σ2, _, (hr1.seq (Run.ite_false hc hr2)).mono ?_, le_rfl, ⟨i, k + 1, _, hpos', hSt2, ?_⟩, ?_⟩
    · simp [Cond.size, Expr.size]; omega
    · rw [tab_append]; exact hDy2
    · rw [hDy2.ip, hDy2.kp, hDy.ip, hDy.kp]; omega

end Lax496464Proofs.Ram.W3SweepEv
