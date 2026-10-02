import Lax496464Proofs.Ram.D4Step
import Lax496464Proofs.Ram.D4Sum
import Lax496464Proofs.Ram.D2Core

/-!
# Corollary 2's Machine: the Core (Dual Table)

`core4` takes the sorted arrays `PS QS DS WS` and the scalars `n m W` (as `sortSetup3` leaves them),
sums `PS` into `R = P`, sets the block width `R + 1`, and fills the table.  `core4_spec` describes
its final state: the table is `DInv … 0` (right on every good cell), `zk` is the number of the first
`m` indices, `"R" = P + 1`, `"W" = W`.
-/

namespace Lax496464Proofs.Ram.D4Core

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.D2Step (turnCost blockCost loopWork)
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch
open Lax496464Proofs.Ram.D2Core (PSL QSL DSL WSL getD_map_range fails_mono setupCost
  pwSetup_wvars pwSetup_warrs nxLoop_wvars nxLoop_warrs code0Loop_wvars code0Loop_warrs
  validOK_init firstM_eq sl_range)
open Lax496464Proofs.Ram.D4Step Lax496464Proofs.Ram.D4Tab Lax496464Proofs.Ram.D4Sum
open Lax496464Proofs.Ram.Nxt1 (Fails Res res_isNxt)
open Lax496464.DynamicProgram (firstM)
open Lax496464Proofs.Ram.Dp1 (IsNxt pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)
open Lax496464Proofs.Ram.ListUtil

/-- What `core4` needs to know about the sorted instance and the word bound. -/
structure CI4 (J : Instance) (B n m W R : ℕ) : Prop where
  hB : 2 < B
  hn : J.jobs = n
  hmach : J.machines = m
  hn1 : 1 ≤ n
  hm : 1 ≤ m
  hest : EstOrdered J
  hq : ∀ i : J.Job, 0 < J.q i
  hR : (PSL J).sum = R
  bpw : ∀ i ≤ m, (n + 1) ^ i < B
  bm : m < B
  bn : 2 * n + 3 < B
  bW : W + 2 < B
  bR : (n + 1) ^ m * (R + 1) < B
  bd : ∀ k < n, dv J k + 2 < B
  bp : ∀ k < n, R + pv J k + qv J k + 1 < B
  bs : ∀ a b, a < n → b < n → dv J a + qv J b < B
  bw : ∀ k < n, wv J k + W < B

/-- The set-up: constants, the sum, `PW`, `N`, `NX`, the number of the first `m` indices. -/
def setup4 : Com :=
  .seq (.assign "nb" (.bin .add (V "n") (.lit 1)))
    (.seq sumCom
      (.seq (.assign "R" (.bin .add (V "R") (.lit 1)))
        (.seq pwSetup
          (.seq (.assign "N" (.get "PW" (V "m")))
            (.seq nxLoop (.seq code0Loop (.assign "cc" (V "N"))))))))

/-- What the machine starts the core from. -/
def CPre4 (J : Instance) (n m W R : ℕ) (σ : Env) : Prop :=
  σ.arrs "PS" = PSL J ∧ σ.arrs "QS" = QSL J ∧ σ.arrs "DS" = DSL J ∧ σ.arrs "WS" = WSL J ∧
  σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "sn" = n ∧ σ.vars "W" = W ∧
  (σ.arrs "NX").length = n ∧ (σ.arrs "PW").length = m + 1 ∧
  σ.arrs "VALID" = List.replicate ((n + 1) ^ m) 0 ∧
  σ.arrs "TAB" = List.replicate ((n + 1) ^ m * (R + 1)) 0

/-- The cost of the set-up. -/
def setupCost4 (n m : ℕ) : ℕ := setupCost n m + 24 * n + 60

set_option maxHeartbeats 8000000 in
theorem setup4_spec {J : Instance} {B n m W R : ℕ} (ci : CI4 J B n m W R) :
    Spec B (CPre4 J n m W R) setup4
      (fun _σ σ' => ∃ NXl PWl, SC4 J B n m W R (PSL J) (QSL J) (DSL J) (WSL J) NXl PWl ∧
        Stat4 n m W R (PSL J) (QSL J) (DSL J) (WSL J) NXl PWl σ' ∧
        σ'.vars "cc" = (n + 1) ^ m ∧ σ'.vars "zk" = codeL n m (List.range (min m n)) ∧
        σ'.vars "W" = W ∧ σ'.arrs "TAB" = List.replicate ((n + 1) ^ m * (R + 1)) 0 ∧
        σ'.arrs "VALID" = List.replicate ((n + 1) ^ m) 0)
      (setupCost4 n m) := by
  have hB := ci.hB
  have hn := ci.hn
  have hmach := ci.hmach
  have hn1 := ci.hn1
  have hm := ci.hm
  have hest := ci.hest
  have hq := ci.hq
  have hRsum := ci.hR
  have bpw := ci.bpw
  have bm := ci.bm
  have bn := ci.bn
  have bW := ci.bW
  have bR := ci.bR
  have bd := ci.bd
  have bp := ci.bp
  have bs := ci.bs
  have bw := ci.bw
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) bR
  have hRB : R + 1 < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) bR
  have hJn : (List.range J.jobs).length = n := by simp [hn]
  have lD : (DSL J).length = n := by simp [DSL, hn]
  have lQ : (QSL J).length = n := by simp [QSL, hn]
  have lP : (PSL J).length = n := by simp [PSL, hn]
  have lW : (WSL J).length = n := by simp [WSL, hn]
  have gD : ∀ k < n, (DSL J).getD k 0 = dv J k := fun k hk => by
    unfold DSL; rw [getD_map_range _ (by omega)]
  have gQ : ∀ k < n, (QSL J).getD k 0 = qv J k := fun k hk => by
    unfold QSL; rw [getD_map_range _ (by omega)]
  have gP : ∀ k < n, (PSL J).getD k 0 = pv J k := fun k hk => by
    unfold PSL; rw [getD_map_range _ (by omega)]
  have gW : ∀ k < n, (WSL J).getD k 0 = wv J k := fun k hk => by
    unfold WSL; rw [getD_map_range _ (by omega)]
  have gD' : ∀ x < J.jobs, (DSL J).getD x 0 = dv J x := fun x hx => gD x (by omega)
  have gQ' : ∀ x < J.jobs, (QSL J).getD x 0 = qv J x := fun x hx => gQ x (by omega)
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hPS0, hQS0, hDS0, hWS0, hn0, hm0, hsn0, hW0, hNXl0, hPWl0, hV0, hT0⟩ := hσ
  -- 1: nb := n + 1
  have hvn : (V "n").evalB B σ = some n := hn0 ▸ evalB_var (by rw [hn0]; omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "nb") (e := .bin .add (V "n") (.lit 1)) (v := n + 1)
    (evalB_bin hvn (evalB_lit (by omega)) (by show n + 1 < B; omega))
  set σ1 : Env := σ.setVar "nb" (n + 1) with hσ1
  clear_value σ1
  -- 2: the sum
  have hPvB : ∀ v ∈ PSL J, v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk' : k < n := by simpa [lP] using hk
    have := gP k hk'
    rw [List.getD_eq_getElem _ _ hk] at this
    rw [this]; have := bp k hk'; omega
  obtain ⟨σ2, hr2, hR2, hfv2, hfa2⟩ :=
    (sumCom_spec (B := B) hB n (PSL J) lP (by omega) (by omega) hPvB).run (σ := σ1)
      ⟨by simp [hσ1, hn0], by simp [hσ1, hPS0]⟩
  rw [hRsum] at hR2
  have hf2 : ∀ y, y ∉ ["R", "sI"] → σ2.vars y = σ1.vars y := hfv2
  -- 3: R := R + 1
  have hvR2 : (V "R").evalB B σ2 = some R := hR2 ▸ evalB_var (by rw [hR2]; omega)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "R") (e := .bin .add (V "R") (.lit 1)) (v := R + 1)
    (evalB_bin hvR2 (evalB_lit (by omega)) (by show R + 1 < B; exact hRB))
  set σ3 : Env := σ2.setVar "R" (R + 1) with hσ3
  clear_value σ3
  -- 4: the powers
  obtain ⟨σ4, hr4, ⟨hPI4, hpi4⟩, hfv4, hfa4, -, -⟩ :=
    (pwSetup_spec (B := B) hB n m bpw bm).frame.run (σ := σ3)
      ⟨by simp [hσ3, hf2 "nb" (by decide), hσ1],
       by simp [hσ3, hf2 "m" (by decide), hσ1, hm0],
       by simp [hσ3, hfa2, hσ1, hPWl0]⟩
  have hPW4 : ∀ i ≤ m, (σ4.arrs "PW").getD i 0 = (n + 1) ^ i := fun i hi => hPI4.2.2.2.2 i (by omega)
  have hPWl4 : (σ4.arrs "PW").length = m + 1 := hPI4.2.2.1
  have hf4 : ∀ y, y ∉ ["pi"] → σ4.vars y = σ3.vars y :=
    fun y hy => hfv4 y (fun h => hy (pwSetup_wvars y h))
  have ha4 : ∀ a, a ≠ "PW" → σ4.arrs a = σ3.arrs a :=
    fun a ha => hfa4 a (fun h => ha (pwSetup_warrs a h))
  -- 5: N := PW[m]
  have hvm4 : (V "m").evalB B σ4 = some m := by
    have : σ4.vars "m" = m := by rw [hf4 "m" (by decide)]; simp [hσ3, hf2 "m" (by decide), hσ1, hm0]
    exact this ▸ evalB_var (by rw [this]; exact bm)
  have r5 := Run.assign (B := B) (σ := σ4) (x := "N") (e := .get "PW" (V "m")) (v := (n + 1) ^ m)
    (by
      have := RunStep.eval_get B σ4 "PW" (V "m") m hvm4 (by omega) (by rw [hPW4 m le_rfl]; exact hNB)
      rwa [hPW4 m le_rfl] at this)
  set σ5 : Env := σ4.setVar "N" ((n + 1) ^ m) with hσ5
  clear_value σ5
  -- 6: NX
  have hDS5 : σ5.arrs "DS" = DSL J := by
    simp only [hσ5, arrs_setVar]; rw [ha4 "DS" (by decide)]; simp [hσ3, hfa2, hσ1, hDS0]
  have hQS5 : σ5.arrs "QS" = QSL J := by
    simp only [hσ5, arrs_setVar]; rw [ha4 "QS" (by decide)]; simp [hσ3, hfa2, hσ1, hQS0]
  have hsn5 : σ5.vars "sn" = n := by
    simp [hσ5]; rw [hf4 "sn" (by decide)]; simp [hσ3, hf2 "sn" (by decide), hσ1, hsn0]
  have hNXl5 : (σ5.arrs "NX").length = n := by
    simp only [hσ5, arrs_setVar]; rw [ha4 "NX" (by decide)]; simp [hσ3, hfa2, hσ1, hNXl0]
  have hDB : ∀ v ∈ DSL J, v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk' : k < n := by simpa [lD] using hk
    have := gD k hk'
    rw [List.getD_eq_getElem _ _ hk] at this
    rw [this]; have := bd k hk'; omega
  have hQB : ∀ v ∈ QSL J, v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk' : k < n := by simpa [lQ] using hk
    have := gQ k hk'
    rw [List.getD_eq_getElem _ _ hk] at this
    rw [this]; have := bp k hk'; omega
  have hsum : ∀ a b, a < n → b < n → (DSL J).getD a 0 + (QSL J).getD b 0 < B := by
    intro a b ha hb; rw [gD a ha, gQ b hb]; exact bs a b ha hb
  have hmono : ∀ j, j < n → ∀ x y, j < x → x ≤ y → y < n →
      Fails (DSL J) (QSL J) j x → Fails (DSL J) (QSL J) j y :=
    fun j hj x y h1 h2 h3 => fails_mono hest (DSL J) (QSL J) gD' gQ' j (by omega) x y h1 h2 (by omega)
  obtain ⟨σ6, hr6, ⟨hD6, hQ6, hsn6, hres6⟩, hfv6, hfa6, -, -⟩ :=
    (nxLoop_spec (B := B) (by omega) (DSL J) (QSL J) n lD lQ hDB hQB hsum (by omega) hmono).frame.run
      (σ := σ5) ⟨hDS5, hQS5, hsn5, hNXl5⟩
  have hf6 : ∀ y, y ∉ ["sj", "dj", "bl", "bh", "bm", "ex", "qx", "tt"] → σ6.vars y = σ5.vars y :=
    fun y hy => hfv6 y (fun h => hy (nxLoop_wvars y h))
  have ha6 : ∀ a, a ≠ "NX" → σ6.arrs a = σ5.arrs a :=
    fun a ha => hfa6 a (fun h => ha (nxLoop_warrs a h))
  have hNXl6 : (σ6.arrs "NX").length = n := by
    rw [Lax496464Proofs.Ram.Corollary1Prog.run_arrs_length_eq hr6 "NX"]; exact hNXl5
  -- 7: the first `m` indices
  have hnb6 : σ6.vars "nb" = n + 1 := by
    rw [hf6 "nb" (by decide), hσ5]; simp only [vars_setVar]
    rw [if_neg (by decide), hf4 "nb" (by decide)]; simp [hσ3, hf2 "nb" (by decide), hσ1]
  have hm6 : σ6.vars "m" = m := by
    rw [hf6 "m" (by decide), hσ5]; simp only [vars_setVar]
    rw [if_neg (by decide), hf4 "m" (by decide)]; simp [hσ3, hf2 "m" (by decide), hσ1, hm0]
  have hn6 : σ6.vars "n" = n := by
    rw [hf6 "n" (by decide), hσ5]; simp only [vars_setVar]
    rw [if_neg (by decide), hf4 "n" (by decide)]; simp [hσ3, hf2 "n" (by decide), hσ1, hn0]
  obtain ⟨σ7, hr7, hzk7, hfv7, hfa7, -, -⟩ :=
    (code0Loop_spec (B := B) hB n m bpw bm).frame.run (σ := σ6) ⟨hnb6, hm6, hn6⟩
  have hf7 : ∀ y, y ∉ ["zk", "zi2"] → σ7.vars y = σ6.vars y :=
    fun y hy => hfv7 y (fun h => hy (code0Loop_wvars y h))
  have ha7 : ∀ a, σ7.arrs a = σ6.arrs a := fun a => hfa7 a (by rw [code0Loop_warrs]; simp)
  -- 8: cc := N
  have hN7 : σ7.vars "N" = (n + 1) ^ m := by
    rw [hf7 "N" (by decide), hf6 "N" (by decide), hσ5]; simp
  have hvN7 : (V "N").evalB B σ7 = some ((n + 1) ^ m) := hN7 ▸ evalB_var (by rw [hN7]; exact hNB)
  have r8 := Run.assign (B := B) (σ := σ7) (x := "cc") (e := V "N") (v := (n + 1) ^ m) hvN7
  set σ8 : Env := σ7.setVar "cc" ((n + 1) ^ m) with hσ8
  clear_value σ8
  -- the facts about the final state
  have hNX8 : σ8.arrs "NX" = σ6.arrs "NX" := by simp [hσ8, ha7]
  have hSC : SC4 J B n m W R (PSL J) (QSL J) (DSL J) (WSL J) (σ8.arrs "NX") (σ4.arrs "PW") := by
    refine ⟨hB, hn, hm, hest, hq, lP, lQ, lD, lW, ?_, gP, gQ, gD, gW, ?_, hPWl4, hPW4,
      bpw, bm, by omega, bW, bR, bp, fun k hk => by have := bd k hk; omega, bw⟩
    · rw [hNX8]; exact hNXl6
    · intro j hj
      rw [hNX8]
      have hj' : j < n := by omega
      exact res_isNxt hest hq hj (DSL J) (QSL J) gD' gQ' (hn ▸ hres6 j hj')
  have hbase8 : ∀ y, y ∉ ["cc", "zk", "zi2", "sj", "dj", "bl", "bh", "bm", "ex", "qx", "tt",
      "N", "pi", "R", "sI", "nb"] → σ8.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16⟩ := hy
    simp only [hσ8, vars_setVar]
    rw [if_neg y1, hf7 y (by simp [y2, y3]), hf6 y (by simp [y4, y5, y6, y7, y8, y9, y10, y11]),
      hσ5]
    simp only [vars_setVar]
    rw [if_neg y12, hf4 y (by simp [y13]), hσ3]
    simp only [vars_setVar]
    rw [if_neg y14, hf2 y (by simp [y14, y15]), hσ1]
    simp only [vars_setVar]
    rw [if_neg y16]
  have hbaseA : ∀ a, a ≠ "NX" → a ≠ "PW" → σ8.arrs a = σ.arrs a := by
    intro a h1 h2
    simp only [hσ8, arrs_setVar]
    rw [ha7, ha6 a h1, hσ5]; simp only [arrs_setVar]
    rw [ha4 a h2, hσ3]; simp only [arrs_setVar]; rw [hfa2, hσ1]; simp only [arrs_setVar]
  have hT8 : σ8.arrs "TAB" = List.replicate ((n + 1) ^ m * (R + 1)) 0 := by
    rw [hbaseA "TAB" (by decide) (by decide)]; exact hT0
  have hV8 : σ8.arrs "VALID" = List.replicate ((n + 1) ^ m) 0 := by
    rw [hbaseA "VALID" (by decide) (by decide)]; exact hV0
  have hR8 : σ8.vars "R" = R + 1 := by
    simp only [hσ8, vars_setVar]
    rw [if_neg (by decide), hf7 "R" (by decide), hf6 "R" (by decide), hσ5]
    simp only [vars_setVar]
    rw [if_neg (by decide), hf4 "R" (by decide), hσ3]; simp
  have hStat : Stat4 n m W R (PSL J) (QSL J) (DSL J) (WSL J) (σ8.arrs "NX") (σ4.arrs "PW") σ8 := by
    refine ⟨?_, ?_, ?_, hR8, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rw [hbase8 "n" (by decide)]; exact hn0
    · rw [hbase8 "m" (by decide)]; exact hm0
    · simp only [hσ8, vars_setVar]; rw [if_neg (by decide), hf7 "nb" (by decide)]; exact hnb6
    · simp only [hσ8, vars_setVar]; rw [if_neg (by decide)]; exact hN7
    · rw [hbase8 "W" (by decide)]; exact hW0
    · rw [hbaseA "PS" (by decide) (by decide), hPS0]
    · rw [hbaseA "QS" (by decide) (by decide), hQS0]
    · rw [hbaseA "DS" (by decide) (by decide), hDS0]
    · rw [hbaseA "WS" (by decide) (by decide), hWS0]
    · simp only [hσ8, arrs_setVar]
      rw [ha7, ha6 "PW" (by decide), hσ5]; simp only [arrs_setVar]
  have hnx : nxBodyCost n + 4 = 68 + 44 * n.size := by unfold nxBodyCost; omega
  have hrun : Run B setup4 σ σ8 _ :=
    Run.seq r1 <| Run.seq hr2 <| Run.seq r3 <| Run.seq hr4 <| Run.seq r5 <| Run.seq hr6 <|
    Run.seq hr7 r8
  refine ⟨σ8, _, hrun.mono ?_, le_rfl, σ8.arrs "NX", σ4.arrs "PW", hSC, hStat, ?_, ?_, ?_, hT8, hV8⟩
  · unfold setupCost4 setupCost; rw [hnx]; simp only [Expr.size]; omega
  · simp [hσ8]
  · simp [hσ8, hzk7]
  · rw [hbase8 "W" (by decide)]; exact hW0


/-- The whole core. -/
def core4 : Com := .seq setup4 loopCom4

theorem loopCom4_wvars : ∀ y ∈ loopCom4.wvars,
    y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx",
      "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1",
      "zr", "ct", "cf"] := by decide

/-- **The core's specification.** -/
theorem core4_spec {J : Instance} {B n m W R : ℕ} (ci : CI4 J B n m W R) :
    Spec B (CPre4 J n m W R) core4
      (fun _σ σ' => σ'.vars "zk" = codeL n m (List.range (min m n)) ∧ σ'.vars "R" = R + 1 ∧
        σ'.vars "W" = W ∧ (σ'.arrs "TAB").length = (n + 1) ^ m * (R + 1) ∧
        DInv J n m W R ((n + 1) ^ m) 0 (σ'.arrs "TAB"))
      (setupCost4 n m + (loopWork n m R ((n + 1) ^ m) + 4)) := by
  have hset := setup4_spec ci
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ1, hr1, NXl, PWl, sc, hSt, hcc, hzk, hW, hT, hV⟩ := hset σ hσ
  obtain ⟨σ2, hr2, ⟨hcc2, hT2⟩, hfv2, hfa2, -, -⟩ :=
    (loopCom4_spec sc).frame.run (σ := σ1)
      ⟨⟨hSt, by rw [hcc], by rw [hT, hcc]; exact dinv_init J n m W R,
        by rw [hcc, hV]; exact validOK_init n m⟩, hcc⟩
  have hfv : ∀ y, y ∉ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi",
      "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp",
      "ri", "z1", "zr", "ct", "cf"] → σ2.vars y = σ1.vars y :=
    fun y hy => hfv2 y (fun h => hy (loopCom4_wvars y h))
  refine ⟨σ2, _, hr1.seq hr2, le_rfl, ?_, ?_, ?_, hT2.1.1, hT2⟩
  · rw [hfv "zk" (by decide)]; exact hzk
  · rw [hfv "R" (by decide)]; exact hSt.2.2.2.1
  · rw [hfv "W" (by decide)]; exact hW

end Lax496464Proofs.Ram.D4Core
