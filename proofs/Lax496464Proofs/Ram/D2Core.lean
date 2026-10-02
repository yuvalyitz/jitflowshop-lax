import Lax496464Proofs.Ram.D2Step
import Lax496464Proofs.Ram.D2Bsearch
import Lax496464Proofs.Ram.D2Setup
import Lax496464Proofs.Ram.Corollary1Init

/-!
# Theorem 2's Machine, Part 7: the Core

`core2` takes the sorted arrays `PS QS DS WS` and the scalars `n m W` (as `sortSetup3` leaves them)
and fills the table.  Its specification, `core2_spec`, describes the final contents of the table: for
every weight `r ≤ W`, the entry of the number of the first `m` indices is the `Rep` of "some set of
weight at least `r` compatible with those thresholds can be preprocessed from `P'`".  The decision
bit is `finish`'s business (`D2Final`).
-/

namespace Lax496464Proofs.Ram.D2Core

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.D2Step Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch
open Lax496464Proofs.Ram.Nxt1 (Fails Res res_isNxt)
open Lax496464.DynamicProgram (firstM)
open Lax496464Proofs.Ram.Dp1 (IsNxt pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)
open Lax496464Proofs.Ram.ListUtil

theorem le_foldr_max {l : List ℕ} {v : ℕ} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The list of the values of `f` on `0 … n-1`, read at `k < n`. -/
theorem getD_map_range (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl

/-- `Fails` is `d j ≤ s x`. -/
theorem fails_iff {J : Instance} (D Q : List ℕ) (hD : ∀ x < J.jobs, D.getD x 0 = dv J x)
    (hQ : ∀ x < J.jobs, Q.getD x 0 = qv J x) {j x : ℕ} (hj : j < J.jobs) (hx : x < J.jobs) :
    Fails D Q j x ↔ ((J.d ⟨j, hj⟩ : ℤ) ≤ s (⟨x, hx⟩ : J.Job)) := by
  unfold Fails
  rw [hD x hx, hD j hj, hQ x hx]
  unfold dv qv
  rw [dif_pos hj, dif_pos hx, dif_pos hx]
  have : s (⟨x, hx⟩ : J.Job) = (J.d ⟨x, hx⟩ : ℤ) - J.q ⟨x, hx⟩ := rfl
  omega

theorem fails_mono {J : Instance} (hest : EstOrdered J) (D Q : List ℕ)
    (hD : ∀ x < J.jobs, D.getD x 0 = dv J x) (hQ : ∀ x < J.jobs, Q.getD x 0 = qv J x) :
    ∀ j, j < J.jobs → ∀ x y, j < x → x ≤ y → y < J.jobs → Fails D Q j x → Fails D Q j y := by
  intro j hj x y hjx hxy hy hf
  have hx : x < J.jobs := by omega
  rw [fails_iff D Q hD hQ hj hx] at hf
  rw [fails_iff D Q hD hQ hj hy]
  have := hest ⟨x, hx⟩ ⟨y, hy⟩ (Fin.mk_le_mk.mpr hxy)
  omega


/-- What `core2` needs to know about the sorted instance and the word bound. -/
structure CI (J : Instance) (B n m W : ℕ) : Prop where
  hB : 2 < B
  hn : J.jobs = n
  hmach : J.machines = m
  hn1 : 1 ≤ n
  hm : 1 ≤ m
  hest : EstOrdered J
  hq : ∀ i : J.Job, 0 < J.q i
  bpw : ∀ i ≤ m, (n + 1) ^ i < B
  bm : m < B
  bn : 2 * n + 3 < B
  bW : W + 2 < B
  bR : (n + 1) ^ m * (W + 1) < B
  bd : ∀ k < n, dv J k + 2 < B
  bp : ∀ k < n, pv J k + qv J k < B
  bs : ∀ a b, a < n → b < n → dv J a + qv J b < B
  bw : ∀ k < n, wv J k < B

/-- The set-up: constants, `PW`, `N`, `cinf`, `NX`, the number of the first `m` indices. -/
def setup2 : Com :=
  .seq (.assign "nb" (.bin .add (V "n") (.lit 1)))
    (.seq (.assign "R" (.bin .add (V "W") (.lit 1)))
      (.seq pwSetup
        (.seq (.assign "N" (.get "PW" (V "m")))
          (.seq Lax496464Proofs.Ram.Corollary1Init.maxScan
            (.seq nxLoop (.seq code0Loop (.assign "cc" (V "N"))))))))

theorem pwSetup_wvars : ∀ y ∈ pwSetup.wvars, y ∈ ["pi"] := by decide
theorem pwSetup_warrs : ∀ a ∈ pwSetup.warrs, a = "PW" := by decide
theorem maxScan_wvars : ∀ y ∈ Lax496464Proofs.Ram.Corollary1Init.maxScan.wvars,
    y ∈ ["cinf", "mi", "mv"] := by decide
theorem maxScan_warrs : Lax496464Proofs.Ram.Corollary1Init.maxScan.warrs = [] := by decide
theorem nxLoop_wvars : ∀ y ∈ nxLoop.wvars,
    y ∈ ["sj", "dj", "bl", "bh", "bm", "ex", "qx", "tt"] := by decide
theorem nxLoop_warrs : ∀ a ∈ nxLoop.warrs, a = "NX" := by decide
theorem code0Loop_wvars : ∀ y ∈ code0Loop.wvars, y ∈ ["zk", "zi2"] := by decide
theorem code0Loop_warrs : code0Loop.warrs = [] := by decide


/-- The sorted arrays as lists. -/
def PSL (J : Instance) : List ℕ := (List.range J.jobs).map (pv J)
def QSL (J : Instance) : List ℕ := (List.range J.jobs).map (qv J)
def DSL (J : Instance) : List ℕ := (List.range J.jobs).map (dv J)
def WSL (J : Instance) : List ℕ := (List.range J.jobs).map (wv J)

/-- What the machine starts the core from. -/
def CPre (J : Instance) (n m W : ℕ) (σ : Env) : Prop :=
  σ.arrs "PS" = PSL J ∧ σ.arrs "QS" = QSL J ∧ σ.arrs "DS" = DSL J ∧ σ.arrs "WS" = WSL J ∧
  σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "sn" = n ∧ σ.vars "W" = W ∧
  (σ.arrs "NX").length = n ∧ (σ.arrs "PW").length = m + 1 ∧
  σ.arrs "VALID" = List.replicate ((n + 1) ^ m) 0 ∧
  σ.arrs "TAB" = List.replicate ((n + 1) ^ m * (W + 1)) 0

/-- The first table's numbers are all zero, as `TabOK` needs. -/
theorem tabOK_init (J : Instance) (n m W inf : ℕ) :
    TabOK J n m W inf ((n + 1) ^ m) ((n + 1) ^ m) (List.replicate ((n + 1) ^ m * (W + 1)) 0) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro Zs hsl h
    have := hsl.codeL_lt
    omega
  · intro i hi _
    simp [hi]

theorem validOK_init (n m : ℕ) :
    ValidOK n m ((n + 1) ^ m) ((n + 1) ^ m) (List.replicate ((n + 1) ^ m) 0) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro c' h1 h2; omega
  · intro i
    by_cases hi : i < (n + 1) ^ m
    · simp [hi]
    · simp [List.getD_eq_getElem?_getD, hi]


/-- The cost of the set-up. -/
def setupCost (n m : ℕ) : ℕ := 100 + 68 * m + 54 * n + (68 + 44 * n.size) * n

set_option maxHeartbeats 8000000 in
theorem setup2_spec {J : Instance} {B n m W : ℕ} (ci : CI J B n m W) :
    Spec B (CPre J n m W) setup2
      (fun _σ σ' => ∃ inf NXl PWl, SC J B n m W inf (PSL J) (QSL J) (DSL J) (WSL J) NXl PWl ∧
        Stat n m W inf (PSL J) (QSL J) (DSL J) (WSL J) NXl PWl σ' ∧
        σ'.vars "cc" = (n + 1) ^ m ∧ σ'.vars "zk" = codeL n m (List.range (min m n)) ∧
        σ'.vars "W" = W ∧ σ'.arrs "TAB" = List.replicate ((n + 1) ^ m * (W + 1)) 0 ∧
        σ'.arrs "VALID" = List.replicate ((n + 1) ^ m) 0)
      (setupCost n m) := by
  have hB := ci.hB
  have hn := ci.hn
  have hmach := ci.hmach
  have hn1 := ci.hn1
  have hm := ci.hm
  have hest := ci.hest
  have hq := ci.hq
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
  -- 1, 2
  have hvn : (V "n").evalB B σ = some n := hn0 ▸ evalB_var (by rw [hn0]; omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "nb") (e := .bin .add (V "n") (.lit 1)) (v := n + 1)
    (evalB_bin hvn (evalB_lit (by omega)) (by show n + 1 < B; omega))
  set σ1 : Env := σ.setVar "nb" (n + 1) with hσ1
  clear_value σ1
  have hvW : (V "W").evalB B σ1 = some W := by
    have : σ1.vars "W" = W := by simp [hσ1, hW0]
    exact this ▸ evalB_var (by rw [this]; omega)
  have r2 := Run.assign (B := B) (σ := σ1) (x := "R") (e := .bin .add (V "W") (.lit 1)) (v := W + 1)
    (evalB_bin hvW (evalB_lit (by omega)) (by show W + 1 < B; omega))
  set σ2 : Env := σ1.setVar "R" (W + 1) with hσ2
  clear_value σ2
  -- 3: the powers
  obtain ⟨σ3, hr3, ⟨hPI3, hpi3⟩, hfv3, hfa3, -, -⟩ :=
    (pwSetup_spec (B := B) hB n m bpw bm).frame.run (σ := σ2)
      ⟨by simp [hσ2, hσ1], by simp [hσ2, hσ1, hm0], by simp [hσ2, hσ1, hPWl0]⟩
  have hPW3 : ∀ i ≤ m, (σ3.arrs "PW").getD i 0 = (n + 1) ^ i := fun i hi => hPI3.2.2.2.2 i (by omega)
  have hPWl3 : (σ3.arrs "PW").length = m + 1 := hPI3.2.2.1
  have hf3 : ∀ y, y ∉ ["pi"] → σ3.vars y = σ2.vars y :=
    fun y hy => hfv3 y (fun h => hy (pwSetup_wvars y h))
  have ha3 : ∀ a, a ≠ "PW" → σ3.arrs a = σ2.arrs a :=
    fun a ha => hfa3 a (fun h => ha (pwSetup_warrs a h))
  -- 4: N := PW[m]
  have hvm3 : (V "m").evalB B σ3 = some m := by
    have : σ3.vars "m" = m := by rw [hf3 "m" (by decide)]; simp [hσ2, hσ1, hm0]
    exact this ▸ evalB_var (by rw [this]; exact bm)
  have r4 := Run.assign (B := B) (σ := σ3) (x := "N") (e := .get "PW" (V "m")) (v := (n + 1) ^ m)
    (by
      have := RunStep.eval_get B σ3 "PW" (V "m") m hvm3 (by omega) (by rw [hPW3 m le_rfl]; exact hNB)
      rwa [hPW3 m le_rfl] at this)
  set σ4 : Env := σ3.setVar "N" ((n + 1) ^ m) with hσ4
  clear_value σ4
  -- 5: cinf
  have hDS4 : σ4.arrs "DS" = DSL J := by
    simp only [hσ4, arrs_setVar]; rw [ha3 "DS" (by decide)]; simp [hσ2, hσ1, hDS0]
  have hsn4 : σ4.vars "sn" = n := by
    simp [hσ4]; rw [hf3 "sn" (by decide)]; simp [hσ2, hσ1, hsn0]
  have hDB2 : ∀ v ∈ DSL J, v + 2 < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk' : k < n := by simpa [lD] using hk
    have := gD k hk'
    rw [List.getD_eq_getElem _ _ hk] at this
    rw [this]; exact bd k hk'
  obtain ⟨σ5, hr5, hcinf5, hfv5, hfa5, -, -⟩ :=
    (Lax496464Proofs.Ram.Corollary1Init.maxScan_spec (B := B) (by omega) (DSL J) n lD hDB2
      (by omega)).frame.run (σ := σ4) ⟨hDS4, hsn4⟩
  set inf : ℕ := (DSL J).foldr max 0 + 2 with hinfdef
  have hf5 : ∀ y, y ∉ ["cinf", "mi", "mv"] → σ5.vars y = σ4.vars y :=
    fun y hy => hfv5 y (fun h => hy (maxScan_wvars y h))
  have ha5 : ∀ a, σ5.arrs a = σ4.arrs a := fun a => hfa5 a (by rw [maxScan_warrs]; simp)
  -- 6: NX
  have hinfB : inf < B := Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt hDB2 (by omega)
  have hQB : ∀ v ∈ QSL J, v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hk' : k < n := by simpa [lQ] using hk
    have := gQ k hk'
    rw [List.getD_eq_getElem _ _ hk] at this
    rw [this]; have := bp k hk'; omega
  have hDB : ∀ v ∈ DSL J, v < B := fun v hv => by have := hDB2 v hv; omega
  have hsum : ∀ a b, a < n → b < n → (DSL J).getD a 0 + (QSL J).getD b 0 < B := by
    intro a b ha hb; rw [gD a ha, gQ b hb]; exact bs a b ha hb
  have hmono : ∀ j, j < n → ∀ x y, j < x → x ≤ y → y < n →
      Fails (DSL J) (QSL J) j x → Fails (DSL J) (QSL J) j y :=
    fun j hj x y h1 h2 h3 => fails_mono hest (DSL J) (QSL J) gD' gQ' j (by omega) x y h1 h2 (by omega)
  have hQS5 : σ5.arrs "QS" = QSL J := by
    rw [ha5, hσ4]; simp only [arrs_setVar]; rw [ha3 "QS" (by decide)]; simp [hσ2, hσ1, hQS0]
  have hDS5 : σ5.arrs "DS" = DSL J := by rw [ha5]; exact hDS4
  have hsn5 : σ5.vars "sn" = n := by rw [hf5 "sn" (by decide)]; exact hsn4
  have hNXl5 : (σ5.arrs "NX").length = n := by
    rw [ha5, hσ4]; simp only [arrs_setVar]; rw [ha3 "NX" (by decide)]; simp [hσ2, hσ1, hNXl0]
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
    rw [hf6 "nb" (by decide), hf5 "nb" (by decide), hσ4]; simp only [vars_setVar]
    rw [if_neg (by decide), hf3 "nb" (by decide)]; simp [hσ2, hσ1]
  have hm6 : σ6.vars "m" = m := by
    rw [hf6 "m" (by decide), hf5 "m" (by decide), hσ4]; simp only [vars_setVar]
    rw [if_neg (by decide), hf3 "m" (by decide)]; simp [hσ2, hσ1, hm0]
  have hn6 : σ6.vars "n" = n := by
    rw [hf6 "n" (by decide), hf5 "n" (by decide), hσ4]; simp only [vars_setVar]
    rw [if_neg (by decide), hf3 "n" (by decide)]; simp [hσ2, hσ1, hn0]
  obtain ⟨σ7, hr7, hzk7, hfv7, hfa7, -, -⟩ :=
    (code0Loop_spec (B := B) hB n m bpw bm).frame.run (σ := σ6) ⟨hnb6, hm6, hn6⟩
  have hf7 : ∀ y, y ∉ ["zk", "zi2"] → σ7.vars y = σ6.vars y :=
    fun y hy => hfv7 y (fun h => hy (code0Loop_wvars y h))
  have ha7 : ∀ a, σ7.arrs a = σ6.arrs a := fun a => hfa7 a (by rw [code0Loop_warrs]; simp)
  -- 8: cc := N
  have hN7 : σ7.vars "N" = (n + 1) ^ m := by
    rw [hf7 "N" (by decide), hf6 "N" (by decide), hf5 "N" (by decide), hσ4]; simp
  have hvN7 : (V "N").evalB B σ7 = some ((n + 1) ^ m) := hN7 ▸ evalB_var (by rw [hN7]; exact hNB)
  have r8 := Run.assign (B := B) (σ := σ7) (x := "cc") (e := V "N") (v := (n + 1) ^ m) hvN7
  set σ8 : Env := σ7.setVar "cc" ((n + 1) ^ m) with hσ8
  clear_value σ8
  -- the facts about the final state
  have hV3 : ∀ y, σ7.vars y = σ6.vars y ∨ y = "zk" ∨ y = "zi2" := by
    intro y; by_cases h : y = "zk" ∨ y = "zi2"
    · tauto
    · left; apply hf7; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact h
  have hNX8 : σ8.arrs "NX" = σ6.arrs "NX" := by simp [hσ8, ha7]
  have hSC : SC J B n m W inf (PSL J) (QSL J) (DSL J) (WSL J) (σ8.arrs "NX") (σ3.arrs "PW") := by
    refine ⟨hB, hn, hm, hest, hq, ?_, ?_, hinfB, lP, lQ, lD, lW, ?_, gP, gQ, gD, gW, ?_, hPWl3, hPW3,
      bpw, bm, by omega, bW, bR, bp, fun k hk => by have := bd k hk; omega, bw⟩
    · omega
    · intro i
      have hle : (J.d i : ℕ) ≤ (DSL J).foldr max 0 := by
        apply le_foldr_max
        have hi := i.isLt
        have hdv : dv J i = (J.d i : ℕ) := by unfold dv; rw [dif_pos i.isLt]
        have hlen : (i : ℕ) < (DSL J).length := by omega
        have := gD i (by omega)
        rw [List.getD_eq_getElem _ _ hlen, hdv] at this
        rw [← this]; exact List.getElem_mem hlen
      have hs : s i ≤ (J.d i : ℤ) := by unfold Instance.s; omega
      have : ((J.d i : ℕ) : ℤ) ≤ ((DSL J).foldr max 0 : ℕ) := by exact_mod_cast hle
      omega
    · rw [hNX8]; exact hNXl6
    · intro j hj
      rw [hNX8]
      have hj' : j < n := by omega
      exact res_isNxt hest hq hj (DSL J) (QSL J) gD' gQ' (hn ▸ hres6 j hj')
  have hbase8 : ∀ y, y ∉ ["cc", "zk", "zi2", "sj", "dj", "bl", "bh", "bm", "ex", "qx", "tt", "cinf",
      "mi", "mv", "N", "pi", "R", "nb"] → σ8.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18⟩ := hy
    simp only [hσ8, vars_setVar]
    rw [if_neg y1, hf7 y (by simp [y2, y3]), hf6 y (by simp [y4, y5, y6, y7, y8, y9, y10, y11]),
      hf5 y (by simp [y12, y13, y14]), hσ4]
    simp only [vars_setVar]
    rw [if_neg y15, hf3 y (by simp [y16]), hσ2]
    simp only [vars_setVar]
    rw [if_neg y17, hσ1]
    simp only [vars_setVar]
    rw [if_neg y18]
  have hbaseA : ∀ a, a ≠ "NX" → a ≠ "PW" → a ≠ "TAB" → a ≠ "VALID" → σ8.arrs a = σ.arrs a := by
    intro a h1 h2 h3 h4
    simp only [hσ8, arrs_setVar]
    rw [ha7, ha6 a h1, ha5, hσ4]; simp only [arrs_setVar]
    rw [ha3 a h2, hσ2]; simp only [arrs_setVar]; rw [hσ1]; simp only [arrs_setVar]
  have hT8 : σ8.arrs "TAB" = List.replicate ((n + 1) ^ m * (W + 1)) 0 := by
    simp only [hσ8, arrs_setVar]
    rw [ha7, ha6 "TAB" (by decide), ha5, hσ4]; simp only [arrs_setVar]
    rw [ha3 "TAB" (by decide), hσ2]; simp only [arrs_setVar]; rw [hσ1]; simp only [arrs_setVar]; exact hT0
  have hV8 : σ8.arrs "VALID" = List.replicate ((n + 1) ^ m) 0 := by
    simp only [hσ8, arrs_setVar]
    rw [ha7, ha6 "VALID" (by decide), ha5, hσ4]; simp only [arrs_setVar]
    rw [ha3 "VALID" (by decide), hσ2]; simp only [arrs_setVar]; rw [hσ1]; simp only [arrs_setVar]; exact hV0
  have hStat : Stat n m W inf (PSL J) (QSL J) (DSL J) (WSL J) (σ8.arrs "NX") (σ3.arrs "PW") σ8 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rw [hbase8 "n" (by decide)]; exact hn0
    · rw [hbase8 "m" (by decide)]; exact hm0
    · simp only [hσ8, vars_setVar]; rw [if_neg (by decide), hf7 "nb" (by decide)]; exact hnb6
    · simp only [hσ8, vars_setVar]
      rw [if_neg (by decide), hf7 "R" (by decide), hf6 "R" (by decide), hf5 "R" (by decide), hσ4]
      simp only [vars_setVar]
      rw [if_neg (by decide), hf3 "R" (by decide), hσ2]; simp
    · simp only [hσ8, vars_setVar]; rw [if_neg (by decide)]; exact hN7
    · simp only [hσ8, vars_setVar]
      rw [if_neg (by decide), hf7 "cinf" (by decide), hf6 "cinf" (by decide), hcinf5.1]
    · rw [hbaseA "PS" (by decide) (by decide) (by decide) (by decide), hPS0]
    · rw [hbaseA "QS" (by decide) (by decide) (by decide) (by decide), hQS0]
    · rw [hbaseA "DS" (by decide) (by decide) (by decide) (by decide), hDS0]
    · rw [hbaseA "WS" (by decide) (by decide) (by decide) (by decide), hWS0]
    · simp only [hσ8, arrs_setVar]
      rw [ha7, ha6 "PW" (by decide), ha5, hσ4]; simp only [arrs_setVar]
  have hnx : nxBodyCost n + 4 = 68 + 44 * n.size := by unfold nxBodyCost; omega
  have hrun : Run B setup2 σ σ8 _ :=
    Run.seq r1 <| Run.seq r2 <| Run.seq hr3 <| Run.seq r4 <| Run.seq hr5 <| Run.seq hr6 <|
    Run.seq hr7 r8
  refine ⟨σ8, _, hrun.mono ?_, le_rfl, inf, σ8.arrs "NX", σ3.arrs "PW", hSC, hStat, ?_, ?_, ?_, hT8, hV8⟩
  · unfold setupCost; rw [hnx]; simp only [Expr.size]; omega
  · simp [hσ8]
  · simp [hσ8, hzk7]
  · rw [hbase8 "W" (by decide)]; exact hW0


/-- The whole core. -/
def core2 : Com := .seq setup2 loopCom

theorem loopCom_wvars : ∀ y ∈ loopCom.wvars,
    y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx",
      "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1",
      "zr", "ct", "cf", "cw", "ce", "cg"] := by decide

theorem firstM_eq {J : Instance} {n m : ℕ} (hn : J.jobs = n) (hmach : J.machines = m) :
    ofList J (List.range (min m n)) = firstM J := by
  ext x
  simp only [mem_ofList, List.mem_range, firstM, Finset.mem_filter, Finset.mem_univ, true_and,
    hmach]
  have := x.isLt
  omega

theorem sl_range (n m : ℕ) : SL n m (List.range (min m n)) := by
  refine ⟨?_, fun z hz => ?_, by simp⟩
  · rw [List.sortedLT_iff_pairwise]; exact List.pairwise_lt_range
  · simp at hz; omega

/-- **The core's specification: the whole column of the first `m` indices.** -/
theorem core2_spec {J : Instance} {B n m W : ℕ} (ci : CI J B n m W) :
    Spec B (CPre J n m W) core2
      (fun _σ σ' => ∃ inf, 1 < inf ∧ inf < B ∧ (∀ i : J.Job, s i + 1 < inf) ∧
        σ'.vars "zk" = codeL n m (List.range (min m n)) ∧ σ'.vars "R" = W + 1 ∧ σ'.vars "W" = W ∧
        (σ'.arrs "TAB").length = (n + 1) ^ m * (W + 1) ∧
        ∀ r ≤ W, Rep inf ((σ'.arrs "TAB").getD (codeL n m (List.range (min m n)) * (W + 1) + r) 0)
          (fun P' => AchGe J (firstM J) r P'))
      (setupCost n m + (loopWork n m W ((n + 1) ^ m) + 4)) := by
  have hset := setup2_spec ci
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ1, hr1, inf, NXl, PWl, sc, hSt, hcc, hzk, hW, hT, hV⟩ := hset σ hσ
  obtain ⟨σ2, hr2, ⟨hcc2, hT2⟩, hfv2, hfa2, -, -⟩ :=
    (loopCom_spec sc).frame.run (σ := σ1)
      ⟨⟨hSt, by rw [hcc], by rw [hT, hcc]; exact tabOK_init J n m W inf, by rw [hcc, hV]; exact validOK_init n m⟩, hcc⟩
  have hfv : ∀ y, y ∉ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim",
      "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1",
      "zr", "ct", "cf", "cw", "ce", "cg"] → σ2.vars y = σ1.vars y :=
    fun y hy => hfv2 y (fun h => hy (loopCom_wvars y h))
  refine ⟨σ2, _, hr1.seq hr2, le_rfl, inf, sc.hi1, sc.hinfB, sc.hinf, ?_, ?_, ?_, hT2.1, ?_⟩
  · rw [hfv "zk" (by decide)]; exact hzk
  · rw [hfv "R" (by decide)]; exact hSt.2.2.2.1
  · rw [hfv "W" (by decide)]; exact hW
  · intro r hr
    have := hT2.2.1 (List.range (min m n)) (sl_range n m) (Nat.zero_le _) r hr
    rw [firstM_eq sc.hn ci.hmach] at this
    exact this

end Lax496464Proofs.Ram.D2Core
