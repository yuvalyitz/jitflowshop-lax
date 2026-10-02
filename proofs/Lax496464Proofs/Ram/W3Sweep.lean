import Lax496464Proofs.Ram.W3SweepEv
import Lax496464Proofs.Ram.Corollary1Init

/-!
# The Sweep Loop, and the Sweep Core

`sweepLoop` runs the events of the merge until all `2n` are done (`sweepLoop_spec`), and
`core` is `initCore ; sweepLoop`: it reads the sorted arrays `PS QS DS WS SA` and the threshold
`W` and leaves in row `0` of `TB` the table of the sweep, `TB[c] < INF ↔ HasWeight J c` for every
`c ≤ W` (`core_spec`).
-/

namespace Lax496464Proofs.Ram.W3Sweep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464.FlowShop Lax496464.EstOrder
open Lax496464.FlowShop.Instance (HasWeight)
open Lax496464Proofs.Ram.W3Bits Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3Model
open Lax496464Proofs.Ram.W3SweepModel Lax496464Proofs.Ram.W3SweepEv
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)
open Lax496464Proofs.Ram.W3Loops (V tabOf)

/-! ## Filling row `0` of the table -/

/-- One cell of the fill: `TB[ci] := cinf`. -/
def fillBody : Com :=
  .seq (.store "TB" (V "ci") (V "cinf")) (.assign "ci" (.bin .add (V "ci") (.lit 1)))

/-- `TB[0], …, TB[W1-1] := cinf`. -/
def fillTB : Com := .seq (.assign "ci" (.lit 0)) (.while (.lt (V "ci") (V "W1")) fillBody)

/-- The fill's invariant. -/
def FillInv (W1 INF : ℕ) (TB0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.vars "ci" ≤ W1 ∧
  (σ.arrs "TB").length = TB0.length ∧
  ∀ j, (σ.arrs "TB").getD j 0 = if j < σ.vars "ci" then INF else TB0.getD j 0

theorem fillBody_spec {B : ℕ} (hB : 1 < B) (W1 INF : ℕ) (TB0 : List ℕ) (hW1B : W1 < B)
    (hINF : INF < B) (hW1L : W1 ≤ TB0.length) :
    Spec B (fun σ => FillInv W1 INF TB0 σ ∧ σ.vars "ci" < W1) fillBody
      (fun σ σ' => FillInv W1 INF TB0 σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1) 20 := by
  simp only [FillInv]
  run_vcg
  rename_i hlt h1 h2 h3 h4 h5
  simp only [vars_setVar, arrs_setVar, arrs_setArr, if_true]
  simp [h1, h2]
  refine ⟨hlt, h4, fun j => ?_⟩
  have e := h5 j
  rw [List.getD_eq_getElem?_getD] at e
  by_cases hj : j = σ.vars "ci"
  · subst hj
    rw [List.getElem?_set_self (by omega)]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hj), e]
    split_ifs <;> first | rfl | omega

theorem fillTB_spec {B : ℕ} (hB : 1 < B) (W1 INF : ℕ) (TB0 : List ℕ) (hW1B : W1 < B)
    (hINF : INF < B) (hW1L : W1 ≤ TB0.length) :
    Spec B (fun σ => σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "TB" = TB0) fillTB
      (fun _ σ' => (σ'.arrs "TB").length = TB0.length ∧
        ∀ j, (σ'.arrs "TB").getD j 0 = if j < W1 then INF else TB0.getD j 0)
      ((20 + 4) * W1 + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := fillBody) "ci" "W1" (FillInv W1 INF TB0) W1 20
    hW1B (fun σ h => h.2.2.1) (fun σ h => h.1) (fillBody_spec hB W1 INF TB0 hW1B hINF hW1L)
  refine (hloop.pre ?_).post ?_
  · rintro σ ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, by simp, by simp [h3], ?_⟩
    intro j; simp [h3]
  · rintro σ σ' - ⟨⟨-, -, -, hl, hg⟩, hci⟩
    refine ⟨hl, fun j => ?_⟩
    rw [hg j, hci]

/-! ## The loop -/

/-- `while ip + kp < n2 do stepBody`. -/
def sweepLoop : Com :=
  .while (.lt (.bin .add (V "ip") (V "kp")) (V "n2")) stepBody

theorem loopCond_true {B : ℕ} {σ : Env}
    (h : (Cond.lt (.bin .add (V "ip") (V "kp")) (V "n2")).evalB B σ = some true) :
    σ.vars "ip" + σ.vars "kp" < σ.vars "n2" := by
  simp only [evalB_condLt_iff, evalB_bin_iff, evalB_var_iff] at h
  obtain ⟨m, n, ⟨a, b, ⟨ha, -⟩, ⟨hb, -⟩, hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hn
  simp only [Bop.apply_add] at hm
  subst hm
  simpa [ha, hb] using hr.symm

theorem loopCond_false {B : ℕ} {σ : Env}
    (h : (Cond.lt (.bin .add (V "ip") (V "kp")) (V "n2")).evalB B σ = some false) :
    σ.vars "n2" ≤ σ.vars "ip" + σ.vars "kp" := by
  simp only [evalB_condLt_iff, evalB_bin_iff, evalB_var_iff] at h
  obtain ⟨m, n, ⟨a, b, ⟨ha, -⟩, ⟨hb, -⟩, hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hn
  simp only [Bop.apply_add] at hm
  subst hm
  have := hr.symm
  simp only [decide_eq_false_iff_not, not_lt] at this
  rw [ha, hb] at this
  exact this

open Classical in
/-- **The sweep loop**: from any invariant state, the machine does all the remaining events. -/
theorem sweepLoop_spec {B : ℕ} {J : Instance} {wd W1 INF LTB LPC LFS LSLT LP2 : ℕ}
    (hN : Nums J wd W1 INF B LTB LPC LFS LSLT LP2) (hE : EstOrdered J)
    (hq : ∀ i : J.Job, 0 < J.q i) (hwd : widthJ J ≤ wd) :
    Spec B (fun σ => Mach J INF W1 LTB LPC LFS LSLT LP2 σ ∧
        σ.vars "ip" + σ.vars "kp" ≤ 2 * J.jobs) sweepLoop
      (fun _ σ' => Mach J INF W1 LTB LPC LFS LSLT LP2 σ' ∧
        σ'.vars "ip" + σ'.vars "kp" = 2 * J.jobs)
      ((108 * (2 ^ wd * W1) + 306) * (2 * J.jobs) + 6) := by
  have hnB := hN.nB
  have hcsize : (Cond.lt (.bin .add (V "ip") (V "kp")) (V "n2")).size = 5 := by
    simp [Cond.size, Expr.size]
  have hI : ∀ σ : Env, (Mach J INF W1 LTB LPC LFS LSLT LP2 σ ∧
      σ.vars "ip" + σ.vars "kp" ≤ 2 * J.jobs) → σ.vars "n2" = 2 * J.jobs ∧
      σ.vars "ip" + σ.vars "kp" < B := by
    rintro σ ⟨⟨i, k, pre, hpos, hSt, hDy⟩, hle⟩
    exact ⟨hSt.n2, by omega⟩
  refine (Spec.while_count (P := fun σ => Mach J INF W1 LTB LPC LFS LSLT LP2 σ ∧
      σ.vars "ip" + σ.vars "kp" ≤ 2 * J.jobs)
    (fun σ => Mach J INF W1 LTB LPC LFS LSLT LP2 σ ∧ σ.vars "ip" + σ.vars "kp" ≤ 2 * J.jobs)
    (fun σ => 2 * J.jobs - (σ.vars "ip" + σ.vars "kp")) (108 * (2 ^ wd * W1) + 300) ?_ ?_
    (fun σ h => h) ?_).post ?_
  · intro σ h
    obtain ⟨h1, h2⟩ := hI σ h
    obtain ⟨⟨i, k, pre, hpos, hSt, hDy⟩, hle⟩ := h
    have hip : σ.vars "ip" < B := by rw [hDy.ip]; have := (pos_evs hpos).2.1; omega
    have hkp : σ.vars "kp" < B := by rw [hDy.kp]; have := (pos_evs hpos).2.2; omega
    have hn2 : σ.vars "n2" < B := by rw [h1]; omega
    exact evalB_condLt_isSome (evalB_bin (evalB_var hip) (evalB_var hkp) (by simpa using h2))
      (evalB_var hn2) |>.imp fun v hv => hv.1
  · refine (body_spec hN hE hq hwd).conseq ?_ ?_ le_rfl
    · rintro σ ⟨⟨hM, hle⟩, hc⟩
      refine ⟨hM, ?_⟩
      have := loopCond_true hc
      obtain ⟨⟨i, k, pre, hpos, hSt, hDy⟩, -⟩ := (⟨hM, hle⟩ : _ ∧ _)
      rw [hSt.n2] at this
      exact this
    · rintro σ σ' ⟨⟨hM, hle⟩, hc⟩ ⟨hM', hsum⟩
      have := loopCond_true hc
      obtain ⟨⟨i, k, pre, hpos, hSt, hDy⟩, -⟩ := (⟨hM, hle⟩ : _ ∧ _)
      rw [hSt.n2] at this
      exact ⟨⟨hM', by omega⟩, by omega⟩
  · intro σ ⟨hM, hle⟩
    rw [hcsize]
    have e : 1 + 5 + (108 * (2 ^ wd * W1) + 300) = 108 * (2 ^ wd * W1) + 306 := by ring
    rw [e]
    have h1 : 2 * J.jobs - (σ.vars "ip" + σ.vars "kp") ≤ 2 * J.jobs := Nat.sub_le _ _
    have := Nat.mul_le_mul_left (108 * (2 ^ wd * W1) + 306) h1
    omega
  · rintro σ σ' - ⟨⟨hM, hle⟩, hc⟩
    refine ⟨hM, ?_⟩
    have := loopCond_false hc
    obtain ⟨i, k, pre, hpos, hSt, hDy⟩ := hM
    rw [hSt.n2] at this
    omega

/-! ## The start of the sweep -/

open Lax496464Proofs.Ram.Corollary1Init (maxScan maxScan_spec)

/-- The set-up of the sweep: `cinf := maxd + 2`, `W1 := W + 1`, `n2 := 2n`, row `0` of the table
holds the empty selection, no mask, no slot, no event yet. -/
def initCore : Com :=
  .seq maxScan
    (.seq (.assign "W1" (.bin .add (V "W") (.lit 1)))
      (.seq (.assign "n2" (.bin .add (V "n") (V "n")))
        (.seq fillTB
          (.seq (.store "TB" (.lit 0) (.lit 0))
            (.seq (.store "PC" (.lit 0) (.lit 0))
              (.seq (.assign "MK" (.lit 1))
                (.seq (.assign "nx" (.lit 0))
                  (.seq (.assign "fp" (.lit 0))
                    (.seq (.assign "ip" (.lit 0)) (.assign "kp" (.lit 0)))))))))))

theorem maxScan_frame : (∀ y ∈ maxScan.wvars, y = "cinf" ∨ y = "mi" ∨ y = "mv") ∧
    maxScan.warrs = [] := by decide

theorem fillTB_frame : (∀ y ∈ fillTB.wvars, y = "ci") ∧ (∀ a ∈ fillTB.warrs, a = "TB") := by
  decide

theorem maxScan_spec' {B : ℕ} (hB : 1 < B) (DS : List ℕ) (n : ℕ) (hDSl : DS.length = n)
    (hDSB : ∀ v ∈ DS, v + 2 < B) (hnB : n + 2 < B) :
    Spec B (fun σ => σ.arrs "DS" = DS ∧ σ.vars "sn" = n) maxScan
      (fun σ σ' => (σ'.vars "cinf" = DS.foldr max 0 + 2 ∧ σ'.arrs "DS" = DS ∧ σ'.vars "sn" = n) ∧
        (∀ y, y ≠ "cinf" → y ≠ "mi" → y ≠ "mv" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (2 + (2 + ((50 + 4) * n + 6) + 4 + 4)) :=
  (maxScan_spec hB DS n hDSl hDSB hnB).frame.post fun σ σ' _ ⟨hq, hv, ha, _, _⟩ =>
    ⟨hq, fun y h1 h2 h3 => hv y (fun hy => by
        rcases maxScan_frame.1 y hy with h | h | h <;> contradiction),
      funext fun a => ha a (by rw [maxScan_frame.2]; simp)⟩

theorem fillTB_spec' {B : ℕ} (hB : 1 < B) (W1 INF : ℕ) (TB0 : List ℕ) (hW1B : W1 < B)
    (hINF : INF < B) (hW1L : W1 ≤ TB0.length) :
    Spec B (fun σ => σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "TB" = TB0) fillTB
      (fun σ σ' => ((σ'.arrs "TB").length = TB0.length ∧
        ∀ j, (σ'.arrs "TB").getD j 0 = if j < W1 then INF else TB0.getD j 0) ∧
        (∀ y, y ≠ "ci" → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a))
      ((20 + 4) * W1 + 6) :=
  (fillTB_spec hB W1 INF TB0 hW1B hINF hW1L).frame.post fun _σ _σ' _ ⟨hq, hv, ha, _, _⟩ =>
    ⟨hq, fun y h1 => hv y (fun hy => h1 (fillTB_frame.1 y hy)),
      fun a h1 => ha a (fun hy => h1 (fillTB_frame.2 a hy))⟩

theorem initCore_spec {B : ℕ} (hB : 1 < B) (DS TB0 PC0 : List ℕ) (N W : ℕ)
    (hDSB : ∀ v ∈ DS, v + 2 < B) (hDSl : DS.length = N) (hnB : 2 * N + 5 < B)
    (hWB : W + 2 < B) (hINFB : DS.foldr max 0 + 2 < B) (hW1L : W + 1 ≤ TB0.length)
    (hPCL : 0 < PC0.length) (_hle : ∀ j, TB0.getD j 0 ≤ DS.foldr max 0 + 2) :
    Spec B (fun σ => σ.arrs "DS" = DS ∧ σ.vars "sn" = N ∧ σ.vars "n" = N ∧ σ.vars "W" = W ∧
        σ.arrs "TB" = TB0 ∧ σ.arrs "PC" = PC0) initCore
      (fun _ σ' => σ'.vars "cinf" = DS.foldr max 0 + 2 ∧ σ'.vars "W1" = W + 1 ∧
        σ'.vars "n2" = N + N ∧ σ'.vars "MK" = 1 ∧ σ'.vars "nx" = 0 ∧ σ'.vars "fp" = 0 ∧
        σ'.vars "ip" = 0 ∧ σ'.vars "kp" = 0 ∧ σ'.vars "W" = W ∧ σ'.vars "n" = N ∧
        (σ'.arrs "TB").length = TB0.length ∧
        (∀ j, (σ'.arrs "TB").getD j 0 =
          if j = 0 then 0 else if j < W + 1 then DS.foldr max 0 + 2 else TB0.getD j 0) ∧
        σ'.arrs "PC" = PC0.set 0 0)
      (54 * N + 24 * (W + 1) + 120) := by
  refine Spec.of_exists fun σ ⟨hDS, hsn, hn, hW, hTB, hPC⟩ => ?_
  have hscan := maxScan_spec' (B := B) hB DS N hDSl hDSB (by omega)
  have hfill := fillTB_spec' (B := B) hB (W + 1) (DS.foldr max 0 + 2) TB0 (by omega) hINFB hW1L
  run_vcg [hscan, hfill]
  vcg_fin2
  rename_i hA hC
  obtain ⟨⟨hlen, hget⟩, -, -⟩ := hC
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [List.getElem?_set_self (by omega)]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hj), hget j]
    split_ifs <;> rfl

theorem foldr_dv (J : Instance) : ((List.range J.jobs).map (dv J)).foldr max 0 = maxd J := by
  unfold maxd
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    have hk : k < J.jobs := by simpa using h2
    simp [List.getElem_map, List.getElem_range, dv, hk]

theorem two_le_infOf (J : Instance) (j : J.Job) : J.d j + 2 ≤ infOf J := by
  have := d_le_maxd j
  unfold infOf; omega

/-- The machine right after `initCore` is in the sweep's invariant, with nothing done yet. -/
theorem mach_init {J : Instance} {W W1 LTB LPC LFS LSLT LP2 : ℕ} {σ σ' : Env}
    (hW1 : W1 = W + 1)
    (hm : σ.vars "m" = J.machines)
    (hps : σ.arrs "PS" = (List.range J.jobs).map (pv J))
    (hqs : σ.arrs "QS" = (List.range J.jobs).map (qv J))
    (hds : σ.arrs "DS" = (List.range J.jobs).map (dv J))
    (hws : σ.arrs "WS" = (List.range J.jobs).map (wv J))
    (hsa : σ.arrs "SA" = (dueOrder J).map Fin.val)
    (hltb : (σ.arrs "TB").length = LTB) (hlpc : (σ.arrs "PC").length = LPC)
    (hlfs : (σ.arrs "FS").length = LFS) (hlslt : (σ.arrs "SLT").length = LSLT)
    (hlp2 : (σ.arrs "P2").length = LP2)
    (hcinf : σ'.vars "cinf" = infOf J) (hW1' : σ'.vars "W1" = W + 1)
    (hn2 : σ'.vars "n2" = J.jobs + J.jobs) (hMK : σ'.vars "MK" = 1) (hnx : σ'.vars "nx" = 0)
    (hfp : σ'.vars "fp" = 0) (hip : σ'.vars "ip" = 0) (hkp : σ'.vars "kp" = 0)
    (hn : σ'.vars "n" = J.jobs)
    (hvars : ∀ y, y ∉ initCore.wvars → σ'.vars y = σ.vars y)
    (harrs : ∀ a, a ∉ initCore.warrs → σ'.arrs a = σ.arrs a)
    (hTBl : (σ'.arrs "TB").length = (σ.arrs "TB").length)
    (hTB : ∀ j, (σ'.arrs "TB").getD j 0 =
      if j = 0 then 0 else if j < W + 1 then infOf J else (σ.arrs "TB").getD j 0)
    (hTB0 : ∀ j, (σ.arrs "TB").getD j 0 ≤ infOf J)
    (hPC : σ'.arrs "PC" = (σ.arrs "PC").set 0 0) (hPCl : 0 < LPC) :
    Mach J (infOf J) W1 LTB LPC LFS LSLT LP2 σ' := by
  refine ⟨0, 0, [], Pos.zero, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hcinf, by rw [hW1', hW1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hn
    · rw [hn2]; omega
    · rw [hvars "m" (by decide)]; exact hm
    · rw [harrs "PS" (by decide)]; exact hps
    · rw [harrs "QS" (by decide)]; exact hqs
    · rw [harrs "DS" (by decide)]; exact hds
    · rw [harrs "WS" (by decide)]; exact hws
    · rw [harrs "SA" (by decide)]; exact hsa
    · rw [hTBl]; exact hltb
    · rw [hPC, List.length_set]; exact hlpc
    · rw [harrs "FS" (by decide)]; exact hlfs
    · rw [harrs "SLT" (by decide)]; exact hlslt
    · rw [harrs "P2" (by decide)]; exact hlp2
  · have hinit : tab J (infOf J) [] = St.init J (infOf J) := rfl
    rw [hinit]
    refine ⟨hip, hkp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hnx
    · show σ'.vars "fp" = ([] : List ℕ).length
      exact hfp
    · show σ'.vars "MK" = 2 ^ 0
      exact hMK
    · show ([] : List ℕ) = ((σ'.arrs "FS").take ([] : List ℕ).length).reverse
      simp
    · intro j hj; exact absurd hj (by omega)
    · intro b hb; exact absurd hb (by simp [St.init])
    · intro X hX
      have hX0 : X = 0 := by simpa [St.init] using hX
      subst hX0
      show (σ'.arrs "PC").getD 0 0 = pcnt 0
      rw [hPC, getD_set_self _ _ _ (by rw [hlpc]; exact hPCl)]
      simp [pcnt]
    · intro X hX c hc
      have hX0 : X = 0 := by simpa [St.init] using hX
      subst hX0
      simp only [tabOf, Nat.zero_mul, Nat.zero_add]
      rw [hTB c]
      by_cases hc0 : c = 0
      · subst hc0; simp [St.init]
      · simp [hc0, St.init]; omega
    · intro j
      rw [hTB j]
      split_ifs
      · exact Nat.zero_le _
      · exact le_rfl
      · exact hTB0 j

/-! ## The core -/

/-- **The sweep core**: set up, then do all the events. -/
def core : Com := .seq initCore sweepLoop

/-- The core's cost, for a sorted instance of `n` jobs, width bound `wd` and `W1 = W + 1`. -/
def Kcore (n wd W1 : ℕ) : ℕ :=
  (54 * n + 24 * W1 + 120) + ((108 * (2 ^ wd * W1) + 306) * (2 * n) + 6)

theorem core_warrs : ∀ a ∈ core.warrs, a ∈ ["TB", "PC", "FS", "SLT", "P2"] := by decide

theorem core_wvars_n : "n" ∉ core.wvars ∧ "sn" ∉ core.wvars ∧ "m" ∉ core.wvars ∧
    "W" ∉ core.wvars := by decide

open Classical in
set_option maxHeartbeats 4000000 in
/-- **The sweep core, correct.**  From the sorted arrays `PS QS DS WS SA` of the est-sorted
instance `J`, the threshold `W`, and any `TB` whose entries are at most `infOf J`, the core
leaves row `0` of `TB` holding the sweep's table: for every `c ≤ W`,
`TB[c] < infOf J ↔ HasWeight J c`. -/
theorem core_spec {B : ℕ} {J : Instance} {wd W W1 LTB LPC LFS LSLT LP2 : ℕ}
    (hW1 : W1 = W + 1) (hN : Nums J wd W1 (infOf J) B LTB LPC LFS LSLT LP2)
    (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (hwd : widthJ J ≤ wd) (hWB : W + 2 < B) :
    Spec B (fun σ => σ.vars "n" = J.jobs ∧ σ.vars "sn" = J.jobs ∧ σ.vars "m" = J.machines ∧
        σ.vars "W" = W ∧ σ.arrs "PS" = (List.range J.jobs).map (pv J) ∧
        σ.arrs "QS" = (List.range J.jobs).map (qv J) ∧
        σ.arrs "DS" = (List.range J.jobs).map (dv J) ∧
        σ.arrs "WS" = (List.range J.jobs).map (wv J) ∧
        σ.arrs "SA" = (dueOrder J).map Fin.val ∧
        (σ.arrs "TB").length = LTB ∧ (σ.arrs "PC").length = LPC ∧ (σ.arrs "FS").length = LFS ∧
        (σ.arrs "SLT").length = LSLT ∧ (σ.arrs "P2").length = LP2 ∧
        ∀ j, (σ.arrs "TB").getD j 0 ≤ infOf J) core
      (fun σ σ' => σ'.vars "cinf" = infOf J ∧ σ'.vars "W1" = W + 1 ∧ σ'.vars "W" = W ∧
        σ'.vars "n" = J.jobs ∧ σ'.vars "sn" = J.jobs ∧ σ'.vars "m" = J.machines ∧
        (∀ c, c ≤ W → ((σ'.arrs "TB").getD c 0 < infOf J ↔ HasWeight J c)) ∧
        (∀ j, (σ'.arrs "TB").getD j 0 ≤ infOf J) ∧
        (∀ a, (σ'.arrs a).length = (σ.arrs a).length) ∧
        (∀ a, a ∉ ["TB", "PC", "FS", "SLT", "P2"] → σ'.arrs a = σ.arrs a))
      (Kcore J.jobs wd W1) := by
  refine Spec.of_exists fun σ ⟨hn, hsn, hm, hW, hps, hqs, hds, hws, hsa, hltb, hlpc, hlfs, hlslt,
    hlp2, hTBle⟩ => ?_
  have hnB := hN.nB
  have hinfeq : (σ.arrs "DS").foldr max 0 + 2 = infOf J := by rw [hds, foldr_dv]; rfl
  have hDSB : ∀ v ∈ σ.arrs "DS", v + 2 < B := by
    intro v hv
    rw [hds] at hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    have hj' : j < J.jobs := List.mem_range.mp hj
    have := two_le_infOf J ⟨j, hj'⟩
    have := hN.infB
    simp only [dv, hj', dif_pos]; omega
  have hdsl : (σ.arrs "DS").length = J.jobs := by rw [hds]; simp
  have hW1L : W + 1 ≤ (σ.arrs "TB").length := by
    rw [hltb]
    have := hN.tbL
    have h2 : W1 ≤ 2 ^ wd * W1 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have hPCl : 0 < (σ.arrs "PC").length := by
    rw [hlpc]; have := hN.pcL; have := Nat.two_pow_pos wd; omega
  obtain ⟨σ1, hr1, ⟨hcinf, hW1', hn2, hMK, hnx, hfp, hip, hkp, hW', hn', hTBl, hTB, hPC⟩, hfv1, hfa1,
    -, -⟩ :=
    (initCore_spec (B := B) hN.hB (σ.arrs "DS") (σ.arrs "TB") (σ.arrs "PC") J.jobs W hDSB hdsl
      (by omega) hWB (by rw [hinfeq]; exact hN.infB) hW1L hPCl
      (by rw [hinfeq]; exact hTBle)).frame.run ⟨rfl, hsn, hn, hW, rfl, rfl⟩
  rw [hinfeq] at hcinf hTB
  have hM1 : Mach J (infOf J) W1 LTB LPC LFS LSLT LP2 σ1 :=
    mach_init hW1 hm hps hqs hds hws hsa hltb hlpc hlfs hlslt hlp2 hcinf hW1' hn2 hMK hnx hfp
      hip hkp hn' hfv1 hfa1 hTBl hTB hTBle hPC (by rw [← hlpc]; exact hPCl)
  obtain ⟨σ2, hr2, hM2, hsum⟩ := (sweepLoop_spec hN hE hq hwd).run ⟨hM1, by omega⟩
  have hrall : Run B core σ σ2 _ := hr1.seq hr2
  obtain ⟨i, k, pre, hpos, hSt2, hDy2⟩ := hM2
  have hik : i + k = 2 * J.jobs := by rw [← hDy2.ip, ← hDy2.kp]; exact hsum
  have hpre : pre = evs J := pos_final hpos hik
  subst hpre
  obtain ⟨hcn, hcs, hcm, hcW⟩ := core_wvars_n
  refine ⟨σ2, _, hrall.mono ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Kcore; omega
  · rw [hSt2.cinf]
  · rw [hSt2.w1, hW1]
  · rw [hrall.frame_var "W" hcW]; exact hW
  · rw [hrall.frame_var "n" hcn]; exact hn
  · rw [hrall.frame_var "sn" hcs]; exact hsn
  · rw [hrall.frame_var "m" hcm]; exact hm
  · intro c hc
    have hX : (0 : ℕ) < 2 ^ (tab J (infOf J) (evs J)).next := Nat.two_pow_pos _
    have := hDy2.tb 0 hX c (by omega)
    simp only [tabOf, Nat.zero_mul, Nat.zero_add] at this
    rw [this]
    exact sweep_correct_maxd hE hq c
  · exact hDy2.tbLe
  · exact Lax496464Proofs.Ram.Corollary1Prog.run_arrs_length_eq hrall
  · intro a ha
    exact hrall.frame_arr a (fun h => ha (core_warrs a h))

end Lax496464Proofs.Ram.W3Sweep
