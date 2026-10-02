import Lax496464Proofs.Ram.D4Tab
import Lax496464Proofs.Ram.D4Row
import Lax496464Proofs.Ram.D2Step

/-!
# Corollary 2's Machine: One Number of the Main Loop (Dual Table)

The same loop as `D2Step`, with the table of width `R + 1` (rows `t = 0 … R`, `R = P`), the cell of
`D4Row`, and the invariant `D4Tab.DInv`.  The block of the empty set is all zero, so the top number
only records that it is a code.  Costs are those of `D2Step` at `W := R` (`turnCost n m R`).
-/

namespace Lax496464Proofs.Ram.D4Step

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.D2Scan1 Lax496464Proofs.Ram.D2Valid1
open Lax496464Proofs.Ram.D2StepPure
open Lax496464Proofs.Ram.D2Step (turnCost blockCost loopWork scanCom_wvars scanCom_warrs scanCom_spec'
  mul_step_lt mul_step_le lenOf_cons vphase_wvars vphase_warrs)
open Lax496464Proofs.Ram.D3Dual (dcap DTabOK GoodF)
open Lax496464Proofs.Ram.D4Row Lax496464Proofs.Ram.D4Tab
open Lax496464Proofs.Ram.Dp1 (IsNxt pv qv dv nxt_gt)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- Everything about the sorted instance and the machine's arrays that does not change while the
table is filled. -/
structure SC4 (J : Instance) (B n m W R : ℕ) (PSl QSl DSl WSl NXl PWl : List ℕ) : Prop where
  hB : 2 < B
  hn : J.jobs = n
  hm : 1 ≤ m
  hest : EstOrdered J
  hq : ∀ i : J.Job, 0 < J.q i
  lenPS : PSl.length = n
  lenQS : QSl.length = n
  lenDS : DSl.length = n
  lenWS : WSl.length = n
  lenNX : NXl.length = n
  PS : ∀ k < n, PSl.getD k 0 = pv J k
  QS : ∀ k < n, QSl.getD k 0 = qv J k
  DS : ∀ k < n, DSl.getD k 0 = dv J k
  WS : ∀ k < n, WSl.getD k 0 = wv J k
  NX : ∀ (j : ℕ) (h : j < J.jobs), IsNxt j h (NXl.getD j 0)
  lenPW : PWl.length = m + 1
  PW : ∀ i ≤ m, PWl.getD i 0 = (n + 1) ^ i
  bpw : ∀ i ≤ m, (n + 1) ^ i < B
  bm : m < B
  bn : n + 2 < B
  bW : W + 2 < B
  bR : (n + 1) ^ m * (R + 1) < B
  bp : ∀ k < n, R + pv J k + qv J k + 1 < B
  bd : ∀ k < n, dv J k + 1 < B
  bw : ∀ k < n, wv J k + W < B

/-- The scalars and arrays the loop never changes. -/
def Stat4 (n m W R : ℕ) (PSl QSl DSl WSl NXl PWl : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "nb" = n + 1 ∧ σ.vars "R" = R + 1 ∧
  σ.vars "N" = (n + 1) ^ m ∧ σ.vars "W" = W ∧
  σ.arrs "PS" = PSl ∧ σ.arrs "QS" = QSl ∧ σ.arrs "DS" = DSl ∧ σ.arrs "WS" = WSl ∧
  σ.arrs "NX" = NXl ∧ σ.arrs "PW" = PWl

/-- The block of a number that is a code: two scans, and the cells. -/
def stepIsCode4 : Com :=
  .seq (.assign "zj" (V "zx1"))
    (.seq (.assign "zy" (.bin .add (V "zj") (.lit 1)))
      (.seq scanCom
        (.seq (.assign "zb1" (.bin .mul (V "zcode") (V "R")))
          (.seq (.assign "zy" (.get "NX" (V "zj")))
            (.seq scanCom
              (.seq (.assign "zb2" (.bin .mul (V "zcode") (V "R")))
                (.seq (.assign "zbc" (.bin .mul (V "zc") (V "R")))
                  (.seq (.assign "wj" (.get "WS" (V "zj")))
                    (.seq (.assign "cd" (.get "DS" (V "zj")))
                      (.seq (.assign "cq" (.get "QS" (V "zj")))
                        (.seq (.assign "cp" (.get "PS" (V "zj"))) rowsLoop4)))))))))))

theorem stepIsCode4_warrs : ∀ a ∈ stepIsCode4.warrs, a = "TAB" := by decide

set_option maxHeartbeats 4000000 in
theorem stepIsCode4_core {J : Instance} {B n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC4 J B n m W R PSl QSl DSl WSl NXl PWl) {c j : ℕ} {Zs : List ℕ} {T : List ℕ}
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c)
    (hT : DInv J n m W R ((n + 1) ^ m) (c + 1) T) :
    Spec B (fun σ => Stat4 n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.vars "zx1" = j ∧ σ.arrs "TAB" = T) stepIsCode4
      (fun _σ σ' => ∃ T', σ'.arrs "TAB" = T' ∧ DInv J n m W R ((n + 1) ^ m) c T')
      (2 * (64 * (Zs.length + 1) + 110) + ((100 + 4) * (R + 1) + 6) + 60) := by
  have hB := sc.hB
  have hn := sc.hn
  have hm := sc.hm
  have hest := sc.hest
  have hq := sc.hq
  have lPS := sc.lenPS
  have lQS := sc.lenQS
  have lDS := sc.lenDS
  have lWS := sc.lenWS
  have lNX := sc.lenNX
  have ePS := sc.PS
  have eQS := sc.QS
  have eDS := sc.DS
  have eWS := sc.WS
  have eNX := sc.NX
  have lPW := sc.lenPW
  have ePW := sc.PW
  have bpw := sc.bpw
  have bm := sc.bm
  have bn := sc.bn
  have bW := sc.bW
  have bR := sc.bR
  have bp := sc.bp
  have bd := sc.bd
  have bw := sc.bw
  have hjn : j < n := hsl.lt j (by simp)
  have hjJ : j < J.jobs := by rw [hn]; exact hjn
  have hcN : c < (n + 1) ^ m := by rw [← hcode]; exact hsl.codeL_lt
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) bR
  have hRB : R + 1 < B :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) bR
  have hTlen : T.length = (n + 1) ^ m * (R + 1) := hT.1.1
  have hcodeR : ∀ c', c' < (n + 1) ^ m → c' * (R + 1) < B := fun c' hc' =>
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hc'.le) bR
  have hnB : n + 1 < B := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩, hzc0, hzx10, hT0⟩ := hσ
  -- 1: zj := zx1
  have hzx1B : σ.vars "zx1" < B := by rw [hzx10]; omega
  have r1 := Run.assign (B := B) (σ := σ) (x := "zj") (e := V "zx1") (v := j)
    (by rw [evalB_var hzx1B, hzx10])
  set σ1 : Env := σ.setVar "zj" j with hσ1
  clear_value σ1
  -- 2: zy := zj + 1
  have hvj1 : (V "zj").evalB B σ1 = some j := by
    have : σ1.vars "zj" = j := by simp [hσ1]
    exact this ▸ evalB_var (by rw [this]; omega)
  have r2 := Run.assign (B := B) (σ := σ1) (x := "zy") (e := .bin .add (V "zj") (.lit 1))
    (v := j + 1) (evalB_bin hvj1 (evalB_lit (by omega)) (by show j + 1 < B; omega))
  set σ2 : Env := σ1.setVar "zy" (j + 1) with hσ2
  clear_value σ2
  -- 3: the first scan
  obtain ⟨σ3, hr3, hcode3, hfv3, hfa3⟩ :=
    (scanCom_spec' (B := B) (by omega) n m j (j + 1) Zs PWl hsl hm (by omega) lPW ePW hNB bm).run
      (σ := σ2)
      ⟨by simp [hσ2, hσ1, hzc0, hcode], by simp [hσ2, hσ1, hnb0], by simp [hσ2, hσ1, hn0],
       by simp [hσ2, hσ1, hm0], by simp [hσ2, hσ1, hPW0], by simp [hσ2]⟩
  obtain ⟨cur1, k1, hs1⟩ : ∃ cur k, scanF n (lstOf n (m - 1) Zs) (j + 1) = (cur, k) :=
    ⟨_, _, rfl⟩
  rw [hs1] at hcode3
  simp only at hcode3
  have hTsl : SL n (m - 1) Zs := sl_tail hsl
  have hok1 : ScanOK n Zs (j + 1) (cur1, k1) := by
    have := scanF_ok n Zs (m - 1 - Zs.length) (j + 1) (List.sortedLT_iff_pairwise.mp hTsl.sorted)
      hTsl.lt (by omega)
    have h2 : lstOf n (m - 1) Zs = Zs ++ List.replicate (m - 1 - Zs.length) n := rfl
    rw [← h2, hs1] at this; exact this
  have hsl1 := newL_sl hm hTsl hok1
  have hcode1B : codeL n m (newL n Zs cur1 k1) < (n + 1) ^ m := hsl1.codeL_lt
  have hzb1B : codeL n m (newL n Zs cur1 k1) * (R + 1) < B := hcodeR _ hcode1B
  -- 4: zb1 := zcode * R
  have hvcode3 : (V "zcode").evalB B σ3 = some (codeL n m (newL n Zs cur1 k1)) := by
    rw [← hcode3]; exact evalB_var (by rw [hcode3]; omega)
  have hvR3 : (V "R").evalB B σ3 = some (R + 1) := by
    have : σ3.vars "R" = R + 1 := by
      rw [hfv3 "R" (by decide)]; simp [hσ2, hσ1, hR0]
    exact this ▸ evalB_var (by rw [this]; omega)
  have r4 := Run.assign (B := B) (σ := σ3) (x := "zb1") (e := .bin .mul (V "zcode") (V "R"))
    (v := codeL n m (newL n Zs cur1 k1) * (R + 1)) (evalB_bin hvcode3 hvR3 hzb1B)
  set σ4 : Env := σ3.setVar "zb1" (codeL n m (newL n Zs cur1 k1) * (R + 1)) with hσ4
  clear_value σ4
  -- 5: zy := NX[zj]
  have hzj4 : σ4.vars "zj" = j := by
    simp [hσ4]; rw [hfv3 "zj" (by decide)]; simp [hσ2, hσ1]
  have hvj4 : (V "zj").evalB B σ4 = some j := hzj4 ▸ evalB_var (by rw [hzj4]; omega)
  have hNX4 : σ4.arrs "NX" = NXl := by
    simp only [hσ4, arrs_setVar]; rw [hfa3]; simp [hσ2, hσ1, hNX0]
  have hnx := eNX j hjJ
  have hy0 : NXl.getD j 0 ≤ n := by
    rcases hnx.1 with ⟨hy, -⟩ | h
    · rw [hn] at hy; exact hy.le
    · rw [h, hn]
  have r5 := Run.assign (B := B) (σ := σ4) (x := "zy") (e := .get "NX" (V "zj"))
    (v := NXl.getD j 0)
    (by
      have := RunStep.eval_get B σ4 "NX" (V "zj") j hvj4 (by rw [hNX4]; omega)
        (by rw [hNX4]; omega)
      rwa [hNX4] at this)
  set σ5 : Env := σ4.setVar "zy" (NXl.getD j 0) with hσ5
  clear_value σ5
  -- 6: the second scan
  obtain ⟨σ6, hr6, hcode6, hfv6, hfa6⟩ :=
    (scanCom_spec' (B := B) (by omega) n m j (NXl.getD j 0) Zs PWl hsl hm hy0 lPW ePW hNB bm).run
      (σ := σ5)
      ⟨by simp [hσ5, hσ4]; rw [hfv3 "zc" (by decide)]; simp [hσ2, hσ1, hzc0, hcode],
       by simp [hσ5, hσ4]; rw [hfv3 "nb" (by decide)]; simp [hσ2, hσ1, hnb0],
       by simp [hσ5, hσ4]; rw [hfv3 "n" (by decide)]; simp [hσ2, hσ1, hn0],
       by simp [hσ5, hσ4]; rw [hfv3 "m" (by decide)]; simp [hσ2, hσ1, hm0],
       by simp only [hσ5, arrs_setVar]; simp only [hσ4, arrs_setVar]; rw [hfa3]; simp [hσ2, hσ1, hPW0],
       by simp [hσ5]⟩
  obtain ⟨cur2, k2, hs2⟩ : ∃ cur k, scanF n (lstOf n (m - 1) Zs) (NXl.getD j 0) = (cur, k) :=
    ⟨_, _, rfl⟩
  rw [hs2] at hcode6
  simp only at hcode6
  have hok2 : ScanOK n Zs (NXl.getD j 0) (cur2, k2) := by
    have := scanF_ok n Zs (m - 1 - Zs.length) (NXl.getD j 0) (List.sortedLT_iff_pairwise.mp hTsl.sorted)
      hTsl.lt hy0
    have h2 : lstOf n (m - 1) Zs = Zs ++ List.replicate (m - 1 - Zs.length) n := rfl
    rw [← h2, hs2] at this; exact this
  have hsl2 := newL_sl hm hTsl hok2
  have hcode2B : codeL n m (newL n Zs cur2 k2) < (n + 1) ^ m := hsl2.codeL_lt
  have hzb2B : codeL n m (newL n Zs cur2 k2) * (R + 1) < B := hcodeR _ hcode2B
  -- 7: zb2 := zcode * R
  have hvcode6 : (V "zcode").evalB B σ6 = some (codeL n m (newL n Zs cur2 k2)) := by
    rw [← hcode6]; exact evalB_var (by rw [hcode6]; omega)
  have hR6 : σ6.vars "R" = R + 1 := by
    rw [hfv6 "R" (by decide)]; simp [hσ5, hσ4]; rw [hfv3 "R" (by decide)]; simp [hσ2, hσ1, hR0]
  have hvR6 : (V "R").evalB B σ6 = some (R + 1) := hR6 ▸ evalB_var (by rw [hR6]; omega)
  have r7 := Run.assign (B := B) (σ := σ6) (x := "zb2") (e := .bin .mul (V "zcode") (V "R"))
    (v := codeL n m (newL n Zs cur2 k2) * (R + 1)) (evalB_bin hvcode6 hvR6 hzb2B)
  set σ7 : Env := σ6.setVar "zb2" (codeL n m (newL n Zs cur2 k2) * (R + 1)) with hσ7
  clear_value σ7
  -- 8: zbc := zc * R
  have hzc7 : σ7.vars "zc" = c := by
    simp [hσ7]; rw [hfv6 "zc" (by decide)]; simp [hσ5, hσ4]; rw [hfv3 "zc" (by decide)]
    simp [hσ2, hσ1, hzc0]
  have hvc7 : (V "zc").evalB B σ7 = some c := hzc7 ▸ evalB_var (by rw [hzc7]; omega)
  have hvR7 : (V "R").evalB B σ7 = some (R + 1) := by
    have : σ7.vars "R" = R + 1 := by simp [hσ7, hR6]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hcRB := hcodeR c hcN
  have r8 := Run.assign (B := B) (σ := σ7) (x := "zbc") (e := .bin .mul (V "zc") (V "R"))
    (v := c * (R + 1)) (evalB_bin hvc7 hvR7 hcRB)
  set σ8 : Env := σ7.setVar "zbc" (c * (R + 1)) with hσ8
  clear_value σ8
  -- 9-12: the job's numbers
  have hzj8 : σ8.vars "zj" = j := by
    simp [hσ8, hσ7]; rw [hfv6 "zj" (by decide)]; simp [hσ5, hσ4]; rw [hfv3 "zj" (by decide)]
    simp [hσ2, hσ1]
  have hvj8 : (V "zj").evalB B σ8 = some j := hzj8 ▸ evalB_var (by rw [hzj8]; omega)
  have hA8 : ∀ a, σ8.arrs a = σ.arrs a := by
    intro a
    simp only [hσ8, hσ7, arrs_setVar]
    rw [hfa6]; simp only [hσ5, hσ4, arrs_setVar]; rw [hfa3]; simp [hσ2, hσ1]
  have hWS8 : σ8.arrs "WS" = WSl := by rw [hA8 "WS", hWS0]
  have hDS8 : σ8.arrs "DS" = DSl := by rw [hA8 "DS", hDS0]
  have hQS8 : σ8.arrs "QS" = QSl := by rw [hA8 "QS", hQS0]
  have hPS8 : σ8.arrs "PS" = PSl := by rw [hA8 "PS", hPS0]
  have hwj := ePS
  have r9 := Run.assign (B := B) (σ := σ8) (x := "wj") (e := .get "WS" (V "zj")) (v := WSl.getD j 0)
    (by
      have := RunStep.eval_get B σ8 "WS" (V "zj") j hvj8 (by rw [hWS8]; omega)
        (by rw [hWS8, eWS j hjn]; have := bw j hjn; omega)
      rwa [hWS8] at this)
  set σ9 : Env := σ8.setVar "wj" (WSl.getD j 0) with hσ9
  clear_value σ9
  have hvj9 : (V "zj").evalB B σ9 = some j := by
    have : σ9.vars "zj" = j := by simp [hσ9, hzj8]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hDS9 : σ9.arrs "DS" = DSl := by rw [hσ9]; simp only [arrs_setVar]; exact hDS8
  have hbdj := bd j hjn
  have r10 := Run.assign (B := B) (σ := σ9) (x := "cd") (e := .get "DS" (V "zj")) (v := DSl.getD j 0)
    (by
      have := RunStep.eval_get B σ9 "DS" (V "zj") j hvj9 (by rw [hDS9]; omega)
        (by rw [hDS9, eDS j hjn]; omega)
      rwa [hDS9] at this)
  set σ10 : Env := σ9.setVar "cd" (DSl.getD j 0) with hσ10
  clear_value σ10
  have hvj10 : (V "zj").evalB B σ10 = some j := by
    have : σ10.vars "zj" = j := by simp [hσ10, hσ9, hzj8]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hQS10 : σ10.arrs "QS" = QSl := by rw [hσ10, hσ9]; simp only [arrs_setVar]; exact hQS8
  have hbpj := bp j hjn
  have hpqj : pv J j + qv J j < B := by omega
  have r11 := Run.assign (B := B) (σ := σ10) (x := "cq") (e := .get "QS" (V "zj")) (v := QSl.getD j 0)
    (by
      have := RunStep.eval_get B σ10 "QS" (V "zj") j hvj10 (by rw [hQS10]; omega)
        (by rw [hQS10, eQS j hjn]; omega)
      rwa [hQS10] at this)
  set σ11 : Env := σ10.setVar "cq" (QSl.getD j 0) with hσ11
  clear_value σ11
  have hvj11 : (V "zj").evalB B σ11 = some j := by
    have : σ11.vars "zj" = j := by simp [hσ11, hσ10, hσ9, hzj8]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hPS11 : σ11.arrs "PS" = PSl := by rw [hσ11, hσ10, hσ9]; simp only [arrs_setVar]; exact hPS8
  have r12 := Run.assign (B := B) (σ := σ11) (x := "cp") (e := .get "PS" (V "zj")) (v := PSl.getD j 0)
    (by
      have := RunStep.eval_get B σ11 "PS" (V "zj") j hvj11 (by rw [hPS11]; omega)
        (by rw [hPS11, ePS j hjn]; omega)
      rwa [hPS11] at this)
  set σ12 : Env := σ11.setVar "cp" (PSl.getD j 0) with hσ12
  clear_value σ12
  -- 13: the cells
  have hc1 : c < codeL n m (newL n Zs cur1 k1) :=
    newcode_gt hm hsl hcode (by omega) (by omega) hs1
  have hc2 : c < codeL n m (newL n Zs cur2 k2) :=
    newcode_gt hm hsl hcode (nxt_gt hest hq hjJ hnx) hy0 hs2
  have hT12 : σ12.arrs "TAB" = T := by
    have := hA8 "TAB"
    simp only [hσ12, hσ11, hσ10, hσ9, arrs_setVar]; rw [this, hT0]
  have hb1 : σ12.vars "zb1" = codeL n m (newL n Zs cur1 k1) * (R + 1) := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]; rw [hfv6 "zb1" (by decide)]; simp [hσ5, hσ4]
  have hb2 : σ12.vars "zb2" = codeL n m (newL n Zs cur2 k2) * (R + 1) := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]
  have hbc : σ12.vars "zbc" = c * (R + 1) := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8]
  have hwj12 : σ12.vars "wj" = WSl.getD j 0 := by
    simp [hσ12, hσ11, hσ10, hσ9]
  have hcd12 : σ12.vars "cd" = DSl.getD j 0 := by
    simp [hσ12, hσ11, hσ10]
  have hcq12 : σ12.vars "cq" = QSl.getD j 0 := by
    simp [hσ12, hσ11]
  have hcp12 : σ12.vars "cp" = PSl.getD j 0 := by
    simp [hσ12]
  have hW12 : σ12.vars "W" = W := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]; rw [hfv6 "W" (by decide)]
    simp [hσ5, hσ4]; rw [hfv3 "W" (by decide)]; simp [hσ2, hσ1, hinf0]
  have hR12 : σ12.vars "R" = R + 1 := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hR6]
  have hpj : PSl.getD j 0 = pv J j := ePS j hjn
  have hqj : QSl.getD j 0 = qv J j := eQS j hjn
  have hdj : DSl.getD j 0 = dv J j := eDS j hjn
  have hwjj : WSl.getD j 0 = wv J j := eWS j hjn
  have hdB : DSl.getD j 0 + 1 < B := by rw [hdj]; exact hbdj
  have hqB : QSl.getD j 0 < B := by rw [hqj]; have := hpqj; omega
  have hpB : PSl.getD j 0 < B := by rw [hpj]; have := hpqj; omega
  have hpq : PSl.getD j 0 + QSl.getD j 0 < B := by rw [hpj, hqj]; exact hpqj
  have hwB : WSl.getD j 0 < B := by rw [hwjj]; have := bw j hjn; omega
  have hwW : WSl.getD j 0 + W < B := by rw [hwjj]; exact bw j hjn
  have hrp : R + PSl.getD j 0 + QSl.getD j 0 + 1 < B := by rw [hpj, hqj]; exact hbpj
  have hWB : W + 1 < B := by omega
  have hNR : ((n + 1) ^ m) * (R + 1) < B := bR
  have hrep1 : ∀ r, r < R + 1 → T.getD (codeL n m (newL n Zs cur1 k1) * (R + 1) + r) 0 ≤ W :=
    fun r _ => hT.2 _
  have hrep2 : ∀ r, r < R + 1 → T.getD (codeL n m (newL n Zs cur2 k2) * (R + 1) + r) 0 ≤ W :=
    fun r _ => hT.2 _
  obtain ⟨σ13, hr13, hlen13, hout13, hcell13, -, -⟩ :=
    (rowsLoop4_spec (B := B) hB W R (DSl.getD j 0) (QSl.getD j 0) (PSl.getD j 0) (WSl.getD j 0)
      (codeL n m (newL n Zs cur1 k1) * (R + 1)) (codeL n m (newL n Zs cur2 k2) * (R + 1))
      (c * (R + 1)) ((n + 1) ^ m * (R + 1)) T hWB hwW hdB hqB hpB hrp hwB hNR hRB hTlen
      (mul_step_lt hc1) (mul_step_lt hc2) (mul_step_le hcode1B) (mul_step_le hcode2B)
      (mul_step_le hcN) hrep1 hrep2).run
      (σ := σ12) ⟨hT12, hb1, hb2, hbc, hwj12, hW12, hcd12, hcq12, hcp12, hR12⟩
  have hpv : pv J j = J.p ⟨j, hjJ⟩ := by unfold pv; rw [dif_pos hjJ]
  have hqv : qv J j = J.q ⟨j, hjJ⟩ := by unfold qv; rw [dif_pos hjJ]
  have hdv : dv J j = J.d ⟨j, hjJ⟩ := by unfold dv; rw [dif_pos hjJ]
  have hwv : wv J j = J.w ⟨j, hjJ⟩ := by unfold wv; rw [dif_pos hjJ]
  have hcellJ : ∀ r, r ≤ R → (σ13.arrs "TAB").getD (c * (R + 1) + r) 0 =
      Lax496464Proofs.Ram.D3Dual.dStep W R (J.p ⟨j, hjJ⟩) (J.q ⟨j, hjJ⟩) (J.d ⟨j, hjJ⟩)
        (J.w ⟨j, hjJ⟩) r (T.getD (codeL n m (newL n Zs cur1 k1) * (R + 1) + r) 0)
        (T.getD (codeL n m (newL n Zs cur2 k2) * (R + 1) + (r + J.p ⟨j, hjJ⟩)) 0) := by
    intro r hr
    have := hcell13 r (by omega)
    unfold cellVal4 at this
    rw [hdj, hqj, hpj, hwjj, hdv, hqv, hpv, hwv] at this
    exact this
  have hTab' : DInv J n m W R ((n + 1) ^ m) c (σ13.arrs "TAB") := by
    refine dinv_step rfl hT hlen13 ?_ ?_ ?_
    · intro i hi hne
      have hlt : i < c * (R + 1) ∨ c * (R + 1) + (R + 1) ≤ i := by
        by_contra hcon
        push Not at hcon
        apply hne
        apply Nat.div_eq_of_lt_le hcon.1 (by rw [Nat.add_mul, Nat.one_mul]; omega)
      exact hout13 i hi (by omega)
    · intro Zs0 hsl0 hc0 t ht hgood
      have hZ : Zs0 = j :: Zs := SL.codeL_inj hsl0 hsl (hc0.trans hcode.symm)
      subst hZ
      exact dblock hn hm hest hq hT.1 hsl hcode hjJ hnx hs1 hs2 hcellJ t ht hgood
    · intro i hi hic
      have hlo : c * (R + 1) ≤ i := by
        have := Nat.div_mul_le_self i (R + 1)
        rw [hic] at this; exact this
      have hhi : i < c * (R + 1) + (R + 1) := by
        have := Nat.lt_div_mul_add (a := i) (b := R + 1) (by omega)
        rw [hic] at this; omega
      have hi' : i = c * (R + 1) + (i - c * (R + 1)) := by omega
      rw [hi', hcell13 (i - c * (R + 1)) (by omega)]
      unfold cellVal4
      exact dStep_le (hT.2 _)
  have hrun : Run B stepIsCode4 σ σ13 _ :=
    Run.seq r1 <| Run.seq r2 <| Run.seq hr3 <| Run.seq r4 <| Run.seq r5 <| Run.seq hr6 <|
    Run.seq r7 <| Run.seq r8 <| Run.seq r9 <| Run.seq r10 <| Run.seq r11 <| Run.seq r12 hr13
  exact ⟨σ13, _, hrun.mono (by simp only [Expr.size]; omega), le_rfl, _, rfl, hTab'⟩


/-! ## The two kinds of number -/

/-- The top number, the code of the empty set: its block is zero, it is a code. -/
def topCom4 : Com := .store "VALID" (V "zc") (.lit 1)

theorem topCom4_spec {J : Instance} {B n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC4 J B n m W R PSl QSl DSl WSl NXl PWl) {c : ℕ} (hc : c + 1 = (n + 1) ^ m)
    {T Vl : List ℕ} (hT : DInv J n m W R ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => Stat4 n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) topCom4
      (fun _σ σ' => DInv J n m W R ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID")) 20 := by
  classical
  have hB := sc.hB
  have hcN : c < (n + 1) ^ m := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨-, hzc0, hT0, hV0⟩ := hσ
  have hvc : (V "zc").evalB B σ = some c := by
    have hcB : c < B := lt_of_lt_of_le hcN (by
      have := sc.bR
      calc (n + 1) ^ m ≤ (n + 1) ^ m * (R + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ B := this.le)
    exact hzc0 ▸ evalB_var (by rw [hzc0]; exact hcB)
  have hidx : c < (σ.arrs "VALID").length := by rw [hV0, hV.1]; exact hcN
  have r2 := Run.store (B := B) (σ := σ) (a := "VALID") (i := V "zc") (e := .lit 1)
    (idx := c) (v := 1) hvc (evalB_lit (by omega)) hidx
  refine ⟨σ.setArr "VALID" c 1, _, r2.mono (by simp only [Expr.size]; omega), le_rfl, ?_, ?_⟩
  · have := dinv_step_empty (J := J) (n := n) (m := m) (W := W) (R := R) (N := (n + 1) ^ m)
      (c := c) (T := T) rfl (by omega) hT
    have h2 : (σ.setArr "VALID" c 1).arrs "TAB" = T := by simp [hT0]
    rw [h2]; exact this
  · have hval := valid_step (n := n) (m := m) (N := (n + 1) ^ m) (c := c) (v := 1) (V := Vl) hV hcN
      (by
        have hcode : IsCode n m c := ⟨[], sl_nil n m, by rw [codeL_nil]; omega⟩
        rw [if_pos hcode])
    have h2 : (σ.setArr "VALID" c 1).arrs "VALID" = Vl.set c 1 := by
      simp [hV0]
    rw [h2]; exact hval

/-- A number that is not the top one: decide whether it is a code, and if it is, fill its cells. -/
def stepCom4 : Com :=
  .seq vphase (.ite (.eq (.get "VALID" (V "zc")) (.lit 1)) stepIsCode4 .skip)


set_option maxHeartbeats 4000000 in
theorem stepCom4_spec {J : Instance} {B n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC4 J B n m W R PSl QSl DSl WSl NXl PWl) {c : ℕ} (hc : c + 1 < (n + 1) ^ m)
    {T Vl : List ℕ} (hT : DInv J n m W R ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => Stat4 n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) stepCom4
      (fun _σ σ' => DInv J n m W R ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID"))
      (500 + blockCost n m R c) := by
  classical
  have hB := sc.hB
  have hbR := sc.bR
  have hbW := sc.bW
  have hm := sc.hm
  have hcN : c < (n + 1) ^ m := by omega
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hbR
  have hsuf : sufc n m c < (n + 1) ^ m := sufc_lt_pow hm
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩, hzc0, hT0, hV0⟩ := hσ
  obtain ⟨σ1, hr1, ⟨hVal1, hx11⟩, hfv1, hfa1, -, -⟩ :=
    (vphase_spec (B := B) (by omega) n m c PWl Vl hm sc.lenPW sc.PW (lt_trans hcN hNB) sc.bpw
      (lt_trans hsuf hNB) (by have := sc.bn; omega) sc.bm (by rw [hV.1]; exact hsuf)
      (by rw [hV.1]; exact hcN)
      (fun i => by have := hV.2.2 i; omega)).frame.run (σ := σ)
      ⟨hzc0, hnb0, hn0, hm0, hPW0, hV0⟩
  have hviff := valid_iff hm rfl hc hV
  have hv : (if x1 n m c < x2 n m c ∧ Vl.getD (sufc n m c) 0 = 1 then 1 else 0) =
      (if IsCode n m c then 1 else 0) := by
    by_cases h : IsCode n m c
    · rw [if_pos (hviff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hviff.mp h')), if_neg h]
  rw [hv] at hVal1
  have hzc1 : σ1.vars "zc" = c := by rw [hfv1 "zc" (by decide)]; exact hzc0
  have hT1 : σ1.arrs "TAB" = T := by rw [hfa1 "TAB" (fun h => absurd (vphase_warrs "TAB" h) (by decide))]; exact hT0
  have hVok1 := valid_step (n := n) (m := m) (N := (n + 1) ^ m) (c := c) (v := if IsCode n m c then 1 else 0)
    (V := Vl) hV hcN rfl
  have hV1 : ValidOK n m ((n + 1) ^ m) c (σ1.arrs "VALID") := by rw [hVal1]; exact hVok1
  have hvcond : ∀ σ' : Env, σ'.vars "zc" = c → σ'.arrs "VALID" = Vl.set c (if IsCode n m c then 1 else 0) →
      (Expr.get "VALID" (V "zc")).evalB B σ' = some (if IsCode n m c then 1 else 0) := by
    intro σ' hz hva
    have hvz : (V "zc").evalB B σ' = some c := hz ▸ evalB_var (by rw [hz]; omega)
    have hl : c < (σ'.arrs "VALID").length := by rw [hva, List.length_set, hV.1]; exact hcN
    have := RunStep.eval_get B σ' "VALID" (V "zc") c hvz hl
      (by rw [hva, ListUtil.getD_set_self _ _ _ (by rw [hV.1]; exact hcN)]; split_ifs <;> omega)
    rw [hva, ListUtil.getD_set_self _ _ _ (by rw [hV.1]; exact hcN)] at this
    exact this
  by_cases hcode : IsCode n m c
  · have hcode' := hcode
    obtain ⟨Zs0, hsl0, hc0⟩ := hcode
    obtain ⟨j, Zs, rfl⟩ : ∃ j Zs, Zs0 = j :: Zs := by
      cases Zs0 with
      | nil =>
        exfalso
        have : c = (n + 1) ^ m - 1 := by rw [← hc0, codeL_nil]
        omega
      | cons j Zs => exact ⟨j, Zs, rfl⟩
    have hx1 : σ1.vars "zx1" = j := by rw [hx11, ← hc0]; exact x1_cons hm hsl0
    have hcondv := hvcond σ1 hzc1 (by rw [hVal1])
    rw [if_pos hcode'] at hcondv
    have hcv : (Cond.eq (Expr.get "VALID" (V "zc")) (Expr.lit 1)).evalB B σ1 = some true := by
      have := evalB_condEq hcondv (evalB_lit (show 1 < B by omega))
      rw [this]; rfl
    have hfa1' : ∀ a, a ≠ "VALID" → σ1.arrs a = σ.arrs a :=
      fun a ha => hfa1 a (fun h => ha (vphase_warrs a h))
    have hfv1' : ∀ y, y ∉ ["zx1", "zx2", "zt", "zsuf", "zv"] → σ1.vars y = σ.vars y :=
      fun y hy => hfv1 y (fun h => hy (vphase_wvars y h))
    have hStat1 : Stat4 n m W R PSl QSl DSl WSl NXl PWl σ1 :=
      ⟨by rw [hfv1' "n" (by decide)]; exact hn0, by rw [hfv1' "m" (by decide)]; exact hm0,
       by rw [hfv1' "nb" (by decide)]; exact hnb0, by rw [hfv1' "R" (by decide)]; exact hR0,
       by rw [hfv1' "N" (by decide)]; exact hN0, by rw [hfv1' "W" (by decide)]; exact hinf0,
       by rw [hfa1' "PS" (by decide)]; exact hPS0, by rw [hfa1' "QS" (by decide)]; exact hQS0,
       by rw [hfa1' "DS" (by decide)]; exact hDS0, by rw [hfa1' "WS" (by decide)]; exact hWS0,
       by rw [hfa1' "NX" (by decide)]; exact hNX0, by rw [hfa1' "PW" (by decide)]; exact hPW0⟩
    obtain ⟨σ2, hr2, ⟨T', hT2, hTok⟩, hfv2, hfa2, -, -⟩ :=
      (stepIsCode4_core sc hsl0 hc0 hT).frame.run (σ := σ1) ⟨hStat1, hzc1, hx1, hT1⟩
    have hVal2 : σ2.arrs "VALID" = σ1.arrs "VALID" :=
      hfa2 "VALID" (fun h => absurd (stepIsCode4_warrs _ h) (by decide))
    have hcost := lenOf_cons hsl0 hc0
    have hbc : blockCost n m R c = 128 * (Zs.length + 1) + 104 * (R + 1) := by
      unfold blockCost; rw [if_pos hcode', hcost]
    refine ⟨σ2, _, (hr1.seq (Run.ite_true hcv hr2)).mono ?_, le_rfl, ?_, ?_⟩
    · simp only [Cond.size, Expr.size]; rw [hbc]; omega
    · rw [hT2]; exact hTok
    · rw [hVal2]; exact hV1
  · have hcondv := hvcond σ1 hzc1 (by rw [hVal1])
    rw [if_neg hcode] at hcondv
    have hcv : (Cond.eq (Expr.get "VALID" (V "zc")) (Expr.lit 1)).evalB B σ1 = some false := by
      have := evalB_condEq hcondv (evalB_lit (show 1 < B by omega))
      rw [this]; rfl
    refine ⟨σ1, _, (hr1.seq (Run.ite_false hcv Run.skip)).mono ?_, le_rfl, ?_, hV1⟩
    · simp only [Cond.size, Expr.size]; omega
    · rw [hT1]; exact dinv_step_invalid rfl hcode hT

/-- One turn of the main loop: `zc := cc - 1`, fill the number `zc`, `cc := zc`. -/
def bodyCom4 : Com :=
  .seq (.assign "zc" (.bin .sub (V "cc") (.lit 1)))
    (.seq (.ite (.eq (V "cc") (V "N")) topCom4 stepCom4) (.assign "cc" (V "zc")))

set_option maxHeartbeats 4000000 in
theorem bodyCom4_spec {J : Instance} {B n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC4 J B n m W R PSl QSl DSl WSl NXl PWl) {c : ℕ} (hc : c < (n + 1) ^ m)
    {T Vl : List ℕ} (hT : DInv J n m W R ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => Stat4 n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = c + 1 ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) bodyCom4
      (fun _σ σ' => σ'.vars "cc" = c ∧ DInv J n m W R ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID")) (turnCost n m R c) := by
  classical
  have hB := sc.hB
  have hbR := sc.bR
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hbR
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hSt, hcc0, hT0, hV0⟩ := hσ
  obtain ⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩ := hSt
  have hvcc : (V "cc").evalB B σ = some (c + 1) := hcc0 ▸ evalB_var (by rw [hcc0]; omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "zc") (e := .bin .sub (V "cc") (.lit 1)) (v := c)
    (by
      have := RunStep.eval_sub B σ (V "cc") (.lit 1) (c + 1) 1 hvcc
        (evalB_lit (show 1 < B by omega)) (show c + 1 - 1 < B by omega)
      simpa using this)
  set σ1 : Env := σ.setVar "zc" c with hσ1
  clear_value σ1
  have hSt1 : Stat4 n m W R PSl QSl DSl WSl NXl PWl σ1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [*]
  have hzc1 : σ1.vars "zc" = c := by simp [hσ1]
  have hcc1 : σ1.vars "cc" = c + 1 := by simp [hσ1, hcc0]
  have hT1 : σ1.arrs "TAB" = T := by simp [hσ1, hT0]
  have hV1 : σ1.arrs "VALID" = Vl := by simp [hσ1, hV0]
  have hvN : (V "N").evalB B σ1 = some ((n + 1) ^ m) := by
    have : σ1.vars "N" = (n + 1) ^ m := hSt1.2.2.2.2.1
    exact this ▸ evalB_var (by rw [this]; exact hNB)
  have hvcc1 : (V "cc").evalB B σ1 = some (c + 1) := hcc1 ▸ evalB_var (by rw [hcc1]; omega)
  have hcondE := evalB_condEq hvcc1 hvN
  by_cases htop : c + 1 = (n + 1) ^ m
  · have hcv : (Cond.eq (V "cc") (V "N")).evalB B σ1 = some true := by
      rw [hcondE, htop]; simp
    obtain ⟨σ2, hr2, ⟨hTok, hVok⟩, hfv2, hfa2, -, -⟩ :=
      (topCom4_spec sc htop hT hV).frame.run (σ := σ1) ⟨hSt1, hzc1, hT1, hV1⟩
    have hzc2 : σ2.vars "zc" = c := by rw [hfv2 "zc" (by decide)]; exact hzc1
    have hvz : (V "zc").evalB B σ2 = some c := hzc2 ▸ evalB_var (by rw [hzc2]; omega)
    have r3 := Run.assign (B := B) (σ := σ2) (x := "cc") (e := V "zc") (v := c) hvz
    refine ⟨σ2.setVar "cc" c, _, (r1.seq ((Run.ite_true hcv hr2).seq r3)).mono ?_, le_rfl,
      by simp, by simpa using hTok, by simpa using hVok⟩
    · simp only [Cond.size, Expr.size, turnCost]; omega
  · have hcv : (Cond.eq (V "cc") (V "N")).evalB B σ1 = some false := by
      rw [hcondE]
      have : (c + 1 == (n + 1) ^ m) = false := by simpa using htop
      rw [this]
    have hc1 : c + 1 < (n + 1) ^ m := by omega
    obtain ⟨σ2, hr2, ⟨hTok, hVok⟩, hfv2, hfa2, -, -⟩ :=
      (stepCom4_spec sc hc1 hT hV).frame.run (σ := σ1) ⟨hSt1, hzc1, hT1, hV1⟩
    have hzc2 : σ2.vars "zc" = c := by rw [hfv2 "zc" (by decide)]; exact hzc1
    have hvz : (V "zc").evalB B σ2 = some c := hzc2 ▸ evalB_var (by rw [hzc2]; omega)
    have r3 := Run.assign (B := B) (σ := σ2) (x := "cc") (e := V "zc") (v := c) hvz
    refine ⟨σ2.setVar "cc" c, _, (r1.seq ((Run.ite_false hcv hr2).seq r3)).mono ?_, le_rfl,
      by simp, by simpa using hTok, by simpa using hVok⟩
    · simp only [Cond.size, Expr.size, turnCost]; omega


theorem bodyCom4_wvars : ∀ y ∈ bodyCom4.wvars,
    y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx",
      "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1",
      "zr", "ct", "cf", "cw", "ce", "cg"] := by decide

theorem bodyCom4_warrs : ∀ a ∈ bodyCom4.warrs, a = "TAB" ∨ a = "VALID" := by decide

theorem Stat4_of_frame {n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ} {σ σ' : Env}
    (hS : Stat4 n m W R PSl QSl DSl WSl NXl PWl σ) (c : Com)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (hw : ∀ y ∈ c.wvars, y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi",
      "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp",
      "ri", "z1", "zr", "ct", "cf", "cw", "ce", "cg"])
    (hwa : ∀ a ∈ c.warrs, a = "TAB" ∨ a = "VALID") :
    Stat4 n m W R PSl QSl DSl WSl NXl PWl σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hvv : ∀ y, y ∉ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi",
      "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp",
      "ri", "z1", "zr", "ct", "cf", "cw", "ce", "cg"] → σ'.vars y = σ.vars y :=
    fun y hy => hv y (fun h => hy (hw y h))
  have haa : ∀ a, a ≠ "TAB" → a ≠ "VALID" → σ'.arrs a = σ.arrs a :=
    fun a h1 h2 => ha a (fun h => by rcases hwa a h with h | h <;> contradiction)
  exact ⟨by rw [hvv "n" (by decide)]; exact h1, by rw [hvv "m" (by decide)]; exact h2,
    by rw [hvv "nb" (by decide)]; exact h3, by rw [hvv "R" (by decide)]; exact h4,
    by rw [hvv "N" (by decide)]; exact h5, by rw [hvv "W" (by decide)]; exact h6,
    by rw [haa "PS" (by decide) (by decide)]; exact h7,
    by rw [haa "QS" (by decide) (by decide)]; exact h8,
    by rw [haa "DS" (by decide) (by decide)]; exact h9,
    by rw [haa "WS" (by decide) (by decide)]; exact h10,
    by rw [haa "NX" (by decide) (by decide)]; exact h11,
    by rw [haa "PW" (by decide) (by decide)]; exact h12⟩

def loopCom4 : Com := .while (.lt (.lit 0) (V "cc")) bodyCom4

/-- The invariant of the loop over the numbers. -/
def LInv4 (J : Instance) (n m W R : ℕ) (PSl QSl DSl WSl NXl PWl : List ℕ) (σ : Env) : Prop :=
  Stat4 n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" ≤ (n + 1) ^ m ∧
    DInv J n m W R ((n + 1) ^ m) (σ.vars "cc") (σ.arrs "TAB") ∧
    ValidOK n m ((n + 1) ^ m) (σ.vars "cc") (σ.arrs "VALID")

set_option maxHeartbeats 4000000 in
theorem loopCom4_spec {J : Instance} {B n m W R : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC4 J B n m W R PSl QSl DSl WSl NXl PWl) :
    Spec B (fun σ => LInv4 J n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = (n + 1) ^ m) loopCom4
      (fun _ σ' => σ'.vars "cc" = 0 ∧
        DInv J n m W R ((n + 1) ^ m) 0 (σ'.arrs "TAB"))
      (loopWork n m R ((n + 1) ^ m) + 4) := by
  have hB := sc.hB
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) sc.bR
  have hdef : ∀ σ, LInv4 J n m W R PSl QSl DSl WSl NXl PWl σ →
      ∃ v, (Cond.lt (.lit 0) (V "cc")).evalB B σ = some v := by
    intro σ hI
    have hcc : σ.vars "cc" < B := lt_of_le_of_lt hI.2.1 hNB
    exact ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var hcc)⟩
  have hstep : ∀ σ, LInv4 J n m W R PSl QSl DSl WSl NXl PWl σ →
      (Cond.lt (.lit 0) (V "cc")).evalB B σ = some true →
      ∃ σ' K, Run B bodyCom4 σ σ' K ∧ LInv4 J n m W R PSl QSl DSl WSl NXl PWl σ' ∧
        1 + (Cond.lt (.lit 0) (V "cc")).size + K +
          (fun σ : Env => loopWork n m R (σ.vars "cc")) σ' ≤
        (fun σ : Env => loopWork n m R (σ.vars "cc")) σ := by
    intro σ hI hv
    obtain ⟨hS, hle, hT, hV⟩ := hI
    have hcc : σ.vars "cc" < B := lt_of_le_of_lt hle hNB
    have hpos : 0 < σ.vars "cc" := by
      have := evalB_condLt (B := B) (σ := σ) (e := .lit 0) (f := V "cc") (evalB_lit (by omega))
        (evalB_var hcc)
      rw [this] at hv
      have := Option.some.inj hv
      simpa using this
    obtain ⟨c, hc⟩ : ∃ c, σ.vars "cc" = c + 1 := ⟨σ.vars "cc" - 1, by omega⟩
    rw [hc] at hT hV hle
    obtain ⟨σ', hr, ⟨hcc', hT', hV'⟩, hfv, hfa, -, -⟩ :=
      (bodyCom4_spec sc (c := c) (by omega) hT hV).frame.run (σ := σ) ⟨hS, hc, rfl, rfl⟩
    refine ⟨σ', _, hr, ⟨Stat4_of_frame hS bodyCom4 hfv hfa bodyCom4_wvars bodyCom4_warrs, ?_, ?_, ?_⟩, ?_⟩
    · rw [hcc']; omega
    · rw [hcc']; exact hT'
    · rw [hcc']; exact hV'
    · show 1 + (Cond.lt (.lit 0) (V "cc")).size + turnCost n m R c + loopWork n m R (σ'.vars "cc") ≤
        loopWork n m R (σ.vars "cc")
      rw [hcc', hc]
      unfold loopWork
      rw [Finset.sum_range_succ]
      simp only [Cond.size, Expr.size]
      omega
  have hloop := Spec.while_potential (B := B) (b := Cond.lt (.lit 0) (V "cc")) (c := bodyCom4)
    (P := fun σ => LInv4 J n m W R PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = (n + 1) ^ m)
    (K := loopWork n m R ((n + 1) ^ m) + 4) (LInv4 J n m W R PSl QSl DSl WSl NXl PWl)
    (fun σ : Env => loopWork n m R (σ.vars "cc")) hdef hstep
    (fun σ h => h.1)
    (by
      rintro σ ⟨-, h2⟩
      show loopWork n m R (σ.vars "cc") + 1 + (Cond.lt (.lit 0) (V "cc")).size ≤ _
      rw [h2]; simp only [Cond.size, Expr.size]; omega)
  refine hloop.post ?_
  rintro σ σ' - ⟨⟨hS, hle, hT, hV⟩, hfalse⟩
  have hcc : σ'.vars "cc" < B := lt_of_le_of_lt hle hNB
  have := evalB_condLt (B := B) (σ := σ') (e := .lit 0) (f := V "cc") (evalB_lit (by omega))
    (evalB_var hcc)
  rw [this] at hfalse
  have h0 : σ'.vars "cc" = 0 := by
    have := Option.some.inj hfalse
    simp at this; omega
  exact ⟨h0, by rw [h0] at hT; exact hT⟩



end Lax496464Proofs.Ram.D4Step
