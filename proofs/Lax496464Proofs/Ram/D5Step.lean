import Lax496464Proofs.Ram.D2Step
import Lax496464Proofs.Ram.D5Row
import Lax496464Proofs.Ram.D5Pure

/-!
# Corollary 3's Machine, Part 3: the Block of One Number

The block of a code: two scans, the job's numbers, its limit, and the `n + 1` cells.  The table
is that of `D5Pure.UTab` with block width `R = n + 1`; the set-up is `D2Step`'s with the
table parameter `W := n`, the actual threshold living in the scalar `"Wc"`.
-/

namespace Lax496464Proofs.Ram.D5Step

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.D2Scan1 Lax496464Proofs.Ram.D2Valid1
open Lax496464Proofs.Ram.D2StepPure Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D5Row Lax496464Proofs.Ram.D5Pure
open Lax496464Proofs.Ram.D3Cor3
open Lax496464Proofs.Ram.Dp1 (IsNxt pv qv dv nxt_gt)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The scalars of the state: `D2Step.Stat` at the table parameter `n`, and the threshold. -/
def StatU (n m Wr inf : ℕ) (PSl QSl DSl WSl NXl PWl : List ℕ) (σ : Env) : Prop :=
  Stat n m n inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "Wc" = Wr

/-- The block of a number that is a code: two scans, the limit, and the cells. -/
def stepIsCodeU : Com :=
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
                        (.seq (.assign "cp" (.get "PS" (V "zj")))
                          (.seq limCom rowsLoopU))))))))))))

theorem limCom_wvars : ∀ y ∈ limCom.wvars, y ∈ ["lim"] := by decide

theorem limCom_warrs : limCom.warrs = [] := by decide

set_option maxHeartbeats 4000000 in
theorem stepIsCodeU_core {J : Instance} {B n m Wr inf p : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC J B n m n inf PSl QSl DSl WSl NXl PWl) (hWr : Wr < B)
    (hwW : ∀ k < n, wv J k + Wr < B) (hp : ∀ i : J.Job, J.p i = p)
    {c j : ℕ} {Zs : List ℕ} {T : List ℕ}
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c)
    (hT : UTab J n m Wr p ((n + 1) ^ m) (c + 1) T) :
    Spec B (fun σ => StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.vars "zx1" = j ∧ σ.arrs "TAB" = T) stepIsCodeU
      (fun _σ σ' => ∃ T', σ'.arrs "TAB" = T' ∧ UTab J n m Wr p ((n + 1) ^ m) c T')
      (2 * (64 * (Zs.length + 1) + 110) + ((100 + 4) * (n + 1) + 6) + 100) := by
  have hB := sc.hB
  have hn := sc.hn
  have hm := sc.hm
  have hest := sc.hest
  have hq := sc.hq
  have hi1 := sc.hi1
  have hinf := sc.hinf
  have hinfB := sc.hinfB
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
  have hRB : n + 1 < B := by omega
  have hTlen : T.length = (n + 1) ^ m * (n + 1) := hT.1.1
  have hcodeR : ∀ c', c' < (n + 1) ^ m → c' * (n + 1) < B := fun c' hc' =>
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hc'.le) bR
  have hnB : n + 1 < B := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩, hWc0⟩, hzc0, hzx10, hT0⟩ := hσ
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
  have hzb1B : codeL n m (newL n Zs cur1 k1) * (n + 1) < B := hcodeR _ hcode1B
  -- 4: zb1 := zcode * R
  have hvcode3 : (V "zcode").evalB B σ3 = some (codeL n m (newL n Zs cur1 k1)) := by
    rw [← hcode3]; exact evalB_var (by rw [hcode3]; omega)
  have hvR3 : (V "R").evalB B σ3 = some (n + 1) := by
    have : σ3.vars "R" = n + 1 := by
      rw [hfv3 "R" (by decide)]; simp [hσ2, hσ1, hR0]
    exact this ▸ evalB_var (by rw [this]; omega)
  have r4 := Run.assign (B := B) (σ := σ3) (x := "zb1") (e := .bin .mul (V "zcode") (V "R"))
    (v := codeL n m (newL n Zs cur1 k1) * (n + 1)) (evalB_bin hvcode3 hvR3 hzb1B)
  set σ4 : Env := σ3.setVar "zb1" (codeL n m (newL n Zs cur1 k1) * (n + 1)) with hσ4
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
  have hzb2B : codeL n m (newL n Zs cur2 k2) * (n + 1) < B := hcodeR _ hcode2B
  -- 7: zb2 := zcode * R
  have hvcode6 : (V "zcode").evalB B σ6 = some (codeL n m (newL n Zs cur2 k2)) := by
    rw [← hcode6]; exact evalB_var (by rw [hcode6]; omega)
  have hR6 : σ6.vars "R" = n + 1 := by
    rw [hfv6 "R" (by decide)]; simp [hσ5, hσ4]; rw [hfv3 "R" (by decide)]; simp [hσ2, hσ1, hR0]
  have hvR6 : (V "R").evalB B σ6 = some (n + 1) := hR6 ▸ evalB_var (by rw [hR6]; omega)
  have r7 := Run.assign (B := B) (σ := σ6) (x := "zb2") (e := .bin .mul (V "zcode") (V "R"))
    (v := codeL n m (newL n Zs cur2 k2) * (n + 1)) (evalB_bin hvcode6 hvR6 hzb2B)
  set σ7 : Env := σ6.setVar "zb2" (codeL n m (newL n Zs cur2 k2) * (n + 1)) with hσ7
  clear_value σ7
  -- 8: zbc := zc * R
  have hzc7 : σ7.vars "zc" = c := by
    simp [hσ7]; rw [hfv6 "zc" (by decide)]; simp [hσ5, hσ4]; rw [hfv3 "zc" (by decide)]
    simp [hσ2, hσ1, hzc0]
  have hvc7 : (V "zc").evalB B σ7 = some c := hzc7 ▸ evalB_var (by rw [hzc7]; omega)
  have hvR7 : (V "R").evalB B σ7 = some (n + 1) := by
    have : σ7.vars "R" = n + 1 := by simp [hσ7, hR6]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hcRB := hcodeR c hcN
  have r8 := Run.assign (B := B) (σ := σ7) (x := "zbc") (e := .bin .mul (V "zc") (V "R"))
    (v := c * (n + 1)) (evalB_bin hvc7 hvR7 hcRB)
  set σ8 : Env := σ7.setVar "zbc" (c * (n + 1)) with hσ8
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
        (by rw [hWS8, eWS j hjn]; exact bw j hjn)
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
  have hpqj : pv J j + qv J j < B := hbpj
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
  -- 13: the limit
  have hpj : PSl.getD j 0 = pv J j := ePS j hjn
  have hqj : QSl.getD j 0 = qv J j := eQS j hjn
  have hdj : DSl.getD j 0 = dv J j := eDS j hjn
  have hwjj : WSl.getD j 0 = wv J j := eWS j hjn
  have hpv : pv J j = J.p ⟨j, hjJ⟩ := by unfold pv; rw [dif_pos hjJ]
  have hqv : qv J j = J.q ⟨j, hjJ⟩ := by unfold qv; rw [dif_pos hjJ]
  have hdv : dv J j = J.d ⟨j, hjJ⟩ := by unfold dv; rw [dif_pos hjJ]
  have hwv : wv J j = J.w ⟨j, hjJ⟩ := by unfold wv; rw [dif_pos hjJ]
  have hpjp : PSl.getD j 0 = p := by rw [hpj, hpv]; exact hp _
  have hbdj := bd j hjn
  have hbpj := bp j hjn
  have hdB : DSl.getD j 0 + 1 < B := by rw [hdj]; exact hbdj
  have hqB : QSl.getD j 0 < B := by rw [hqj]; have := hbpj; omega
  have hpB : PSl.getD j 0 < B := by rw [hpj]; have := hbpj; omega
  have hwB : WSl.getD j 0 < B := by rw [hwjj]; exact bw j hjn
  have hwWj : WSl.getD j 0 + Wr < B := by rw [hwjj]; exact hwW j hjn
  have hcd12 : σ12.vars "cd" = DSl.getD j 0 := by simp [hσ12, hσ11, hσ10]
  have hcq12 : σ12.vars "cq" = QSl.getD j 0 := by simp [hσ12, hσ11]
  have hcp12 : σ12.vars "cp" = PSl.getD j 0 := by simp [hσ12]
  have hn12 : σ12.vars "n" = n := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]; rw [hfv6 "n" (by decide)]
    simp [hσ5, hσ4]; rw [hfv3 "n" (by decide)]; simp [hσ2, hσ1, hn0]
  have hWc12 : σ12.vars "Wc" = Wr := by
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]; rw [hfv6 "Wc" (by decide)]
    simp [hσ5, hσ4]; rw [hfv3 "Wc" (by decide)]; simp [hσ2, hσ1, hWc0]
  obtain ⟨σ13, hr13, hlim13, hfv13, hfa13, -, -⟩ :=
    (limCom_spec (B := B) hB n (PSl.getD j 0) (QSl.getD j 0) (DSl.getD j 0) (by omega) (by omega)
      hqB hpB).frame.run (σ := σ12) ⟨hn12, hcp12, hcq12, hcd12⟩
  have hfv13' : ∀ y, y ≠ "lim" → σ13.vars y = σ12.vars y :=
    fun y hy => hfv13 y (fun h => hy (by simpa using limCom_wvars y h))
  have hlimle : limOf n (PSl.getD j 0) (QSl.getD j 0) (DSl.getD j 0) ≤ n := limOf_le _ _ _ _
  -- 14: the cells
  have hc1 : c < codeL n m (newL n Zs cur1 k1) :=
    newcode_gt hm hsl hcode (by omega) (by omega) hs1
  have hc2 : c < codeL n m (newL n Zs cur2 k2) :=
    newcode_gt hm hsl hcode (nxt_gt hest hq hjJ hnx) hy0 hs2
  have hT13 : σ13.arrs "TAB" = T := by
    have := hA8 "TAB"
    rw [hfa13 "TAB" (by rw [limCom_warrs]; simp)]
    simp only [hσ12, hσ11, hσ10, hσ9, arrs_setVar]; rw [this, hT0]
  have hb1 : σ13.vars "zb1" = codeL n m (newL n Zs cur1 k1) * (n + 1) := by
    rw [hfv13' "zb1" (by decide)]
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]; rw [hfv6 "zb1" (by decide)]; simp [hσ5, hσ4]
  have hb2 : σ13.vars "zb2" = codeL n m (newL n Zs cur2 k2) * (n + 1) := by
    rw [hfv13' "zb2" (by decide)]
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7]
  have hbc : σ13.vars "zbc" = c * (n + 1) := by
    rw [hfv13' "zbc" (by decide)]
    simp [hσ12, hσ11, hσ10, hσ9, hσ8]
  have hwj13 : σ13.vars "wj" = WSl.getD j 0 := by
    rw [hfv13' "wj" (by decide)]
    simp [hσ12, hσ11, hσ10, hσ9]
  have hWc13 : σ13.vars "Wc" = Wr := by
    rw [hfv13' "Wc" (by decide)]; exact hWc12
  have hR13 : σ13.vars "R" = n + 1 := by
    rw [hfv13' "R" (by decide)]
    simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hR6]
  have hlimB : limOf n (PSl.getD j 0) (QSl.getD j 0) (DSl.getD j 0) < B := by omega
  have hTb := hT.2
  have hrep1 : ∀ r, r < n + 1 → T.getD (codeL n m (newL n Zs cur1 k1) * (n + 1) + r) 0 ≤ Wr :=
    fun r _ => hTb _
  have hrep2 : ∀ r, r < limOf n (PSl.getD j 0) (QSl.getD j 0) (DSl.getD j 0) →
      T.getD (codeL n m (newL n Zs cur2 k2) * (n + 1) + r + 1) 0 ≤ Wr := fun r _ => hTb _
  have hNR : ((n + 1) ^ m) * (n + 1) < B := bR
  obtain ⟨σ14, hr14, hlen14, hout14, hcell14, -, -⟩ :=
    (rowsLoopU_spec' (B := B) hB Wr (limOf n (PSl.getD j 0) (QSl.getD j 0) (DSl.getD j 0))
      (WSl.getD j 0) (codeL n m (newL n Zs cur1 k1) * (n + 1))
      (codeL n m (newL n Zs cur2 k2) * (n + 1)) (c * (n + 1)) (n + 1) ((n + 1) ^ m * (n + 1)) T
      hWr hwWj hwB hlimB hNR hRB hTlen (mul_step_lt hc1) (mul_step_lt hc2) (mul_step_le hcode1B)
      (mul_step_le hcode2B) (mul_step_le hcN) (by omega) hrep1 hrep2).run
      (σ := σ13) ⟨hT13, hb1, hb2, hbc, hwj13, hWc13, hlim13, hR13⟩
  have hTab' : UTab J n m Wr p ((n + 1) ^ m) c (σ14.arrs "TAB") := by
    refine utab_step' rfl hT hlen14 ?_ ?_ ?_
    · intro i hi hne
      have hlt : i < c * (n + 1) ∨ c * (n + 1) + (n + 1) ≤ i := by
        by_contra hcon
        push Not at hcon
        apply hne
        apply Nat.div_eq_of_lt_le hcon.1 (by rw [Nat.add_mul, Nat.one_mul]; omega)
      exact hout14 i hi (by omega)
    · intro Zs0 hsl0 hc0 u hu hgood
      have hZ : Zs0 = j :: Zs := SL.codeL_inj hsl0 hsl (hc0.trans hcode.symm)
      subst hZ
      refine ublock hn hm hest hq hp hT.1 hsl hcode hjJ hnx hs1 hs2 ?_ u hu hgood
      intro u' hu'
      have h := hcell14 u' (by omega)
      unfold cellVal at h
      rw [h, hpjp, hqj, hdj, hwjj, hqv, hdv, hwv]
      exact cellV_eq_dStepU
    · intro i
      by_cases hi : i < (n + 1) ^ m * (n + 1)
      · by_cases hib : c * (n + 1) ≤ i ∧ i < c * (n + 1) + (n + 1)
        · obtain ⟨r, hr⟩ : ∃ r, i = c * (n + 1) + r := ⟨i - c * (n + 1), by omega⟩
          have h := hcell14 r (by omega)
          rw [hr, h]
          unfold cellVal
          exact cellV_le (hTb _)
        · rw [hout14 i hi (by omega)]; exact hTb i
      · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
  have hrun : Run B stepIsCodeU σ σ14 _ :=
    Run.seq r1 <| Run.seq r2 <| Run.seq hr3 <| Run.seq r4 <| Run.seq r5 <| Run.seq hr6 <|
    Run.seq r7 <| Run.seq r8 <| Run.seq r9 <| Run.seq r10 <| Run.seq r11 <|
    Run.seq r12 (Run.seq hr13 hr14)
  exact ⟨σ14, _, hrun.mono (by simp only [Expr.size]; omega), le_rfl, _, rfl, hTab'⟩

end Lax496464Proofs.Ram.D5Step
