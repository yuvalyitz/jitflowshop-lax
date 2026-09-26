import Lax496464Proofs.Ram.D5Step

/-!
# Corollary 3's machine, part 4: the main loop over the numbers

`topComU` (the number of the empty set: its block is zero already, only `VALID` is set),
`stepComU` (decide whether a number is a code, and if so fill its block), `bodyComU`,
`loopComU`.  Costs are `D2Step`'s `blockCost`/`turnCost`/`loopWork` at `W := n`.
-/

namespace Lax496464Proofs.Ram.D5Loop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.D2Scan1 Lax496464Proofs.Ram.D2Valid1
open Lax496464Proofs.Ram.D2StepPure Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D5Row Lax496464Proofs.Ram.D5Pure Lax496464Proofs.Ram.D5Step
open Lax496464Proofs.Ram.Dp1 (IsNxt pv qv dv nxt_gt)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The number of the empty set: only `VALID` is set. -/
def topComU : Com := .store "VALID" (V "zc") (.lit 1)

theorem topComU_spec {J : Instance} {B n m Wr inf p : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC J B n m n inf PSl QSl DSl WSl NXl PWl) {c : ℕ} (hc : c + 1 = (n + 1) ^ m)
    {T Vl : List ℕ} (hT : UTab J n m Wr p ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) topComU
      (fun _σ σ' => UTab J n m Wr p ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID")) 20 := by
  classical
  have hB := sc.hB
  have hcN : c < (n + 1) ^ m := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨-, hzc0, hT0, hV0⟩ := hσ
  have hvc : (V "zc").evalB B σ = some c := hzc0 ▸ evalB_var (by rw [hzc0]; have := sc.bR; nlinarith [Nat.zero_le c])
  have hidx : c < (σ.arrs "VALID").length := by rw [hV0, hV.1]; exact hcN
  have r2 := Run.store (B := B) (σ := σ) (a := "VALID") (i := V "zc") (e := .lit 1)
    (idx := c) (v := 1) hvc (evalB_lit (by omega)) hidx
  refine ⟨σ.setArr "VALID" c 1, _, r2.mono (by simp only [Expr.size]; omega), le_rfl, ?_, ?_⟩
  · have h2 : (σ.setArr "VALID" c 1).arrs "TAB" = T := by
      simp [hT0]
    rw [h2]
    exact utab_step_empty' rfl (by omega) hT
  · have hval := valid_step (n := n) (m := m) (N := (n + 1) ^ m) (c := c) (v := 1) (V := Vl) hV hcN
      (by
        have hcode : IsCode n m c := ⟨[], sl_nil n m, by rw [codeL_nil]; omega⟩
        rw [if_pos hcode])
    have h2 : (σ.setArr "VALID" c 1).arrs "VALID" = Vl.set c 1 := by
      simp [hV0]
    rw [h2]; exact hval

/-- A number that is not the top one: decide whether it is a code, and if it is, fill its cells. -/
def stepComU : Com :=
  .seq vphase (.ite (.eq (.get "VALID" (V "zc")) (.lit 1)) stepIsCodeU .skip)

set_option maxHeartbeats 4000000 in
theorem stepComU_spec {J : Instance} {B n m Wr inf p : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC J B n m n inf PSl QSl DSl WSl NXl PWl) (hWr : Wr < B)
    (hwW : ∀ k < n, wv J k + Wr < B) (hp : ∀ i : J.Job, J.p i = p) {c : ℕ} (hc : c + 1 < (n + 1) ^ m)
    {T Vl : List ℕ} (hT : UTab J n m Wr p ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "zc" = c ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) stepComU
      (fun _σ σ' => UTab J n m Wr p ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID"))
      (500 + blockCost n m n c) := by
  classical
  have hB := sc.hB
  have hbR := sc.bR
  have hbW := sc.bW
  have hm := sc.hm
  have hcN : c < (n + 1) ^ m := by omega
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hbR
  have hsuf : sufc n m c < (n + 1) ^ m := sufc_lt_pow hm
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩, hWc0⟩, hzc0, hT0, hV0⟩ := hσ
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
    have hStat1 : StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ1 :=
      ⟨⟨by rw [hfv1' "n" (by decide)]; exact hn0, by rw [hfv1' "m" (by decide)]; exact hm0,
       by rw [hfv1' "nb" (by decide)]; exact hnb0, by rw [hfv1' "R" (by decide)]; exact hR0,
       by rw [hfv1' "N" (by decide)]; exact hN0, by rw [hfv1' "cinf" (by decide)]; exact hinf0,
       by rw [hfa1' "PS" (by decide)]; exact hPS0, by rw [hfa1' "QS" (by decide)]; exact hQS0,
       by rw [hfa1' "DS" (by decide)]; exact hDS0, by rw [hfa1' "WS" (by decide)]; exact hWS0,
       by rw [hfa1' "NX" (by decide)]; exact hNX0, by rw [hfa1' "PW" (by decide)]; exact hPW0⟩,
       by rw [hfv1' "Wc" (by decide)]; exact hWc0⟩
    obtain ⟨σ2, hr2, ⟨T', hT2, hTok⟩, hfv2, hfa2, -, -⟩ :=
      (stepIsCodeU_core sc hWr hwW hp hsl0 hc0 hT).frame.run (σ := σ1) ⟨hStat1, hzc1, hx1, hT1⟩
    have hVal2 : σ2.arrs "VALID" = σ1.arrs "VALID" :=
      hfa2 "VALID" (fun h => absurd (stepIsCode_warrs _ h) (by decide))
    have hcost := lenOf_cons hsl0 hc0
    have hbc : blockCost n m n c = 128 * (Zs.length + 1) + 104 * (n + 1) := by
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
    · rw [hT1]; exact utab_step_invalid' rfl hcode hT



/-- One turn of the main loop: `zc := cc - 1`, fill the number `zc`, `cc := zc`. -/
def bodyComU : Com :=
  .seq (.assign "zc" (.bin .sub (V "cc") (.lit 1)))
    (.seq (.ite (.eq (V "cc") (V "N")) topComU stepComU) (.assign "cc" (V "zc")))

set_option maxHeartbeats 4000000 in
theorem bodyComU_spec {J : Instance} {B n m Wr inf p : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC J B n m n inf PSl QSl DSl WSl NXl PWl) (hWr : Wr < B)
    (hwW : ∀ k < n, wv J k + Wr < B) (hp : ∀ i : J.Job, J.p i = p) {c : ℕ} (hc : c < (n + 1) ^ m)
    {T Vl : List ℕ} (hT : UTab J n m Wr p ((n + 1) ^ m) (c + 1) T)
    (hV : ValidOK n m ((n + 1) ^ m) (c + 1) Vl) :
    Spec B (fun σ => StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = c + 1 ∧
        σ.arrs "TAB" = T ∧ σ.arrs "VALID" = Vl) bodyComU
      (fun _σ σ' => σ'.vars "cc" = c ∧ UTab J n m Wr p ((n + 1) ^ m) c (σ'.arrs "TAB") ∧
        ValidOK n m ((n + 1) ^ m) c (σ'.arrs "VALID")) (turnCost n m n c) := by
  classical
  have hB := sc.hB
  have hbR := sc.bR
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hbR
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hSt, hcc0, hT0, hV0⟩ := hσ
  obtain ⟨⟨hn0, hm0, hnb0, hR0, hN0, hinf0, hPS0, hQS0, hDS0, hWS0, hNX0, hPW0⟩, hWc0⟩ := hSt
  have hvcc : (V "cc").evalB B σ = some (c + 1) := hcc0 ▸ evalB_var (by rw [hcc0]; omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "zc") (e := .bin .sub (V "cc") (.lit 1)) (v := c)
    (by
      have := RunStep.eval_sub B σ (V "cc") (.lit 1) (c + 1) 1 hvcc
        (evalB_lit (show 1 < B by omega)) (show c + 1 - 1 < B by omega)
      simpa using this)
  set σ1 : Env := σ.setVar "zc" c with hσ1
  clear_value σ1
  have hSt1 : StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ1 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [*]
  have hzc1 : σ1.vars "zc" = c := by simp [hσ1]
  have hcc1 : σ1.vars "cc" = c + 1 := by simp [hσ1, hcc0]
  have hT1 : σ1.arrs "TAB" = T := by simp [hσ1, hT0]
  have hV1 : σ1.arrs "VALID" = Vl := by simp [hσ1, hV0]
  have hvN : (V "N").evalB B σ1 = some ((n + 1) ^ m) := by
    have : σ1.vars "N" = (n + 1) ^ m := hSt1.1.2.2.2.2.1
    exact this ▸ evalB_var (by rw [this]; exact hNB)
  have hvcc1 : (V "cc").evalB B σ1 = some (c + 1) := hcc1 ▸ evalB_var (by rw [hcc1]; omega)
  have hcondE := evalB_condEq hvcc1 hvN
  by_cases htop : c + 1 = (n + 1) ^ m
  · have hcv : (Cond.eq (V "cc") (V "N")).evalB B σ1 = some true := by
      rw [hcondE, htop]; simp
    obtain ⟨σ2, hr2, ⟨hTok, hVok⟩, hfv2, hfa2, -, -⟩ :=
      (topComU_spec sc htop hT hV).frame.run (σ := σ1) ⟨hSt1, hzc1, hT1, hV1⟩
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
      (stepComU_spec sc hWr hwW hp hc1 hT hV).frame.run (σ := σ1) ⟨hSt1, hzc1, hT1, hV1⟩
    have hzc2 : σ2.vars "zc" = c := by rw [hfv2 "zc" (by decide)]; exact hzc1
    have hvz : (V "zc").evalB B σ2 = some c := hzc2 ▸ evalB_var (by rw [hzc2]; omega)
    have r3 := Run.assign (B := B) (σ := σ2) (x := "cc") (e := V "zc") (v := c) hvz
    refine ⟨σ2.setVar "cc" c, _, (r1.seq ((Run.ite_false hcv hr2).seq r3)).mono ?_, le_rfl,
      by simp, by simpa using hTok, by simpa using hVok⟩
    · simp only [Cond.size, Expr.size, turnCost]; omega


theorem bodyComU_wvars : ∀ y ∈ bodyComU.wvars,
    y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx",
      "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "lim", "ri",
      "z1", "ct"] := by decide

theorem bodyComU_warrs : ∀ a ∈ bodyComU.warrs, a = "TAB" ∨ a = "VALID" := by decide

theorem StatU_of_frame {n m Wr inf : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ} {σ σ' : Env}
    (hS : StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ) (c : Com)
    (hv : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (ha : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (hw : ∀ y ∈ c.wvars, y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur",
      "zi", "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq",
      "cp", "lim", "ri", "z1", "ct"])
    (hwa : ∀ a ∈ c.warrs, a = "TAB" ∨ a = "VALID") :
    StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ' := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13⟩ := hS
  have hvv : ∀ y, y ∉ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur",
      "zi", "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq",
      "cp", "lim", "ri", "z1", "ct"] → σ'.vars y = σ.vars y :=
    fun y hy => hv y (fun h => hy (hw y h))
  have haa : ∀ a, a ≠ "TAB" → a ≠ "VALID" → σ'.arrs a = σ.arrs a :=
    fun a h1 h2 => ha a (fun h => by rcases hwa a h with h | h <;> contradiction)
  exact ⟨⟨by rw [hvv "n" (by decide)]; exact h1, by rw [hvv "m" (by decide)]; exact h2,
    by rw [hvv "nb" (by decide)]; exact h3, by rw [hvv "R" (by decide)]; exact h4,
    by rw [hvv "N" (by decide)]; exact h5, by rw [hvv "cinf" (by decide)]; exact h6,
    by rw [haa "PS" (by decide) (by decide)]; exact h7,
    by rw [haa "QS" (by decide) (by decide)]; exact h8,
    by rw [haa "DS" (by decide) (by decide)]; exact h9,
    by rw [haa "WS" (by decide) (by decide)]; exact h10,
    by rw [haa "NX" (by decide) (by decide)]; exact h11,
    by rw [haa "PW" (by decide) (by decide)]; exact h12⟩,
    by rw [hvv "Wc" (by decide)]; exact h13⟩

/-- All the turns. -/
def loopComU : Com := .while (.lt (.lit 0) (V "cc")) bodyComU

/-- The invariant of the loop over the numbers. -/
def LInv (J : Instance) (n m Wr p inf : ℕ) (PSl QSl DSl WSl NXl PWl : List ℕ) (σ : Env) : Prop :=
  StatU n m Wr inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" ≤ (n + 1) ^ m ∧
    UTab J n m Wr p ((n + 1) ^ m) (σ.vars "cc") (σ.arrs "TAB") ∧
    ValidOK n m ((n + 1) ^ m) (σ.vars "cc") (σ.arrs "VALID")

set_option maxHeartbeats 4000000 in
theorem loopComU_spec {J : Instance} {B n m Wr inf p : ℕ} {PSl QSl DSl WSl NXl PWl : List ℕ}
    (sc : SC J B n m n inf PSl QSl DSl WSl NXl PWl) (hWr : Wr < B)
    (hwW : ∀ k < n, wv J k + Wr < B) (hp : ∀ i : J.Job, J.p i = p) :
    Spec B (fun σ => LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = (n + 1) ^ m) loopComU
      (fun _ σ' => σ'.vars "cc" = 0 ∧
        UTab J n m Wr p ((n + 1) ^ m) 0 (σ'.arrs "TAB"))
      (loopWork n m n ((n + 1) ^ m) + 4) := by
  have hB := sc.hB
  have hNB : (n + 1) ^ m < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) sc.bR
  have hdef : ∀ σ, LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl σ →
      ∃ v, (Cond.lt (.lit 0) (V "cc")).evalB B σ = some v := by
    intro σ hI
    have hcc : σ.vars "cc" < B := lt_of_le_of_lt hI.2.1 hNB
    exact ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var hcc)⟩
  have hstep : ∀ σ, LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl σ →
      (Cond.lt (.lit 0) (V "cc")).evalB B σ = some true →
      ∃ σ' K, Run B bodyComU σ σ' K ∧ LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl σ' ∧
        1 + (Cond.lt (.lit 0) (V "cc")).size + K +
          (fun σ : Env => loopWork n m n (σ.vars "cc")) σ' ≤
        (fun σ : Env => loopWork n m n (σ.vars "cc")) σ := by
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
      (bodyComU_spec sc hWr hwW hp (c := c) (by omega) hT hV).frame.run (σ := σ) ⟨hS, hc, rfl, rfl⟩
    refine ⟨σ', _, hr, ⟨StatU_of_frame hS bodyComU hfv hfa bodyComU_wvars bodyComU_warrs, ?_, ?_, ?_⟩, ?_⟩
    · rw [hcc']; omega
    · rw [hcc']; exact hT'
    · rw [hcc']; exact hV'
    · show 1 + (Cond.lt (.lit 0) (V "cc")).size + turnCost n m n c + loopWork n m n (σ'.vars "cc") ≤
        loopWork n m n (σ.vars "cc")
      rw [hcc', hc]
      unfold loopWork
      rw [Finset.sum_range_succ]
      simp only [Cond.size, Expr.size]
      omega
  have hloop := Spec.while_potential (B := B) (b := Cond.lt (.lit 0) (V "cc")) (c := bodyComU)
    (P := fun σ => LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl σ ∧ σ.vars "cc" = (n + 1) ^ m)
    (K := loopWork n m n ((n + 1) ^ m) + 4) (LInv J n m Wr p inf PSl QSl DSl WSl NXl PWl)
    (fun σ : Env => loopWork n m n (σ.vars "cc")) hdef hstep
    (fun σ h => h.1)
    (by
      rintro σ ⟨-, h2⟩
      show loopWork n m n (σ.vars "cc") + 1 + (Cond.lt (.lit 0) (V "cc")).size ≤ _
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

end Lax496464Proofs.Ram.D5Loop
