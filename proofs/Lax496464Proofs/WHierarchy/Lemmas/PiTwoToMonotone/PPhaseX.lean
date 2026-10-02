import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf

/-!
# Phase X: the Clauses of the Pairs of Blocks with Values

Four nested loops over `b1, v1, b2, v2` (the slots decoded into `bd1, vd1, bd2, vd2`); for each
pair, the conflict test and the `2C` literals of `OutW.xWords`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf

variable {B : ℕ} {Dt : Data} {x : List ℕ}

/-- The context of the innermost loop. -/
def X4 (Dt : Data) (x : List ℕ) (b1 v1 b2 : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_b1" = b1 ∧ σ.arrs "bd1" = (par Dt x).bd b1 ∧ σ.vars "g_v1" = v1 ∧
    σ.arrs "vd1" = (par Dt x).vd v1 ∧ σ.vars "g_b2" = b2 ∧ σ.arrs "bd2" = (par Dt x).bd b2

set_option maxHeartbeats 2000000 in
/-- A literal of the first half. -/
theorem lit1_spec (hB : BB Dt x B) {b1 v1 e cf : ℕ} (hb1 : b1 < (par Dt x).W)
    (he : e < (par Dt x).C) (hcf : cf ≤ 1) :
    Spec B (fun σ => σ.vars "g_b1" = b1 ∧ σ.vars "g_v1" = v1 ∧ σ.vars "g_e" = e ∧
        σ.vars "g_cf" = cf ∧ σ.vars "g_W" = (par Dt x).W ∧ v1 < B) lit1
      (fun σ σ' => σ'.out = σ.out ++ [if cf = 0 ∨ e ≠ v1 then 2 * (par Dt x).zv b1 e else 0] ∧
        σ' = { σ with out := σ'.out }) 30 := by
  intro σ ⟨h1, h2, h3, h4, h5, hv1⟩
  have hs := hB.small
  obtain ⟨σ', hw, ho, heq⟩ := litWrite_spec hB hb1 he "g_b1" "g_e" σ ⟨h1, h3, h5⟩
  have ecf := evalB_var (B := B) (σ := σ) (x := "g_cf") (by rw [h4]; omega)
  have e0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have ee := evalB_var (B := B) (σ := σ) (x := "g_e") (by rw [h3]; omega)
  have ev := evalB_var (B := B) (σ := σ) (x := "g_v1") (by rw [h2]; omega)
  by_cases hc : cf = 0
  · refine ⟨σ', (RunStep.ite_true B _ _ _ σ _ _ (RunStep.cond_eq_true B σ _ _ _ _ ecf e0
      (by rw [h4, hc])) hw).mono (by simp [Cond.size, Expr.size]), by rw [ho, if_pos (Or.inl hc)],
      heq⟩
  · by_cases hev : e = v1
    · have hw0 := RunStep.write B σ (.lit 0) 0 e0
      refine ⟨_, (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ecf e0
        (by rw [h4]; exact hc)) (RunStep.ite_true B _ _ _ σ _ _
          (RunStep.cond_eq_true B σ _ _ _ _ ee ev (by rw [h3, h2, hev])) hw0)).mono
        (by simp [Cond.size, Expr.size]), by rw [if_neg (by tauto)], rfl⟩
    · refine ⟨σ', (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ecf e0
        (by rw [h4]; exact hc)) (RunStep.ite_false B _ _ _ σ _ _
          (RunStep.cond_eq_false B σ _ _ _ _ ee ev (by rw [h3, h2]; exact hev)) hw)).mono
        (by simp [Cond.size, Expr.size]), by rw [ho, if_pos (Or.inr hev)], heq⟩

set_option maxHeartbeats 2000000 in
/-- A literal of the second half. -/
theorem lit2_spec (hB : BB Dt x B) {b2 v2 e cf : ℕ} (hb2 : b2 < (par Dt x).W)
    (he : e < (par Dt x).C) (hcf : cf ≤ 1) :
    Spec B (fun σ => σ.vars "g_b2" = b2 ∧ σ.vars "g_v2" = v2 ∧ σ.vars "g_e" = e ∧
        σ.vars "g_cf" = cf ∧ σ.vars "g_W" = (par Dt x).W ∧ v2 < B) lit2
      (fun σ σ' => σ'.out = σ.out ++ [if cf = 1 ∧ e ≠ v2 then 2 * (par Dt x).zv b2 e else 0] ∧
        σ' = { σ with out := σ'.out }) 30 := by
  intro σ ⟨h1, h2, h3, h4, h5, hv2⟩
  have hs := hB.small
  obtain ⟨σ', hw, ho, heq⟩ := litWrite_spec hB hb2 he "g_b2" "g_e" σ ⟨h1, h3, h5⟩
  have ecf := evalB_var (B := B) (σ := σ) (x := "g_cf") (by rw [h4]; omega)
  have e0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have ee := evalB_var (B := B) (σ := σ) (x := "g_e") (by rw [h3]; omega)
  have ev := evalB_var (B := B) (σ := σ) (x := "g_v2") (by rw [h2]; omega)
  have hw0 := RunStep.write B σ (.lit 0) 0 e0
  by_cases hc : cf = 0
  · refine ⟨_, (RunStep.ite_true B _ _ _ σ _ _ (RunStep.cond_eq_true B σ _ _ _ _ ecf e0
      (by rw [h4, hc])) hw0).mono (by simp [Cond.size, Expr.size]),
      by rw [if_neg (by omega)], rfl⟩
  · by_cases hev : e = v2
    · refine ⟨_, (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ecf e0
        (by rw [h4]; exact hc)) (RunStep.ite_true B _ _ _ σ _ _
          (RunStep.cond_eq_true B σ _ _ _ _ ee ev (by rw [h3, h2, hev])) hw0)).mono
        (by simp [Cond.size, Expr.size]), by rw [if_neg (by tauto)], rfl⟩
    · refine ⟨σ', (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ecf e0
        (by rw [h4]; exact hc)) (RunStep.ite_false B _ _ _ σ _ _
          (RunStep.cond_eq_false B σ _ _ _ _ ee ev (by rw [h3, h2]; exact hev)) hw)).mono
        (by simp [Cond.size, Expr.size]), by rw [ho, if_pos ⟨by omega, hev⟩], heq⟩

theorem length_bd (b : ℕ) : ((par Dt x).bd b).length = Dt.D := length_digits _ _ _

theorem length_vd (v : ℕ) : ((par Dt x).vd v).length = Dt.D := length_digits _ _ _

theorem bd_le (b j : ℕ) : ((par Dt x).bd b).getD j 0 ≤ kW x := digits_bd_lt j

theorem vd_le (v j : ℕ) : ((par Dt x).vd v).getD j 0 ≤ nU Dt x ^ Dt.s := digits_bd_lt j

/-- The cost of one pair. -/
def Kx2 (Dt : Data) (x : List ℕ) : ℕ :=
  (20 * Dt.D + 3) + Kcf Dt.D + 2 + ((30 + 8) * (par Dt x).C + 6) + ((30 + 8) * (par Dt x).C + 6) + 1

set_option maxHeartbeats 4000000 in
/-- **One pair of blocks with values.** -/
theorem xv2_spec (hB : BB Dt x B) {b1 v1 b2 : ℕ} (hb1 : b1 < (par Dt x).W)
    (hv1 : v1 < (par Dt x).C) (hb2 : b2 < (par Dt x).W) (v2 : ℕ) (hv2 : v2 < (par Dt x).C) :
    Spec B (fun σ => X4 Dt x b1 v1 b2 σ ∧ σ.vars "g_v2" = v2) (xv2Body Dt.D)
      (fun σ σ' => X4 Dt x b1 v1 b2 σ' ∧ σ'.vars "g_v2" = v2 ∧
        σ'.out = σ.out ++ xWords Dt x b1 v1 b2 v2) (Kx2 Dt x) := by
  intro σ ⟨⟨hg, e1, a1, e2, a2, e3, a3⟩, e4⟩
  have hs := hB.small
  -- the values of the second block
  obtain ⟨σ1, hr1, d1, f1, o1⟩ := decV_spec hB (src := "g_v2") (arr := "vd2") hv2 σ
    ⟨hg, e4, hg.vd2⟩
  have hg1 : GC Dt x σ1 := hg.frame f1 (by simp [gcVars]) (by simp [gcArrs]) (by
    intro b hb; by_cases h : b = "vd2"
    · subst h; rw [d1, hg.vd2, length_vd]
    · rw [f1.2.1 _ (by simpa using h)])
  have hk1 : ∀ y ∈ ["g_b1", "g_v1", "g_b2", "g_v2"], σ1.vars y = σ.vars y := fun y hy =>
    f1.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl <;> decide)
  have ha1 : ∀ b ∈ ["bd1", "vd1", "bd2"], σ1.arrs b = σ.arrs b := fun b hb =>
    f1.2.1 b (by simp at hb ⊢; rcases hb with rfl | rfl | rfl <;> decide)
  -- the conflict test
  have hCB : CB B (kW x) (nU Dt x ^ Dt.s) Dt.D ((par Dt x).bd b1) ((par Dt x).vd v1)
      ((par Dt x).bd b2) ((par Dt x).vd v2) :=
    ⟨length_bd _, length_vd _, length_bd _, length_vd _, by omega, by omega, by omega,
      fun j => by have := bd_le (Dt := Dt) (x := x) b1 j; omega,
      fun j => by have := vd_le (Dt := Dt) (x := x) v1 j; omega,
      fun j => by have := bd_le (Dt := Dt) (x := x) b2 j; omega,
      fun j => by have := vd_le (Dt := Dt) (x := x) v2 j; omega⟩
  obtain ⟨σ2, hr2, c2, f2, o2⟩ := cfCom_spec hCB σ1
    ⟨by rw [ha1 _ (by simp)]; exact a1, by rw [ha1 _ (by simp)]; exact a2,
      by rw [ha1 _ (by simp)]; exact a3, d1, hg1.k, hg1.NT, hg1.D, hg1.DD⟩
  have hg2 : GC Dt x σ2 := hg1.frame f2 (by simp [cfVars, gcVars]) (by simp) (fun _ _ => by
    rw [f2.2.1 _ (by simp)])
  set cfv := bn (decide (Conflict (kW x) (nU Dt x ^ Dt.s) Dt.D ((par Dt x).bd b1) ((par Dt x).vd v1)
    ((par Dt x).bd b2) ((par Dt x).vd v2))) with hcfv
  have hcf1 : cfv ≤ 1 := bn_le_one _
  have hpc : (par Dt x).cf b1 v1 b2 v2 = decide (Conflict (kW x) (nU Dt x ^ Dt.s) Dt.D
      ((par Dt x).bd b1) ((par Dt x).vd v1) ((par Dt x).bd b2) ((par Dt x).vd v2)) := rfl
  have hcfe : (cfv = 0) ↔ (par Dt x).cf b1 v1 b2 v2 = false := by
    rw [hcfv, hpc]
    cases decide (Conflict (kW x) (nU Dt x ^ Dt.s) Dt.D ((par Dt x).bd b1) ((par Dt x).vd v1)
      ((par Dt x).bd b2) ((par Dt x).vd v2)) <;> simp [bn]
  have hcfe1 : (cfv = 1) ↔ (par Dt x).cf b1 v1 b2 v2 = true := by
    rw [hcfv, hpc]
    cases decide (Conflict (kW x) (nU Dt x ^ Dt.s) Dt.D ((par Dt x).bd b1) ((par Dt x).vd v1)
      ((par Dt x).bd b2) ((par Dt x).vd v2)) <;> simp [bn]
  have hk2 : ∀ y ∈ ["g_b1", "g_v1", "g_b2", "g_v2"], σ2.vars y = σ.vars y := fun y hy => by
    rw [f2.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl <;> decide), hk1 y hy]
  have ha2 : ∀ b ∈ ["bd1", "vd1", "bd2", "vd2"], σ2.arrs b = σ1.arrs b := fun b _ =>
    f2.2.1 b (by simp)
  -- the length of the clause
  have hr3 := RunStep.write B σ2 (V "g_C2") _ (evalB_var (by rw [hg2.C2]; omega))
  set σ3 := { σ2 with out := σ2.out ++ [σ2.vars "g_C2"] } with hσ3
  -- the context of the two loops
  let X5 : Env → Prop := fun τ => X4 Dt x b1 v1 b2 τ ∧ τ.vars "g_v2" = v2 ∧
    τ.arrs "vd2" = (par Dt x).vd v2 ∧ τ.vars "g_cf" = cfv
  have hX5 : X5 σ3 := by
    refine ⟨⟨hg2.frame (S := []) (A := []) ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩ (by simp) (by simp)
      (fun _ _ => rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show σ2.vars _ = _; rw [hk2 _ (by simp)]; exact e1
    · show σ2.arrs _ = _; rw [ha2 _ (by simp), ha1 _ (by simp)]; exact a1
    · show σ2.vars _ = _; rw [hk2 _ (by simp)]; exact e2
    · show σ2.arrs _ = _; rw [ha2 _ (by simp), ha1 _ (by simp)]; exact a2
    · show σ2.vars _ = _; rw [hk2 _ (by simp)]; exact e3
    · show σ2.arrs _ = _; rw [ha2 _ (by simp), ha1 _ (by simp)]; exact a3
    · show σ2.vars _ = _; rw [hk2 _ (by simp)]; exact e4
    · show σ2.arrs _ = _; rw [ha2 _ (by simp)]; exact d1
    · exact c2
  have hX5set : ∀ τ w, X5 τ → X5 (τ.setVar "g_e" w) := by
    intro τ w ⟨⟨h0, h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩
    exact ⟨⟨h0.setVar (by simp [gcVars]) w, by simp [Env.setVar, h1], by simp [Env.setVar, h2],
      by simp [Env.setVar, h3], by simp [Env.setVar, h4], by simp [Env.setVar, h5],
      by simp [Env.setVar, h6]⟩, by simp [Env.setVar, h7], by simp [Env.setVar, h8],
      by simp [Env.setVar, h9]⟩
  have hX5out : ∀ τ τ', X5 τ → τ' = { τ with out := τ'.out } → X5 τ' := by
    intro τ τ' ⟨⟨h0, h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ heq
    rw [heq]
    exact ⟨⟨h0.frame (S := []) (A := []) ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩ (by simp) (by simp)
      (fun _ _ => rfl), h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩
  have hl1 := loopC_out (B := B) (x := "g_e") (m := "g_C") (body := lit1) (N := (par Dt x).C)
    (Kb := 30) (by omega) X5 hX5set (fun τ h => h.1.1.C)
    (fun e => [if cfv = 0 ∨ e ≠ v1 then 2 * (par Dt x).zv b1 e else 0]) fun e he => by
      intro τ ⟨h, he'⟩
      obtain ⟨τ', hr, ho, heq⟩ := lit1_spec hB hb1 he hcf1 τ ⟨h.1.2.1, h.1.2.2.2.1, he', h.2.2.2,
        h.1.1.W, by omega⟩
      exact ⟨τ', hr, hX5out τ τ' h heq, by rw [heq]; exact he', ho⟩
  obtain ⟨σ4, hr4, hX4, o4⟩ := hl1 σ3 hX5
  have hl2 := loopC_out (B := B) (x := "g_e") (m := "g_C") (body := lit2) (N := (par Dt x).C)
    (Kb := 30) (by omega) X5 hX5set (fun τ h => h.1.1.C)
    (fun e => [if cfv = 1 ∧ e ≠ v2 then 2 * (par Dt x).zv b2 e else 0]) fun e he => by
      intro τ ⟨h, he'⟩
      obtain ⟨τ', hr, ho, heq⟩ := lit2_spec hB hb2 he hcf1 τ ⟨h.1.2.2.2.2.2.1, h.2.1, he', h.2.2.2,
        h.1.1.W, by omega⟩
      exact ⟨τ', hr, hX5out τ τ' h heq, by rw [heq]; exact he', ho⟩
  obtain ⟨σ5, hr5, hX5', o5⟩ := hl2 σ4 hX4
  have hm1 : (List.range (par Dt x).C).map (fun e => if cfv = 0 ∨ e ≠ v1 then
      2 * (par Dt x).zv b1 e else 0) = (List.range (par Dt x).C).map (fun e =>
      if (par Dt x).cf b1 v1 b2 v2 = false ∨ e ≠ v1 then 2 * (par Dt x).zv b1 e else 0) := by
    refine List.map_congr_left fun e _ => ?_
    by_cases h : cfv = 0
    · rw [if_pos (Or.inl h), if_pos (Or.inl (hcfe.mp h))]
    · have h' : (par Dt x).cf b1 v1 b2 v2 = true := by
        cases hc : (par Dt x).cf b1 v1 b2 v2
        · exact absurd (hcfe.mpr hc) h
        · rfl
      by_cases he : e = v1
      · rw [if_neg (by tauto), if_neg (by rw [h']; tauto)]
      · rw [if_pos (Or.inr he), if_pos (Or.inr he)]
  have hm2 : (List.range (par Dt x).C).map (fun e => if cfv = 1 ∧ e ≠ v2 then
      2 * (par Dt x).zv b2 e else 0) = (List.range (par Dt x).C).map (fun e =>
      if (par Dt x).cf b1 v1 b2 v2 = true ∧ e ≠ v2 then 2 * (par Dt x).zv b2 e else 0) := by
    refine List.map_congr_left fun e _ => ?_
    by_cases h : cfv = 1
    · have h' := hcfe1.mp h
      by_cases he : e = v2
      · rw [if_neg (by tauto), if_neg (by tauto)]
      · rw [if_pos ⟨h, he⟩, if_pos ⟨h', he⟩]
    · have h' : (par Dt x).cf b1 v1 b2 v2 = false := by
        cases hc : (par Dt x).cf b1 v1 b2 v2
        · rfl
        · exact absurd (hcfe1.mpr hc) h
      rw [if_neg (by tauto), if_neg (by rw [h']; simp)]
  refine ⟨σ5, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq Run.skip))))).mono
    (by simp [Kx2, Expr.size]; omega), hX5'.1, hX5'.2.1, ?_⟩
  rw [o5, o4, hσ3, o2, o1]
  simp only [xWords, List.append_assoc, List.cons_append, List.nil_append, flatMap_single]
  rw [hg2.C2, hm1, hm2]

/-- A decoded array keeps the context. -/
theorem gcDec {σ σ' : Env} {arr : String} (hg : GC Dt x σ) (hf : Frame ["g_w"] [arr] σ σ')
    (harr : arr ∈ gcArrs) (hlen : (σ'.arrs arr).length = (σ.arrs arr).length) : GC Dt x σ' :=
  hg.frame hf (by simp [gcVars]) (by simpa using harr) (fun b _ => by
    by_cases h : b = arr
    · subst h; exact hlen
    · rw [hf.2.1 _ (by simpa using h)])

/-- The context of the loop over `v2`. -/
def X3 (Dt : Data) (x : List ℕ) (b1 v1 : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_b1" = b1 ∧ σ.arrs "bd1" = (par Dt x).bd b1 ∧ σ.vars "g_v1" = v1 ∧
    σ.arrs "vd1" = (par Dt x).vd v1

/-- The context of the loop over `v1`. -/
def X2 (Dt : Data) (x : List ℕ) (b1 : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_b1" = b1 ∧ σ.arrs "bd1" = (par Dt x).bd b1

def Kxb2 (Dt : Data) (x : List ℕ) : ℕ := (20 * Dt.D + 3) + ((Kx2 Dt x + 8) * (par Dt x).C + 6)

def Kxv1 (Dt : Data) (x : List ℕ) : ℕ := (20 * Dt.D + 3) + ((Kxb2 Dt x + 8) * (par Dt x).W + 6)

def Kxb1 (Dt : Data) (x : List ℕ) : ℕ := (20 * Dt.D + 3) + ((Kxv1 Dt x + 8) * (par Dt x).C + 6)

/-- The cost of phase X. -/
def KX (Dt : Data) (x : List ℕ) : ℕ := (Kxb1 Dt x + 8) * (par Dt x).W + 6

set_option maxHeartbeats 2000000 in
theorem xb2_spec (hB : BB Dt x B) {b1 v1 : ℕ} (hb1 : b1 < (par Dt x).W)
    (hv1 : v1 < (par Dt x).C) (b2 : ℕ) (hb2 : b2 < (par Dt x).W) :
    Spec B (fun σ => X3 Dt x b1 v1 σ ∧ σ.vars "g_b2" = b2) (xb2Body Dt.D)
      (fun σ σ' => X3 Dt x b1 v1 σ' ∧ σ'.vars "g_b2" = b2 ∧
        σ'.out = σ.out ++ (List.range (par Dt x).C).flatMap (xWords Dt x b1 v1 b2)) (Kxb2 Dt x) := by
  intro σ ⟨⟨hg, e1, a1, e2, a2⟩, e3⟩
  have hs := hB.small
  obtain ⟨σ1, hr1, d1, f1, o1⟩ := decB_spec hB (src := "g_b2") (arr := "bd2") hb2 σ
    ⟨hg, e3, hg.bd2⟩
  have hg1 : GC Dt x σ1 := gcDec hg f1 (by simp [gcArrs]) (by rw [d1, hg.bd2, length_bd])
  have hX4 : X4 Dt x b1 v1 b2 σ1 :=
    ⟨hg1, by rw [f1.1 _ (by decide)]; exact e1, by rw [f1.2.1 _ (by decide)]; exact a1,
      by rw [f1.1 _ (by decide)]; exact e2, by rw [f1.2.1 _ (by decide)]; exact a2,
      by rw [f1.1 _ (by decide)]; exact e3, d1⟩
  have hl := loopC_out (B := B) (x := "g_v2") (m := "g_C") (body := xv2Body Dt.D)
    (N := (par Dt x).C) (Kb := Kx2 Dt x) (by omega) (X4 Dt x b1 v1 b2)
    (fun τ w ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h0.setVar (by simp [gcVars]) w,
      by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
      by simp [Env.setVar, h4], by simp [Env.setVar, h5], by simp [Env.setVar, h6]⟩)
    (fun τ h => h.1.C) (xWords Dt x b1 v1 b2) (fun v2 hv2 => xv2_spec hB hb1 hv1 hb2 v2 hv2)
  obtain ⟨σ2, hr2, ⟨h0, h1, h2, h3, h4, h5, -⟩, o2⟩ := hl σ1 hX4
  exact ⟨σ2, (hr1.seq hr2).mono (by simp [Kxb2]), ⟨h0, h1, h2, h3, h4⟩, h5,
    by rw [o2, o1]⟩

set_option maxHeartbeats 2000000 in
theorem xv1_spec (hB : BB Dt x B) {b1 : ℕ} (hb1 : b1 < (par Dt x).W)
    (v1 : ℕ) (hv1 : v1 < (par Dt x).C) :
    Spec B (fun σ => X2 Dt x b1 σ ∧ σ.vars "g_v1" = v1) (xv1Body Dt.D)
      (fun σ σ' => X2 Dt x b1 σ' ∧ σ'.vars "g_v1" = v1 ∧
        σ'.out = σ.out ++ (List.range (par Dt x).W).flatMap fun b2 =>
          (List.range (par Dt x).C).flatMap (xWords Dt x b1 v1 b2)) (Kxv1 Dt x) := by
  intro σ ⟨⟨hg, e1, a1⟩, e2⟩
  have hs := hB.small
  obtain ⟨σ1, hr1, d1, f1, o1⟩ := decV_spec hB (src := "g_v1") (arr := "vd1") hv1 σ
    ⟨hg, e2, hg.vd1⟩
  have hg1 : GC Dt x σ1 := gcDec hg f1 (by simp [gcArrs]) (by rw [d1, hg.vd1, length_vd])
  have hX3 : X3 Dt x b1 v1 σ1 :=
    ⟨hg1, by rw [f1.1 _ (by decide)]; exact e1, by rw [f1.2.1 _ (by decide)]; exact a1,
      by rw [f1.1 _ (by decide)]; exact e2, d1⟩
  have hl := loopC_out (B := B) (x := "g_b2") (m := "g_W") (body := xb2Body Dt.D)
    (N := (par Dt x).W) (Kb := Kxb2 Dt x) (by omega) (X3 Dt x b1 v1)
    (fun τ w ⟨h0, h1, h2, h3, h4⟩ => ⟨h0.setVar (by simp [gcVars]) w,
      by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
      by simp [Env.setVar, h4]⟩)
    (fun τ h => h.1.W) (fun b2 => (List.range (par Dt x).C).flatMap (xWords Dt x b1 v1 b2))
    (fun b2 hb2 => xb2_spec hB hb1 hv1 b2 hb2)
  obtain ⟨σ2, hr2, ⟨h0, h1, h2, h3, -⟩, o2⟩ := hl σ1 hX3
  exact ⟨σ2, (hr1.seq hr2).mono (by simp [Kxv1]), ⟨h0, h1, h2⟩, h3, by rw [o2, o1]⟩

set_option maxHeartbeats 2000000 in
theorem xb1_spec (hB : BB Dt x B) (b1 : ℕ) (hb1 : b1 < (par Dt x).W) :
    Spec B (fun σ => GC Dt x σ ∧ σ.vars "g_b1" = b1) (xb1Body Dt.D)
      (fun σ σ' => GC Dt x σ' ∧ σ'.vars "g_b1" = b1 ∧
        σ'.out = σ.out ++ (List.range (par Dt x).C).flatMap fun v1 =>
          (List.range (par Dt x).W).flatMap fun b2 =>
            (List.range (par Dt x).C).flatMap (xWords Dt x b1 v1 b2)) (Kxb1 Dt x) := by
  intro σ ⟨hg, e1⟩
  have hs := hB.small
  obtain ⟨σ1, hr1, d1, f1, o1⟩ := decB_spec hB (src := "g_b1") (arr := "bd1") hb1 σ
    ⟨hg, e1, hg.bd1⟩
  have hg1 : GC Dt x σ1 := gcDec hg f1 (by simp [gcArrs]) (by rw [d1, hg.bd1, length_bd])
  have hX2 : X2 Dt x b1 σ1 := ⟨hg1, by rw [f1.1 _ (by decide)]; exact e1, d1⟩
  have hl := loopC_out (B := B) (x := "g_v1") (m := "g_C") (body := xv1Body Dt.D)
    (N := (par Dt x).C) (Kb := Kxv1 Dt x) (by omega) (X2 Dt x b1)
    (fun τ w ⟨h0, h1, h2⟩ => ⟨h0.setVar (by simp [gcVars]) w, by simp [Env.setVar, h1],
      by simp [Env.setVar, h2]⟩)
    (fun τ h => h.1.C) (fun v1 => (List.range (par Dt x).W).flatMap fun b2 =>
      (List.range (par Dt x).C).flatMap (xWords Dt x b1 v1 b2))
    (fun v1 hv1 => xv1_spec hB hb1 v1 hv1)
  obtain ⟨σ2, hr2, ⟨h0, h1, -⟩, o2⟩ := hl σ1 hX2
  exact ⟨σ2, (hr1.seq hr2).mono (by simp [Kxb1]), h0, h1, by rw [o2, o1]⟩

/-- **Phase X.** -/
theorem phaseX_spec (hB : BB Dt x B) :
    Spec B (GC Dt x) (phaseX Dt.D)
      (fun σ σ' => GC Dt x σ' ∧ σ'.out = σ.out ++ xAll Dt x) (KX Dt x) := by
  have hs := hB.small
  exact loopC_out (by omega) (GC Dt x) (fun σ v h => h.setVar (by simp [gcVars]) v)
    (fun σ h => h.W) _ (fun b1 hb1 => xb1_spec hB b1 hb1)

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX
