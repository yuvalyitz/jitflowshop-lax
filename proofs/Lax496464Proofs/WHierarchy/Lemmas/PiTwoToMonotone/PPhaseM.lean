import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval

/-!
# Phase M: the clauses of the universal assignments

Loops over `za` (its digits into `od[q..r)`), the blocks `b1`, the values `v1` and `zb` (its digits
into `od[0..q)`); for each, the evaluation of `ψ` and the literal of `OutW.mWords`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseM

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF DsOk Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath (Good)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval

variable {B : ℕ} {Dt : Data} {x : List ℕ}

/-- The context of the innermost loop. -/
def M4 (Dt : Data) (x : List ℕ) (za b1 v1 : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_za" = za ∧ (σ.arrs "od").drop Dt.q = digits (nU Dt x) Dt.p za ∧
    σ.vars "g_b1" = b1 ∧ σ.arrs "bd1" = (par Dt x).bd b1 ∧ σ.vars "g_v1" = v1 ∧
    σ.arrs "vd1" = (par Dt x).vd v1

theorem digits_lt_of {n e z : ℕ} (hz : z < n ^ e) : ∀ d ∈ digits n e z, d < n := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [digits]
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h, zero_pow (by omega)] at hz; omega
      · exact h
    exact digits_lt hn e z

theorem dsOk_of {za zb : ℕ} (hza : za < nU Dt x ^ Dt.p) (hzb : zb < nU Dt x ^ Dt.q) :
    DsOk (wd Dt) x (dsOf Dt x za zb) := by
  refine ⟨by simp [dsOf, wd, Data.r], fun d hd => ?_⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact digits_lt_of hzb d hd
  · exact digits_lt_of hza d hd

set_option maxHeartbeats 2000000 in
/-- The literal of `Z(b1, v1)` under `(za, zb)`. -/
theorem litM_spec (hB : BB Dt x B) {b1 v1 : ℕ} (hb1 : b1 < (par Dt x).W) (hv1 : v1 < (par Dt x).C)
    (r : Bool × Bool) :
    Spec B (fun σ => σ.vars "g_b1" = b1 ∧ σ.vars "g_v1" = v1 ∧ σ.vars "g_W" = (par Dt x).W ∧
        σ.vars "w_f" = bn r.1 ∧ σ.vars "g_und" = bn r.2) litM
      (fun σ σ' => σ'.out = σ.out ++ [if (r == (true, false)) = true then 2 * (par Dt x).zv b1 v1
        else 0] ∧ σ' = { σ with out := σ'.out }) 30 := by
  intro σ ⟨h1, h2, h3, h4, h5⟩
  have hs := hB.small
  obtain ⟨σ', hw, ho, heq⟩ := litWrite_spec hB hb1 hv1 "g_b1" "g_v1" σ ⟨h1, h2, h3⟩
  have ef := evalB_var (B := B) (σ := σ) (x := "w_f") (by rw [h4]; have := bn_le_one r.1; omega)
  have eu := evalB_var (B := B) (σ := σ) (x := "g_und") (by rw [h5]; have := bn_le_one r.2; omega)
  have e0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have e1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
  have hw0 := RunStep.write B σ (.lit 0) 0 e0
  obtain ⟨r1, r2⟩ := r
  cases r1 <;> cases r2
  · refine ⟨_, (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ef e1
      (by rw [h4]; simp)) hw0).mono (by simp [Cond.size, Expr.size]), by simp, rfl⟩
  · refine ⟨_, (RunStep.ite_false B _ _ _ σ _ _ (RunStep.cond_eq_false B σ _ _ _ _ ef e1
      (by rw [h4]; simp)) hw0).mono (by simp [Cond.size, Expr.size]), by simp, rfl⟩
  · refine ⟨σ', (RunStep.ite_true B _ _ _ σ _ _ (RunStep.cond_eq_true B σ _ _ _ _ ef e1
      (by rw [h4]; simp)) (RunStep.ite_true B _ _ _ σ _ _
        (RunStep.cond_eq_true B σ _ _ _ _ eu e0 (by rw [h5]; simp)) hw)).mono
      (by simp [Cond.size, Expr.size]), by rw [ho]; simp, heq⟩
  · refine ⟨_, (RunStep.ite_true B _ _ _ σ _ _ (RunStep.cond_eq_true B σ _ _ _ _ ef e1
      (by rw [h4]; simp)) (RunStep.ite_false B _ _ _ σ _ _
        (RunStep.cond_eq_false B σ _ _ _ _ eu e0 (by rw [h5]; simp)) hw0)).mono
      (by simp [Cond.size, Expr.size]), by simp, rfl⟩

def Kmzb (Dt : Data) (x : List ℕ) : ℕ := 2 + (20 * Dt.q + 1) + 2 + Kev Dt x Dt.ψ + 30 + 1

def Kmv (Dt : Data) (x : List ℕ) : ℕ := (20 * Dt.D + 3) + ((Kmzb Dt x + 8) * (par Dt x).Q + 6)

def Kmb (Dt : Data) (x : List ℕ) : ℕ := (20 * Dt.D + 3) + ((Kmv Dt x + 8) * (par Dt x).C + 6)

def Kmza (Dt : Data) (x : List ℕ) : ℕ :=
  2 + (20 * Dt.p + 1) + 2 + ((Kmb Dt x + 8) * (par Dt x).W + 6) + 1

/-- The cost of phase M. -/
def KM (Dt : Data) (x : List ℕ) : ℕ := (Kmza Dt x + 8) * (par Dt x).P + 6

section
variable (hB : BB Dt x B) (hgood : Good x) (hA : AtomsOk Dt x Dt.ψ)
include hB hgood hA

set_option maxHeartbeats 4000000 in
/-- One existential assignment. -/
theorem mzb_spec {za b1 v1 : ℕ} (hza : za < (par Dt x).P) (hb1 : b1 < (par Dt x).W)
    (hv1 : v1 < (par Dt x).C) (zb : ℕ) (hzb : zb < (par Dt x).Q) :
    Spec B (fun σ => M4 Dt x za b1 v1 σ ∧ σ.vars "g_zb" = zb) (mzbBody Dt)
      (fun σ σ' => M4 Dt x za b1 v1 σ' ∧ σ'.vars "g_zb" = zb ∧
        σ'.out = σ.out ++ [if good Dt x za b1 v1 zb = true then 2 * (par Dt x).zv b1 v1 else 0])
      (Kmzb Dt x) := by
  intro σ ⟨⟨hg, e1, dza, e2, a2, e3, a3⟩, e4⟩
  have hs := hB.small
  have hQ := hB.Q_lt
  have hnB : nU Dt x < B := by have := hB.bf.n; exact lt_of_le_of_lt (Nat.le_succ _) this
  -- the digits of `zb`
  have hr1 := RunStep.assign B σ "g_w" (V "g_zb") zb (by rw [← e4]; exact evalB_var (by rw [e4]; omega))
  obtain ⟨σ2, hr2, d2, f2, o2⟩ := decG_spec (B := B) (arr := "od") (w := "g_w") (bs := "w_n")
    (by decide) hnB (L := Dt.r) Dt.q 0 zb (by omega) (by simp only [Data.r]; omega) (by
      have h := hs.2.2.2.2.2.2.2.1; simp only [Data.r] at h; omega) (σ.setVar "g_w" zb)
    ⟨by simp [Env.setVar], by simp [Env.setVar]; exact hg.ctx.n, by simp [Env.setVar]; exact hg.ctx.odlen⟩
  have hod2 : σ2.arrs "od" = dsOf Dt x za zb := by
    rw [d2]
    have : (σ.setVar "g_w" zb).arrs "od" = σ.arrs "od" := rfl
    rw [this, Nat.zero_add, dza]; simp [dsOf]
  have hg2 : GC Dt x σ2 := (hg.setVar (by simp [gcVars]) zb).frame f2 (by simp [gcVars])
    (by simp [gcArrs]) (fun b _ => by
      by_cases h : b = "od"
      · subst h; rw [hod2]; simp [dsOf, Env.setVar, hg.ctx.odlen, wd, Data.r]
      · rw [f2.2.1 _ (by simpa using h)])
  -- `und := 0`
  have hr3 := RunStep.assign B σ2 "g_und" (.lit 0) 0 (evalB_lit (by omega))
  set σ3 := σ2.setVar "g_und" 0 with hσ3
  have hg3 : GC Dt x σ3 := hg2.setVar (by simp [gcVars]) 0
  have hk3 : ∀ y ∈ ["g_za", "g_b1", "g_v1", "g_zb"], σ3.vars y = σ.vars y := by
    intro y hy
    simp only [hσ3, Env.setVar]
    rw [if_neg (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide)]
    rw [f2.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl <;> decide)]
    simp only [Env.setVar]
    rw [if_neg (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide)]
  have ha3 : ∀ b ∈ ["bd1", "vd1"], σ3.arrs b = σ.arrs b := fun b hb => by
    show σ2.arrs b = _
    rw [f2.2.1 b (by simp at hb ⊢; rcases hb with rfl | rfl <;> decide)]; rfl
  -- the evaluation
  have hEB : EB B Dt x ((par Dt x).bd b1) ((par Dt x).vd v1) :=
    ⟨hB.bf, hgood, length_bd _, length_vd _, by omega, by omega, by omega,
      fun j => by have := bd_le (Dt := Dt) (x := x) b1 j; omega,
      fun j => by have := vd_le (Dt := Dt) (x := x) v1 j; omega⟩
  obtain ⟨σ4, hr4, w4, u4, f4, o4⟩ := evalCom_spec (dsOk_of hza hzb) hEB rfl rfl Dt.ψ hA σ3
    ⟨hg3.ctx, by show σ2.arrs "od" = _; exact hod2, by rw [ha3 _ (by simp)]; exact a2,
      by rw [ha3 _ (by simp)]; exact a3, hg3.k, hg3.D, hg3.DD⟩
  have hg4 : GC Dt x σ4 := hg3.frame f4 (by simp [evVars, gcVars]) (by simp) (fun b _ => by
    rw [f4.2.1 _ (by simp)])
  set r := ev (oracle Dt x (dsOf Dt x za zb) b1 v1) Dt.ψ with hr
  have hu4 : σ4.vars "g_und" = bn r.2 := by
    rw [u4]; simp only [hσ3, Env.setVar, if_true]
  have hv4 : ∀ y ∈ ["g_za", "g_b1", "g_v1", "g_zb", "g_W"], σ4.vars y = σ3.vars y := fun y hy =>
    f4.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨σ5, hr5, o5, heq5⟩ := litM_spec hB hb1 hv1 r σ4
    ⟨by rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e2,
      by rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e3, hg4.W, w4, hu4⟩
  refine ⟨σ5, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq Run.skip))))).mono
    (by simp [Kmzb, Expr.size]; omega), ?_, ?_, ?_⟩
  · rw [heq5]
    refine ⟨hg4.frame (S := []) (A := []) ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩ (by simp) (by simp)
      (fun _ _ => rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ4.vars _ = _; rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e1
    · show (σ4.arrs "od").drop _ = _
      rw [f4.2.1 _ (by simp)]; show (σ2.arrs "od").drop _ = _
      rw [hod2]; simp [dsOf]
    · show σ4.vars _ = _; rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e2
    · show σ4.arrs _ = _; rw [f4.2.1 _ (by simp), ha3 _ (by simp)]; exact a2
    · show σ4.vars _ = _; rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e3
    · show σ4.arrs _ = _; rw [f4.2.1 _ (by simp), ha3 _ (by simp)]; exact a3
  · rw [heq5]; show σ4.vars _ = _; rw [hv4 _ (by simp), hk3 _ (by simp)]; exact e4
  · rw [o5, o4]
    show σ2.out ++ _ = _
    rw [o2]
    rfl

/-- The context of the loop over `v1`. -/
def M3 (Dt : Data) (x : List ℕ) (za b1 : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_za" = za ∧ (σ.arrs "od").drop Dt.q = digits (nU Dt x) Dt.p za ∧
    σ.vars "g_b1" = b1 ∧ σ.arrs "bd1" = (par Dt x).bd b1

/-- The context of the loop over `b1`. -/
def M2 (Dt : Data) (x : List ℕ) (za : ℕ) (σ : Env) : Prop :=
  GC Dt x σ ∧ σ.vars "g_za" = za ∧ (σ.arrs "od").drop Dt.q = digits (nU Dt x) Dt.p za

set_option maxHeartbeats 2000000 in
theorem mv_spec {za b1 : ℕ} (hza : za < (par Dt x).P) (hb1 : b1 < (par Dt x).W)
    (v1 : ℕ) (hv1 : v1 < (par Dt x).C) :
    Spec B (fun σ => M3 Dt x za b1 σ ∧ σ.vars "g_v1" = v1) (mvBody Dt)
      (fun σ σ' => M3 Dt x za b1 σ' ∧ σ'.vars "g_v1" = v1 ∧
        σ'.out = σ.out ++ (List.range (par Dt x).Q).flatMap fun zb =>
          [if good Dt x za b1 v1 zb = true then 2 * (par Dt x).zv b1 v1 else 0]) (Kmv Dt x) := by
  intro σ ⟨⟨hg, e1, d1, e2, a2⟩, e3⟩
  have hs := hB.small; have hQ := hB.Q_lt
  obtain ⟨σ1, hr1, dv, f1, o1⟩ := decV_spec hB (src := "g_v1") (arr := "vd1") hv1 σ
    ⟨hg, e3, hg.vd1⟩
  have hg1 : GC Dt x σ1 := gcDec hg f1 (by simp [gcArrs]) (by rw [dv, hg.vd1, length_vd])
  have hM4 : M4 Dt x za b1 v1 σ1 :=
    ⟨hg1, by rw [f1.1 _ (by decide)]; exact e1, by rw [f1.2.1 _ (by decide)]; exact d1,
      by rw [f1.1 _ (by decide)]; exact e2, by rw [f1.2.1 _ (by decide)]; exact a2,
      by rw [f1.1 _ (by decide)]; exact e3, dv⟩
  have hl := loopC_out (B := B) (x := "g_zb") (m := "g_Q") (body := mzbBody Dt)
    (N := (par Dt x).Q) (Kb := Kmzb Dt x) (by omega) (M4 Dt x za b1 v1)
    (fun τ w ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h0.setVar (by simp [gcVars]) w,
      by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
      by simp [Env.setVar, h4], by simp [Env.setVar, h5], by simp [Env.setVar, h6]⟩)
    (fun τ h => h.1.Q) _ (fun zb hzb => mzb_spec hB hgood hA hza hb1 hv1 zb hzb)
  obtain ⟨σ2, hr2, ⟨h0, h1, h2, h3, h4, h5, -⟩, o2⟩ := hl σ1 hM4
  exact ⟨σ2, (hr1.seq hr2).mono (by simp [Kmv]), ⟨h0, h1, h2, h3, h4⟩, h5, by rw [o2, o1]⟩

set_option maxHeartbeats 2000000 in
theorem mb_spec {za : ℕ} (hza : za < (par Dt x).P) (b1 : ℕ) (hb1 : b1 < (par Dt x).W) :
    Spec B (fun σ => M2 Dt x za σ ∧ σ.vars "g_b1" = b1) (mbBody Dt)
      (fun σ σ' => M2 Dt x za σ' ∧ σ'.vars "g_b1" = b1 ∧
        σ'.out = σ.out ++ (List.range (par Dt x).C).flatMap fun v1 =>
          (List.range (par Dt x).Q).flatMap fun zb =>
            [if good Dt x za b1 v1 zb = true then 2 * (par Dt x).zv b1 v1 else 0]) (Kmb Dt x) := by
  intro σ ⟨⟨hg, e1, d1⟩, e2⟩
  have hs := hB.small
  obtain ⟨σ1, hr1, db, f1, o1⟩ := decB_spec hB (src := "g_b1") (arr := "bd1") hb1 σ
    ⟨hg, e2, hg.bd1⟩
  have hg1 : GC Dt x σ1 := gcDec hg f1 (by simp [gcArrs]) (by rw [db, hg.bd1, length_bd])
  have hM3 : M3 Dt x za b1 σ1 :=
    ⟨hg1, by rw [f1.1 _ (by decide)]; exact e1, by rw [f1.2.1 _ (by decide)]; exact d1,
      by rw [f1.1 _ (by decide)]; exact e2, db⟩
  have hl := loopC_out (B := B) (x := "g_v1") (m := "g_C") (body := mvBody Dt)
    (N := (par Dt x).C) (Kb := Kmv Dt x) (by omega) (M3 Dt x za b1)
    (fun τ w ⟨h0, h1, h2, h3, h4⟩ => ⟨h0.setVar (by simp [gcVars]) w,
      by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
      by simp [Env.setVar, h4]⟩)
    (fun τ h => h.1.C) _ (fun v1 hv1 => mv_spec hB hgood hA hza hb1 v1 hv1)
  obtain ⟨σ2, hr2, ⟨h0, h1, h2, h3, -⟩, o2⟩ := hl σ1 hM3
  exact ⟨σ2, (hr1.seq hr2).mono (by simp [Kmb]), ⟨h0, h1, h2⟩, h3, by rw [o2, o1]⟩

set_option maxHeartbeats 4000000 in
theorem mza_spec (za : ℕ) (hza : za < (par Dt x).P) :
    Spec B (fun σ => GC Dt x σ ∧ σ.vars "g_za" = za) (mzaBody Dt)
      (fun σ σ' => GC Dt x σ' ∧ σ'.vars "g_za" = za ∧ σ'.out = σ.out ++ mWords Dt x za)
      (Kmza Dt x) := by
  intro σ ⟨hg, e1⟩
  have hs := hB.small
  have hnB : nU Dt x < B := by have := hB.bf.n; exact lt_of_le_of_lt (Nat.le_succ _) this
  have hr1 := RunStep.assign B σ "g_w" (V "g_za") za (by rw [← e1]; exact evalB_var (by rw [e1]; omega))
  have hrB : Dt.r < B := hs.2.2.2.2.2.2.2.1
  obtain ⟨σ2, hr2, d2, f2, o2⟩ := decG_spec (B := B) (arr := "od") (w := "g_w") (bs := "w_n")
    (by decide) hnB (L := Dt.r) Dt.p Dt.q za (by omega) (by simp only [Data.r]; omega)
    (by simp only [Data.r] at hrB; omega) (σ.setVar "g_w" za)
    ⟨by simp [Env.setVar], by simp [Env.setVar]; exact hg.ctx.n, by simp [Env.setVar]; exact hg.ctx.odlen⟩
  have hodl : (σ.arrs "od").length = Dt.r := hg.ctx.odlen
  have hodl' : (σ.arrs "od").length = Dt.q + Dt.p := hodl
  have hd2 : (σ2.arrs "od").drop Dt.q = digits (nU Dt x) Dt.p za := by
    rw [d2]
    have : (σ.setVar "g_w" za).arrs "od" = σ.arrs "od" := rfl
    rw [this, List.drop_of_length_le (l := σ.arrs "od") (by omega)]
    rw [List.append_nil, List.drop_append_of_le_length (by simp [hodl, Data.r])]
    simp
  have hg2 : GC Dt x σ2 := (hg.setVar (by simp [gcVars]) za).frame f2 (by simp [gcVars])
    (by simp [gcArrs]) (fun b _ => by
      by_cases h : b = "od"
      · subst h; rw [d2]; simp [Env.setVar, hodl, Data.r]
      · rw [f2.2.1 _ (by simpa using h)])
  have hr3 := RunStep.write B σ2 (V "g_WCQ") _ (evalB_var (by rw [hg2.WCQ]; exact hB.WCQ_lt))
  set σ3 := { σ2 with out := σ2.out ++ [σ2.vars "g_WCQ"] } with hσ3
  have hM2 : M2 Dt x za σ3 :=
    ⟨hg2.frame (S := []) (A := []) ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩ (by simp) (by simp)
      (fun _ _ => rfl), by show σ2.vars _ = _; rw [f2.1 _ (by decide)]; simp [Env.setVar, e1], hd2⟩
  have hl := loopC_out (B := B) (x := "g_b1") (m := "g_W") (body := mbBody Dt)
    (N := (par Dt x).W) (Kb := Kmb Dt x) (by omega) (M2 Dt x za)
    (fun τ w ⟨h0, h1, h2⟩ => ⟨h0.setVar (by simp [gcVars]) w, by simp [Env.setVar, h1],
      by simp [Env.setVar, h2]⟩)
    (fun τ h => h.1.W) _ (fun b1 hb1 => mb_spec hB hgood hA hza b1 hb1)
  obtain ⟨σ4, hr4, ⟨h0, h1, -⟩, o4⟩ := hl σ3 hM2
  refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq (hr4.seq Run.skip)))).mono (le_of_eq (by simp [Kmza, Expr.size]; ring)),
    h0, h1, ?_⟩
  rw [o4, hσ3, hg2.WCQ, o2]
  simp only [mWords, flatMap_single, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- **Phase M.** -/
theorem phaseM_spec :
    Spec B (GC Dt x) (phaseM Dt)
      (fun σ σ' => GC Dt x σ' ∧ σ'.out = σ.out ++ (List.range (par Dt x).P).flatMap (mWords Dt x))
      (KM Dt x) := by
  have hs := hB.small
  exact loopC_out (by omega) (GC Dt x) (fun σ v h => h.setVar (by simp [gcVars]) v)
    (fun σ h => h.P) _ (fun za hza => mza_spec hB hgood hA za hza)

end

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseM
