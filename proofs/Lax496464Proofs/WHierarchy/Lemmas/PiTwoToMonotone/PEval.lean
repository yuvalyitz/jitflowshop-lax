import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ

/-!
# The evaluation of the quantifier-free formula

`evalCom_spec`: with the digits `ds` of an assignment in `od` and a block with values in `bd1, vd1`,
`evalCom ψ` computes `Eval.ev` of the oracle `Out.oracle`: `w_f` is its value, and `g_und` is set if
an undecided `X`-atom is met. By induction on `ψ`; the relation atoms and equations are the
atoms of `Lemmas/WDToWSat` (`relCom_value`, `eqCom_value`), an `X`-atom is the code of its tuple
(`codeCom_spec`) followed by the decision (`PDec.decCom_spec`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList relCom atomCom codeCom)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF DsOk Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath (Good)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom (relCom_value Krel)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause (eqCom_value codeCom_spec atom_frame zS zA ZPre)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec

variable {B : ℕ} {Dt : Data} {x : List ℕ}

/-- The scalars the evaluation assigns. -/
def evVars : List String :=
  ["w_bs", "w_cnt", "w_f", "w_t", "w_mt", "w_st", "w_c", "g_fT", "g_j", "g_fF", "g_i", "g_j2",
    "g_und"]

/-- The state the evaluation runs in. -/
def EvCtx (Dt : Data) (x ds bl vl : List ℕ) (σ : Env) : Prop :=
  Ctx (wd Dt) x σ ∧ σ.arrs "od" = ds ∧ σ.arrs "bd1" = bl ∧ σ.arrs "vd1" = vl ∧
    σ.vars "w_k" = kW x ∧ σ.vars "g_D" = Dt.D ∧ σ.vars "g_DD" = Dt.D * Dt.D

theorem EvCtx.frame {ds bl vl : List ℕ} {σ σ' : Env} {S : List String}
    (h : EvCtx Dt x ds bl vl σ) (hf : Frame S [] σ σ') (hS : ∀ y ∈ S, y ∈ evVars) :
    EvCtx Dt x ds bl vl σ' := by
  obtain ⟨hc, h1, h2, h3, h4, h5, h6⟩ := h
  have hv : ∀ y, y ∉ evVars → σ'.vars y = σ.vars y := fun y hy => hf.1 y fun hm => hy (hS y hm)
  exact ⟨hc.frame hf (fun hm => by have := hS _ hm; simp [evVars] at this) ⟨by simp, by simp, by simp,
      by simp⟩, by rw [hf.2.1 _ (by simp)]; exact h1, by rw [hf.2.1 _ (by simp)]; exact h2,
    by rw [hf.2.1 _ (by simp)]; exact h3, by rw [hv _ (by simp [evVars])]; exact h4,
    by rw [hv _ (by simp [evVars])]; exact h5, by rw [hv _ (by simp [evVars])]; exact h6⟩

/-- The atoms of the formula fit the word and have positions below `r`. -/
def AtomsOk (Dt : Data) (x : List ℕ) (ψ : Formula) : Prop :=
  ∀ a ∈ atoms ψ, (∀ i js, a = .rel i js → i < spW x ∧ js.length = x.getD (1 + i) 0 ∧
      ∀ j ∈ js, j < Dt.r) ∧ (∀ a1 a2, a = .eq a1 a2 → a1 < Dt.r ∧ a2 < Dt.r) ∧
    (∀ js, a = .setVar js → js.length = Dt.s ∧ ∀ j ∈ js, j < Dt.r)

theorem AtomsOk.sub {ψ φ : Formula} (h : AtomsOk Dt x ψ) (hs : ∀ a ∈ atoms φ, a ∈ atoms ψ) :
    AtomsOk Dt x φ := fun a ha => h a (hs a ha)

/-- The cost of the evaluation. -/
def Kev (Dt : Data) (x : List ℕ) : Formula → ℕ
  | .rel _ js => Krel x js
  | .eq _ _ => 12
  | .setVar js => 7 * js.length + 2 + Kdec Dt.D
  | .neg φ => Kev Dt x φ + 6
  | .and φ ψ => Kev Dt x φ + Kev Dt x ψ + 6
  | .or φ ψ => Kev Dt x φ + Kev Dt x ψ + 6
  | .ex _ _ => 2
  | .all _ _ => 2

/-- The bounds the evaluation needs. -/
structure EB (B : ℕ) (Dt : Data) (x bl vl : List ℕ) : Prop where
  bf : BF (wd Dt) x B
  good : Good x
  hbl : bl.length = Dt.D
  hvl : vl.length = Dt.D
  hk : kW x + 1 < B
  hN : nU Dt x ^ Dt.s + 1 < B
  hD : Dt.D * Dt.D + Dt.D + 1 < B
  hb : ∀ j, bl.getD j 0 + 1 < B
  hv : ∀ j, vl.getD j 0 + 1 < B

set_option maxHeartbeats 4000000 in
/-- **The evaluation.** -/
theorem evalCom_spec {ds bl vl : List ℕ} (hds : DsOk (wd Dt) x ds) (hb : EB B Dt x bl vl)
    {b v : ℕ} (hbl : bl = (par Dt x).bd b) (hvl : vl = (par Dt x).vd v) :
    ∀ ψ : Formula, AtomsOk Dt x ψ →
    Spec B (EvCtx Dt x ds bl vl) (evalCom ψ)
      (fun σ σ' => σ'.vars "w_f" = bn (ev (oracle Dt x ds b v) ψ).1 ∧
        σ'.vars "g_und" = (if (ev (oracle Dt x ds b v) ψ).2 then 1 else σ.vars "g_und") ∧
        Frame evVars [] σ σ' ∧ σ'.out = σ.out) (Kev Dt x ψ)
  | .rel i js, hA => by
    obtain ⟨hi, hjl, hjs⟩ := (hA _ (by simp [atoms])).1 i js rfl
    have h := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx.Spec.framedOut (relCom_value hb.bf hb.good hds hi hjl hjs) zA []
      (atom_frame (.rel i js)).1 (atom_frame (.rel i js)).2.1
      (atom_frame (.rel i js)).2.2.1 (atom_frame (.rel i js)).2.2.2
    intro σ hσ
    obtain ⟨σ', hr, e, fr, o⟩ := h σ ⟨hσ.1, hσ.2.1⟩
    refine ⟨σ', hr, ?_, ?_, fr.mono (by simp [zA, evVars]) (by simp), o⟩
    · rw [e]
      show (if memW x i (js.map (elemOf Dt x ds)) then 1 else 0) = _
      by_cases hP : memW x i (js.map (elemOf Dt x ds)) <;> simp [ev, oracle, hP]
    · simp only [ev, Bool.false_eq_true, if_false]
      exact fr.1 _ (by simp [zA])
  | .eq a c, hA => by
    obtain ⟨ha, hc⟩ := (hA _ (by simp [atoms])).2.1 a c rfl
    have h := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx.Spec.framedOut (eqCom_value hb.bf hds ha hc) zA []
      (atom_frame (.eq a c)).1 (atom_frame (.eq a c)).2.1
      (atom_frame (.eq a c)).2.2.1 (atom_frame (.eq a c)).2.2.2
    intro σ hσ
    obtain ⟨σ', hr, e, fr, o⟩ := h σ ⟨hσ.1, hσ.2.1⟩
    refine ⟨σ', hr, ?_, ?_, fr.mono (by simp [zA, evVars]) (by simp), o⟩
    · rw [e]
      show (if elemOf Dt x ds a = elemOf Dt x ds c then 1 else 0) = _
      by_cases hP : elemOf Dt x ds a = elemOf Dt x ds c <;> simp [ev, oracle, hP]
    · simp only [ev, Bool.false_eq_true, if_false]
      exact fr.1 _ (by simp [zA])
  | .setVar js, hA => by
    obtain ⟨hjl, hjs⟩ := (hA _ (by simp [atoms])).2.2 js rfl
    intro σ hσ
    obtain ⟨hc, hod, hbd, hvd, hk, hD, hDD⟩ := hσ
    set u := codeOf (nU Dt x) (js.map fun j => ds.getD j 0) with hu
    have hult : u < nU Dt x ^ Dt.s := by
      have := codeOf_lt (n := nU Dt x) (js.map fun j => ds.getD j 0) fun d hd => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
        exact hds.getD_lt (hjs j hj)
      rwa [List.length_map, hjl] at this
    obtain ⟨σ1, hr1, e1, fr1, o1⟩ := codeCom_spec hb.bf hds js hjs (by rw [hjl]; rfl) σ ⟨hc, hod⟩
    have hv1 : ∀ y, y ∉ zS → σ1.vars y = σ.vars y := fr1.1
    have ha1 : ∀ a, σ1.arrs a = σ.arrs a := fun a => fr1.2.1 a (by simp)
    have hDB : DB B (kW x) Dt.D u bl vl :=
      ⟨hb.hbl, hb.hvl, hb.hk, by have := hb.hN; omega, hb.hD, hb.hb, hb.hv⟩
    obtain ⟨σ2, hr2, e2, e2u, fr2, o2⟩ := decCom_spec hDB σ1
      ⟨by rw [ha1]; exact hbd, by rw [ha1]; exact hvd, by rw [hv1 _ (by simp [zS])]; exact hk,
        e1, by rw [hv1 _ (by simp [zS])]; exact hD, by rw [hv1 _ (by simp [zS])]; exact hDD⟩
    have hxd : (oracle Dt x ds b v).xdec js = dec (kW x) Dt.D bl vl u := by
      simp only [oracle, codeW, hbl, hvl, hu]
    refine ⟨σ2, (hr1.seq hr2).mono (by simp [Kev]), ?_, ?_,
      (fr1.mono (by simp [zS, evVars]) (by simp)).trans (fr2.mono (by simp [decVars, evVars])
        (by simp)), by rw [o2, o1]⟩
    · rw [e2]
      simp only [ev, hxd]
      cases hd : dec (kW x) Dt.D bl vl u with
      | none => simp
      | some bb => cases bb <;> simp
    · rw [e2u, hv1 _ (by simp [zS])]
      simp only [ev, hxd]
      cases hd : dec (kW x) Dt.D bl vl u with
      | none => simp
      | some bb => simp
  | .neg φ, hA => by
    have ih := evalCom_spec hds hb hbl hvl φ (hA.sub fun a ha => by simpa [atoms] using ha)
    intro σ hσ
    obtain ⟨σ1, hr1, e1, u1, fr1, o1⟩ := ih σ hσ
    have hwB : σ1.vars "w_f" < B := by
      rw [e1]; have := bn_le_one (ev (oracle Dt x ds b v) φ).1; have := hb.hk; omega
    have ev1 : (Expr.sub (.lit 1) (V "w_f")).evalB B σ1 = some (1 - σ1.vars "w_f") :=
      evalB_bin (evalB_lit (by have := hb.hk; omega)) (evalB_var hwB) (by
        simp only [Bop.apply_sub]; have := hb.hk; omega)
    have hr2 := RunStep.assign B σ1 "w_f" _ _ ev1
    refine ⟨_, (hr1.seq hr2).mono (by simp [Kev, Expr.size]), ?_, ?_,
      fr1.trans (Frame.setVar σ1 (by simp [evVars]) _), by rw [← o1]; rfl⟩
    · simp only [Env.setVar, if_true, e1, ev]
      cases (ev (oracle Dt x ds b v) φ).1 <;> rfl
    · simp only [Env.setVar, String.reduceEq, if_false, ev]; exact u1
  | .and φ ψ, hA => by
    have ih1 := evalCom_spec hds hb hbl hvl φ (hA.sub fun a ha => by simp [atoms, ha])
    have ih2 := evalCom_spec hds hb hbl hvl ψ (hA.sub fun a ha => by simp [atoms, ha])
    intro σ hσ
    obtain ⟨σ1, hr1, e1, u1, fr1, o1⟩ := ih1 σ hσ
    have hσ1 : EvCtx Dt x ds bl vl σ1 := hσ.frame fr1 (fun y hy => hy)
    have hwB : σ1.vars "w_f" < B := by
      rw [e1]; have := bn_le_one (ev (oracle Dt x ds b v) φ).1; have := hb.hk; omega
    have ev1 := evalB_var (B := B) (x := "w_f") hwB
    have ev2 : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit (by have := hb.hk; omega)
    cases h1 : (ev (oracle Dt x ds b v) φ).1
    · have hw : σ1.vars "w_f" = 0 := by rw [e1, h1]; rfl
      refine ⟨σ1, (hr1.seq (RunStep.ite_false B _ _ _ σ1 _ _
        (RunStep.cond_eq_false B σ1 _ _ _ _ ev1 ev2 (by omega)) (RunStep.skip B σ1))).mono
        (by simp [Kev, Cond.size, Expr.size]; omega), ?_, ?_, fr1, o1⟩
      · rw [hw]; simp [ev, h1]
      · rw [u1]; simp [ev, h1]
    · have hw : σ1.vars "w_f" = 1 := by rw [e1, h1]; rfl
      obtain ⟨σ2, hr2, e2, u2, fr2, o2⟩ := ih2 σ1 hσ1
      refine ⟨σ2, (hr1.seq (RunStep.ite_true B _ _ _ σ1 _ _
        (RunStep.cond_eq_true B σ1 _ _ _ _ ev1 ev2 hw) hr2)).mono
        (by simp [Kev, Cond.size, Expr.size]; omega), ?_, ?_, fr1.trans fr2, by rw [o2, o1]⟩
      · rw [e2]; simp [ev, h1]
      · rw [u2, u1]
        simp only [ev, h1, if_true]
        cases (ev (oracle Dt x ds b v) φ).2 <;> cases (ev (oracle Dt x ds b v) ψ).2 <;> simp
  | .or φ ψ, hA => by
    have ih1 := evalCom_spec hds hb hbl hvl φ (hA.sub fun a ha => by simp [atoms, ha])
    have ih2 := evalCom_spec hds hb hbl hvl ψ (hA.sub fun a ha => by simp [atoms, ha])
    intro σ hσ
    obtain ⟨σ1, hr1, e1, u1, fr1, o1⟩ := ih1 σ hσ
    have hσ1 : EvCtx Dt x ds bl vl σ1 := hσ.frame fr1 (fun y hy => hy)
    have hwB : σ1.vars "w_f" < B := by
      rw [e1]; have := bn_le_one (ev (oracle Dt x ds b v) φ).1; have := hb.hk; omega
    have ev1 := evalB_var (B := B) (x := "w_f") hwB
    have ev2 : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit (by have := hb.hk; omega)
    cases h1 : (ev (oracle Dt x ds b v) φ).1
    · have hw : σ1.vars "w_f" = 0 := by rw [e1, h1]; rfl
      obtain ⟨σ2, hr2, e2, u2, fr2, o2⟩ := ih2 σ1 hσ1
      refine ⟨σ2, (hr1.seq (RunStep.ite_false B _ _ _ σ1 _ _
        (RunStep.cond_eq_false B σ1 _ _ _ _ ev1 ev2 (by omega)) hr2)).mono
        (by simp [Kev, Cond.size, Expr.size]; omega), ?_, ?_, fr1.trans fr2, by rw [o2, o1]⟩
      · rw [e2]; simp [ev, h1]
      · rw [u2, u1]
        simp only [ev, h1]
        cases (ev (oracle Dt x ds b v) φ).2 <;> cases (ev (oracle Dt x ds b v) ψ).2 <;> simp
    · have hw : σ1.vars "w_f" = 1 := by rw [e1, h1]; rfl
      refine ⟨σ1, (hr1.seq (RunStep.ite_true B _ _ _ σ1 _ _
        (RunStep.cond_eq_true B σ1 _ _ _ _ ev1 ev2 hw) (RunStep.skip B σ1))).mono
        (by simp [Kev, Cond.size, Expr.size]; omega), ?_, ?_, fr1, o1⟩
      · rw [hw]; simp [ev, h1]
      · rw [u1]; simp [ev, h1]
  | .ex _ _, _ => by
    intro σ _
    have hr := RunStep.assign B σ "w_f" (.lit 0) 0 (evalB_lit (by have := hb.hk; omega))
    refine ⟨_, hr.mono (by simp [Kev, Expr.size]), by simp [Env.setVar, ev],
      by simp [Env.setVar, ev], Frame.setVar σ (by simp [evVars]) _, rfl⟩
  | .all _ _, _ => by
    intro σ _
    have hr := RunStep.assign B σ "w_f" (.lit 0) 0 (evalB_lit (by have := hb.hk; omega))
    refine ⟨_, hr.mono (by simp [Kev, Expr.size]), by simp [Env.setVar, ev],
      by simp [Env.setVar, ev], Frame.setVar σ (by simp [evVars]) _, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval
