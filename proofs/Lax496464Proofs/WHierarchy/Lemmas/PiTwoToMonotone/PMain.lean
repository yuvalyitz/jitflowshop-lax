import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseM
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain

/-!
# The whole program

`mainCom_run`: the setup of `Lemmas/WDToWSat` (block positions, `L`, the elements, powers of `n`),
the constants, the number of clauses, the phases B, X, M and `W`; the output is `OutW.outWords`.
`prog_run`: the program computes the reduction `Out.R`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList headCom fitCom boCom LCom uCom
  powCom noCom uCom fill1 fill1Body fill2 fill2Body pushNew memScan memLoop memBody)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF DsOk Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath (Good)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgSetup (headCom_spec fitCom_spec boCom_spec LCom_spec
  powCom_spec)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill (uCom_value capW)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain (noCom_spec)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseM
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval

variable {B : ℕ} {Dt : Data} {x : List ℕ}

/-- The state before the main part. -/
structure MPre (Dt : Data) (x : List ℕ) (σ : Env) : Prop where
  a : σ.arrs "a" = x
  n : σ.vars "rt_n" = x.length
  sp : σ.vars "w_sp" = spW x
  N : σ.vars "w_N" = NW x
  k : σ.vars "w_k" = kW x
  bo : (σ.arrs "bo").length = spW x
  U : σ.arrs "U" = List.replicate (capW (wd Dt) x) 0
  od : (σ.arrs "od").length = Dt.r
  bd1 : (σ.arrs "bd1").length = Dt.D
  vd1 : (σ.arrs "vd1").length = Dt.D
  bd2 : (σ.arrs "bd2").length = Dt.D
  vd2 : (σ.arrs "vd2").length = Dt.D

/-- The scalars of the constants. -/
def constVars : List String :=
  ["g_NT", "g_M", "g_C", "g_k1", "g_W", "g_D", "g_DD", "g_C2", "g_WCQ"]

set_option maxHeartbeats 4000000 in
/-- **The constants.** -/
theorem constCom_run (hB : BB Dt x B) {σ : Env} (hPS : σ.vars "w_PS" = nU Dt x ^ Dt.s)
    (hk : σ.vars "w_k" = kW x) (hQ : σ.vars "g_Q" = (par Dt x).Q) :
    ∃ σ', Run B (constCom Dt.D) σ σ' (8 * Dt.D + 40) ∧
      σ'.vars "g_NT" = nU Dt x ^ Dt.s ∧ σ'.vars "g_M" = nU Dt x ^ Dt.s + 1 ∧
      σ'.vars "g_C" = (par Dt x).C ∧ σ'.vars "g_k1" = kW x + 1 ∧ σ'.vars "g_W" = (par Dt x).W ∧
      σ'.vars "g_D" = Dt.D ∧ σ'.vars "g_DD" = Dt.D * Dt.D ∧ σ'.vars "g_C2" = 2 * (par Dt x).C ∧
      σ'.vars "g_WCQ" = (par Dt x).W * (par Dt x).C * (par Dt x).Q ∧
      Frame constVars [] σ σ' ∧ σ'.out = σ.out := by
  have hs := hB.small
  have hcnt := hB.count_lt
  have hWCQ := hB.WCQ_lt
  -- `NT := n^s`, `M := NT + 1`
  have r1 := RunStep.assign B σ "g_NT" (V "w_PS") _ (evalB_var (B := B) (σ := σ) (x := "w_PS")
    (by rw [hPS]; omega))
  set σ1 := σ.setVar "g_NT" (σ.vars "w_PS") with hσ1
  have e1 : σ1.vars "g_NT" = nU Dt x ^ Dt.s := by simp [hσ1, Env.setVar, hPS]
  have r2 := RunStep.assign B σ1 "g_M" (.add (V "g_NT") (.lit 1)) _
    (evalB_bin (evalB_var (B := B) (σ := σ1) (x := "g_NT") (by rw [e1]; omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply_add]; rw [e1]; omega))
  set σ2 := σ1.setVar "g_M" (σ1.vars "g_NT" + 1) with hσ2
  have e2 : σ2.vars "g_M" = nU Dt x ^ Dt.s + 1 := by simp [hσ2, Env.setVar, e1]
  -- `C := M^D`
  obtain ⟨σ3, r3, e3, f3, o3⟩ := powG_spec (B := B) (dst := "g_C") (bs := "g_M") (by decide)
    (b0 := nU Dt x ^ Dt.s + 1) (by omega) Dt.D (by
      have := hs.2.2.2.2.2.2.2.2.1; rwa [show nU Dt x ^ Dt.s + 1 + 1 = nU Dt x ^ Dt.s + 2 by ring])
    σ2 e2
  -- `k1 := k + 1`
  have hk3 : σ3.vars "w_k" = kW x := by
    rw [f3.1 _ (by decide)]; simp [hσ2, hσ1, Env.setVar, hk]
  have r4 := RunStep.assign B σ3 "g_k1" (.add (V "w_k") (.lit 1)) _
    (evalB_bin (evalB_var (B := B) (σ := σ3) (x := "w_k") (by rw [hk3]; omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply_add]; rw [hk3]; omega))
  set σ4 := σ3.setVar "g_k1" (σ3.vars "w_k" + 1) with hσ4
  have e4 : σ4.vars "g_k1" = kW x + 1 := by simp [hσ4, Env.setVar, hk3]
  -- `W := k1^D`
  obtain ⟨σ5, r5, e5, f5, o5⟩ := powG_spec (B := B) (dst := "g_W") (bs := "g_k1") (by decide)
    (b0 := kW x + 1) (by omega) Dt.D (by
      have := hs.2.2.2.2.2.2.2.2.2; rwa [show kW x + 1 + 1 = kW x + 2 by ring]) σ4 e4
  -- `D`, `D·D`
  have r6 := RunStep.assign B σ5 "g_D" (.lit Dt.D) _ (evalB_lit (by omega))
  set σ6 := σ5.setVar "g_D" Dt.D with hσ6
  have r7 := RunStep.assign B σ6 "g_DD" (.lit (Dt.D * Dt.D)) _ (evalB_lit (by omega))
  set σ7 := σ6.setVar "g_DD" (Dt.D * Dt.D) with hσ7
  have hC7 : σ7.vars "g_C" = (par Dt x).C := by
    simp only [hσ7, hσ6, Env.setVar, String.reduceEq, if_false]
    rw [f5.1 _ (by decide)]; simp only [hσ4, Env.setVar, String.reduceEq, if_false, e3]; rfl
  have hW7 : σ7.vars "g_W" = (par Dt x).W := by
    simp only [hσ7, hσ6, Env.setVar, String.reduceEq, if_false, e5]; rfl
  have hQ7 : σ7.vars "g_Q" = (par Dt x).Q := by
    simp only [hσ7, hσ6, Env.setVar, String.reduceEq, if_false]
    rw [f5.1 _ (by decide)]; simp only [hσ4, Env.setVar, String.reduceEq, if_false]
    rw [f3.1 _ (by decide)]; simp only [hσ2, hσ1, Env.setVar, String.reduceEq, if_false, hQ]
  -- `C2`, `WCQ`
  have r8 := RunStep.assign B σ7 "g_C2" (.mul (.lit 2) (V "g_C")) _
    (evalB_bin (evalB_lit (by omega)) (evalB_var (B := B) (σ := σ7) (x := "g_C") (by rw [hC7]; omega))
      (by simp only [Bop.apply_mul]; rw [hC7]; omega))
  set σ8 := σ7.setVar "g_C2" (2 * σ7.vars "g_C") with hσ8
  have hW8 : σ8.vars "g_W" = (par Dt x).W := by simp [hσ8, Env.setVar, hW7]
  have hC8 : σ8.vars "g_C" = (par Dt x).C := by simp [hσ8, Env.setVar, hC7]
  have hQ8 : σ8.vars "g_Q" = (par Dt x).Q := by simp [hσ8, Env.setVar, hQ7]
  have r9 := RunStep.assign B σ8 "g_WCQ" (.mul (.mul (V "g_W") (V "g_C")) (V "g_Q")) _
    (evalB_bin (evalB_bin (evalB_var (B := B) (σ := σ8) (x := "g_W") (by rw [hW8]; omega))
      (evalB_var (B := B) (σ := σ8) (x := "g_C") (by rw [hC8]; omega))
      (by simp only [Bop.apply_mul]; rw [hW8, hC8]; omega))
      (evalB_var (B := B) (σ := σ8) (x := "g_Q") (by rw [hQ8]; have := hB.Q_lt; omega))
      (by simp only [Bop.apply_mul]; rw [hW8, hC8, hQ8]; omega))
  set σ9 := σ8.setVar "g_WCQ" (σ8.vars "g_W" * σ8.vars "g_C" * σ8.vars "g_Q") with hσ9
  refine ⟨σ9, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    Run.skip))))))))).mono (by simp [Expr.size]; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hσ9, hσ8, hσ7, hσ6, Env.setVar, String.reduceEq, if_false]
    rw [f5.1 _ (by decide)]; simp only [hσ4, Env.setVar, String.reduceEq, if_false]
    rw [f3.1 _ (by decide)]; exact e1
  · simp only [hσ9, hσ8, hσ7, hσ6, Env.setVar, String.reduceEq, if_false]
    rw [f5.1 _ (by decide)]; simp only [hσ4, Env.setVar, String.reduceEq, if_false]
    rw [f3.1 _ (by decide)]; exact e2
  · simp only [hσ9, Env.setVar, String.reduceEq, if_false]; exact hC8
  · simp only [hσ9, hσ8, hσ7, hσ6, Env.setVar, String.reduceEq, if_false]
    rw [f5.1 _ (by decide)]; exact e4
  · simp only [hσ9, Env.setVar, String.reduceEq, if_false]; exact hW8
  · simp [hσ9, hσ8, hσ7, hσ6, Env.setVar]
  · simp [hσ9, hσ8, hσ7, Env.setVar]
  · simp [hσ9, hσ8, Env.setVar, hC7]
  · simp only [hσ9, Env.setVar, if_true]; rw [hW8, hC8, hQ8]
  · refine ⟨fun y hy => ?_, fun _ _ => ?_, ?_⟩
    · simp only [constVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [hσ9, hσ8, hσ7, hσ6, Env.setVar, if_neg hy.2.2.2.2.2.2.2.2,
        if_neg hy.2.2.2.2.2.2.2.1, if_neg hy.2.2.2.2.2.2.1, if_neg hy.2.2.2.2.2.1]
      rw [f5.1 _ (by simpa using hy.2.2.2.2.1)]
      simp only [hσ4, Env.setVar, if_neg hy.2.2.2.1]
      rw [f3.1 _ (by simpa using hy.2.2.1)]
      simp only [hσ2, hσ1, Env.setVar, if_neg hy.2.1, if_neg hy.1]
    · exact (f5.2.1 _ (by simp)).trans (f3.2.1 _ (by simp))
    · exact f5.2.2.trans f3.2.2
  · simp only [hσ9, hσ8, hσ7, hσ6]
    show σ5.out = σ.out
    rw [o5]; show σ3.out = σ.out; rw [o3]; rfl

/-- The cost of the main part. -/
def Kmain (Dt : Data) (x : List ℕ) : ℕ :=
  (34 * spW x + 12) + (20 + (((10 + 4) * LW Dt.s Dt.r x + 6 + 3 +
    ((16 * capW (wd Dt) x + 70 + 4) * x.length + 6)) + ((6 * Dt.s + 3) + ((6 * Dt.p + 3) +
    ((6 * Dt.q + 3) + ((8 * Dt.D + 40) + (30 + (((((10 + 8) * (par Dt x).C + 6 + 2 + 8) + 8) *
      (par Dt x).W + 6) + (KX Dt x + (KM Dt x + (2 + 1)))))))))))

set_option maxHeartbeats 8000000 in
/-- **The main part** writes the formula and `W`. -/
theorem mainCom_run (hB : BB Dt x B) (hg : Good x) (hA : AtomsOk Dt x Dt.ψ) {σ : Env}
    (hσ : MPre Dt x σ) :
    ∃ σ', Run B (mainCom Dt) σ σ' (Kmain Dt x) ∧ σ'.out = σ.out ++ outWords Dt x := by
  have hbf := hB.bf
  have hs := hB.small
  have hcnt := hB.count_lt
  have hkB : kW x < B := by omega
  have hrs : Dt.s ≤ (wd Dt).r + (wd Dt).s := by simp [wd]
  have hps : Dt.p ≤ (wd Dt).r + (wd Dt).s := by simp [wd, Data.r]; omega
  have hqs : Dt.q ≤ (wd Dt).r + (wd Dt).s := by simp [wd, Data.r]; omega
  -- block positions, `L`, the elements
  obtain ⟨σ1, hr1, bo1, f1, o1⟩ := boCom_spec hbf hg σ ⟨hσ.a, hσ.sp, hσ.bo⟩
  obtain ⟨σ2, hr2, L2, f2, o2⟩ := LCom_spec hbf (D := wd Dt) σ1
    ⟨by rw [f1.1 _ (by simp)]; exact hσ.n, by rw [f1.1 _ (by simp)]; exact hσ.k,
      by rw [f1.1 _ (by simp)]; exact hσ.N⟩
  have hu := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx.Spec.framedOut (uCom_value hbf (D := wd Dt))
    ["w_e", "w_n", "w_p", "w_f", "w_q"] ["U"]
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.wvars])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.warrs])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.reads])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.NoWrite])
  have f12 : Frame ["w_p", "w_i", "w_t", "w_L"] ["bo"] σ σ2 :=
    (f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))
  obtain ⟨σ3, hr3, ⟨U3, Ul3, n3⟩, f3, o3⟩ := hu σ2
    ⟨by rw [f12.2.1 _ (by simp)]; exact hσ.a, by rw [f12.1 _ (by simp)]; exact hσ.n, L2,
      by rw [f12.1 _ (by simp)]; exact hσ.N, by rw [f12.2.1 _ (by simp)]; exact hσ.U⟩
  -- powers of `n`
  obtain ⟨σ4, hr4, P4, f4, o4⟩ := powCom_spec hbf "w_PS" (by decide) hrs σ3 n3
  obtain ⟨σ5, hr5, P5, f5, o5⟩ := powCom_spec hbf "g_P" (by decide) hps σ4
    (by show σ4.vars "w_n" = _; rw [f4.1 _ (by simp)]; exact n3)
  obtain ⟨σ6, hr6, P6, f6, o6⟩ := powCom_spec hbf "g_Q" (by decide) hqs σ5
    (by show σ5.vars "w_n" = _; rw [f5.1 _ (by simp), f4.1 _ (by simp)]; exact n3)
  have f36 : Frame ["w_PS", "g_P", "g_Q"] [] σ3 σ6 :=
    ((f4.mono (by simp) (by simp)).trans (f5.mono (by simp) (by simp))).trans
      (f6.mono (by simp) (by simp))
  have f06 : Frame ["w_p", "w_i", "w_t", "w_L", "w_e", "w_n", "w_f", "w_q", "w_PS", "g_P", "g_Q"]
      ["bo", "U"] σ σ6 :=
    ((f12.mono (by simp) (by simp)).trans (f3.mono (by simp) (by simp))).trans
      (f36.mono (by simp) (by simp))
  -- the constants
  obtain ⟨σ7, hr7, c1, c2, c3, c4, c5, c6, c7, c8, c9, f7, o7⟩ := constCom_run hB (σ := σ6)
    (by rw [f6.1 _ (by simp), f5.1 _ (by simp)]; exact P4)
    (by rw [f06.1 _ (by simp)]; exact hσ.k) P6
  -- the number of clauses
  have hW7 : σ7.vars "g_W" = (par Dt x).W := c5
  have hC7 : σ7.vars "g_C" = (par Dt x).C := c3
  have hP7 : σ7.vars "g_P" = (par Dt x).P := by
    rw [f7.1 _ (by simp [constVars]), f6.1 _ (by simp)]; exact P5
  have hQ7 : σ7.vars "g_Q" = (par Dt x).Q := by rw [f7.1 _ (by simp [constVars])]; exact P6
  have evc : countCom = .write (.add (.add (V "g_W") (.mul (.mul (.mul (V "g_W") (V "g_C"))
      (V "g_W")) (V "g_C"))) (V "g_P")) := rfl
  have ecount : (Expr.add (.add (V "g_W") (.mul (.mul (.mul (V "g_W") (V "g_C")) (V "g_W"))
      (V "g_C"))) (V "g_P")).evalB B σ7 = some ((par Dt x).W + (par Dt x).W * (par Dt x).C *
        (par Dt x).W * (par Dt x).C + (par Dt x).P) := by
    have eW : (V "g_W").evalB B σ7 = some (par Dt x).W := by
      rw [← hW7]; exact evalB_var (by rw [hW7]; omega)
    have eC : (V "g_C").evalB B σ7 = some (par Dt x).C := by
      rw [← hC7]; exact evalB_var (by rw [hC7]; omega)
    have eP : (V "g_P").evalB B σ7 = some (par Dt x).P := by
      rw [← hP7]; exact evalB_var (by rw [hP7]; omega)
    exact evalB_bin (evalB_bin eW (evalB_bin (evalB_bin (evalB_bin eW eC (by simp; omega)) eW
      (by simp; omega)) eC (by simp; omega)) (by simp; omega)) eP (by simp; omega)
  have hr8 := RunStep.write B σ7 _ _ ecount
  set σ8 := { σ7 with out := σ7.out ++ [(par Dt x).W + (par Dt x).W * (par Dt x).C *
    (par Dt x).W * (par Dt x).C + (par Dt x).P] } with hσ8
  -- the context of the phases
  have f07 : Frame (["w_p", "w_i", "w_t", "w_L", "w_e", "w_n", "w_f", "w_q", "w_PS", "g_P", "g_Q"] ++
      constVars) ["bo", "U"] σ σ7 :=
    (f06.mono (by simp) (by simp)).trans (f7.mono (by simp [constVars]) (by simp))
  have hGC : GC Dt x σ8 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, c1, c2, c3, c4, c5, c6, c7, c8, c9, hP7, hQ7, ?_, ?_, ?_, ?_⟩
    · show σ7.arrs "a" = x; rw [f07.2.1 _ (by simp)]; exact hσ.a
    · show σ7.arrs "bo" = _
      rw [f7.2.1 _ (by simp), f36.2.1 _ (by simp), f3.2.1 _ (by simp), f2.2.1 _ (by simp)]
      exact bo1
    · intro q hq
      show (σ7.arrs "U").getD q 0 = _
      rw [f7.2.1 _ (by simp), f36.2.1 _ (by simp)]; exact U3 q hq
    · show _ ≤ (σ7.arrs "U").length
      rw [f7.2.1 _ (by simp), f36.2.1 _ (by simp)]; exact Ul3
    · show (σ7.arrs "od").length = _; rw [f07.2.1 _ (by simp)]; exact hσ.od
    · show σ7.vars "w_n" = _
      rw [f7.1 _ (by simp [constVars]), f36.1 _ (by simp)]; exact n3
    · show σ7.vars "w_k" = _; rw [f07.1 _ (by simp [constVars])]; exact hσ.k
    · show (σ7.arrs "bd1").length = _; rw [f07.2.1 _ (by simp)]; exact hσ.bd1
    · show (σ7.arrs "vd1").length = _; rw [f07.2.1 _ (by simp)]; exact hσ.vd1
    · show (σ7.arrs "bd2").length = _; rw [f07.2.1 _ (by simp)]; exact hσ.bd2
    · show (σ7.arrs "vd2").length = _; rw [f07.2.1 _ (by simp)]; exact hσ.vd2
  -- the phases
  obtain ⟨σ9, hr9, hg9, o9⟩ := phaseB_spec hB σ8 hGC
  obtain ⟨σ10, hr10, hg10, o10⟩ := phaseX_spec hB σ9 hg9
  obtain ⟨σ11, hr11, hg11, o11⟩ := phaseM_spec hB hg hA σ10 hg10
  -- `W`
  have hr12 := RunStep.write B σ11 (V "g_W") _ (evalB_var (by rw [hg11.W]; omega))
  refine ⟨_, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq (hr9.seq
    (hr10.seq (hr11.seq (hr12.seq Run.skip)))))))))))).mono
    (by simp only [Kmain, Expr.size]
        rw [show LW (wd Dt).s (wd Dt).r x = LW Dt.s Dt.r x from rfl]; ring_nf; omega), ?_⟩
  show σ11.out ++ [σ11.vars "g_W"] = _
  rw [hg11.W, o11, o10, o9, hσ8]
  show σ7.out ++ _ ++ _ ++ _ ++ _ ++ _ = _
  rw [o7, o6, o5, o4, o3, o2, o1]
  simp [outWords]

/-! ### The whole program -/

/-- The array lengths of the initial environment. -/
def extP (Dt : Data) (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length else if a = "bo" then spW x else if a = "U" then capW (wd Dt) x
  else if a = "od" then Dt.r
  else if a = "bd1" ∨ a = "vd1" ∨ a = "bd2" ∨ a = "vd2" then Dt.D else 0

/-- The cost of the program. -/
def Kprog (Dt : Data) (x : List ℕ) : ℕ :=
  16 * x.length + 7 + (20 + ((12 * (wd Dt).rels.length + 4) + (1 + 3 + (Kmain Dt x + 10))))

set_option maxHeartbeats 4000000 in
/-- **The program computes the reduction.** -/
theorem prog_run (hB : BB Dt x B) (hg : Good x) (hA : fitW Dt x → AtomsOk Dt x Dt.ψ) :
    ∃ σ', Run B (prog Dt) (initEnv (extP Dt x) (x.length :: x)) σ' (Kprog Dt x) ∧
      σ'.out = R Dt x := by
  have hbf := hB.bf
  have hlen := hbf.len
  have hkB : kW x < B := hbf.getD_lt _
  set σ0 := initEnv (extP Dt x) (x.length :: x) with hσ0
  obtain ⟨σ1, hr1, a1, n1, -, out1, v1, arr1⟩ :=
    Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape_spec x σ0 hbf.entries (by omega) rfl
      (by simp [σ0, initEnv, extP]) σ0 rfl
  obtain ⟨σ2, hr2, sp2, N2, k2, f2, o2⟩ := headCom_spec hbf hg σ1 ⟨a1, n1⟩
  obtain ⟨σ3, hr3, ft3, f3, o3⟩ := fitCom_spec hbf hg (D := wd Dt) σ2
    ⟨by rw [f2.2.1 _ (by simp)]; exact a1, sp2⟩
  have ev_ft : (Expr.var "w_ft").evalB B σ3 = some (σ3.vars "w_ft") :=
    evalB_var (by rw [ft3]; split_ifs <;> omega)
  have ev_1 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit (by omega)
  have hk3 : σ3.vars "w_k" = kW x := by rw [f3.1 _ (by simp)]; exact k2
  have hout3 : σ3.out = [] := by rw [o3, o2, out1]; simp [σ0, initEnv]
  have harr : ∀ b, b ≠ "a" → σ3.arrs b = List.replicate (extP Dt x b) 0 := by
    intro b hb
    rw [f3.2.1 _ (by simp), f2.2.1 _ (by simp), arr1 _ hb]; simp [σ0, initEnv]
  by_cases hfit : fitW Dt x
  · have hft : σ3.vars "w_ft" = 1 := by
      rw [ft3, if_pos (show Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output.fitW (wd Dt) x from hfit)]
    have f23 : Frame ["w_sp", "w_N", "w_k", "w_ft"] [] σ1 σ3 :=
      (f2.mono (by simp) (by simp)).trans (f3.mono (by simp) (by simp))
    have hpre : MPre Dt x σ3 := by
      refine ⟨by rw [f23.2.1 _ (by simp)]; exact a1, by rw [f23.1 _ (by simp)]; exact n1,
        by rw [f3.1 _ (by simp)]; exact sp2, by rw [f3.1 _ (by simp)]; exact N2, hk3, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      all_goals (rw [harr _ (by decide)]; simp [extP])
    obtain ⟨σ4, hr4, o4⟩ := mainCom_run hB hg (hA hfit) hpre
    refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq (RunStep.ite_true B _ _ _ σ3 σ4 _
      (RunStep.cond_eq_true B σ3 _ _ _ _ ev_ft ev_1 hft) hr4)))).mono
      (by simp only [Kprog, Cond.size, Expr.size]; omega), ?_⟩
    rw [o4, hout3, R_eq Dt x hfit]; rfl
  · have hft : σ3.vars "w_ft" = 0 := by
      rw [ft3, if_neg (show ¬ Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output.fitW (wd Dt) x from hfit)]
    obtain ⟨σ4, hr4, o4⟩ := noCom_spec (x := x) hkB (by omega) σ3 hk3
    refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq (RunStep.ite_false B _ _ _ σ3 σ4 _
      (RunStep.cond_eq_false B σ3 _ _ _ _ ev_ft ev_1 (by omega)) hr4)))).mono
      (by simp only [Kprog, Cond.size, Expr.size]; omega), ?_⟩
    rw [o4, hout3]; unfold R; rw [if_neg hfit]; rfl

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PMain
