import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdRow

/-! # p-Clique to Multicoloured Clique: the four passes over the copies

`pass1_spec`: the sum of the degrees, into `b_M`; `pass2_spec`: the running offsets; `pass3_spec`:
the targets, each copy's neighbours in increasing order; `pass4_spec`: the colours. Together they
write the compressed sparse row word of the multicoloured graph and its colouring. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdRow

theorem ps_succ (x : List ℕ) (s : ℕ) : ps x (s + 1) = ps x s + dg x s :=
  CsrWord.psum_succ _ _ _

theorem ps_mono (x : List ℕ) {s t : ℕ} (h : s ≤ t) : ps x s ≤ ps x t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [ps_succ]; omega

theorem dg_le_ps (x : List ℕ) {s : ℕ} (h : s < NOf x) : ps x s + dg x s ≤ ps x (NOf x) := by
  rw [← ps_succ]; exact ps_mono x h

/-- The bound `B` must exceed: length, number of vertices, number of edge slots. -/
def BOK (x : List ℕ) (B : ℕ) : Prop := RB x B ∧ x.length + NOf x + ps x (NOf x) + 2 < B

theorem BOK.row {x : List ℕ} {B : ℕ} (h : BOK x B) : RB x B := h.1

/-- Invariant of the degree-sum loop. -/
def P1I (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ NOf x ∧ σ.vars "b_M" = ps x (σ.vars "b_s")

set_option maxHeartbeats 1000000 in
theorem pass1_body {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => P1I x σ ∧ σ.vars "b_s" < NOf x)
      (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))
      (fun σ σ' => P1I x σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow x + 20) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  refine Spec.pre (P := fun σ => P1I x σ ∧ σ.vars "b_s" < NOf x ∧
    ps x (σ.vars "b_s") + dg x (σ.vars "b_s") ≤ ps x (NOf x) ∧ 2 < B) ?_ ?_
  · run_vcg [rowCount_spec' hB.row]
    all_goals (simp only [P1I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, ps_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, dg_le_ps x h2, by omega⟩

/-- The cost of `pass1`. -/
def K1 (x : List ℕ) : ℕ := (Krow x + 20 + 4) * NOf x + 8

/-- The scalars `pass1` may assign. -/
def pass1Vars : List String := rowVars ++ ["b_M", "b_s"]

theorem pass1_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass1
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_M" = ps x (NOf x) ∧ Keep pass1Vars σ σ' ∧
        σ'.out = σ.out) (K1 x) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  unfold pass1
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))
    "b_s" "b_N" (P1I x) (NOf x) (Krow x + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass1_body hB)
  have h0 : Spec B (fun σ => Ctx x σ) (.assign "b_M" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "b_M" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  have hfull : Spec B (fun σ => Ctx x σ)
      (.seq (.assign "b_M" (.lit 0)) (.seq (.assign "b_s" (.lit 0)) (.while (.lt (V "b_s") (V "b_N"))
        (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s"))))))
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_M" = ps x (NOf x)) (K1 x) := by
    refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
    · rintro σ σ1 ⟨ha, hn, hbase, hN⟩ rfl
      simp only [P1I, Ctx, Env.setVar]
      simp [ps, CsrWord.psum, ha, hn, hbase, hN]
    · rintro σ σ1 σ2 - - ⟨⟨hc, -, hM⟩, hs⟩
      rw [hs] at hM
      exact ⟨hc, hM⟩
  refine Spec.post (Spec.keep hfull pass1Vars ?_ ?_ ?_).frame ?_
  · intro y hy
    simp only [rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.wvars, pass1Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.warrs]
  · simp [rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq.1, hq.2, hk, ho (by simp [rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.NoWrite])⟩

/-- Invariant of the offset loop. -/
def P2I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ NOf x ∧ σ.vars "b_off" = ps x (σ.vars "b_s") ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).map (fun r => ps x (r + 1))

set_option maxHeartbeats 1000000 in
theorem pass2_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P2I x out0 σ ∧ σ.vars "b_s" < NOf x)
      (.seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
        (.seq (.write (V "b_off")) (bump "b_s"))))
      (fun σ σ' => P2I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow x + 20) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  refine Spec.pre (P := fun σ => P2I x out0 σ ∧ σ.vars "b_s" < NOf x ∧
    ps x (σ.vars "b_s") + dg x (σ.vars "b_s") ≤ ps x (NOf x) ∧ 2 < B) ?_ ?_
  · run_vcg [rowCount_spec' hB.row]
    all_goals (simp only [P2I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, ps_succ, List.range_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, dg_le_ps x h2, by omega⟩

/-- The scalars `pass2` may assign. -/
def pass2Vars : List String := rowVars ++ ["b_off", "b_s"]

theorem pass2_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass2
      (fun _ σ' => Ctx x σ' ∧
        σ'.out = out0 ++ (List.range (NOf x)).map (fun r => ps x (r + 1))) (K1 x) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  unfold pass2
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
        (.seq (.write (V "b_off")) (bump "b_s"))))
    "b_s" "b_N" (P2I x out0) (NOf x) (Krow x + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass2_body hB out0)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.out = out0) (.assign "b_off" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "b_off" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
  · rintro σ σ1 ⟨⟨ha, hn, hbase, hN⟩, ho⟩ rfl
    simp only [P2I, Ctx, Env.setVar]
    simp [ps, CsrWord.psum, ha, hn, hbase, hN, ho]
  · rintro σ σ1 σ2 - - ⟨⟨hc, -, -, ho⟩, hs⟩
    rw [hs] at ho
    exact ⟨hc, ho⟩

theorem pass2_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass2
      (fun σ σ' => Ctx x σ' ∧
        σ'.out = σ.out ++ (List.range (NOf x)).map (fun r => ps x (r + 1)) ∧
        Keep pass2Vars σ σ') (K1 x) := by
  intro σ hσ
  have h := Spec.keep (pass2_value hB σ.out) pass2Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass2, rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.wvars, pass2Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass2, rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.warrs]
  · simp [pass2, rowCount, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.reads]

/-- Invariant of the target-writing loop. -/
def P3I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ NOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).flatMap (nb x)

set_option maxHeartbeats 1000000 in
theorem pass3_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P3I x out0 σ ∧ σ.vars "b_s" < NOf x)
      (.seq rowEmit (bump "b_s"))
      (fun σ σ' => P3I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow x + 10) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  refine Spec.pre (P := fun σ => P3I x out0 σ ∧ σ.vars "b_s" < NOf x) ?_ (fun σ h => h)
  run_vcg [rowEmit_spec' hB.row]
  all_goals (simp only [P3I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, List.range_succ, List.flatMap_append]; try omega)

/-- The scalars `pass3` may assign. -/
def pass3Vars : List String := rowVars ++ ["b_s"]

/-- The cost of `pass3`. -/
def K3 (x : List ℕ) : ℕ := (Krow x + 10 + 4) * NOf x + 6

theorem pass3_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass3
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (NOf x)).flatMap (nb x)) (K3 x) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  unfold pass3
  have hloop := Spec.forRangeZero (B := B) (c := .seq rowEmit (bump "b_s"))
    "b_s" "b_N" (P3I x out0) (NOf x) (Krow x + 10) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass3_body hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K3])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨⟨ha, hn, hbase, hN⟩, ho⟩
    simp only [P3I, Ctx, Env.setVar]
    simp [ho, ha, hn, hbase, hN]

theorem pass3_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass3
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (NOf x)).flatMap (nb x) ∧
        Keep pass3Vars σ σ') (K3 x) := by
  intro σ hσ
  have h := Spec.keep (pass3_value hB σ.out) pass3Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass3, rowEmit, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, emitIf, bump, Com.wvars, pass3Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass3, rowEmit, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, emitIf, bump, Com.warrs]
  · simp [pass3, rowEmit, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, emitIf, bump, Com.reads]

/-- Invariant of the colour-writing loop. -/
def P4I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ NOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).map (fun r => r / nV x)

set_option maxHeartbeats 1000000 in
theorem pass4_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P4I x out0 σ ∧ σ.vars "b_s" < NOf x)
      (.seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s"))
      (fun σ σ' => P4I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) 12 := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  have hn3 : nV x + 3 < x.length := hB.1.1.1
  refine Spec.pre (P := fun σ => P4I x out0 σ ∧ σ.vars "b_s" < NOf x ∧
    σ.vars "b_s" / σ.vars "b_n" ≤ σ.vars "b_s") ?_ (fun σ h => ⟨h.1, h.2, Nat.div_le_self _ _⟩)
  run_vcg
  all_goals (simp only [P4I, Ctx] at *; simp_all [Env.setVar, List.range_succ]; try omega)

/-- The scalars `pass4` may assign. -/
def pass4Vars : List String := ["b_s"]

/-- The cost of `pass4`. -/
def K4 (x : List ℕ) : ℕ := (12 + 4) * NOf x + 6

theorem pass4_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass4
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (NOf x)).map (fun r => r / nV x))
      (K4 x) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  unfold pass4
  have hloop := Spec.forRangeZero (B := B) (c := .seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s"))
    "b_s" "b_N" (P4I x out0) (NOf x) 12 (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass4_body hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K4])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨⟨ha, hn, hbase, hN⟩, ho⟩
    simp only [P4I, Ctx, Env.setVar]
    simp [ho, ha, hn, hbase, hN]

theorem pass4_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass4
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (NOf x)).map (fun r => r / nV x) ∧
        Keep pass4Vars σ σ') (K4 x) := by
  intro σ hσ
  have h := Spec.keep (pass4_value hB σ.out) pass4Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass4, bump, Com.wvars, pass4Vars] at hy ⊢
    simpa using hy
  · simp [pass4, bump, Com.warrs]
  · simp [pass4, bump, Com.reads]

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass
