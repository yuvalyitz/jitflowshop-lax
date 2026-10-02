import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow

/-!
# The Passes of `body`

The four passes of `body`, writing the number of edges, the offsets, the targets and the colours,
with their loop invariants and costs.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyPass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow

theorem psum_mono (x : List ℕ) {s t : ℕ} (h : s ≤ t) : psum x s ≤ psum x t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [psum_succ]; omega

theorem degW_le_psum (x : List ℕ) {s : ℕ} (h : s < nOf x) : psum x s + degW x s ≤ psum x (nOf x) := by
  rw [← psum_succ]; exact psum_mono x h

/-- The bound `B` must exceed: length, number of vertices, number of edge slots. -/
def BOK (x : List ℕ) (B : ℕ) : Prop := x.length + nOf x + psum x (nOf x) + 2 < B

theorem BOK.row {x : List ℕ} {B : ℕ} (h : BOK x B) : x.length + nOf x + 2 < B := by
  unfold BOK at h; omega

/-- Invariant of the degree-sum loop. -/
def P1I (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ nOf x ∧ σ.vars "b_M" = psum x (σ.vars "b_s")

set_option maxHeartbeats 1000000 in
theorem pass1_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => P1I x σ ∧ σ.vars "b_s" < nOf x)
      (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))
      (fun σ σ' => P1I x σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow (nOf x) + 20) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  refine Spec.pre (P := fun σ => P1I x σ ∧ σ.vars "b_s" < nOf x ∧
    psum x (σ.vars "b_s") + degW x (σ.vars "b_s") ≤ psum x (nOf x) ∧ 2 < B) ?_ ?_
  · run_vcg [rowCount_spec' hx hB.row]
    all_goals (simp only [P1I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, psum_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, degW_le_psum x h2, by omega⟩

/-- The cost of `pass1`. -/
def K1 (N : ℕ) : ℕ := (Krow N + 20 + 4) * N + 8

/-- The scalars `pass1` may assign. -/
def pass1Vars : List String := rowVars ++ ["b_M", "b_s"]

theorem pass1_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass1
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_M" = psum x (nOf x) ∧ Keep pass1Vars σ σ' ∧
        σ'.out = σ.out) (K1 (nOf x)) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  unfold pass1
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))
    "b_s" "b_N" (P1I x) (nOf x) (Krow (nOf x) + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass1_body hx hB)
  have h0 : Spec B (fun σ => Ctx x σ) (.assign "b_M" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "b_M" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  have hfull : Spec B (fun σ => Ctx x σ)
      (.seq (.assign "b_M" (.lit 0)) (.seq (.assign "b_s" (.lit 0)) (.while (.lt (V "b_s") (V "b_N"))
        (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s"))))))
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_M" = psum x (nOf x)) (K1 (nOf x)) := by
    refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
    · rintro σ σ1 ⟨ha, hn, hbase, hN⟩ rfl
      simp only [P1I, Ctx, Env.setVar]
      simp [psum, ha, hn, hbase, hN]
    · rintro σ σ1 σ2 - - ⟨⟨hc, -, hM⟩, hs⟩
      rw [hs] at hM
      exact ⟨hc, hM⟩
  refine Spec.post (Spec.keep hfull pass1Vars ?_ ?_ ?_).frame ?_
  · intro y hy
    simp only [rowCount, adjCom, adjPrep, adjTest, bump, Com.wvars, pass1Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.warrs]
  · simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq.1, hq.2, hk, ho (by simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.NoWrite])⟩

/-- Invariant of the offset loop. -/
def P2I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ nOf x ∧ σ.vars "b_off" = psum x (σ.vars "b_s") ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).map (fun r => psum x (r + 1))

set_option maxHeartbeats 1000000 in
theorem pass2_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P2I x out0 σ ∧ σ.vars "b_s" < nOf x)
      (.seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
        (.seq (.write (V "b_off")) (bump "b_s"))))
      (fun σ σ' => P2I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow (nOf x) + 20) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  refine Spec.pre (P := fun σ => P2I x out0 σ ∧ σ.vars "b_s" < nOf x ∧
    psum x (σ.vars "b_s") + degW x (σ.vars "b_s") ≤ psum x (nOf x) ∧ 2 < B) ?_ ?_
  · run_vcg [rowCount_spec' hx hB.row]
    all_goals (simp only [P2I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, psum_succ, List.range_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, degW_le_psum x h2, by omega⟩

/-- The scalars `pass2` may assign. -/
def pass2Vars : List String := rowVars ++ ["b_off", "b_s"]

theorem pass2_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass2
      (fun _ σ' => Ctx x σ' ∧
        σ'.out = out0 ++ (List.range (nOf x)).map (fun r => psum x (r + 1))) (K1 (nOf x)) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  unfold pass2
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
        (.seq (.write (V "b_off")) (bump "b_s"))))
    "b_s" "b_N" (P2I x out0) (nOf x) (Krow (nOf x) + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass2_body hx hB out0)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.out = out0) (.assign "b_off" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "b_off" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
  · rintro σ σ1 ⟨⟨ha, hn, hbase, hN⟩, ho⟩ rfl
    simp only [P2I, Ctx, Env.setVar]
    simp [psum, ha, hn, hbase, hN, ho]
  · rintro σ σ1 σ2 - - ⟨⟨hc, -, -, ho⟩, hs⟩
    rw [hs] at ho
    exact ⟨hc, ho⟩

theorem pass2_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass2
      (fun σ σ' => Ctx x σ' ∧
        σ'.out = σ.out ++ (List.range (nOf x)).map (fun r => psum x (r + 1)) ∧
        Keep pass2Vars σ σ') (K1 (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (pass2_value hx hB σ.out) pass2Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass2, rowCount, adjCom, adjPrep, adjTest, bump, Com.wvars, pass2Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass2, rowCount, adjCom, adjPrep, adjTest, bump, Com.warrs]
  · simp [pass2, rowCount, adjCom, adjPrep, adjTest, bump, Com.reads]

/-- Invariant of the target-writing loop. -/
def P3I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ nOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).flatMap (nbW x)

set_option maxHeartbeats 1000000 in
theorem pass3_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P3I x out0 σ ∧ σ.vars "b_s" < nOf x)
      (.seq rowEmit (bump "b_s"))
      (fun σ σ' => P3I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) (Krow (nOf x) + 10) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  refine Spec.pre (P := fun σ => P3I x out0 σ ∧ σ.vars "b_s" < nOf x) ?_ (fun σ h => h)
  run_vcg [rowEmit_spec' hx hB.row]
  all_goals (simp only [P3I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, List.range_succ, List.flatMap_append]; try omega)

/-- The scalars `pass3` may assign. -/
def pass3Vars : List String := rowVars ++ ["b_s"]

/-- The cost of `pass3`. -/
def K3 (N : ℕ) : ℕ := (Krow N + 10 + 4) * N + 6

theorem pass3_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass3
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (nOf x)).flatMap (nbW x)) (K3 (nOf x)) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  unfold pass3
  have hloop := Spec.forRangeZero (B := B) (c := .seq rowEmit (bump "b_s"))
    "b_s" "b_N" (P3I x out0) (nOf x) (Krow (nOf x) + 10) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass3_body hx hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K3])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨⟨ha, hn, hbase, hN⟩, ho⟩
    simp only [P3I, Ctx, Env.setVar]
    simp [ho, ha, hn, hbase, hN]

theorem pass3_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass3
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (nOf x)).flatMap (nbW x) ∧
        Keep pass3Vars σ σ') (K3 (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (pass3_value hx hB σ.out) pass3Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass3, rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.wvars, pass3Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass3, rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.warrs]
  · simp [pass3, rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.reads]

/-- Invariant of the colour-writing loop. -/
def P4I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" ≤ nOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "b_s")).map (fun r => r / order x)

set_option maxHeartbeats 1000000 in
theorem pass4_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P4I x out0 σ ∧ σ.vars "b_s" < nOf x)
      (.seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s"))
      (fun σ σ' => P4I x out0 σ' ∧ σ'.vars "b_s" = σ.vars "b_s" + 1) 12 := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  have hol := order_le_length hx
  refine Spec.pre (P := fun σ => P4I x out0 σ ∧ σ.vars "b_s" < nOf x ∧
    σ.vars "b_s" / σ.vars "b_n" ≤ σ.vars "b_s") ?_ (fun σ h => ⟨h.1, h.2, Nat.div_le_self _ _⟩)
  run_vcg
  all_goals (simp only [P4I, Ctx] at *; simp_all [Env.setVar, List.range_succ]; try omega)

/-- The scalars `pass4` may assign. -/
def pass4Vars : List String := ["b_s"]

/-- The cost of `pass4`. -/
def K4 (N : ℕ) : ℕ := (12 + 4) * N + 6

theorem pass4_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass4
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (nOf x)).map (fun r => r / order x))
      (K4 (nOf x)) := by
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hB
  unfold pass4
  have hloop := Spec.forRangeZero (B := B) (c := .seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s"))
    "b_s" "b_N" (P4I x out0) (nOf x) 12 (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2.2) (pass4_body hx hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K4])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨⟨ha, hn, hbase, hN⟩, ho⟩
    simp only [P4I, Ctx, Env.setVar]
    simp [ho, ha, hn, hbase, hN]

theorem pass4_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass4
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (nOf x)).map (fun r => r / order x) ∧
        Keep pass4Vars σ σ') (K4 (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (pass4_value hx hB σ.out) pass4Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass4, bump, Com.wvars, pass4Vars] at hy ⊢
    simpa using hy
  · simp [pass4, bump, Com.warrs]
  · simp [pass4, bump, Com.reads]

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyPass
