import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows

/-! # The three passes over the vertices: degree sum, offsets, targets

`pass1_spec`: the degree sum of the complement; `pass2_spec`: its offsets; `pass3_spec`: its
targets, each vertex's neighbours in increasing order. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Passes

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows

theorem degW_le (x : List ℕ) (s : ℕ) : degW x s ≤ nOf x := by
  unfold degW nbW
  exact (List.length_filter_le _ _).trans (by simp)

theorem psum_le (x : List ℕ) (s : ℕ) : psum x s ≤ s * nOf x := by
  induction s with
  | zero => simp [psum_zero]
  | succ s ih => rw [psum_succ, Nat.succ_mul]; have := degW_le x s; omega

theorem psum_le_sq {x : List ℕ} {s : ℕ} (hs : s ≤ nOf x) : psum x s ≤ nOf x * nOf x :=
  (psum_le x s).trans (Nat.mul_le_mul_right _ hs)

theorem degW_le_psum (x : List ℕ) {s : ℕ} (h : s < nOf x) :
    psum x s + degW x s ≤ nOf x * nOf x := by
  rw [← psum_succ]; exact psum_le_sq (by omega)

/-- Invariant of the degree-sum loop. -/
def P1I (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "ci_s" ≤ nOf x ∧ σ.vars "ci_M" = psum x (σ.vars "ci_s")

set_option maxHeartbeats 1000000 in
theorem pass1_body {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => P1I x σ ∧ σ.vars "ci_s" < nOf x)
      (.seq rowCount (.seq (.assign "ci_M" (.add (V "ci_M") (V "ci_d"))) (bump "ci_s")))
      (fun σ σ' => P1I x σ' ∧ σ'.vars "ci_s" = σ.vars "ci_s" + 1) (Krow (nOf x) + 20) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hn := hB.n_lt
  refine Spec.pre (P := fun σ => P1I x σ ∧ σ.vars "ci_s" < nOf x ∧
    psum x (σ.vars "ci_s") + degW x (σ.vars "ci_s") ≤ nOf x * nOf x) ?_ ?_
  · run_vcg [rowCount_spec' hB]
    all_goals (simp only [P1I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, psum_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, degW_le_psum x h2⟩

/-- The cost of `pass1` and `pass2`. -/
def K1 (N : ℕ) : ℕ := (Krow N + 20 + 4) * N + 8

/-- The scalars `pass1` may assign. -/
def pass1Vars : List String := rowVars ++ ["ci_M", "ci_s"]

theorem pass1_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass1
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "ci_M" = psum x (nOf x) ∧ Keep pass1Vars σ σ' ∧
        σ'.out = σ.out) (K1 (nOf x)) := by
  have hn := hB.n_lt
  unfold pass1
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "ci_M" (.add (V "ci_M") (V "ci_d"))) (bump "ci_s")))
    "ci_s" "ci_n" (P1I x) (nOf x) (Krow (nOf x) + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2) (pass1_body hB)
  have h0 : Spec B (fun σ => Ctx x σ) (.assign "ci_M" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "ci_M" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  have hfull : Spec B (fun σ => Ctx x σ)
      (.seq (.assign "ci_M" (.lit 0)) (.seq (.assign "ci_s" (.lit 0))
        (.while (.lt (V "ci_s") (V "ci_n"))
        (.seq rowCount (.seq (.assign "ci_M" (.add (V "ci_M") (V "ci_d"))) (bump "ci_s"))))))
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "ci_M" = psum x (nOf x)) (K1 (nOf x)) := by
    refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
    · rintro σ σ1 ⟨ha, hm, hn⟩ rfl
      simp only [P1I, Ctx, Env.setVar]
      simp [psum, ha, hm, hn]
    · rintro σ σ1 σ2 - - ⟨⟨hc, -, hM⟩, hs⟩
      rw [hs] at hM
      exact ⟨hc, hM⟩
  refine Spec.post (Spec.keep hfull pass1Vars ?_ ?_ ?_).frame ?_
  · intro y hy
    simp only [rowCount, adjCom, bump, Com.wvars, pass1Vars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowCount, adjCom, bump, Com.warrs]
  · simp [rowCount, adjCom, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq.1, hq.2, hk, ho (by simp [rowCount, adjCom, bump, Com.NoWrite])⟩

/-- Invariant of the offset loop. -/
def P2I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "ci_s" ≤ nOf x ∧ σ.vars "ci_off" = psum x (σ.vars "ci_s") ∧
    σ.out = out0 ++ (List.range (σ.vars "ci_s")).map (fun r => psum x (r + 1))

set_option maxHeartbeats 1000000 in
theorem pass2_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P2I x out0 σ ∧ σ.vars "ci_s" < nOf x)
      (.seq rowCount (.seq (.assign "ci_off" (.add (V "ci_off") (V "ci_d")))
        (.seq (.write (V "ci_off")) (bump "ci_s"))))
      (fun σ σ' => P2I x out0 σ' ∧ σ'.vars "ci_s" = σ.vars "ci_s" + 1) (Krow (nOf x) + 20) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hn := hB.n_lt
  refine Spec.pre (P := fun σ => P2I x out0 σ ∧ σ.vars "ci_s" < nOf x ∧
    psum x (σ.vars "ci_s") + degW x (σ.vars "ci_s") ≤ nOf x * nOf x) ?_ ?_
  · run_vcg [rowCount_spec' hB]
    all_goals (simp only [P2I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, psum_succ, List.range_succ]; try omega)
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, degW_le_psum x h2⟩

/-- The scalars `pass2` may assign. -/
def pass2Vars : List String := rowVars ++ ["ci_off", "ci_s"]

theorem pass2_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass2
      (fun _ σ' => Ctx x σ' ∧
        σ'.out = out0 ++ (List.range (nOf x)).map (fun r => psum x (r + 1))) (K1 (nOf x)) := by
  have hn := hB.n_lt
  unfold pass2
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "ci_off" (.add (V "ci_off") (V "ci_d")))
        (.seq (.write (V "ci_off")) (bump "ci_s"))))
    "ci_s" "ci_n" (P2I x out0) (nOf x) (Krow (nOf x) + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2) (pass2_body hB out0)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.out = out0) (.assign "ci_off" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "ci_off" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
  · rintro σ σ1 ⟨⟨ha, hm, hn⟩, ho⟩ rfl
    simp only [P2I, Ctx, Env.setVar]
    simp [psum, ha, hm, hn, ho]
  · rintro σ σ1 σ2 - - ⟨⟨hc, -, -, ho⟩, hs⟩
    rw [hs] at ho
    exact ⟨hc, ho⟩

theorem pass2_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass2
      (fun σ σ' => Ctx x σ' ∧
        σ'.out = σ.out ++ (List.range (nOf x)).map (fun r => psum x (r + 1)) ∧
        Keep pass2Vars σ σ') (K1 (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (pass2_value hB σ.out) pass2Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass2, rowCount, adjCom, bump, Com.wvars, pass2Vars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass2, rowCount, adjCom, bump, Com.warrs]
  · simp [pass2, rowCount, adjCom, bump, Com.reads]

/-- Invariant of the target-writing loop. -/
def P3I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "ci_s" ≤ nOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "ci_s")).flatMap (nbW x)

set_option maxHeartbeats 1000000 in
theorem pass3_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P3I x out0 σ ∧ σ.vars "ci_s" < nOf x)
      (.seq rowEmit (bump "ci_s"))
      (fun σ σ' => P3I x out0 σ' ∧ σ'.vars "ci_s" = σ.vars "ci_s" + 1) (Krow (nOf x) + 10) := by
  have hn := hB.n_lt
  refine Spec.pre (P := fun σ => P3I x out0 σ ∧ σ.vars "ci_s" < nOf x) ?_ (fun σ h => h)
  run_vcg [rowEmit_spec' hB]
  all_goals (simp only [P3I, Ctx, Keep, rowVars, adjVars] at *; simp_all [Env.setVar, List.range_succ, List.flatMap_append]; try omega)

/-- The scalars `pass3` may assign. -/
def pass3Vars : List String := rowVars ++ ["ci_s"]

/-- The cost of `pass3`. -/
def K3 (N : ℕ) : ℕ := (Krow N + 10 + 4) * N + 6

theorem pass3_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass3
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (nOf x)).flatMap (nbW x))
      (K3 (nOf x)) := by
  have hn := hB.n_lt
  unfold pass3
  have hloop := Spec.forRangeZero (B := B) (c := .seq rowEmit (bump "ci_s"))
    "ci_s" "ci_n" (P3I x out0) (nOf x) (Krow (nOf x) + 10) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2.2) (pass3_body hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K3])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨⟨ha, hm, hn⟩, ho⟩
    simp only [P3I, Ctx, Env.setVar]
    simp [ho, ha, hm, hn]

theorem pass3_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass3
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (nOf x)).flatMap (nbW x) ∧
        Keep pass3Vars σ σ') (K3 (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (pass3_value hB σ.out) pass3Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · intro y hy
    simp only [pass3, rowEmit, adjCom, emitIf, bump, Com.wvars, pass3Vars, rowVars,
      adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [pass3, rowEmit, adjCom, emitIf, bump, Com.warrs]
  · simp [pass3, rowEmit, adjCom, emitIf, bump, Com.reads]

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Passes
