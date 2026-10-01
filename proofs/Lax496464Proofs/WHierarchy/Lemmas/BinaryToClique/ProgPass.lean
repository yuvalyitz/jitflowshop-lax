import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow

/-! # Σ₁[2] model checking to Clique: the three passes (adapted from `CliqueMCC.ProdPass`)

The degree sum (`pass1_spec`), the offsets (`pass2_spec`) and the targets (`pass3_spec`) of the
compressed sparse row word, for the adjacency test of `ProgAdj5`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC

theorem ps_succ (x : List ℕ) (s : ℕ) : ps x (s + 1) = ps x s + dg x s :=
  CsrWord.psum_succ _ _ _

theorem ps_mono (x : List ℕ) {s t : ℕ} (h : s ≤ t) : ps x s ≤ ps x t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [ps_succ]; omega

theorem dg_le_ps (x : List ℕ) {s : ℕ} (h : s < NGX x) : ps x s + dg x s ≤ ps x (NGX x) := by
  rw [← ps_succ]; exact ps_mono x h

theorem Ctx_keepS {x : List ℕ} {σ σ' : Env} (S : List String) (h : Ctx x σ) (hk : Keep S σ σ')
    (hS : "rt_n" ∉ S ∧ "zk" ∉ S ∧ "zne" ∉ S ∧ "zNG" ∉ S) : Ctx x σ' := by
  obtain ⟨hv, ha, -⟩ := hk
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  refine ⟨⟨by rw [ha]; exact h1, by rw [hv _ hS.1]; exact h2, by rw [ha]; exact h3,
    by rw [ha]; exact h4, by rw [ha]; exact h5, by rw [ha]; exact h6, by rw [ha]; exact h7,
    by rw [hv _ hS.2.1]; exact h8, by rw [hv _ hS.2.2.1]; exact h9⟩,
    by rw [hv _ hS.2.2.2]; exact h10⟩

theorem write_run {B : ℕ} {σ : Env} (a : String) (h : σ.vars a < B) :
    Run B (.write (V a)) σ { σ with out := σ.out ++ [σ.vars a] } 2 := by
  have := Run.write (σ := σ) (evalB_var (x := a) (B := B) h)
  simpa using this

/-- The bound `B` must exceed: length, number of vertices, number of edge slots. -/
def BOK (x : List ℕ) (B : ℕ) : Prop := RB x B ∧ x.length + NGX x + ps x (NGX x) + 2 < B

theorem BOK.row {x : List ℕ} {B : ℕ} (h : BOK x B) : RB x B := h.1

/-- Invariant of the degree-sum loop. -/
def P1I (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "gs" ≤ NGX x ∧ σ.vars "gM" = ps x (σ.vars "gs")

set_option maxHeartbeats 1000000 in
theorem pass1_body {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => P1I x σ ∧ σ.vars "gs" < NGX x)
      (.seq rowCount (.seq (.assign "gM" (.add (V "gM") (V "gd"))) (bump "gs")))
      (fun σ σ' => P1I x σ' ∧ σ'.vars "gs" = σ.vars "gs" + 1) (Krow x + 20) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  intro σ ⟨⟨hc, hle, hM⟩, hlt⟩
  have hdp := dg_le_ps x hlt
  obtain ⟨σ1, r1, hd, hk, -⟩ := rowCount_spec' hB.row σ ⟨hc, hlt⟩
  have hc1 := Ctx_keepS rowVars hc hk (by decide)
  have m1 : σ1.vars "gM" = σ.vars "gM" := hk.1 _ (by decide)
  have s1 : σ1.vars "gs" = σ.vars "gs" := hk.1 _ (by decide)
  have r2 := assign_add_spec (B := B) (σ := σ1) "gM" "gM" "gd" (by rw [m1, hM, hd]; omega)
  have r3 := bump_run (B := B) (σ := σ1.setVar "gM" (σ1.vars "gM" + σ1.vars "gd")) "gs"
    (by simp [s1]; omega)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by omega), ⟨?_, ?_, ?_⟩, by simp [s1]⟩
  · exact Ctx_setVar (Ctx_setVar hc1 _ _ (by decide)) _ _ (by decide)
  · simp [s1]; omega
  · simp [s1, m1, hM, hd, ps_succ]

/-- The cost of `pass1`. -/
def K1 (x : List ℕ) : ℕ := (Krow x + 20 + 4) * NGX x + 8

/-- The scalars `pass1` may assign. -/
def pass1Vars : List String := rowVars ++ ["gM", "gs"]

theorem pass1_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass1
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "gM" = ps x (NGX x) ∧ Keep pass1Vars σ σ' ∧
        σ'.out = σ.out) (K1 x) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  unfold pass1
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "gM" (.add (V "gM") (V "gd"))) (bump "gs")))
    "gs" "zNG" (P1I x) (NGX x) (Krow x + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2) (pass1_body hB)
  have h0 : Spec B (fun σ => Ctx x σ) (.assign "gM" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "gM" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  have hfull : Spec B (fun σ => Ctx x σ)
      (.seq (.assign "gM" (.lit 0)) (.seq (.assign "gs" (.lit 0)) (.while (.lt (V "gs") (V "zNG"))
        (.seq rowCount (.seq (.assign "gM" (.add (V "gM") (V "gd"))) (bump "gs"))))))
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "gM" = ps x (NGX x)) (K1 x) := by
    refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
    · rintro σ σ1 hc rfl
      exact ⟨Ctx_setVar (Ctx_setVar hc _ _ (by decide)) _ _ (by decide), by simp,
        by simp [ps, CsrWord.psum]⟩
    · rintro σ σ1 σ2 - - ⟨⟨hc, -, hM⟩, hs⟩
      rw [hs] at hM
      exact ⟨hc, hM⟩
  refine Spec.post (Spec.keep hfull pass1Vars ?_ ?_ ?_).frame ?_
  · exact (show ∀ y ∈ Com.wvars (.seq (.assign "gM" (.lit 0)) (.seq (.assign "gs" (.lit 0))
      (.while (.lt (V "gs") (V "zNG")) (.seq rowCount (.seq (.assign "gM" (.add (V "gM") (V "gd")))
      (bump "gs")))))), y ∈ pass1Vars by decide)
  · decide
  · decide
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq.1, hq.2, hk, ho (by decide)⟩

/-- Invariant of the offset loop. -/
def P2I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "gs" ≤ NGX x ∧ σ.vars "goff" = ps x (σ.vars "gs") ∧
    σ.out = out0 ++ (List.range (σ.vars "gs")).map (fun r => ps x (r + 1))

set_option maxHeartbeats 1000000 in
theorem pass2_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P2I x out0 σ ∧ σ.vars "gs" < NGX x)
      (.seq rowCount (.seq (.assign "goff" (.add (V "goff") (V "gd")))
        (.seq (.write (V "goff")) (bump "gs"))))
      (fun σ σ' => P2I x out0 σ' ∧ σ'.vars "gs" = σ.vars "gs" + 1) (Krow x + 20) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  intro σ ⟨⟨hc, hle, hoff, ho⟩, hlt⟩
  have hdp := dg_le_ps x hlt
  obtain ⟨σ1, r1, hd, hk, ho1⟩ := rowCount_spec' hB.row σ ⟨hc, hlt⟩
  have hc1 := Ctx_keepS rowVars hc hk (by decide)
  have f1 : σ1.vars "goff" = σ.vars "goff" := hk.1 _ (by decide)
  have s1 : σ1.vars "gs" = σ.vars "gs" := hk.1 _ (by decide)
  have r2 := assign_add_spec (B := B) (σ := σ1) "goff" "goff" "gd" (by rw [f1, hoff, hd]; omega)
  set σ2 := σ1.setVar "goff" (σ1.vars "goff" + σ1.vars "gd") with hσ2
  have r3 := write_run (B := B) (σ := σ2) "goff" (by simp [hσ2, f1, hoff, hd]; omega)
  have r4 := bump_run (B := B) (σ := { σ2 with out := σ2.out ++ [σ2.vars "goff"] }) "gs"
    (by simp [hσ2, s1]; omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ⟨?_, ?_, ?_, ?_⟩, by simp [hσ2, s1]⟩
  · have := Ctx_setVar (Ctx_setVar hc1 "goff" (σ1.vars "goff" + σ1.vars "gd") (by decide)) "gs"
      (σ.vars "gs" + 1) (by decide)
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := this
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩
  · simp [hσ2, s1]; omega
  · simp [hσ2, s1, f1, hoff, hd, ps_succ]
  · simp [hσ2, s1, f1, hoff, hd, ps_succ, ho1, ho, List.range_succ]

/-- The scalars `pass2` may assign. -/
def pass2Vars : List String := rowVars ++ ["goff", "gs"]

theorem pass2_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass2
      (fun _ σ' => Ctx x σ' ∧
        σ'.out = out0 ++ (List.range (NGX x)).map (fun r => ps x (r + 1))) (K1 x) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  unfold pass2
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq rowCount (.seq (.assign "goff" (.add (V "goff") (V "gd")))
        (.seq (.write (V "goff")) (bump "gs"))))
    "gs" "zNG" (P2I x out0) (NGX x) (Krow x + 20) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2) (pass2_body hB out0)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.out = out0) (.assign "goff" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "goff" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [K1, Expr.size]; omega)
  · rintro σ σ1 ⟨hc, ho⟩ rfl
    exact ⟨Ctx_setVar (Ctx_setVar hc _ _ (by decide)) _ _ (by decide), by simp,
      by simp [ps, CsrWord.psum], by simp [ho]⟩
  · rintro σ σ1 σ2 - - ⟨⟨hc, -, -, ho⟩, hs⟩
    rw [hs] at ho
    exact ⟨hc, ho⟩

theorem pass2_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass2
      (fun σ σ' => Ctx x σ' ∧
        σ'.out = σ.out ++ (List.range (NGX x)).map (fun r => ps x (r + 1)) ∧
        Keep pass2Vars σ σ') (K1 x) := by
  intro σ hσ
  have h := Spec.keep (pass2_value hB σ.out) pass2Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · exact (show ∀ y ∈ pass2.wvars, y ∈ pass2Vars by decide)
  · decide
  · decide

/-- Invariant of the target-writing loop. -/
def P3I (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "gs" ≤ NGX x ∧
    σ.out = out0 ++ (List.range (σ.vars "gs")).flatMap (nb x)

set_option maxHeartbeats 1000000 in
theorem pass3_body {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => P3I x out0 σ ∧ σ.vars "gs" < NGX x)
      (.seq rowEmit (bump "gs"))
      (fun σ σ' => P3I x out0 σ' ∧ σ'.vars "gs" = σ.vars "gs" + 1) (Krow x + 10) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  intro σ ⟨⟨hc, hle, ho⟩, hlt⟩
  obtain ⟨σ1, r1, ho1, hk⟩ := rowEmit_spec' hB.row σ ⟨hc, hlt⟩
  have hc1 := Ctx_keepS rowVars hc hk (by decide)
  have s1 : σ1.vars "gs" = σ.vars "gs" := hk.1 _ (by decide)
  have r2 := bump_run (B := B) (σ := σ1) "gs" (by rw [s1]; omega)
  refine ⟨_, (r1.seq r2).mono (by omega), ⟨?_, ?_, ?_⟩, by simp [s1]⟩
  · exact Ctx_setVar hc1 _ _ (by decide)
  · simp [s1]; omega
  · simp [ho1, ho, s1, List.range_succ, List.flatMap_append]

/-- The scalars `pass3` may assign. -/
def pass3Vars : List String := rowVars ++ ["gs"]

/-- The cost of `pass3`. -/
def K3 (x : List ℕ) : ℕ := (Krow x + 10 + 4) * NGX x + 6

theorem pass3_value {x : List ℕ} {B : ℕ} (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) pass3
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (List.range (NGX x)).flatMap (nb x)) (K3 x) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  unfold pass3
  have hloop := Spec.forRangeZero (B := B) (c := .seq rowEmit (bump "gs"))
    "gs" "zNG" (P3I x out0) (NGX x) (Krow x + 10) (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1.2) (pass3_body hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [K3])
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, ht⟩
    rw [ht] at ho
    exact ⟨hc, ho⟩
  · rintro σ ⟨hc, ho⟩
    exact ⟨Ctx_setVar hc _ _ (by decide), by simp, by simp [ho]⟩

theorem pass3_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ) pass3
      (fun σ σ' => Ctx x σ' ∧ σ'.out = σ.out ++ (List.range (NGX x)).flatMap (nb x) ∧
        Keep pass3Vars σ σ') (K3 x) := by
  intro σ hσ
  have h := Spec.keep (pass3_value hB σ.out) pass3Vars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
    exact ⟨σ', hr, hq.1, hq.2, hk⟩
  · exact (show ∀ y ∈ pass3.wvars, y ∈ pass3Vars by decide)
  · decide
  · decide

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass
