import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5

/-! # Σ₁[2] model checking to Clique: one row of the graph (adapted from `CliqueMCC.ProdRow`)

`rowCount_spec`: the degree of a vertex; `rowEmit_spec`: its neighbours in increasing order, for the
adjacency test of `ProgAdj5`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC

/-- The context of the passes. -/
def Ctx (x : List ℕ) (σ : Env) : Prop := AC x σ ∧ σ.vars "zNG" = NGX x

/-- The neighbours of `s`. -/
abbrev nb (x : List ℕ) (s : ℕ) : List ℕ := CsrWord.nbW (adjX x) (NGX x) s

/-- The degree of `s`. -/
abbrev dg (x : List ℕ) (s : ℕ) : ℕ := CsrWord.degW (adjX x) (NGX x) s

/-- The sum of the first `s` degrees. -/
abbrev ps (x : List ℕ) (s : ℕ) : ℕ := CsrWord.psum (adjX x) (NGX x) s

theorem Ctx_setVar {x : List ℕ} {σ : Env} (h : Ctx x σ) (y : String) (v : ℕ)
    (hy : y ∉ ["rt_n", "zk", "zne", "zNG"]) : Ctx x (σ.setVar y v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  exact ⟨⟨h1, by simp [Ne.symm hy.1, h2], h3, h4, h5, h6, h7, by simp [Ne.symm hy.2.1, h8],
    by simp [Ne.symm hy.2.2.1, h9]⟩, by simp [Ne.symm hy.2.2.2, h10]⟩

theorem Ctx_keep {x : List ℕ} {σ σ' : Env} (h : Ctx x σ) (hk : Keep adjVars σ σ') : Ctx x σ' := by
  obtain ⟨hv, ha, -⟩ := hk
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  refine ⟨⟨by rw [ha]; exact h1, by rw [hv _ (by decide)]; exact h2, by rw [ha]; exact h3,
    by rw [ha]; exact h4, by rw [ha]; exact h5, by rw [ha]; exact h6, by rw [ha]; exact h7,
    by rw [hv _ (by decide)]; exact h8, by rw [hv _ (by decide)]; exact h9⟩,
    by rw [hv _ (by decide)]; exact h10⟩

/-- The hypotheses a row runs under: the shape of the word and the value bound. -/
def RB (x : List ℕ) (B : ℕ) : Prop := AB x B ∧ x.length + NGX x + 2 < B

/-- The number of neighbours of `s` among the first `t` vertices. -/
def dpre (x : List ℕ) (s t : ℕ) : ℕ := ((List.range t).filter (adjX x s)).length

theorem dpre_succ (x : List ℕ) (s t : ℕ) :
    dpre x s (t + 1) = dpre x s t + if adjX x s t then 1 else 0 := by
  unfold dpre
  rw [List.range_succ, List.filter_append]
  by_cases h : adjX x s t = true <;> simp [h]

theorem dpre_le (x : List ℕ) (s t : ℕ) : dpre x s t ≤ t := by
  unfold dpre
  exact (List.length_filter_le _ _).trans (by simp)

/-- The invariant of the row loops. -/
def RowI (x : List ℕ) (s : ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "gs" = s ∧ σ.vars "gt" ≤ NGX x ∧ σ.vars "gd" = dpre x s (σ.vars "gt")

theorem assign_add_spec {B : ℕ} {σ : Env} (dst a b : String) (h : σ.vars a + σ.vars b < B) :
    Run B (.assign dst (.add (V a) (V b))) σ (σ.setVar dst (σ.vars a + σ.vars b)) 4 := by
  have ha : (V a).evalB B σ = some (σ.vars a) := evalB_var (by omega)
  have hb : (V b).evalB B σ = some (σ.vars b) := evalB_var (by omega)
  have := Run.assign (x := dst) (σ := σ) (evalB_bin (op := .add) ha hb (by simpa using h))
  simpa using this

theorem bump_run {B : ℕ} {σ : Env} (a : String) (h : σ.vars a + 1 < B) :
    Run B (bump a) σ (σ.setVar a (σ.vars a + 1)) 4 := by
  have ha : (V a).evalB B σ = some (σ.vars a) := evalB_var (by omega)
  have hb : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
  have := Run.assign (x := a) (σ := σ) (evalB_bin (op := .add) ha hb (by simpa using h))
  simpa using this

set_option maxHeartbeats 1000000 in
theorem rowCount_body {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) :
    Spec B (fun σ => RowI x s σ ∧ σ.vars "gt" < NGX x)
      (.seq adjCom (.seq (.assign "gd" (.add (V "gd") (V "gf"))) (bump "gt")))
      (fun σ σ' => RowI x s σ' ∧ σ'.vars "gt" = σ.vars "gt" + 1) (Kadj x + 100) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  intro σ ⟨⟨hc, hs', hle, hd⟩, hlt⟩
  obtain ⟨σ1, r1, hf, hk, -⟩ := adjCom_spec' hR.1 σ ⟨hc.1, by rw [hs']; exact hs, hlt⟩
  have hc1 := Ctx_keep hc hk
  have g1 : σ1.vars "gd" = σ.vars "gd" := hk.1 _ (by decide)
  have t1 : σ1.vars "gt" = σ.vars "gt" := hk.1 _ (by decide)
  have s1 : σ1.vars "gs" = σ.vars "gs" := hk.1 _ (by decide)
  have hdl := dpre_le x s (σ.vars "gt")
  have hfB : σ1.vars "gf" ≤ 1 := by rw [hf]; split_ifs <;> omega
  have r2 := assign_add_spec (B := B) (σ := σ1) "gd" "gd" "gf" (by rw [g1, hd]; omega)
  have r3 := bump_run (B := B) (σ := σ1.setVar "gd" (σ1.vars "gd" + σ1.vars "gf")) "gt"
    (by simp [t1]; omega)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by unfold Kadj at *; omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Ctx_setVar (Ctx_setVar hc1 _ _ (by decide)) _ _ (by decide)
  · simp [s1, hs']
  · simp [t1]; omega
  · simp [t1, g1, hd, hf, dpre_succ, hs']
  · simp [t1]
/-- The scalars a row command may assign. -/
def rowVars : List String := adjVars ++ ["gd", "gt"]

/-- The cost of a row command. -/
def Krow (x : List ℕ) : ℕ := (Kadj x + 100 + 4) * NGX x + 8

theorem rowCount_value {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" = s) rowCount
      (fun _ σ' => σ'.vars "gd" = dg x s) (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  unfold rowCount
  have hloop := Spec.forRangeZero (B := B) (c := .seq adjCom (.seq (.assign "gd" (.add (V "gd") (V "gf"))) (bump "gt")))
    "gt" "zNG" (RowI x s) (NGX x) (Kadj x + 100) (by have := hR.2; omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2)
    (rowCount_body hR hs)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" = s) (.assign "gd" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "gd" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [Krow, Expr.size]; omega)
  · rintro σ σ1 ⟨hc, hs'⟩ rfl
    refine ⟨Ctx_setVar (Ctx_setVar hc _ _ (by decide)) _ _ (by decide), by simp [hs'], by simp,
      by simp [dpre]⟩
  · rintro σ σ1 σ2 - - ⟨⟨-, -, -, hd⟩, ht⟩
    rw [hd, ht]; rfl

theorem rowCount_spec {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" = s) rowCount
      (fun σ σ' => σ'.vars "gd" = dg x s ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out) (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  refine Spec.post (Spec.keep (rowCount_value hR hs) rowVars ?_ ?_ ?_).frame ?_
  · exact (show ∀ y ∈ rowCount.wvars, y ∈ rowVars by decide)
  · decide
  · decide
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq, hk, ho (by decide)⟩

theorem filter_range_succ (x : List ℕ) (s t : ℕ) :
    (List.range (t + 1)).filter (adjX x s) =
      (List.range t).filter (adjX x s) ++ if adjX x s t = true then [t] else [] := by
  rw [List.range_succ, List.filter_append]
  by_cases h : adjX x s t = true <;> simp [h]

/-- The invariant of the emitting row loop. -/
def EmI (x : List ℕ) (s : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "gs" = s ∧ σ.vars "gt" ≤ NGX x ∧
    σ.out = out0 ++ (List.range (σ.vars "gt")).filter (adjX x s)

theorem emitIf_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "gt" < B ∧ σ.vars "gf" < B ∧ 1 < B) emitIf
      (fun σ σ' => σ'.out = σ.out ++ (if σ.vars "gf" = 1 then [σ.vars "gt"] else []) ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 10 := by
  unfold emitIf
  run_vcg
  all_goals simp_all

set_option maxHeartbeats 1000000 in
theorem rowEmit_body {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) (out0 : List ℕ) :
    Spec B (fun σ => EmI x s out0 σ ∧ σ.vars "gt" < NGX x)
      (.seq adjCom (.seq emitIf (bump "gt")))
      (fun σ σ' => EmI x s out0 σ' ∧ σ'.vars "gt" = σ.vars "gt" + 1) (Kadj x + 100) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  intro σ ⟨⟨hc, hs', hle, ho⟩, hlt⟩
  obtain ⟨σ1, r1, hf, hk, ho1⟩ := adjCom_spec' hR.1 σ ⟨hc.1, by rw [hs']; exact hs, hlt⟩
  have hc1 := Ctx_keep hc hk
  have t1 : σ1.vars "gt" = σ.vars "gt" := hk.1 _ (by decide)
  have s1 : σ1.vars "gs" = σ.vars "gs" := hk.1 _ (by decide)
  have hfB : σ1.vars "gf" ≤ 1 := by rw [hf]; split_ifs <;> omega
  obtain ⟨σ2, r2, he1, he2, he3, he4⟩ := emitIf_spec (B := B) σ1 ⟨by omega, by omega, by omega⟩
  have hc2 : Ctx x σ2 := Ctx_keep hc1 ⟨fun y _ => by rw [he2], he3, he4⟩
  have t2 : σ2.vars "gt" = σ.vars "gt" := by rw [he2, t1]
  have r3 := bump_run (B := B) (σ := σ2) "gt" (by rw [t2]; omega)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by unfold Kadj at *; omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Ctx_setVar hc2 _ _ (by decide)
  · simp [he2, s1, hs']
  · simp [t2]; omega
  · simp only [out_setVar, vars_setVar, ↓reduceIte, he1, ho1, ho, hf, t2, t1, hs']
    rw [filter_range_succ]
    split_ifs <;> simp_all
  · simp [t2]

theorem rowEmit_value {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" = s ∧ σ.out = out0) rowEmit
      (fun _ σ' => σ'.out = out0 ++ nb x s) (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  unfold rowEmit
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq adjCom (.seq emitIf (bump "gt")))
    "gt" "zNG" (EmI x s out0) (NGX x) (Kadj x + 100) (by have := hR.2; omega) (fun σ h => h.2.2.1)
    (fun σ h => h.1.2) (rowEmit_body hR hs out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [Krow])
  · rintro σ σ' - ⟨⟨-, -, -, ho⟩, ht⟩
    rw [ho, ht]; rfl
  · rintro σ ⟨hc, hs', ho⟩
    refine ⟨Ctx_setVar hc _ _ (by decide), by simp [hs'], by simp, by simp [ho]⟩

theorem rowEmit_spec {x : List ℕ} {B : ℕ} (hR : RB x B)
    {s : ℕ} (hs : s < NGX x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" = s) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nb x s ∧ Keep rowVars σ σ') (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  intro σ hσ
  have h := Spec.keep (rowEmit_value hR hs σ.out) rowVars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ.1, hσ.2, rfl⟩
    exact ⟨σ', hr, hq, hk⟩
  · exact (show ∀ y ∈ rowEmit.wvars, y ∈ rowVars by decide)
  · decide
  · decide

/-- State-relative form: the vertex is whatever `b_s` holds. -/
theorem rowCount_spec' {x : List ℕ} {B : ℕ} (hR : RB x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" < NGX x) rowCount
      (fun σ σ' => σ'.vars "gd" = dg x (σ.vars "gs") ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out)
      (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  intro σ hσ
  exact rowCount_spec hR hσ.2 σ ⟨hσ.1, rfl⟩

theorem rowEmit_spec' {x : List ℕ} {B : ℕ} (hR : RB x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "gs" < NGX x) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nb x (σ.vars "gs") ∧ Keep rowVars σ σ') (Krow x) := by
  have hxB : x.length + NGX x + 2 < B := hR.2
  intro σ hσ
  exact rowEmit_spec hR hσ.2 σ ⟨hσ.1, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow
