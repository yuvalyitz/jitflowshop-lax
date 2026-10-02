import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj

/-!
# One Row of the Multicoloured Graph

The loop counting the neighbours of one vertex, with its invariant and cost.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj

/-- The number of neighbours of `s` among the first `t` vertices. -/
def dpre (x : List ℕ) (s t : ℕ) : ℕ := ((List.range t).filter (adjW x s)).length

theorem dpre_succ (x : List ℕ) (s t : ℕ) :
    dpre x s (t + 1) = dpre x s t + if adjW x s t then 1 else 0 := by
  unfold dpre
  rw [List.range_succ, List.filter_append]
  by_cases h : adjW x s t = true <;> simp [h]

theorem dpre_le (x : List ℕ) (s t : ℕ) : dpre x s t ≤ t := by
  unfold dpre
  exact (List.length_filter_le _ _).trans (by simp)

/-- The invariant of the row loops. -/
def RowI (x : List ℕ) (s : ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" = s ∧ σ.vars "b_t" ≤ nOf x ∧ σ.vars "b_d" = dpre x s (σ.vars "b_t")

set_option maxHeartbeats 1000000 in
theorem rowCount_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => RowI x s σ ∧ σ.vars "b_t" < nOf x)
      (.seq adjCom (.seq (.assign "b_d" (.add (V "b_d") (V "b_f"))) (bump "b_t")))
      (fun σ σ' => RowI x s σ' ∧ σ'.vars "b_t" = σ.vars "b_t" + 1) 300 := by
  refine Spec.pre (P := fun σ => RowI x s σ ∧ σ.vars "b_t" < nOf x ∧ dpre x s (σ.vars "b_t") ≤ σ.vars "b_t") ?_ ?_
  · run_vcg [adjCom_spec' hx hB]
    all_goals (simp only [RowI, Ctx, Keep, adjVars] at *; simp_all [Env.setVar, dpre_succ]; try (first | omega | (split_ifs <;> omega)))
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, dpre_le _ _ _⟩

/-- The scalars a row command may assign. -/
def rowVars : List String := adjVars ++ ["b_d", "b_t"]

/-- The cost of a row command. -/
def Krow (N : ℕ) : ℕ := 304 * N + 8

theorem rowCount_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" = s) rowCount
      (fun _ σ' => σ'.vars "b_d" = degW x s) (Krow (nOf x)) := by
  unfold rowCount
  have hloop := Spec.forRangeZero (B := B) (c := .seq adjCom (.seq (.assign "b_d" (.add (V "b_d") (V "b_f"))) (bump "b_t")))
    "b_t" "b_N" (RowI x s) (nOf x) 300 (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2.2.2)
    (rowCount_body hx hB hs)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" = s) (.assign "b_d" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "b_d" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [Krow, Expr.size]; omega)
  · rintro σ σ1 ⟨⟨ha, hn, hbase, hN⟩, hs'⟩ rfl
    simp only [RowI, Ctx, Env.setVar]
    simp [dpre, hs', ha, hn, hbase, hN]
  · rintro σ σ1 σ2 - - ⟨⟨-, -, -, hd⟩, ht⟩
    rw [hd, ht]; rfl

theorem rowCount_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" = s) rowCount
      (fun σ σ' => σ'.vars "b_d" = degW x s ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out) (Krow (nOf x)) := by
  refine Spec.post (Spec.keep (rowCount_value hx hB hs) rowVars ?_ ?_ ?_).frame ?_
  · intro y hy
    simp only [rowCount, adjCom, adjPrep, adjTest, bump, Com.wvars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.warrs]
  · simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq, hk, ho (by simp [rowCount, adjCom, adjPrep, adjTest, bump, Com.NoWrite])⟩

theorem filter_range_succ (x : List ℕ) (s t : ℕ) :
    (List.range (t + 1)).filter (adjW x s) =
      (List.range t).filter (adjW x s) ++ if adjW x s t = true then [t] else [] := by
  rw [List.range_succ, List.filter_append]
  by_cases h : adjW x s t = true <;> simp [h]

/-- The invariant of the emitting row loop. -/
def EmI (x : List ℕ) (s : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "b_s" = s ∧ σ.vars "b_t" ≤ nOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "b_t")).filter (adjW x s)

theorem emitIf_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "b_t" < B ∧ σ.vars "b_f" < B ∧ 1 < B) emitIf
      (fun σ σ' => σ'.out = σ.out ++ (if σ.vars "b_f" = 1 then [σ.vars "b_t"] else []) ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 10 := by
  unfold emitIf
  run_vcg
  all_goals simp_all

set_option maxHeartbeats 1000000 in
theorem rowEmit_body {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) (out0 : List ℕ) :
    Spec B (fun σ => EmI x s out0 σ ∧ σ.vars "b_t" < nOf x)
      (.seq adjCom (.seq emitIf (bump "b_t")))
      (fun σ σ' => EmI x s out0 σ' ∧ σ'.vars "b_t" = σ.vars "b_t" + 1) 300 := by
  refine Spec.pre (P := fun σ => EmI x s out0 σ ∧ σ.vars "b_t" < nOf x ∧ 1 < B) ?_ ?_
  · run_vcg [adjCom_spec' hx hB, emitIf_spec (B := B)]
    all_goals (simp only [EmI, Ctx, Keep, adjVars] at *; simp_all [Env.setVar, filter_range_succ]; try (first | omega | (split_ifs <;> omega)))
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, by omega⟩

theorem rowEmit_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" = s ∧ σ.out = out0) rowEmit
      (fun _ σ' => σ'.out = out0 ++ nbW x s) (Krow (nOf x)) := by
  unfold rowEmit
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq adjCom (.seq emitIf (bump "b_t")))
    "b_t" "b_N" (EmI x s out0) (nOf x) 300 (by omega) (fun σ h => h.2.2.1)
    (fun σ h => h.1.2.2.2) (rowEmit_body hx hB hs out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [Krow])
  · rintro σ σ' - ⟨⟨-, -, -, ho⟩, ht⟩
    rw [ho, ht]; rfl
  · rintro σ ⟨⟨ha, hn, hbase, hN⟩, hs', ho⟩
    simp only [EmI, Ctx, Env.setVar]
    simp [ho, ha, hn, hbase, hN, hs']

theorem rowEmit_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B)
    {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" = s) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nbW x s ∧ Keep rowVars σ σ') (Krow (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (rowEmit_value hx hB hs σ.out) rowVars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ.1, hσ.2, rfl⟩
    exact ⟨σ', hr, hq, hk⟩
  · intro y hy
    simp only [rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.wvars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.warrs]
  · simp [rowEmit, adjCom, adjPrep, adjTest, emitIf, bump, Com.reads]

/-- State-relative form: the vertex is whatever `b_s` holds. -/
theorem rowCount_spec' {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < nOf x) rowCount
      (fun σ σ' => σ'.vars "b_d" = degW x (σ.vars "b_s") ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out)
      (Krow (nOf x)) := by
  intro σ hσ
  exact rowCount_spec hx hB hσ.2 σ ⟨hσ.1, rfl⟩

theorem rowEmit_spec' {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < nOf x) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nbW x (σ.vars "b_s") ∧ Keep rowVars σ σ') (Krow (nOf x)) := by
  intro σ hσ
  exact rowEmit_spec hx hB hσ.2 σ ⟨hσ.1, rfl⟩

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow
