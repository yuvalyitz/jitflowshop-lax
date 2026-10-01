import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill

/-! # The complement test and one row: `adjCom`, `rowCount`, `rowEmit`

`adjCom_spec`: the complement test of `(s, t)` on the adjacency matrix; `rowCount_spec` and
`rowEmit_spec`: the degree of a vertex in the complement and its neighbours in increasing order. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill

/-- The context every pass runs in: the word, the finished matrix, `n`. -/
def Ctx (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.arrs "mat" = matF x ∧ σ.vars "ci_n" = nOf x

theorem adjW_eq_of (x : List ℕ) (s t : ℕ) (m : ℕ) (hm : m = if inBlock x s t then 1 else 0) :
    (if s = t then 0 else if m = 0 then 1 else 0) = if adjW x s t then 1 else 0 := by
  by_cases hst : s = t
  · subst hst; simp [adjW]
  · by_cases hb : inBlock x s t = true
    · simp [adjW, hst, hb, hm]
    · simp [adjW, hst, hb, hm]

set_option maxHeartbeats 1000000 in
theorem adjCom_value {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" < nOf x ∧ σ.vars "ci_t" < nOf x) adjCom
      (fun σ σ' => σ'.vars "ci_f" =
        if σ.vars "ci_s" = σ.vars "ci_t" then 0 else
          if (σ.arrs "mat").getD (σ.vars "ci_s" * σ.vars "ci_n" + σ.vars "ci_t") 0 = 0 then 1
          else 0) 100 := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  unfold adjCom
  refine Spec.pre (P := fun σ => Ctx x σ ∧ σ.vars "ci_s" < nOf x ∧ σ.vars "ci_t" < nOf x ∧
      σ.vars "ci_s" * σ.vars "ci_n" + σ.vars "ci_t" < (σ.arrs "mat").length ∧
      (σ.arrs "mat").getD (σ.vars "ci_s" * σ.vars "ci_n" + σ.vars "ci_t") 0 ≤ 1 ∧
      σ.vars "ci_s" * σ.vars "ci_n" + σ.vars "ci_t" < B ∧ 1 < B ∧ nOf x < B) ?_ ?_
  · run_vcg
    all_goals (simp only [Ctx] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨ha, hm, hn⟩, hs, ht⟩
    have hsq := mul_add_lt_sq hs ht
    refine ⟨⟨ha, hm, hn⟩, hs, ht, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm, hn, length_matF]; exact hsq
    · rw [hm, hn, matF_getD hs ht]; split <;> omega
    · rw [hn]; omega
    · omega
    · have := hB.n_lt; omega

/-- The scalars assigned by `adjCom`. -/
def adjVars : List String := ["ci_f"]

theorem adjCom_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" < nOf x ∧ σ.vars "ci_t" < nOf x) adjCom
      (fun σ σ' => σ'.vars "ci_f" = (if adjW x (σ.vars "ci_s") (σ.vars "ci_t") then 1 else 0) ∧
        Keep adjVars σ σ' ∧ σ'.out = σ.out) 100 := by
  refine Spec.post (Spec.frame (adjCom_value hB)) fun σ σ' hpre ⟨hq, hv, ha, hi, ho⟩ => ⟨?_, ?_, ?_⟩
  · obtain ⟨⟨-, hm, hn⟩, hs, ht⟩ := hpre
    rw [hq]
    apply adjW_eq_of
    rw [hm, hn, matF_getD hs ht]
  · refine ⟨fun y hy => hv y ?_, funext fun a => ha a ?_, hi ?_⟩
    · simp only [adjCom, Com.wvars, adjVars] at hy ⊢
      simpa using hy
    · simp [adjCom, Com.warrs]
    · simp [adjCom, Com.reads]
  · exact ho (by simp [adjCom, Com.NoWrite])

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
  Ctx x σ ∧ σ.vars "ci_s" = s ∧ σ.vars "ci_t" ≤ nOf x ∧ σ.vars "ci_d" = dpre x s (σ.vars "ci_t")

set_option maxHeartbeats 1000000 in
theorem rowCount_body {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => RowI x s σ ∧ σ.vars "ci_t" < nOf x)
      (.seq adjCom (.seq (.assign "ci_d" (.add (V "ci_d") (V "ci_f"))) (bump "ci_t")))
      (fun σ σ' => RowI x s σ' ∧ σ'.vars "ci_t" = σ.vars "ci_t" + 1) 200 := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  refine Spec.pre (P := fun σ => RowI x s σ ∧ σ.vars "ci_t" < nOf x ∧
    dpre x s (σ.vars "ci_t") ≤ σ.vars "ci_t" ∧ nOf x < B) ?_ ?_
  · run_vcg [adjCom_spec hB]
    all_goals (simp only [RowI, Ctx, Keep, adjVars] at *; simp_all [Env.setVar, dpre_succ]; try (first | omega | (split_ifs <;> omega)))
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, dpre_le _ _ _, by have := hB.n_lt; omega⟩

/-- The scalars a row command may assign. -/
def rowVars : List String := adjVars ++ ["ci_d", "ci_t"]

/-- The cost of a row command. -/
def Krow (N : ℕ) : ℕ := 204 * N + 8

theorem rowCount_value {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" = s) rowCount
      (fun _ σ' => σ'.vars "ci_d" = degW x s) (Krow (nOf x)) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  unfold rowCount
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq adjCom (.seq (.assign "ci_d" (.add (V "ci_d") (V "ci_f"))) (bump "ci_t")))
    "ci_t" "ci_n" (RowI x s) (nOf x) 200 (by have := hB.n_lt; omega) (fun σ h => h.2.2.1)
    (fun σ h => h.1.2.2) (rowCount_body hB hs)
  have h0 : Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" = s) (.assign "ci_d" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "ci_d" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [Krow, Expr.size]; omega)
  · rintro σ σ1 ⟨⟨ha, hm, hn⟩, hs'⟩ rfl
    simp only [RowI, Ctx, Env.setVar]
    simp [dpre, hs', ha, hm, hn]
  · rintro σ σ1 σ2 - - ⟨⟨-, -, -, hd⟩, ht⟩
    rw [hd, ht]; rfl

theorem rowCount_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" = s) rowCount
      (fun σ σ' => σ'.vars "ci_d" = degW x s ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out)
      (Krow (nOf x)) := by
  refine Spec.post (Spec.keep (rowCount_value hB hs) rowVars ?_ ?_ ?_).frame ?_
  · intro y hy
    simp only [rowCount, adjCom, bump, Com.wvars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowCount, adjCom, bump, Com.warrs]
  · simp [rowCount, adjCom, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq, hk, ho (by simp [rowCount, adjCom, bump, Com.NoWrite])⟩

theorem filter_range_succ (x : List ℕ) (s t : ℕ) :
    (List.range (t + 1)).filter (adjW x s) =
      (List.range t).filter (adjW x s) ++ if adjW x s t = true then [t] else [] := by
  rw [List.range_succ, List.filter_append]
  by_cases h : adjW x s t = true <;> simp [h]

/-- The invariant of the emitting row loop. -/
def EmI (x : List ℕ) (s : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "ci_s" = s ∧ σ.vars "ci_t" ≤ nOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "ci_t")).filter (adjW x s)

theorem emitIf_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "ci_t" < B ∧ σ.vars "ci_f" < B ∧ 1 < B) emitIf
      (fun σ σ' => σ'.out = σ.out ++ (if σ.vars "ci_f" = 1 then [σ.vars "ci_t"] else []) ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 10 := by
  unfold emitIf
  run_vcg
  all_goals simp_all

set_option maxHeartbeats 1000000 in
theorem rowEmit_body {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x)
    (out0 : List ℕ) :
    Spec B (fun σ => EmI x s out0 σ ∧ σ.vars "ci_t" < nOf x)
      (.seq adjCom (.seq emitIf (bump "ci_t")))
      (fun σ σ' => EmI x s out0 σ' ∧ σ'.vars "ci_t" = σ.vars "ci_t" + 1) 200 := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  refine Spec.pre (P := fun σ => EmI x s out0 σ ∧ σ.vars "ci_t" < nOf x ∧ 1 < B ∧ nOf x < B) ?_ ?_
  · run_vcg [adjCom_spec hB, emitIf_spec (B := B)]
    all_goals (simp only [EmI, Ctx, Keep, adjVars] at *; simp_all [Env.setVar, filter_range_succ]; try (first | omega | (split_ifs <;> omega)))
  · rintro σ ⟨h1, h2⟩
    exact ⟨h1, h2, by have := hB.n_lt; omega, by have := hB.n_lt; omega⟩

theorem rowEmit_value {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x)
    (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" = s ∧ σ.out = out0) rowEmit
      (fun _ σ' => σ'.out = out0 ++ nbW x s) (Krow (nOf x)) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  unfold rowEmit
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq adjCom (.seq emitIf (bump "ci_t")))
    "ci_t" "ci_n" (EmI x s out0) (nOf x) 200 (by have := hB.n_lt; omega) (fun σ h => h.2.2.1)
    (fun σ h => h.1.2.2) (rowEmit_body hB hs out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by simp [Krow])
  · rintro σ σ' - ⟨⟨-, -, -, ho⟩, ht⟩
    rw [ho, ht]; rfl
  · rintro σ ⟨⟨ha, hm, hn⟩, hs', ho⟩
    simp only [EmI, Ctx, Env.setVar]
    simp [ho, ha, hm, hn, hs']

theorem rowEmit_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) {s : ℕ} (hs : s < nOf x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" = s) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nbW x s ∧ Keep rowVars σ σ') (Krow (nOf x)) := by
  intro σ hσ
  have h := Spec.keep (rowEmit_value hB hs σ.out) rowVars ?_ ?_ ?_
  · obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ.1, hσ.2, rfl⟩
    exact ⟨σ', hr, hq, hk⟩
  · intro y hy
    simp only [rowEmit, adjCom, emitIf, bump, Com.wvars, rowVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [rowEmit, adjCom, emitIf, bump, Com.warrs]
  · simp [rowEmit, adjCom, emitIf, bump, Com.reads]

/-- State-relative form: the vertex is whatever `ci_s` holds. -/
theorem rowCount_spec' {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" < nOf x) rowCount
      (fun σ σ' => σ'.vars "ci_d" = degW x (σ.vars "ci_s") ∧ Keep rowVars σ σ' ∧ σ'.out = σ.out)
      (Krow (nOf x)) := by
  intro σ hσ
  exact rowCount_spec hB hσ.2 σ ⟨hσ.1, rfl⟩

theorem rowEmit_spec' {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "ci_s" < nOf x) rowEmit
      (fun σ σ' => σ'.out = σ.out ++ nbW x (σ.vars "ci_s") ∧ Keep rowVars σ σ') (Krow (nOf x)) := by
  intro σ hσ
  exact rowEmit_spec hB hσ.2 σ ⟨hσ.1, rfl⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows
