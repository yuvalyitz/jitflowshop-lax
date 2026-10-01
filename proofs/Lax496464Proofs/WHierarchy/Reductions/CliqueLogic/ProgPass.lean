import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj

/-!
# The two passes over the pairs, and the word of the graph structure

`countPass` counts the adjacent ordered pairs, `emitPass` writes them, and `graphCom` writes the
word of the graph structure `1, 2, n, M, pairs`.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj

/-! ### The mathematics of the passes -/

/-- The adjacent `v' < v` of `u`. -/
def cntRow (x : List ℕ) (u v : ℕ) : ℕ := ((List.range v).filter (adjW x u)).length

/-- The adjacent pairs with first vertex below `u`. -/
def cntUpTo (x : List ℕ) (u : ℕ) : ℕ := ((List.range u).map fun u' => (rowW x u').length).sum

theorem cntRow_succ (x : List ℕ) (u v : ℕ) :
    cntRow x u (v + 1) = cntRow x u v + if adjW x u v then 1 else 0 := by
  unfold cntRow
  rw [List.range_succ, List.filter_append]
  by_cases h : adjW x u v = true <;> simp [h]

theorem cntRow_le (x : List ℕ) (u v : ℕ) : cntRow x u v ≤ v := by
  unfold cntRow
  exact (List.length_filter_le _ _).trans (by simp)

theorem cntRow_full (x : List ℕ) (u : ℕ) : cntRow x u (nV x) = (rowW x u).length := rfl

theorem cntUpTo_succ (x : List ℕ) (u : ℕ) :
    cntUpTo x (u + 1) = cntUpTo x u + (rowW x u).length := by
  unfold cntUpTo; rw [List.range_succ]; simp

theorem cntUpTo_le (x : List ℕ) (u : ℕ) : cntUpTo x u ≤ u * nV x := by
  induction u with
  | zero => simp [cntUpTo]
  | succ u ih => rw [cntUpTo_succ, Nat.succ_mul]; have := length_rowW_le x u; omega

theorem length_pairs (x : List ℕ) : (pairs x).length = cntUpTo x (nV x) := by
  unfold pairs cntUpTo
  rw [List.length_flatMap]
  simp

/-- The pairs `[u', v']` with `u' < u`, flattened. -/
def emUpTo (x : List ℕ) (u : ℕ) : List ℕ :=
  (List.range u).flatMap fun u' => (rowW x u').flatMap fun v => [u', v]

/-- The adjacent `v' < v` of `u`, as pairs, flattened. -/
def emRow (x : List ℕ) (u v : ℕ) : List ℕ :=
  ((List.range v).filter (adjW x u)).flatMap fun v' => [u, v']

theorem emRow_succ (x : List ℕ) (u v : ℕ) :
    emRow x u (v + 1) = emRow x u v ++ if adjW x u v then [u, v] else [] := by
  unfold emRow
  rw [List.range_succ, List.filter_append]
  by_cases h : adjW x u v = true <;> simp [h]

theorem emUpTo_succ (x : List ℕ) (u : ℕ) :
    emUpTo x (u + 1) = emUpTo x u ++ emRow x u (nV x) := by
  unfold emUpTo emRow rowW; rw [List.range_succ]; simp

theorem flatten_flatMap' (f : ℕ → List (List ℕ)) :
    ∀ l : List ℕ, (l.flatMap f).flatten = l.flatMap fun a => (f a).flatten
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, List.flatten_append, flatten_flatMap' f l]

theorem flatten_pairs (x : List ℕ) : (pairs x).flatten = emUpTo x (nV x) := by
  unfold pairs emUpTo
  rw [flatten_flatMap']
  refine List.flatMap_congr fun u _ => ?_
  rw [List.flatMap_def]

/-! ### The counting pass -/

/-- The scalars the passes assign. -/
def passVars : List String := adjVars ++ ["g_M", "g_u", "g_v"]

/-- The invariant of the inner counting loop. -/
def CI (x : List ℕ) (u : ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" ≤ nV x ∧
    σ.vars "g_M" = cntUpTo x u + cntRow x u (σ.vars "g_v")

theorem CI.pre {x : List ℕ} {u : ℕ} (hu : u < nV x) {σ : Env} (h : CI x u σ)
    (hv : σ.vars "g_v" < nV x) : Ctx x σ ∧ σ.vars "g_u" < nV x ∧ σ.vars "g_v" < nV x :=
  ⟨h.1, by rw [h.2.1]; exact hu, hv⟩

set_option maxHeartbeats 1000000 in
theorem countBody_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u : ℕ}
    (hu : u < nV x) :
    Spec B (fun σ => CI x u σ ∧ σ.vars "g_v" < nV x) countBody
      (fun σ σ' => CI x u σ' ∧ σ'.vars "g_v" = σ.vars "g_v" + 1) (Kadj x + 20) := by
  have hlen := hx.len
  have hBl := hB.len
  have hnn : u * nV x + nV x ≤ nV x * nV x := by
    have := Nat.mul_le_mul_right (nV x) (show u + 1 ≤ nV x by omega); rw [Nat.succ_mul] at this
    exact this
  have hsq : nV x * nV x + 8 < B := by
    have : nV x * nV x ≤ (x.length + 2) * (x.length + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hcu := cntUpTo_le x u
  refine Spec.pre (P := fun σ => (CI x u σ ∧ σ.vars "g_v" < nV x) ∧
    σ.vars "g_M" + 1 < B ∧ σ.vars "g_v" + 1 < B) ?_ ?_
  · unfold countBody
    run_vcg [adjTest_spec hx hB]
    all_goals (try exact CI.pre hu ‹_› ‹_›)
    all_goals
      obtain ⟨⟨hca, hcn⟩, hu', hv, hM⟩ := ‹CI x u σ›
      obtain ⟨hf, ⟨hkv, hka, -⟩, -⟩ := ‹_ ∧ Keep adjVars σ _ ∧ _›
      have eM := hkv "g_M" (by decide)
      have ev := hkv "g_v" (by decide)
      have eu := hkv "g_u" (by decide)
      have en := hkv "g_n" (by decide)
      rw [hu'] at hf
      have hcr := cntRow_le x u (σ.vars "g_v")
      try simp only [CI, Ctx, Env.setVar]
      simp [hka, eM, ev, eu, en, hf, hca, hcn, hu', hM, cntRow_succ]
      try split
      all_goals try omega
  · rintro σ ⟨⟨hc, hu', hv, hM⟩, hlt⟩
    have := cntRow_le x u (σ.vars "g_v")
    exact ⟨⟨⟨hc, hu', hv, hM⟩, hlt⟩, by omega, by omega⟩

theorem sq_lt {x : List ℕ} {B : ℕ} (hx : Good x) (hB : Fits x B) : nV x * nV x + 8 < B := by
  have hlen := hx.len
  have hBl := hB.len
  have : nV x * nV x ≤ (x.length + 2) * (x.length + 2) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem n_lt {x : List ℕ} {B : ℕ} (hx : Good x) (hB : Fits x B) : nV x + 8 < B := by
  have hlen := hx.len
  have := hB.len_lt
  omega

theorem countRow_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u : ℕ}
    (hu : u < nV x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_M" = cntUpTo x u) countRow
      (fun _ σ' => Ctx x σ' ∧ σ'.vars "g_u" = u ∧ σ'.vars "g_M" = cntUpTo x (u + 1))
      ((Kadj x + 20 + 4) * nV x + 6) := by
  have hn := n_lt hx hB
  have hloop := Spec.forRangeZero (B := B) (c := countBody) "g_v" "g_n" (CI x u) (nV x)
    (Kadj x + 20) (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2) (countBody_spec hx hB hu)
  refine Spec.pre (Spec.post hloop ?_) ?_
  · rintro σ σ' - ⟨⟨hc, hu', -, hM⟩, hv⟩
    refine ⟨hc, hu', ?_⟩
    rw [hM, hv, cntRow_full, cntUpTo_succ]
  · rintro σ ⟨⟨ha, hn⟩, hu', hM⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [Env.setVar, ha, hn, hu', hM, cntRow]

theorem countRow_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" < nV x ∧ σ.vars "g_M" = cntUpTo x (σ.vars "g_u"))
      countRow
      (fun σ σ' => (Ctx x σ' ∧ σ'.vars "g_u" = σ.vars "g_u" ∧
        σ'.vars "g_M" = cntUpTo x (σ.vars "g_u" + 1)) ∧ Keep passVars σ σ' ∧ σ'.out = σ.out)
      ((Kadj x + 20 + 4) * nV x + 6) := by
  intro σ hσ
  have h := Spec.keepOut (countRow_value hx hB hσ.2.1) passVars ?_ ?_ ?_ ?_
  · exact h σ ⟨hσ.1, rfl, hσ.2.2⟩
  · intro y hy
    simp only [countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.wvars,
      passVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.warrs]
  · simp [countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.reads]
  · simp [countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.NoWrite]

/-- The cost of one turn of an outer loop. -/
def Krow (x : List ℕ) : ℕ := (Kadj x + 24) * nV x + 20

/-- The invariant of the outer counting loop. -/
def CO (x : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "g_u" ≤ nV x ∧ σ.vars "g_M" = cntUpTo x (σ.vars "g_u")

theorem CO.pre {x : List ℕ} {σ : Env} (h : CO x σ) (hu : σ.vars "g_u" < nV x) :
    Ctx x σ ∧ σ.vars "g_u" < nV x ∧ σ.vars "g_M" = cntUpTo x (σ.vars "g_u") :=
  ⟨h.1, hu, h.2.2⟩

set_option maxHeartbeats 1000000 in
theorem countOuter_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => CO x σ ∧ σ.vars "g_u" < nV x) (.seq countRow (bump "g_u"))
      (fun σ σ' => CO x σ' ∧ σ'.vars "g_u" = σ.vars "g_u" + 1) (Krow x) := by
  have hn := n_lt hx hB
  refine Spec.pre (P := fun σ => (CO x σ ∧ σ.vars "g_u" < nV x) ∧ σ.vars "g_u" + 1 < B) ?_ ?_
  · unfold Krow
    run_vcg [countRow_spec hx hB]
    all_goals (try exact CO.pre ‹_› ‹_›)
    all_goals
      obtain ⟨⟨hc, hu', hM⟩, ⟨hkv, hka, -⟩, -⟩ := ‹(Ctx x _ ∧ _ ∧ _) ∧ Keep passVars σ _ ∧ _›
      try simp only [CO, Ctx, Env.setVar]
      simp [hc.1, hc.2, hu', hM]
      all_goals try omega
  · rintro σ ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, by omega⟩

/-- The cost of a pass. -/
def Kpass (x : List ℕ) : ℕ := (Krow x + 4) * nV x + 8

theorem countPass_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ) countPass
      (fun _ σ' => Ctx x σ' ∧ σ'.vars "g_M" = (pairs x).length) (Kpass x) := by
  have hn := n_lt hx hB
  have hloop := Spec.forRangeZero (B := B) (c := .seq countRow (bump "g_u")) "g_u" "g_n" (CO x)
    (nV x) (Krow x) (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2) (countOuter_spec hx hB)
  have h0 : Spec B (fun σ => Ctx x σ) (.assign "g_M" (.lit 0))
      (fun σ σ' => σ' = σ.setVar "g_M" 0) (1 + (Expr.lit 0).size) :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by simp [Kpass, Expr.size]; omega)
  · rintro σ σ1 ⟨ha, hn⟩ rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [Env.setVar, ha, hn, cntUpTo]
  · rintro σ σ1 σ2 - - ⟨⟨hc, -, hM⟩, hu⟩
    rw [hu] at hM
    exact ⟨hc, by rw [hM, length_pairs]⟩

theorem countPass_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ) countPass
      (fun σ σ' => (Ctx x σ' ∧ σ'.vars "g_M" = (pairs x).length) ∧ Keep passVars σ σ' ∧
        σ'.out = σ.out) (Kpass x) := by
  refine Spec.keepOut (countPass_value hx hB) passVars ?_ ?_ ?_ ?_
  · intro y hy
    simp only [countPass, countLoop, countRow, countBody, adjTest, adjPrep, adjLoop, adjBody,
      adjStep, bump, Com.wvars, passVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [countPass, countLoop, countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep,
      bump, Com.warrs]
  · simp [countPass, countLoop, countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep,
      bump, Com.reads]
  · simp [countPass, countLoop, countRow, countBody, adjTest, adjPrep, adjLoop, adjBody, adjStep,
      bump, Com.NoWrite]

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass
