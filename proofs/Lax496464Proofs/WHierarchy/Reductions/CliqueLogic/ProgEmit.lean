import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass

/-! # The emitting pass and the word of the graph structure

`emitPass_spec`: the adjacent ordered pairs `u, v` in lexicographic order; `graphCom_value`: the
word of the graph structure, `1, 2, n, M` followed by those pairs. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass

theorem emitIf_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "g_u" < B ∧ σ.vars "g_v" < B ∧ σ.vars "g_f" < B ∧ 1 < B) emitIf
      (fun σ σ' => σ'.out = σ.out ++
          (if σ.vars "g_f" = 1 then [σ.vars "g_u", σ.vars "g_v"] else []) ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 10 := by
  unfold emitIf
  run_vcg
  all_goals simp_all

/-- The invariant of the inner emitting loop. -/
def EI (x : List ℕ) (u : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" ≤ nV x ∧ σ.out = out0 ++ emRow x u (σ.vars "g_v")

theorem EI.pre {x : List ℕ} {u : ℕ} (hu : u < nV x) {out0 : List ℕ} {σ : Env}
    (h : EI x u out0 σ) (hv : σ.vars "g_v" < nV x) :
    Ctx x σ ∧ σ.vars "g_u" < nV x ∧ σ.vars "g_v" < nV x :=
  ⟨h.1, by rw [h.2.1]; exact hu, hv⟩

set_option maxHeartbeats 1000000 in
theorem emitBody_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u : ℕ}
    (hu : u < nV x) (out0 : List ℕ) :
    Spec B (fun σ => EI x u out0 σ ∧ σ.vars "g_v" < nV x) emitBody
      (fun σ σ' => EI x u out0 σ' ∧ σ'.vars "g_v" = σ.vars "g_v" + 1) (Kadj x + 20) := by
  have hn := n_lt hx hB
  refine Spec.pre (P := fun σ => (EI x u out0 σ ∧ σ.vars "g_v" < nV x) ∧
    σ.vars "g_u" < B ∧ σ.vars "g_v" + 1 < B ∧ 1 < B) ?_ ?_
  · unfold emitBody
    run_vcg [adjTest_spec hx hB, emitIf_spec (B := B)]
    all_goals (try exact EI.pre hu ‹_› ‹_›)
    all_goals
      obtain ⟨⟨hca, hcn⟩, hu', hv, ho⟩ := ‹EI x u out0 σ›
      obtain ⟨hf, ⟨hkv, hka, -⟩, hout⟩ := ‹_ ∧ Keep adjVars σ _ ∧ _›
      have eu := hkv "g_u" (by decide)
      have ev := hkv "g_v" (by decide)
      have en := hkv "g_n" (by decide)
      rw [hu'] at hf
      try simp only [EI, Ctx, Env.setVar] at *
      try simp_all [emRow_succ]
      all_goals try (split <;> omega)
      all_goals try omega
  · rintro σ ⟨⟨hc, hu', hv, ho⟩, hlt⟩
    exact ⟨⟨⟨hc, hu', hv, ho⟩, hlt⟩, by omega, by omega, by omega⟩

theorem emitRow_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u : ℕ}
    (hu : u < nV x) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.out = out0) emitRow
      (fun _ σ' => Ctx x σ' ∧ σ'.vars "g_u" = u ∧ σ'.out = out0 ++ emRow x u (nV x))
      ((Kadj x + 20 + 4) * nV x + 6) := by
  have hn := n_lt hx hB
  have hloop := Spec.forRangeZero (B := B) (c := emitBody) "g_v" "g_n" (EI x u out0) (nV x)
    (Kadj x + 20) (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2)
    (emitBody_spec hx hB hu out0)
  refine Spec.pre (Spec.post hloop ?_) ?_
  · rintro σ σ' - ⟨⟨hc, hu', -, ho⟩, hv⟩
    exact ⟨hc, hu', by rw [ho, hv]⟩
  · rintro σ ⟨⟨ha, hn⟩, hu', ho⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [Env.setVar, ha, hn, hu', ho, emRow]

theorem emitRow_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" < nV x) emitRow
      (fun σ σ' => (Ctx x σ' ∧ σ'.vars "g_u" = σ.vars "g_u" ∧
        σ'.out = σ.out ++ emRow x (σ.vars "g_u") (nV x)) ∧ Keep passVars σ σ')
      ((Kadj x + 20 + 4) * nV x + 6) := by
  intro σ hσ
  have h := Spec.keep (emitRow_value hx hB hσ.2 σ.out) passVars ?_ ?_ ?_
  · exact h σ ⟨hσ.1, rfl, rfl⟩
  · intro y hy
    simp only [emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump,
      Com.wvars, passVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.warrs]
  · simp [emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.reads]

/-- The invariant of the outer emitting loop. -/
def EO (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "g_u" ≤ nV x ∧ σ.out = out0 ++ emUpTo x (σ.vars "g_u")

theorem EO.pre {x : List ℕ} {out0 : List ℕ} {σ : Env} (h : EO x out0 σ)
    (hu : σ.vars "g_u" < nV x) : Ctx x σ ∧ σ.vars "g_u" < nV x := ⟨h.1, hu⟩

set_option maxHeartbeats 1000000 in
theorem emitOuter_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) (out0 : List ℕ) :
    Spec B (fun σ => EO x out0 σ ∧ σ.vars "g_u" < nV x) (.seq emitRow (bump "g_u"))
      (fun σ σ' => EO x out0 σ' ∧ σ'.vars "g_u" = σ.vars "g_u" + 1) (Krow x) := by
  have hn := n_lt hx hB
  refine Spec.pre (P := fun σ => (EO x out0 σ ∧ σ.vars "g_u" < nV x) ∧ σ.vars "g_u" + 1 < B)
    ?_ ?_
  · unfold Krow
    run_vcg [emitRow_spec hx hB]
    all_goals (try exact EO.pre ‹_› ‹_›)
    all_goals
      obtain ⟨⟨hc, hu', ho'⟩, -⟩ := ‹(Ctx x _ ∧ _ ∧ _) ∧ Keep passVars σ _›
      obtain ⟨-, -, ho⟩ := ‹EO x out0 σ›
      try simp only [EO, Ctx, Env.setVar]
      simp [hc.1, hc.2, hu', ho', ho, emUpTo_succ]
      all_goals try omega
  · rintro σ ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, by omega⟩

theorem emitPass_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x σ ∧ σ.out = out0) emitPass
      (fun _ σ' => Ctx x σ' ∧ σ'.out = out0 ++ (pairs x).flatten) (Kpass x) := by
  have hn := n_lt hx hB
  have hloop := Spec.forRangeZero (B := B) (c := .seq emitRow (bump "g_u")) "g_u" "g_n"
    (EO x out0) (nV x) (Krow x) (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2)
    (emitOuter_spec hx hB out0)
  refine Spec.mono (Spec.pre (Spec.post hloop ?_) ?_) (by unfold Kpass; omega)
  · rintro σ σ' - ⟨⟨hc, -, ho⟩, hu⟩
    exact ⟨hc, by rw [ho, hu, flatten_pairs]⟩
  · rintro σ ⟨⟨ha, hn⟩, ho⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [Env.setVar, ha, hn, ho, emUpTo]

theorem emitPass_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ) emitPass
      (fun σ σ' => (Ctx x σ' ∧ σ'.out = σ.out ++ (pairs x).flatten) ∧ Keep passVars σ σ')
      (Kpass x) := by
  intro σ hσ
  have h := Spec.keep (emitPass_value hx hB σ.out) passVars ?_ ?_ ?_
  · exact h σ ⟨hσ, rfl⟩
  · intro y hy
    simp only [emitPass, emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep,
      bump, Com.wvars, passVars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [emitPass, emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump,
      Com.warrs]
  · simp [emitPass, emitRow, emitBody, emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, bump,
      Com.reads]

/-! ### The word of the graph structure -/

/-- The cost of writing the word of the graph structure. -/
def Kgraph (x : List ℕ) : ℕ := 2 * Kpass x + 20

theorem length_pairs_lt {x : List ℕ} {B : ℕ} (hx : Good x) (hB : Fits x B) :
    (pairs x).length < B := by
  have := length_pairs_le x
  have := sq_lt hx hB
  omega

set_option maxHeartbeats 1000000 in
theorem graphCom_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ) graphCom
      (fun σ σ' => σ'.out = σ.out ++ graphWord x ∧ Keep passVars σ σ') (Kgraph x) := by
  have hn := n_lt hx hB
  have hM := length_pairs_lt hx hB
  have hK : Spec B (fun σ => Ctx x σ ∧ 2 < B ∧ σ.vars "g_n" < B) graphCom
      (fun σ σ' => σ'.out = σ.out ++ graphWord x ∧ Keep passVars σ σ') (Kgraph x) := by
    unfold graphCom Kgraph
    run_vcg [countPass_spec hx hB, emitPass_spec hx hB]
    all_goals (try exact ‹Ctx x σ›)
    all_goals (try exact (‹(Ctx x _ ∧ _) ∧ Keep passVars _ _ ∧ _›).1.1)
    all_goals
      obtain ⟨⟨hc1, hM1⟩, hk1, ho1⟩ := ‹(Ctx x _ ∧ _ = (pairs x).length) ∧ Keep passVars _ _ ∧ _›
      try obtain ⟨⟨hc2, ho2⟩, hk2⟩ := ‹(Ctx x _ ∧ _ = _ ++ (pairs x).flatten) ∧ Keep passVars _ _›
      try simp_all [graphWord_eq]
    all_goals
      rename_i h1 h2
      exact ⟨(‹Ctx x σ›).2, Keep.trans h1 h2⟩
  intro σ hσ
  exact hK σ ⟨hσ, by omega, by rw [hσ.2]; omega⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit
