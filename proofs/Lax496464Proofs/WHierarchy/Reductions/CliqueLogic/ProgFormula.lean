import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath

/-! # Writing the code of `clique_k`

`formulaCom_spec`: the program writes the code of `clique_k` for `k = g_k` — the quantifier block,
then the right-nested chain of the conjuncts `¬ x_i = x_j ∧ E x_i x_j`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgFormula

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath

/-! ### The quantifier block -/

/-- The invariant of the quantifier loop. -/
def QI (k : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "g_k" = k ∧ σ.vars "g_i" ≤ k ∧ σ.out = out0 ++ quantEnc (σ.vars "g_i")

theorem quantEnc_succ (i : ℕ) : quantEnc (i + 1) = quantEnc i ++ [6, i] := by
  simp [quantEnc, List.range_succ]

set_option maxHeartbeats 1000000 in
theorem quantBody_spec {B k : ℕ} (hk : k + 8 < B) (out0 : List ℕ) :
    Spec B (fun σ => QI k out0 σ ∧ σ.vars "g_i" < k) quantBody
      (fun σ σ' => QI k out0 σ' ∧ σ'.vars "g_i" = σ.vars "g_i" + 1) 10 := by
  refine Spec.pre (P := fun σ => (QI k out0 σ ∧ σ.vars "g_i" < k) ∧ σ.vars "g_i" + 1 < B ∧ 6 < B)
    ?_ ?_
  · unfold quantBody
    run_vcg
    all_goals
      obtain ⟨hk', hi, ho⟩ := ‹QI k out0 σ›
      simp only [QI, Env.setVar]
      simp [hk', ho, quantEnc_succ]
      try omega
  · rintro σ ⟨⟨hk', hi, ho⟩, hlt⟩
    exact ⟨⟨⟨hk', hi, ho⟩, hlt⟩, by omega, by omega⟩

theorem quantLoop_spec {B k : ℕ} (hk : k + 8 < B) (out0 : List ℕ) :
    Spec B (fun σ => σ.vars "g_k" = k ∧ σ.out = out0) quantLoop
      (fun _ σ' => σ'.vars "g_k" = k ∧ σ'.out = out0 ++ quantEnc k) ((10 + 4) * k + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := quantBody) "g_i" "g_k" (QI k out0) k 10
    (by omega) (fun σ h => h.2.1) (fun σ h => h.1) (quantBody_spec hk out0)
  refine Spec.pre (Spec.post hloop ?_) ?_
  · rintro σ σ' - ⟨⟨hk', -, ho⟩, hi⟩
    exact ⟨hk', by rw [ho, hi]⟩
  · rintro σ ⟨hk', ho⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [Env.setVar, hk', ho, quantEnc]

/-! ### The pair items -/

/-- The items `i, j'` for `j' < j`, as the scan writes them. -/
def rowEnc (i j : ℕ) : List ℕ :=
  (List.range j).flatMap fun j' => if i < j' then itemEnc i j' else []

theorem rowEnc_succ (i j : ℕ) :
    rowEnc i (j + 1) = rowEnc i j ++ if i < j then itemEnc i j else [] := by
  simp [rowEnc, List.range_succ]

theorem itemCom_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "g_i" < B ∧ σ.vars "g_j" < B ∧ 4 < B) itemCom
      (fun σ σ' => σ'.out = σ.out ++ itemEnc (σ.vars "g_i") (σ.vars "g_j") ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 30 := by
  simp only [itemCom, writeExprs]
  run_vcg
  all_goals simp_all [itemEnc]

theorem itemIf_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "g_i" < B ∧ σ.vars "g_j" < B ∧ 4 < B) itemIf
      (fun σ σ' => σ'.out = σ.out ++
          (if σ.vars "g_i" < σ.vars "g_j" then itemEnc (σ.vars "g_i") (σ.vars "g_j") else []) ∧
        σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) 34 := by
  unfold itemIf
  run_vcg [itemCom_spec (B := B)]
  all_goals simp_all

/-- The invariant of the inner pair loop. -/
def PI (k i : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "g_k" = k ∧ σ.vars "g_i" = i ∧ σ.vars "g_j" ≤ k ∧ σ.out = out0 ++ rowEnc i (σ.vars "g_j")

set_option maxHeartbeats 1000000 in
theorem pairBody_spec {B k i : ℕ} (hk : k + 8 < B) (hi : i < k) (out0 : List ℕ) :
    Spec B (fun σ => PI k i out0 σ ∧ σ.vars "g_j" < k) (.seq itemIf (bump "g_j"))
      (fun σ σ' => PI k i out0 σ' ∧ σ'.vars "g_j" = σ.vars "g_j" + 1) 40 := by
  refine Spec.pre (P := fun σ => (PI k i out0 σ ∧ σ.vars "g_j" < k) ∧ σ.vars "g_i" < B ∧
    σ.vars "g_j" + 1 < B ∧ 4 < B) ?_ ?_
  · run_vcg [itemIf_spec (B := B)]
    all_goals
      obtain ⟨hk', hi', hj, ho⟩ := ‹PI k i out0 σ›
      try simp only [PI, Env.setVar] at *
      try simp_all [rowEnc_succ]
      all_goals try omega
  · rintro σ ⟨⟨hk', hi', hj, ho⟩, hlt⟩
    exact ⟨⟨⟨hk', hi', hj, ho⟩, hlt⟩, by omega, by omega, by omega⟩

theorem pairRow_spec {B k : ℕ} (hk : k + 8 < B) :
    Spec B (fun σ => σ.vars "g_k" = k ∧ σ.vars "g_i" < k) pairRow
      (fun σ σ' => σ'.vars "g_k" = k ∧ σ'.vars "g_i" = σ.vars "g_i" ∧
        σ'.out = σ.out ++ rowEnc (σ.vars "g_i") k) ((40 + 4) * k + 6) := by
  intro σ ⟨hk', hi⟩
  have hloop := Spec.forRangeZero (B := B) (c := .seq itemIf (bump "g_j")) "g_j" "g_k"
    (PI k (σ.vars "g_i") σ.out) k 40 (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1)
    (pairBody_spec hk hi σ.out)
  obtain ⟨σ', hr, ⟨hk'', hi', -, ho⟩, hj⟩ := hloop σ (by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hk', rowEnc])
  exact ⟨σ', hr, hk'', hi', by rw [ho, hj]⟩

/-- The invariant of the outer pair loop. -/
def PO (k : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "g_k" = k ∧ σ.vars "g_i" ≤ k ∧
    σ.out = out0 ++ (List.range (σ.vars "g_i")).flatMap fun i => rowEnc i k

set_option maxHeartbeats 1000000 in
theorem pairOuter_spec {B k : ℕ} (hk : k + 8 < B) (out0 : List ℕ) :
    Spec B (fun σ => PO k out0 σ ∧ σ.vars "g_i" < k) (.seq pairRow (bump "g_i"))
      (fun σ σ' => PO k out0 σ' ∧ σ'.vars "g_i" = σ.vars "g_i" + 1) ((40 + 4) * k + 10) := by
  refine Spec.pre (P := fun σ => (PO k out0 σ ∧ σ.vars "g_i" < k) ∧ σ.vars "g_i" + 1 < B) ?_ ?_
  · run_vcg [pairRow_spec hk]
    all_goals (try exact ⟨(‹PO k out0 σ›).1, ‹_›⟩)
    all_goals
      obtain ⟨hk', hi, ho⟩ := ‹PO k out0 σ›
      try simp only [PO, Env.setVar] at *
      try simp_all [List.range_succ]
  · rintro σ ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, by omega⟩

theorem pairLoop_spec {B k : ℕ} (hk : k + 8 < B) (out0 : List ℕ) :
    Spec B (fun σ => σ.vars "g_k" = k ∧ σ.out = out0) pairLoop
      (fun _ σ' => σ'.vars "g_k" = k ∧ σ'.out = out0 ++ pairsEnc k)
      (((40 + 4) * k + 10 + 4) * k + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := .seq pairRow (bump "g_i")) "g_i" "g_k"
    (PO k out0) k ((40 + 4) * k + 10) (by omega) (fun σ h => h.2.1) (fun σ h => h.1)
    (pairOuter_spec hk out0)
  refine Spec.pre (Spec.post hloop ?_) ?_
  · rintro σ σ' - ⟨⟨hk', -, ho⟩, hi⟩
    exact ⟨hk', by rw [ho, hi]; rfl⟩
  · rintro σ ⟨hk', ho⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [Env.setVar, hk', ho]

/-! ### The formula -/

/-- The cost of writing `clique_k`. -/
def Kform (k : ℕ) : ℕ := 60 * (k + 1) * (k + 1) + 40

/-- The scalars `formulaCom` assigns. -/
def formVars : List String := ["g_i", "g_j"]

set_option maxHeartbeats 1000000 in
theorem formulaCom_value {B k : ℕ} (hk : k + 8 < B) :
    Spec B (fun σ => σ.vars "g_k" = k) formulaCom
      (fun σ σ' => σ'.out = σ.out ++ (cliqueSent k).encode) (Kform k) := by
  intro σ hσ
  have h : Spec B (fun τ => τ.vars "g_k" = k ∧ τ.out = σ.out ∧ 2 < B) formulaCom
      (fun _ σ' => σ'.out = σ.out ++ (cliqueSent k).encode)
      ((10 + 4) * k + 6 + ((((40 + 4) * k + 10 + 4) * k + 6) + 12)) := by
    unfold formulaCom
    run_vcg [quantLoop_spec hk σ.out, pairLoop_spec hk (σ.out ++ quantEnc k)]
    all_goals (try simp_all [encode_cliqueSent])
  obtain ⟨σ', hr, hq⟩ := h σ ⟨hσ, rfl, by omega⟩
  refine ⟨σ', hr.mono ?_, hq⟩
  unfold Kform
  nlinarith

theorem formulaCom_spec {B k : ℕ} (hk : k + 8 < B) :
    Spec B (fun σ => σ.vars "g_k" = k) formulaCom
      (fun σ σ' => σ'.out = σ.out ++ (cliqueSent k).encode ∧ Keep formVars σ σ') (Kform k) := by
  refine Spec.keep (formulaCom_value hk) formVars ?_ ?_ ?_
  · intro y hy
    simp only [formulaCom, quantLoop, quantBody, pairLoop, pairRow, itemIf, itemCom, writeExprs,
      bump, Com.wvars, formVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [formulaCom, quantLoop, quantBody, pairLoop, pairRow, itemIf, itemCom, writeExprs, bump,
      Com.warrs]
  · simp [formulaCom, quantLoop, quantBody, pairLoop, pairRow, itemIf, itemCom, writeExprs, bump,
      Com.reads]

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgFormula
