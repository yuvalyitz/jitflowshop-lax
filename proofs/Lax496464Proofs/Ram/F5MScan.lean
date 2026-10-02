import Lax496464Proofs.Ram.F5WPre
import Lax496464Proofs.Ram.D2Final

/-!
# Theorem 5 (Table of Section 3): the Read-Off

The exact core leaves in `TAB[code·(W+1) + r]`, `r ≤ W`, the entry of the first `m` indices at weight
`r`: non-zero iff weight `r` is reached.  `scanM` finds the largest `r ≤ W` with a non-zero entry
(the last non-zero cell of a left-to-right pass over the column).
-/

namespace Lax496464Proofs.Ram.F5MScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.F5QFit (V)

def scanMBody : Com :=
  .seq (.ite (.lt (.lit 0) (.get "TAB" (.bin .add (V "sb") (V "i")))) (.assign "best" (V "i"))
      .skip)
    (.assign "i" (.bin .add (V "i") (.lit 1)))

def scanMLoop : Com :=
  .seq (.assign "best" (.lit 0))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "R")) scanMBody))

def scanM : Com :=
  .seq (.assign "sb" (.bin .mul (V "zk") (V "R"))) scanMLoop

/-- The scan's invariant: `best` bounds every non-zero cell seen so far and is attained. -/
def SMInv (W1 base : ℕ) (T : List ℕ) (σ : Env) : Prop :=
  σ.vars "R" = W1 ∧ σ.vars "sb" = base ∧ σ.arrs "TAB" = T ∧ σ.vars "i" ≤ W1 ∧
  (∀ idx < σ.vars "i", 0 < T.getD (base + idx) 0 → idx ≤ σ.vars "best") ∧
  (σ.vars "best" = 0 ∨ (σ.vars "best" < σ.vars "i" ∧ 0 < T.getD (base + σ.vars "best") 0))

theorem scanMBody_spec {B W1 base : ℕ} (T : List ℕ) (hB : 1 < B)
    (_hW1B : W1 < B) (hbB : base + W1 < B) (hTl : base + W1 ≤ T.length)
    (hTB : ∀ k < W1, T.getD (base + k) 0 < B) :
    Spec B (fun σ => SMInv W1 base T σ ∧ σ.vars "i" < W1) scanMBody
      (fun σ σ' => SMInv W1 base T σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  intro σ ⟨⟨hW, hs, hT, hi, hub, hatt⟩, hlt⟩
  have hiB : σ.vars "i" + 1 < B := by omega
  have hTi : (σ.arrs "TAB").getD (base + σ.vars "i") 0 < B := by rw [hT]; exact hTB _ hlt
  have hTlen : base + σ.vars "i" < (σ.arrs "TAB").length := by rw [hT]; omega
  have hcell : (σ.arrs "TAB").getD (base + σ.vars "i") 0 = T.getD (base + σ.vars "i") 0 := by
    rw [hT]
  have hsB : σ.vars "sb" + σ.vars "i" < B := by omega
  run_vcg
  all_goals (try simp only [SMInv, Env.setVar] at *)
  all_goals (try simp at *)
  all_goals (try simp only [hs] at *)
  all_goals first
    | omega
    | skip
  · have hfin : 0 < T[base + σ.vars "i"]?.getD 0 := by omega
    exact ⟨hW, hs, hT, hlt, fun idx hidx _ => hidx, Or.inr hfin⟩
  · have hnf : T[base + σ.vars "i"]?.getD 0 = 0 := by omega
    refine ⟨hW, hs, hT, hlt, fun idx hidx hfi => ?_, ?_⟩
    · by_cases h : idx < σ.vars "i"
      · exact hub idx h hfi
      · have : idx = σ.vars "i" := by omega
        rw [this] at hfi; omega
    · rcases hatt with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h2⟩

/-- The loop. -/
theorem scanMLoop_spec {B W1 base : ℕ} (T : List ℕ) (hB : 1 < B)
    (hW1B : W1 < B) (hbB : base + W1 < B) (hTl : base + W1 ≤ T.length)
    (hTB : ∀ k < W1, T.getD (base + k) 0 < B) :
    Spec B (fun σ => σ.vars "R" = W1 ∧ σ.vars "sb" = base ∧ σ.arrs "TAB" = T) scanMLoop
      (fun σ σ' => (∀ idx < W1, 0 < T.getD (base + idx) 0 → idx ≤ σ'.vars "best") ∧
        (σ'.vars "best" = 0 ∨ (σ'.vars "best" < W1 ∧ 0 < T.getD (base + σ'.vars "best") 0)) ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "kk" = σ.vars "kk" ∧ σ'.vars "sb" = σ.vars "sb")
      (34 * W1 + 10) := by
  have hloop := Spec.forRangeZero (B := B) (c := scanMBody) "i" "R" (SMInv W1 base T) W1 30 hW1B
    (fun _ h => h.2.2.2.1) (fun _ h => h.1)
    (scanMBody_spec T hB hW1B hbB hTl hTB)
  refine Spec.of_exists fun σ ⟨hW, hs, hT⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "best") (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar "best" 0 with hσ1
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ1, Env.setVar, hW]
    · simp [hσ1, Env.setVar, hs]
    · simp [hσ1, Env.setVar, hT]
    · simp [hσ1, Env.setVar]
    · intro idx hidx; simp [hσ1, Env.setVar] at hidx
    · simp [hσ1, Env.setVar])
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, ?_⟩
  · simp only [Expr.size]; omega
  · obtain ⟨-, -, -, -, hub, hatt⟩ := hI
    rw [hi] at hub hatt
    have hfv1 := (r1.seq hr2).frame_var "n" (by decide)
    have hfv2 := (r1.seq hr2).frame_var "kk" (by decide)
    have hfv3 := (r1.seq hr2).frame_var "sb" (by decide)
    exact ⟨hub, hatt, hfv1, hfv2, hfv3⟩

/-- **The scan.** -/
theorem scanM_spec {B W1 code : ℕ} (T : List ℕ) (hB : 1 < B) (hcB : code < B)
    (hW1B : W1 < B) (hmulB : code * W1 < B) (hbB : code * W1 + W1 < B)
    (hTl : code * W1 + W1 ≤ T.length) (hTB : ∀ k < W1, T.getD (code * W1 + k) 0 < B) :
    Spec B (fun σ => σ.vars "zk" = code ∧ σ.vars "R" = W1 ∧ σ.arrs "TAB" = T) scanM
      (fun σ σ' => (∀ idx < W1, 0 < T.getD (code * W1 + idx) 0 → idx ≤ σ'.vars "best") ∧
        (σ'.vars "best" = 0 ∨
          (σ'.vars "best" < W1 ∧ 0 < T.getD (code * W1 + σ'.vars "best") 0)) ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "kk" = σ.vars "kk") (34 * W1 + 20) := by
  have hloop := scanMLoop_spec (B := B) (W1 := W1) (base := code * W1) T hB hW1B hbB hTl hTB
  refine Spec.of_exists fun σ ⟨hzk, hW, hT⟩ => ?_
  have hvk : (V "zk").evalB B σ = some code := hzk ▸ evalB_var (by rw [hzk]; omega)
  have hvR : (V "R").evalB B σ = some W1 := hW ▸ evalB_var (by rw [hW]; omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "sb") (e := .bin .mul (V "zk") (V "R"))
    (v := code * W1) (evalB_bin hvk hvR hmulB)
  set σ1 : Env := σ.setVar "sb" (code * W1) with hσ1
  obtain ⟨σ2, hr2, hub, hatt, hn, hkk, -⟩ := hloop.run (σ := σ1)
    ⟨by simp [hσ1, Env.setVar, hW], by simp [hσ1, Env.setVar], by simp [hσ1, Env.setVar, hT]⟩
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, hub, hatt, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · rw [hn]; simp [hσ1, Env.setVar]
  · rw [hkk]; simp [hσ1, Env.setVar]

end Lax496464Proofs.Ram.F5MScan
