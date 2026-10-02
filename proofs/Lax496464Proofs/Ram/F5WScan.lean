import Lax496464Proofs.Ram.F5QFit
import Lax496464Proofs.Ram.W3Sweep

/-!
# Theorem 5 (Endpoint Sweep): the Read-Off

The exact core leaves in `TB[0 … W]` the row of the endpoint sweep: `TB[c] < INF` iff weight `c`
is reached.  `scanW` finds the largest `c ≤ W` with `TB[c] < INF` (the last finite cell of a
left-to-right pass).
-/

namespace Lax496464Proofs.Ram.F5WScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.F5QFit (V getq_set)

def scanWBody : Com :=
  .seq (.ite (.lt (.get "TB" (V "i")) (V "cinf")) (.assign "best" (V "i")) .skip)
    (.assign "i" (.bin .add (V "i") (.lit 1)))

def scanW : Com :=
  .seq (.assign "best" (.lit 0))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "W1")) scanWBody))

/-- The scan's invariant: `best` bounds every finite cell seen so far and is attained. -/
def SWInv (W1 INF : ℕ) (T : List ℕ) (σ : Env) : Prop :=
  σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "TB" = T ∧ σ.vars "i" ≤ W1 ∧
  (∀ idx < σ.vars "i", T.getD idx 0 < INF → idx ≤ σ.vars "best") ∧
  (σ.vars "best" = 0 ∨ (σ.vars "best" < σ.vars "i" ∧ T.getD (σ.vars "best") 0 < INF))

theorem scanWBody_spec {B W1 INF : ℕ} (T : List ℕ) (hB : 1 < B)
    (hW1B : W1 < B) (hTl : W1 ≤ T.length) (hTB : ∀ k < W1, T.getD k 0 < B)
    (hINF : INF < B) :
    Spec B (fun σ => SWInv W1 INF T σ ∧ σ.vars "i" < W1) scanWBody
      (fun σ σ' => SWInv W1 INF T σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  intro σ ⟨⟨hW, hc, hT, hi, hub, hatt⟩, hlt⟩
  have hiB : σ.vars "i" + 1 < B := by omega
  have hTi : (σ.arrs "TB").getD (σ.vars "i") 0 < B := by rw [hT]; exact hTB _ hlt
  have hTlen : σ.vars "i" < (σ.arrs "TB").length := by rw [hT]; omega
  have hcell : (σ.arrs "TB").getD (σ.vars "i") 0 = T.getD (σ.vars "i") 0 := by rw [hT]
  run_vcg
  all_goals simp only [SWInv, Env.setVar] at *
  all_goals simp at *
  · have hfin : T[σ.vars "i"]?.getD 0 < INF := by omega
    exact ⟨hW, hc, hT, hlt, fun idx hidx _ => hidx, Or.inr hfin⟩
  · have hnf : INF ≤ T[σ.vars "i"]?.getD 0 := by omega
    refine ⟨hW, hc, hT, hlt, fun idx hidx hfi => ?_, ?_⟩
    · by_cases h : idx < σ.vars "i"
      · exact hub idx h hfi
      · have : idx = σ.vars "i" := by omega
        rw [this] at hfi; omega
    · rcases hatt with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h2⟩

/-- **The scan.** -/
theorem scanW_spec {B W1 INF : ℕ} (T : List ℕ) (hB : 1 < B)
    (hW1B : W1 < B) (hTl : W1 ≤ T.length) (hTB : ∀ k < W1, T.getD k 0 < B)
    (hINF : INF < B) :
    Spec B (fun σ => σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "TB" = T) scanW
      (fun σ σ' => (∀ idx < W1, T.getD idx 0 < INF → idx ≤ σ'.vars "best") ∧
        (σ'.vars "best" = 0 ∨ (σ'.vars "best" < W1 ∧ T.getD (σ'.vars "best") 0 < INF)) ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "kk" = σ.vars "kk") (34 * W1 + 10) := by
  have hloop := Spec.forRangeZero (B := B) (c := scanWBody) "i" "W1" (SWInv W1 INF T) W1 30 hW1B
    (fun _ h => h.2.2.2.1) (fun _ h => h.1)
    (scanWBody_spec T hB hW1B hTl hTB hINF)
  refine Spec.of_exists fun σ ⟨hW, hc, hT⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "best") (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar "best" 0 with hσ1
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ1, Env.setVar, hW]
    · simp [hσ1, Env.setVar, hc]
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
    exact ⟨hub, hatt, hfv1, hfv2⟩

end Lax496464Proofs.Ram.F5WScan
