import Lax496464Proofs.Ram.D4Core
import Lax496464Proofs.Ram.D2Prog

/-!
# Corollary 2's program, top level

`prog4 = sortSetup3 ; if n < 1 then answer(W = 0) else if m < 1 then answer(W = 0) else
core4 ; finish`.  `finish` compares the entry of row `0` of the first `m` indices' block with `W`.
-/

namespace Lax496464Proofs.Ram.D4Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D4Core
open Lax496464Proofs.Ram.D2Prog (writeW writeW_spec)
open Lax496464Proofs.Ram.W3Front2 (sortSetup3)

/-- **`finish`**: the answer is whether the entry of the first `m` indices at row `0` is `W`. -/
def finishCom4 : Com :=
  .seq (.assign "ans" (.get "TAB" (.bin .mul (V "zk") (V "R"))))
    (.ite (.eq (V "ans") (V "W")) (.write (.lit 1)) (.write (.lit 0)))

theorem finishCom4_spec {B : ℕ} (hB : 2 < B) (code R W : ℕ) (T : List ℕ) (out : List ℕ)
    (hidx : code * (R + 1) < T.length) (hval : T.getD (code * (R + 1)) 0 ≤ W)
    (hcodeB : code < B) (hRB : R + 1 < B) (hWB : W < B) (hmulB : code * (R + 1) < B) :
    Spec B (fun σ => σ.vars "zk" = code ∧ σ.vars "R" = R + 1 ∧ σ.vars "W" = W ∧
        σ.arrs "TAB" = T ∧ σ.out = out) finishCom4
      (fun _ σ' => σ'.out = out ++ [if T.getD (code * (R + 1)) 0 = W then 1 else 0]) 20 := by
  refine Spec.of_exists fun σ ⟨hzk, hR, hW, hT, hout⟩ => ?_
  have hvk : (V "zk").evalB B σ = some code := hzk ▸ evalB_var (by rw [hzk]; omega)
  have hvR : (V "R").evalB B σ = some (R + 1) := hR ▸ evalB_var (by rw [hR]; omega)
  have hg := RunStep.eval_get B σ "TAB" (.bin .mul (V "zk") (V "R"))
    (code * (R + 1))
    (evalB_bin hvk hvR hmulB) (by rw [hT]; exact hidx) (by rw [hT]; omega)
  rw [hT] at hg
  have r1 := Run.assign (B := B) (σ := σ) (x := "ans")
    (e := .get "TAB" (.bin .mul (V "zk") (V "R")))
    (v := T.getD (code * (R + 1)) 0) hg
  set σ1 : Env := σ.setVar "ans" (T.getD (code * (R + 1)) 0) with hσ1
  clear_value σ1
  have hva : (V "ans").evalB B σ1 = some (T.getD (code * (R + 1)) 0) := by
    have : σ1.vars "ans" = T.getD (code * (R + 1)) 0 := by simp [hσ1]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hvW : (V "W").evalB B σ1 = some W := by
    have : σ1.vars "W" = W := by simp [hσ1, hW]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hcond := evalB_condEq hva hvW
  by_cases h0 : T.getD (code * (R + 1)) 0 = W
  · have hc : (Cond.eq (V "ans") (V "W")).evalB B σ1 = some true := by
      rw [hcond, h0]; simp
    have r2 := Run.write (B := B) (σ := σ1) (e := .lit 1) (v := 1) (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [1] }, _, (r1.seq (Run.ite_true hc r2)).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · show σ1.out ++ [1] = _
      rw [if_pos h0]; simp [hσ1, hout]
  · have hc : (Cond.eq (V "ans") (V "W")).evalB B σ1 = some false := by
      rw [hcond, beq_false_of_ne h0]
    have r2 := Run.write (B := B) (σ := σ1) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [0] }, _, (r1.seq (Run.ite_false hc r2)).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · show σ1.out ++ [0] = _
      rw [if_neg h0]; simp [hσ1, hout]

/-- **The whole program.** -/
def prog4 : Com :=
  .seq sortSetup3
    (.ite (.lt (V "n") (.lit 1)) writeW
      (.ite (.lt (V "m") (.lit 1)) writeW (.seq core4 finishCom4)))

end Lax496464Proofs.Ram.D4Prog
