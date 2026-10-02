import Lax496464Proofs.Ram.D2Core

/-!
# Theorem 2's Program, Top Level

`prog2 = sortSetup3 ; if n < 1 then answer(W = 0) else if m < 1 then answer(W = 0) else
core2 ; finish`.  `finish` reads the entry of the column at the threshold and writes the bit.
-/

namespace Lax496464Proofs.Ram.D2Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D2Core
open Lax496464Proofs.Ram.W3Front2 (sortSetup3)

/-- **`finish`**: the answer is the entry of the first `m` indices at weight `W`. -/
def finishCom : Com :=
  .seq (.assign "ans" (.get "TAB" (.bin .add (.bin .mul (V "zk") (V "R")) (V "W"))))
    (.ite (.eq (V "ans") (.lit 0)) (.write (.lit 0)) (.write (.lit 1)))

theorem finishCom_spec {B : ℕ} (hB : 2 < B) (code W : ℕ) (T : List ℕ) (out : List ℕ)
    (hidx : code * (W + 1) + W < T.length) (hval : T.getD (code * (W + 1) + W) 0 < B)
    (hbig : code * (W + 1) + W < B) (hcodeB : code < B) (hRB : W + 1 < B) (hWB : W < B)
    (hmulB : code * (W + 1) < B) :
    Spec B (fun σ => σ.vars "zk" = code ∧ σ.vars "R" = W + 1 ∧ σ.vars "W" = W ∧
        σ.arrs "TAB" = T ∧ σ.out = out) finishCom
      (fun _ σ' => σ'.out = out ++ [if T.getD (code * (W + 1) + W) 0 = 0 then 0 else 1]) 20 := by
  refine Spec.of_exists fun σ ⟨hzk, hR, hW, hT, hout⟩ => ?_
  have hvk : (V "zk").evalB B σ = some code := hzk ▸ evalB_var (by rw [hzk]; omega)
  have hvR : (V "R").evalB B σ = some (W + 1) := hR ▸ evalB_var (by rw [hR]; omega)
  have hvW : (V "W").evalB B σ = some W := hW ▸ evalB_var (by rw [hW]; omega)
  have hg := RunStep.eval_get B σ "TAB" (.bin .add (.bin .mul (V "zk") (V "R")) (V "W"))
    (code * (W + 1) + W)
    (evalB_bin (evalB_bin hvk hvR hmulB) hvW hbig) (by rw [hT]; exact hidx) (by rw [hT]; exact hval)
  rw [hT] at hg
  have r1 := Run.assign (B := B) (σ := σ) (x := "ans")
    (e := .get "TAB" (.bin .add (.bin .mul (V "zk") (V "R")) (V "W")))
    (v := T.getD (code * (W + 1) + W) 0) hg
  set σ1 : Env := σ.setVar "ans" (T.getD (code * (W + 1) + W) 0) with hσ1
  clear_value σ1
  have hva : (V "ans").evalB B σ1 = some (T.getD (code * (W + 1) + W) 0) := by
    have : σ1.vars "ans" = T.getD (code * (W + 1) + W) 0 := by simp [hσ1]
    exact this ▸ evalB_var (by rw [this]; exact hval)
  have hcond := evalB_condEq hva (evalB_lit (show 0 < B by omega))
  by_cases h0 : T.getD (code * (W + 1) + W) 0 = 0
  · have hc : (Cond.eq (V "ans") (Expr.lit 0)).evalB B σ1 = some true := by
      rw [hcond, h0]; rfl
    have r2 := Run.write (B := B) (σ := σ1) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [0] }, _, (r1.seq (Run.ite_true hc r2)).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · show σ1.out ++ [0] = _
      rw [if_pos h0]; simp [hσ1, hout]
  · have hc : (Cond.eq (V "ans") (Expr.lit 0)).evalB B σ1 = some false := by
      rw [hcond, beq_false_of_ne h0]
    have r2 := Run.write (B := B) (σ := σ1) (e := .lit 1) (v := 1) (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [1] }, _, (r1.seq (Run.ite_false hc r2)).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · show σ1.out ++ [1] = _
      rw [if_neg h0]; simp [hσ1, hout]

/-- The answer when there is no job or no machine: the empty set is the only feasible set. -/
def writeW : Com := .ite (.eq (V "W") (.lit 0)) (.write (.lit 1)) (.write (.lit 0))

theorem writeW_spec {B : ℕ} (hB : 2 < B) (W : ℕ) (out : List ℕ) (hW : W < B) :
    Spec B (fun σ => σ.vars "W" = W ∧ σ.out = out) writeW
      (fun _ σ' => σ'.out = out ++ [if W = 0 then 1 else 0]) 10 := by
  refine Spec.of_exists fun σ ⟨hWv, hout⟩ => ?_
  have hvW : (V "W").evalB B σ = some W := hWv ▸ evalB_var (by rw [hWv]; omega)
  have hcond := evalB_condEq hvW (evalB_lit (show 0 < B by omega))
  by_cases h0 : W = 0
  · have hc : (Cond.eq (V "W") (Expr.lit 0)).evalB B σ = some true := by rw [hcond, h0]; rfl
    have r2 := Run.write (B := B) (σ := σ) (e := .lit 1) (v := 1) (evalB_lit (by omega))
    refine ⟨{ σ with out := σ.out ++ [1] }, _, (Run.ite_true hc r2).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · simp [hout, h0]
  · have hc : (Cond.eq (V "W") (Expr.lit 0)).evalB B σ = some false := by rw [hcond]; simp [h0]
    have r2 := Run.write (B := B) (σ := σ) (e := .lit 0) (v := 0) (evalB_lit (by omega))
    refine ⟨{ σ with out := σ.out ++ [0] }, _, (Run.ite_false hc r2).mono ?_, le_rfl, ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · simp [hout, h0]

/-- **The whole program.** -/
def prog2 : Com :=
  .seq sortSetup3
    (.ite (.lt (V "n") (.lit 1)) writeW
      (.ite (.lt (V "m") (.lit 1)) writeW (.seq core2 finishCom)))

end Lax496464Proofs.Ram.D2Prog
