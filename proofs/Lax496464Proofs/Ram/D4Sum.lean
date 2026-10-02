import Lax496464Proofs.Ram.D2Core

/-!
# Corollary 2's Machine: the Total Preprocessing Time

`sumCom` leaves `P = Σ_k PS[k]` in the scalar `"R"` (the caller then adds one to get the block
width); `O(n)`.
-/

namespace Lax496464Proofs.Ram.D4Sum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)

def sumBody : Com :=
  .seq (.assign "R" (.bin .add (V "R") (.get "PS" (V "sI")))) (bump "sI")

def sumLoop : Com := .seq (.assign "sI" (.lit 0)) (.while (.lt (V "sI") (V "n")) sumBody)

def sumCom : Com := .seq (.assign "R" (.lit 0)) sumLoop

/-- The invariant of the loop. -/
def SInv (n : ℕ) (PSl : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "PS" = PSl ∧ σ.vars "sI" ≤ n ∧
    σ.vars "R" = (PSl.take (σ.vars "sI")).sum

theorem take_sum_le (l : List ℕ) (k : ℕ) : (l.take k).sum ≤ l.sum := by
  have := List.sum_take_add_sum_drop l k
  omega

theorem sumBody_spec {B : ℕ} (hB : 2 < B) (n : ℕ) (PSl : List ℕ) (hlen : PSl.length = n) (hnB : n < B)
    (hsum : PSl.sum < B) (hval : ∀ v ∈ PSl, v < B) :
    Spec B (fun σ => SInv n PSl σ ∧ σ.vars "sI" < n) sumBody
      (fun σ σ' => SInv n PSl σ' ∧ σ'.vars "sI" = σ.vars "sI" + 1) 20 := by
  refine Spec.of_exists fun σ ⟨⟨hn, hPS, hle, hR⟩, hlt⟩ => ?_
  have hk : σ.vars "sI" < PSl.length := by omega
  have hsucc := List.sum_take_succ PSl (σ.vars "sI") hk
  have hle1 := take_sum_le PSl (σ.vars "sI" + 1)
  have hkB : PSl[σ.vars "sI"] < B := hval _ (List.getElem_mem hk)
  have hgetD : (σ.arrs "PS").getD (σ.vars "sI") 0 = PSl[σ.vars "sI"] := by
    rw [hPS, List.getD_eq_getElem _ _ hk]
  run_vcg
  all_goals (simp_all [SInv])


theorem sumCom_core {B : ℕ} (hB : 2 < B) (n : ℕ) (PSl : List ℕ) (hlen : PSl.length = n)
    (hnB : n < B) (hsum : PSl.sum < B) (hval : ∀ v ∈ PSl, v < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "PS" = PSl) sumCom
      (fun _ σ' => σ'.vars "R" = PSl.sum) (24 * n + 20) := by
  have hbody := sumBody_spec hB n PSl hlen hnB hsum hval
  have hloop := Spec.forRangeZero (B := B) (c := sumBody) "sI" "n" (SInv n PSl) n 20 hnB
    (fun σ h => h.2.2.1) (fun σ h => h.1) hbody
  refine Spec.of_exists fun σ ⟨hn, hPS⟩ => ?_
  have r1 := Run.assign (B := B) (σ := σ) (x := "R") (e := .lit 0) (v := 0) (evalB_lit (by omega))
  obtain ⟨σ2, hr2, ⟨-, -, -, hR⟩, hsI⟩ := hloop.run (σ := σ.setVar "R" 0)
    ⟨by simp [hn], by simp [hPS], by simp, by simp⟩
  refine ⟨σ2, _, (r1.seq hr2).mono (by simp only [Expr.size]; omega), le_rfl, ?_⟩
  rw [hR, hsI, List.take_of_length_le (by omega)]

theorem sumCom_wvars : ∀ y ∈ sumCom.wvars, y ∈ ["R", "sI"] := by decide
theorem sumCom_warrs : sumCom.warrs = [] := by decide

theorem sumCom_spec {B : ℕ} (hB : 2 < B) (n : ℕ) (PSl : List ℕ) (hlen : PSl.length = n)
    (hnB : n < B) (hsum : PSl.sum < B) (hval : ∀ v ∈ PSl, v < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "PS" = PSl) sumCom
      (fun σ σ' => σ'.vars "R" = PSl.sum ∧ (∀ v, v ∉ ["R", "sI"] → σ'.vars v = σ.vars v) ∧
        σ'.arrs = σ.arrs) (24 * n + 20) := by
  refine ((sumCom_core hB n PSl hlen hnB hsum hval).frame).post ?_
  rintro σ σ' - ⟨hR, hfv, hfa, -, -⟩
  refine ⟨hR, fun v hv => hfv v (fun h => hv (sumCom_wvars v h)), ?_⟩
  funext a
  exact hfa a (by rw [sumCom_warrs]; simp)

end Lax496464Proofs.Ram.D4Sum
