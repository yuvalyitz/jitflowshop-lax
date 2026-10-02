import Lax496464Proofs.Ram.F5QScale
import Lax496464Proofs.Ram.Q3Defs

/-!
# Theorem 5 (Profile Sweep): the Read-Off

`scanCom` finds the largest weight column `c ≤ W` that has a finite cell (one pass over the flat
table: `best := max best (i mod w1)` at every finite cell), and `outCom` writes
`k · (best − n)` if `k > 1`, else `best`.
-/

namespace Lax496464Proofs.Ram.F5QScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Q3Defs
open Lax496464Proofs.Ram.F5QFit (V)

def scanBody : Com :=
  .seq (.assign "u1" (.get "T" (V "i")))
    (.seq (.assign "u2" (.bin .div (V "i") (V "w1")))
      (.seq (.assign "u3" (.bin .sub (V "i") (.bin .mul (V "u2") (V "w1"))))
        (.seq (.ite (.lt (V "u1") (V "cinf"))
            (.ite (.lt (V "best") (V "u3")) (.assign "best" (V "u3")) .skip) .skip)
          (.assign "i" (.bin .add (V "i") (.lit 1))))))

def scanCom : Com :=
  .seq (.assign "best" (.lit 0))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) scanBody))

def outCom : Com :=
  .ite (.lt (.lit 1) (V "kk")) (.write (.bin .mul (V "kk") (.bin .sub (V "best") (V "n"))))
    (.write (V "best"))

/-- The scan's invariant: `best` bounds every finite column seen so far and is attained. -/
def SInv (N w1 INF : ℕ) (T : List ℕ) (σ : Env) : Prop :=
  σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "T" = T ∧
  σ.vars "i" ≤ N ∧
  (∀ idx < σ.vars "i", T.getD idx 0 < INF → idx % w1 ≤ σ.vars "best") ∧
  (σ.vars "best" = 0 ∨ ∃ idx < σ.vars "i", T.getD idx 0 < INF ∧ idx % w1 = σ.vars "best")

theorem mod_eq_sub (i w1 : ℕ) : i - i / w1 * w1 = i % w1 := by
  rw [Nat.mod_def, Nat.mul_comm w1 (i / w1)]

theorem scanBody_spec {B N w1 INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : 0 < w1)
    (hNB : N < B) (hw1B : w1 < B) (hTl : N ≤ T.length) (hTB : ∀ k < N, T.getD k 0 < B)
    (hINF : INF < B) :
    Spec B (fun σ => SInv N w1 INF T σ ∧ σ.vars "i" < N) scanBody
      (fun σ σ' => SInv N w1 INF T σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 60 := by
  intro σ ⟨⟨hN, hw, hc, hT, hi, hub, hatt⟩, hlt⟩
  have hiB : σ.vars "i" + 1 < B := by omega
  have hdm : σ.vars "i" / σ.vars "w1" * σ.vars "w1" ≤ σ.vars "i" := Nat.div_mul_le_self _ _
  have hdv : σ.vars "i" / σ.vars "w1" ≤ σ.vars "i" := Nat.div_le_self _ _
  have hTi : (σ.arrs "T").getD (σ.vars "i") 0 < B := by rw [hT]; exact hTB _ hlt
  have hTlen : σ.vars "i" < (σ.arrs "T").length := by rw [hT]; omega
  have hbestB : σ.vars "best" < B := by
    rcases hatt with h | ⟨idx, hidx, -, hbe⟩
    · omega
    · rw [← hbe]; exact lt_of_lt_of_le (Nat.mod_lt _ hw1) (by omega)
  have hmd : σ.vars "i" % σ.vars "w1" + σ.vars "i" / σ.vars "w1" * σ.vars "w1" = σ.vars "i" := by
    rw [Nat.mul_comm (σ.vars "i" / σ.vars "w1")]; exact Nat.mod_add_div _ _
  have hmw : σ.vars "i" % σ.vars "w1" = σ.vars "i" % w1 := by rw [hw]
  have hmodlt : σ.vars "i" % w1 < w1 := Nat.mod_lt _ hw1
  have hcell : (σ.arrs "T").getD (σ.vars "i") 0 = T.getD (σ.vars "i") 0 := by rw [hT]
  run_vcg
  all_goals simp only [SInv, Env.setVar] at *
  all_goals simp at *
  all_goals (try simp only [mod_eq_sub] at *)
  all_goals (try simp only [hmw] at *)
  all_goals first
    | omega
    | skip
  · -- finite, new best
    have hlt' : σ.vars "best" < σ.vars "i" % w1 := by omega
    have hfin : T[σ.vars "i"]?.getD 0 < INF := by omega
    refine ⟨hN, hw, hc, hT, by omega, ?_, ?_⟩
    · intro idx hidx hfi
      by_cases h : idx < σ.vars "i"
      · have := hub idx h hfi; omega
      · have : idx = σ.vars "i" := by omega
        rw [this]
    · right; exact ⟨σ.vars "i", le_rfl, hfin, rfl⟩
  · -- finite, not better
    have hle : σ.vars "i" % w1 ≤ σ.vars "best" := by omega
    refine ⟨hN, hw, hc, hT, by omega, ?_, ?_⟩
    · intro idx hidx hfi
      by_cases h : idx < σ.vars "i"
      · exact hub idx h hfi
      · have : idx = σ.vars "i" := by omega
        rw [this]; exact hle
    · rcases hatt with h | ⟨idx, hidx, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨idx, by omega, h1, h2⟩
  · -- not finite
    have hnf : INF ≤ T[σ.vars "i"]?.getD 0 := by omega
    refine ⟨hN, hw, hc, hT, by omega, ?_, ?_⟩
    · intro idx hidx hfi
      by_cases h : idx < σ.vars "i"
      · exact hub idx h hfi
      · have : idx = σ.vars "i" := by omega
        rw [this] at hfi; omega
    · rcases hatt with h | ⟨idx, hidx, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨idx, by omega, h1, h2⟩

/-- **The scan.** -/
theorem scanCom_spec {B N w1 INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : 0 < w1)
    (hNB : N < B) (hw1B : w1 < B) (hTl : N ≤ T.length) (hTB : ∀ k < N, T.getD k 0 < B)
    (hINF : INF < B) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "cinf" = INF ∧ σ.arrs "T" = T)
      scanCom
      (fun σ σ' => (∀ idx < N, T.getD idx 0 < INF → idx % w1 ≤ σ'.vars "best") ∧
        (σ'.vars "best" = 0 ∨ ∃ idx < N, T.getD idx 0 < INF ∧ idx % w1 = σ'.vars "best") ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "kk" = σ.vars "kk") (64 * N + 10) := by
  have hloop := Spec.forRangeZero (B := B) (c := scanBody) "i" "N" (SInv N w1 INF T) N 60 hNB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.1)
    (scanBody_spec T hB hw1 hNB hw1B hTl hTB hINF)
  refine Spec.of_exists fun σ ⟨hN, hw, hc, hT⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "best") (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar "best" 0 with hσ1
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ1, Env.setVar, hN]
    · simp [hσ1, Env.setVar, hw]
    · simp [hσ1, Env.setVar, hc]
    · simp [hσ1, Env.setVar, hT]
    · simp [hσ1, Env.setVar]
    · intro idx hidx; simp [hσ1, Env.setVar] at hidx
    · simp [hσ1, Env.setVar])
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, ?_⟩
  · simp only [Expr.size]; omega
  · obtain ⟨-, -, -, -, -, hub, hatt⟩ := hI
    rw [hi] at hub hatt
    have hfv1 := (r1.seq hr2).frame_var "n" (by decide)
    have hfv2 := (r1.seq hr2).frame_var "kk" (by decide)
    exact ⟨hub, hatt, hfv1, hfv2⟩

/-- **The output.** -/
theorem outCom_spec {B k b n : ℕ} (hB : 1 < B) (hk : k < B) (hb : b < B) (hn : n < B)
    (hkb : k * (b - n) < B) :
    Spec B (fun σ => σ.vars "kk" = k ∧ σ.vars "best" = b ∧ σ.vars "n" = n) outCom
      (fun σ σ' => σ'.out = σ.out ++ [if 1 < k then k * (b - n) else b]) 12 := by
  intro σ ⟨hk', hb', hn'⟩
  unfold outCom
  run_vcg
  all_goals simp [hk', hb', hn'] at *
  all_goals omega

end Lax496464Proofs.Ram.F5QScan
