import Lax496464Proofs.WHierarchy.MccNP.Ram.PolyProg

/-!
# The Program Computes the Reduction

On every word `x`, the program run on `|x| :: x` prints `reduce x` within `Kfull x` steps, with all
values below `Bd x`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.PolyRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Ram Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum
open Lax496464Proofs.WHierarchy.MccNP.Validate Lax496464Proofs.WHierarchy.MccNP.Ram.PolyProg
open Lax496464.WH_F2_MccConstruction (reduce)

/-- The cost bound of the body, valid or not. -/
def Kb (x : List ℕ) : ℕ := 1200 * (x.length + 1) ^ 3

/-- The cost bound of the program. -/
def Kfull (x : List ℕ) : ℕ := (12 * x.length + 10) + (Kval x + (1 + 3 + Kb x))

theorem Kbody_le_Kb {x : List ℕ} (hx : Shape.Valid x) : Kbody x ≤ Kb x := by
  unfold Kbody Kb bodyC
  have h := k_le hx
  have h2 : (Shape.kOf x + 1) ^ 2 ≤ (x.length + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : 1200 * (Shape.kOf x + 1) ^ 2 * (x.length + 1) ≤ 1200 * (x.length + 1) ^ 2 * (x.length + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
  calc _ ≤ _ := this
    _ = 1200 * (x.length + 1) ^ 3 := by ring

/-- The state after reading and validating. -/
def Mid (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.out = [] ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧
    (σ.vars "ok" = 1 ↔ Shape.Valid x)

theorem ok_iff {x : List ℕ} {σ : Env} (hB3 : 1 < Bd x) (hok : σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) :
    Cond.evalB (Bd x) (.eq (.var "ok") (.lit 1)) σ = some (decide (σ.vars "ok" = 1)) := by
  have : σ.vars "ok" < Bd x := by rcases hok with h | h <;> omega
  simp [Cond.evalB, Expr.evalB, fit, this, hB3]
  by_cases h : σ.vars "ok" = 1 <;> simp [h]

theorem main_spec (x : List ℕ) :
    Spec (Bd x) (fun σ => σ.inp = x.length :: x ∧ σ.out = [] ∧ (σ.arrs "a").length = x.length)
      cmd (fun _ σ' => σ'.out = reduce x) (Kfull x) := by
  have hy : ∀ v ∈ x, v < Bd x := fun v hv => mem_lt_Bd hv
  have hL := len_lt_Bd x
  have hB := bval_lt_Bd x
  have hB3 : 1 < Bd x := by have := len_lt_Bd x; omega
  have h1 := Lax391470Proofs.ReadAll.readAll_spec (B := Bd x) (y := x) hy hL
  have h2 := validate_spec_list (B := Bd x) (x := x) hy hB
  have h2' := Spec.pre h2 (P' := fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.out = [])
    (fun σ h => ⟨h.1, h.2.1⟩)
  have h3 : Spec (Bd x) (Mid x) (.ite (.eq (.var "ok") (.lit 1)) body .skip)
      (fun _ σ' => σ'.out = reduce x) (1 + 3 + Kb x) := by
    refine Spec.ite ?_ ?_ ?_
    · rintro σ ⟨-, -, hok, -⟩
      exact ⟨_, ok_iff hB3 hok⟩
    · rintro σ ⟨⟨ha, hout, hok, hiff⟩, he⟩
      rw [ok_iff hB3 hok] at he
      have h1' : σ.vars "ok" = 1 := by simpa using he
      have hv : Shape.Valid x := hiff.mp h1'
      obtain ⟨σ', hr, hq⟩ := body_spec hv (B := Bd x) (Bbody_lt_Bd hv) σ ha
      refine ⟨σ', hr.mono (Kbody_le_Kb hv), ?_⟩
      show σ'.out = reduce x
      rw [hq.1, hout, Shape.reduce_valid hv]; simp
    · rintro σ ⟨⟨ha, hout, hok, hiff⟩, he⟩
      rw [ok_iff hB3 hok] at he
      have h1' : ¬ σ.vars "ok" = 1 := by simpa using he
      have hv : ¬ Shape.Valid x := fun h => h1' (hiff.mpr h)
      have hKb : 0 < Kb x := by unfold Kb; positivity
      refine ⟨σ, Run.skip.mono (by omega), ?_⟩
      show σ.out = reduce x
      rw [hout, Shape.reduce_invalid hv]
  have h23 : Spec (Bd x) (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.out = [])
      (.seq validate (.ite (.eq (.var "ok") (.lit 1)) body .skip))
      (fun _ σ' => σ'.out = reduce x) (Kval x + (1 + 3 + Kb x)) := by
    refine Spec.seq h2' h3 ?_ (fun _ _ _ _ _ h => h)
    rintro σ σ' ⟨ha, -, hout⟩ ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩
    exact ⟨by rw [hq3, ha], by rw [hq4, hout], hq2, hq1⟩
  refine Spec.mono (Spec.seq h1 h23 ?_ (fun _ _ _ _ _ h => h)) le_rfl
  rintro σ σ' - ⟨hq1, hq2, hq3, hq4⟩
  exact ⟨hq2, hq1, hq3⟩

end Lax496464Proofs.WHierarchy.MccNP.Ram.PolyRun
