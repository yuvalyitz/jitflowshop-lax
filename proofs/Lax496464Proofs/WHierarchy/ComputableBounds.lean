import Lax496464.WH_A6_ComputableBounds
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Computability of the arithmetic that bounds are written with. -/

namespace Lax496464Proofs.WHierarchy.ComputableBounds

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.computable_add
---
-/
theorem computable_add {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun k => f k + g k :=
  Primrec.nat_add.to_comp.comp hf hg

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.computable_mul
---
-/
theorem computable_mul {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun k => f k * g k :=
  Primrec.nat_mul.to_comp.comp hf hg

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.computable_pow
---
-/
theorem computable_pow {f : ℕ → ℕ} (e : ℕ) (hf : Computable f) :
    Computable fun k => f k ^ e := by
  induction e with
  | zero => simpa using (Computable.const 1 : Computable fun _ : ℕ => 1)
  | succ e ih => simpa [pow_succ] using computable_mul ih hf

/-- `n ↦ b ^ n` is primitive recursive. -/
theorem primrec_pow_left (b : ℕ) : Primrec fun n : ℕ => b ^ n := by
  have h : Primrec (Nat.rec (motive := fun _ => ℕ) 1 fun _ acc => acc * b) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const b))
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp [pow_succ, ← ih]

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.computable_exp
---
-/
theorem computable_exp (b : ℕ) {f : ℕ → ℕ} (hf : Computable f) :
    Computable fun k => b ^ f k :=
  (primrec_pow_left b).to_comp.comp hf

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.computable_polynomial
---
-/
theorem computable_polynomial (p : Polynomial ℕ) : Computable fun k => p.eval k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using computable_add hp hq
  | monomial n a =>
    simpa [Polynomial.eval_monomial] using
      computable_mul (Computable.const a) (computable_pow n Computable.id)

/-- The partial sums `∑_{i < n} f i`, by recursion. -/
def partialSums (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun y s => s + f y) n

/--
---
conclusion: Lax496464.WH_A6_ComputableBounds.exists_monotone_bound
---
-/
theorem exists_monotone_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ g : ℕ → ℕ, Computable g ∧ Monotone g ∧ ∀ k, f k ≤ g k := by
  have hS : Computable (partialSums f) := by
    have := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (0 : ℕ))
      (h := fun _ (p : ℕ × ℕ) => p.2 + f p.1) Computable.id (Computable.const 0)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (hf.comp (Computable.fst.comp Computable.snd))).to₂
    exact this
  refine ⟨fun k => partialSums f (k + 1), hS.comp (Primrec.succ.to_comp), ?_, fun k => ?_⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    show partialSums f (n + 1) ≤ partialSums f (n + 1) + f (n + 1)
    omega
  · show f k ≤ partialSums f k + f k
    omega

end Lax496464Proofs.WHierarchy.ComputableBounds
