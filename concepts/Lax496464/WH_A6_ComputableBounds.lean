import Mathlib.Computability.Partrec
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
---
title: Computable Bounds
type: theorem
---
The time factor and the parameter bound of an fpt-reduction must be computable. The bounds that
occur in practice are built from constants and the parameter by sums, products, powers and
exponentials, and all of them are computable. Every computable $f\colon\mathbb N\to\mathbb N$ is
bounded by the computable nondecreasing function $k \mapsto \sum_{i \le k} f(i)$, which is what
allows bounds to be composed.

# Formalization Notes

Computability is Mathlib's `Computable`. Together with `Computable.const`, `Computable.id` and
`Computable.comp`, these statements show a bound such as $(k+1)^2$ or $2^k \cdot k$ computable by
combining them.
-/

namespace Lax496464.WH_A6_ComputableBounds

/-- Sums of computable functions are computable. -/
axiom computable_add {f g : ℕ → ℕ} :
    Computable f → Computable g → Computable fun k => f k + g k

/-- Products of computable functions are computable. -/
axiom computable_mul {f g : ℕ → ℕ} :
    Computable f → Computable g → Computable fun k => f k * g k

/-- Fixed powers of computable functions are computable. -/
axiom computable_pow {f : ℕ → ℕ} (e : ℕ) : Computable f → Computable fun k => f k ^ e

/-- Exponentials `b ^ f(k)` of computable functions are computable. -/
axiom computable_exp (b : ℕ) {f : ℕ → ℕ} : Computable f → Computable fun k => b ^ f k

/-- Polynomials with natural coefficients are computable. -/
axiom computable_polynomial (p : Polynomial ℕ) : Computable fun k => p.eval k

/-- Every computable function is bounded by a computable nondecreasing function. -/
axiom exists_monotone_bound {f : ℕ → ℕ} :
    Computable f → ∃ g : ℕ → ℕ, Computable g ∧ Monotone g ∧ ∀ k, f k ≤ g k

end Lax496464.WH_A6_ComputableBounds
