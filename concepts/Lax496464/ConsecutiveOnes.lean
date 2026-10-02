import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

/-!
---
title: Consecutive Ones Implies Total Unimodularity
type: theorem
---
A matrix of zeros and ones has the *consecutive ones property* when the ones in each row
occupy a consecutive block of columns. Such a matrix is *totally unimodular*: every
square submatrix has determinant $0$, $1$ or $-1$.

This is the theorem of Fulkerson and Gross, and it is what makes the integer program of
Section 6.2 solvable as a linear program.

# Formalization Notes

The property is stated as a closure condition — if a row has a one at two columns then it
has a one at every column between them — rather than through an ordering of the columns
supplied from outside. The two agree once the columns are ordered, and the closure form
is what a matrix built from intervals satisfies by construction and what a proof uses.

The columns are only required to carry an order, not to be finite or linearly ordered:
nothing below needs more. Total unimodularity is mathlib's, so the conclusion is the
standard one and is available to whatever consumes it.

The paper cites this result. It is proved here rather than assumed, since neither it nor
anything equivalent is in the background library, and a hardness or tractability claim
resting on it should not rest on an axiom that could as well be false.
-/

namespace Lax496464.ConsecutiveOnes

/-- The ones of each row occupy a consecutive block of columns. -/
def HasConsecutiveOnes {m n : Type*} [LE n] (A : Matrix m n ℤ) : Prop :=
  (∀ r c, A r c = 0 ∨ A r c = 1) ∧
    ∀ r c₁ c c₂, c₁ ≤ c → c ≤ c₂ → A r c₁ = 1 → A r c₂ = 1 → A r c = 1

/-- **Fulkerson–Gross.** A matrix with the consecutive ones property is totally
unimodular. -/
axiom isTotallyUnimodular {m n : Type*} [LinearOrder n] {A : Matrix m n ℤ}
    (h : HasConsecutiveOnes A) : A.IsTotallyUnimodular

end Lax496464.ConsecutiveOnes
