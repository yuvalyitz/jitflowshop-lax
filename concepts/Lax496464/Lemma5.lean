import Lax496464.ConsecutiveOnes
import Lax496464.IntegerProgram

/-!
---
title: Lemma 5
type: theorem
---
On a proper instance the jobs alive at any one instant form a consecutive block of the
earliest-start-time order, so the constraint matrix of Section 6.2 has the consecutive
ones property: the first family of rows is a family of prefixes, and the second is a
family of blocks.

With the theorem of Fulkerson and Gross this makes the matrix totally unimodular, which
is what lets the integer program be solved as a linear program.

The correspondence the section asserts — that the feasible solutions of the program are
exactly the feasible sets — is stated here too. It holds on every instance with equal,
positive preprocessing times and nonnegative start times, proper or not.

# Formalization notes

Three statements: that the program describes the problem, that its matrix has the
consecutive ones property, and that the matrix is therefore totally unimodular.

The first is asserted in the paper and not proved there. It is the statement that turns a
program on paper into an algorithm for the shop, and both directions are needed: a
feasible set gives a feasible vector, and a feasible vector gives a feasible set.

Properness enters only in the second. What it buys is that the order by start time and
the order by due date agree, which is what makes a set of intervals containing a common
point an interval of the order.
-/

namespace Lax496464.Lemma5

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.ProperInstances
open Lax496464.ConsecutiveOnes Lax496464.IntegerProgram
open Matrix

variable (I : Instance)

/-- **The program is the problem.** With equal positive preprocessing times and
nonnegative start times, a set of jobs is feasible exactly when its indicator vector
satisfies both families of constraints. -/
axiom ilp_correct (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p) (hp0 : 0 < p)
    (hq : ∀ i : I.Job, 0 < I.q i) (hs : ∀ j : I.Job, 0 ≤ s j) (Z : Finset I.Job) :
    Feasible I Z ↔ ∀ r, (matrix I *ᵥ indicator I Z) r ≤ rhs I p r

/-- **The optimum is the optimum.** A `0/1` vector satisfying the constraints with
objective value `W` is exactly a feasible set of weight `W`. -/
axiom ilp_optimum (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p) (hp0 : 0 < p)
    (hq : ∀ i : I.Job, 0 < I.q i) (hs : ∀ j : I.Job, 0 ≤ s j) (W : ℕ) :
    (∃ x : I.Job → ℤ, (∀ i, x i = 0 ∨ x i = 1) ∧
        (∀ r, (matrix I *ᵥ x) r ≤ rhs I p r) ∧ ∑ i, (I.w i : ℤ) * x i = W) ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W

/-- **Lemma 5.** On a proper instance the constraint matrix has the consecutive ones
property. -/
axiom lemma5 (hest : EstOrdered I) (h : Proper I) : HasConsecutiveOnes (matrix I)

/-- The constraint matrix of a proper instance is totally unimodular. -/
axiom matrix_isTotallyUnimodular (hest : EstOrdered I) (h : Proper I) :
    (matrix I).IsTotallyUnimodular

end Lax496464.Lemma5
