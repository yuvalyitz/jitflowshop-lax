import Lax496464.WH_A5_Bridges
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! On all words, polynomial time in the sense of `WH_A1_FptTime` is the archive's `RamPolytime`: a
bound `c · (n + 1)^d` is a polynomial, and every polynomial with natural coefficients is below
`p(1) · (n + 1)^deg p`. -/

namespace Lax496464Proofs.WHierarchy.Machine.UnivIff

open Polynomial Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax496464.WH_A1_FptTime

theorem eval_le (p : Polynomial ℕ) (n : ℕ) : p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [one_pow, mul_one]
  refine Nat.mul_le_mul_left _ ?_
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n + 1) ^ p.natDegree := Nat.pow_le_pow_right (by omega) hi'

theorem eval_le' (p : Polynomial ℕ) (n c d : ℕ) (hc : p.eval 1 ≤ c) (hd : p.natDegree ≤ d) :
    p.eval n ≤ c * (n + 1) ^ d :=
  (eval_le p n).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd))

theorem fits_mono {a b : ℕ} {y : List ℕ} (h : FitsInWords a y) (hab : a ≤ b) :
    FitsInWords b y := fun v hv =>
  lt_of_lt_of_le (h v hv) (Nat.pow_le_pow_right (by norm_num) hab)

/--
---
conclusion: Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff
---
-/
theorem polyTimeOn_univ_iff (F : List ℕ → List ℕ) : PolyTimeOn Set.univ F ↔ RamPolytime F := by
  constructor
  · rintro ⟨p, c, d, h⟩
    refine ⟨p, C c * (X + 1) ^ d, C c * (X + 1) ^ d, fun x => ?_⟩
    have hev : (C c * (X + 1) ^ d : Polynomial ℕ).eval (bitSize x) = c * (bitSize x + 1) ^ d := by
      simp
    rw [hev]
    exact h x (Set.mem_univ x)
  · rintro ⟨p, wb, tb, h⟩
    refine ⟨p, wb.eval 1 + tb.eval 1, wb.natDegree + tb.natDegree, fun x _ => ?_⟩
    have hw := eval_le' wb (bitSize x) (wb.eval 1 + tb.eval 1) (wb.natDegree + tb.natDegree)
      (by omega) (by omega)
    have ht := eval_le' tb (bitSize x) (wb.eval 1 + tb.eval 1) (wb.natDegree + tb.natDegree)
      (by omega) (by omega)
    obtain ⟨hfit, hrun⟩ := h x
    refine ⟨fits_mono hfit hw, fun w hw' => ?_⟩
    obtain ⟨t, htb, hr⟩ := hrun w (hw.trans hw')
    exact ⟨t, htb.trans ht, hr⟩

end Lax496464Proofs.WHierarchy.Machine.UnivIff
