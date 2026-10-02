import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fin.Tuple.Sort

namespace Lax496464Proofs

/-!
# The Consecutive Ones Property

Definition 1 of the paper: a `0/1` matrix *has the consecutive ones property* when each row
is of the form `(0, …, 0, 1, …, 1, 0, …, 0)`. Stated order-theoretically — the ones in a row
form an interval of columns — so that it applies to any linearly ordered column type and
needs no enumeration.

This file is deliberately free of scheduling: it is the one notion
`Assumptions.lean`'s literature axiom (consecutive ones ⟹ total unimodularity) is phrased
in, and `Section6_ILP.lean` is where the paper's matrix is shown to satisfy it.
-/

namespace Matrix

open _root_.Matrix

/-- **Definition 1.** Every entry is `0` or `1`, and in each row the ones are consecutive. -/
def HasConsecutiveOnes {m n : Type*} [LE n] (A : Matrix m n ℤ) : Prop :=
  (∀ r c, A r c = 0 ∨ A r c = 1) ∧
    ∀ r c₁ c c₂, c₁ ≤ c → c ≤ c₂ → A r c₁ = 1 → A r c₂ = 1 → A r c = 1

/-! ## Interval matrices have determinant `0` or `±1`

The classical argument. Rows are half-open intervals `[a i, b i)` of columns. If no row
covers column `0`, that column is zero. Otherwise take the covering row `r` whose interval
is shortest and subtract it from every other covering row: each becomes `[b r, b i)`, still an
interval, and column `0` now has a single one. Expanding along column `0` leaves an interval
matrix one size smaller. All the subtractions are done at once, as multiplication by
`1 + col (−c) · row eᵣ`, whose determinant is `1 − c r = 1`. -/

/-- A square `0/1` matrix whose row `i` is one exactly on columns `[a i, b i)`. -/
def intervalMat {k : ℕ} (a b : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  of fun i j => if a i ≤ (j : ℕ) ∧ (j : ℕ) < b i then 1 else 0

private lemma one_add_col_row_mul_apply {k : ℕ} (u : Fin k → ℤ) (r : Fin k)
    (A : Matrix (Fin k) (Fin k) ℤ) (i j : Fin k) :
    (((1 : Matrix (Fin k) (Fin k) ℤ) + replicateCol Unit u *
        replicateRow Unit (Pi.single r (1 : ℤ))) * A) i j
      = A i j + u i * A r j := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_assoc]
  congr 1
  simp [Matrix.mul_apply, replicateCol, replicateRow, Pi.single_apply]

theorem det_intervalMat : ∀ (k : ℕ) (a b : Fin k → ℕ),
    (intervalMat a b).det = 0 ∨ (intervalMat a b).det = 1 ∨ (intervalMat a b).det = -1
  | 0, _, _ => Or.inr (Or.inl det_isEmpty)
  | k + 1, a, b => by
    classical
    by_cases hS : ∃ i, a i = 0 ∧ 0 < b i
    · -- the pivot: a row through column `0` with the shortest interval
      have hne : (Finset.univ.filter fun i => a i = 0 ∧ 0 < b i).Nonempty := by
        obtain ⟨i, hi⟩ := hS
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      obtain ⟨r, hrmem, hrmin⟩ := Finset.exists_min_image _ b hne
      obtain ⟨hra, hrb⟩ := (Finset.mem_filter.mp hrmem).2
      have hmin : ∀ i, a i = 0 ∧ 0 < b i → b r ≤ b i := fun i hi =>
        hrmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      set P : Fin (k + 1) → Prop := fun i => (a i = 0 ∧ 0 < b i) ∧ i ≠ r with hP
      set c : Fin (k + 1) → ℤ := fun i => if P i then 1 else 0 with hc
      set a' : Fin (k + 1) → ℕ := fun i => if P i then b r else a i with ha'
      -- the row operations, as one determinant-one multiplication
      set E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
        1 + replicateCol Unit (-c) * replicateRow Unit (Pi.single r (1 : ℤ)) with hEdef
      have hE : E.det = 1 := by
        rw [hEdef, det_one_add_replicateCol_mul_replicateRow]
        have hcr : c r = 0 := by simp [hc, hP]
        simp [dotProduct, Pi.single_apply, hcr]
      have hEA : E * intervalMat a b = intervalMat a' b := by
        ext i j
        rw [hEdef, one_add_col_row_mul_apply]
        simp only [intervalMat, of_apply, hc, ha', Pi.neg_apply]
        by_cases hPi : P i
        · have hbi := hmin i hPi.1
          simp only [if_pos hPi, hPi.1.1, hra]
          split_ifs <;> omega
        · simp [if_neg hPi]
      have hdet : (intervalMat a b).det = (intervalMat a' b).det := by
        rw [← hEA, det_mul, hE, one_mul]
      -- expand along column `0`: only the pivot row survives
      have hcol : ∀ i, i ≠ r → intervalMat a' b i 0 = 0 := by
        intro i hir
        have h0 : ((0 : Fin (k + 1)) : ℕ) = 0 := rfl
        simp only [intervalMat, of_apply, ha']
        by_cases hPi : P i
        · rw [if_pos hPi]
          simp only [ite_eq_right_iff]
          intro hh
          omega
        · rw [if_neg hPi]
          simp only [ite_eq_right_iff]
          intro hh
          exact absurd ⟨⟨by omega, hh.2⟩, hir⟩ hPi
      have hpiv : intervalMat a' b r 0 = 1 := by
        have : ¬ P r := fun h => h.2 rfl
        simp only [intervalMat, of_apply, ha', if_neg this, Fin.val_zero]
        split_ifs with hh
        · rfl
        · exact absurd ⟨by omega, hrb⟩ hh
      have hminor : (intervalMat a' b).submatrix r.succAbove Fin.succ
          = intervalMat (fun i => a' (r.succAbove i) - 1) (fun i => b (r.succAbove i) - 1) := by
        ext i j
        simp only [submatrix_apply, intervalMat, of_apply, Fin.val_succ]
        split_ifs <;> omega
      rw [hdet, det_succ_column_zero, Finset.sum_eq_single r (fun i _ hir => by
          rw [hcol i hir]; ring) (fun h => absurd (Finset.mem_univ r) h),
        hpiv, hminor, mul_one]
      rcases det_intervalMat k (fun i => a' (r.succAbove i) - 1)
          (fun i => b (r.succAbove i) - 1) with h | h | h <;> rw [h] <;>
        rcases neg_one_pow_eq_or ℤ (r : ℕ) with h' | h' <;> simp [h']
    · -- column `0` is zero
      left
      refine det_eq_zero_of_column_eq_zero 0 fun i => ?_
      have h0 : ((0 : Fin (k + 1)) : ℕ) = 0 := rfl
      simp only [intervalMat, of_apply, ite_eq_right_iff]
      intro hh
      exact absurd ⟨i, by omega, hh.2⟩ hS

/-! ## Consecutive ones implies total unimodularity -/

/-- **Consecutive ones ⟹ totally unimodular** (Fulkerson and Gross, 1965). Sort the chosen
columns — which changes the determinant only by a sign — and each row of the submatrix
becomes an interval, so `det_intervalMat` applies. -/
theorem HasConsecutiveOnes.isTotallyUnimodular {m n : Type*} [LinearOrder n]
    {A : Matrix m n ℤ} (hA : HasConsecutiveOnes A) : A.IsTotallyUnimodular := by
  classical
  intro k f g _ hg
  set σ := Tuple.sort g with hσ
  have hsmono : StrictMono (g ∘ σ) :=
    (Tuple.monotone_sort g).strictMono_of_injective (hg.comp σ.injective)
  -- each row of the column-sorted submatrix is an interval
  have hrow : ∀ i : Fin k, ∃ a b : ℕ, ∀ c : Fin k,
      A (f i) (g (σ c)) = if a ≤ (c : ℕ) ∧ (c : ℕ) < b then 1 else 0 := by
    intro i
    by_cases hne : (Finset.univ.filter fun c : Fin k => A (f i) (g (σ c)) = 1).Nonempty
    · set T := Finset.univ.filter fun c : Fin k => A (f i) (g (σ c)) = 1 with hT
      refine ⟨(T.min' hne : ℕ), (T.max' hne : ℕ) + 1, fun c => ?_⟩
      have hlo := (Finset.mem_filter.mp (T.min'_mem hne)).2
      have hhi := (Finset.mem_filter.mp (T.max'_mem hne)).2
      split_ifs with hh
      · refine hA.2 (f i) _ _ _ (hsmono.monotone (Fin.le_def.mpr hh.1))
          (hsmono.monotone (Fin.le_def.mpr (by omega))) hlo hhi
      · rcases hA.1 (f i) (g (σ c)) with h0 | h1
        · exact h0
        · exfalso
          have hcT : c ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
          have := T.min'_le c hcT
          have := T.le_max' c hcT
          exact hh ⟨Fin.le_def.mp ‹_›, by have := Fin.le_def.mp ‹T.max' hne ≥ c›; omega⟩
    · refine ⟨0, 0, fun c => ?_⟩
      rw [if_neg (by omega)]
      rcases hA.1 (f i) (g (σ c)) with h0 | h1
      · exact h0
      · exact absurd ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩ hne
  choose a b hab using hrow
  have hsorted : A.submatrix f (g ∘ σ) = intervalMat a b := by
    ext i c
    simp only [submatrix_apply, Function.comp_apply, intervalMat, of_apply]
    exact hab i c
  have hD := det_intervalMat k a b
  have hperm := det_permute' σ (A.submatrix f g)
  rw [show (A.submatrix f g).submatrix id σ = intervalMat a b from hsorted] at hperm
  have key : (A.submatrix f g).det = 0 ∨ (A.submatrix f g).det = 1 ∨
      (A.submatrix f g).det = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
      simp only [hs, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul,
        neg_mul] at hperm <;> rw [hperm] at hD <;> omega
  rcases key with h | h | h <;> rw [h]
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨-1, rfl⟩

end Matrix

end Lax496464Proofs
