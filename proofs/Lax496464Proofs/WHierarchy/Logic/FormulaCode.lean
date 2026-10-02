import Lax496464.WH_B2_FirstOrder

/-! The prefix code of formulas is prefix-free: a word that begins with the code of a formula
determines the formula and the rest of the word. In particular `Formula.encode` is injective. -/

namespace Lax496464Proofs.WHierarchy.Logic.FormulaCode

open Lax496464.WH_B2_FirstOrder

/-- **The formula code is prefix-free.** -/
theorem encode_prefix : ∀ (φ ψ : Formula) (r r' : List ℕ),
    φ.encode ++ r = ψ.encode ++ r' → φ = ψ ∧ r = r'
  | .rel i xs, ψ, r, r', h => by
    cases ψ with
    | rel i' xs' =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, rfl, hl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := List.append_inj h hl
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h
  | .setVar xs, ψ, r, r', h => by
    cases ψ with
    | setVar xs' =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, hl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := List.append_inj h hl
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h
  | .eq x y, ψ, r, r', h => by
    cases ψ with
    | eq x' y' =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq, List.nil_append] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h
  | .neg φ, ψ, r, r', h => by
    cases ψ with
    | neg ψ =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := encode_prefix φ ψ r r' h.2
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h
  | .and φ₁ φ₂, ψ, r, r', h => by
    cases ψ with
    | and ψ₁ ψ₂ =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := encode_prefix φ₁ ψ₁ _ _ h.2
      obtain ⟨h3, h4⟩ := encode_prefix φ₂ ψ₂ r r' h2
      exact ⟨by rw [h1, h3], h4⟩
    | _ => simp [Formula.encode] at h
  | .or φ₁ φ₂, ψ, r, r', h => by
    cases ψ with
    | or ψ₁ ψ₂ =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := encode_prefix φ₁ ψ₁ _ _ h.2
      obtain ⟨h3, h4⟩ := encode_prefix φ₂ ψ₂ r r' h2
      exact ⟨by rw [h1, h3], h4⟩
    | _ => simp [Formula.encode] at h
  | .ex x φ, ψ, r, r', h => by
    cases ψ with
    | ex x' ψ =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := encode_prefix φ ψ r r' h
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h
  | .all x φ, ψ, r, r', h => by
    cases ψ with
    | all x' ψ =>
      simp only [Formula.encode, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := encode_prefix φ ψ r r' h
      exact ⟨rfl, rfl⟩
    | _ => simp [Formula.encode] at h

/-- **The formula code is injective.** -/
theorem encode_injective : Function.Injective Formula.encode := fun φ ψ h =>
  (encode_prefix φ ψ [] [] (by simpa using h)).1

/-- The code of a formula is never empty. -/
theorem encode_ne_nil (φ : Formula) : φ.encode ≠ [] := by
  cases φ <;> simp [Formula.encode]

/-- The code of a formula is at most three times as long as its size. -/
theorem length_encode_le_three_mul_size : ∀ φ : Formula, φ.encode.length ≤ 3 * φ.size
  | .rel _ xs => by simp [Formula.encode, Formula.size]; omega
  | .setVar xs => by simp [Formula.encode, Formula.size]; omega
  | .eq _ _ => by simp [Formula.encode, Formula.size]
  | .neg φ => by
    have := length_encode_le_three_mul_size φ
    simp [Formula.encode, Formula.size]; omega
  | .and φ ψ => by
    have := length_encode_le_three_mul_size φ
    have := length_encode_le_three_mul_size ψ
    simp [Formula.encode, Formula.size]; omega
  | .or φ ψ => by
    have := length_encode_le_three_mul_size φ
    have := length_encode_le_three_mul_size ψ
    simp [Formula.encode, Formula.size]; omega
  | .ex _ φ => by
    have := length_encode_le_three_mul_size φ
    simp [Formula.encode, Formula.size]; omega
  | .all _ φ => by
    have := length_encode_le_three_mul_size φ
    simp [Formula.encode, Formula.size]; omega

/-- The size of a formula is at most the length of its code. -/
theorem size_le_length_encode : ∀ φ : Formula, φ.size ≤ φ.encode.length
  | .rel _ xs => by simp [Formula.encode, Formula.size]
  | .setVar xs => by simp [Formula.encode, Formula.size]
  | .eq _ _ => by simp [Formula.encode, Formula.size]
  | .neg φ => by
    have := size_le_length_encode φ
    simp [Formula.encode, Formula.size]; omega
  | .and φ ψ => by
    have := size_le_length_encode φ
    have := size_le_length_encode ψ
    simp [Formula.encode, Formula.size]; omega
  | .or φ ψ => by
    have := size_le_length_encode φ
    have := size_le_length_encode ψ
    simp [Formula.encode, Formula.size]; omega
  | .ex _ φ => by
    have := size_le_length_encode φ
    simp [Formula.encode, Formula.size]; omega
  | .all _ φ => by
    have := size_le_length_encode φ
    simp [Formula.encode, Formula.size]; omega

end Lax496464Proofs.WHierarchy.Logic.FormulaCode
