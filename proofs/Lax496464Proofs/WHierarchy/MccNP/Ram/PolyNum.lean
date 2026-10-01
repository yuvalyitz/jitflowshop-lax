import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyStmt
import Lax496464Proofs.WHierarchy.MccNP.Ram.FptTimeProof
import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateStmt

/-!
# Sizes for the polynomial bound

On a valid word `x`, the entries of the output and the values of the program are bounded by
`(|x| + 2) ^ 4`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum

open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Ram Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath

/-- The largest entry of a word. -/
def Mmax (x : List ℕ) : ℕ := x.foldr max 0

theorem le_Mmax {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v ≤ Mmax x := by
  induction x with
  | nil => simp at hv
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem Mmax_mem_or_zero (y : List ℕ) : Mmax y ∈ y ∨ Mmax y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    rcases Nat.le_total a (List.foldr max 0 t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

/-- The value bound of the whole program. -/
def Bd (x : List ℕ) : ℕ := (x.length + 2) ^ 4 + Mmax x + 1

theorem bval_lt_Bd (x : List ℕ) : Validate.Bval x < Bd x := by
  unfold Validate.Bval Bd
  have h : (x.length + 2) ^ 2 < (x.length + 2) ^ 4 := by
    apply Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem len_lt_Bd (x : List ℕ) : x.length + 1 < Bd x := by
  unfold Bd
  have h : x.length + 2 ≤ (x.length + 2) ^ 4 := by
    calc x.length + 2 = (x.length + 2) ^ 1 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem mem_lt_Bd {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v < Bd x := by
  have := le_Mmax hv
  unfold Bd; omega

theorem k_le {x : List ℕ} (hx : Shape.Valid x) : Shape.kOf x ≤ x.length := by
  have := hx.2.1; omega

theorem nOf_le {x : List ℕ} (hx : Shape.Valid x) : nOf x ≤ x.length * x.length := by
  have h1 := k_le hx
  have h2 := BodyAdj.order_le_length hx
  exact Nat.mul_le_mul h1 h2

theorem degW_le (x : List ℕ) (s : ℕ) : degW x s ≤ nOf x := by
  unfold degW
  exact (List.length_filter_le _ _).trans (by simp)

theorem psum_le (x : List ℕ) (s : ℕ) : psum x s ≤ s * nOf x := by
  unfold psum
  have := List.sum_le_card_nsmul ((List.range s).map (degW x)) (nOf x) (by
    intro v hv
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
    exact degW_le x t)
  simpa using this

theorem psum_le_sq {x : List ℕ} {s : ℕ} (hs : s ≤ nOf x) : psum x s ≤ nOf x * nOf x :=
  (psum_le x s).trans (Nat.mul_le_mul_right _ hs)

theorem Bbody_lt_Bd {x : List ℕ} (hx : Shape.Valid x) : Bbody x < Bd x := by
  rw [FptTimeProof.Bbody_eq hx]
  have hN := nOf_le hx
  have hp := psum_le_sq (x := x) (le_refl (nOf x))
  have hNN : nOf x * nOf x ≤ (x.length * x.length) * (x.length * x.length) := Nat.mul_le_mul hN hN
  unfold Bd
  generalize x.length = l at *
  generalize nOf x = N at *
  generalize psum x N = P at *
  have e : (l + 2) ^ 4 = l * l * (l * l) + 8 * (l * l * l) + 24 * (l * l) + 32 * l + 16 := by ring
  have h3 : l * l * l = l * l * l := rfl
  have h4 : l ≤ l * l + l * l * l := by nlinarith [Nat.zero_le (l*l), Nat.zero_le (l*l*l)]
  omega

/-- Every entry of the word of the construction on a valid word is at most `(|x|+2)^4`. -/
theorem entry_le {x : List ℕ} (hx : Shape.Valid x) {v : ℕ}
    (hv : v ∈ Lax496464.WH_F2_MccConstruction.word (Shape.decode x)) : v ≤ (x.length + 2) ^ 4 := by
  rw [BodyMath.word_eq hx] at hv
  have hN := nOf_le hx
  have hNN : nOf x * nOf x ≤ (x.length * x.length) * (x.length * x.length) := Nat.mul_le_mul hN hN
  have hk := k_le hx
  have hbig : (x.length * x.length) * (x.length * x.length) + x.length ≤ (x.length + 2) ^ 4 := by
    generalize x.length = l
    have e : (l + 2) ^ 4 = l * l * (l * l) + 8 * (l * l * l) + 24 * (l * l) + 32 * l + 16 := by ring
    have h4 : l ≤ l * l * l + l * l := by nlinarith [Nat.zero_le (l*l), Nat.zero_le (l*l*l)]
    omega
  have hPle := psum_le_sq (x := x) (le_refl (nOf x))
  have hN2 : nOf x ≤ nOf x * nOf x ∨ nOf x = 0 := by
    rcases Nat.eq_zero_or_pos (nOf x) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hv
  have main : v ≤ nOf x * nOf x ∨ v ≤ Shape.kOf x := by
    rcases hv with rfl | rfl | rfl | ((⟨s, hs, rfl⟩ | ⟨s, hs, ht⟩) | ⟨s, hs, rfl⟩) | rfl
    · rcases hN2 with h | h <;> omega
    · omega
    · omega
    · left
      have := psum_le_sq (x := x) (s := s + 1) (by omega)
      exact this
    · left
      have : v < nOf x := by
        have hm : v ∈ nbW x s := ht
        unfold nbW at hm
        exact List.mem_range.mp (List.mem_filter.mp hm).1
      rcases hN2 with h | h <;> omega
    · left
      have := Nat.div_le_self s (Shape.order x)
      rcases hN2 with h | h <;> omega
    · right; exact le_rfl
  omega

end Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum
