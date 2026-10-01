import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! The largest entry of a word, and bounds against `2 ^ bitSize`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

open Lax759944.BinaryWordEncoding Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-- The largest entry of a word (`0` for the empty word). -/
def Mmax (x : List ℕ) : ℕ := x.foldr max 0

theorem Mmax_cons (a : ℕ) (x : List ℕ) : Mmax (a :: x) = max a (Mmax x) := rfl

theorem le_Mmax {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v ≤ Mmax x := by
  induction x with
  | nil => simp at hv
  | cons a t ih =>
    rw [Mmax_cons]
    rcases List.mem_cons.mp hv with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem Mmax_mem_or_zero (y : List ℕ) : Mmax y ∈ y ∨ Mmax y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    rw [Mmax_cons]
    rcases Nat.le_total a (Mmax t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

theorem Mmax_lt_two_pow (x : List ℕ) : Mmax x < 2 ^ bitSize x := by
  rcases Mmax_mem_or_zero x with h | h
  · exact lt_two_pow_bitSize h
  · rw [h]; exact Nat.two_pow_pos _

theorem length_lt_two_pow (x : List ℕ) : x.length < 2 ^ bitSize x :=
  lt_of_le_of_lt (length_le_bitSize x) Nat.lt_two_pow_self

theorem getD_le_Mmax (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ Mmax x := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact le_Mmax (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]; exact Nat.zero_le _

theorem last_le_Mmax (x : List ℕ) : x.getLast?.getD 0 ≤ Mmax x := by
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · simp
  · simpa using le_Mmax (x := l ++ [a]) (v := a) (by simp)

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds
