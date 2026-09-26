import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The values of the dynamic program's table, as natural numbers

A table entry `T[X, W']` is the latest instant `P' ≥ 0` from which a set of weight `W'`
compatible with `X` can be preprocessed. Machine words are natural numbers, and the entry
takes three kinds of value: none (`−∞`), all of `P' ≥ 0` (`+∞`, the empty set will do), and a
largest `v`. Since the recursion only ever *lowers* the instant, and only instants `≥ 0`
matter at the end, everything below zero may be folded into "none". The three kinds are coded
`0`, a sentinel `inf`, and `v + 1`, and `Rep` says which predicate on `P'` a code stands for.
-/

namespace Lax496464Proofs.Ram.DpCore

/-- The natural number `t` codes the predicate `Q`, on the instants `P' ≥ 0`. -/
def Rep (inf t : ℕ) (Q : ℤ → Prop) : Prop :=
  (t = 0 ∧ ∀ P' : ℤ, 0 ≤ P' → ¬ Q P') ∨ (t = inf ∧ ∀ P' : ℤ, 0 ≤ P' → Q P') ∨
    (∃ v : ℕ, t = v + 1 ∧ t < inf ∧ t ≠ 0 ∧ ∀ P' : ℤ, 0 ≤ P' → (Q P' ↔ P' ≤ v))

theorem Rep.congr {inf t : ℕ} {Q Q' : ℤ → Prop} (h : Rep inf t Q)
    (hQ : ∀ P' : ℤ, 0 ≤ P' → (Q P' ↔ Q' P')) : Rep inf t Q' := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨v, h0, h1, h2, h3⟩
  · exact Or.inl ⟨h0, fun P hP hq => h1 P hP ((hQ P hP).mpr hq)⟩
  · exact Or.inr (Or.inl ⟨h0, fun P hP => (hQ P hP).mp (h1 P hP)⟩)
  · exact Or.inr (Or.inr ⟨v, h0, h1, h2, fun P hP => (hQ P hP).symm.trans (h3 P hP)⟩)

/-- The code of "the instants `P'` with `P' + p ≤ s` and `Q₂ (P' + p)`", from the code `t₂` of
`Q₂`: the recursion's second branch. -/
def stepF (inf t₂ : ℕ) (s : ℤ) (p : ℕ) : ℕ :=
  if t₂ = 0 then 0 else
    if (p : ℤ) ≤ (if t₂ = inf then s else min ((t₂ : ℤ) - 1) s) then
      ((if t₂ = inf then s else min ((t₂ : ℤ) - 1) s) - p).toNat + 1
    else 0

theorem stepF_rep {inf t₂ : ℕ} {Q₂ : ℤ → Prop} (s : ℤ) (p : ℕ) (hs : s + 1 < inf) (hi1 : 1 < inf)
    (h : Rep inf t₂ Q₂) :
    Rep inf (stepF inf t₂ s p) (fun P' => P' + p ≤ s ∧ Q₂ (P' + p)) := by
  unfold stepF
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨v, h0, h1, h2, h3⟩
  · subst h0
    simp only [if_true]
    exact Or.inl ⟨rfl, fun P hP hq => h1 _ (by omega) hq.2⟩
  · have hne : t₂ ≠ 0 := by
      intro h; omega
    have hi0 : inf ≠ 0 := by omega
    simp only [if_false, h0, if_true, hi0]
    by_cases hp : (p : ℤ) ≤ s
    · rw [if_pos hp]
      refine Or.inr (Or.inr ⟨(s - p).toNat, rfl, ?_, by omega, ?_⟩)
      · omega
      · intro P' hP
        constructor
        · rintro ⟨hle, -⟩; omega
        · intro hle; exact ⟨by omega, h1 _ (by omega)⟩
    · rw [if_neg hp]
      exact Or.inl ⟨rfl, fun P' hP hq => hp (by have := hq.1; omega)⟩
  · have hne : t₂ ≠ 0 := h2
    have hne2 : t₂ ≠ inf := Nat.ne_of_lt h1
    simp only [hne, if_false, hne2]
    have hv : ((t₂ : ℤ) - 1) = v := by omega
    have hmin : min ((t₂ : ℤ) - 1) s = min (v : ℤ) s := by rw [hv]
    rw [hmin]
    by_cases hp : (p : ℤ) ≤ min (v : ℤ) s
    · rw [if_pos hp]
      refine Or.inr (Or.inr ⟨(min (v : ℤ) s - p).toNat, rfl, ?_, by omega, ?_⟩)
      · omega
      · intro P' hP
        constructor
        · rintro ⟨hle, hq⟩
          have := (h3 _ (by omega)).mp hq
          omega
        · intro hle
          exact ⟨by omega, (h3 _ (by omega)).mpr (by omega)⟩
    · rw [if_neg hp]
      exact Or.inl ⟨rfl, fun P' hP hq => by
        have h1' := hq.1
        have := (h3 _ (by omega)).mp hq.2
        omega⟩

/-- The union of two predicates, coded by the larger code. -/
theorem max_rep {inf t₁ f : ℕ} {Q₁ Q₃ : ℤ → Prop} (hf : f ≤ inf)
    (h₁ : Rep inf t₁ Q₁) (h₃ : Rep inf f Q₃) :
    Rep inf (max t₁ f) (fun P' => Q₁ P' ∨ Q₃ P') := by
  rcases h₁ with ⟨a0, a1⟩ | ⟨a0, a1⟩ | ⟨v, a0, a1, a2, a3⟩ <;>
  rcases h₃ with ⟨b0, b1⟩ | ⟨b0, b1⟩ | ⟨u, b0, b1, b2, b3⟩
  · subst a0; subst b0
    exact Or.inl ⟨rfl, fun P hP hq => hq.elim (a1 P hP) (b1 P hP)⟩
  · subst a0
    have : max 0 f = f := by omega
    rw [this]
    exact (Or.inr (Or.inl ⟨b0, fun P hP => Or.inr (b1 P hP)⟩))
  · subst a0
    have : max 0 f = f := by omega
    rw [this]
    refine Or.inr (Or.inr ⟨u, b0, b1, b2, fun P hP => ?_⟩)
    rw [← b3 P hP]; exact ⟨fun h => h.elim (fun h => absurd h (a1 P hP)) id, Or.inr⟩
  · subst b0
    have : max t₁ 0 = t₁ := by omega
    rw [this]
    exact Or.inr (Or.inl ⟨a0, fun P hP => Or.inl (a1 P hP)⟩)
  · have : max t₁ f = inf := by omega
    rw [this]
    exact Or.inr (Or.inl ⟨rfl, fun P hP => Or.inl (a1 P hP)⟩)
  · have : max t₁ f = inf := by omega
    rw [this]
    exact Or.inr (Or.inl ⟨rfl, fun P hP => Or.inl (a1 P hP)⟩)
  · subst b0
    have : max t₁ 0 = t₁ := by omega
    rw [this]
    refine Or.inr (Or.inr ⟨v, a0, a1, a2, fun P hP => ?_⟩)
    rw [← a3 P hP]; exact ⟨fun h => h.elim id (fun h => absurd h (b1 P hP)), Or.inl⟩
  · have : max t₁ f = inf := by omega
    rw [this]
    exact Or.inr (Or.inl ⟨rfl, fun P hP => Or.inr (b1 P hP)⟩)
  · rcases le_total t₁ f with hle | hle
    · rw [max_eq_right hle]
      refine Or.inr (Or.inr ⟨u, b0, b1, b2, fun P hP => ?_⟩)
      constructor
      · rintro (h | h)
        · have := (a3 P hP).mp h; omega
        · exact (b3 P hP).mp h
      · intro h; exact Or.inr ((b3 P hP).mpr h)
    · rw [max_eq_left hle]
      refine Or.inr (Or.inr ⟨v, a0, a1, a2, fun P hP => ?_⟩)
      constructor
      · rintro (h | h)
        · exact (a3 P hP).mp h
        · have := (b3 P hP).mp h; omega
      · intro h; exact Or.inl ((a3 P hP).mpr h)

end Lax496464Proofs.Ram.DpCore
