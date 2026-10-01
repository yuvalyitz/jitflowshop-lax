import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax

/-! # Evaluating a quantifier-free formula with some `X`-atoms undecided

The reduction knows only part of the relation `X`: an *oracle* gives the value of every relation
atom and equation, and of an `X`-atom either its value or nothing (undecided). `ev` evaluates a
quantifier-free formula from left to right, short-circuiting `∧` and `∨`, and returns the value
together with a flag that records whether an undecided `X`-atom was met; the program computes
exactly this.

* `ev_sound`: if the oracle's decisions are true of `X := S` and no undecided atom was met, the
  value is the truth value of the formula.
* `ev_complete`: if the oracle decides every `X`-atom of the formula, and correctly, no undecided
  atom is met. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax

/-- What the reduction knows of the atoms. -/
structure Oracle where
  /-- The value of a relation atom. -/
  relv : ℕ → List ℕ → Bool
  /-- The value of an equation. -/
  eqv : ℕ → ℕ → Bool
  /-- The value of an `X`-atom, if decided. -/
  xdec : List ℕ → Option Bool

/-- **The evaluation**: the value, and whether an undecided `X`-atom was met. -/
def ev (o : Oracle) : Formula → Bool × Bool
  | .rel i js => (o.relv i js, false)
  | .eq a b => (o.eqv a b, false)
  | .setVar js =>
    match o.xdec js with
    | some b => (b, false)
    | none => (false, true)
  | .neg φ => (!(ev o φ).1, (ev o φ).2)
  | .and φ ψ =>
    if (ev o φ).1 then ((ev o ψ).1, (ev o φ).2 || (ev o ψ).2) else (false, (ev o φ).2)
  | .or φ ψ =>
    if (ev o φ).1 then (true, (ev o φ).2) else ((ev o ψ).1, (ev o φ).2 || (ev o ψ).2)
  | .ex _ _ => (false, false)
  | .all _ _ => (false, false)

/-- The oracle is right about the relation atoms and equations of `ψ`, under `ε`. -/
def RelOk (o : Oracle) (A : Structure) (ε : ℕ → ℕ) (ψ : Formula) : Prop :=
  (∀ i js, .rel i js ∈ atoms ψ → (o.relv i js = true ↔ js.map ε ∈ A.rel i)) ∧
    ∀ a b, .eq a b ∈ atoms ψ → (o.eqv a b = true ↔ ε a = ε b)

theorem RelOk.left {o : Oracle} {A : Structure} {ε : ℕ → ℕ} {φ ψ : Formula}
    (h : ∀ c ∈ atoms φ, c ∈ atoms ψ) (hr : RelOk o A ε ψ) : RelOk o A ε φ :=
  ⟨fun i js hm => hr.1 i js (h _ hm), fun a b hm => hr.2 a b (h _ hm)⟩

/-- **Soundness.** -/
theorem ev_sound (o : Oracle) (A : Structure) (S : Set (List ℕ)) (ε : ℕ → ℕ)
    (ψ : Formula) (hψ : ψ.IsQF) (hr : RelOk o A ε ψ)
    (hx : ∀ js ∈ xatoms ψ, ∀ b, o.xdec js = some b → (b = true ↔ js.map ε ∈ S)) :
    (ev o ψ).2 = false → ((ev o ψ).1 = true ↔ Sat A S ψ ε) := by
  induction ψ with
  | rel i js =>
    intro _; simp only [ev, Sat]; exact hr.1 i js (by simp [atoms])
  | eq a b =>
    intro _; simp only [ev, Sat]; exact hr.2 a b (by simp [atoms])
  | setVar js =>
    intro hu
    simp only [ev, Sat] at hu ⊢
    cases h : o.xdec js with
    | none => rw [h] at hu; simp at hu
    | some b => simpa [h] using hx js (by simp [xatoms]) b h
  | neg φ ih =>
    intro hu
    simp only [ev, Sat] at hu ⊢
    rw [← ih hψ (hr.left fun c hc => by simpa [atoms] using hc)
      (fun js hj => hx js (by simpa [xatoms] using hj)) hu]
    simp
  | and φ ψ ih1 ih2 =>
    intro hu
    have hr1 := hr.left (φ := φ) fun c hc => by simp [atoms, hc]
    have hr2 := hr.left (φ := ψ) fun c hc => by simp [atoms, hc]
    have hx1 := fun js (hj : js ∈ xatoms φ) => hx js (by simp [xatoms, hj])
    have hx2 := fun js (hj : js ∈ xatoms ψ) => hx js (by simp [xatoms, hj])
    simp only [ev, Sat] at hu ⊢
    by_cases h1 : (ev o φ).1 = true
    · rw [if_pos h1] at hu ⊢
      simp only [Bool.or_eq_false_iff] at hu
      rw [← ih1 hψ.1 hr1 hx1 hu.1, ← ih2 hψ.2 hr2 hx2 hu.2]
      simp [h1]
    · rw [if_neg h1] at hu ⊢
      rw [← ih1 hψ.1 hr1 hx1 hu]
      simp [h1]
  | or φ ψ ih1 ih2 =>
    intro hu
    have hr1 := hr.left (φ := φ) fun c hc => by simp [atoms, hc]
    have hr2 := hr.left (φ := ψ) fun c hc => by simp [atoms, hc]
    have hx1 := fun js (hj : js ∈ xatoms φ) => hx js (by simp [xatoms, hj])
    have hx2 := fun js (hj : js ∈ xatoms ψ) => hx js (by simp [xatoms, hj])
    simp only [ev, Sat] at hu ⊢
    by_cases h1 : (ev o φ).1 = true
    · rw [if_pos h1] at hu ⊢
      rw [← ih1 hψ.1 hr1 hx1 hu]
      simp [h1]
    · rw [if_neg h1] at hu ⊢
      simp only [Bool.or_eq_false_iff] at hu
      rw [← ih1 hψ.1 hr1 hx1 hu.1, ← ih2 hψ.2 hr2 hx2 hu.2]
      simp [h1]
  | ex _ _ _ => exact absurd hψ (by simp [Formula.IsQF])
  | all _ _ _ => exact absurd hψ (by simp [Formula.IsQF])

/-- **Completeness**: every `X`-atom decided, no undecided atom is met. -/
theorem ev_complete (o : Oracle) :
    ∀ ψ : Formula, (∀ js ∈ xatoms ψ, o.xdec js ≠ none) → (ev o ψ).2 = false
  | .rel i js, _ => rfl
  | .eq a b, _ => rfl
  | .setVar js, h => by
    have := h js (by simp [xatoms])
    simp only [ev]
    cases hd : o.xdec js with
    | none => exact absurd hd this
    | some b => rfl
  | .neg φ, h => ev_complete o φ h
  | .and φ ψ, h => by
    have h1 := ev_complete o φ fun js hj => h js (by simp [xatoms, hj])
    have h2 := ev_complete o ψ fun js hj => h js (by simp [xatoms, hj])
    simp only [ev]; split_ifs <;> simp [h1, h2]
  | .or φ ψ, h => by
    have h1 := ev_complete o φ fun js hj => h js (by simp [xatoms, hj])
    have h2 := ev_complete o ψ fun js hj => h js (by simp [xatoms, hj])
    simp only [ev]; split_ifs <;> simp [h1, h2]
  | .ex _ _, _ => rfl
  | .all _ _, _ => rfl

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval
