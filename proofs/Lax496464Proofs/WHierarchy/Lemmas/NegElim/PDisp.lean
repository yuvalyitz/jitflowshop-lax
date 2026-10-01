import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms

/-! # The dispatch on the tag of the token

For each kind of token, `dispatch` runs the right arm: `disp_*` select it from the value of `tg`. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg

variable {x : List ℕ} {p pl c hh : ℕ} {st : List ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {K : ℕ}

/-- The context of the dispatch: the arm context and the tag. -/
def DC (x : List ℕ) (p pl c hh : ℕ) (st : List ℕ) (tg : ℕ) (σ : Env) : Prop :=
  AC x p pl c hh st σ ∧ σ.vars "tg" = tg

theorem tg_cond {tg k : ℕ} (hk : k < Bv x) (htg : tg < Bv x) :
    ∀ σ, DC x p pl c hh st tg σ → (Cond.eq (V "tg") (L k)).evalB (Bv x) σ = some (tg == k) :=
  fun σ h => by rw [evalB_eq_lit (by rw [h.2]; exact htg) hk, h.2]

theorem sel {tg k : ℕ} {c₁ c₂ : Com} {K₁ K₂ : ℕ} (hk : k < Bv x) (htg : tg < Bv x)
    (h₁ : tg = k → Spec (Bv x) (DC x p pl c hh st tg) c₁ Q K₁)
    (h₂ : tg ≠ k → Spec (Bv x) (DC x p pl c hh st tg) c₂ Q K₂) :
    Spec (Bv x) (DC x p pl c hh st tg) (.ite (.eq (V "tg") (L k)) c₁ c₂) Q (4 + max K₁ K₂) := by
  by_cases h : tg = k
  · exact ((Spec.ite_pos (fun σ hσ => by rw [tg_cond hk htg σ hσ]; simp [h]) (h₁ h)).mono
      (by simp <;> omega))
  · exact ((Spec.ite_neg (fun σ hσ => by rw [tg_cond hk htg σ hσ]; simp [h]) (h₂ h)).mono
      (by simp <;> omega))

/-- The uniform cost bound of one arm. -/
def Kd (x : List ℕ) : ℕ := Kneg x.length + 28 * x.length + 400

theorem Kneg_mono {r n : ℕ} (h : r ≤ n) : Kneg r ≤ Kneg n := by unfold Kneg; omega

theorem armPre {tg : ℕ} {c₁ : Com} {K₁ : ℕ} (h : Spec (Bv x) (AC x p pl c hh st) c₁ Q K₁) :
    Spec (Bv x) (DC x p pl c hh st tg) c₁ Q K₁ := h.pre fun _ hσ => hσ.1

theorem dispatch_of {tg : ℕ} (htg : tg < Bv x) (hB : 8 < Bv x)
    (h0 : tg = 0 → Spec (Bv x) (DC x p pl c hh st tg) relBr Q (Kd x))
    (h1 : tg = 1 → Spec (Bv x) (DC x p pl c hh st tg) svBr Q (Kd x))
    (h2 : tg = 2 → Spec (Bv x) (DC x p pl c hh st tg) eqBr Q (Kd x))
    (h3 : tg = 3 → Spec (Bv x) (DC x p pl c hh st tg) negBr Q (Kd x))
    (h4 : tg = 4 → Spec (Bv x) (DC x p pl c hh st tg) (conBr (.sub (L 5) (V "pl"))) Q (Kd x))
    (h5 : tg = 5 → Spec (Bv x) (DC x p pl c hh st tg) (conBr (.add (L 4) (V "pl"))) Q (Kd x))
    (h6 : tg ≠ 0 → tg ≠ 1 → tg ≠ 2 → tg ≠ 3 → tg ≠ 4 → tg ≠ 5 →
      Spec (Bv x) (DC x p pl c hh st tg) qBr Q (Kd x)) :
    Spec (Bv x) (DC x p pl c hh st tg) dispatch Q (Kd x + 24) := by
  unfold dispatch
  refine (sel (by omega) htg h0 fun n0 => sel (by omega) htg h1 fun n1 =>
    sel (by omega) htg h2 fun n2 => sel (by omega) htg h3 fun n3 =>
    sel (by omega) htg h4 fun n4 => sel (by omega) htg h5 fun n5 =>
    h6 n0 n1 n2 n3 n4 n5).mono ?_
  simp only [max_self]; omega

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp
