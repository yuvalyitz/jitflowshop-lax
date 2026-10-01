import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMain

/-!
# The specification of the program body

`body_spec`: on a valid word `x` in array `a`, `body` appends `WH_F2_MccConstruction.word (decode x)` to
the output within `Kbody x = bodyC * (kOf x + 1) ^ 2 * (|x| + 1)` steps, leaving the arrays, the
input and every scalar outside `bodyVars` unchanged.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464 Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Ram

theorem mem_word_nOf {x : List ℕ} (hx : Shape.Valid x) :
    BodyMath.nOf x ∈ WH_F2_MccConstruction.word (Shape.decode x) := by
  unfold WH_F2_MccConstruction.word
  rw [BodyMath.size_decode hx]
  simp

theorem mem_word_psum {x : List ℕ} (hx : Shape.Valid x) :
    BodyMath.psum x (BodyMath.nOf x) ∈ WH_F2_MccConstruction.word (Shape.decode x) := by
  unfold WH_F2_MccConstruction.word
  rw [BodyMath.offsets_eq hx]
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false]
  refine Or.inl (Or.inl (Or.inl (Or.inr ⟨BodyMath.nOf x, by omega, rfl⟩)))

theorem body_spec {x : List ℕ} (hx : Shape.Valid x) {B : ℕ} (hB : Bbody x < B) :
    Spec B (fun σ => σ.arrs "a" = x) body
      (fun σ σ' => σ'.out = σ.out ++ WH_F2_MccConstruction.word (Shape.decode x) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ ∀ y, y ∉ bodyVars → σ'.vars y = σ.vars y)
      (Kbody x) := BodyMain.body_spec_proof hx hB

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs
