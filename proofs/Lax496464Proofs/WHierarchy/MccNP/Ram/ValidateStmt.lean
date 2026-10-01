import Lax496464Proofs.WHierarchy.MccNP.Shape
import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateDefs
import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateProof

/-!
# The specification of the validator

`validate_spec_list`: from `a = x` and `L = |x|`, `validate` ends with `ok = 1 ↔ Shape.Valid x`
within `Kval x` steps, leaving the arrays, the tapes and every scalar outside `validateVars`
unchanged.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The scalars `validate` may assign to (all `"ok"` or `"v_*"`). -/
abbrev validateVars : List String := SF

/-- The same specification with the frame stated as an explicit list of assignable scalars
(membership in it is decided by `decide`/`simp`). -/
theorem validate_spec_list {B : ℕ} {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : Bval x < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length) validate
      (fun σ σ' => (σ'.vars "ok" = 1 ↔ Shape.Valid x) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp ∧ ∀ y, y ∉ validateVars → σ'.vars y = σ.vars y)
      (Kval x) := by
  refine (validate_spec' hx hB).post ?_
  rintro σ σ' - ⟨⟨h1, h2⟩, hf1, hf2, hf3, hf4⟩
  exact ⟨h1, h2, hf1, hf2, hf3, hf4⟩

end Lax496464Proofs.WHierarchy.MccNP.Validate
