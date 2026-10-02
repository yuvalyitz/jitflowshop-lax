import Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyOk
import Lax391470Proofs.ReadAll

/-!
# The Program on Every Word

The program reads the length and the word into array `a`, decides whether the word is valid, and
writes the word of the multicoloured graph if it is.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.PolyProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Ram Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum
open Lax496464Proofs.WHierarchy.MccNP.Validate

/-- The layout: the reader's scalars, the validator's and the body's, and the array `a`. -/
def layout : Layout := ⟨["L", "rt", "rv"] ++ validateVars ++ bodyVars, ["a"], BodyOk.bodyTemps⟩

/-- The program. -/
def cmd : Com :=
  .seq Lax391470Proofs.ReadAll.readAll
    (.seq validate (.ite (.eq (.var "ok") (.lit 1)) body .skip))

set_option maxHeartbeats 4000000 in
theorem validate_ok : Com.Ok layout validate := by
  simp [layout, BodyOk.bodyTemps, validate, Validate.runFrom, Validate.runLoop, Validate.runBody,
    Validate.matRead, Validate.matGates, Validate.matBody, Validate.matLoop, Validate.finalGate,
    Validate.afterMat, Validate.checkA, Validate.checkS, Validate.fail, Validate.bump,
    validateVars, SF, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem read_ok : Com.Ok layout Lax391470Proofs.ReadAll.readAll := by
  simp [layout, BodyOk.bodyTemps, Lax391470Proofs.ReadAll.readAll, Lax391470Proofs.ReadAll.readLoop,
    Lax391470Proofs.ReadAll.readBody, Lax391470Proofs.ReadAll.bump, Lax391470Proofs.ReadAll.V,
    Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem cmd_ok : Com.Ok layout cmd := by
  refine ⟨read_ok, validate_ok, ?_, ?_, ?_⟩
  · simp [layout, validateVars, SF, Cond.Ok, Expr.Ok, condExpr, BodyOk.bodyTemps]
  · exact BodyOk.body_ok layout (by intro y hy; simp [layout, hy]) (by simp [layout])
      (by simp [layout])
  · trivial

end Lax496464Proofs.WHierarchy.MccNP.Ram.PolyProg
