import Lax496464Proofs.Ram.InstanceWord

/-!
# The fixed output for a tape that does not decode

`Ram/Validate.lean`'s `validate` leaves `"valid"` at `0` when the scan's data does not satisfy
`HittingSet.Encodes`'s own conditions. What the total program does on such an input does not
need to relate to the input at all (`ScanModel.lean`'s docstring: soundness of the scan is not
needed) — it only needs to be *some* fixed, cheaply computable, well-formed decision word, so
that the whole program is total. `rejectProg` writes the decision word of the empty instance
(`jobs = 0`, no weight can ever be met), the simplest word `InstanceWord.decisionWord` admits.
-/

namespace Lax496464Proofs.Ram.Reject

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop
open Lax496464Proofs.Ram.InstanceWord (decisionWord instanceWord blk)

/-- The instance with no jobs at all. -/
def emptyInstance : Instance := ⟨0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

@[simp] theorem decisionWord_emptyInstance : decisionWord emptyInstance 0 = [0, 0, 0] := by
  simp [decisionWord, instanceWord, blk, emptyInstance]

/-- Write the three entries of `decisionWord emptyInstance 0`. -/
def rejectProg : Com := .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 0)))

/-- **The reject branch's output.** A plain sequence of writes, correct and cheap on every
starting state — nothing about the tape's own content is read or needed. -/
theorem rejectProg_spec {B : ℕ} (hB : 0 < B) (o : List ℕ) :
    Spec B (fun σ => σ.out = o) rejectProg
      (fun _ σ' => σ'.out = o ++ decisionWord emptyInstance 0) 20 := by
  simp only [decisionWord_emptyInstance]
  run_vcg
  all_goals simp_all

end Lax496464Proofs.Ram.Reject
