import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Lax808846Proofs.Lib

/-!
# The Word RAM's IMP+ Pipeline, Re-Exported

Every running-time statement of this submission is discharged the same way: the algorithm
is written as an IMP+ command, its correctness and cost are proved on natural-number
arithmetic where no word length occurs, and `Transfer.computesInTime_of_solves` turns that
into the statement about a machine program that the concept asks for.

This module only gathers the pipeline's namespaces, so that the algorithm files below it
open one thing.
-/

namespace Lax496464Proofs.Ram
end Lax496464Proofs.Ram
