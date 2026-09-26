import Lax496464Proofs.Ram.Fits

/-!
# The pipeline, end to end, on the smallest program there is

`echo` reads one number and writes it back. Nothing about the shop is involved; the point
is that the three layers this submission's running-time proofs are built from — an IMP+
specification, the value bound of `Ram/Fits.lean`, and the compiler's transfer theorem —
fit together, and what comes out is a statement about a word RAM program of exactly the
shape the concepts ask for.
-/

namespace Lax496464Proofs.Ram.Smoke

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.ParameterizedComplexity Lax496464Proofs.Ram.Fits

/-- One scalar, no arrays, room for four nested temporaries. -/
def L0 : Layout := ⟨["n"], [], 4⟩

/-- Read a number and write it back. -/
def echo : Com := .seq (.read "n") (.write (.var "n"))

/-- The words with something on them. -/
def D : Set (List ℕ) := {x | x ≠ []}

end Lax496464Proofs.Ram.Smoke
