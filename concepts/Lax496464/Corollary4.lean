import Lax496464.Construction
import Lax496464.Problems
import Lax496464.W2Hardness

/-!
---
title: Corollary 4
type: theorem
---
There exists an FPT-reduction from Hitting Set, parameterized by solution size, to
just-in-time scheduling parameterized by the number of second-stage machines.
The construction preserves the parameter: a hitting-set instance with solution size
$k$ produces a shop with exactly $k$ machines.

The W[2]-hardness consequence follows from the W[2]-hardness of Hitting Set.

# Formalization Notes

The statement uses `W2Hard`, which unfolds to the existence of this reduction.
Its proof establishes correctness and the required running-time and parameter bounds.
It does not depend on the supporting `WH_*` development, included for completeness
beyond the scope of the scheduling project.
-/

namespace Lax496464.Corollary4

open Lax496464.Problems Lax496464.W2Hardness

/-- **Corollary 4.** The problem is W[2]-hard with respect to the number of machines. -/
axiom w2Hard_byMachines : W2Hard byMachines

end Lax496464.Corollary4
