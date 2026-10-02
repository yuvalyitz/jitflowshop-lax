import Lax496464.HittingSet

/-!
---
title: W[2]-Hardness
type: definition
---
The scheduling development uses `W2Hard P` to state the existence of an FPT-reduction
from Hitting Set, parameterized by solution size, to `P`. Its interpretation as
W[2]-hardness follows from the W[2]-hardness of Hitting Set.

# Formalization Notes

The Lean definition below refers to Hitting Set and FPT-reductions. The scheduling
proofs establish these reductions directly. For completeness, the submission also
includes the `WH_*` development of the W-hierarchy, following Flum and Grohe (2006).
That supporting material goes beyond the scope of the scheduling project and is not
needed to state or prove the scheduling reduction.
-/

namespace Lax496464.W2Hardness

open Lax496464.ParameterizedComplexity

/-- `P` is **W[2]-hard**: Hitting Set, parameterized by the solution size, fpt-reduces to
it. -/
def W2Hard (P : Problem) : Prop := HittingSet.byK ≤fpt P

end Lax496464.W2Hardness
