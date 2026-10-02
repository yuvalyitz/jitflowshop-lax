import Lax496464.HittingSet

/-!
---
title: W[2]-Hardness
type: definition
---
A parameterized problem is *W[2]-hard* if Hitting Set, parameterized by the solution
size, fpt-reduces to it.

Hitting Set is W[2]-complete for that parameter, so this agrees with the usual definition
— every problem in W[2] fpt-reduces to a W[2]-hard one — and a W[2]-hard problem is
fixed-parameter tractable only if $\mathrm{W}[2] = \mathrm{FPT}$, which is not believed.

# Formalization Notes

Hardness is stated against a fixed complete problem rather than by quantifying over a
class. The two are equivalent given the W[2]-completeness of Hitting Set, which is the
literature result a parameterized hardness proof cites anyway, and which is what makes
reducing *from* Hitting Set the standard way to prove W[2]-hardness.

The gain is that nothing about W[2] itself has to be formalized. A definition by
quantification would need the class, and therefore a machine model with a weft-bounded
circuit characterization or an equivalent; none of that appears in a hardness proof, and
formalizing it in order to state one would put a large body of machinery between the
statement and what the proof establishes.

The price is that the definition is only as good as that completeness result. It is
recorded here in prose, cited, and assumed nowhere in Lean: no statement of this
submission depends on it, because every statement is about the reduction the definition
unfolds to.
-/

namespace Lax496464.W2Hardness

open Lax496464.ParameterizedComplexity

/-- `P` is **W[2]-hard**: Hitting Set, parameterized by the solution size, fpt-reduces to
it. -/
def W2Hard (P : Problem) : Prop := HittingSet.byK ≤fpt P

end Lax496464.W2Hardness
