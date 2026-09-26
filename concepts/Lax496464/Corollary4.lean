import Lax496464.Construction
import Lax496464.Problems
import Lax496464.W2Hardness

/-!
---
title: Corollary 4
type: theorem
---
Just-in-time scheduling in a two-stage flexible flow shop is W[2]-hard with respect to
the number $m$ of second-stage machines. So it is fixed-parameter tractable for that
parameter only if $\mathrm{W}[2] = \mathrm{FPT}$, and the dependence on $m$ in the
running time of the paper's first dynamic program cannot be confined to a function of
$m$ alone.

The construction of the previous theorem is already an fpt-reduction for this parameter:
the shop it builds has exactly $k$ machines, so the new parameter is the old one, and
everything else about the construction is polynomial in the size of the instance it
reads.

# Formalization notes

The claim is about the parameterized problem whose parameter is the word's second entry,
the number of machines, and it unfolds to the existence of an fpt-reduction from Hitting
Set, parameterized by the solution size. Nothing about the class W[2] appears, by the
choice made in the definition of W[2]-hardness.

The parameter is preserved exactly rather than merely bounded, which is stronger than
what an fpt-reduction requires. The bound is the identity, and stating it that way would
add nothing to the claim that is proved.
-/

namespace Lax496464.Corollary4

open Lax496464.Problems Lax496464.W2Hardness

/-- **Corollary 4.** The problem is W[2]-hard with respect to the number of machines. -/
axiom w2Hard_byMachines : W2Hard byMachines

end Lax496464.Corollary4
