import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Common

namespace Lax496464Proofs

/-!
# Hitting Set

The source problem of Section 8:

> **Input:** A family `F` of `m` subsets of a universe `U = {1, …, n}`, and an integer `k`.
> **Question:** Is there a set `H ⊆ U` with `|H| = k` and `|H ∩ F| ≥ 1` for every `F ∈ F`?

NP-hard (Karp 1972) and W[2]-hard with respect to `k` (Downey–Fellows 1999); both are
cited by the paper and assumed here as literature axioms, in `Assumptions.lean`.

The universe is `Fin n` — `0`-indexed, where the paper writes `{1, …, n}`. Section 8's
construction uses the element `i` as an additive offset inside a due date and needs it to
be at least `1`, so the construction adds one; see `Theorem1_FromHittingSet.lean`.

`|H| = k` rather than `|H| ≤ k`: this is the paper's phrasing, and the two are equivalent
for a nonempty universe. The construction's target cardinality is calibrated to a hitting
set of *exactly* `k` elements, so the equality version is the one to reduce from.
-/


namespace FlexFlowJIT

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An instance of Hitting Set: a universe `Fin n` and a family of `m` subsets of it. The
solution size `k` is carried separately, as the problem's parameter. -/
structure HSInstance where
  /-- `n`: the size of the universe. -/
  n : ℕ
  /-- `m`: the number of sets in the family. -/
  m : ℕ
  /-- The family `F₁, …, F_m`. -/
  F : Fin m → Finset (Fin n)

namespace HSInstance

variable (P : HSInstance)

/-- `P` has a hitting set of size exactly `k`. -/
def HasHittingSet (k : ℕ) : Prop :=
  ∃ H : Finset (Fin P.n), H.card = k ∧ ∀ j : Fin P.m, ∃ i ∈ H, i ∈ P.F j

/-- The pairs `(j, i)` with `i ∈ F j` — the index set of Section 8's selection jobs.
Every set of the family contributes one selection job per epoch per element it contains. -/
def SelIdx : Type := Σ j : Fin P.m, {i : Fin P.n // i ∈ P.F j}

instance : Fintype P.SelIdx := inferInstanceAs (Fintype (Σ _ : Fin P.m, _))
instance : DecidableEq P.SelIdx := inferInstanceAs (DecidableEq (Σ _ : Fin P.m, _))

end HSInstance

end FlexFlowJIT

end Lax496464Proofs
