import Lax496464.Construction
import Lax496464.NPHardness

/-!
---
title: Theorem 1
type: theorem
---
Just-in-time scheduling in a two-stage flexible flow shop is strongly NP-hard, already
when every weight is one.

The reduction is from Hitting Set. For $2 \le k \le n$, the shop built from a family
$F_1, \dots, F_m$ over $\{1, \dots, n\}$ admits $R \cdot m \cdot (2k-1)$ just-in-time
jobs exactly when the family has a hitting set of size $k$.

One direction schedules: a hitting set assigns to each of its $k$ elements one machine,
which runs in every epoch either the selection job of the element that hits that epoch's
set or the two dummies of the element it is responsible for, and the preprocessing of
those dummies fits into the epoch exactly. The other direction extracts: the
preprocessing budget of an epoch admits at most $2(k-1)$ dummies, so a solution of the
target size holds exactly one selection job and $2(k-1)$ dummies in every epoch, the
element a machine is responsible for never decreases from one segment to the next, and
with more than $k(n-1)$ gaps between segments some gap sees no change at all — the $k$
elements of that segment hit every set.

The numbers of the constructed shop are polynomial in $n$, $m$ and $k$, and hence in the
length of the Hitting Set instance, so the hardness is strong: no algorithm polynomial in
the magnitudes of the due dates can exist unless $\mathrm{P} = \mathrm{NP}$.

# Formalization Notes

Two statements, with different content and different costs.

The first is the correctness of the construction, which is what the section proves, and
it is an equivalence between two combinatorial facts — no machine and no encoding occur
in it. It carries the hypothesis $2 \le k \le n$, which the problem reduced from
supplies, and without which the construction is false.

The second is the hardness claim, which quantifies over every language in NP and composes
the construction with the NP-hardness of Hitting Set. It is stated against the classical
Turing-machine notion, since that is what a claim of NP-hardness means, and on the
unit-weight slice, because the construction lands there: the theorem is about
$FF(1,m) \mid\mid \sum_j Z_j$, the shop with no weights at all.

What stands between the two is the ordinary work of a reduction: composing two
polynomial-time maps, and reading the composite's output size off the construction. The
hardness of Hitting Set itself is `HittingSetHardness`.
-/

namespace Lax496464.Theorem1

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.HittingSet Lax496464.Construction Lax496464.NPHardness

/-- **Theorem 1, the construction.** For `2 ≤ k ≤ n`, the constructed shop has a feasible
set of `R·m·(2k−1)` just-in-time jobs exactly when `P` has a hitting set of size `k`. -/
axiom construct_correct (P : HittingSet.Instance) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    Instance.HasHittingSet P k ↔ HasWeight (construct P k) (target P k)

/-- **Theorem 1.** Just-in-time scheduling in a two-stage flexible flow shop is strongly
NP-hard, already on instances all of whose weights are one. -/
axiom stronglyNPHard_hasWeight :
    StronglyNPHardOn (fun I W => HasWeight I W) fun I => ∀ j : I.Job, I.w j = 1

end Lax496464.Theorem1
