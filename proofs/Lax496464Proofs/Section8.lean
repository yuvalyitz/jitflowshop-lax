import Lax496464Proofs.Section8Bridge
import Lax496464.Theorem1

/-!
# Section 8: the Reduction from Hitting Set

Given a Hitting Set instance and a size `k`, the construction builds a shop with `k`
second-stage machines whose jobs come in `R·m` *epochs*. Each epoch admits one *selection*
job — one per element of the set it belongs to — and `2(k−1)` *dummies*, and the target
counts exactly that many jobs per epoch. A hitting set of size `k` schedules them
(Lemma 6); conversely, a solution of the target size forces one selection job per epoch,
its machine offsets never decrease, and some segment repeats — whose `k` offsets are a
hitting set (Lemmas 7 to 9).

## Two Errata

Both surfaced in the formalization and are repaired in `Construction`; every result about
the construction is generic in the parameters they touch, so the repair is free.

* **The reduction is false for `k ≤ 1`.** There `Q = (k−1)(n+1)` collapses to `0`, every
  window `[s, d)` is empty, nothing conflicts, and all selection jobs are schedulable at
  once whatever the family looks like. With `n = m = 2`, `F₀ = {0}`, `F₁ = {1}` and `k = 1`
  there is a feasible set of exactly the target size and no hitting set of size `1`. Hence
  the hypothesis `2 ≤ k`.
* **`R = k(n−1)+1` is one segment too few.** Lemma 9's pigeonhole needs *more* than
  `k(n−1)` gaps between segments and that value gives exactly `k(n−1)`; the bound is not
  slack, since `k` machines can consume every gap. `Construction.R` is `k(n−1)+2`.

The hypothesis `k ≤ P.n` is a normalization rather than a defect: a hitting set of size
*exactly* `k` cannot exist above that.
-/

namespace Lax496464Proofs.Section8

open Lax496464.HittingSet Lax496464.Construction
open FlexFlowJIT Section8Bridge

/-- Theorem 1's correctness, in the development's own vocabulary. -/
theorem theorem1_correct (P : HSInstance) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    P.HasHittingSet k ↔ (Theorem1.inst P k).HasWeight (Theorem1.targetSize P k) := by
  constructor
  · exact Theorem1.hasWeight_of_hasHittingSet
  · rintro ⟨Z, hfeas, hw⟩
    have hwcard : (Theorem1.inst P k).weight Z = Z.card := by
      simp only [FFJ.weight, Theorem1.inst]
      exact (Finset.card_eq_sum_ones Z).symm
    have hcard : Theorem1.targetSize P k ≤ Z.card := by rw [← hwcard]; exact hw
    obtain ⟨-, c, hlt, hindep⟩ := ((Theorem1.inst P k).feasible_iff Z).mp hfeas
    exact Theorem1.Setup.lemma9
      { hk := hk, hfeas := hfeas, hcard := hcard,
        c := c, hlt := hlt, hindep := hindep } hkn

/--
---
conclusion: Lax496464.Theorem1.construct_correct
---
Lemma 6 in one direction, Lemmas 7 to 9 in the other, transported along the numbering of
the jobs.
-/
theorem construct_correct (P : Lax496464.HittingSet.Instance) (k : ℕ) (hk : 2 ≤ k)
    (hkn : k ≤ P.n) :
    Instance.HasHittingSet P k ↔
      Lax496464.FlowShop.Instance.HasWeight (construct P k) (target P k) :=
  (theorem1_correct (hs P) k hk hkn).trans (hasWeight_iff (target P k))

end Lax496464Proofs.Section8
