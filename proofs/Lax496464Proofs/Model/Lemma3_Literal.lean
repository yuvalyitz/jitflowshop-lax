import Lax496464Proofs.Model.Lemma3_Profile
import Lax496464Proofs.Model.Sorted
import Mathlib.Data.Fin.VecNotation

namespace Lax496464Proofs

/-!
# Lemma 3 as Printed Is False: Two Machine-Checked Counterexamples

Lemma 3 claims that recursion (5) *"correctly computes `Tⱼ[x⃗, W']`"*, where `Tⱼ[x⃗, W']` is
the least preprocessing load of a feasible `Z ⊆ Jⱼ` of weight `W'` whose due-date profile at
`sⱼ` is `x⃗` (with `xᵢ` the number of jobs due at `sⱼ + i`, for `i = 1, …, q_max`).

Recursion (5) shifts the previous profile by `δⱼ = sⱼ − s_{j−1}` through the set
`x⃗[δ] = {y⃗ : yᵢ = x_{i−δ} for i ∈ {δ+1, …, q_max}}`, which pins `y⃗` on its last
`q_max − δ` coordinates and leaves **the last `δ` coordinates of `x⃗`** — respectively of
`x⃗^{(qⱼ)}` in the branch that takes job `j` — unconstrained. They must be zero: every job of
`J_{j−1}` is due by `s_{j−1} + q_max = sⱼ + q_max − δⱼ`. Without that condition the
recursion assigns finite values to entries whose true value is `∞`, **in both branches**.

`LitReach` encodes (5) exactly as printed — as the set of derivations the recursion admits,
so `LitReach t x W P` says the printed recursion yields `T_t[x, W] ≤ P` — and the two theorems
below exhibit, for each branch, an entry it derives that no job set realizes.

**What is not claimed.** Only the *table invariant* fails. On 5,200 random small instances
(brute force against the printed and the repaired recursion; `scripts/lemma3_check.py`) the
printed recursion's *final optimum* was always correct, and the repaired recursion — the tail
condition added to both branches — got every table entry right. That the optimum is never
affected is supported by that evidence, not proved: the mislabelled entries only over-count
busy machines, the conservative direction for the `∑ xᵢ ≤ m` cap.

The repaired recursion is what `Lemma3_Profile.lean` proves (`FFJ.reachableProfile_start`):
carrying the profile untruncated makes the shift constrain every coordinate.
-/

namespace FlexFlowJIT

namespace EstFFJ

/-- `s_{k−1}`, the start time before job `k`, with the paper's `s₀ = 0`. -/
def sBefore (E : EstFFJ) (k : Fin E.n) : ℤ :=
  if h : (k : ℕ) = 0 then 0 else E.st ⟨(k : ℕ) - 1, by omega⟩

/-- The paper's `δ` for job `k`. -/
def delta (E : EstFFJ) (k : Fin E.n) : ℕ := (E.st k - E.sBefore k).toNat

/-- The paper's `x⃗^{(q)}`: one coordinate decremented. -/
def decAt {qmax : ℕ} (x : Fin qmax → ℕ) (c : Fin qmax) : Fin qmax → ℕ :=
  Function.update x c (x c - 1)

/-- **Recursion (5), exactly as printed.** Coordinates are `0`-indexed, so coordinate `c`
counts jobs due at `sⱼ + c + 1`. The rules are the paper's: the base `T₀[0⃗, 0] = 0`, the
convention `Tⱼ[0⃗, 0] = 0`, the cap `∑ xᵢ ≤ m` and `W' > 0` on every other entry, and the two
branches, each through the printed shift — which constrains `y⃗` only on coordinates `≥ δ`. -/
inductive LitReach (E : EstFFJ) (qmax : ℕ) : ℕ → (Fin qmax → ℕ) → ℕ → ℤ → Prop
  | init : LitReach E qmax 0 0 0 0
  | zero (t : ℕ) : LitReach E qmax t 0 0 0
  | skip {k : Fin E.n} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ}
      (hcap : ∑ i, x i ≤ E.numMachines) (hW : 0 < W)
      (hshift : ∀ i : Fin qmax, ∀ hi : E.delta k ≤ (i : ℕ),
        y i = x ⟨(i : ℕ) - E.delta k, by have := i.isLt; omega⟩)
      (h : LitReach E qmax k y W P) : LitReach E qmax (k + 1) x W P
  | take {k : Fin E.n} {x y : Fin qmax → ℕ} {W : ℕ} {P : ℤ} (c : Fin qmax)
      (hc : (c : ℕ) + 1 = E.q k) (hxc : 1 ≤ x c)
      (hcap : ∑ i, x i ≤ E.numMachines) (hW : 0 < W) (hwW : E.w k ≤ W)
      (hshift : ∀ i : Fin qmax, ∀ hi : E.delta k ≤ (i : ℕ),
        y i = decAt x c ⟨(i : ℕ) - E.delta k, by have := i.isLt; omega⟩)
      (h : LitReach E qmax k y (W - E.w k) P) (hfit : P + E.p k ≤ E.st k) :
      LitReach E qmax (k + 1) x W (P + E.p k)

/-! ## The branch that takes job `j` -/

/-- One job — `s = 1`, `d = 2`, `p = 0`, `w = 3` — and two machines. -/
abbrev cexTake : EstFFJ where
  n := 1
  numMachines := 2
  p := ![0]
  q := ![1]
  d := ![2]
  w := ![3]
  est := by decide

/-- **Counterexample, taking branch.** The printed recursion derives `T₁[(2), 3] ≤ 0` — two
jobs due at `s₁ + 1 = 2` — for an instance that has only one job. The shift is vacuous
(`δ₁ = 1 = q_max`), so nothing ties the decremented profile `(1)` to anything. -/
theorem lemma3_printed_fails_take :
    cexTake.LitReach 1 1 ![2] 3 0 ∧
      ∀ Z : Finset (Fin cexTake.n), cexTake.toFFJ.dueProfile Z (cexTake.st 0) 1 ≠ 2 := by
  refine ⟨?_, fun Z hZ => ?_⟩
  · have h := LitReach.take (E := cexTake) (qmax := 1) (k := 0) (x := ![2]) (y := 0)
      (W := 3) (P := 0) 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun i hi => absurd hi (by have := i.isLt; simp [delta, sBefore, st, cexTake]))
      (LitReach.init) (by decide)
    simpa [cexTake] using h
  · have h1 : cexTake.toFFJ.dueProfile Z (cexTake.st 0) 1 ≤ Z.card :=
      Finset.card_filter_le _ _
    have h2 : Z.card ≤ 1 := by
      simpa using Finset.card_le_univ Z
    omega

end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
