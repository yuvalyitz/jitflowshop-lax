import Lax496464Proofs.Model.Optimum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Lax496464Proofs

/-!
# Section 7: the rounding scheme behind the FPTAS

Theorem 5 has two halves. One is algorithmic: the dynamic programs of Sections 3 and 5
solve the problem in time polynomial in the *total weight* `W`, so making the weights
small makes them fast. The other is the classical Ibarra–Kim rounding argument, which is
what says the small weights cost almost nothing — the paper's chain of inequalities (8).

This file is the second half, in full. It is the part of Theorem 5 that is mathematics
rather than a resource bound, and it is the part the paper actually writes out.

## The construction

`rescale I k` divides every weight by the *scaling factor* `k` and rounds up. Nothing else
changes — not `p`, not `q`, not `d`, not `m` — so `feasible_rescale` is `Iff.rfl` and a
solution of one instance is literally a solution of the other. The scaling factor the
paper picks is `k = ε · w_max / n`; the theorem below takes any `k` satisfying
`k · n ≤ ε · w_max`, which is what that choice is for and all the argument uses.

## The chain

With `Z` optimal for `I` and `Z*` optimal for `rescale I k`, and writing `w*` for the
rounded weights, every step is a one-line consequence of `k·(w*ⱼ − 1) ≤ wⱼ ≤ k·w*ⱼ`:

```
w(Z*) ≥ k·w*(Z*) − k·|Z*| ≥ k·w*(Z) − k·n ≥ w(Z) − k·n ≥ w(Z) − ε·w_max ≥ (1 − ε)·w(Z)
```

The last step is `w_max ≤ w(Z)` — `FFJ.wmax_le_opt`, which is where the paper's standing
assumption that every job can be preprocessed on its own gets used.
-/


namespace FFJ

/-! ## 1. Rescaling the weights -/

/-- `rescale I k`: the instance `I` with every weight replaced by `⌈wⱼ / k⌉`. The shop
itself — jobs, processing times, due dates, machines — is untouched. -/
def rescale (I : FFJ) (k : ℕ) : FFJ where
  Job := I.Job
  jobFintype := I.jobFintype
  jobDecEq := I.jobDecEq
  numMachines := I.numMachines
  p := I.p
  q := I.q
  d := I.d
  w := fun j => (I.w j + (k - 1)) / k

variable (I : FFJ) (k : ℕ)

@[simp] lemma rescale_w (j : I.Job) : (I.rescale k).w j = (I.w j + (k - 1)) / k := rfl

/-- `k·⌈wⱼ/k⌉` brackets `wⱼ`: it is at least `wⱼ`, and overshoots by less than `k`. -/
theorem rescale_bounds (hk : 0 < k) (j : I.Job) :
    I.w j ≤ k * (I.rescale k).w j ∧ k * (I.rescale k).w j ≤ I.w j + k := by
  have h1 := Nat.div_add_mod (I.w j + (k - 1)) k
  have h2 := Nat.mod_lt (I.w j + (k - 1)) hk
  simp only [rescale_w]
  omega

/-! ## 2. The two summed estimates -/

theorem weight_le_rescale (hk : 0 < k) (Z : Finset I.Job) :
    I.weight Z ≤ k * (I.rescale k).weight Z := by
  calc I.weight Z ≤ ∑ j ∈ Z, k * (I.rescale k).w j :=
        Finset.sum_le_sum fun j _ => (I.rescale_bounds k hk j).1
    _ = k * (I.rescale k).weight Z := (Finset.mul_sum Z (I.rescale k).w k).symm

theorem rescale_le_weight (hk : 0 < k) (Z : Finset I.Job) :
    k * (I.rescale k).weight Z ≤ I.weight Z + k * Z.card := by
  calc k * (I.rescale k).weight Z = ∑ j ∈ Z, k * (I.rescale k).w j :=
        Finset.mul_sum Z (I.rescale k).w k
    _ ≤ ∑ j ∈ Z, (I.w j + k) := Finset.sum_le_sum fun j _ => (I.rescale_bounds k hk j).2
    _ = I.weight Z + k * Z.card := by
        rw [Finset.sum_add_distrib]
        simp [weight, mul_comm]

/-! ## 3. Chain (8) -/

/-- **The paper's inequality chain (8).** An optimal solution of the rescaled instance,
read back as a solution of the original one, loses at most a `(1 − ε)` factor.

`hopt` is the only thing asked of `Zs`: that it is at least as good as every feasible set
*under the rounded weights*. `hkn` is what the paper's choice `k = ε·w_max/n` achieves,
and `hwmax` is `FFJ.wmax_le_opt`. -/
theorem rescale_approx {ε : ℚ} (hε : 0 ≤ ε) (hk : 0 < k)
    (Zs : Finset I.Job)
    (hopt : ∀ Z : Finset I.Job, I.Feasible Z → (I.rescale k).weight Z ≤ (I.rescale k).weight Zs)
    (hkn : (k : ℚ) * I.numJobs ≤ ε * I.wmax) (hwmax : (I.wmax : ℚ) ≤ I.opt) :
    (1 - ε) * (I.opt : ℚ) ≤ (I.weight Zs : ℚ) := by
  classical
  obtain ⟨Z, hZfeas, hZopt⟩ := I.exists_feasible_weight_eq_opt
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have e1 : (k : ℚ) * ((I.rescale k).weight Zs : ℚ) ≤ (I.weight Zs : ℚ) + k * Zs.card := by
    exact_mod_cast I.rescale_le_weight k hk Zs
  have e2 : ((I.rescale k).weight Z : ℚ) ≤ ((I.rescale k).weight Zs : ℚ) := by
    exact_mod_cast hopt Z hZfeas
  have e3 : (I.weight Z : ℚ) ≤ (k : ℚ) * ((I.rescale k).weight Z : ℚ) := by
    exact_mod_cast I.weight_le_rescale k hk Z
  have e4 : (Zs.card : ℚ) ≤ (I.numJobs : ℚ) := by
    have h : Zs.card ≤ I.numJobs := by
      simpa [numJobs, Finset.card_univ] using Finset.card_le_univ Zs
    exact_mod_cast h
  have e5 : (k : ℚ) * Zs.card ≤ ε * I.opt :=
    calc (k : ℚ) * Zs.card ≤ (k : ℚ) * I.numJobs := mul_le_mul_of_nonneg_left e4 hk'.le
      _ ≤ ε * I.wmax := hkn
      _ ≤ ε * I.opt := mul_le_mul_of_nonneg_left hwmax hε
  have e6 : (k : ℚ) * ((I.rescale k).weight Z : ℚ)
      ≤ (k : ℚ) * ((I.rescale k).weight Zs : ℚ) := mul_le_mul_of_nonneg_left e2 hk'.le
  have e7 : (I.weight Z : ℚ) = (I.opt : ℚ) := by exact_mod_cast hZopt
  have main : (I.opt : ℚ) - ε * (I.opt : ℚ) ≤ (I.weight Zs : ℚ) := by linarith
  calc (1 - ε) * (I.opt : ℚ) = (I.opt : ℚ) - ε * (I.opt : ℚ) := by ring
    _ ≤ (I.weight Zs : ℚ) := main

end FFJ

end Lax496464Proofs
