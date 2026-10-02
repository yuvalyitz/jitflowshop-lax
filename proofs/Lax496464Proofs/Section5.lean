import Lax496464Proofs.EstBridge
import Lax496464Proofs.Model.Theorem3_Printed
import Lax496464.Lemma3

/-!
# Section 5: the Sweep over Due-Date Profiles, and What the Paper Prints

Section 5 replaces the alive *set* of Section 4 by its **due-date profile** — how many
selected jobs are due at each of the next `q_max` instants — which is what makes the table
`O(m^{q_max})` wide instead of `O(2^ω)`.

Recursion (5), as the paper prints it, constrains the earlier vector only at coordinates at
or above the shift `δ_j`. When `δ_j` is as large as `q_max` that constrains nothing, and the
recursion derives entries for profiles that no set of jobs realizes: `printed_not_correct`
exhibits two such instances, one for each branch. The algorithm is nevertheless correct —
`printed_readoff` — because a spurious entry is never *better* than a genuine one, so it
cannot become the answer. The repaired recursion, which ties the whole vector, is
`reachableProfile_start`.
-/

namespace Lax496464Proofs.Section5

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Sweep Lax496464.Profile Bridge EstBridge
open FlexFlowJIT FlexFlowJIT.EstFFJ

variable {I : Instance}

/-- The profile table means the same on both sides. -/
theorem reachableProfile_iff_model (t : ℤ) (x : ℕ → ℕ) (W' : ℕ) (P' : ℤ) :
    ReachableProfile I t x W' P' ↔ (model I).ReachableProfile t x W' P' :=
  exists_congr fun Z => and_congr_left fun _ => feasible_iff_model Z

/-- Recursion (5) as the concepts print it is recursion (5) as the development prints it. -/
theorem printed_iff_litReach (h : EstOrdered I) {qmax t : ℕ} {x : Fin qmax → ℕ} {W : ℕ}
    {P : ℤ} : Printed I qmax t x W P ↔ (estModel I h).LitReach qmax t x W P := by
  constructor
  · intro hp
    induction hp with
    | init => exact .init
    | zero t => exact .zero t
    | skip hcap hW hshift _ ih => exact .skip hcap hW hshift ih
    | take c hc hxc hcap hW hwW hshift _ hfit ih =>
        exact .take c hc hxc hcap hW hwW hshift ih hfit
  · intro hp
    induction hp with
    | init => exact .init
    | zero t => exact .zero t
    | skip hcap hW hshift _ ih => exact .skip hcap hW hshift ih
    | take c hc hxc hcap hW hwW hshift _ hfit ih =>
        exact .take c hc hxc hcap hW hwW hshift ih hfit

/--
---
conclusion: Lax496464.Lemma3.reachableProfile_start
---
The repaired step. Reading the profile at `t` back to `t'` is a shift by `δ = t − t'`, and
the two branches differ by whether `j` is added — which decrements the coordinate `q_j` and
needs a free machine, the capacity test being the sum of the whole profile.
-/
theorem reachableProfile_start (I : Instance) (hq : ∀ i : I.Job, 0 < I.q i) {qmax : ℕ}
    (hqmax : ∀ k : I.Job, I.q k ≤ qmax) {t' t : ℤ} {δ : ℕ} {j : I.Job}
    {x : ℕ → ℕ} {W' : ℕ} {P' : ℤ}
    (hδ : (δ : ℤ) = t - t') (htt : t' < t) (hsj : s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t)) :
    ReachableProfile I t x W' P' ↔
      (∃ y : ℕ → ℕ, (∀ i, 1 ≤ i → x i = y (δ + i)) ∧ ReachableProfile I t' y W' P') ∨
      (0 < x (I.q j) ∧ (∑ i ∈ Finset.Icc 1 qmax, x i) ≤ I.machines ∧
        ∃ (W'' : ℕ) (P'' : ℤ) (y : ℕ → ℕ),
          W'' + I.w j = W' ∧
          (∀ i, 1 ≤ i → (if i = I.q j then x i - 1 else x i) = y (δ + i)) ∧
          ReachableProfile I t' y W'' P'' ∧
          P'' + I.p j ≤ s j ∧ P'' + I.p j ≤ P') := by
  simp only [reachableProfile_iff_model]
  exact (model I).reachableProfile_start hq hqmax hδ htt hsj hnos

/--
---
conclusion: Lax496464.Lemma3.exists_reachableProfile_iff
---
Past the last start time the profile and the load carry no further information.
-/
theorem exists_reachableProfile_iff (I : Instance) {t : ℤ} (ht : ∀ k : I.Job, s k ≤ t)
    (W' : ℕ) :
    (∃ (x : ℕ → ℕ) (P' : ℤ), ReachableProfile I t x W' P') ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W' := by
  simp only [reachableProfile_iff_model]
  refine ((model I).exists_reachableProfile_iff ht W').trans (exists_congr fun Z => ?_)
  exact and_congr_left fun _ => (feasible_iff_model Z).symm

/-- The instance of the counterexample: one job, two machines, `p = 0`, `q = 1`, `d = 2`,
`w = 3`. -/
abbrev cex : Instance where
  jobs := 1
  machines := 2
  p := ![0]
  q := ![1]
  d := ![2]
  w := ![3]

theorem cex_est : EstOrdered cex := by unfold EstOrdered; decide

/--
---
conclusion: Lax496464.Lemma3.printed_not_correct
---
One job, `s₁ = 1`, `d₁ = 2`, two machines, `q_max = 1`. The shift at the only job is
`δ₁ = 1 = q_max`, so the printed recursion's `hshift` is vacuous and the taking branch
derives `T₁[(2), 3] ≤ 0` — two jobs due at `2` — in an instance with one job. The instance
has positive processing times and positive weights, so it is not excluded by any standing
assumption.
-/
theorem printed_not_correct :
    ∃ (J : Instance) (qmax : ℕ) (k : J.Job) (x : Fin qmax → ℕ) (W : ℕ) (P : ℤ),
      (∀ i : J.Job, 0 < J.q i) ∧ (∀ i : J.Job, 0 < J.w i) ∧
      (∀ i : J.Job, J.q i ≤ qmax) ∧
      Printed J qmax ((k : ℕ) + 1) x W P ∧
      ∀ Z : Finset J.Job, ∃ c : Fin qmax,
        dueProfile J Z (s k) ((c : ℕ) + 1) ≠ x c := by
  refine ⟨cex, 1, 0, ![2], 3, 0, by decide, by decide, by decide, ?_, ?_⟩
  · exact (printed_iff_litReach cex_est).mpr lemma3_printed_fails_take.1
  · exact fun Z => ⟨0, lemma3_printed_fails_take.2 Z⟩

/--
---
conclusion: Lax496464.Lemma3.printed_readoff
---
Soundness and completeness of the printed recursion, proved in `Model/Theorem3_Printed.lean`.
A derived entry is always *dominated* by a genuine one — the sets the recursion really
tracks have at least the weight and at most the load it records — so the optimum it reports
is the true optimum even though individual entries are not.
-/
theorem printed_readoff (I : Instance) {qmax : ℕ} (hq : ∀ i : I.Job, 0 < I.q i)
    (hw : ∀ i : I.Job, 0 < I.w i) (hqmax : ∀ i : I.Job, I.q i ≤ qmax)
    (hdist : ∀ i j : I.Job, i < j → s i < s j) (W : ℕ) :
    (∃ (x : Fin qmax → ℕ) (P : ℤ), Printed I qmax I.jobs x W P) ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W := by
  have hest : EstOrdered I := fun i j hij => by
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (hdist i j hlt).le
  constructor
  · rintro ⟨x, P, hP⟩
    obtain ⟨Z, hZ, hwZ⟩ :=
      ((estModel I hest).theorem3_printed_readoff hq hw hqmax hdist W).mp
        ⟨x, P, (printed_iff_litReach hest).mp hP⟩
    exact ⟨Z, (feasible_iff_model Z).mpr hZ, hwZ⟩
  · rintro ⟨Z, hZ, hwZ⟩
    obtain ⟨x, P, hP⟩ :=
      ((estModel I hest).theorem3_printed_readoff hq hw hqmax hdist W).mpr
        ⟨Z, (feasible_iff_model Z).mp hZ, hwZ⟩
    exact ⟨x, P, (printed_iff_litReach hest).mpr hP⟩

end Lax496464Proofs.Section5
