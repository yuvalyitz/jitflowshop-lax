import Lax496464Proofs.Model.IntervalColoring
import Lax496464Proofs.Model.Optimum

namespace Lax496464Proofs

/-!
# Section 6: Uniform Preprocessing Times, and Proper Instances

Two structural facts the paper's `p_j = p` algorithms are built on.

**Condition 1 becomes a counting condition.** When every job takes the same time `p` to
preprocess, *"`Z` can be preprocessed in time"* says only that at most `⌊s_j / p⌋` of the
selected jobs start no later than `j` — which is what Section 6.1's first stopping rule
(*"`s_j < (|Z_{j−1}| + 1)·p`"*) tests, and what the ILP constraint (6) of Section 6.2,
`∑_{i ≤ j} x_i ≤ ⌊s_j / p⌋`, encodes.

**Proper instances are EDD instances, and their running sets are intervals.** Section 6.2
calls an instance *proper* when no job's second-operation interval is contained in
another's. `proper_d_le` is the paper's *"The fact that `J` is proper implies that this
order is the same as the Early Due Date (EDD) order"*, and `running_convex` is the
combinatorial content of **Lemma 5**: in EST order, the jobs alive at any one instant form
a *consecutive block*. That is precisely why the second family of ILP constraints has the
consecutive ones property — the first family, `∑_{i ≤ j} x_i ≤ ⌊s_j/p⌋`, is a prefix and so
consecutive for free — and hence why the constraint matrix is totally unimodular and the
relaxation integral.

Stating Lemma 5 this way rather than as a property of a `2n × n` matrix keeps it about the
instance instead of about a chosen enumeration of it: "the ones in row `j` are consecutive"
*is* "if `a` and `c` are alive at `t` and `b` sits between them in EST order, then `b` is
alive at `t`".
-/


namespace FFJ

variable (I : FFJ)

/-! ## 1. Uniform preprocessing times -/

/-- **Condition 1 under `p_j = p`.** Preprocessing `Z` in time is a bound on how *many*
of its jobs may start by each deadline, not on their total length. -/
theorem preprocessable_of_uniform {p : ℕ} (hp : ∀ j, I.p j = p) (Z : Finset I.Job) :
    I.Preprocessable Z ↔
      ∀ j ∈ Z, ((Z.filter (fun i => I.s i ≤ I.s j)).card : ℤ) * p ≤ I.s j := by
  classical
  have hsum : ∀ j : I.Job,
      ∑ i ∈ Z.filter (fun i => I.s i ≤ I.s j), (I.p i : ℤ)
        = ((Z.filter (fun i => I.s i ≤ I.s j)).card : ℤ) * p := by
    intro j
    rw [Finset.sum_congr rfl (fun i _ => by rw [hp i]), Finset.sum_const, nsmul_eq_mul]
  exact ⟨fun h j hj => (hsum j) ▸ h j hj, fun h j hj => (hsum j).symm ▸ h j hj⟩

/-! ## 2. Proper instances -/

/-- An instance is **proper** when no job's second-operation interval `[s j, d j)` is
contained in another's — the paper's *"instances where there are no two jobs `i` and `j`
with `[s_i, d_i) ⊆ [s_j, d_j)`"*. -/
def Proper : Prop :=
  ∀ i j : I.Job, i ≠ j → ¬ (I.s j ≤ I.s i ∧ (I.d i : ℤ) ≤ (I.d j : ℤ))

variable {I}

/-- **EST order is EDD order on a proper instance.** If one job's second operation starts
no later than another's, its due date is no later either — otherwise the second interval
would sit inside the first. -/
theorem proper_d_le (h : I.Proper) {i j : I.Job} (hne : i ≠ j) (hs : I.s i ≤ I.s j) :
    (I.d i : ℤ) ≤ (I.d j : ℤ) := by
  by_contra hd
  exact h j i (Ne.symm hne) ⟨hs, by omega⟩

/-- **Lemma 5, intrinsically.** On a proper instance the jobs alive at any one instant
form a consecutive block of the Early Start Time order: anything that starts between two
jobs alive at `t` is itself alive at `t`.

This is the consecutive ones property of the ILP's second family of constraints; see the
module doc. -/
theorem running_convex (h : I.Proper) {Z : Finset I.Job} {t : ℤ} {a b c : I.Job}
    (ha : a ∈ I.running Z t) (hc : c ∈ I.running Z t) (hb : b ∈ Z)
    (hab : I.s a ≤ I.s b) (hbc : I.s b ≤ I.s c) : b ∈ I.running Z t := by
  obtain ⟨-, ha1, ha2⟩ := mem_running.mp ha
  obtain ⟨-, hc1, -⟩ := mem_running.mp hc
  refine mem_running.mpr ⟨hb, by omega, ?_⟩
  by_cases hab' : a = b
  · subst hab'; exact ha2
  · exact lt_of_lt_of_le ha2 (proper_d_le h hab' hab)

end FFJ

end Lax496464Proofs
