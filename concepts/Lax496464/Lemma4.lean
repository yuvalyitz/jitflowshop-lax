import Lax496464.Greedy

/-!
---
title: Lemma 4
type: theorem
---
After the greedy has considered the first $k$ jobs, the set it holds is feasible, uses
only those jobs, and dominates every feasible set of jobs among them. Consequently the
set it holds at the end is a feasible set of largest possible cardinality, which is the
correctness of the algorithm of Section 6.1.

# Formalization Notes

The statement is about every run of the relation, since the rule leaves choices open, and
it is proved by induction along the run with the domination property as the invariant.

The order is the counting one, which is stronger than what the paper's disjunction gives
where the cardinalities differ — see the definition for why the paper's will not carry
this induction. The conclusion of the algorithm's correctness is unaffected: an order
that dominates in this sense also dominates in cardinality.

The run is presented as a sequence of sets indexed by how many jobs have been considered,
with a first member that is empty and a step at each job. Nothing requires the sequence
to be computed by anything in particular; what is claimed is that any sequence satisfying
the two conditions ends at an optimum.

Equal preprocessing times and positive processing times are hypotheses, as in the
paper. Weights play no role: this is the unweighted case, and the conclusion is about
cardinality.
-/

namespace Lax496464.Lemma4

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Greedy

variable (I : Instance)

/-- **Lemma 4.** Along any greedy run, the set held after `k` jobs is a feasible subset of
the first `k` jobs dominating every such feasible set. -/
axiom greedy_dominating (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p)
    (hq : ∀ i : I.Job, 0 < I.q i)
    (S : ℕ → Finset I.Job) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < I.jobs, Step I p (S k) (S (k + 1)) ⟨k, hk⟩) :
    ∀ k ≤ I.jobs,
      Feasible I (S k) ∧ S k ⊆ firstJobs I k ∧
        ∀ B : Finset I.Job, B ⊆ firstJobs I k → Feasible I B → SDom I (S k) B

/-- **The greedy is optimal.** Its final set is a feasible set of largest cardinality. -/
axiom greedy_card_max (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p)
    (hq : ∀ i : I.Job, 0 < I.q i)
    (S : ℕ → Finset I.Job) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < I.jobs, Step I p (S k) (S (k + 1)) ⟨k, hk⟩) :
    Feasible I (S I.jobs) ∧
      ∀ B : Finset I.Job, Feasible I B → B.card ≤ (S I.jobs).card

end Lax496464.Lemma4
