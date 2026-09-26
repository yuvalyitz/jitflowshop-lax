import Lax496464Proofs.Ram.F5QFinal
import Lax496464.Theorem5

/-!
# Theorem 5 from the profile sweep, tagged as the concept's conclusion
-/

namespace Lax496464Proofs.F5QConclude

open Lax496464.WordEncoding Lax496464.Problems Lax496464.Fptas Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes

/--
---
conclusion: Lax496464.Theorem5.theorem5_byQmax
---
The approximation scheme of the fifth theorem from the profile sweep: read the word, zero the
weights of the jobs that cannot be preprocessed on their own, choose the rescaling `k`, round
the weights up to multiples of `k`, run the profile sweep of the third theorem with the
threshold `2 e n²` that the rounding leaves, and write `k · (W' - n)`, where `W'` is the
largest weight the rescaled table reaches (`W'` itself when `k = 1`).
-/
theorem theorem5_byQmax_proved :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ApproximatesInTime w prog
        {x | x ∈ ApproxInstances ∧ Fits c w x ∧
          c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
          (∀ j < jobCount x, 0 < procTime x j) ∧
          c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
            (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) ≤ 2 ^ w}
        (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
          (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) + c * sortCost x) :=
  Lax496464Proofs.F5QFinal.theorem5_byQmax_strong

end Lax496464Proofs.F5QConclude
