import Lax496464Proofs.Ram.D2Bound

/-!
# Corollary 3: the running time, against the printed bound

The program's cost is that of Theorem 2's at the table parameter `W := n`, plus a constant:
`O((n+1)^(m+1) + sortCost)`.
-/

namespace Lax496464Proofs.Ram.D5Bound

open Lax496464Proofs.Ram.D2Bound

/-- The cost of the whole program on an instance of `n` jobs and `m` machines. -/
noncomputable def cost5 (n m : ℕ) : ℕ := cost2 n m n + 10

/-- **The bound.** -/
theorem cost5_le {n m len : ℕ} (hn : n ≤ len) :
    10 * cost5 n m + 1 ≤ 200000 * (n + 1) ^ (m + 1) +
      100000 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) := by
  have h := cost2_le (m := m) (W := n) hn
  have hP : 1 ≤ (n + 1) ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
  have hpw : (n + 1) * (n + 1) ^ m = (n + 1) ^ (m + 1) := by ring
  rw [hpw] at h
  unfold cost5
  omega

end Lax496464Proofs.Ram.D5Bound
