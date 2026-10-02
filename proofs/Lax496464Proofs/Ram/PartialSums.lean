import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Partial Sums of a List of Naturals

The three facts about `List.partialSums` (defined in the core library as `scanl (· + ·) 0`) that
the Hitting Set word's offsets need, for lists of natural numbers: its length, its `i`-th entry
as the sum of the first `i` entries, and how a head element enters.
-/

namespace Lax496464Proofs.Ram.PartialSums

@[simp] theorem length_partialSums (l : List ℕ) : l.partialSums.length = l.length + 1 := by
  simp [List.partialSums]

@[simp] theorem getElem_partialSums {l : List ℕ} {i : ℕ} (h : i < l.partialSums.length) :
    l.partialSums[i] = (l.take i).sum := by
  simp [List.partialSums, List.sum_eq_foldl]

@[simp] theorem partialSums_nil : ([] : List ℕ).partialSums = [0] := by
  simp [List.partialSums]

theorem scanl_add_shift (a : ℕ) : ∀ (l : List ℕ),
    List.scanl (· + ·) a l = (List.scanl (· + ·) 0 l).map (a + ·)
  | [] => by simp
  | b :: l => by
    have ih := scanl_add_shift (a + b) l
    have ih0 := scanl_add_shift b l
    simp only [List.scanl_cons, List.map_cons, Nat.add_zero, Nat.zero_add]
    rw [ih, ih0, List.map_map]
    simp [Nat.add_assoc, Function.comp_def]

theorem partialSums_cons (a : ℕ) (l : List ℕ) :
    (a :: l).partialSums = 0 :: l.partialSums.map (a + ·) := by
  simp only [List.partialSums, List.scanl_cons, Nat.zero_add]
  rw [scanl_add_shift a l]

end Lax496464Proofs.Ram.PartialSums
