import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Common

namespace Lax496464Proofs

/-!
# Non-overlapping intervals fit inside the horizon they end in

One general fact, used by `Section2.lean` and by nothing else in this development:
pairwise non-overlapping intervals that start at or after `0` and end at or before `T`
have total length at most `T`.

It has no scheduling content — it is the statement that a single machine cannot do more
than `T` units of work by time `T` — but it is the only step of the paper's Section 2
analysis that is not a rearrangement, so it is isolated here rather than buried in the
proof that uses it. The paper does not prove it; it does not even state it, writing only
*"It is well known that if a set of jobs can be completed, on a single machine, no later
than their due dates, then this can be done also by scheduling the jobs in a
nondecreasing order of due dates (Moore, 1968)"*.

The proof is the obvious one: discard the zero-length intervals, take the one that
finishes last, and observe that non-overlap puts every other interval entirely before it
*starts* — so the rest fit inside `[0, a)` for that interval's start `a`, and induction
applies with the shorter horizon `a`.
-/


namespace FlexFlowJIT

variable {ι : Type*}

/-- The induction, with the intervals already known to be nonempty. Nonemptiness is what
makes "finishes last" also mean "starts last": with zero-length intervals allowed, an
interval can end exactly where the last one ends without being before it. -/
private theorem sum_len_le_of_pos (a len : ι → ℤ) :
    ∀ (n : ℕ) (S : Finset ι) (T : ℤ), S.card ≤ n → 0 ≤ T →
      (∀ i ∈ S, 0 < len i) → (∀ i ∈ S, 0 ≤ a i) → (∀ i ∈ S, a i + len i ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → a i + len i ≤ a j ∨ a j + len j ≤ a i) →
      ∑ i ∈ S, len i ≤ T := by
  classical
  intro n
  induction n with
  | zero =>
      intro S T hcard hT _ _ _ _
      have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hS; simpa using hT
  | succ n ih =>
      intro S T hcard hT hpos hnn hend hdisj
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simpa using hT
      obtain ⟨m, hm, hmax⟩ := S.exists_max_image (fun i => a i + len i) hne
      have hkey : ∀ i ∈ S.erase m, a i + len i ≤ a m := by
        intro i hi
        have hiS : i ∈ S := Finset.mem_of_mem_erase hi
        rcases hdisj i hiS m hm (Finset.ne_of_mem_erase hi) with h | h
        · exact h
        · have h1 := hmax i hiS
          have h2 := hpos i hiS
          omega
      have hcard' : (S.erase m).card ≤ n := by
        have h := Finset.card_erase_of_mem hm
        have : 1 ≤ S.card := Finset.card_pos.mpr hne
        omega
      have hrec := ih (S.erase m) (a m) hcard' (hnn m hm)
        (fun i hi => hpos i (Finset.mem_of_mem_erase hi))
        (fun i hi => hnn i (Finset.mem_of_mem_erase hi)) hkey
        (fun i hi j hj => hdisj i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
      have hsplit := Finset.sum_erase_add S len hm
      have hendm := hend m hm
      omega

/-- **Pairwise non-overlapping intervals inside `[0, T]` have total length at most `T`.**
`a i` is the start of interval `i` and `len i` its length; the last hypothesis says any
two distinct intervals are separated, in one order or the other. -/
theorem sum_len_le (S : Finset ι) (a len : ι → ℤ) (T : ℤ) (hT : 0 ≤ T)
    (hlen : ∀ i ∈ S, 0 ≤ len i) (hnn : ∀ i ∈ S, 0 ≤ a i)
    (hend : ∀ i ∈ S, a i + len i ≤ T)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → a i + len i ≤ a j ∨ a j + len j ≤ a i) :
    ∑ i ∈ S, len i ≤ T := by
  classical
  have hfil : ∑ i ∈ S.filter (fun i => 0 < len i), len i = ∑ i ∈ S, len i :=
    Finset.sum_filter_of_ne fun x hx hne => lt_of_le_of_ne (hlen x hx) (Ne.symm hne)
  rw [← hfil]
  refine sum_len_le_of_pos a len (S.filter (fun i => 0 < len i)).card _ T le_rfl hT
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hi => hnn i (Finset.mem_filter.mp hi).1)
    (fun i hi => hend i (Finset.mem_filter.mp hi).1)
    (fun i hi j hj => hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1)

end FlexFlowJIT

end Lax496464Proofs
