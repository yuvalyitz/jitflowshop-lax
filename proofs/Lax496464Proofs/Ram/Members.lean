import Lax496464.Construction
import Mathlib.Data.List.GetD

/-!
# The Membership Pairs, Read Off the Word

`Construction.memberList` enumerates the pairs `(j, i)` with `i ∈ F j`, set by set and
within a set in the order of the universe. A program has only the word, which presents
each set as a block of the member array in no particular order and possibly with
repetitions. `wmemberList` is the same enumeration computed from the word, and
`wmemberList_eq` says the two agree.
-/

namespace Lax496464Proofs.Ram.Members

open Lax496464.HittingSet Lax496464.Construction

variable (x : List ℕ)

/-- Does the block of set `j` contain `i`? -/
def memB (j i : ℕ) : Bool :=
  (List.range (offset x (j + 1))).any fun t => decide (offset x j ≤ t ∧ member x t = i)

variable {x}

theorem memB_iff {j i : ℕ} :
    memB x j i = true ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ member x t = i := by
  simp only [memB, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, hlo, hmem⟩; exact ⟨t, hlo, ht, hmem⟩
  · rintro ⟨t, hlo, ht, hmem⟩; exact ⟨t, ht, hlo, hmem⟩

variable (x)

/-- The elements of set `j`, in the order of the universe. -/
def wmembers (j : ℕ) : List ℕ := (List.range (universeSize x)).filter (memB x j)

/-- The membership pairs, in the order `Construction.memberList` uses. -/
def wmemberList : List (ℕ × ℕ) :=
  (List.range (setCount x)).flatMap fun j => (wmembers x j).map fun i => (j, i)

variable {x}

theorem wmembers_eq {P : Lax496464.HittingSet.Instance} {k : ℕ} (h : Encodes x P k)
    (j : Fin P.m) : wmembers x (j : ℕ) = (P.members j).map Fin.val := by
  have hn : universeSize x = P.n := h.universeSize_eq
  rw [wmembers, hn, ← List.map_coe_finRange_eq_range, List.filter_map, Instance.members]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff, memB_iff, decide_eq_true_eq]
  exact (h.mem_iff j i).symm

theorem wmemberList_eq {P : Lax496464.HittingSet.Instance} {k : ℕ} (h : Encodes x P k) :
    wmemberList x = memberList P := by
  rw [wmemberList, memberList, h.setCount_eq, ← List.map_coe_finRange_eq_range,
    List.flatMap_map]
  refine List.flatMap_congr fun j _ => ?_
  rw [wmembers_eq h j, List.map_map]
  rfl

end Lax496464Proofs.Ram.Members
