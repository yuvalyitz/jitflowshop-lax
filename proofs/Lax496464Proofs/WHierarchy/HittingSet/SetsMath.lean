import Lax496464Proofs.WHierarchy.HittingSet.Form

/-! # Hitting Set instances given by a membership test

`ofPred U m p` is the instance with universe `{0, …, U-1}` and sets `F_j = {a : p j a}`. Its word is
the codes of `U`, `m`, `k`, then per set the code of its size and the codes of its members in
increasing order (`word_ofPred`): the members are `(List.range U).filter (p j)`, which is how the
programs of the encoding side write them — one candidate after the other.

`inSetB` is the membership test those programs use: `a` lies in set `j` when `a = j` (if `self`) or
`a` is one of the values `VAL[p]` at the positions `OFF[j] ≤ p < OFF[j+1]`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.SetsMath

open Lax496464.HittingSet Lax496464.WH_C2_HittingSet
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form

/-- The instance with universe `U`, `m` sets, and `a ∈ F_j` iff `p j a`. -/
def ofPred (U m : ℕ) (p : ℕ → ℕ → Bool) : Instance where
  n := U
  m := m
  F j := Finset.univ.filter fun a : Fin U => p j a = true

theorem mem_ofPred {U m : ℕ} {p : ℕ → ℕ → Bool} (j : Fin (ofPred U m p).m)
    (a : Fin (ofPred U m p).n) : a ∈ (ofPred U m p).F j ↔ p j a = true :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

theorem mlist_ofPred (U m : ℕ) (p : ℕ → ℕ → Bool) {j : ℕ} (hj : j < m) :
    mlist (ofPred U m p) j = (List.range U).filter (p j) := by
  rw [mlist_of_lt _ hj]
  simp only [Instance.members]
  rw [← map_val_finRange, List.filter_map]
  congr 1
  refine List.filter_congr fun a _ => ?_
  simp only [Function.comp]
  exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact mem_ofPred (p := p) ⟨j, hj⟩ a)

/-- The codes of the sets, from `j` on, of the instance of a test. -/
def setsOut (U m : ℕ) (p : ℕ → ℕ → Bool) : List ℕ :=
  (List.range m).flatMap fun j => setBits ((List.range U).filter (p j))

/-- **The word of the instance of a test.** -/
theorem word_ofPred (U m : ℕ) (p : ℕ → ℕ → Bool) (k : ℕ) :
    word (ofPred U m p) k = bitsNat U ++ bitsNat m ++ bitsNat k ++ setsOut U m p := by
  rw [word_eq]
  congr 1
  unfold restSets setsOut
  rw [List.drop_zero]
  refine List.flatMap_congr fun j hj => ?_
  rw [mlist_ofPred U m p (List.mem_range.mp hj)]

/-- The membership test of the programs: `a = j` (if `self`), or `a` is a value `VAL[q]` at a
position `OFF[j] ≤ q < OFF[j+1]`. -/
def inSetB (VAL OFF : List ℕ) (self : Bool) (j a : ℕ) : Bool :=
  (self && a == j) ||
    decide (∃ q < OFF.getD (j + 1) 0, OFF.getD j 0 ≤ q ∧ VAL.getD q 0 = a)

theorem inSetB_iff (VAL OFF : List ℕ) (self : Bool) (j a : ℕ) :
    inSetB VAL OFF self j a = true ↔
      (self = true ∧ a = j) ∨ ∃ q < OFF.getD (j + 1) 0, OFF.getD j 0 ≤ q ∧ VAL.getD q 0 = a := by
  simp [inSetB]

end Lax496464Proofs.WHierarchy.HittingSet.SetsMath
