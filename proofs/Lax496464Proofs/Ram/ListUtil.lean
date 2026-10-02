import Mathlib.Data.List.GetD

/-!
# Two Facts About `List.set`, in the `getD` Form Every Array Invariant Is Written in
-/

namespace Lax496464Proofs.Ram.ListUtil

theorem getD_set_self (l : List ℕ) (t v : ℕ) (ht : t < l.length) : (l.set t v).getD t 0 = v := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem getD_set_ne (l : List ℕ) (t v s : ℕ) (h : s ≠ t) :
    (l.set t v).getD s 0 = l.getD s 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

end Lax496464Proofs.Ram.ListUtil
