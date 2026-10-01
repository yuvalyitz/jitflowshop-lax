import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse

/-! # The array of numbers as the program fills it

The program writes the final array `hs` from left to right: after `n` stores it holds
`hsS n = hs.take n ++ 0 …`. The entries of `hs` by segment, the first occurrences after the first
segment (`fst`), and the order in which the searches store their tuples. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath

open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.HittingSet.Compress (getD_idxOf getD_mem idxOf_eq_of_least)

variable (cl : List (List ℕ)) (d k : ℕ)

/-- The array after `n` stores. -/
def hsS (n : ℕ) : List ℕ := (hs cl d k).take n ++ List.replicate ((hs cl d k).length - n) 0

theorem hsS_set {n : ℕ} (hn : n < sz cl d k) :
    (hsS cl d k n).set n ((hs cl d k).getD n 0) = hsS cl d k (n + 1) :=
  Lax496464Proofs.WHierarchy.Machine.ReadTape.take_append_set _ n (by rw [length_hs]; exact hn)

theorem length_hsS (n : ℕ) : (hsS cl d k n).length = sz cl d k := by
  simp [hsS, length_hs]; omega

theorem hsS_zero : hsS cl d k 0 = List.replicate (sz cl d k) 0 := by simp [hsS, length_hs]

theorem nL_le_sz : 2 * nL cl + cl.length ≤ sz cl d k := by unfold sz; omega

/-! ### The segments -/

theorem hs_eq : hs cl d k = varNums cl ++ (canonNums cl ++ (nNums cl d ++ (lNums cl d k ++
    List.replicate (sz cl d k - (2 * nL cl + cl.length + (lNums cl d k).length)) 0))) := by
  simp [hs, List.append_assoc]

theorem hs_var {j : ℕ} (hj : j < nL cl) : (hs cl d k).getD j 0 = code cl j / 2 * MM cl := by
  rw [hs_eq, List.getD_append _ _ _ _ (by rw [length_varNums]; exact hj)]
  simp [varNums, List.getD_eq_getElem?_getD, hj]

theorem hs_canon {j : ℕ} (hj : j < nL cl) :
    (hs cl d k).getD (nL cl + j) 0 = 1 + MM cl * fst cl j := by
  rw [hs_eq, List.getD_append_right _ _ _ _ (by rw [length_varNums]; omega), length_varNums,
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by rw [length_canonNums]; exact hj)]
  simp [canonNums, List.getD_eq_getElem?_getD, hj]

theorem hs_n {c : ℕ} (hc : c < cl.length) :
    (hs cl d k).getD (2 * nL cl + c) 0 = nNum cl d c := by
  rw [hs_eq, List.getD_append_right _ _ _ _ (by rw [length_varNums]; omega), length_varNums,
    List.getD_append_right _ _ _ _ (by rw [length_canonNums]; omega), length_canonNums,
    show 2 * nL cl + c - nL cl - nL cl = c by omega,
    List.getD_append _ _ _ _ (by rw [length_nNums]; exact hc)]
  simp [nNums, List.getD_eq_getElem?_getD, hc]

theorem hs_l {r : ℕ} (hr : r < (lNums cl d k).length) :
    (hs cl d k).getD (2 * nL cl + cl.length + r) 0 = (lNums cl d k).getD r 0 := by
  rw [hs_eq, List.getD_append_right _ _ _ _ (by rw [length_varNums]; omega), length_varNums,
    List.getD_append_right _ _ _ _ (by rw [length_canonNums]; omega), length_canonNums,
    List.getD_append_right _ _ _ _ (by rw [length_nNums]; omega), length_nNums,
    show 2 * nL cl + cl.length + r - nL cl - nL cl - cl.length = r by omega,
    List.getD_append _ _ _ _ hr]

/-! ### The first occurrences after the first segment -/

theorem idxOf_map_inj {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ (l : List ℕ) (a : ℕ), (l.map f).idxOf (f a) = l.idxOf a
  | [], _ => by simp
  | b :: l, a => by
    simp only [List.map_cons, List.idxOf_cons]
    by_cases h : b = a
    · subst h; simp
    · have : (f b == f a) = false := by simpa using fun h' => h (hf h')
      rw [this, show (b == a) = false by simpa using h]
      simp [idxOf_map_inj hf l a]

theorem varNums_eq : varNums cl = (varList cl).map (· * MM cl) := by
  refine List.ext_getElem (by rw [length_varNums, List.length_map, length_varList])
    fun j h1 h2 => ?_
  simp only [varNums, List.getElem_map, List.getElem_range]
  have hj : j < nL cl := by simpa [varNums] using h1
  rw [← varList_getD cl hj, List.getD_eq_getElem _ _ (by rw [length_varList]; exact hj)]

theorem hs_take_nL : (hs cl d k).take (nL cl) = varNums cl := by
  rw [hs_eq, List.take_append_of_le_length (by rw [length_varNums]), List.take_of_length_le
    (by rw [length_varNums])]

/-- **The first occurrences, after the variables are stored.** -/
theorem firsts_hsS_nL {j : ℕ} (hj : j < nL cl) :
    (Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts (hsS cl d k (nL cl))).getD j 0 = fst cl j := by
  have hM : 0 < MM cl := by unfold MM; omega
  have hl : (hsS cl d k (nL cl)).length = sz cl d k := length_hsS cl d k _
  have hsz := nL_le_sz cl d k
  unfold Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts
  rw [List.getD_eq_getElem _ _ (by simp [hl]; omega)]
  simp only [List.getElem_map, List.getElem_range]
  have e1 : hsS cl d k (nL cl) = varNums cl ++ List.replicate (sz cl d k - nL cl) 0 := by
    rw [hsS, hs_take_nL, length_hs]
  have hv : (hsS cl d k (nL cl)).getD j 0 = code cl j / 2 * MM cl := by
    rw [e1, List.getD_append _ _ _ _ (by rw [length_varNums]; exact hj)]
    simp [varNums, List.getD_eq_getElem?_getD, hj]
  rw [hv, e1, List.idxOf_append_of_mem]
  · rw [varNums_eq, idxOf_map_inj (fun a b h => Nat.eq_of_mul_eq_mul_right hM h)]
    rfl
  · rw [varNums_eq]
    exact List.mem_map.mpr ⟨_, mem_varList cl hj, rfl⟩

/-! ### Keys -/

theorem nNum_eq_iff {c c' : ℕ} : nNum cl d c = nNum cl d c' ↔ key cl d c = key cl d c' := by
  constructor
  · intro h
    unfold nNum at h
    have hM : 0 < MM cl := by unfold MM; omega
    have h' : num (MM cl) (key cl d c) = num (MM cl) (key cl d c') :=
      Nat.eq_of_mul_eq_mul_left hM (by omega)
    exact num_inj (fun x hx => key_lt cl d hx) (fun x hx => key_lt cl d hx)
      (by rw [length_key, length_key]) h'
  · intro h; unfold nNum; rw [h]

/-! ### The order of the tuples of `Lr` -/

/-- The tuple of branch word `b` of clause `c`, if the search succeeds. -/
def gT (c b : ℕ) : Option (List ℕ) := (sim cl d k c b).map fun ch => key cl d c ++ pad cl k ch

/-- The tuples of the clauses below `c`, and of the branch words below `b` of clause `c`. -/
def lPre (c b : ℕ) : List (List ℕ) :=
  ((List.range c).flatMap fun c' => (List.range (d ^ k)).filterMap (gT cl d k c')) ++
    (List.range b).filterMap (gT cl d k c)

theorem lPre_succ (c b : ℕ) :
    lPre cl d k c (b + 1) = lPre cl d k c b ++ (gT cl d k c b).toList := by
  unfold lPre
  rw [List.range_succ, List.filterMap_append, List.append_assoc]
  congr 2

theorem lPre_next (c : ℕ) : lPre cl d k c (d ^ k) = lPre cl d k (c + 1) 0 := by
  simp [lPre, List.range_succ, List.flatMap_append]

theorem lPre_all : lPre cl d k cl.length 0 = lTuples cl d k := by
  unfold lPre lTuples gT; simp

/-- `lPre` is a prefix of all the tuples. -/
theorem lPre_prefix {c b : ℕ} (hc : c < cl.length) (hb : b ≤ d ^ k) :
    lPre cl d k c b <+: lTuples cl d k := by
  rw [← lPre_all]
  have h1 : lPre cl d k c b <+: lPre cl d k c (d ^ k) := by
    unfold lPre
    refine (List.prefix_append_right_inj _).mpr ?_
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hb
    rw [he, List.range_add, List.filterMap_append]
    exact List.prefix_append _ _
  refine h1.trans ?_
  rw [lPre_next]
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show c + 1 ≤ cl.length by omega)
  rw [he]
  unfold lPre
  simp only [List.range_zero, List.filterMap_nil, List.append_nil]
  have hr : List.range (c + 1 + e) = List.range (c + 1) ++
      List.map (fun x => c + 1 + x) (List.range e) := List.range_add
  rw [hr, List.flatMap_append]
  exact List.prefix_append _ _

theorem length_lPre_le {c b : ℕ} (hc : c < cl.length) (hb : b ≤ d ^ k) :
    (lPre cl d k c b).length ≤ (lTuples cl d k).length :=
  (lPre_prefix cl d k hc hb).length_le

/-- The number stored for branch word `b` of clause `c`. -/
theorem lNums_at {c b : ℕ} (hc : c < cl.length) (hb : b < d ^ k) {ch : List ℕ}
    (hs : sim cl d k c b = some ch) :
    (lPre cl d k c b).length < (lNums cl d k).length ∧
      (lNums cl d k).getD (lPre cl d k c b).length 0 =
        3 + MM cl * num (MM cl) (key cl d c ++ pad cl k ch) := by
  have hg : gT cl d k c b = some (key cl d c ++ pad cl k ch) := by simp [gT, hs]
  have hp := lPre_prefix cl d k hc (show b + 1 ≤ d ^ k by omega)
  rw [lPre_succ, hg] at hp
  obtain ⟨rest, hrest⟩ := hp
  have hlen : (lPre cl d k c b).length < (lTuples cl d k).length := by
    rw [← hrest]; simp
  refine ⟨by rw [length_lNums]; exact hlen, ?_⟩
  unfold lNums
  rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map]
  congr 2
  simp only [← hrest, Option.toList_some, List.append_assoc, List.singleton_append]
  rw [List.getElem_append_right (by simp)]
  simp

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
