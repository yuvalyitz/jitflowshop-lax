import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PSym

/-! # What the program needs of an instance word

`Dom x φ`: the word `x` is the word of a structure followed by the code of the `Σ_1`-formula `φ`.
From it: where the blocks and the entries are (`bo`, `oo`, `entsUpTo`), the entries and their ranks
as the program computes them (first occurrences `foL`, rank as a count), and the tuples of the
compressed structure as the program reads them off the array of ranks. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.StructureCode Lax496464Proofs.WHierarchy.Logic.Words
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PSym

/-! ### The entries, block by block -/

/-- The entries of the blocks below `i`. -/
def entsUpTo (x : List ℕ) (i : ℕ) : List ℕ :=
  (List.range i).flatMap fun i' => tupR x (bo x i' + 1) (cntOf x i' * arOf x i')

/-- The number of entries of the blocks below `i`. -/
def oo (x : List ℕ) (i : ℕ) : ℕ := (entsUpTo x i).length

theorem entsUpTo_succ (x : List ℕ) (i : ℕ) :
    entsUpTo x (i + 1) = entsUpTo x i ++ tupR x (bo x i + 1) (cntOf x i * arOf x i) := by
  simp [entsUpTo, List.range_succ]

theorem oo_succ (x : List ℕ) (i : ℕ) : oo x (i + 1) = oo x i + cntOf x i * arOf x i := by
  simp [oo, entsUpTo_succ]

theorem oo_mono (x : List ℕ) {i i' : ℕ} (h : i ≤ i') : oo x i ≤ oo x i' := by
  induction i' with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_refl _
  | succ i' ih =>
    rcases Nat.lt_or_ge i (i' + 1) with h' | h'
    · have := ih (by omega); rw [oo_succ]; omega
    · have : i = i' + 1 := by omega
      subst this; exact le_refl _

theorem bo_succ (x : List ℕ) (i : ℕ) : bo x (i + 1) = bo x i + 1 + cntOf x i * arOf x i := rfl

theorem bo_eq (x : List ℕ) : ∀ i, bo x i = 2 + sOf x + oo x i + i
  | 0 => by simp [bo, oo, entsUpTo]
  | i + 1 => by rw [bo_succ, oo_succ, bo_eq x i]; ring

theorem listOf_eq (x : List ℕ) (i : ℕ) :
    listOf x i = LR x (bo x i + 1) (cntOf x i) (arOf x i) := by
  unfold listOf LR
  refine List.map_congr_left fun j _ => ?_
  unfold tupR entOf
  refine List.map_congr_left fun l _ => ?_
  congr 1; try ring

theorem entries_eq (x : List ℕ) : entries x = entsUpTo x (sOf x) := by
  unfold entries entsUpTo
  refine List.flatMap_congr fun i _ => ?_
  rw [listOf_eq, flatten_LR]

/-- Entry `k` of block `i`, in the list of all entries. -/
theorem entsUpTo_getD {x : List ℕ} {i i' k : ℕ} (hi : i < i') (hk : k < cntOf x i * arOf x i) :
    (entsUpTo x i').getD (oo x i + k) 0 = x.getD (bo x i + 1 + k) 0 := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rw [entsUpTo_succ]
    rcases Nat.lt_or_ge i i' with h | h
    · have hl : oo x i + k < (entsUpTo x i').length := by
        have : oo x (i + 1) ≤ oo x i' := oo_mono x (by omega)
        rw [oo_succ] at this
        show oo x i + k < oo x i'
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD,
        ih h]
    · have : i = i' := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by unfold oo; omega)]
      unfold oo
      rw [show (entsUpTo x i).length + k - (entsUpTo x i).length = k by omega,
        ← List.getD_eq_getElem?_getD]
      unfold tupR
      rw [List.getD_eq_getElem?_getD]
      simp [hk]

/-! ### Ranks, as the program counts them -/

/-- `1` if entry `q` of `E` occurs for the first time at `q`. -/
def foL (E : List ℕ) (q : ℕ) : ℕ := if E.getD q 0 ∈ E.take q then 0 else 1

/-- The count the rank pass makes for the value `e`, over the first `q` positions. -/
def rkCount (E : List ℕ) (e q : ℕ) : ℕ :=
  ((List.range q).map fun q' => if E.getD q' 0 < e then foL E q' else 0).sum

theorem rkCount_succ (E : List ℕ) (e q : ℕ) :
    rkCount E e (q + 1) = rkCount E e q + if E.getD q 0 < e then foL E q else 0 := by
  simp [rkCount, List.range_succ]

theorem foL_append {E : List ℕ} {v q : ℕ} (hq : q < E.length) : foL (E ++ [v]) q = foL E q := by
  unfold foL
  rw [List.take_append_of_le_length hq.le, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hq, ← List.getD_eq_getElem?_getD]

theorem rkCount_append (E : List ℕ) (v e : ℕ) : ∀ q, q ≤ E.length →
    rkCount (E ++ [v]) e q = rkCount E e q
  | 0, _ => rfl
  | q + 1, h => by
    rw [rkCount_succ, rkCount_succ, rkCount_append E v e q (by omega), foL_append (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]

/-- **The count is the rank.** -/
theorem rkCount_eq (e : ℕ) : ∀ E : List ℕ, rkCount E e E.length = rk E.toFinset e := by
  intro E
  induction E using List.reverseRecOn with
  | nil => simp [rkCount, rk]
  | append_singleton E v ih =>
    rw [List.length_append, List.length_singleton, rkCount_succ, rkCount_append E v e _ le_rfl, ih]
    have hg : (E ++ [v]).getD E.length 0 = v := by simp
    have hf : foL (E ++ [v]) E.length = if v ∈ E then 0 else 1 := by
      unfold foL; rw [hg, List.take_left' rfl]
    rw [hg, hf, List.toFinset_append]
    unfold rk
    by_cases hv : v ∈ E
    · have h1 : E.toFinset ∪ [v].toFinset = E.toFinset := by
        ext a; simp only [Finset.mem_union, List.mem_toFinset, List.mem_singleton]
        constructor
        · rintro (h | rfl) <;> assumption
        · exact Or.inl
      rw [h1]; simp [hv]
    · have hdisj : Disjoint (E.toFinset.filter (· < e)) ([v].toFinset.filter (· < e)) := by
        rw [Finset.disjoint_left]; intro a ha hb
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_singleton] at ha hb
        rw [hb.1] at ha; exact hv ha.1
      rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj]
      by_cases hve : v < e <;> simp [hve, hv, Finset.filter_singleton]

/-! ### Blocks of the compressed structure -/

theorem length_sList {L : List (List ℕ)} (hL : L.Nodup) : (sList L).length = L.length - 1 := by
  by_cases hne : L = []
  · subst hne; simp [sList]
  unfold sList
  rw [List.length_filterMap_eq_countP]
  have h := List.length_eq_countP_add_countP
    (fun u => (Option.map (fun x => u ++ x) (succOf L u)).isSome) (l := L)
  have hnone : List.countP (fun a => decide ¬((Option.map (fun x => a ++ x) (succOf L a)).isSome = true)) L
      = L.count (maxL L) := by
    rw [List.count_eq_countP]
    refine List.countP_congr fun u hu => ?_
    simp only [Option.isSome_map, decide_not, Bool.not_eq_true', beq_iff_eq]
    constructor
    · intro h
      have hn : succOf L u = none := by
        cases hs : succOf L u with
        | none => rfl
        | some v => simp [hs] at h
      rw [succOf_none] at hn
      refine le_antisymm (le_maxL hu) ?_
      rcases lt_or_ge u (maxL L) with h' | h'
      · exact absurd h' (hn _ (maxL_mem hne))
      · exact h'
    · rintro rfl
      have : succOf L (maxL L) = none :=
        succOf_none.mpr fun w hw hlt => absurd (le_maxL hw) (not_le.mpr hlt)
      simp [this]
  rw [hnone, List.count_eq_one_of_mem hL (maxL_mem hne)] at h
  omega

theorem blockOf_fList (L : List (List ℕ)) :
    blockOf (fList L) = if L.length = 0 then [0] else 1 :: minL L := by
  unfold blockOf fList
  by_cases hne : L = []
  · subst hne; simp
  · rw [if_neg hne, if_neg (by simpa using hne)]; simp

theorem blockOf_lList (L : List (List ℕ)) :
    blockOf (lList L) = if L.length = 0 then [0] else 1 :: maxL L := by
  unfold blockOf lList
  by_cases hne : L = []
  · subst hne; simp
  · rw [if_neg hne, if_neg (by simpa using hne)]; simp

theorem blockOf_zList (M : ℕ) (L : List (List ℕ)) :
    blockOf (zList M L) = if L.length = 0 then M :: List.range M else [0] := by
  unfold blockOf zList
  by_cases hne : L = []
  · subst hne; simp
    induction M with
    | zero => rfl
    | succ M ih => simp [List.range_succ]; exact ih
  · rw [if_neg hne, if_neg (by simpa using hne)]; simp

/-- **What `symW` writes is the five blocks.** -/
theorem symOut_eq {w : List ℕ} {o c r M : ℕ} (hL : (LR w o c r).Nodup) :
    symOut w o c r M = ((NData.blocks ⟨0, M, fun _ => r, fun _ => LR w o c r⟩ 0).map blockOf).flatten := by
  simp only [NData.blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [blockOf_fList, blockOf_lList, blockOf_zList, symOut, length_LR]
  unfold blockOf
  rw [length_LR, flatten_LR, length_sList hL, length_LR]
  simp only [List.append_assoc]

/-! ### Instance words -/

/-- What the program needs of an instance word. -/
structure Dom (x : List ℕ) (φ : Formula) : Prop where
  drop_eq : x.drop (bo x (sOf x)) = φ.encode
  fs_eq : bo x (sOf x) + φ.encode.length = x.length
  ar_pos : ∀ i < sOf x, 1 ≤ arOf x i
  nodup : ∀ i < sOf x, (listOf x i).Nodup
  sigma : IsSigma 1 φ
  nsv : φ.NoSetVar

/-- **An instance word has what the program needs.** -/
theorem dom_of_mem {x : List ℕ} (hx : x ∈ (pMC {φ | IsSigma 1 φ}).Domain) :
    ∃ A φ, EncodesMC x A φ ∧ Dom x φ := by
  obtain ⟨A, φ, h, hσ, hns⟩ := hx
  obtain ⟨y, hy, hxy⟩ := h
  obtain ⟨hs, hN, har, hlist, hbo⟩ := parse hy hxy
  refine ⟨A, φ, ⟨y, hy, hxy⟩, ⟨?_, ?_, ?_, fun i hi => (hlist i hi).1, hσ, hns⟩⟩
  · rw [hbo, hxy, List.drop_left]
  · rw [hbo, hxy, List.length_append]
  · intro i hi
    rw [har i hi]
    rw [hs] at hi
    exact Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem.Structure.arity_pos' A i hi

variable {x : List ℕ} {φ : Formula}

theorem Dom.fs_le (hd : Dom x φ) : bo x (sOf x) ≤ x.length := by have := hd.fs_eq; omega

theorem Dom.hdr (hd : Dom x φ) : 2 + sOf x < x.length := by
  have := hd.fs_eq
  have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil φ
  have := bo_eq x (sOf x)
  have : 0 < φ.encode.length := List.length_pos_iff.mpr ‹_›
  omega

theorem Dom.bo_le (_hd : Dom x φ) {i : ℕ} (hi : i ≤ sOf x) : bo x i ≤ bo x (sOf x) := by
  rw [bo_eq, bo_eq]; have := oo_mono x hi; omega

theorem Dom.oo_le (hd : Dom x φ) {i : ℕ} (hi : i ≤ sOf x) : oo x i + i + 2 ≤ x.length := by
  have := hd.bo_le hi; rw [bo_eq] at this; have := hd.fs_le; omega

theorem Dom.blk_le (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    bo x i + 1 + cntOf x i * arOf x i ≤ bo x (sOf x) := by
  rw [← bo_succ]; exact hd.bo_le hi

/-- The bound on every value the program computes. -/
def Bv (x : List ℕ) : ℕ := 16 * maxEntry x + 64 * (x.length + 2) * (x.length + 2) + 64

theorem getD_le_maxEntry (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ maxEntry x := by
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact le_maxEntry (List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; exact Nat.zero_le _

theorem len_sq_le (x : List ℕ) : (x.length + 2) * (x.length + 2) ≥ x.length + 2 := by
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
