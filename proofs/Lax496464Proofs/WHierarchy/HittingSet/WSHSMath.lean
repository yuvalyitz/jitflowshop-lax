import Lax496464Proofs.WHierarchy.HittingSet.SetsMath
import Lax496464Proofs.WHierarchy.HittingSet.Compress
import Lax496464Proofs.WHierarchy.HittingSet.Firsts
import Lax496464.WH_C3_WeightedSat
import Lax496464.WH_E2_HittingSetW2Complete

/-! # Weighted monotone satisfiability to Hitting Set: the mathematics

The clauses, read as sets of variables, are the hyperedges (Flum–Grohe, proof of Theorem 7.14): for
a monotone formula, an assignment satisfies it exactly when its true variables meet every clause.

The variables are word entries, so they can be huge; they are renamed by the position of their
first occurrence in the list of all literals (`litsL`), as in `Compress`. The universe is the set of
positions `{0, …, T-1}`; a position that is not a first occurrence lies in no set. The weight of the
formula is exact and its true variables must be variables of the formula, so a satisfying
assignment of weight `k` exists only for `k ≤ |vars α|`; for such `k` a hitting set of size at most
`k` can be padded inside the variables, and the answers agree. For `k > |vars α|` the reduction
writes a fixed no-instance. The empty formula has no variables and is `0`-satisfiable only; an
empty clause gives an empty set, which no set hits. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WSHSMath

open Lax429075.CNF Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_C3_WeightedSat
open Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.Compress (idxOf_eq_of_least getD_idxOf getD_mem)

/-! ## The word of a formula determines the formula -/

/-- The word of one clause. -/
def encC (C : Clause) : List ℕ := C.length :: C.map litCode

theorem encode_eq (α : Formula) : encode α = α.length :: α.flatMap encC := rfl

theorem litCode_inj {l l' : Literal} (h : litCode l = litCode l') : l = l' := by
  obtain ⟨i, p⟩ := l
  obtain ⟨i', p'⟩ := l'
  simp only [litCode] at h
  cases p <;> cases p' <;> simp at h ⊢ <;> omega

theorem map_litCode_inj {C D : Clause} (h : C.map litCode = D.map litCode) : C = D :=
  List.map_injective_iff.mpr (fun _ _ h => litCode_inj h) h

theorem flatMap_encC_peel : ∀ (α β : Formula) (r r' : List ℕ), α.length = β.length →
    α.flatMap encC ++ r = β.flatMap encC ++ r' → α = β ∧ r = r'
  | [], [], r, r', _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | C :: α, D :: β, r, r', hl, h => by
      simp only [List.flatMap_cons, encC, List.cons_append, List.append_assoc,
        List.cons.injEq] at h
      obtain ⟨hlen, h⟩ := h
      obtain ⟨hm, h⟩ := List.append_inj h (by simp [hlen])
      obtain ⟨rfl, rfl⟩ := flatMap_encC_peel α β r r' (by simpa using hl) h
      exact ⟨by rw [map_litCode_inj hm], rfl⟩

/-- **A weighted-satisfiability word determines the formula and the weight.** -/
theorem encode_inj {α β : Formula} {k k' : ℕ} (h : encode α ++ [k] = encode β ++ [k']) :
    α = β ∧ k = k' := by
  simp only [encode_eq, List.cons_append, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  obtain ⟨rfl, hk⟩ := flatMap_encC_peel α β _ _ hl h
  exact ⟨rfl, by simpa using hk⟩

/-! ## The literals, their first occurrences, the clause offsets -/

/-- The variables of all literals, clause after clause. -/
def litsL (α : Formula) : List ℕ := α.flatMap fun C => C.map Literal.index

/-- The offset of clause `j` in `litsL`. -/
def cOff (α : Formula) (j : ℕ) : ℕ := ((α.take j).map List.length).sum

/-- The offsets, as the list the program builds. -/
def offL (α : Formula) : List ℕ := (List.range (α.length + 1)).map (cOff α)

/-- The number of literals. -/
def T (α : Formula) : ℕ := (litsL α).length

theorem vars_eq (α : Formula) : vars α = (litsL α).toFinset := rfl

theorem litsL_split (α : Formula) (j : ℕ) :
    litsL α = (α.take j).flatMap (fun C => C.map Literal.index) ++
      (α.drop j).flatMap (fun C => C.map Literal.index) := by
  rw [litsL, ← List.flatMap_append, List.take_append_drop]

theorem length_take_flatMap (α : Formula) (j : ℕ) :
    ((α.take j).flatMap fun C => C.map Literal.index).length = cOff α j := by
  simp [cOff, List.length_flatMap]

theorem cOff_succ (α : Formula) {j : ℕ} (hj : j < α.length) :
    cOff α (j + 1) = cOff α j + (α[j]).length := by
  rw [cOff, cOff, List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem cOff_mono (α : Formula) {i j : ℕ} (h : i ≤ j) : cOff α i ≤ cOff α j := by
  unfold cOff
  have := List.take_append_drop i (α.take j)
  rw [List.take_take, Nat.min_eq_left h] at this
  rw [← this, List.map_append, List.sum_append]
  omega

theorem cOff_length (α : Formula) : cOff α α.length = T α := by
  simp [cOff, T, litsL, List.length_flatMap]

/-- The literal at position `cOff j + q` is literal `q` of clause `j`. -/
theorem litsL_getD (α : Formula) {j q : ℕ} (hj : j < α.length) (hq : q < (α[j]).length) :
    (litsL α).getD (cOff α j + q) 0 = (α[j][q]).index := by
  rw [litsL_split α j, List.getD_append_right _ _ _ _ (by rw [length_take_flatMap]; omega),
    length_take_flatMap, Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hj,
    List.flatMap_cons, List.getD_append _ _ _ _ (by simpa using hq)]
  simp [List.getD_eq_getElem?_getD, hq]

/-! ## The first occurrences and the number of variables -/

/-- The first position holding the variable at position `p`. -/
def fstL (α : Formula) (p : ℕ) : ℕ := (litsL α).idxOf ((litsL α).getD p 0)

theorem firsts_getD (α : Formula) {p : ℕ} (hp : p < T α) :
    (Firsts.firsts (litsL α)).getD p 0 = fstL α p := by
  rw [List.getD_eq_getElem _ _ (by simpa [Firsts.firsts, T] using hp)]
  simp [Firsts.firsts, fstL]

/-- The positions that are first occurrences, counted. -/
def countFirst (l : List ℕ) : ℕ :=
  ((List.range l.length).filter fun p => l.idxOf (l.getD p 0) = p).length

theorem countFirst_eq (l : List ℕ) : countFirst l = l.toFinset.card := by
  induction l using List.reverseRecOn with
  | nil => simp [countFirst]
  | append_singleton l a ih =>
      unfold countFirst at ih ⊢
      rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
        List.length_append]
      have e1 : ((List.range l.length).filter fun p =>
          (l ++ [a]).idxOf ((l ++ [a]).getD p 0) = p) =
          (List.range l.length).filter fun p => l.idxOf (l.getD p 0) = p := by
        refine List.filter_congr fun p hp => ?_
        rw [List.mem_range] at hp
        rw [List.getD_append _ _ _ _ hp, List.idxOf_append, if_pos (getD_mem hp)]
      rw [e1, ih]
      have hins : (l ++ [a]).toFinset = insert a l.toFinset := by
        ext v; simp
      rw [hins]
      by_cases ha : a ∈ l
      · have hlt := List.idxOf_lt_length_of_mem ha
        have hne : ¬ (l ++ [a]).idxOf ((l ++ [a]).getD l.length 0) = l.length := by
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [List.idxOf_append, if_pos ha]
          omega
        rw [List.filter_cons_of_neg (by simpa using hne), Finset.insert_eq_of_mem
          (List.mem_toFinset.mpr ha)]
        simp
      · have heq : (l ++ [a]).idxOf ((l ++ [a]).getD l.length 0) = l.length := by
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [List.idxOf_append, if_neg ha]
          simp
        rw [List.filter_cons_of_pos (by simpa using heq), Finset.card_insert_of_notMem
          (by simpa using ha)]
        simp

/-! ## The instance -/

/-- **The instance of a formula**: universe the positions, set `j` the first occurrences of the
variables of clause `j`. -/
def hsOfF (α : Formula) : Instance :=
  ofPred (T α) α.length (inSetB (Firsts.firsts (litsL α)) (offL α) false)

theorem offL_getD (α : Formula) {j : ℕ} (hj : j ≤ α.length) : (offL α).getD j 0 = cOff α j := by
  simp [offL, List.getD_eq_getElem?_getD, show j < α.length + 1 by omega]

/-- Membership in a set of the instance, by the literals of the clause. -/
theorem mem_hsOfF_iff (α : Formula) {j : ℕ} (hj : j < α.length) (a : ℕ) :
    inSetB (Firsts.firsts (litsL α)) (offL α) false j a = true ↔
      ∃ l ∈ α[j], (litsL α).idxOf l.index = a := by
  rw [inSetB_iff, offL_getD α (by omega), offL_getD α hj.le, cOff_succ α hj]
  constructor
  · rintro (⟨h, -⟩ | ⟨q, hq, h1, h2⟩)
    · exact absurd h (by simp)
    · have hqT : q < T α := by
        have := cOff_mono α (show j + 1 ≤ α.length by omega)
        rw [cOff_succ α hj, cOff_length] at this; omega
      rw [firsts_getD α hqT] at h2
      have hq' : q - cOff α j < (α[j]).length := by omega
      refine ⟨α[j][q - cOff α j], List.getElem_mem _, ?_⟩
      rw [← litsL_getD α hj hq', show cOff α j + (q - cOff α j) = q by omega]
      exact h2
  · rintro ⟨l, hl, rfl⟩
    right
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hl
    have hqT : cOff α j + q < T α := by
      have := cOff_mono α (show j + 1 ≤ α.length by omega)
      rw [cOff_succ α hj, cOff_length] at this; omega
    refine ⟨cOff α j + q, by omega, by omega, ?_⟩
    rw [firsts_getD α hqT, fstL, litsL_getD α hj hq]

theorem index_mem_litsL (α : Formula) {j : ℕ} (hj : j < α.length) {l : Literal} (hl : l ∈ α[j]) :
    l.index ∈ litsL α := by
  unfold litsL
  exact List.mem_flatMap.mpr ⟨α[j], List.getElem_mem hj, List.mem_map_of_mem hl⟩

/-- A monotone formula is satisfied exactly by the sets meeting every clause. -/
theorem eval_monotone {α : Formula} (hα : IsMonotone α) (S : Finset ℕ) :
    eval α (fun i => decide (i ∈ S)) = true ↔ ∀ j, ∀ hj : j < α.length, ∃ l ∈ α[j], l.index ∈ S := by
  simp only [eval, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h j hj
    obtain ⟨l, hl, hle⟩ := h _ (List.getElem_mem hj)
    have hp := hα _ (List.getElem_mem hj) l hl
    simp [Literal.eval, hp] at hle
    exact ⟨l, hl, hle⟩
  · intro h C hC
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hC
    obtain ⟨l, hl, hS⟩ := h j hj
    have hp := hα _ (List.getElem_mem hj) l hl
    exact ⟨l, hl, by simp [Literal.eval, hp, hS]⟩

/-- **For `k` at most the number of variables, the answers agree.** -/
theorem weightSat_iff {α : Formula} (hα : IsMonotone α) {k : ℕ} (hk : k ≤ (vars α).card) :
    WeightSat α k ↔ (hsOfF α).HasHittingSet k := by
  classical
  have hDT : (vars α).card ≤ T α := by
    rw [vars_eq]; exact List.toFinset_card_le _
  rw [Compress.hasHittingSet_iff_le _ (show k ≤ T α by omega)]
  have hmem : ∀ (j : Fin (hsOfF α).m) (a : Fin (hsOfF α).n),
      a ∈ (hsOfF α).F j ↔ ∃ l ∈ α[j.val]'j.isLt, (litsL α).idxOf l.index = a := fun j a =>
    (mem_ofPred (p := inSetB (Firsts.firsts (litsL α)) (offL α) false) j a).trans
      (mem_hsOfF_iff α j.isLt a)
  constructor
  · rintro ⟨S, hSv, hc, he⟩
    rw [eval_monotone hα] at he
    refine ⟨Finset.univ.filter fun a : Fin (T α) => ∃ i ∈ S, (litsL α).idxOf i = a.val, ?_, ?_⟩
    · rw [← hc]
      calc (Finset.univ.filter fun a : Fin (T α) => ∃ i ∈ S, (litsL α).idxOf i = a.val).card
          = ((Finset.univ.filter fun a : Fin (T α) => ∃ i ∈ S, (litsL α).idxOf i = a.val).map
              Fin.valEmbedding).card := (Finset.card_map _).symm
        _ ≤ (S.image fun i => (litsL α).idxOf i).card := by
            refine Finset.card_le_card fun v hv => ?_
            obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
            obtain ⟨i, hi, hia⟩ := (Finset.mem_filter.mp ha).2
            exact Finset.mem_image.mpr ⟨i, hi, hia⟩
        _ ≤ S.card := Finset.card_image_le
    · intro j
      obtain ⟨l, hl, hS⟩ := he j.val j.isLt
      have hin := index_mem_litsL α j.isLt hl
      have hlt : (litsL α).idxOf l.index < T α := List.idxOf_lt_length_of_mem hin
      exact ⟨⟨_, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.index, hS, rfl⟩,
        (hmem j ⟨_, hlt⟩).mpr ⟨l, hl, rfl⟩⟩
  · rintro ⟨H, hc, hh⟩
    have hsub : (H.image fun a => (litsL α).getD a.val 0) ⊆ vars α := by
      intro v hv
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hv
      rw [vars_eq, List.mem_toFinset]
      exact getD_mem a.isLt
    obtain ⟨S', hS1, hS2, hS3⟩ := Finset.exists_subsuperset_card_eq hsub
      (Finset.card_image_le.trans hc) hk
    refine ⟨S', hS2, hS3, (eval_monotone hα S').mpr fun j hj => ?_⟩
    obtain ⟨a, ha, haj⟩ := hh ⟨j, hj⟩
    obtain ⟨l, hl, hla⟩ := (hmem ⟨j, hj⟩ a).mp haj
    refine ⟨l, hl, hS1 (Finset.mem_image.mpr ⟨a, ha, ?_⟩)⟩
    rw [← hla]
    exact getD_idxOf (index_mem_litsL α hj hl)

theorem not_weightSat_of_lt {α : Formula} {k : ℕ} (hk : (vars α).card < k) : ¬ WeightSat α k := by
  rintro ⟨S, hS, hc, -⟩
  have := Finset.card_le_card hS
  omega

/-! ## The reduction on words -/

/-- The fixed no-instance: an empty universe and weight `1`. -/
def noInst : Instance := ⟨0, 0, fun j => j.elim0⟩

theorem not_hasHittingSet_noInst : ¬ noInst.HasHittingSet 1 := by
  rintro ⟨H, hc, -⟩
  have : H = ∅ := Finset.eq_empty_of_forall_notMem fun a _ => a.elim0
  rw [this] at hc; simp at hc

open Classical in
/-- **The reduction.** -/
noncomputable def redWS (x : List ℕ) : List ℕ :=
  if h : ∃ p : Formula × ℕ, x = encode p.1 ++ [p.2] then
    (if (Classical.choose h).2 ≤ (vars (Classical.choose h).1).card then
      word (hsOfF (Classical.choose h).1) (Classical.choose h).2 else word noInst 1)
  else []

open Classical in
theorem redWS_word (α : Formula) (k : ℕ) :
    redWS (encode α ++ [k]) = if k ≤ (vars α).card then word (hsOfF α) k else word noInst 1 := by
  have h : ∃ p : Formula × ℕ, encode α ++ [k] = encode p.1 ++ [p.2] := ⟨(α, k), rfl⟩
  unfold redWS
  rw [dif_pos h]
  obtain ⟨e1, e2⟩ := encode_inj (Classical.choose_spec h)
  rw [← e1, ← e2]

theorem yes_iff (α : Formula) (k : ℕ) :
    (pWSat {α | IsMonotone α}).Yes (encode α ++ [k]) ↔ WeightSat α k := by
  constructor
  · rintro ⟨β, k', h, hw⟩
    obtain ⟨rfl, rfl⟩ := encode_inj h
    exact hw
  · intro h; exact ⟨α, k, rfl, h⟩

theorem isReduction : IsReduction (pWSat {α | IsMonotone α}) HittingSet redWS := by
  classical
  constructor
  · rintro x ⟨α, -, k, rfl⟩
    rw [redWS_word]
    split_ifs
    · exact word_mem_domain _ _
    · exact word_mem_domain _ _
  · rintro x ⟨α, hα, k, rfl⟩
    rw [yes_iff, redWS_word]
    split_ifs with hk
    · rw [yes_word_iff, weightSat_iff hα hk]
    · rw [yes_word_iff]
      exact iff_of_false (not_weightSat_of_lt (by omega)) not_hasHittingSet_noInst

theorem paramBounded : ParamBounded (pWSat {α | IsMonotone α}) HittingSet redWS := by
  classical
  refine ⟨Nat.succ, Computable.succ, ?_⟩
  rintro x ⟨α, -, k, rfl⟩
  rw [redWS_word]
  have hp : (pWSat {α | IsMonotone α}).param (encode α ++ [k]) = k := by simp [pWSat]
  rw [hp]
  split_ifs
  · rw [param_word]; omega
  · rw [param_word]; omega

end Lax496464Proofs.WHierarchy.HittingSet.WSHSMath
