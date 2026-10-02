import Lax496464Proofs.WHierarchy.HittingSet.Compress
import Lax496464Proofs.WHierarchy.HittingSet.Words
import Lax496464Proofs.WHierarchy.Logic.StructureCode
import Lax496464.WH_E1_HittingSetInW2
import Mathlib.Tactic.IntervalCases

/-! # Hitting Set to weighted definability: the mathematics

The structure of an instance `Q` has one element per element of the universe and one per set,
`VERT` and `EDGE` telling them apart, and the incidence relation `I`: `[i, n + j] ∈ I` when `i` lies
in set `j`. A witness of weight `k` for `hsFormula` in it is exactly a hitting set of size `k`
(`witness_iff`).

The reduction applies this to the compressed instance (`Compress.compress`), whose size is
polynomial in the word; when `k > n` it writes a fixed no-instance instead. The word it writes
(`wdOut`) lists the tuples of `I` in the order of the positions of `memL`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WDMath

open Lax496464.HittingSet Lax496464.WH_C2_HittingSet
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_E1_HittingSetInW2 Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Compress Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! ## The structure of an instance -/

/-- `VERT`: the elements `0, …, n-1`. -/
def vertRel (n : ℕ) : Finset (List ℕ) := (Finset.range n).image fun i => [i]

/-- `EDGE`: the sets, as the elements `n, …, n+m-1`. -/
def edgeRel (n m : ℕ) : Finset (List ℕ) := (Finset.range m).image fun j => [n + j]

/-- `I`: element `i` lies in set `j`. -/
def incRel (Q : Instance) : Finset (List ℕ) :=
  Finset.univ.biUnion fun j : Fin Q.m => (Q.F j).image fun i => [i.val, Q.n + j.val]

/-- The relations. -/
def relOf (Q : Instance) (i : ℕ) : Finset (List ℕ) :=
  if i = 0 then vertRel Q.n else if i = 1 then edgeRel Q.n Q.m else if i = 2 then incRel Q else ∅

theorem mem_vertRel {n : ℕ} {t : List ℕ} : t ∈ vertRel n ↔ ∃ i < n, t = [i] := by
  simp [vertRel, eq_comm]

theorem mem_edgeRel {n m : ℕ} {t : List ℕ} : t ∈ edgeRel n m ↔ ∃ j < m, t = [n + j] := by
  simp [edgeRel, eq_comm]

theorem mem_incRel {Q : Instance} {t : List ℕ} :
    t ∈ incRel Q ↔ ∃ j : Fin Q.m, ∃ i ∈ Q.F j, t = [i.val, Q.n + j.val] := by
  simp [incRel, eq_comm]

/-- **The structure of an instance.** -/
def structOf (Q : Instance) : Structure where
  arities := [1, 1, 2]
  size := Q.n + Q.m
  rel := relOf Q
  arity_pos := by simp
  wf := by
    intro i t ht
    unfold relOf at ht
    split_ifs at ht with h0 h1 h2
    · subst h0
      obtain ⟨a, ha, rfl⟩ := mem_vertRel.mp ht
      refine ⟨by simp, by simp, ?_⟩
      intro b hb; simp at hb; omega
    · subst h1
      obtain ⟨a, ha, rfl⟩ := mem_edgeRel.mp ht
      refine ⟨by simp, by simp, ?_⟩
      intro b hb; simp at hb; omega
    · subst h2
      obtain ⟨j, a, -, rfl⟩ := mem_incRel.mp ht
      refine ⟨by simp, by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · have := a.isLt; omega
      · have := j.isLt; omega
    · simp at ht

@[simp] theorem structOf_rel0 (Q : Instance) : (structOf Q).rel 0 = vertRel Q.n := by unfold structOf; try rfl
@[simp] theorem structOf_rel1 (Q : Instance) : (structOf Q).rel 1 = edgeRel Q.n Q.m := by unfold structOf; try rfl
@[simp] theorem structOf_rel2 (Q : Instance) : (structOf Q).rel 2 = incRel Q := by unfold structOf; try rfl
@[simp] theorem structOf_size (Q : Instance) : (structOf Q).size = Q.n + Q.m := by unfold structOf; try rfl
@[simp] theorem structOf_arities (Q : Instance) : (structOf Q).arities = [1, 1, 2] := by simp only [structOf]

/-! ## Witnesses are hitting sets -/

theorem sat_hs (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) :
    Sat A S hsFormula ρ ↔ ∀ x < A.size, ∀ z < A.size, ∃ y < A.size,
      ([x] ∈ A.rel 1 → ([y] ∈ S ∧ [y] ∈ A.rel 0 ∧ [y, x] ∈ A.rel 2)) ∧
        ([z] ∈ S → [z] ∈ A.rel 0) := by
  simp only [hsFormula, Sat, Formula.imp, Assignment.update, List.map_cons, List.map_nil]
  simp only [↓reduceIte, OfNat.zero_ne_ofNat, zero_ne_one]
  simp only [imp_iff_not_or]
  norm_num

theorem fits_hs : hsFormula.Fits [1, 1, 2] 1 := by
  simp [hsFormula, Formula.Fits, Formula.imp]

/-- **Witnesses of `hs(X)` in the structure of `Q` are the hitting sets of `Q`.** -/
theorem witness_iff (Q : Instance) (k : ℕ) :
    Witness (structOf Q) hsFormula 1 k ↔ Q.HasHittingSet k := by
  classical
  constructor
  · rintro ⟨-, S, hcard, hS, hsat⟩
    rw [sat_hs] at hsat
    simp only [structOf_size, structOf_rel0, structOf_rel1, structOf_rel2] at hsat
    -- every tuple of `S` is `[i]` for an element `i`
    have hS' : ∀ t ∈ S, ∃ i < Q.n, t = [i] := by
      intro t ht
      obtain ⟨hl, hlt⟩ := hS t ht
      obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hl
      have hz : z < Q.n + Q.m := hlt z (by simp)
      obtain ⟨y, -, -, hv⟩ := hsat z hz z hz
      exact mem_vertRel.mp (hv (by simpa using ht))
    obtain ⟨H, hH⟩ : ∃ H : Finset (Fin Q.n), H = Finset.univ.filter fun i => [i.val] ∈ S :=
      ⟨_, rfl⟩
    have hmemH : ∀ i : Fin Q.n, i ∈ H ↔ [i.val] ∈ S := by
      intro i; rw [hH]; simp
    refine ⟨H, ?_, ?_⟩
    · have hSeq : S = H.image (fun i => [i.val]) := by
        ext t
        constructor
        · intro ht
          obtain ⟨i, hi, rfl⟩ := hS' t ht
          exact Finset.mem_image.mpr ⟨⟨i, hi⟩, (hmemH _).mpr ht, rfl⟩
        · intro ht
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
          exact (hmemH i).mp hi
      rw [← hcard, hSeq, Finset.card_image_of_injective _
        (fun a b h => by simpa [Fin.val_inj] using h)]
    · intro j
      have hx : Q.n + j.val < Q.n + Q.m := by have := j.isLt; omega
      obtain ⟨y, -, hy, -⟩ := hsat (Q.n + j.val) hx (Q.n + j.val) hx
      obtain ⟨hyS, hyV, hyI⟩ := hy (mem_edgeRel.mpr ⟨j.val, j.isLt, rfl⟩)
      obtain ⟨i, hi, hyi⟩ := mem_vertRel.mp hyV
      have hyi' : y = i := by simpa using hyi
      rw [hyi'] at hyS hyI
      obtain ⟨j', i', hi', he⟩ := mem_incRel.mp hyI
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨h1, h2⟩ := he
      have hjj : j' = j := Fin.ext (by omega)
      rw [hjj] at hi'
      refine ⟨⟨i, hi⟩, (hmemH _).mpr (by simpa using hyS), ?_⟩
      have : i' = ⟨i, hi⟩ := Fin.ext h1.symm
      rw [← this]; exact hi'
  · rintro ⟨H, hcard, hh⟩
    refine ⟨fits_hs, H.image fun i => [i.val], ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => by simpa [Fin.val_inj] using h), hcard]
    · intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      refine ⟨rfl, fun a ha => ?_⟩
      simp only [List.mem_singleton] at ha
      subst ha
      simp only [structOf_size]; have := i.isLt; omega
    · rw [sat_hs]
      simp only [structOf_size, structOf_rel0, structOf_rel1, structOf_rel2]
      intro x hx z hz
      by_cases he : [x] ∈ edgeRel Q.n Q.m
      · obtain ⟨j, hj, hxj⟩ := mem_edgeRel.mp he
        simp only [List.cons.injEq, and_true] at hxj
        subst hxj
        obtain ⟨i, hiH, hij⟩ := hh ⟨j, hj⟩
        refine ⟨i.val, by have := i.isLt; omega, fun _ => ⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
          exact ⟨i, hiH, rfl⟩
        · exact mem_vertRel.mpr ⟨i.val, i.isLt, rfl⟩
        · exact mem_incRel.mpr ⟨⟨j, hj⟩, i, hij, rfl⟩
        · intro hzS
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hzS
          obtain ⟨i', -, hi'⟩ := hzS
          exact mem_vertRel.mpr ⟨i'.val, i'.isLt, hi'.symm⟩
      · refine ⟨x, hx, fun h => absurd h he, ?_⟩
        intro hzS
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hzS
        obtain ⟨i', -, hi'⟩ := hzS
        exact mem_vertRel.mpr ⟨i'.val, i'.isLt, hi'.symm⟩

/-! ## The fixed no-instance -/

/-- A structure with the vocabulary of `hs(X)` and an empty universe. -/
def structNo : Structure where
  arities := [1, 1, 2]
  size := 0
  rel := fun _ => ∅
  arity_pos := by simp
  wf := by simp

/-- Its word, followed by the weight `1`. -/
def noWD : List ℕ := [3, 1, 1, 2, 0, 0, 0, 0, 1]

theorem encodesWD_noWD : EncodesWD noWD structNo 1 := by
  refine ⟨wordOf [1, 1, 2] 0 [[], [], []], ?_, rfl⟩
  refine encodes_wordOf structNo _ rfl fun i hi => ?_
  simp only [structNo, List.length_cons, List.length_nil] at hi
  interval_cases i <;> simp [structNo]

theorem not_witness_no : ¬ Witness structNo hsFormula 1 1 := by
  rintro ⟨-, S, hc, hS, -⟩
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hc
  obtain ⟨hl, hlt⟩ := hS t (by simp)
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hl
  have := hlt z (by simp)
  simp [structNo] at this

/-! ## The word of the compressed instance -/

/-- The tuples of `VERT`, `EDGE` and `I` of the compressed instance, in the order written. -/
def tuplesWD (P : Instance) (k : ℕ) : List (List (List ℕ)) :=
  [(List.range (NN P k)).map (fun i => [i]), (List.range P.m).map (fun j => [NN P k + j]),
    (List.range (total P)).map (fun p => [fst P p, NN P k + (ownL P).getD p 0])]

/-- **The word the reduction writes**, for `k ≤ n`. -/
noncomputable def wdOut (P : Instance) (k : ℕ) : List ℕ :=
  wordOf [1, 1, 2] (NN P k + P.m) (tuplesWD P k) ++ [kk P k]

theorem nodup_map_singleton (l : List ℕ) (hl : l.Nodup) : (l.map fun i => [i]).Nodup :=
  hl.map (fun a b h => by simpa using h)

theorem compress_n (P : Instance) (k : ℕ) : (compress P k).n = NN P k := rfl
theorem compress_m (P : Instance) (k : ℕ) : (compress P k).m = P.m := by simp only [compress]

theorem inc_toFinset (P : Instance) (k : ℕ) :
    ((List.range (total P)).map (fun p => [fst P p, NN P k + (ownL P).getD p 0])).toFinset =
      incRel (compress P k) := by
  ext t
  simp only [List.mem_toFinset, List.mem_map, List.mem_range, mem_incRel]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hf := fst_lt hp
    have ho := ownL_lt P hp
    refine ⟨⟨(ownL P).getD p 0, ho⟩, ⟨fst P p, by rw [compress_n]; unfold NN; omega⟩, ?_, rfl⟩
    exact (mem_compress_F (P := P) (k := k) ⟨_, ho⟩ _).mpr ⟨p, hp, rfl, rfl⟩
  · rintro ⟨j, a, ha, rfl⟩
    obtain ⟨p, hp, hpa, hpj⟩ := (mem_compress_F (P := P) (k := k) j a).mp ha
    exact ⟨p, hp, by rw [hpa, hpj]; rfl⟩

theorem encodes_wd (P : Instance) (k : ℕ) :
    Encodes (wordOf [1, 1, 2] (NN P k + P.m) (tuplesWD P k)) (structOf (compress P k)) := by
  refine encodes_wordOf (structOf (compress P k)) _ rfl fun i hi => ?_
  simp only [structOf_arities, List.length_cons, List.length_nil] at hi
  interval_cases i
  · refine ⟨nodup_map_singleton _ List.nodup_range, ?_⟩
    ext t; simp [tuplesWD, mem_vertRel, compress_n, eq_comm]
  · refine ⟨(List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
    ext t; simp [tuplesWD, mem_edgeRel, compress_n, compress_m, eq_comm]
  · refine ⟨?_, inc_toFinset P k⟩
    refine (List.nodup_range).map_on fun p hp p' hp' h => ?_
    simp only [List.mem_range] at hp hp'
    simp only [List.cons.injEq, and_true] at h
    exact fst_inj hp hp' (by omega) h.1

theorem encodesWD_out (P : Instance) (k : ℕ) :
    EncodesWD (wdOut P k) (structOf (compress P k)) (kk P k) :=
  ⟨_, encodes_wd P k, rfl⟩

/-! ## The reduction on words -/

open Classical in
/-- **The reduction**: on the word of `(P, k)`, the word of the compressed structure and `min k m`
when `k ≤ n`, the fixed no-instance otherwise. -/
noncomputable def redWD (x : List ℕ) : List ℕ :=
  if h : ∃ p : Instance × ℕ, x = word p.1 p.2 then
    (if (Classical.choose h).2 ≤ (Classical.choose h).1.n then
      wdOut (Classical.choose h).1 (Classical.choose h).2 else noWD)
  else []

theorem redWD_word (P : Instance) (k : ℕ) :
    redWD (word P k) = if k ≤ P.n then wdOut P k else noWD := by
  have h : ∃ p : Instance × ℕ, word P k = word p.1 p.2 := ⟨(P, k), rfl⟩
  unfold redWD
  rw [dif_pos h]
  obtain ⟨e1, e2⟩ := word_inj (Classical.choose_spec h)
  rw [← e1, ← e2]

/-- The answer of the word of a structure followed by a number is the witness question for that
structure. -/
theorem yes_iff_of_encodes {x : List ℕ} {A : Structure} {k : ℕ} (h : EncodesWD x A k) :
    (pWD hsFormula 1).Yes x ↔ Witness A hsFormula 1 k := by
  constructor
  · rintro ⟨A', k', h', hw⟩
    obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨y', hy', he⟩ := h'
    obtain ⟨-, hA, hk⟩ := encodes_prefix hy hy' he
    subst hA
    simp only [List.cons.injEq, and_true] at hk
    subst hk
    exact hw
  · intro hw; exact ⟨A, k, h, hw⟩

theorem not_hasHittingSet_of_lt {P : Instance} {k : ℕ} (h : P.n < k) : ¬ P.HasHittingSet k := by
  rintro ⟨H, hc, -⟩
  have := Finset.card_le_univ H
  simp at this; omega

theorem isReduction : IsReduction HittingSet (pWD hsFormula 1) redWD := by
  constructor
  · rintro x ⟨P, k, rfl⟩
    rw [redWD_word]
    split_ifs
    · exact ⟨_, _, encodesWD_out P k⟩
    · exact ⟨_, _, encodesWD_noWD⟩
  · rintro x ⟨P, k, rfl⟩
    rw [yes_word_iff, redWD_word]
    split_ifs with hk
    · rw [yes_iff_of_encodes (encodesWD_out P k), witness_iff, ← hasHittingSet_compress P hk]
    · rw [yes_iff_of_encodes encodesWD_noWD]
      exact iff_of_false (not_hasHittingSet_of_lt (by omega)) not_witness_no

theorem paramBounded : ParamBounded HittingSet (pWD hsFormula 1) redWD := by
  refine ⟨Nat.succ, Computable.succ, ?_⟩
  rintro x ⟨P, k, rfl⟩
  rw [param_word, redWD_word]
  split_ifs
  · simp only [pWD, wdOut, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.getD_some, kk]
    omega
  · simp [pWD, noWD]

end Lax496464Proofs.WHierarchy.HittingSet.WDMath
