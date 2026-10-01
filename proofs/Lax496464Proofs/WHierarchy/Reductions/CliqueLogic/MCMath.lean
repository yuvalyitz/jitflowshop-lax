import Lax496464.WH_D02_CliqueInA1
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.WDMath
import Lax496464Proofs.WHierarchy.ComputableBounds
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-! The mathematics of `p-Clique ≤fpt p-MC(Σ_1)`.

The sentence `clique_k = ∃x_0 … ∃x_{k-1} ⋀_{i<j<k} (¬ x_i = x_j ∧ E x_i x_j)` is written with the
conjunction as a right-nested chain ending in `x_0 = x_0` (which also makes `clique_1` the sentence
`∃x_0 x_0 = x_0`). For `k ≥ 1` it holds in the structure of a graph exactly when the graph has a
`k`-clique. The two cases where it cannot be used go to fixed instances: `k = 0` (every graph has a
`0`-clique, but no `Σ_1`-sentence of this syntax holds in the empty structure) to a fixed
yes-instance, and `k > n` (no `k`-clique) to a fixed no-instance, which keeps the formula of the
main case of size `O(n²)`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax271696.VertexCover
open Lax496464Proofs.WHierarchy.Logic.Words Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure

/-! ### The sentence -/

/-- `¬ x_i = x_j ∧ E x_i x_j`. -/
def pairItem (i j : ℕ) : Formula := .and (.neg (.eq i j)) (.rel 0 [i, j])

/-- The pairs `i < j < k`, in lexicographic order. -/
def pairList (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun i => ((List.range k).filter fun j => i < j).map fun j => (i, j)

/-- The right-nested conjunction of the pair items, ending in `x_0 = x_0`. -/
def chain : List (ℕ × ℕ) → Formula
  | [] => .eq 0 0
  | p :: ps => .and (pairItem p.1 p.2) (chain ps)

/-- **`clique_k`.** -/
def cliqueSent (k : ℕ) : Formula := Formula.exBlock (List.range k) (chain (pairList k))

theorem mem_pairList {k : ℕ} {p : ℕ × ℕ} : p ∈ pairList k ↔ p.1 < p.2 ∧ p.2 < k := by
  obtain ⟨i, j⟩ := p
  simp only [pairList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', ⟨hj', hij⟩, rfl, rfl⟩; exact ⟨hij, hj'⟩
  · rintro ⟨hij, hj⟩; exact ⟨i, by omega, j, ⟨hj, hij⟩, rfl, rfl⟩

theorem length_pairList_le (k : ℕ) : (pairList k).length ≤ k * k := by
  unfold pairList
  rw [List.length_flatMap]
  have := sum_le_of_forall_le ((List.range k).map fun i =>
    (((List.range k).filter fun j => i < j).map fun j => (i, j)).length) k (by
    intro a ha
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp))
  simpa using this

/-- The code of an item. -/
def itemEnc (i j : ℕ) : List ℕ := [4, 4, 3, 2, i, j, 0, 0, 2, i, j]

theorem encode_chain : ∀ ps : List (ℕ × ℕ),
    (chain ps).encode = ps.flatMap (fun p => itemEnc p.1 p.2) ++ [2, 0, 0]
  | [] => rfl
  | p :: ps => by
    simp [chain, Formula.encode, pairItem, encode_chain ps, itemEnc]

/-- The pair part of the code, as the nested scan writes it. -/
def pairsEnc (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun i => (List.range k).flatMap fun j => if i < j then itemEnc i j else []

theorem flatMap_pairList (k : ℕ) :
    (pairList k).flatMap (fun p => itemEnc p.1 p.2) = pairsEnc k := by
  unfold pairList pairsEnc
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun i _ => ?_
  rw [List.flatMap_map]
  induction (List.range k) with
  | nil => rfl
  | cons j l ih =>
    by_cases h : i < j
    · simp [h, ih]
    · simp [h, ih]

/-- The quantifier part of the code. -/
def quantEnc (k : ℕ) : List ℕ := (List.range k).flatMap fun i => [6, i]

/-- **The code of `clique_k`**: the quantifiers, the pair items, `x_0 = x_0`. -/
theorem encode_cliqueSent (k : ℕ) :
    (cliqueSent k).encode = quantEnc k ++ pairsEnc k ++ [2, 0, 0] := by
  rw [cliqueSent, encode_exBlock, encode_chain, flatMap_pairList, quantEnc, List.append_assoc]

theorem size_chain : ∀ ps : List (ℕ × ℕ), (chain ps).size = 9 * ps.length + 3
  | [] => rfl
  | p :: ps => by simp [chain, Formula.size, pairItem, size_chain ps]; ring

theorem size_cliqueSent (k : ℕ) : (cliqueSent k).size ≤ 10 * (k + 1) ^ 2 := by
  rw [cliqueSent, size_exBlock, size_chain]
  have := length_pairList_le k
  simp only [List.length_range]
  nlinarith

theorem isQF_chain : ∀ ps : List (ℕ × ℕ), (chain ps).IsQF
  | [] => trivial
  | _ :: ps => ⟨⟨trivial, trivial⟩, isQF_chain ps⟩

theorem noSetVar_chain : ∀ ps : List (ℕ × ℕ), (chain ps).NoSetVar
  | [] => trivial
  | _ :: ps => ⟨⟨trivial, trivial⟩, noSetVar_chain ps⟩

theorem fits_chain (ar : List ℕ) (har : ar = [2]) : ∀ ps : List (ℕ × ℕ), (chain ps).Fits ar 0
  | [] => trivial
  | _ :: ps => ⟨⟨trivial, by subst har; simp [Formula.Fits]⟩, fits_chain ar har ps⟩

theorem freeVars_chain : ∀ ps : List (ℕ × ℕ),
    ∀ v ∈ (chain ps).freeVars, v = 0 ∨ ∃ p ∈ ps, v = p.1 ∨ v = p.2
  | [] => by simp [chain, Formula.freeVars]
  | p :: ps => by
    intro v hv
    simp only [chain, pairItem, Formula.freeVars, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, List.toFinset_cons, List.toFinset_nil, insert_empty_eq] at hv
    rcases hv with ((h | h) | (h | h)) | h
    · exact Or.inr ⟨p, by simp, Or.inl h⟩
    · exact Or.inr ⟨p, by simp, Or.inr h⟩
    · exact Or.inr ⟨p, by simp, Or.inl h⟩
    · exact Or.inr ⟨p, by simp, Or.inr h⟩
    · rcases freeVars_chain ps v h with h | ⟨q, hq, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by simp [hq], h⟩

theorem isSentence_cliqueSent {k : ℕ} (hk : 1 ≤ k) : IsSentence (cliqueSent k) := by
  refine isSentence_exBlock fun v hv => ?_
  rw [List.mem_range]
  rcases freeVars_chain _ v hv with rfl | ⟨p, hp, h⟩
  · omega
  · have := mem_pairList.mp hp; omega

theorem isSigma_cliqueSent (k : ℕ) : IsSigma 1 (cliqueSent k) :=
  isSigma_one_exBlock (isQF_chain _) _

theorem noSetVar_cliqueSent (k : ℕ) : (cliqueSent k).NoSetVar :=
  (noSetVar_exBlock _ _).mpr (noSetVar_chain _)

/-- What the chain says. -/
theorem sat_chain {A : Structure} {S : Set (List ℕ)} {ρ : Assignment} :
    ∀ ps : List (ℕ × ℕ), Sat A S (chain ps) ρ ↔
      ∀ p ∈ ps, ρ p.1 ≠ ρ p.2 ∧ [ρ p.1, ρ p.2] ∈ A.rel 0
  | [] => by simp [chain, Sat]
  | p :: ps => by
    simp only [chain, pairItem, Sat, sat_chain ps, List.map_cons, List.map_nil, List.mem_cons,
      forall_eq_or_imp]

/-- **`clique_k` holds in the structure of a graph iff it has a `k`-clique**, for `k ≥ 1`. -/
theorem clique_iff_sat (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) :
    (∃ s : Finset (Fin n), G.IsNClique k s) ↔
      Sat (graphStructure n G) ∅ (cliqueSent k) (fun _ => 0) := by
  classical
  rw [cliqueSent, sat_exBlock]
  simp only [sat_chain, List.mem_range, graphStructure_size, graphStructure_rel_zero, mem_pairList]
  constructor
  · rintro ⟨s, hs⟩
    let e := s.orderEmbOfFin hs.card_eq
    refine ⟨fun v => if h : v < k then (e ⟨v, h⟩).val else 0, fun v hv => by simp [hv],
      fun v hv => by simp [hv], ?_⟩
    rintro ⟨i, j⟩ ⟨hij, hj⟩
    simp only [show i < k by omega, hj, dite_true]
    have hne : e ⟨i, by omega⟩ ≠ e ⟨j, hj⟩ := fun h => by
      have := congrArg Fin.val (e.injective h); simp at this; omega
    refine ⟨fun h => hne (Fin.ext h), ?_⟩
    rw [pair_mem_edgeRel]
    exact ⟨(e _).2, (e _).2, hs.isClique (s.orderEmbOfFin_mem hs.card_eq _)
      (s.orderEmbOfFin_mem hs.card_eq _) hne⟩
  · rintro ⟨ρ, -, hlt, hpair⟩
    have hinj : Set.InjOn ρ (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (hpair (i, j) ⟨h, hj⟩).1 hij
      · exact (hpair (j, i) ⟨h, hi⟩).1 hij.symm
    refine ⟨Finset.univ.filter fun u : Fin n => ∃ i < k, ρ i = u.val, ⟨?_, ?_⟩⟩
    · intro u hu v hv huv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
      obtain ⟨i, hi, hui⟩ := hu
      obtain ⟨j, hj, hvj⟩ := hv
      have hij : i ≠ j := fun h => huv (Fin.ext (by rw [← hvj, ← hui, h]))
      have hu' : u = ⟨ρ i, hlt i hi⟩ := Fin.ext hui.symm
      have hv' : v = ⟨ρ j, hlt j hj⟩ := Fin.ext hvj.symm
      subst hu' hv'
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · obtain ⟨_, _, hadj⟩ := pair_mem_edgeRel.mp (hpair (i, j) ⟨h, hj⟩).2
        exact hadj
      · obtain ⟨_, _, hadj⟩ := pair_mem_edgeRel.mp (hpair (j, i) ⟨h, hi⟩).2
        exact hadj.symm
    · have hmap : (Finset.univ.filter fun u : Fin n => ∃ i < k, ρ i = u.val).map
          Fin.valEmbedding = (Finset.range k).image ρ := by
        ext a
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨u, ⟨i, hi, h⟩, rfl⟩; exact ⟨i, hi, h⟩
        · rintro ⟨i, hi, rfl⟩; exact ⟨⟨ρ i, hlt i hi⟩, ⟨i, hi, rfl⟩, rfl⟩
      rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_image_of_injOn hinj,
        Finset.card_range]

/-- **`clique_k` holds in the structure of a graph iff it has a `k`-clique**, for `k ≥ 1`. -/
theorem clique_iff_models (n : ℕ) (G : SimpleGraph (Fin n)) {k : ℕ} (hk : 1 ≤ k) :
    (∃ s : Finset (Fin n), G.IsNClique k s) ↔ Models (graphStructure n G) (cliqueSent k) := by
  rw [models_iff_of_sentence (isSentence_cliqueSent hk) (fun _ => 0), clique_iff_sat]
  have hfits : (cliqueSent k).Fits (graphStructure n G).arities 0 :=
    (fits_exBlock _ _ _ _).mpr (fits_chain _ rfl _)
  exact ⟨fun h => ⟨hfits, noSetVar_cliqueSent _, h⟩, fun h => h.2.2⟩

/-! ### The fixed instances -/

/-- The structure with no symbols and `m` elements. -/
def emptyStructure (m : ℕ) : Structure where
  arities := []
  size := m
  rel _ := ∅
  arity_pos := by simp
  wf := by simp

theorem encodes_emptyStructure (m : ℕ) : Encodes [0, m] (emptyStructure m) :=
  ⟨[], rfl, by simp [emptyStructure], rfl⟩

/-- The fixed yes-instance: one element, `∃x_0 x_0 = x_0`. -/
def yesWord : List ℕ := [0, 1] ++ (cliqueSent 1).encode

/-- The fixed no-instance: no element, `∃x_0 x_0 = x_0`. -/
def noWord : List ℕ := [0, 0] ++ (cliqueSent 1).encode

theorem cliqueSent_one : cliqueSent 1 = .ex 0 (.eq 0 0) := rfl

theorem yesWord_eq : yesWord = [0, 1, 6, 0, 2, 0, 0] := rfl

theorem noWord_eq : noWord = [0, 0, 6, 0, 2, 0, 0] := rfl

theorem models_one_iff (m : ℕ) : Models (emptyStructure m) (cliqueSent 1) ↔ 1 ≤ m := by
  rw [models_iff_of_sentence (isSentence_cliqueSent le_rfl) (fun _ => 0), cliqueSent_one]
  have hs : Sat (emptyStructure m) ∅ (.ex 0 (.eq 0 0)) (fun _ => 0) ↔ ∃ a, a < m ∧ True := by
    simp only [Sat, emptyStructure, and_true]
  rw [hs]
  exact ⟨fun ⟨_, ⟨a, ha, _⟩⟩ => by omega, fun h => ⟨trivial, trivial, 0, h, trivial⟩⟩

/-! ### The map on words -/

/-- The parameter of a graph word. -/
def kOf (x : List ℕ) : ℕ := x.getLast?.getD 0

/-- **The reduction on words.** -/
def redMC (x : List ℕ) : List ℕ :=
  if kOf x = 0 then yesWord
  else if nV x < kOf x then noWord
  else graphWord x ++ (cliqueSent (kOf x)).encode

theorem redMC_encodes {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) :
    (k = 0 ∧ EncodesMC (redMC x) (emptyStructure 1) (cliqueSent 1)) ∨
    (k ≠ 0 ∧ n < k ∧ EncodesMC (redMC x) (emptyStructure 0) (cliqueSent 1)) ∨
    (k ≠ 0 ∧ k ≤ n ∧ EncodesMC (redMC x) (graphStructure n G) (cliqueSent k)) := by
  have hk : kOf x = k := Lax496464Proofs.WHierarchy.Graphs.CsrUnique.param_eq h
  have hn : nV x = n := by obtain ⟨g, hx, hg⟩ := h; exact nV_eq hx hg
  unfold redMC
  rw [hk, hn]
  by_cases h0 : k = 0
  · left; rw [if_pos h0]; exact ⟨h0, encodesMC_append (encodes_emptyStructure 1) _⟩
  · rw [if_neg h0]
    by_cases hnk : n < k
    · right; left; rw [if_pos hnk]; exact ⟨h0, hnk, encodesMC_append (encodes_emptyStructure 0) _⟩
    · right; right; rw [if_neg hnk]
      exact ⟨h0, by omega, encodesMC_append (encodes_graphWord_of_param h) _⟩

/-- Step 1: construction and correctness. -/
theorem isReduction : IsReduction Clique (pMC {φ | IsSigma 1 φ}) redMC where
  maps_domain x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    rcases redMC_encodes h with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩
    · exact ⟨_, _, he, isSigma_cliqueSent _, noSetVar_cliqueSent _⟩
    · exact ⟨_, _, he, isSigma_cliqueSent _, noSetVar_cliqueSent _⟩
    · exact ⟨_, _, he, isSigma_cliqueSent _, noSetVar_cliqueSent _⟩
  correct x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    have hyes : Clique.Yes x ↔ ∃ s : Finset (Fin n), G.IsNClique k s := by
      constructor
      · rintro ⟨n', G', k', h', hs⟩
        obtain rfl := Lax496464Proofs.WHierarchy.Graphs.CsrUnique.vertices_eq h h'
        obtain ⟨rfl, rfl⟩ := Lax496464Proofs.WHierarchy.Graphs.CsrUnique.graph_param_eq h h'
        exact hs
      · exact fun hs => ⟨n, G, k, h, hs⟩
    rw [hyes]
    rcases redMC_encodes h with ⟨rfl, he⟩ | ⟨-, hnk, he⟩ | ⟨h0, -, he⟩
    · rw [pMC_yes_iff _ he, models_one_iff]
      exact ⟨fun _ => le_rfl, fun _ => ⟨∅, by simp⟩⟩
    · rw [pMC_yes_iff _ he, models_one_iff]
      refine ⟨fun ⟨s, hs⟩ => ?_, fun h => absurd h (by omega)⟩
      have := hs.card_eq ▸ Finset.card_le_univ s
      simp at this; omega
    · rw [pMC_yes_iff _ he]
      exact clique_iff_models n G (by omega)

/-- The bound on the new parameter. -/
def gMC (k : ℕ) : ℕ := 10 * (k + 1) ^ 2

theorem computable_gMC : Computable gMC := by
  have h := Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const 10)
    (Lax496464Proofs.WHierarchy.ComputableBounds.computable_pow 2
      (Lax496464Proofs.WHierarchy.ComputableBounds.computable_add Computable.id (Computable.const 1)))
  exact h

/-- Step 2: the new parameter is at most `10 (k + 1)²`. -/
theorem paramBounded : ParamBounded Clique (pMC {φ | IsSigma 1 φ}) redMC := by
  refine ⟨gMC, computable_gMC, fun x hx => ?_⟩
  obtain ⟨n, G, k, h⟩ := hx
  show mcParam (redMC x) ≤ gMC (x.getLast?.getD 0)
  rw [Lax496464Proofs.WHierarchy.Graphs.CsrUnique.param_eq h]
  have h1 : (cliqueSent 1).size ≤ gMC k := by
    have : (cliqueSent 1).size = 5 := rfl
    have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [‹(cliqueSent 1).size = 5›, gMC]; omega
  rcases redMC_encodes h with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩
  · rw [mcParam_eq he]; exact h1
  · rw [mcParam_eq he]; exact h1
  · rw [mcParam_eq he]; exact size_cliqueSent k

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath
