import Lax496464.WH_F4_IndependentSetToMcc
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The word encodes the multicoloured graph

The proof of `WH_F4_IndependentSetToMcc.word_encodes`, with the facts about the word (length, targets,
adjacency) used by the other modules.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof

open Lax762056.GraphEncoding (Instance)
open Lax496464 Lax496464.WH_F2_MccConstruction

/-! ### Blocks of a `flatMap` over `range` -/

/-- The sum of the lengths of the first `s` lists `f 0, …, f (s-1)`. -/
def pre (f : ℕ → List ℕ) (s : ℕ) : ℕ := ((List.range s).map fun r => (f r).length).sum

theorem pre_succ (f : ℕ → List ℕ) (s : ℕ) : pre f (s + 1) = pre f s + (f s).length := by
  simp [pre, List.sum_range_succ]

theorem pre_mono (f : ℕ → List ℕ) {a b : ℕ} (h : a ≤ b) : pre f a ≤ pre f b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => rw [pre_succ]; omega

theorem length_flatMap_range (f : ℕ → List ℕ) (N : ℕ) :
    ((List.range N).flatMap f).length = pre f N := by
  simp [List.length_flatMap, pre]

/-- Position `j` inside the block of `s` of `flatMap f (range N)` is the corresponding position
of `f s`. -/
theorem getElem?_flatMap_range (f : ℕ → List ℕ) (N : ℕ) :
    ∀ s < N, ∀ j, pre f s ≤ j → j < pre f (s + 1) →
      ((List.range N).flatMap f)[j]? = (f s)[j - pre f s]? := by
  induction N with
  | zero => intro s hs; omega
  | succ N ih =>
    intro s hs j h1 h2
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hsN : s < N
    · have hlen : ((List.range N).flatMap f).length = pre f N := length_flatMap_range f N
      have : pre f (s + 1) ≤ pre f N := pre_mono f hsN
      rw [List.getElem?_append_left (by omega)]
      exact ih s hsN j h1 h2
    · have hsN' : s = N := by omega
      subst hsN'
      have hlen : ((List.range s).flatMap f).length = pre f s := length_flatMap_range f s
      rw [List.getElem?_append_right (by omega), hlen]

/-! ### The graph and the numbered vertices -/

variable (I : Instance)

theorem order_pos_of_lt {s : ℕ} (hs : s < size I) : 0 < I.order := by
  unfold size at hs
  rcases Nat.eq_zero_or_pos I.order with h | h
  · rw [h] at hs; simp at hs
  · exact h

/-- The adjacency test of the word is the adjacency of the multicoloured graph. -/
theorem adjB_iff_adj {s t : ℕ} (hs : s < size I) (ht : t < size I) :
    adjB I s t = true ↔
      (WH_F2_MccConstruction.graph I).Adj (⟨s, hs⟩ : Fin (I.threshold * I.order)) ⟨t, ht⟩ := by
  have hn := order_pos_of_lt I hs
  have hsm : s % I.order < I.order := Nat.mod_lt _ hn
  have htm : t % I.order < I.order := Nat.mod_lt _ hn
  have hG : adjG I (s % I.order) (t % I.order) = false ↔
      ¬ I.graph.Adj ⟨s % I.order, hsm⟩ ⟨t % I.order, htm⟩ := by
    unfold adjG
    simp [hsm, htm]
  simp only [adjB, decide_eq_true_eq, WH_F2_MccConstruction.graph, WH_F2_MccConstruction.Adj,
    finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat, ne_eq]
  constructor
  · rintro ⟨_, _, h1, h2, h3⟩
    refine ⟨?_, ?_, hG.1 h3⟩
    · intro h; apply h1; exact congrArg Fin.val h
    · intro h; apply h2; exact congrArg Fin.val h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hs, ht, ?_, ?_, hG.2 h3⟩
    · intro h; apply h1; exact Fin.ext h
    · intro h; apply h2; exact Fin.ext h

theorem mem_neighbours_iff {s t : ℕ} (hs : s < size I) :
    t ∈ neighbours I s ↔ ∃ ht : t < size I,
      (WH_F2_MccConstruction.graph I).Adj (⟨s, hs⟩ : Fin (I.threshold * I.order)) ⟨t, ht⟩ := by
  unfold neighbours
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨ht, h⟩; exact ⟨ht, (adjB_iff_adj I hs ht).1 h⟩
  · rintro ⟨ht, h⟩; exact ⟨ht, (adjB_iff_adj I hs ht).2 h⟩

theorem mem_neighbours_lt {s t : ℕ} (h : t ∈ neighbours I s) : t < size I := by
  unfold neighbours at h
  exact List.mem_range.1 (List.mem_of_mem_filter h)

theorem neighbours_pairwise (s : ℕ) : List.Pairwise (· < ·) (neighbours I s) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- Every entry of the target array is a vertex. -/
theorem mem_targets_lt {t : ℕ} (h : t ∈ targets I) : t < size I := by
  unfold targets at h
  obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 h
  exact mem_neighbours_lt I hs

theorem length_neighbours {s : ℕ} (hs : s < size I) :
    (neighbours I s).length =
      by classical exact (WH_F2_MccConstruction.graph I).degree (⟨s, hs⟩ : Fin (I.threshold * I.order)) := by
  classical
  have h1 : (neighbours I s).length = ((Finset.range (size I)).filter (fun t => adjB I s t = true)).card := by
    unfold neighbours
    simp [Finset.card, Finset.filter, Finset.range, Multiset.range, Multiset.filter_coe]
  rw [h1, ← SimpleGraph.card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun (t : Fin (I.threshold * I.order)) _ => t.val)
  · intro t ht
    simp only [SimpleGraph.mem_neighborFinset] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨t.2, (adjB_iff_adj I hs t.2).2 ht⟩
  · intro a _ b _ h; exact Fin.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    exact ⟨⟨t, ht.1⟩, by simpa using (adjB_iff_adj I hs ht.1).1 ht.2, rfl⟩

theorem length_targets_eq_sum :
    (targets I).length =
      by classical exact ∑ v : Fin (I.threshold * I.order), (WH_F2_MccConstruction.graph I).degree v := by
  classical
  unfold targets
  rw [length_flatMap_range]
  have h : pre (neighbours I) (size I) = ∑ i ∈ Finset.range (size I), (neighbours I i).length := by
    unfold pre
    induction size I with
    | zero => simp
    | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]
  rw [h, ← Fin.sum_univ_eq_sum_range (fun i => (neighbours I i).length) (size I)]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact length_neighbours I v.2

/-- The target array has even length (each edge is listed from both of its endpoints). -/
theorem length_targets_eq_two_mul : (targets I).length = 2 * ((targets I).length / 2) := by
  classical
  have h := length_targets_eq_sum I
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges (WH_F2_MccConstruction.graph I)
  rw [h, h2]
  omega

theorem length_offsets : (offsets I).length = size I + 1 := by simp [offsets]

/-- The offsets are the prefix sums of the degrees. -/
theorem offsets_eq : offsets I = (List.range (size I + 1)).map (pre (neighbours I)) := rfl

/-- The block of numbers of the compressed sparse row encoding. -/
noncomputable def block : List ℕ := [size I, (targets I).length / 2] ++ offsets I ++ targets I

theorem length_block : (block I).length = 3 + size I + (targets I).length := by
  simp [block, length_offsets]
  omega

theorem offset_block {i : ℕ} (hi : i ≤ size I) :
    Lax271696.GraphEncoding.offset (block I) i = pre (neighbours I) i := by
  unfold Lax271696.GraphEncoding.offset block
  rw [List.getD_append _ _ _ _ (by simp [length_offsets]; omega),
    List.getD_append_right _ _ _ _ (by simp)]
  rw [offsets_eq]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i < size I + 1 by omega)]
  simp

theorem target_block (j : ℕ) :
    Lax271696.GraphEncoding.target (block I) j = (targets I).getD j 0 := by
  unfold Lax271696.GraphEncoding.target
  have hv : Lax271696.GraphEncoding.vertexCount (block I) = size I := by
    simp [Lax271696.GraphEncoding.vertexCount, block]
  rw [hv]
  unfold block
  rw [List.getD_append_right _ _ _ _ (by simp [length_offsets]; omega)]
  simp [length_offsets]
  rw [show 3 + size I + j - (size I + 1 + 1 + 1) = j by omega]

theorem target_block_block {s : ℕ} (hs : s < size I) {j : ℕ}
    (h1 : pre (neighbours I) s ≤ j) (h2 : j < pre (neighbours I) (s + 1)) :
    Lax271696.GraphEncoding.target (block I) j =
      (neighbours I s).getD (j - pre (neighbours I) s) 0 := by
  have hT : pre (neighbours I) (s + 1) ≤ (targets I).length := by
    unfold targets; rw [length_flatMap_range]; exact pre_mono _ hs
  rw [target_block I _, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold targets
  rw [getElem?_flatMap_range (neighbours I) (size I) s hs j h1 h2]

theorem colours_eq :
    List.ofFn (fun v : Fin (I.threshold * I.order) => ((finProdFinEquiv.symm v).1 : ℕ)) =
      colours I := by
  apply List.ext_getElem
  · simp [colours, size]
  · intro i h1 h2
    simp [colours, finProdFinEquiv_symm_apply, Fin.divNat]

theorem word_eq_block : word I = block I ++ colours I ++ [I.threshold] := by
  simp [word, block, List.append_assoc]

theorem pre_size : pre (neighbours I) (size I) = (targets I).length := by
  unfold targets; rw [length_flatMap_range]

theorem encodesGraph :
    Lax271696.GraphEncoding.EncodesGraph (block I) (WH_F2_MccConstruction.construct I).vertices
      (WH_F2_MccConstruction.construct I).graph := by
  have hT := length_targets_eq_two_mul I
  have hedge : Lax271696.GraphEncoding.edgeCount (block I) = (targets I).length / 2 := by
    simp [Lax271696.GraphEncoding.edgeCount, block]
  have hvc : Lax271696.GraphEncoding.vertexCount (block I) = size I := by
    simp [Lax271696.GraphEncoding.vertexCount, block]
  refine ⟨hvc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (block I).length = 3 + size I + 2 * _
    rw [length_block, hedge]; omega
  · rw [offset_block I (Nat.zero_le _)]; simp [pre]
  · show Lax271696.GraphEncoding.offset (block I) (size I) = _
    rw [hedge, offset_block I le_rfl, pre_size]; omega
  · intro i hi
    have hi : i < size I := hi
    rw [offset_block I (by omega), offset_block I (by omega)]
    exact pre_mono _ (Nat.le_succ i)
  · intro j hj
    rw [hedge] at hj
    have hj' : j < (targets I).length := by omega
    rw [target_block I j, List.getD_eq_getElem _ _ hj']
    exact mem_targets_lt I (List.getElem_mem hj')
  · intro u v
    have hu : u.val < size I := u.2
    rw [offset_block I (by omega), offset_block I (by omega), pre_succ]
    constructor
    · intro hadj
      have hv : v.val ∈ neighbours I u.val :=
        (mem_neighbours_iff I hu).2 ⟨v.2, hadj⟩
      obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hv
      refine ⟨pre (neighbours I) u.val + i, by omega, by omega, ?_⟩
      rw [target_block_block I hu (by omega) (by rw [pre_succ]; omega)]
      rw [show pre (neighbours I) u.val + i - pre (neighbours I) u.val = i by omega,
        List.getD_eq_getElem _ _ hi, hiv]
    · rintro ⟨j, h1, h2, h3⟩
      have h2' : j < pre (neighbours I) (u.val + 1) := by rw [pre_succ]; omega
      rw [target_block_block I hu h1 h2'] at h3
      have hlt : j - pre (neighbours I) u.val < (neighbours I u.val).length := by omega
      rw [List.getD_eq_getElem _ _ hlt] at h3
      have hv : v.val ∈ neighbours I u.val := h3 ▸ List.getElem_mem hlt
      obtain ⟨_, h⟩ := (mem_neighbours_iff I hu).1 hv
      exact h

theorem sortedBlocks (u : ℕ) (hu : u < (WH_F2_MccConstruction.construct I).vertices) (t : ℕ)
    (h1 : Lax271696.GraphEncoding.offset (block I) u ≤ t)
    (h2 : t + 1 < Lax271696.GraphEncoding.offset (block I) (u + 1)) :
    Lax271696.GraphEncoding.target (block I) t < Lax271696.GraphEncoding.target (block I) (t + 1) := by
  have hu' : u < size I := hu
  rw [offset_block I (by omega)] at h1
  rw [offset_block I (by omega), pre_succ] at h2
  have e1 := target_block_block I hu' h1 (by rw [pre_succ]; omega)
  have e2 := target_block_block I hu' (show pre (neighbours I) u ≤ t + 1 by omega)
    (by rw [pre_succ]; omega)
  rw [e1, e2]
  have hi : t - pre (neighbours I) u < (neighbours I u).length := by omega
  have hi' : t + 1 - pre (neighbours I) u < (neighbours I u).length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
  exact List.pairwise_iff_getElem.1 (neighbours_pairwise I u) _ _ hi hi' (by omega)

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.word_encodes
---
**The word encodes the construction.** The word is the compressed sparse row block (the header
`[N, M]`, the prefix sums of the degrees, the concatenated increasing neighbour lists), the
colours `⌊s / n⌋`, and `k`; the block encodes the multicoloured graph, the length of the
target array being even by the degree-sum formula, and each block is strictly increasing.
-/
theorem word_encodes_proved (I : Instance) :
    Lax888481.MulticolouredClique.EncodesInstance (WH_F2_MccConstruction.word I)
      (WH_F2_MccConstruction.construct I) := by
  refine ⟨block I, ?_, encodesGraph I, sortedBlocks I⟩
  rw [word_eq_block]
  have := colours_eq I
  simp only [WH_F2_MccConstruction.construct]
  rw [this]

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.word_encodes := word_encodes_proved


end Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof
