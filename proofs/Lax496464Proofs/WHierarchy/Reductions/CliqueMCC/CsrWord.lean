import Lax888481.MulticolouredClique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD

/-!
# The Compressed Sparse Row Word of a Decidable Adjacency

For a Boolean relation `r` on `0, …, N-1` that is the adjacency of a graph `H`, the word
`[N, M, 0, psum 1, …, psum N] ++ targets`, where the targets list the neighbours of each vertex in
increasing order and `psum s` is the sum of the first `s` degrees, encodes `H` with strictly
increasing adjacency lists.

Adapted from mcc-lax (`Lax369822Proofs.WordEncodesProof`), made generic in the relation.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord

open Lax271696.GraphEncoding

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

theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-! ### The word -/

variable (r : ℕ → ℕ → Bool) (N : ℕ)

/-- The neighbours of `s`, in increasing order. -/
def nbW (s : ℕ) : List ℕ := (List.range N).filter (r s)

/-- The degree of `s`. -/
def degW (s : ℕ) : ℕ := (nbW r N s).length

/-- The prefix sum of the degrees. -/
def psum (s : ℕ) : ℕ := ((List.range s).map (degW r N)).sum

/-- The target array. -/
def tgW : List ℕ := (List.range N).flatMap (nbW r N)

/-- **The compressed sparse row word.** -/
def csrWord : List ℕ :=
  [N, psum r N N / 2, 0] ++ (List.range N).map (fun s => psum r N (s + 1)) ++ tgW r N

theorem psum_succ (s : ℕ) : psum r N (s + 1) = psum r N s + degW r N s := by
  unfold psum; rw [List.range_succ]; simp

theorem psum_mono {s t : ℕ} (h : s ≤ t) : psum r N s ≤ psum r N t := pre_mono _ h

theorem length_tgW : (tgW r N).length = psum r N N := length_flatMap_range _ _

theorem mem_nbW_lt {s t : ℕ} (h : t ∈ nbW r N s) : t < N :=
  List.mem_range.1 (List.mem_of_mem_filter h)

theorem mem_tgW_lt {t : ℕ} (h : t ∈ tgW r N) : t < N := by
  obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 h
  exact mem_nbW_lt r N hs

theorem nbW_pairwise (s : ℕ) : List.Pairwise (· < ·) (nbW r N s) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_nbW_iff {s t : ℕ} : t ∈ nbW r N s ↔ t < N ∧ r s t = true := by
  unfold nbW; rw [List.mem_filter, List.mem_range]

theorem offsets_eq :
    (List.range (N + 1)).map (psum r N) =
      0 :: (List.range N).map (fun s => psum r N (s + 1)) := by
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def, psum]

theorem length_csrWord : (csrWord r N).length = 3 + N + psum r N N := by
  simp [csrWord, length_tgW]; omega

theorem csrWord_eq : csrWord r N =
    [N, psum r N N / 2] ++ (List.range (N + 1)).map (psum r N) ++ tgW r N := by
  rw [offsets_eq]; simp [csrWord]

theorem vertexCount_csrWord : vertexCount (csrWord r N) = N := by
  simp [vertexCount, csrWord]

theorem edgeCount_csrWord : edgeCount (csrWord r N) = psum r N N / 2 := by
  simp [edgeCount, csrWord]

theorem offset_csrWord {i : ℕ} (hi : i ≤ N) : offset (csrWord r N) i = psum r N i := by
  unfold offset
  rw [csrWord_eq, List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 2 + i - 2 < N + 1 by omega)]
  simp

theorem target_csrWord (j : ℕ) : target (csrWord r N) j = (tgW r N).getD j 0 := by
  unfold target
  rw [vertexCount_csrWord, csrWord_eq, List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  congr 1; omega

theorem target_csrWord_block {s : ℕ} (hs : s < N) {j : ℕ} (h1 : psum r N s ≤ j)
    (h2 : j < psum r N (s + 1)) :
    target (csrWord r N) j = (nbW r N s).getD (j - psum r N s) 0 := by
  rw [target_csrWord, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold tgW
  rw [getElem?_flatMap_range (nbW r N) N s hs j h1 h2]
  rfl

/-! ### It encodes the graph -/

variable {r N}

theorem length_nbW_eq_degree {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    (hH : ∀ s t : Fin N, H.Adj s t ↔ r s t = true) (s : Fin N) :
    (nbW r N s).length = H.degree s := by
  classical
  have h1 : (nbW r N s).length =
      ((Finset.range N).filter (fun t => r s t = true)).card := by
    unfold nbW
    simp [Finset.card, Finset.filter, Finset.range, Multiset.range, Multiset.filter_coe]
  rw [h1, ← SimpleGraph.card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun (t : Fin N) _ => t.val)
  · intro t ht
    simp only [SimpleGraph.mem_neighborFinset] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨t.2, (hH s t).1 ht⟩
  · intro a _ b _ h; exact Fin.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    exact ⟨⟨t, ht.1⟩, by simpa using (hH s ⟨t, ht.1⟩).2 ht.2, rfl⟩

theorem psum_even {H : SimpleGraph (Fin N)} (hH : ∀ s t : Fin N, H.Adj s t ↔ r s t = true) :
    psum r N N = 2 * (psum r N N / 2) := by
  classical
  have h : psum r N N = ∑ v : Fin N, H.degree v := by
    have e : psum r N N = ∑ i ∈ Finset.range N, (nbW r N i).length := by
      unfold psum degW
      exact sum_map_range _ N
    rw [e, ← Fin.sum_univ_eq_sum_range (fun i => (nbW r N i).length) N]
    exact Finset.sum_congr rfl fun v _ => length_nbW_eq_degree hH v
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges H
  rw [h, h2]
  omega

/-- **The word encodes the graph.** -/
theorem encodesGraph {H : SimpleGraph (Fin N)} (hH : ∀ s t : Fin N, H.Adj s t ↔ r s t = true) :
    EncodesGraph (csrWord r N) N H := by
  have hT := psum_even hH
  refine ⟨vertexCount_csrWord r N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_csrWord, edgeCount_csrWord]; omega
  · rw [offset_csrWord r N (Nat.zero_le _)]; rfl
  · rw [edgeCount_csrWord, offset_csrWord r N le_rfl]; omega
  · intro i hi
    rw [offset_csrWord r N (by omega), offset_csrWord r N (by omega)]
    exact psum_mono r N (Nat.le_succ i)
  · intro j hj
    rw [edgeCount_csrWord] at hj
    have hj' : j < (tgW r N).length := by rw [length_tgW]; omega
    rw [target_csrWord, List.getD_eq_getElem _ _ hj']
    exact mem_tgW_lt r N (List.getElem_mem hj')
  · intro u v
    have hu : u.val < N := u.2
    rw [offset_csrWord r N (by omega), offset_csrWord r N (by omega), psum_succ]
    constructor
    · intro hadj
      have hv : v.val ∈ nbW r N u.val := (mem_nbW_iff r N).2 ⟨v.2, (hH u v).1 hadj⟩
      obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hv
      refine ⟨psum r N u.val + i, by omega, by unfold degW; omega, ?_⟩
      rw [target_csrWord_block r N hu (by omega) (by rw [psum_succ]; unfold degW; omega)]
      rw [show psum r N u.val + i - psum r N u.val = i by omega,
        List.getD_eq_getElem _ _ hi, hiv]
    · rintro ⟨j, h1, h2, h3⟩
      have h2' : j < psum r N (u.val + 1) := by rw [psum_succ]; omega
      rw [target_csrWord_block r N hu h1 h2'] at h3
      have hlt : j - psum r N u.val < (nbW r N u.val).length := by unfold degW at h2; omega
      rw [List.getD_eq_getElem _ _ hlt] at h3
      have hv : v.val ∈ nbW r N u.val := h3 ▸ List.getElem_mem hlt
      exact (hH u v).2 ((mem_nbW_iff r N).1 hv).2

/-- **The adjacency lists are strictly increasing.** -/
theorem sorted (u : ℕ) (hu : u < N) (t : ℕ) (h1 : offset (csrWord r N) u ≤ t)
    (h2 : t + 1 < offset (csrWord r N) (u + 1)) :
    target (csrWord r N) t < target (csrWord r N) (t + 1) := by
  rw [offset_csrWord r N (by omega)] at h1
  rw [offset_csrWord r N (by omega), psum_succ] at h2
  have e1 := target_csrWord_block r N hu h1 (by rw [psum_succ]; omega)
  have e2 := target_csrWord_block r N hu (show psum r N u ≤ t + 1 by omega)
    (by rw [psum_succ]; omega)
  rw [e1, e2]
  have hi : t - psum r N u < (nbW r N u).length := by unfold degW at h2; omega
  have hi' : t + 1 - psum r N u < (nbW r N u).length := by unfold degW at h2; omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
  exact List.pairwise_iff_getElem.1 (nbW_pairwise r N u) _ _ hi hi' (by omega)

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord
