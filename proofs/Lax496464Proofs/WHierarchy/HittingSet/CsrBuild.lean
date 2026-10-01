import Lax496464Proofs.WHierarchy.HittingSet.Form
import Lax496464.WH_C1_GraphProblems

/-! # A compressed-sparse-row word from its blocks

Given the neighbour list `g u` of every vertex `u < N`, the word `[N, M]`, the offsets
`pre g 0, …, pre g N` and the concatenated lists encodes every graph whose adjacency is membership in
the lists, provided `2 M` is the total length and every listed vertex is below `N`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.CsrBuild

open Lax271696.GraphEncoding Lax496464Proofs.WHierarchy.HittingSet.Form

/-- The word with header `[N, M]`, the offsets of the blocks `g 0, …, g (N-1)`, and the blocks. -/
def csrWord (N M : ℕ) (g : ℕ → List ℕ) : List ℕ :=
  [N, M] ++ (List.range (N + 1)).map (pre g) ++ (List.range N).flatMap g

theorem csrWord_getD_off (N M : ℕ) (g : ℕ → List ℕ) {i : ℕ} (hi : i ≤ N) :
    (csrWord N M g).getD (2 + i) 0 = pre g i := by
  unfold csrWord
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp), List.getD_append _ _ _ _
    (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, show i < N + 1 by omega]

theorem csrWord_getD_tgt (N M : ℕ) (g : ℕ → List ℕ) (j : ℕ) :
    (csrWord N M g).getD (3 + N + j) 0 = ((List.range N).flatMap g).getD j 0 := by
  unfold csrWord
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  congr 1
  simp; omega

/-- **The word of the blocks encodes the graph.** -/
theorem encodesGraph_csrWord (N M : ℕ) (g : ℕ → List ℕ) (hM : pre g N = 2 * M)
    (hlt : ∀ u < N, ∀ v ∈ g u, v < N) (G : SimpleGraph (Fin N))
    (hadj : ∀ u v : Fin N, G.Adj u v ↔ v.val ∈ g u.val) :
    EncodesGraph (csrWord N M g) N G := by
  have hoff : ∀ i ≤ N, offset (csrWord N M g) i = pre g i := fun i hi => csrWord_getD_off N M g hi
  have hvc : vertexCount (csrWord N M g) = N := by simp [vertexCount, csrWord]
  have hec : edgeCount (csrWord N M g) = M := by simp [edgeCount, csrWord]
  have htg : ∀ j, target (csrWord N M g) j = ((List.range N).flatMap g).getD j 0 := by
    intro j; unfold target; rw [hvc]; exact csrWord_getD_tgt N M g j
  refine ⟨hvc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlen : (csrWord N M g).length = 3 + N + pre g N := by
      unfold csrWord
      rw [List.length_append, List.length_append, length_flatMap_range]; simp; omega
    rw [hlen, hec, hM]
  · rw [hoff 0 (by omega), pre_zero]
  · rw [hoff N le_rfl, hec, hM]
  · intro i hi; rw [hoff i (by omega), hoff (i + 1) (by omega)]; exact pre_mono g (by omega)
  · intro j hj
    rw [hec, ← hM, ← length_flatMap_range] at hj
    obtain ⟨u, hu, q, hq, rfl⟩ := exists_block g hj
    rw [htg, getD_flatMap_range g hu hq, List.getD_eq_getElem _ _ hq]
    exact hlt u hu _ (List.getElem_mem hq)
  · intro u v
    rw [hadj, hoff u (by omega), hoff (u + 1) (by have := u.isLt; omega), pre_succ]
    constructor
    · intro hv
      obtain ⟨q, hq, hqv⟩ := List.getElem_of_mem hv
      refine ⟨pre g u + q, by omega, by omega, ?_⟩
      rw [htg, getD_flatMap_range g u.isLt hq, List.getD_eq_getElem _ _ hq, hqv]
    · rintro ⟨j, h1, h2, hj⟩
      rw [htg, show j = pre g u + (j - pre g u) by omega,
        getD_flatMap_range g u.isLt (by omega), List.getD_eq_getElem _ _ (by omega)] at hj
      rw [← hj]
      exact List.getElem_mem _

end Lax496464Proofs.WHierarchy.HittingSet.CsrBuild
