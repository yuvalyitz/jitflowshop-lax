import Lax496464.WH_C1_GraphProblems

/-! A word presenting a graph with a parameter determines the number of vertices, the graph and the
parameter. -/

namespace Lax496464Proofs.WHierarchy.Graphs.CsrUnique

open Lax271696.GraphEncoding Lax271696.VertexCover

theorem encodesGraph_graph_eq {g : List ℕ} {n : ℕ} {G G' : SimpleGraph (Fin n)}
    (h : EncodesGraph g n G) (h' : EncodesGraph g n G') : G = G' := by
  ext u v
  rw [h.adj_iff, h'.adj_iff]

/-- The split of a word into graph block and parameter. -/
theorem split_eq {x g g' : List ℕ} {k k' : ℕ} (h : x = g ++ [k]) (h' : x = g' ++ [k']) :
    g = g' ∧ k = k' := by
  subst h
  have := List.append_inj h' (by
    have := congrArg List.length h'
    simp at this ⊢; omega)
  simp at this
  exact ⟨this.1, this.2⟩

/-- The number of vertices is determined. -/
theorem vertices_eq {x : List ℕ} {n n' : ℕ} {G : SimpleGraph (Fin n)} {G' : SimpleGraph (Fin n')}
    {k k' : ℕ} (h : EncodesParamInstance x n G k) (h' : EncodesParamInstance x n' G' k') :
    n = n' := by
  obtain ⟨g, hx, hg⟩ := h
  obtain ⟨g', hx', hg'⟩ := h'
  obtain ⟨rfl, -⟩ := split_eq hx hx'
  rw [← hg.vertexCount_eq, hg'.vertexCount_eq]

/-- On the same number of vertices, the graph and the parameter are determined. -/
theorem graph_param_eq {x : List ℕ} {n : ℕ} {G G' : SimpleGraph (Fin n)} {k k' : ℕ}
    (h : EncodesParamInstance x n G k) (h' : EncodesParamInstance x n G' k') :
    G = G' ∧ k = k' := by
  obtain ⟨g, hx, hg⟩ := h
  obtain ⟨g', hx', hg'⟩ := h'
  obtain ⟨rfl, rfl⟩ := split_eq hx hx'
  exact ⟨encodesGraph_graph_eq hg hg', rfl⟩

/-- The parameter of a graph word is its `k`. -/
theorem param_eq {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) : x.getLast?.getD 0 = k := by
  obtain ⟨g, rfl, -⟩ := h
  simp

end Lax496464Proofs.WHierarchy.Graphs.CsrUnique
