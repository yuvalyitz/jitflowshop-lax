import Lax496464.WH_D12_MulticolouredClique
import Lax496464Proofs.WHierarchy.Graphs.CsrUnique
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.MccUnique

/-! Facts shared by the two reductions between p-Clique and Multicoloured Clique: the yes-instances
of p-Clique on a word that presents a known graph, and the multicoloured cliques of an instance as
the cliques of size the number of colours. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Common

open Lax888481.MulticolouredClique Lax271696.GraphEncoding Lax271696.VertexCover
open Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Graphs

/-- On a word presenting `G` and `k`, p-Clique asks for a `k`-clique of `G`. -/
theorem clique_yes_iff {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) :
    Clique.Yes x ↔ ∃ s : Finset (Fin n), G.IsNClique k s := by
  constructor
  · rintro ⟨n', G', k', h', s, hs⟩
    obtain rfl := CsrUnique.vertices_eq h h'
    obtain ⟨rfl, rfl⟩ := CsrUnique.graph_param_eq h h'
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨n, G, k, h, s, hs⟩

/-- **A multicoloured clique is a clique with as many vertices as there are colours**: adjacent
vertices have different colours, so such a clique has one vertex of each colour. -/
theorem hasMulticolouredClique_iff (G : Instance) :
    G.HasMulticolouredClique ↔ ∃ s : Finset (Fin G.vertices), G.graph.IsNClique G.colours s := by
  classical
  constructor
  · rintro ⟨f, hf, hadj⟩
    have hinj : Function.Injective f := by
      intro c c' h
      rw [← hf c, ← hf c', h]
    refine ⟨Finset.univ.image f, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, by rw [Finset.card_image_of_injective _ hinj]; simp⟩
    intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨c', rfl⟩ := hb
    exact hadj c c' fun h => hab (by rw [h])
  · rintro ⟨s, hs⟩
    let col : s → Fin G.colours := fun a => G.colour a
    have hinj : Function.Injective col := by
      intro a b h
      by_contra hne
      have hne' : (a : Fin G.vertices) ≠ b := fun h' => hne (Subtype.ext h')
      exact G.adj_colour_ne _ _ (hs.1 a.2 b.2 hne') h
    have hb : Function.Bijective col :=
      (Fintype.bijective_iff_injective_and_card col).mpr ⟨hinj, by simp [hs.card_eq]⟩
    let e := Equiv.ofBijective col hb
    refine ⟨fun c => (e.symm c : Fin G.vertices), fun c => ?_, fun c c' hcc => ?_⟩
    · have := Equiv.ofBijective_apply_symm_apply col hb c
      exact this
    · have hne : e.symm c ≠ e.symm c' := fun h => hcc (e.symm.injective h)
      exact hs.1 (e.symm c).2 (e.symm c').2 fun h => hne (Subtype.ext h)

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Common
