import Lax496464.WH_D01_CliqueInW1
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! The mathematics of `p-Clique ≤fpt p-WD_clique`: the witnesses of `clique(X)` of weight `k`
in the structure of a graph are its `k`-cliques, and the map `x ↦ graphWord x ++ [k]` is a
reduction with the parameter unchanged. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.WDMath

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems Lax496464.WH_D01_CliqueInW1
open Lax271696.VertexCover
open Lax496464Proofs.WHierarchy.Logic.Words Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure

/-- What `clique(X)` says in the structure of a graph. -/
theorem sat_cliqueFormula {n : ℕ} {G : SimpleGraph (Fin n)} (S : Set (List ℕ)) (ρ : Assignment) :
    Sat (graphStructure n G) S cliqueFormula ρ ↔
      ∀ a < n, ∀ b < n, [a] ∈ S → [b] ∈ S → a ≠ b → [a, b] ∈ edgeRel n G := by
  simp only [cliqueFormula, Sat, sat_imp, graphStructure_size, List.map_cons, List.map_nil,
    graphStructure_rel_zero]
  simp only [Assignment.update, if_true, one_ne_zero, zero_ne_one, if_false]
  constructor
  · intro h a ha b hb hSa hSb hab
    exact h a ha b hb ⟨hSa, hSb, hab⟩
  · rintro h a ha b hb ⟨hSa, hSb, hab⟩
    exact h a ha b hb hSa hSb hab

/-- **The witnesses of weight `k` are the `k`-cliques.** -/
theorem clique_iff_witness (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) :
    (∃ s : Finset (Fin n), G.IsNClique k s) ↔ Witness (graphStructure n G) cliqueFormula 1 k := by
  classical
  have hfits : cliqueFormula.Fits (graphStructure n G).arities 1 := by
    simp [cliqueFormula, Formula.imp, Formula.Fits]
  unfold Witness
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨hfits, s.image fun v => [v.val], ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
      exact hs.card_eq
    · intro t ht
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨rfl, by simp⟩
    · rw [sat_cliqueFormula]
      intro a ha b hb hSa hSb hab
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.cons.injEq, and_true]
        at hSa hSb
      obtain ⟨u, hu, rfl⟩ := hSa
      obtain ⟨v, hv, rfl⟩ := hSb
      rw [pair_mem_edgeRel]
      exact ⟨u.2, v.2, hs.isClique hu hv (fun h => hab (by rw [h]))⟩
  · rintro ⟨-, S, hcard, hS, hsat⟩
    rw [sat_cliqueFormula] at hsat
    refine ⟨Finset.univ.filter fun v : Fin n => [v.val] ∈ S, ⟨?_, ?_⟩⟩
    · intro u hu v hv huv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
      obtain ⟨_, _, hadj⟩ := pair_mem_edgeRel.mp
        (hsat u u.2 v v.2 hu hv (fun h => huv (Fin.ext h)))
      exact hadj
    · rw [← hcard]
      have hS' : S = (Finset.univ.filter fun v : Fin n => [v.val] ∈ S).image fun v => [v.val] := by
        ext t
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ht
          obtain ⟨hl, hlt⟩ := hS t ht
          match t, hl with
          | [a], _ => exact ⟨⟨a, hlt a (by simp)⟩, ht, rfl⟩
        · rintro ⟨v, hv, rfl⟩; exact hv
      conv_rhs => rw [hS']
      rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

/-! ### The map on words -/

/-- **The reduction on words**: the word of the graph structure, then `k`. -/
def redWD (x : List ℕ) : List ℕ := graphWord x ++ [x.getLast?.getD 0]

theorem encodesWD_redWD {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) : EncodesWD (redWD x) (graphStructure n G) k := by
  rw [redWD, Lax496464Proofs.WHierarchy.Graphs.CsrUnique.param_eq h]
  exact encodesWD_append (encodes_graphWord_of_param h) k

/-- Step 1: construction and correctness. -/
theorem isReduction : IsReduction Clique (pWD cliqueFormula 1) redWD where
  maps_domain x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    exact ⟨_, _, encodesWD_redWD h⟩
  correct x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    rw [pWD_yes_iff _ _ (encodesWD_redWD h), ← clique_iff_witness]
    constructor
    · rintro ⟨n', G', k', h', hs⟩
      obtain rfl := Lax496464Proofs.WHierarchy.Graphs.CsrUnique.vertices_eq h h'
      obtain ⟨rfl, rfl⟩ := Lax496464Proofs.WHierarchy.Graphs.CsrUnique.graph_param_eq h h'
      exact hs
    · exact fun hs => ⟨n, G, k, h, hs⟩

/-- Step 2: the parameter is unchanged. -/
theorem paramBounded : ParamBounded Clique (pWD cliqueFormula 1) redWD := by
  refine ⟨id, Computable.id, fun x hx => ?_⟩
  obtain ⟨n, G, k, h⟩ := hx
  show (pWD cliqueFormula 1).param (redWD x) ≤ x.getLast?.getD 0
  rw [pWD_param_eq _ _ (encodesWD_redWD h), Lax496464Proofs.WHierarchy.Graphs.CsrUnique.param_eq h]

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.WDMath
