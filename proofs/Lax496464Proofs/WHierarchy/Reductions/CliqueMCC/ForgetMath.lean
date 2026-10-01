import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Common

/-! # Multicoloured Clique to p-Clique: forget the colours (construction and correctness)

The word of a Multicoloured Clique instance is a graph block, one colour per vertex, and the number
of colours. The reduction keeps the graph block and the number of colours, and drops the colours:
the result presents the same graph with the parameter `k`. The graph block declares its own length
in its first two entries, so the map is `x ↦ take (3 + n + 2m) x ++ [last x]`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetMath

open Lax888481.MulticolouredClique Lax271696.GraphEncoding Lax271696.VertexCover
open Lax496464.WH_C1_GraphProblems Lax496464.WH_A2_FptReductions

/-- The length of the graph block a word declares: two header entries, `n + 1` offsets, `2m`
targets. -/
def blockLen (x : List ℕ) : ℕ := 3 + x.getD 0 0 + 2 * x.getD 1 0

/-- **The reduction**: the graph block followed by the last entry, the number of colours. -/
def forget (x : List ℕ) : List ℕ := x.take (blockLen x) ++ [x.getLast?.getD 0]

private lemma getD_prefix {g r : List ℕ} {i : ℕ} (hi : i < g.length) :
    (g ++ r).getD i 0 = g.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The graph block of a word of Multicoloured Clique is its prefix of the declared length. -/
theorem blockLen_eq {x : List ℕ} {G : Instance} {g : List ℕ}
    (hx : x = g ++ (List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours])
    (hg : EncodesGraph g G.vertices G.graph) : blockLen x = g.length := by
  have hl := hg.length_eq
  have hx' : x = g ++ ((List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours]) := by
    rw [hx, List.append_assoc]
  unfold blockLen
  rw [hx', getD_prefix (by omega), getD_prefix (by omega)]
  have h0 : g.getD 0 0 = G.vertices := hg.vertexCount_eq
  have h1 : g.getD 1 0 = edgeCount g := rfl
  rw [h0, h1, hl]

theorem forget_eq {x : List ℕ} {G : Instance} {g : List ℕ}
    (hx : x = g ++ (List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours])
    (hg : EncodesGraph g G.vertices G.graph) : forget x = g ++ [G.colours] := by
  unfold forget
  rw [blockLen_eq hx hg]
  have hx' : x = g ++ ((List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours]) := by
    rw [hx, List.append_assoc]
  rw [hx', List.take_left]
  rw [← List.append_assoc]
  simp

/-- The result presents the graph of the instance with the parameter `k`. -/
theorem forget_encodes {x : List ℕ} {G : Instance} (h : EncodesInstance x G) :
    EncodesParamInstance (forget x) G.vertices G.graph G.colours := by
  obtain ⟨g, hx, hg, -⟩ := h
  exact ⟨g, forget_eq hx hg, hg⟩

theorem forget_isReduction :
    IsReduction Lax888481.MulticolouredClique.problem Clique forget where
  maps_domain x hx := by
    obtain ⟨G, hG⟩ := hx
    exact ⟨_, _, _, forget_encodes hG⟩
  correct x hx := by
    obtain ⟨G, hG⟩ := hx
    rw [MccUnique.yes_iff hG, Common.clique_yes_iff (forget_encodes hG)]
    exact Common.hasMulticolouredClique_iff G

theorem param_forget (x : List ℕ) :
    Clique.param (forget x) = Lax888481.MulticolouredClique.problem.param x := by
  show (forget x).getLast?.getD 0 = x.getLast?.getD 0
  simp [forget]

theorem forget_paramBounded :
    ParamBounded Lax888481.MulticolouredClique.problem Clique forget :=
  ⟨id, Computable.id, fun x _ => by rw [param_forget]; rfl⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetMath
