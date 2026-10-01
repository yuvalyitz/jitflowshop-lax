import Lax496464.WH_C1_GraphProblems
import Lax496464.WH_B3_LogicProblems
import Lax496464Proofs.WHierarchy.Logic.StructureCode
import Lax496464Proofs.WHierarchy.Graphs.CsrUnique
import Mathlib.Data.List.GetD

/-! A graph as a structure, and its word computed from the graph word.

A graph `G` on `n` vertices is the structure with universe `{0, …, n-1}` and one binary relation,
symbol `0`, holding `[u, v]` for every ordered pair of adjacent vertices. Its word is computed from
the CSR word `x` of the graph (followed by anything, e.g. the parameter) by listing, for every `u`
and then every `v` in increasing order, the pair `[u, v]` when `v` occurs in the block of `u`: the
adjacency lists of `x` may repeat entries, but this listing does not. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure

open Lax496464.WH_B1_Structures Lax271696.GraphEncoding Lax271696.VertexCover
open Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! ### The structure of a graph -/

/-- The edge relation of a graph, as a set of pairs. -/
noncomputable def edgeRel (n : ℕ) (G : SimpleGraph (Fin n)) : Finset (List ℕ) := by
  classical
  exact (Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2).image
    fun p => [p.1.val, p.2.val]

theorem mem_edgeRel {n : ℕ} {G : SimpleGraph (Fin n)} {t : List ℕ} :
    t ∈ edgeRel n G ↔ ∃ (a b : ℕ) (ha : a < n) (hb : b < n), t = [a, b] ∧ G.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  unfold edgeRel
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨u, v, hadj, rfl⟩
    exact ⟨u, v, u.2, v.2, rfl, hadj⟩
  · rintro ⟨a, b, ha, hb, rfl, hadj⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hadj, rfl⟩

theorem pair_mem_edgeRel {n : ℕ} {G : SimpleGraph (Fin n)} {a b : ℕ} :
    [a, b] ∈ edgeRel n G ↔ ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [mem_edgeRel]
  constructor
  · rintro ⟨a', b', ha, hb, h, hadj⟩
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ha, hb, hadj⟩
  · rintro ⟨ha, hb, hadj⟩
    exact ⟨a, b, ha, hb, rfl, hadj⟩

/-- **The structure of a graph**: universe `{0, …, n-1}`, one binary relation, the edges. -/
noncomputable def graphStructure (n : ℕ) (G : SimpleGraph (Fin n)) : Structure where
  arities := [2]
  size := n
  rel i := if i = 0 then edgeRel n G else ∅
  arity_pos := by simp
  wf i t ht := by
    by_cases hi : i = 0
    · subst hi
      simp only [if_true] at ht
      obtain ⟨a, b, ha, hb, rfl, -⟩ := mem_edgeRel.mp ht
      refine ⟨by simp, by simp, ?_⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    · simp [hi] at ht

@[simp] theorem graphStructure_arities (n : ℕ) (G : SimpleGraph (Fin n)) :
    (graphStructure n G).arities = [2] := rfl

@[simp] theorem graphStructure_size (n : ℕ) (G : SimpleGraph (Fin n)) :
    (graphStructure n G).size = n := rfl

theorem graphStructure_rel_zero (n : ℕ) (G : SimpleGraph (Fin n)) :
    (graphStructure n G).rel 0 = edgeRel n G := rfl

/-! ### The word, computed from the graph word -/

/-- The number of vertices of a graph word. -/
def nV (x : List ℕ) : ℕ := x.getD 0 0

/-- `v` occurs in the block of `u`. -/
def adjW (x : List ℕ) (u v : ℕ) : Bool :=
  (List.range (offset x (u + 1) - offset x u)).any fun t => target x (offset x u + t) == v

/-- The neighbours of `u` listed by the matrix scan: in increasing order, without repetition. -/
def rowW (x : List ℕ) (u : ℕ) : List ℕ := (List.range (nV x)).filter (adjW x u)

/-- The pairs `[u, v]` of the edge relation, in lexicographic order. -/
def pairs (x : List ℕ) : List (List ℕ) :=
  (List.range (nV x)).flatMap fun u => (rowW x u).map fun v => [u, v]

/-- **The word of the graph structure**: one symbol of arity `2`, `n` elements, the pairs. -/
def graphWord (x : List ℕ) : List ℕ := wordOf [2] (nV x) [pairs x]

theorem graphWord_eq (x : List ℕ) :
    graphWord x = [1, 2, nV x, (pairs x).length] ++ (pairs x).flatten := by
  simp [graphWord, wordOf, blockOf]

theorem pairs_nodup (x : List ℕ) : (pairs x).Nodup := by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · refine List.Nodup.map (fun a b h => by simpa using h) ?_
    exact (List.nodup_range).filter _
  · refine List.nodup_range.pairwise_of_forall_ne fun u _ u' _ huu' => ?_
    rw [Function.onFun, List.disjoint_left]
    intro t ht ht'
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp ht
    obtain ⟨v', -, h⟩ := List.mem_map.mp ht'
    simp only [List.cons.injEq, and_true] at h
    exact huu' h.1.symm

theorem mem_pairs {x : List ℕ} {t : List ℕ} :
    t ∈ pairs x ↔ ∃ u v, u < nV x ∧ v < nV x ∧ adjW x u v = true ∧ t = [u, v] := by
  unfold pairs rowW
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨u, hu, v, ⟨hv, hadj⟩, rfl⟩
    exact ⟨u, v, hu, hv, hadj, rfl⟩
  · rintro ⟨u, v, hu, hv, hadj, rfl⟩
    exact ⟨u, hu, v, ⟨hv, hadj⟩, rfl⟩

/-! ### The word of a graph instance encodes the graph structure -/

theorem getD_append_left {g : List ℕ} {k i : ℕ} (hi : i < g.length) :
    (g ++ [k]).getD i 0 = g.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The offsets of a graph are at most the number of targets. -/
theorem offset_le_last_aux {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph g n G) : ∀ d i, i + d = n → offset g i ≤ offset g n
  | 0, i, hi => by rw [show i = n by omega]
  | d + 1, i, hi => (h.offset_mono i (by omega)).trans (offset_le_last_aux h d (i + 1) (by omega))

theorem offset_le_last {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph g n G) :
    ∀ i ≤ n, offset g i ≤ offset g n :=
  fun i hi => offset_le_last_aux h (n - i) i (by omega)

variable {x g : List ℕ} {n k : ℕ} {G : SimpleGraph (Fin n)}

theorem nV_eq (hx : x = g ++ [k]) (h : EncodesGraph g n G) : nV x = n := by
  subst hx
  have hl := h.length_eq
  rw [nV, getD_append_left (by omega)]
  exact h.vertexCount_eq

theorem offset_eq (hx : x = g ++ [k]) (h : EncodesGraph g n G) {i : ℕ} (hi : i ≤ n) :
    offset x i = offset g i := by
  subst hx
  have hl := h.length_eq
  exact getD_append_left (by omega)

theorem target_eq (hx : x = g ++ [k]) (h : EncodesGraph g n G) {j : ℕ}
    (hj : j < 2 * edgeCount g) : target x j = target g j := by
  subst hx
  have hl := h.length_eq
  have hv := h.vertexCount_eq
  have hvc : vertexCount (g ++ [k]) = vertexCount g := getD_append_left (by omega)
  unfold target
  rw [hvc, getD_append_left (by omega)]

/-- **The scan finds exactly the edges.** -/
theorem adjW_iff (hx : x = g ++ [k]) (h : EncodesGraph g n G) {u v : ℕ} (hu : u < n)
    (hv : v < n) : adjW x u v = true ↔ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [h.adj_iff]
  have hlast := h.offset_last
  have hmono := offset_le_last h
  have h1 := hmono u (by omega)
  have h2 := hmono (u + 1) (by omega)
  have hle := h.offset_mono u hu
  rw [adjW, offset_eq hx h (by omega), offset_eq hx h (by omega)]
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨t, ht, he⟩
    refine ⟨offset g u + t, by omega, by omega, ?_⟩
    rw [← target_eq hx h (by omega)]; exact he
  · rintro ⟨j, hj1, hj2, he⟩
    refine ⟨j - offset g u, by omega, ?_⟩
    rw [show offset g u + (j - offset g u) = j by omega, target_eq hx h (by omega)]
    exact he

theorem pairs_toFinset (hx : x = g ++ [k]) (h : EncodesGraph g n G) :
    (pairs x).toFinset = edgeRel n G := by
  ext t
  rw [List.mem_toFinset, mem_pairs, mem_edgeRel, nV_eq hx h]
  constructor
  · rintro ⟨u, v, hu, hv, hadj, rfl⟩
    exact ⟨u, v, hu, hv, rfl, (adjW_iff hx h hu hv).mp hadj⟩
  · rintro ⟨u, v, hu, hv, rfl, hadj⟩
    exact ⟨u, v, hu, hv, (adjW_iff hx h hu hv).mpr hadj, rfl⟩

/-- **The graph word of a graph instance encodes the graph structure.** -/
theorem encodes_graphWord (hx : x = g ++ [k]) (h : EncodesGraph g n G) :
    Encodes (graphWord x) (graphStructure n G) := by
  have e : graphWord x = wordOf (graphStructure n G).arities (graphStructure n G).size [pairs x] := by
    rw [graphWord, graphStructure_arities, graphStructure_size, nV_eq hx h]
  rw [e]
  refine encodes_wordOf _ _ rfl fun i hi => ?_
  simp only [graphStructure_arities, List.length_cons, List.length_nil, zero_add,
    Nat.lt_one_iff] at hi
  subst hi
  exact ⟨pairs_nodup x, pairs_toFinset hx h⟩

theorem encodes_graphWord_of_param (h : EncodesParamInstance x n G k) :
    Encodes (graphWord x) (graphStructure n G) := by
  obtain ⟨g, hx, hg⟩ := h
  exact encodes_graphWord hx hg

/-! ### Sizes -/

theorem length_rowW_le (x : List ℕ) (u : ℕ) : (rowW x u).length ≤ nV x := by
  unfold rowW
  exact (List.length_filter_le _ _).trans (by simp)

theorem sum_le_of_forall_le : ∀ (l : List ℕ) (c : ℕ), (∀ a ∈ l, a ≤ c) → l.sum ≤ l.length * c
  | [], _, _ => by simp
  | a :: l, c, h => by
    have := sum_le_of_forall_le l c fun b hb => h b (by simp [hb])
    have := h a (by simp)
    simp only [List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]; omega

theorem length_pairs_le (x : List ℕ) : (pairs x).length ≤ nV x * nV x := by
  unfold pairs
  rw [List.length_flatMap]
  have : ∀ u ∈ List.range (nV x), ((rowW x u).map fun v => [u, v]).length ≤ nV x := by
    intro u _; simpa using length_rowW_le x u
  calc ((List.range (nV x)).map fun u => ((rowW x u).map fun v => [u, v]).length).sum
      ≤ (List.range (nV x)).length * nV x := by
        have := sum_le_of_forall_le ((List.range (nV x)).map fun u =>
          ((rowW x u).map fun v => [u, v]).length) (nV x) (by
          intro a ha
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
          exact this u hu)
        simpa using this
    _ = nV x * nV x := by simp

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
