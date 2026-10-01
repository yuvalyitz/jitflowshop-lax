import Lax496464.WH_C1_GraphProblems
import Lax496464Proofs.WHierarchy.Graphs.CsrUnique
import Mathlib.Data.List.GetD

/-! # The complement map on graph words: definitions and the encoding of the complement

`complWord x` reads the word `x` as a CSR graph with a parameter (`n` = entry 0, offsets from entry 2,
targets from entry `3 + n`, parameter = last entry) and writes the CSR word of the complement graph:
the block of `u` lists, in increasing order, the vertices `v ≠ u` not in the block of `u` in `x`.
On a word presenting `(G, k)` this is a word presenting `(Gᶜ, k)` (`encodes_complWord`). -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math

open Lax271696.GraphEncoding Lax271696.VertexCover

/-- The number of vertices of a word: entry `0`. -/
def nOf (x : List ℕ) : ℕ := x.getD 0 0

/-- Offset `i` of a word: entry `2 + i`. -/
def offAt (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- Target `j` of a word: entry `3 + n + j`. -/
def tgtAt (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + nOf x + j) 0

/-- The parameter of a word: its last entry. -/
def kOf (x : List ℕ) : ℕ := x.getLast?.getD 0

/-- `v` is listed in the block of `u`. -/
def inBlock (x : List ℕ) (u v : ℕ) : Bool :=
  (List.range (offAt x (u + 1))).any fun j => decide (offAt x u ≤ j) && decide (tgtAt x j = v)

theorem inBlock_iff {x : List ℕ} {u v : ℕ} :
    inBlock x u v = true ↔ ∃ j, offAt x u ≤ j ∧ j < offAt x (u + 1) ∧ tgtAt x j = v := by
  simp only [inBlock, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, h2, h1, h3⟩
  · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, h2, h1, h3⟩

/-- Adjacency in the complement: different vertices, not listed. -/
def adjW (x : List ℕ) (u v : ℕ) : Bool := decide (u ≠ v) && !inBlock x u v

/-- The block of `u` in the complement word. -/
def nbW (x : List ℕ) (u : ℕ) : List ℕ := (List.range (nOf x)).filter (adjW x u)

/-- The degree of `u` in the complement. -/
def degW (x : List ℕ) (u : ℕ) : ℕ := (nbW x u).length

/-- The prefix sums of the degrees: the offsets of the complement word. -/
def psum (x : List ℕ) (s : ℕ) : ℕ := ((List.range s).map (degW x)).sum

/-- The offsets of the complement word. -/
def offs (x : List ℕ) : List ℕ := (List.range (nOf x + 1)).map (psum x)

/-- The targets of the complement word. -/
def tgs (x : List ℕ) : List ℕ := (List.range (nOf x)).flatMap (nbW x)

/-- The CSR word of the complement. -/
def graphWord (x : List ℕ) : List ℕ := [nOf x, psum x (nOf x) / 2] ++ offs x ++ tgs x

/-- **The map of both reductions**: the complement graph with the same parameter. -/
def complWord (x : List ℕ) : List ℕ := graphWord x ++ [kOf x]

theorem kOf_complWord (x : List ℕ) : kOf (complWord x) = kOf x := by
  simp [kOf, complWord]

/-! ### Sums of degrees -/

theorem psum_succ (x : List ℕ) (s : ℕ) : psum x (s + 1) = psum x s + degW x s := by
  unfold psum; rw [List.range_succ]; simp

theorem psum_zero (x : List ℕ) : psum x 0 = 0 := rfl

theorem psum_mono (x : List ℕ) {s t : ℕ} (h : s ≤ t) : psum x s ≤ psum x t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [psum_succ]; omega

theorem length_tgs (x : List ℕ) : (tgs x).length = psum x (nOf x) := by
  unfold tgs psum
  rw [List.length_flatMap]
  rfl

theorem length_flatMap_range (x : List ℕ) (u : ℕ) :
    ((List.range u).flatMap (nbW x)).length = psum x u := by
  unfold psum
  rw [List.length_flatMap]
  rfl

theorem mem_nbW {x : List ℕ} {u v : ℕ} : v ∈ nbW x u ↔ v < nOf x ∧ adjW x u v = true := by
  simp [nbW]

theorem lt_of_mem_tgs {x : List ℕ} {v : ℕ} (h : v ∈ tgs x) : v < nOf x := by
  simp only [tgs, List.mem_flatMap] at h
  obtain ⟨u, -, hu⟩ := h
  exact (mem_nbW.mp hu).1

/-- The block of `u` inside the targets. -/
theorem tgs_split (x : List ℕ) {u : ℕ} (hu : u < nOf x) :
    ∃ C, tgs x = (List.range u).flatMap (nbW x) ++ (nbW x u ++ C) := by
  have hn : nOf x = (u + 1) + (nOf x - (u + 1)) := by omega
  refine ⟨((List.range (nOf x - (u + 1))).map (fun i => u + 1 + i)).flatMap (nbW x), ?_⟩
  unfold tgs
  rw [hn, List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append]
  simp [← hn]

theorem tgs_getD_block (x : List ℕ) {u i : ℕ} (hu : u < nOf x) (hi : i < degW x u) :
    (tgs x).getD (psum x u + i) 0 = (nbW x u).getD i 0 := by
  obtain ⟨C, hC⟩ := tgs_split x hu
  rw [hC, ← length_flatMap_range x u]
  unfold degW at hi
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

/-! ### Evenness of the degree sum of a symmetric irreflexive relation -/

section Even

variable (r : ℕ → ℕ → Bool)

/-- `Σ_{u<N} |{v < N : r u v}|`. -/
def tot (N : ℕ) : ℕ := ((List.range N).map fun u => ((List.range N).filter (r u)).length).sum

/-- `Σ_{u<N} |{v < u : r u v}|`. -/
def low (N : ℕ) : ℕ := ((List.range N).map fun u => ((List.range u).filter (r u)).length).sum

theorem length_filter_range_succ (p : ℕ → Bool) (N : ℕ) :
    ((List.range (N + 1)).filter p).length =
      ((List.range N).filter p).length + if p N then 1 else 0 := by
  rw [List.range_succ, List.filter_append]
  by_cases h : p N = true <;> simp [h]

theorem sum_indicator (p : ℕ → Bool) (N : ℕ) :
    ((List.range N).map fun u => if p u then 1 else 0).sum = ((List.range N).filter p).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [length_filter_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem tot_eq_two_mul_low (N : ℕ) (hsym : ∀ u v, u < N → v < N → r u v = r v u)
    (hirr : ∀ u, r u u = false) : tot r N = 2 * low r N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have ih' := ih (fun u v hu hv => hsym u v (by omega) (by omega))
    have h1 : tot r (N + 1) = tot r N + ((List.range N).map fun u => if r u N then 1 else 0).sum +
        ((List.range (N + 1)).filter (r N)).length := by
      unfold tot
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [← List.range_succ]
      have : ((List.range N).map fun u => ((List.range (N + 1)).filter (r u)).length) =
          (List.range N).map fun u => ((List.range N).filter (r u)).length +
            if r u N then 1 else 0 := by
        refine List.map_congr_left fun u _ => ?_
        exact length_filter_range_succ (r u) N
      rw [this, List.sum_map_add]
    have h2 : ((List.range N).map fun u => if r u N then 1 else 0).sum =
        ((List.range N).filter (r N)).length := by
      rw [← sum_indicator]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      rw [hsym u N (by simp at hu; omega) (by omega)]
    have h3 : ((List.range (N + 1)).filter (r N)).length = ((List.range N).filter (r N)).length := by
      rw [length_filter_range_succ, hirr]; simp
    have h4 : low r (N + 1) = low r N + ((List.range N).filter (r N)).length := by
      unfold low
      rw [List.range_succ, List.map_append, List.sum_append]
      simp
    rw [h1, h2, h3, h4, ih']
    omega

end Even

/-! ### Words presenting a graph -/

section Dom

variable {x g : List ℕ} {n k : ℕ} {G : SimpleGraph (Fin n)}

theorem getD_of_lt (hx : x = g ++ [k]) {i : ℕ} (hi : i < g.length) : x.getD i 0 = g.getD i 0 := by
  subst hx
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]

theorem length_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    x.length = 4 + n + 2 * edgeCount g := by
  subst hx; have := hg.length_eq; simp; omega

theorem nOf_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) : nOf x = n := by
  have := hg.length_eq
  unfold nOf
  rw [getD_of_lt hx (by omega)]
  exact hg.vertexCount_eq

theorem kOf_eq (hx : x = g ++ [k]) : kOf x = k := by
  subst hx; simp [kOf]

theorem offAt_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) {i : ℕ} (hi : i ≤ n) :
    offAt x i = offset g i := by
  have := hg.length_eq
  unfold offAt offset
  rw [getD_of_lt hx (by omega)]

theorem offset_le_offset (hg : EncodesGraph g n G) {i i' : ℕ} (h : i ≤ i') (h' : i' ≤ n) :
    offset g i ≤ offset g i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t hle ih => exact (ih (by omega)).trans (hg.offset_mono t (by omega))

theorem offset_le_last (hg : EncodesGraph g n G) {i : ℕ} (hi : i ≤ n) :
    offset g i ≤ 2 * edgeCount g := by
  rw [← hg.offset_last]; exact offset_le_offset hg hi le_rfl

theorem tgtAt_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) {j : ℕ}
    (hj : j < 2 * edgeCount g) : tgtAt x j = target g j := by
  have := hg.length_eq
  unfold tgtAt target
  rw [nOf_eq hx hg, hg.vertexCount_eq, getD_of_lt hx (by omega)]

theorem inBlock_iff_adj (hx : x = g ++ [k]) (hg : EncodesGraph g n G) (u v : Fin n) :
    inBlock x u v = true ↔ G.Adj u v := by
  have hu := u.2
  have hlast := offset_le_last hg (i := u + 1) (by omega)
  rw [inBlock_iff, hg.adj_iff, offAt_eq hx hg (by omega), offAt_eq hx hg (by omega)]
  constructor
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨j, h1, h2, by rw [← tgtAt_eq hx hg (by omega)]; exact h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨j, h1, h2, by rw [tgtAt_eq hx hg (by omega)]; exact h3⟩

theorem adjW_iff (hx : x = g ++ [k]) (hg : EncodesGraph g n G) (u v : Fin n) :
    adjW x u v = true ↔ Gᶜ.Adj u v := by
  rw [SimpleGraph.compl_adj, ← inBlock_iff_adj hx hg u v]
  simp [adjW, Fin.val_ne_iff]

theorem adjW_symm (hx : x = g ++ [k]) (hg : EncodesGraph g n G) {u v : ℕ} (hu : u < n)
    (hv : v < n) : adjW x u v = adjW x v u := by
  have h1 := adjW_iff hx hg ⟨u, hu⟩ ⟨v, hv⟩
  have h2 := adjW_iff hx hg ⟨v, hv⟩ ⟨u, hu⟩
  simp only at h1 h2
  rw [Bool.eq_iff_iff, h1, h2]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem adjW_irrefl (x : List ℕ) (u : ℕ) : adjW x u u = false := by simp [adjW]

theorem psum_even (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    psum x (nOf x) = 2 * (psum x (nOf x) / 2) := by
  have hn := nOf_eq hx hg
  have h : psum x (nOf x) = tot (adjW x) (nOf x) := rfl
  rw [h, tot_eq_two_mul_low (adjW x) (nOf x)
    (fun u v hu hv => adjW_symm hx hg (by omega) (by omega)) (adjW_irrefl x)]
  omega

end Dom

/-! ### The complement word -/

theorem graphWord_getD_off (x : List ℕ) {i : ℕ} (hi : i ≤ nOf x) :
    (graphWord x).getD (2 + i) 0 = psum x i := by
  have hlen : i < (offs x).length := by simp [offs]; omega
  rw [show 2 + i = i + 1 + 1 by omega]
  simp only [graphWord, List.cons_append, List.nil_append, List.getD_cons_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hlen]
  simp [offs, show i < nOf x + 1 by omega]

theorem graphWord_getD_tgt (x : List ℕ) (j : ℕ) :
    (graphWord x).getD (3 + nOf x + j) 0 = (tgs x).getD j 0 := by
  have hlen : (offs x).length = nOf x + 1 := by simp [offs]
  rw [show 3 + nOf x + j = (nOf x + 1 + j) + 1 + 1 by omega]
  simp only [graphWord, List.cons_append, List.nil_append, List.getD_cons_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]

theorem vertexCount_graphWord (x : List ℕ) : vertexCount (graphWord x) = nOf x := by
  simp [vertexCount, graphWord]

theorem edgeCount_graphWord (x : List ℕ) : edgeCount (graphWord x) = psum x (nOf x) / 2 := by
  simp [edgeCount, graphWord]

theorem encodesGraph_graphWord {x g : List ℕ} {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hx : x = g ++ [k]) (hg : EncodesGraph g n G) : EncodesGraph (graphWord x) n Gᶜ := by
  have hn := nOf_eq hx hg
  have hev := psum_even hx hg
  have hoff : ∀ i ≤ n, offset (graphWord x) i = psum x i := fun i hi =>
    graphWord_getD_off x (by omega)
  have htgt : ∀ j, target (graphWord x) j = (tgs x).getD j 0 := fun j => by
    unfold target; rw [vertexCount_graphWord]; exact graphWord_getD_tgt x j
  refine ⟨by rw [vertexCount_graphWord, hn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [edgeCount_graphWord]
    have := length_tgs x
    simp [graphWord, offs]
    omega
  · rw [hoff 0 (by omega)]; rfl
  · rw [hoff n le_rfl, edgeCount_graphWord, ← hn]; exact hev
  · intro i hi
    rw [hoff i (by omega), hoff (i + 1) (by omega)]
    exact psum_mono x (by omega)
  · intro j hj
    rw [htgt]
    have hl : j < (tgs x).length := by
      rw [length_tgs]; rw [edgeCount_graphWord] at hj; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, ← hn]
    exact lt_of_mem_tgs (List.getElem_mem hl)
  · intro u v
    have hu := u.2
    rw [hoff u (by omega), hoff (u + 1) (by omega), psum_succ, ← adjW_iff hx hg]
    constructor
    · intro h
      have hm : (v : ℕ) ∈ nbW x u := mem_nbW.mpr ⟨by rw [hn]; exact v.2, h⟩
      obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hm
      refine ⟨psum x u + i, by omega, by unfold degW; omega, ?_⟩
      rw [htgt, tgs_getD_block x (by omega) hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, Option.getD_some, hiv]
    · rintro ⟨j, h1, h2, h3⟩
      have hi : j - psum x u < degW x u := by omega
      rw [htgt, show j = psum x u + (j - psum x u) by omega, tgs_getD_block x (by omega) hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h3
      have hm := List.getElem_mem (l := nbW x u) hi
      rw [h3] at hm
      exact (mem_nbW.mp hm).2

/-- **The complement word presents the complement graph, with the same parameter.** -/
theorem encodes_complWord {x : List ℕ} {n k : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesParamInstance x n G k) : EncodesParamInstance (complWord x) n Gᶜ k := by
  obtain ⟨g, hx, hg⟩ := h
  refine ⟨graphWord x, ?_, encodesGraph_graphWord hx hg⟩
  rw [complWord, kOf_eq hx]

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math
