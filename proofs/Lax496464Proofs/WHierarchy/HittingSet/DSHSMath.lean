import Lax496464Proofs.WHierarchy.HittingSet.SetsMath
import Lax496464Proofs.WHierarchy.HittingSet.DSMath

/-! # Dominating Set to Hitting Set: the mathematics

The closed neighbourhoods (Flum–Grohe, Example 2.7): the universe is the vertex set, and set `v` is
`N[v] = {v} ∪ N(v)`. A set of `k` vertices dominates the graph exactly when it meets every `N[v]`,
so the sizes match exactly and no case needs special treatment. The sets are read off the word:
`N[v]` holds `v` and the targets between the offsets of `v`, which is `SetsMath.inSetB` with `self`;
listing the candidates `a < n` in order makes each set sorted and without repetitions, whatever
order and repetitions the adjacency block of `v` has. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSHSMath

open Lax496464.HittingSet hiding offset member
open Lax496464.WH_C2_HittingSet Lax496464.WH_C1_GraphProblems
open Lax496464.WH_A2_FptReductions Lax271696.VertexCover Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.DSMath

/-- The number of vertices of a graph word. -/
def nX (x : List ℕ) : ℕ := x.getD 0 0

/-- The declared number of edges. -/
def mX (x : List ℕ) : ℕ := x.getD 1 0

/-- The parameter: the last entry. -/
def kX (x : List ℕ) : ℕ := x.getLast?.getD 0

/-- The offsets `0, …, n`. -/
def offX (x : List ℕ) : List ℕ := (List.range (nX x + 1)).map fun i => x.getD (2 + i) 0

/-- The target array. -/
def valX (x : List ℕ) : List ℕ := (List.range (2 * mX x)).map fun q => x.getD (3 + nX x + q) 0

/-- **The instance of the closed neighbourhoods.** -/
def hsOf (x : List ℕ) : Instance := ofPred (nX x) (nX x) (inSetB (valX x) (offX x) true)

/-- **The reduction.** -/
def redDH (x : List ℕ) : List ℕ := word (hsOf x) (kX x)

/-! ## On a graph word -/

section

variable {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}

theorem getD_x (hx : x = g ++ [k]) {i : ℕ} (hi : i < g.length) : x.getD i 0 = g.getD i 0 := by
  subst hx; rw [List.getD_append _ _ _ _ hi]

theorem nX_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) : nX x = n := by
  unfold nX; rw [getD_x hx (by have := hg.length_eq; omega)]; exact hg.vertexCount_eq

theorem mX_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) : mX x = edgeCount g := by
  unfold mX; rw [getD_x hx (by have := hg.length_eq; omega)]; rfl

theorem kX_eq (hx : x = g ++ [k]) : kX x = k := by subst hx; simp [kX]

theorem offX_getD (hx : x = g ++ [k]) (hg : EncodesGraph g n G) {i : ℕ} (hi : i ≤ n) :
    (offX x).getD i 0 = offset g i := by
  rw [offX, nX_eq hx hg]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : i < n + 1),
    Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, getD_x hx (by have := hg.length_eq; omega)]; rfl

theorem valX_getD (hx : x = g ++ [k]) (hg : EncodesGraph g n G) {q : ℕ}
    (hq : q < 2 * edgeCount g) : (valX x).getD q 0 = target g q := by
  rw [valX, mX_eq hx hg, nX_eq hx hg]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
    Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, getD_x hx (by have := hg.length_eq; omega), target,
    hg.vertexCount_eq]

theorem offset_mono_add (hg : EncodesGraph g n G) (i : ℕ) :
    ∀ d, i + d ≤ n → offset g i ≤ offset g (i + d)
  | 0, _ => le_rfl
  | d + 1, h => (offset_mono_add hg i d (by omega)).trans
      (by rw [← Nat.add_assoc]; exact hg.offset_mono (i + d) (by omega))

theorem offset_le_last (hg : EncodesGraph g n G) {i : ℕ} (hi : i ≤ n) :
    offset g i ≤ 2 * edgeCount g := by
  rw [← hg.offset_last]
  have := offset_mono_add hg i (n - i) (by omega)
  rwa [show i + (n - i) = n by omega] at this

/-- **Membership in `hsOf x` is the closed neighbourhood.** -/
theorem mem_hsOf_iff (hx : x = g ++ [k]) (hg : EncodesGraph g n G) (v a : Fin n) :
    inSetB (valX x) (offX x) true v a = true ↔ a = v ∨ G.Adj a v := by
  rw [inSetB_iff, offX_getD hx hg (by have := v.isLt; omega), offX_getD hx hg (le_of_lt v.isLt),
    G.adj_comm, hg.adj_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨q, hq, h1, h2⟩)
    · exact Or.inl (Fin.ext h)
    · right
      refine ⟨q, h1, hq, ?_⟩
      rw [← valX_getD hx hg (lt_of_lt_of_le hq (offset_le_last hg v.isLt)), h2]
  · rintro (h | ⟨q, h1, hq, h2⟩)
    · exact Or.inl ⟨rfl, by rw [h]⟩
    · right
      refine ⟨q, hq, h1, ?_⟩
      rw [valX_getD hx hg (lt_of_lt_of_le hq (offset_le_last hg v.isLt)), h2]

end

/-- **The answer is that of the graph word.** -/
theorem hasHittingSet_hsOf {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    (hsOf x).HasHittingSet k ↔ ∃ s : Finset (Fin n), s.card = k ∧ Dominates G s := by
  have hn := nX_eq hx hg
  subst hn
  have hmem : ∀ v a : Fin (nX x),
      a ∈ (hsOf x).F v ↔ a = v ∨ G.Adj a v := fun v a =>
    (mem_ofPred (p := inSetB (valX x) (offX x) true) v a).trans (mem_hsOf_iff hx hg v a)
  constructor
  · rintro ⟨H, hc, hh⟩
    refine ⟨H, hc, fun v => ?_⟩
    obtain ⟨a, ha, hav⟩ := hh v
    rcases (hmem v a).mp hav with rfl | h
    · exact Or.inl ha
    · exact Or.inr ⟨a, ha, h⟩
  · rintro ⟨s, hc, hd⟩
    refine ⟨s, hc, fun v => ?_⟩
    rcases hd v with h | ⟨u, hu, h⟩
    · exact ⟨v, h, (hmem v v).mpr (Or.inl rfl)⟩
    · exact ⟨u, hu, (hmem v u).mpr (Or.inr h)⟩

theorem isReduction : IsReduction DominatingSet HittingSet redDH := by
  constructor
  · intro x _; exact word_mem_domain _ _
  · rintro x ⟨n, G, k, g, hx, hg⟩
    rw [yes_iff_of_encodes ⟨g, hx, hg⟩, redDH, yes_word_iff, kX_eq hx, hasHittingSet_hsOf hx hg]

theorem paramBounded : ParamBounded DominatingSet HittingSet redDH := by
  refine ⟨id, Computable.id, ?_⟩
  rintro x ⟨n, G, k, g, hx, hg⟩
  rw [redDH, param_word, kX_eq hx]
  subst hx; simp [DominatingSet]

end Lax496464Proofs.WHierarchy.HittingSet.DSHSMath
