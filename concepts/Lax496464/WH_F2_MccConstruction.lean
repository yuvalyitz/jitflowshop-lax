import Lax496464.WH_F1_IndependentSetMatrix
import Lax762056.GraphEncoding
import Lax888481.MulticolouredClique
import Mathlib.Logic.Equiv.Fin.Basic

/-!
---
title: The multicoloured graph of an Independent Set instance
type: definition
---
Let $G$ be a graph on $n$ vertices and $k \in \mathbb N$. The **multicoloured graph** of $(G, k)$
has the $kn$ vertices $(c, v)$ for $c < k$ and $v$ a vertex of $G$, the vertex $(c, v)$ coloured
$c$. Two vertices $(c, u)$ and $(c', v)$ are adjacent when

* $c \ne c'$,
* $u \ne v$, and
* $uv$ is not an edge of $G$.

A multicoloured clique chooses one vertex $(c, v_c)$ of each colour, pairwise adjacent; the
vertices $v_0, \dots, v_{k-1}$ are then $k$ distinct pairwise non-adjacent vertices of $G$. This is
the construction of [FHRV09, Lemma 1] applied to the complement of $G$ (see also
[CFK+15, Theorem 13.7]).

The **reduction** `reduce` maps the word of an instance $(G, k)$ of `WH_F1_IndependentSetMatrix` to
the word of its multicoloured graph, and every other word to the empty word.

# Formalization notes

**Vertex numbering.** The vertex $(c, v)$ is numbered $v + nc$ (`finProdFinEquiv`), so the
vertices are listed colour by colour, and the vertex $s$ is $(\lfloor s/n \rfloor, s \bmod n)$.

**The word** is in the format of `Lax888481.MulticolouredClique`: a compressed sparse row block,
one colour per vertex, and the number of colours. The block lists the number $N = kn$ of vertices,
the number of edges, the $N + 1$ offsets, and the targets, which are the neighbours of each vertex
in increasing order. The colours follow, and the word ends with $k$. The word is given explicitly,
as the unique word of this form, so that the running time of the reduction is a statement about a
single output.

**The map on words.** `reduce` is a function on all words. On the word of an instance it takes the
instance chosen by `Classical.choose`; this instance is unique, since the encoding is injective.
The empty word is a no-instance of Multicoloured Clique.
-/

namespace Lax496464.WH_F2_MccConstruction

open Lax762056.GraphEncoding (Instance)

-- The multicoloured graph

/-- The copies `(c, u)` and `(c', v)` are adjacent. -/
def Adj (I : Instance) (a b : Fin I.threshold × Fin I.order) : Prop :=
  a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ ¬ I.graph.Adj a.2 b.2

/-- The graph on the `k · n` copies, the copy `(c, v)` being the vertex `v + n c`. -/
def graph (I : Instance) : SimpleGraph (Fin (I.threshold * I.order)) where
  Adj s t := Adj I (finProdFinEquiv.symm s) (finProdFinEquiv.symm t)
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, fun h => h3 h.symm⟩⟩
  loopless := ⟨fun _ ⟨h1, _, _⟩ => h1 rfl⟩

/-- The Multicoloured Clique instance: `k` colours, `k · n` vertices, the copy `(c, v)`
coloured `c`. -/
def construct (I : Instance) : Lax888481.MulticolouredClique.Instance where
  colours := I.threshold
  vertices := I.threshold * I.order
  graph := graph I
  colour s := (finProdFinEquiv.symm s).1
  adj_colour_ne _ _ h := h.1

-- The word of the multicoloured graph

open Classical in
/-- Adjacency in `G` of the numbers `u` and `v`; false unless both are vertices. -/
noncomputable def adjG (I : Instance) (u v : ℕ) : Bool :=
  decide (∃ (hu : u < I.order) (hv : v < I.order), I.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩)

/-- The number `k · n` of vertices of the multicoloured graph. -/
def size (I : Instance) : ℕ := I.threshold * I.order

/-- Adjacency in the multicoloured graph of the numbers `s` and `t`; false unless both are
vertices. -/
noncomputable def adjB (I : Instance) (s t : ℕ) : Bool :=
  decide (s < size I ∧ t < size I ∧ s / I.order ≠ t / I.order ∧ s % I.order ≠ t % I.order ∧
    adjG I (s % I.order) (t % I.order) = false)

/-- The neighbours of the vertex `s`, in increasing order. -/
noncomputable def neighbours (I : Instance) (s : ℕ) : List ℕ :=
  (List.range (size I)).filter (adjB I s)

/-- The target array: the neighbours of each vertex in turn. -/
noncomputable def targets (I : Instance) : List ℕ :=
  (List.range (size I)).flatMap (neighbours I)

/-- The offsets: `0`, then the running sums of the degrees. -/
noncomputable def offsets (I : Instance) : List ℕ :=
  (List.range (size I + 1)).map fun s => ((List.range s).map fun r => (neighbours I r).length).sum

/-- The colour of each vertex. -/
def colours (I : Instance) : List ℕ := (List.range (size I)).map fun s => s / I.order

/-- **The word of the multicoloured graph**: the number of vertices, the number of edges, the
offsets, the targets, the colours, and the number of colours. -/
noncomputable def word (I : Instance) : List ℕ :=
  [size I, (targets I).length / 2] ++ offsets I ++ targets I ++ colours I ++ [I.threshold]

-- The reduction on words

open Classical in
/-- **The reduction**: the word of the multicoloured graph on the word of an instance, and the
empty word elsewhere. -/
noncomputable def reduce (x : List ℕ) : List ℕ :=
  if h : x ∈ WH_F1_IndependentSetMatrix.Instances then word (Classical.choose h) else []

end Lax496464.WH_F2_MccConstruction
