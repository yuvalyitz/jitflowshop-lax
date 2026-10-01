import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Common

/-!
# p-Clique to Multicoloured Clique: construction and correctness

For a graph `G` on `n` vertices and `k ≤ n`, the multicoloured graph has the `k · n` vertices
`s = c · n + v` (the copy of `v` in colour `c = s / n`, `v = s % n`), coloured `s / n`; two copies
`s`, `t` are adjacent when their colours differ, their vertices differ, and those vertices are
adjacent in `G`. A multicoloured clique picks `k` different, pairwise adjacent vertices of `G`, and
conversely. When `k > n` there is no `k`-clique and the reduction writes a fixed no-instance.

Everything is read off the word directly: `nV`, `kP`, the offsets `offX`, and the adjacency test
`adjX` (is `v` in the block of `u`?), so the reduction on words is the computable map `reduce`, and
the machine layer computes exactly it.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath

open Lax888481.MulticolouredClique Lax271696.GraphEncoding Lax271696.VertexCover
open Lax496464.WH_C1_GraphProblems Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC

/-! ### The map on words -/

/-- The number of vertices of the word. -/
def nV (x : List ℕ) : ℕ := x.getD 0 0

/-- The parameter of the word, its last entry. -/
def kP (x : List ℕ) : ℕ := x.getLast?.getD 0

/-- The `i`-th offset of the word. -/
def offX (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- `v` is listed in the block of `u`. -/
def adjX (x : List ℕ) (u v : ℕ) : Bool :=
  (List.range (offX x (u + 1) - offX x u)).any fun i => x.getD (3 + nV x + offX x u + i) 0 == v

/-- The number of vertices of the multicoloured graph. -/
def NOf (x : List ℕ) : ℕ := kP x * nV x

/-- The adjacency of the multicoloured graph, on numbers. -/
def adjW (x : List ℕ) (s t : ℕ) : Bool :=
  decide (s / nV x ≠ t / nV x) && adjX x (s % nV x) (t % nV x)

/-- The word of the multicoloured graph: its compressed sparse row word, the colours, and `k`. -/
def prodWord (x : List ℕ) : List ℕ :=
  CsrWord.csrWord (adjW x) (NOf x) ++ (List.range (NOf x)).map (fun s => s / nV x) ++ [kP x]

/-- A fixed no-instance: one colour and no vertices. -/
def noWord : List ℕ := [0, 0, 0, 1]

/-- **The reduction.** -/
def reduce (x : List ℕ) : List ℕ := if nV x < kP x then noWord else prodWord x

/-! ### Reading the word -/

private lemma getD_prefix {g r : List ℕ} {i : ℕ} (hi : i < g.length) :
    (g ++ r).getD i 0 = g.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem offset_mono' {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : offset g i ≤ offset g j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hg.offset_mono j (by omega))

section
variable {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}

theorem nV_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) : nV x = n := by
  have hl := hg.length_eq
  unfold nV; rw [hx, getD_prefix (by omega)]; exact hg.vertexCount_eq

theorem kP_eq (hx : x = g ++ [k]) : kP x = k := by
  unfold kP; rw [hx]; simp

/-- **The adjacency test of the word is the adjacency of the graph.** -/
theorem adjX_iff (hx : x = g ++ [k]) (hg : EncodesGraph g n G) (u v : Fin n) :
    adjX x u v = true ↔ G.Adj u v := by
  have hl := hg.length_eq
  have hlast := hg.offset_last
  have hn := nV_eq hx hg
  have hoff : ∀ i ≤ n, offX x i = offset g i := fun i hi => by
    unfold offX offset; rw [hx, getD_prefix (by omega)]
  have hu := u.2
  have hu1 := hoff u (by omega)
  have hu2 := hoff (u + 1) (by omega)
  have hle : offset g (u + 1) ≤ 2 * edgeCount g := hlast ▸ offset_mono' hg (by omega) le_rfl
  rw [hg.adj_iff]
  unfold adjX
  rw [hn, hu1, hu2]
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨offset g u + i, by omega, by omega, ?_⟩
    unfold target
    rw [hg.vertexCount_eq, ← he, hx, getD_prefix (by omega), Nat.add_assoc (3 + n)]
  · rintro ⟨j, h1, h2, he⟩
    refine ⟨j - offset g u, by omega, ?_⟩
    have hj : 3 + n + offset g u + (j - offset g u) = 3 + vertexCount g + j := by
      rw [hg.vertexCount_eq]; omega
    rw [hx, getD_prefix (by omega), hj]
    exact he

end

/-! ### The multicoloured graph -/

theorem pos_of_fin {k n : ℕ} (s : Fin (k * n)) : 0 < n :=
  Nat.pos_of_ne_zero fun h => by
    have h1 : (s : ℕ) < k * n := s.2
    have h2 : k * n = 0 := by simp [h]
    omega

/-- The vertex of `G` a copy copies. -/
def vOf {k n : ℕ} (s : Fin (k * n)) : Fin n := ⟨s % n, Nat.mod_lt _ (pos_of_fin s)⟩

/-- The colour of a copy. -/
def cOf {k n : ℕ} (s : Fin (k * n)) : Fin k :=
  ⟨s / n, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq s.2 (Nat.mul_comm k n))⟩

/-- The multicoloured graph: copies of different colours of adjacent vertices are adjacent. -/
def prodGraph (n k : ℕ) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (k * n)) where
  Adj s t := cOf s ≠ cOf t ∧ G.Adj (vOf s) (vOf t)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The multicoloured clique instance of `G` and `k`. -/
def prodInst (n k : ℕ) (G : SimpleGraph (Fin n)) : Instance where
  colours := k
  vertices := k * n
  graph := prodGraph n k G
  colour := cOf
  adj_colour_ne _ _ h := h.1

theorem div_eq {c v n : ℕ} (hv : v < n) : (c * n + v) / n = c := by
  have hn : 0 < n := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hv, Nat.zero_add]

theorem mod_eq {c v n : ℕ} (hv : v < n) : (c * n + v) % n = v := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem copy_lt {c v n k : ℕ} (hc : c < k) (hv : v < n) : c * n + v < k * n := by
  have : (c + 1) * n ≤ k * n := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- **Correctness of the construction**: `G` has a `k`-clique iff the multicoloured graph has a
multicoloured clique. -/
theorem hasMulticolouredClique_prod_iff (n k : ℕ) (G : SimpleGraph (Fin n)) :
    (prodInst n k G).HasMulticolouredClique ↔ ∃ s : Finset (Fin n), G.IsNClique k s := by
  classical
  constructor
  · rintro ⟨f, hf, hadj⟩
    let v : Fin k → Fin n := fun c => vOf (f c)
    have hinj : Function.Injective v := by
      intro c c' h
      by_contra hne
      exact (hadj c c' hne).2.ne h
    refine ⟨Finset.univ.image v, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, by rw [Finset.card_image_of_injective _ hinj]; simp⟩
    intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨c', rfl⟩ := hb
    exact (hadj c c' fun h => hab (by rw [h])).2
  · rintro ⟨s, hs⟩
    show ∃ f : Fin k → Fin (k * n), (∀ c, cOf (f c) = c) ∧
      ∀ c c', c ≠ c' → cOf (f c) ≠ cOf (f c') ∧ G.Adj (vOf (f c)) (vOf (f c'))
    let e := s.orderIsoOfFin hs.card_eq
    have hlt : ∀ c : Fin k, (c : ℕ) * n + ((e c : Fin n) : ℕ) < k * n := fun c =>
      copy_lt c.2 (e c : Fin n).2
    let f : Fin k → Fin (k * n) := fun c => ⟨c * n + ((e c : Fin n) : ℕ), hlt c⟩
    have hv : ∀ c, vOf (f c) = (e c : Fin n) := fun c => Fin.ext (mod_eq (e c : Fin n).2)
    have hc : ∀ c, cOf (f c) = c := fun c => Fin.ext (div_eq (e c : Fin n).2)
    refine ⟨f, hc, fun c c' hne => ⟨by rw [hc, hc]; exact hne, ?_⟩⟩
    rw [hv, hv]
    refine hs.1 (e c).2 (e c').2 fun h => hne ?_
    exact e.injective (Subtype.ext h)

section
variable {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}

theorem adjW_iff (hx : x = g ++ [k]) (hg : EncodesGraph g n G) (s t : Fin (k * n)) :
    (prodGraph n k G).Adj s t ↔ adjW x s t = true := by
  have hn := nV_eq hx hg
  have h := adjX_iff hx hg (vOf s) (vOf t)
  show cOf s ≠ cOf t ∧ G.Adj (vOf s) (vOf t) ↔ _
  unfold adjW
  rw [hn, ← h, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr ⟨fun h1 h2 => h1 (Fin.ext h2), fun h1 h2 => h1 (congrArg Fin.val h2)⟩ Iff.rfl

theorem prodWord_eq (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    prodWord x = CsrWord.csrWord (adjW x) (k * n) ++
      (List.range (k * n)).map (fun s => s / n) ++ [k] := by
  unfold prodWord NOf
  rw [nV_eq hx hg, kP_eq hx]

theorem colours_eq :
    List.ofFn (fun v : Fin (k * n) => ((prodInst n k G).colour v : ℕ)) =
      (List.range (k * n)).map (fun s => s / n) := by
  apply List.ext_getElem
  · simp [prodInst]
  · intro i _ _
    simp [prodInst, cOf]

/-- **The word of the construction encodes the multicoloured graph.** -/
theorem prodWord_encodes (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    EncodesInstance (prodWord x) (prodInst n k G) := by
  refine ⟨CsrWord.csrWord (adjW x) (k * n), ?_, CsrWord.encodesGraph (adjW_iff hx hg),
    fun u hu t h1 h2 => CsrWord.sorted u hu t h1 h2⟩
  rw [prodWord_eq hx hg, ← colours_eq (G := G)]
  rfl

end

/-! ### The no-instance -/

/-- One colour and no vertices. -/
def noInst : Instance where
  colours := 1
  vertices := 0
  graph := ⊥
  colour v := v.elim0
  adj_colour_ne u := u.elim0

theorem noWord_encodes : EncodesInstance noWord noInst := by
  refine ⟨[0, 0, 0], by simp [noWord, noInst], ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi
    (Nat.not_lt_zero _), fun j hj => absurd hj (by simp [edgeCount]), fun u => u.elim0⟩,
    fun u hu => absurd hu (Nat.not_lt_zero _)⟩

theorem not_noInst : ¬ noInst.HasMulticolouredClique := fun ⟨f, _⟩ => (f ⟨0, Nat.one_pos⟩).elim0

/-! ### The reduction -/

theorem reduce_isReduction : IsReduction Clique Lax888481.MulticolouredClique.problem reduce where
  maps_domain x hx := by
    obtain ⟨n, G, k, g, hx, hg⟩ := hx
    unfold reduce
    rw [nV_eq hx hg, kP_eq hx]
    split_ifs
    · exact ⟨noInst, noWord_encodes⟩
    · exact ⟨prodInst n k G, prodWord_encodes hx hg⟩
  correct x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    obtain ⟨g, hx, hg⟩ := id h
    rw [Common.clique_yes_iff h]
    unfold reduce
    rw [nV_eq hx hg, kP_eq hx]
    split_ifs with hnk
    · rw [MccUnique.yes_iff noWord_encodes]
      refine ⟨fun ⟨s, hs⟩ => absurd hs.card_eq ?_, fun h => absurd h not_noInst⟩
      have := Finset.card_le_univ s
      simp at this
      omega
    · rw [MccUnique.yes_iff (prodWord_encodes hx hg), hasMulticolouredClique_prod_iff]

theorem param_reduce_le (x : List ℕ) :
    Lax888481.MulticolouredClique.problem.param (reduce x) ≤ Clique.param x := by
  show (reduce x).getLast?.getD 0 ≤ kP x
  unfold reduce
  split_ifs with h
  · simp [noWord]; omega
  · simp [prodWord]

theorem reduce_paramBounded : ParamBounded Clique Lax888481.MulticolouredClique.problem reduce :=
  ⟨id, Computable.id, fun x _ => param_reduce_le x⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath
