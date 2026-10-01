import Lax496464Proofs.WHierarchy.HittingSet.Compress
import Lax496464Proofs.WHierarchy.HittingSet.CsrBuild

/-! # Hitting Set to Dominating Set: the graph

The graph of the compressed instance (`Compress.compress`): the `NN` elements form a clique, the sets
are the vertices `NN, …, NN + m - 1`, and element `a` is joined to set `j` when `a` lies in the
compressed set `j` (`Compress.InF`). Its neighbour lists, in the order the program writes them:
an element `u` lists the other elements and then the sets `NN + own p` of the positions `p` whose
first occurrence is `u`; a set `j` lists the first occurrences of its positions. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSGraph

open Lax496464.HittingSet Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.HittingSet.Form Lax496464Proofs.WHierarchy.HittingSet.Compress
open Lax496464Proofs.WHierarchy.HittingSet.CsrBuild

/-! ## Counting -/

/-- The fibres of a function below `N` partition a list. -/
theorem sum_fiber (f : ℕ → ℕ) : ∀ (N : ℕ) (l : List ℕ), (∀ p ∈ l, f p < N) →
    ((List.range N).map fun u => (l.filter fun p => f p = u).length).sum = l.length
  | 0, l, h => by
      cases l with
      | nil => simp
      | cons a l => exact absurd (h a (by simp)) (Nat.not_lt_zero _)
  | N + 1, l, h => by
      rw [List.range_succ, List.map_append, List.sum_append]
      have ih := sum_fiber f N (l.filter fun p => f p < N) (fun p hp => by
        simp only [List.mem_filter, decide_eq_true_eq] at hp; exact hp.2)
      have e1 : ((List.range N).map fun u => (l.filter fun p => f p = u).length) =
          ((List.range N).map fun u =>
            ((l.filter fun p => f p < N).filter fun p => f p = u).length) := by
        refine List.map_congr_left fun u hu => ?_
        rw [List.filter_filter]
        congr 1
        refine List.filter_congr fun p _ => ?_
        simp only [List.mem_range] at hu
        by_cases hpu : f p = u
        · simp [hpu, hu]
        · simp [hpu]
      rw [e1, ih]
      have e2 := List.length_eq_length_filter_add (l := l) (fun p => decide (f p < N))
      have e3 : (l.filter fun p => !decide (f p < N)).length =
          (l.filter fun p => decide (f p = N)).length := by
        congr 1
        refine List.filter_congr fun p hp => ?_
        have := h p hp
        by_cases hpN : f p = N
        · simp [hpN]
        · simp only [hpN, decide_false]
          simp; omega
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega

/-- The elements of `[0, T)` in an interval. -/
theorem count_interval (a b : ℕ) (hab : a ≤ b) : ∀ T : ℕ,
    ((List.range T).filter fun p => decide (a ≤ p ∧ p < b)).length = min b T - min a T
  | 0 => by simp
  | T + 1 => by
      rw [List.range_succ, List.filter_append, List.length_append, count_interval a b hab T]
      by_cases h : a ≤ T ∧ T < b
      · simp [h]; omega
      · simp only [List.filter_cons, List.filter_nil]
        rw [if_neg (by simpa using h)]
        simp only [List.length_nil]
        simp only [not_and_or, not_le, not_lt] at h
        omega

theorem length_filter_ne' (u : ℕ) : ∀ N : ℕ,
    ((List.range N).filter fun v => v ≠ u).length = if u < N then N - 1 else N
  | 0 => by simp
  | N + 1 => by
      rw [List.range_succ, List.filter_append, List.length_append, length_filter_ne' u N]
      by_cases h : N = u
      · subst h; simp
      · simp only [List.filter_cons, List.filter_nil, ne_eq, h, not_false_eq_true,
          decide_true, ↓reduceIte, List.length_singleton]
        split_ifs <;> omega

theorem length_filter_ne {N u : ℕ} (hu : u < N) :
    ((List.range N).filter fun v => v ≠ u).length = N - 1 := by
  rw [length_filter_ne' u N, if_pos hu]

/-! ## The blocks -/

/-- The owner of a position. -/
def own (P : Instance) (p : ℕ) : ℕ := (ownL P).getD p 0

/-- The neighbours of element `u`: the other elements, then its sets. -/
def elemBlk (P : Instance) (k u : ℕ) : List ℕ :=
  (List.range (NN P k)).filter (fun v => v ≠ u) ++
    ((List.range (total P)).filter fun p => fst P p = u).map fun p => NN P k + own P p

/-- The neighbours of set `j`: the first occurrences of its positions. -/
def setBlk (P : Instance) (j : ℕ) : List ℕ :=
  ((List.range (total P)).filter fun p => own P p = j).map (fst P)

/-- The neighbours of vertex `u`. -/
def blk (P : Instance) (k u : ℕ) : List ℕ :=
  if u < NN P k then elemBlk P k u else setBlk P (u - NN P k)

/-- The number of vertices. -/
def NV (P : Instance) (k : ℕ) : ℕ := NN P k + P.m

/-- The declared number of edges. -/
def MV (P : Instance) (k : ℕ) : ℕ := NN P k * (NN P k - 1) / 2 + total P

/-- The number of positions whose first occurrence is `u`. -/
def cnt (P : Instance) (u : ℕ) : ℕ := ((List.range (total P)).filter fun p => fst P p = u).length

theorem length_elemBlk (P : Instance) (k : ℕ) {u : ℕ} (hu : u < NN P k) :
    (elemBlk P k u).length = NN P k - 1 + cnt P u := by
  rw [elemBlk, List.length_append, length_filter_ne hu, List.length_map]; rfl

theorem length_setBlk (P : Instance) {j : ℕ} (hj : j < P.m) :
    (setBlk P j).length = offs P (j + 1) - offs P j := by
  unfold setBlk
  rw [List.length_map]
  have : ((List.range (total P)).filter fun p => own P p = j) =
      (List.range (total P)).filter fun p => decide (offs P j ≤ p ∧ p < offs P (j + 1)) := by
    refine List.filter_congr fun p hp => ?_
    rw [List.mem_range] at hp
    simp only [own, own_eq_iff P hp hj]
  rw [this, count_interval _ _ (offs_mono P (by omega))]
  have h1 := offs_mono P (show j + 1 ≤ P.m by omega)
  unfold total at *
  omega

theorem sum_cnt (P : Instance) (k : ℕ) :
    ((List.range (NN P k)).map (cnt P)).sum = total P := by
  have := sum_fiber (fst P) (NN P k) (List.range (total P)) (fun p hp => by
    rw [List.mem_range] at hp; have := fst_lt hp; unfold NN; omega)
  unfold cnt; rw [this, List.length_range]

theorem sum_setBlk (P : Instance) :
    ((List.range P.m).map fun j => (setBlk P j).length).sum = total P := by
  have := sum_fiber (own P) P.m (List.range (total P)) (fun p hp => by
    rw [List.mem_range] at hp; exact ownL_lt P hp)
  simpa [setBlk] using this

theorem sum_const_add (N c : ℕ) (g : ℕ → ℕ) :
    ((List.range N).map fun u => c + g u).sum = N * c + ((List.range N).map g).sum := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, ih]; ring

/-- **The total length of the blocks** is twice the declared number of edges. -/
theorem pre_blk (P : Instance) (k : ℕ) : pre (blk P k) (NV P k) = 2 * MV P k := by
  unfold pre NV
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  have e1 : ((List.range (NN P k)).map fun u => (blk P k u).length) =
      (List.range (NN P k)).map fun u => (NN P k - 1) + cnt P u := by
    refine List.map_congr_left fun u hu => ?_
    rw [List.mem_range] at hu
    simp only [blk, if_pos hu, length_elemBlk P k hu]
  have e2 : ((fun u => (blk P k u).length) ∘ (NN P k + ·)) = fun j => (setBlk P j).length := by
    funext j; simp [blk]
  rw [e1, e2, sum_const_add, sum_cnt, sum_setBlk]
  have hev : 2 ∣ NN P k * (NN P k - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self _)
  have := Nat.div_mul_cancel hev
  unfold MV
  rw [Nat.mul_comm (NN P k) (NN P k - 1)] at this ⊢
  omega

/-! ## The graph -/

/-- The adjacency of the graph. -/
def AdjR (P : Instance) (k u v : ℕ) : Prop :=
  u ≠ v ∧ ((u < NN P k ∧ v < NN P k) ∨ (u < NN P k ∧ NN P k ≤ v ∧ InF P u (v - NN P k)) ∨
    (v < NN P k ∧ NN P k ≤ u ∧ InF P v (u - NN P k)))

theorem adjR_symm (P : Instance) (k : ℕ) {u v : ℕ} (h : AdjR P k u v) : AdjR P k v u := by
  obtain ⟨h1, h2 | h2 | h2⟩ := h
  · exact ⟨Ne.symm h1, Or.inl ⟨h2.2, h2.1⟩⟩
  · exact ⟨Ne.symm h1, Or.inr (Or.inr h2)⟩
  · exact ⟨Ne.symm h1, Or.inr (Or.inl h2)⟩

/-- **The graph of the compressed instance.** -/
def dsGraph (P : Instance) (k : ℕ) : SimpleGraph (Fin (NV P k)) where
  Adj u v := AdjR P k u v
  symm := ⟨fun _ _ h => adjR_symm P k h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_blk (P : Instance) (k : ℕ) {u v : ℕ} (_hu : u < NV P k) (hv : v < NV P k) :
    v ∈ blk P k u ↔ AdjR P k u v := by
  unfold blk AdjR NV at *
  by_cases hu' : u < NN P k
  · rw [if_pos hu']
    simp only [elemBlk, List.mem_append, List.mem_filter, List.mem_range, List.mem_map,
      decide_eq_true_eq]
    constructor
    · rintro (⟨hvN, hvu⟩ | ⟨p, ⟨hp, hpu⟩, rfl⟩)
      · exact ⟨Ne.symm hvu, Or.inl ⟨hu', hvN⟩⟩
      · refine ⟨by omega, Or.inr (Or.inl ⟨hu', by omega, ?_⟩)⟩
        exact ⟨p, hp, hpu, by simp [own]⟩
    · rintro ⟨huv, ⟨-, hvN⟩ | ⟨-, hvN, p, hp, hpu, hpj⟩ | ⟨-, hN, -⟩⟩
      · exact Or.inl ⟨hvN, Ne.symm huv⟩
      · exact Or.inr ⟨p, ⟨hp, hpu⟩, by simp only [own]; omega⟩
      · omega
  · rw [if_neg hu']
    simp only [setBlk, List.mem_filter, List.mem_range, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨p, ⟨hp, hpj⟩, rfl⟩
      have := fst_lt hp
      refine ⟨by unfold NN at hu'; omega, Or.inr (Or.inr ⟨by unfold NN; omega, by omega, ?_⟩)⟩
      exact ⟨p, hp, rfl, hpj⟩
    · rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, p, hp, hpv, hpj⟩⟩
      · exact absurd h hu'
      · exact absurd h hu'
      · exact ⟨p, ⟨hp, hpj⟩, hpv⟩

theorem blk_lt (P : Instance) (k : ℕ) {u : ℕ} (hu : u < NV P k) {v : ℕ} (hv : v ∈ blk P k u) :
    v < NV P k := by
  unfold blk NV at *
  split_ifs at hv with hu'
  · simp only [elemBlk, List.mem_append, List.mem_filter, List.mem_range, List.mem_map] at hv
    rcases hv with ⟨h, -⟩ | ⟨p, ⟨hp, -⟩, rfl⟩
    · omega
    · have := ownL_lt P hp; simp only [own]; omega
  · simp only [setBlk, List.mem_filter, List.mem_range, List.mem_map] at hv
    obtain ⟨p, ⟨hp, -⟩, rfl⟩ := hv
    have := fst_lt hp; unfold NN; omega

/-- The word of the graph. -/
def dsGraphWord (P : Instance) (k : ℕ) : List ℕ := csrWord (NV P k) (MV P k) (blk P k)

/-- **The word encodes the graph.** -/
theorem encodesGraph_ds (P : Instance) (k : ℕ) :
    EncodesGraph (dsGraphWord P k) (NV P k) (dsGraph P k) :=
  encodesGraph_csrWord _ _ _ (pre_blk P k) (fun _ hu _ hv => blk_lt P k hu hv) _
    fun u v => ((mem_blk P k u.isLt v.isLt).symm)

end Lax496464Proofs.WHierarchy.HittingSet.DSGraph
