import Lax496464Proofs.WHierarchy.HittingSet.DSGraph
import Lax496464Proofs.WHierarchy.HittingSet.Words
import Lax496464Proofs.WHierarchy.HittingSet.WDMath
import Lax496464Proofs.WHierarchy.Graphs.CsrUnique
import Lax496464.WH_E3_DominatingSet

/-! # Hitting Set to Dominating Set: the mathematics

A hitting set of the compressed instance dominates its graph (the elements form a clique, a set is
dominated by an element it contains), and a dominating set becomes a hitting set of at most the same
size by replacing each set vertex by an element of that set — this needs every set to be nonempty.
So the reduction writes the graph of the compressed instance with `min k m` when `k ≤ n` and no set
is empty, and a fixed no-instance otherwise (Flum–Grohe, Example 2.7). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSMath

open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_C1_GraphProblems
open Lax496464.WH_A2_FptReductions Lax271696.VertexCover Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Compress Lax496464Proofs.WHierarchy.HittingSet.DSGraph
open Lax496464Proofs.WHierarchy.Graphs.CsrUnique

/-! ## Empty sets -/

/-- No set of the family is empty. -/
def NoEmpty (P : Instance) : Prop := ∀ j < P.m, offs P j < offs P (j + 1)

theorem mlist_ne_nil {P : Instance} (h : NoEmpty P) {j : ℕ} (hj : j < P.m) : mlist P j ≠ [] := by
  intro he
  have := h j hj
  rw [offs_succ, he] at this
  simp at this

theorem exists_inF {P : Instance} (h : NoEmpty P) (k : ℕ) {j : ℕ} (hj : j < P.m) :
    ∃ a < NN P k, InF P a j := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (mlist_ne_nil h hj)
  have hin : InF P ((memL P).idxOf e) j := (inF_iff hj).mpr ⟨e, he, rfl⟩
  exact ⟨_, by have := inF_lt hin; unfold NN; omega, hin⟩

theorem not_hasHittingSet_of_empty {P : Instance} (h : ¬ NoEmpty P) (k : ℕ) :
    ¬ P.HasHittingSet k := by
  rintro ⟨H, -, hh⟩
  apply h
  intro j hj
  obtain ⟨i, -, hi⟩ := hh ⟨j, hj⟩
  have hmem : (i : ℕ) ∈ mlist P j := (mem_mlist_iff P hj i).mpr hi
  rw [offs_succ]
  have : (mlist P j).length ≠ 0 := by
    intro h0; rw [List.length_eq_zero_iff] at h0; rw [h0] at hmem; simp at hmem
  omega

theorem total_zero_of_m_zero {P : Instance} (h : P.m = 0) : total P = 0 := by
  unfold total; rw [h, offs_zero]

/-! ## Dominating sets of the graph are hitting sets -/

/-- `s` dominates `G`. -/
def Dominates {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ v, v ∈ s ∨ ∃ u ∈ s, G.Adj u v

theorem NV_le (P : Instance) (k : ℕ) : (compress P k).n ≤ NV P k := by
  show NN P k ≤ NV P k; unfold NV; omega

/-- **A dominating set of `min k m` vertices exists exactly when the compressed instance has a
hitting set of that size.** -/
theorem ds_iff (P : Instance) (k : ℕ) (hne : NoEmpty P) :
    (∃ s : Finset (Fin (NV P k)), s.card = kk P k ∧ Dominates (dsGraph P k) s) ↔
      (compress P k).HasHittingSet (kk P k) := by
  classical
  constructor
  · rintro ⟨s, hs, hdom⟩
    by_cases hk0 : kk P k = 0
    · -- no vertex at all
      have hs0 : s = ∅ := Finset.card_eq_zero.mp (by rw [hs, hk0])
      have hNV : NV P k = 0 := by
        by_contra hpos
        rcases hdom ⟨0, by omega⟩ with h | ⟨u, hu, -⟩
        · rw [hs0] at h; simp at h
        · rw [hs0] at hu; simp at hu
      have hm0 : P.m = 0 := by unfold NV at hNV; omega
      refine ⟨∅, by simp [hk0], fun j => ?_⟩
      have := j.isLt; simp only [compress] at this; omega
    · have hex : ∀ j, ∃ a, j < P.m → a < NN P k ∧ InF P a j := by
        intro j
        by_cases hj : j < P.m
        · obtain ⟨a, ha, hin⟩ := exists_inF hne k hj; exact ⟨a, fun _ => ⟨ha, hin⟩⟩
        · exact ⟨0, fun h => absurd h hj⟩
      choose c hc using hex
      have hφ : ∀ v : Fin (NV P k), (if v.val < NN P k then v.val else c (v.val - NN P k)) <
          NN P k := by
        intro v
        split_ifs with h
        · exact h
        · exact (hc _ (by have := v.isLt; unfold NV at this; omega)).1
      let φ : Fin (NV P k) → Fin (compress P k).n := fun v => ⟨_, hφ v⟩
      rw [hasHittingSet_iff_le _ (kk_le_NN P k)]
      refine ⟨s.image φ, Finset.card_image_le.trans hs.le, fun j => ?_⟩
      have hjv : NN P k + j.val < NV P k := by have := j.isLt; unfold NV; simp only [compress] at this; omega
      rcases hdom ⟨NN P k + j.val, hjv⟩ with h | ⟨u, hu, hadj⟩
      · refine ⟨φ ⟨_, hjv⟩, Finset.mem_image_of_mem _ h, ?_⟩
        rw [mem_compress_F]
        have := (hc j.val j.isLt).2
        simpa [φ] using this
      · obtain ⟨-, h1 | h1 | h1⟩ := hadj
        · simp at h1
        · refine ⟨φ u, Finset.mem_image_of_mem _ hu, ?_⟩
          rw [mem_compress_F]
          have e : (φ u).val = u.val := by simp [φ, h1.1]
          rw [e]
          simpa using h1.2.2
        · simp at h1
  · rintro ⟨H, hH, hh⟩
    refine ⟨H.map (Fin.castLEEmb (NV_le P k)), by rw [Finset.card_map, hH], fun v => ?_⟩
    by_cases hv : v.val < NN P k
    · by_cases hk0 : kk P k = 0
      · -- then `m = 0` and there are no elements
        have hH0 : H = ∅ := Finset.card_eq_zero.mp (by rw [hH, hk0])
        have hm0 : P.m = 0 := by
          by_contra hm
          obtain ⟨a, ha, -⟩ := hh ⟨0, by simp only [compress]; omega⟩
          rw [hH0] at ha; simp at ha
        have := total_zero_of_m_zero hm0
        unfold NN at hv; omega
      · obtain ⟨a, ha⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
        by_cases hav : a.val = v.val
        · left
          refine Finset.mem_map.mpr ⟨a, ha, Fin.ext ?_⟩
          simp [hav]
        · right
          refine ⟨Fin.castLEEmb (NV_le P k) a, Finset.mem_map_of_mem _ ha, ?_⟩
          show AdjR P k _ _
          have := a.isLt
          simp only [Fin.castLEEmb_apply, Fin.val_castLE]
          exact ⟨hav, Or.inl ⟨by simpa [compress] using this, hv⟩⟩
    · right
      have hj : v.val - NN P k < P.m := by have := v.isLt; unfold NV at this; omega
      obtain ⟨a, ha, haj⟩ := hh ⟨v.val - NN P k, hj⟩
      rw [mem_compress_F] at haj
      refine ⟨Fin.castLEEmb (NV_le P k) a, Finset.mem_map_of_mem _ ha, ?_⟩
      show AdjR P k _ _
      have := a.isLt
      simp only [Fin.castLEEmb_apply, Fin.val_castLE]
      have ha' : a.val < NN P k := by simpa [compress] using this
      exact ⟨by omega, Or.inr (Or.inl ⟨ha', by omega, haj⟩)⟩

/-! ## The words -/

/-- **The word the reduction writes** when `k ≤ n` and no set is empty. -/
def dsOut (P : Instance) (k : ℕ) : List ℕ := dsGraphWord P k ++ [kk P k]

/-- The fixed no-instance: the empty graph with parameter `1`. -/
def dsNo : List ℕ := [0, 0, 0, 1]

theorem encodes_dsOut (P : Instance) (k : ℕ) :
    EncodesParamInstance (dsOut P k) (NV P k) (dsGraph P k) (kk P k) :=
  ⟨_, rfl, encodesGraph_ds P k⟩

theorem encodes_dsNo : EncodesParamInstance dsNo 0 ⊥ 1 := by
  refine ⟨[0, 0, 0], rfl, ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun j hj => ?_, fun u => u.elim0⟩⟩
  simp [edgeCount] at hj

theorem yes_iff_of_encodes {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) :
    DominatingSet.Yes x ↔ ∃ s : Finset (Fin n), s.card = k ∧ Dominates G s := by
  constructor
  · rintro ⟨n', G', k', h', hs⟩
    obtain rfl := vertices_eq h h'
    obtain ⟨rfl, rfl⟩ := graph_param_eq h h'
    exact hs
  · intro hs; exact ⟨n, G, k, h, hs⟩

theorem not_yes_dsNo : ¬ DominatingSet.Yes dsNo := by
  rw [yes_iff_of_encodes encodes_dsNo]
  rintro ⟨s, hs, -⟩
  have := Finset.card_le_univ s
  rw [Fintype.card_fin] at this; omega

/-! ## The reduction on words -/

open Classical in
/-- **The reduction.** -/
noncomputable def redDS (x : List ℕ) : List ℕ :=
  if h : ∃ p : Instance × ℕ, x = word p.1 p.2 then
    (if (Classical.choose h).2 ≤ (Classical.choose h).1.n ∧ NoEmpty (Classical.choose h).1 then
      dsOut (Classical.choose h).1 (Classical.choose h).2 else dsNo)
  else []

open Classical in
theorem redDS_word (P : Instance) (k : ℕ) :
    redDS (word P k) = if k ≤ P.n ∧ NoEmpty P then dsOut P k else dsNo := by
  have h : ∃ p : Instance × ℕ, word P k = word p.1 p.2 := ⟨(P, k), rfl⟩
  unfold redDS
  rw [dif_pos h]
  obtain ⟨e1, e2⟩ := word_inj (Classical.choose_spec h)
  rw [← e1, ← e2]

theorem isReduction : IsReduction HittingSet DominatingSet redDS := by
  classical
  constructor
  · rintro x ⟨P, k, rfl⟩
    rw [redDS_word]
    split_ifs
    · exact ⟨_, _, _, encodes_dsOut P k⟩
    · exact ⟨_, _, _, encodes_dsNo⟩
  · rintro x ⟨P, k, rfl⟩
    rw [yes_word_iff, redDS_word]
    split_ifs with h
    · rw [yes_iff_of_encodes (encodes_dsOut P k), hasHittingSet_compress P h.1, ds_iff P k h.2]
    · refine iff_of_false ?_ not_yes_dsNo
      rcases not_and_or.mp h with h1 | h1
      · exact WDMath.not_hasHittingSet_of_lt (by omega)
      · exact not_hasHittingSet_of_empty h1 k

theorem paramBounded : ParamBounded HittingSet DominatingSet redDS := by
  classical
  refine ⟨Nat.succ, Computable.succ, ?_⟩
  rintro x ⟨P, k, rfl⟩
  rw [param_word, redDS_word]
  split_ifs
  · simp only [DominatingSet, dsOut, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.getD_some, kk]
    omega
  · simp [DominatingSet, dsNo]

end Lax496464Proofs.WHierarchy.HittingSet.DSMath
