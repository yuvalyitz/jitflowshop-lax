import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-!
# What the two whole programs share

The facts about a graph word the programs use (`Good`), the value bound, the reading of `n` and
`k`, the layout, and the numeric bounds the time statements need.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax271696.GraphEncoding Lax271696.VertexCover
open Lax759944.BinaryWordEncoding
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath

/-! ### A graph instance is a good word -/

theorem good_of_param {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) : Good x ∧ x ≠ [] := by
  obtain ⟨g, hx, hg⟩ := h
  have hn := nV_eq hx hg
  have hl := hg.length_eq
  have hlast := hg.offset_last
  have hE : E x = 2 * edgeCount g := by
    rw [E, hn, offset_eq hx hg le_rfl, hlast]
  refine ⟨⟨?_, fun u hu => ?_, fun u hu => ?_⟩, by rw [hx]; simp⟩
  · rw [hE, hn, hx]; simp; omega
  · rw [hn] at hu
    rw [offset_eq hx hg (by omega), offset_eq hx hg (by omega)]
    exact hg.offset_mono u hu
  · rw [hn] at hu
    rw [hE, offset_eq hx hg hu, ← hlast]
    exact offset_le_last hg u hu

/-! ### The value bound -/

/-- The largest entry of a word. -/
def Mmax (x : List ℕ) : ℕ := x.foldr max 0

theorem le_Mmax {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v ≤ Mmax x := by
  induction x with
  | nil => simp at hv
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem kOf_le_Mmax (x : List ℕ) : kOf x ≤ Mmax x := by
  unfold kOf
  rcases h : x.getLast? with _ | a
  · simp
  · simpa using le_Mmax (List.mem_of_getLast? h)

theorem Mmax_lt (x : List ℕ) : Mmax x < 2 ^ bitSize x := by
  induction x with
  | nil => simp [Mmax, bitSize, encode]
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    have h1 := Lax496464Proofs.WHierarchy.Machine.SizeFacts.lt_two_pow_bitSize (x := a :: t) (v := a)
      (by simp)
    have h2 : 2 ^ bitSize t ≤ 2 ^ bitSize (a :: t) := Nat.pow_le_pow_right (by norm_num)
      (by rw [Lax496464Proofs.WHierarchy.Machine.SizeFacts.bitSize_cons]; omega)
    exact max_lt h1 (by omega)

/-- **The value bound of the programs.** -/
def Bv (x : List ℕ) : ℕ := (x.length + 2) * (x.length + 2) + Mmax x + 9

theorem fits_Bv (x : List ℕ) : Fits x (Bv x) :=
  ⟨fun v hv => by have := le_Mmax hv; unfold Bv; omega, by unfold Bv; omega⟩

/-! ### Reading `n` and `k` -/

theorem getD_last {x : List ℕ} (hx : x ≠ []) : x.getD (x.length - 1) 0 = kOf x := by
  obtain ⟨l, a, rfl⟩ := List.eq_nil_or_concat x |>.resolve_left hx
  simp [kOf]

theorem kOf_lt {x : List ℕ} (hx : x ≠ []) {B : ℕ} (hB : Fits x B) : kOf x < B := by
  rw [← getD_last hx]; exact hB.getD_lt _

set_option maxHeartbeats 1000000 in
theorem headCom_value {x : List ℕ} (hx : x ≠ []) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) headCom
      (fun _ σ' => σ'.vars "g_n" = nV x ∧ σ'.vars "g_k" = kOf x) 20 := by
  have hl : 0 < x.length := List.length_pos_iff.mpr hx
  have hBl := hB.len_lt
  refine Spec.pre (P := fun σ => (σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) ∧
    (σ.arrs "a").getD 0 0 < B ∧ (σ.arrs "a").getD (σ.vars "rt_n" - 1) 0 < B ∧
    σ.vars "rt_n" < B ∧ 0 < (σ.arrs "a").length ∧ σ.vars "rt_n" - 1 < (σ.arrs "a").length) ?_ ?_
  · unfold headCom
    run_vcg
    all_goals
      have ha : σ.arrs "a" = x := ‹_›
      have hn : σ.vars "rt_n" = x.length := ‹_›
      simp only [Env.setVar]
      simp [ha, hn]
    all_goals first
      | (exact ⟨rfl, by rw [← List.getD_eq_getElem?_getD, getD_last hx]⟩)
      | (rw [← List.getD_eq_getElem?_getD, getD_last hx]; done)
      | exact hB.getD_lt _
  · rintro σ ⟨ha, hn⟩
    refine ⟨⟨ha, hn⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha]; exact hB.getD_lt _
    · rw [ha]; exact hB.getD_lt _
    · rw [hn]; omega
    · rw [ha]; exact hl
    · rw [ha, hn]; omega

/-- The scalars `headCom` assigns. -/
def headVars : List String := ["g_n", "g_k"]

theorem headCom_spec {x : List ℕ} (hx : x ≠ []) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) headCom
      (fun σ σ' => (σ'.vars "g_n" = nV x ∧ σ'.vars "g_k" = kOf x) ∧ Keep headVars σ σ' ∧
        σ'.out = σ.out) 20 := by
  refine Spec.keepOut (headCom_value hx hB) headVars ?_ ?_ ?_ ?_
  · intro y hy
    simp only [headCom, Com.wvars, headVars] at hy ⊢
    simpa using hy
  · simp [headCom, Com.warrs]
  · simp [headCom, Com.reads]
  · simp [headCom, Com.NoWrite]

/-! ### The layout -/

/-- The layout of both programs. -/
def layout : Layout := ⟨progVars, ["a"], 12⟩

/-! ### Numbers -/

/-- `nV x ≤ x.length` and `E x ≤ x.length` on good words. -/
theorem nV_le {x : List ℕ} (hx : Good x) : nV x ≤ x.length := by have := hx.len; omega

theorem E_le {x : List ℕ} (hx : Good x) : E x ≤ x.length := by have := hx.len; omega

/-- The cost of the graph part, bounded by a cube. -/
theorem Kgraph_le {x : List ℕ} (hx : Good x) : Kgraph x ≤ 300 * (x.length + 1) ^ 3 := by
  have hn := nV_le hx
  have hE := E_le hx
  unfold Kgraph Kpass Krow Kadj
  generalize nV x = n at *
  generalize E x = e at *
  generalize x.length = L at *
  have h1 : (24 * e + 40 + 24) * n ≤ 88 * (L + 1) * (L + 1) := by
    have : 24 * e + 40 + 24 ≤ 88 * (L + 1) := by omega
    exact Nat.mul_le_mul this (by omega)
  have h2 : ((24 * e + 40 + 24) * n + 20 + 4) * n ≤ 112 * (L + 1) * (L + 1) * (L + 1) := by
    have : (24 * e + 40 + 24) * n + 20 + 4 ≤ 112 * (L + 1) * (L + 1) := by nlinarith
    exact (Nat.mul_le_mul this (show n ≤ L + 1 by omega))
  have e3 : (L + 1) ^ 3 = (L + 1) * (L + 1) * (L + 1) := by ring
  have h4 : 1 ≤ (L + 1) * (L + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [e3]
  nlinarith

/-- A value bound far below the exponential of the time bound. -/
theorem Bv_add_le (x : List ℕ) (c : ℕ) (hc : 100 ≤ c) :
    Bv x + 100 ≤ 2 ^ (c * (bitSize x + 1) ^ 3) := by
  have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have hM := Mmax_lt x
  set b := bitSize x
  have h1 : x.length + 2 ≤ 2 ^ (b + 1) := by
    have := Nat.lt_two_pow_self (n := b + 1)
    have : b + 2 ≤ 2 ^ (b + 1) := this
    omega
  have h2 : (x.length + 2) * (x.length + 2) ≤ 2 ^ (2 * b + 2) := by
    have := Nat.mul_le_mul h1 h1
    rw [← pow_add] at this
    rw [show 2 * b + 2 = b + 1 + (b + 1) by ring]; exact this
  have h3 : 2 ^ b ≤ 2 ^ (2 * b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ 7 ≤ 2 ^ (2 * b + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ (2 * b + 2) * 32 = 2 ^ (2 * b + 7) := by
    rw [show 2 * b + 7 = (2 * b + 2) + 5 by ring, Nat.pow_add 2 (2 * b + 2) 5]
  have h6 : 2 ^ (2 * b + 9) ≤ 2 ^ (c * (b + 1) ^ 3) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : b + 1 ≤ (b + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    nlinarith
  have h7 : 2 ^ (2 * b + 9) = 2 ^ (2 * b + 7) * 4 := by
    rw [show 2 * b + 9 = (2 * b + 7) + 2 by ring, Nat.pow_add 2 (2 * b + 7) 2]
  unfold Bv
  omega

/-- The span of the layout at the value bound. -/
theorem span_le (x : List ℕ) (c : ℕ) (hc : 100 ≤ c) :
    max (Bv x) (layout.span (Bv x)) ≤ 2 ^ (c * (bitSize x + 1) ^ 3) := by
  have := Bv_add_le x c hc
  simp only [Layout.span, layout, progVars, List.length_cons, List.length_nil]
  omega

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon
