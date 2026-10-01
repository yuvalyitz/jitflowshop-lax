import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetProg
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds
import Lax496464Proofs.WHierarchy.Machine.ImpBridge

/-! # Multicoloured Clique ≤fpt p-Clique

The map `forget` (keep the graph block and the number of colours) is a reduction
(`ForgetMath`), keeps the parameter, and is computed in linear time by the IMP+ program of
`ForgetProg`; the bridges turn these into an fpt-reduction. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax888481.MulticolouredClique Lax271696.GraphEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Machine.ReadTape Lax496464Proofs.WHierarchy.Machine.ImpBridge
open Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetProg
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-- The layout: the reader's scalars, the copy's, and the array `a`. -/
def layout : Layout := ⟨["rt_n", "rt_i", "rt_v", "f_L", "f_i"], ["a"], 4⟩

theorem prog_ok : Com.Ok layout prog := by
  simp [layout, prog, readTape, readLoop, readBody, copyLoop, copyBody, lenExpr, bump, V, Com.Ok,
    Expr.Ok, Cond.Ok, condExpr]

/-- The value bound, on the tape. -/
def Bv (y : List ℕ) : ℕ := Mmax y + y.length + 2

/-- The cost bound, on the tape. -/
def Kc (y : List ℕ) : ℕ := 32 * y.tail.length + 60

theorem domain_facts {x : List ℕ} (hx : x ∈ Lax888481.MulticolouredClique.problem.Domain) :
    blockLen x ≤ x.length ∧ x ≠ [] := by
  obtain ⟨G, g, hxe, hg, -⟩ := hx
  have hb := blockLen_eq hxe hg
  have hl : x.length = g.length + G.vertices + 1 := by rw [hxe]; simp; omega
  refine ⟨by omega, fun h => ?_⟩
  rw [h] at hl; simp at hl

theorem solves :
    Solves layout prog (Tapes Lax888481.MulticolouredClique.problem.Domain)
      (fun y => forget y.tail) Bv Kc := by
  refine ⟨prog_ok, ?_, ?_⟩
  · intro y _ v hv
    have := le_Mmax hv
    unfold Bv; omega
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hL, hne⟩ := domain_facts hx
    refine ⟨fun a => if a = "a" then x.length else 0, ?_⟩
    have hB : ∀ v ∈ x, v < Bv (x.length :: x) := fun v hv => by
      have := le_Mmax (List.mem_cons_of_mem x.length hv)
      unfold Bv; omega
    have hxB : x.length + 1 < Bv (x.length :: x) := by unfold Bv; simp; omega
    obtain ⟨σ', hr, hq⟩ := prog_spec x (initEnv (fun a => if a = "a" then x.length else 0)
      (x.length :: x)) hB hxB hL hne rfl (by simp [initEnv]) rfl _ rfl
    exact ⟨σ', hr.mono (by simp [Kc]), hq⟩

theorem Bv_le (x : List ℕ) : Bv (x.length :: x) ≤ 2 ^ (bitSize x + 3) := by
  have h1 := Mmax_lt_two_pow x
  have h2 := length_lt_two_pow x
  have hm : Mmax (x.length :: x) ≤ 2 ^ bitSize x := by
    rw [Mmax_cons]; exact max_le (by omega) (by omega)
  have : 2 ^ (bitSize x + 3) = 8 * 2 ^ bitSize x := by ring
  unfold Bv; simp; omega

/-- **The reduction is computable in polynomial time.** -/
theorem forget_polyTime :
    PolyTimeOn Lax888481.MulticolouredClique.problem.Domain forget := by
  refine polyTimeOn_of_solves (c₀ := 1000) (d := 1) solves ?_ ?_ ?_
  · intro x _
    simp only [pow_one]
    have h := Bv_le x
    have hb : bitSize x + 5 ≤ 1000 * (bitSize x + 1) := by omega
    have hp : 2 ^ (bitSize x + 5) ≤ 2 ^ (1000 * (bitSize x + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hb
    have he : 2 ^ (bitSize x + 5) = 4 * 2 ^ (bitSize x + 3) := by ring
    refine ⟨by unfold Bv; omega, ?_⟩
    simp only [Layout.span, layout, List.length_cons, List.length_nil]
    have hpos : 2 ^ 3 ≤ 2 ^ (bitSize x + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (by omega) (by omega)
  · intro x _
    have := length_le_bitSize x
    simp [Kc, Layout.const]; omega
  · intro x _ v hv
    simp only [pow_one]
    have hle : v ≤ Mmax x := by
      simp only [forget, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact le_Mmax (List.mem_of_mem_take hv)
      · exact last_le_Mmax x
    have h1 := Mmax_lt_two_pow x
    have hp : 2 ^ bitSize x ≤ 2 ^ (1000 * (bitSize x + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/--
---
conclusion: Lax496464.WH_D12_MulticolouredClique.multicolouredClique_le_clique
---
**Multicoloured Clique ≤fpt p-Clique.** Forget the colours: the word keeps its graph block and its
last entry, the number of colours. A clique of `k` vertices in a properly `k`-coloured graph has one
vertex of each colour, and a multicoloured clique is a `k`-clique; the parameter is unchanged, and
the map is computed in linear time.
-/
theorem multicolouredClique_le_clique :
    Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ Clique :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime forget_isReduction forget_paramBounded
    forget_polyTime

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetFinal
