import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdTop
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds
import Lax496464Proofs.WHierarchy.Machine.ImpBridge

/-! # p-Clique ≤fpt Multicoloured Clique

The map `reduce` is a reduction (`ProdMath`), sends the parameter `k` to at most `k`, and is
computed by the IMP+ program of `ProdTop` in time `O(|x|^5)` (the `k ≤ n` branch writes a word of
`O(k² n²)` entries, each adjacency test scanning one block); the bridges turn these into an
fpt-reduction. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax271696.GraphEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdRow
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMain
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdTop Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-! ### Sizes -/

theorem dg_le (x : List ℕ) (s : ℕ) : dg x s ≤ NOf x := by
  show (List.filter _ (List.range (NOf x))).length ≤ NOf x
  exact (List.length_filter_le _ _).trans (by simp)

theorem ps_le (x : List ℕ) (s : ℕ) : ps x s ≤ s * NOf x := by
  induction s with
  | zero => simp [CsrWord.psum]
  | succ s ih => rw [ps_succ, Nat.succ_mul]; have := dg_le x s; omega

theorem ps_le_sq {x : List ℕ} {s : ℕ} (hs : s ≤ NOf x) : ps x s ≤ NOf x * NOf x :=
  (ps_le x s).trans (Nat.mul_le_mul_right _ hs)

theorem NOf_le {x : List ℕ} (hgood : Good x) (hk : kP x ≤ nV x) :
    NOf x ≤ x.length * x.length := by
  have := hgood.1
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The value bound, on the tape. -/
def Bv (y : List ℕ) : ℕ := (y.length + 2) ^ 4 + Mmax y + 1

/-- The cost bound, on the tape. -/
def Kc (y : List ℕ) : ℕ := 16 * y.tail.length + 7 + (20 + (1 + 3 + Kmain y.tail))

theorem quartic (l : ℕ) : l * l * (l * l) + l * l + l + 2 < (l + 3) ^ 4 := by
  have e : (l + 3) ^ 4 = l * l * (l * l) + 12 * (l * l * l) + 54 * (l * l) + 108 * l + 81 := by ring
  rw [e]; nlinarith [Nat.zero_le (l * l * l)]

theorem bok {x : List ℕ} (hgood : Good x) (hk : kP x ≤ nV x) :
    BOK x (Bv (x.length :: x)) := by
  have hN := NOf_le hgood hk
  have hP := ps_le_sq (x := x) le_rfl
  have hNN : NOf x * NOf x ≤ x.length * x.length * (x.length * x.length) := Nat.mul_le_mul hN hN
  have hq := quartic x.length
  have hB : Bv (x.length :: x) = (x.length + 3) ^ 4 + Mmax (x.length :: x) + 1 := by
    simp [Bv]
  refine ⟨⟨hgood, fun w hw => ?_, ?_⟩, ?_⟩
  · have := le_Mmax (List.mem_cons_of_mem x.length hw); rw [hB]; omega
  · rw [hB]; omega
  · rw [hB]; omega

theorem domain_good {x : List ℕ} (hx : x ∈ Clique.Domain) : Good x := by
  obtain ⟨n, G, k, g, hxe, hg⟩ := hx
  exact good_of hxe hg

theorem solves :
    Solves layout prog (Tapes Clique.Domain) (fun y => reduce y.tail) Bv Kc := by
  refine ⟨prog_ok, ?_, ?_⟩
  · intro y _ v hv
    have := le_Mmax hv
    unfold Bv; omega
  · rintro y ⟨x, hx, rfl⟩
    have hgood := domain_good hx
    refine ⟨fun a => if a = "a" then x.length else 0, ?_⟩
    have hent : ∀ v ∈ x, v < Bv (x.length :: x) := fun v hv => by
      have := le_Mmax (List.mem_cons_of_mem x.length hv)
      unfold Bv; omega
    have hxB : x.length + 1 < Bv (x.length :: x) := by
      have := le_Mmax (List.mem_cons_self (a := x.length) (l := x))
      have : 1 ≤ ((x.length :: x).length + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
      unfold Bv; omega
    obtain ⟨σ', hr, hq⟩ := prog_spec x (initEnv (fun a => if a = "a" then x.length else 0)
      (x.length :: x)) hgood hent hxB (bok hgood) rfl (by simp [initEnv]) rfl _ rfl
    exact ⟨σ', hr.mono (by simp [Kc]), hq⟩

/-! ### The polynomial bounds -/

theorem Ksum_le {x : List ℕ} (hgood : Good x) (hk : kP x ≤ nV x) :
    Ksum x ≤ 1100 * (x.length + 1) ^ 5 := by
  have hN := NOf_le hgood hk
  set L := x.length with hL
  set M := L + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have h25 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by norm_num)
  have h15 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ hM1
  have hN' : NOf x ≤ M ^ 2 := hN.trans (by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega))
  have hA : Kadj x + 100 + 4 ≤ 264 * M := by unfold Kadj; omega
  have hAN : (Kadj x + 100 + 4) * NOf x ≤ 264 * M ^ 3 := by
    calc (Kadj x + 100 + 4) * NOf x ≤ (264 * M) * M ^ 2 := Nat.mul_le_mul hA hN'
      _ = 264 * M ^ 3 := by ring
  have hR : Krow x + 20 + 4 ≤ 264 * M ^ 3 + 32 := by unfold Krow; omega
  have hK1 : (Krow x + 20 + 4) * NOf x ≤ 264 * M ^ 5 + 32 * M ^ 2 := by
    calc (Krow x + 20 + 4) * NOf x ≤ (264 * M ^ 3 + 32) * M ^ 2 := Nat.mul_le_mul hR hN'
      _ = 264 * M ^ 5 + 32 * M ^ 2 := by ring
  have hK3 : (Krow x + 10 + 4) * NOf x ≤ 264 * M ^ 5 + 32 * M ^ 2 :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hK1
  unfold Ksum K1 K3 K4
  omega

theorem Kmain_le {x : List ℕ} (hgood : Good x) : Kmain x ≤ 1120 * (x.length + 1) ^ 5 := by
  have h15 : 1 ≤ (x.length + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  unfold Kmain
  split_ifs with h
  · omega
  · have := Ksum_le hgood (by omega); omega

theorem two_pow_ge (b : ℕ) : b + 3 ≤ 2 ^ (b + 2) := by
  have h := @Nat.lt_two_pow_self b
  have e : 2 ^ (b + 2) = 4 * 2 ^ b := by ring
  omega

theorem entry_le {x : List ℕ} (hx : x ∈ Clique.Domain) {v : ℕ} (hv : v ∈ reduce x) :
    v ≤ (x.length + 3) ^ 4 := by
  have hgood := domain_good hx
  have hq := quartic x.length
  unfold reduce at hv
  split_ifs at hv with hnk
  · simp [noWord] at hv
    rcases hv with rfl | rfl <;> omega
  · have hk : kP x ≤ nV x := by omega
    have hN := NOf_le hgood hk
    have hNN : NOf x * NOf x ≤ x.length * x.length * (x.length * x.length) := Nat.mul_le_mul hN hN
    have hP := ps_le_sq (x := x) le_rfl
    have hn3 := hgood.1
    have hN2 : NOf x ≤ NOf x * NOf x ∨ NOf x = 0 := by
      rcases Nat.eq_zero_or_pos (NOf x) with h | h
      · exact Or.inr h
      · exact Or.inl (Nat.le_mul_of_pos_left _ h)
    rw [word_eq] at hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hv
    have main : v ≤ NOf x * NOf x ∨ v ≤ x.length := by
      rcases hv with rfl | rfl | rfl | ((⟨s, hs, rfl⟩ | ⟨s, hs, ht⟩) | ⟨s, hs, rfl⟩) | rfl
      · rcases hN2 with h | h <;> omega
      · left; omega
      · omega
      · left; exact ps_le_sq (by omega)
      · left
        have : v < NOf x := CsrWord.mem_nbW_lt _ _ ht
        rcases hN2 with h | h <;> omega
      · left
        have := Nat.div_le_self s (nV x)
        rcases hN2 with h | h <;> omega
      · right; omega
    omega

/-- **The reduction is computable in polynomial time.** -/
theorem reduce_polyTime : PolyTimeOn Clique.Domain reduce := by
  refine polyTimeOn_of_solves (c₀ := 20000) (d := 5) solves ?_ ?_ ?_
  · intro x _
    set b := bitSize x with hb
    have hl : x.length ≤ b := length_le_bitSize x
    have h2 := two_pow_ge b
    have h4 : (x.length + 3) ^ 4 ≤ (2 ^ (b + 2)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e4 : (2 ^ (b + 2)) ^ 4 = 2 ^ (4 * b + 8) := by rw [← Nat.pow_mul]; ring_nf
    have hm : Mmax (x.length :: x) < 2 ^ b := by
      rw [Mmax_cons]
      have : Mmax x < 2 ^ b := Mmax_lt_two_pow x
      have : x.length < 2 ^ b := length_lt_two_pow x
      exact max_lt (by omega) (by omega)
    have hbm : 2 ^ b ≤ 2 ^ (4 * b + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hBv : Bv (x.length :: x) + 40 ≤ 2 ^ (4 * b + 10) := by
      have e : 2 ^ (4 * b + 10) = 4 * 2 ^ (4 * b + 8) := by ring
      have h8 : 2 ^ 8 ≤ 2 ^ (4 * b + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Bv, List.length_cons]
      rw [show x.length + 1 + 2 = x.length + 3 by omega]
      omega
    have hT : 4 * b + 10 ≤ 20000 * (b + 1) ^ 5 := by
      have : b + 1 ≤ (b + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
      omega
    have hp : 2 ^ (4 * b + 10) ≤ 2 ^ (20000 * (b + 1) ^ 5) := Nat.pow_le_pow_right (by norm_num) hT
    refine ⟨?_, ?_⟩
    · have : 1 ≤ (x.length + 1 + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
      simp only [Bv, List.length_cons]; omega
    · simp only [Layout.span, layout, bodyVars, List.length_cons, List.length_nil,
        List.length_append]
      exact max_le (by omega) (by omega)
  · intro x hx
    have hgood := domain_good hx
    have hl := length_le_bitSize x
    have hK := Kmain_le hgood
    have h5 : (x.length + 1) ^ 5 ≤ (bitSize x + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have h1 : x.length + 1 ≤ (x.length + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
    simp only [Kc, List.tail_cons, Layout.const]
    omega
  · intro x hx v hv
    set b := bitSize x with hb
    have hl : x.length ≤ b := length_le_bitSize x
    have h1 := entry_le hx hv
    have h2 := two_pow_ge b
    have h4 : (x.length + 3) ^ 4 ≤ (2 ^ (b + 2)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e4 : (2 ^ (b + 2)) ^ 4 = 2 ^ (4 * b + 8) := by rw [← Nat.pow_mul]; ring_nf
    have hT : 4 * b + 9 ≤ 20000 * (b + 1) ^ 5 := by
      have : b + 1 ≤ (b + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
      omega
    have hlt : 2 ^ (4 * b + 8) < 2 ^ (20000 * (b + 1) ^ 5) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

/--
---
conclusion: Lax496464.WH_D12_MulticolouredClique.clique_le_multicolouredClique
---
**p-Clique ≤fpt Multicoloured Clique.** For `k ≤ n`, take `k` copies of the vertex set, the copy
`c` coloured `c`, and join `(c, u)` and `(c', v)` when `c ≠ c'` and `uv` is an edge; a
multicoloured clique picks `k` distinct pairwise adjacent vertices, and conversely. For `k > n`
the word of a fixed no-instance (one colour, no vertices) is written. The number of colours is at
most `k`, and the map is computed in polynomial time.
-/
theorem clique_le_multicolouredClique :
    Clique ≤ᶠᵖᵗ Lax888481.MulticolouredClique.problem :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime reduce_isReduction reduce_paramBounded
    reduce_polyTime

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdFinal
