import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTop
import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.MathFinal

/-!
# Σ₁[2] Model Checking to Clique: the Value Bound and the Cost Bound

The value bound `Bv` on the tape `|x| :: x`, and the facts the running-time bound needs: the number
`NGX x` of vertices is at most `8 · 4^q · |x|` for `q` atoms, and on an instance `q ≤ |φ|` and the
number of symbols is at most `|x|`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Bounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTop
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-- The value bound, for the word `x`. -/
def bnd (x : List ℕ) : ℕ :=
  (x.length + Mmax x + 4) * (x.length + Mmax x + 4) + (NGX x + 1) * (NGX x + 1) + CX x +
    x.length + 10

/-- The value bound, on the tape. -/
def Bv (y : List ℕ) : ℕ := bnd y.tail + Mmax y + 1

/-- The cost bound, on the tape. -/
def Kc (y : List ℕ) : ℕ := 16 * y.tail.length + 7 + Kbody y.tail

theorem dg_le' (x : List ℕ) (s : ℕ) : dg x s ≤ NGX x := by
  show (List.filter _ (List.range (NGX x))).length ≤ NGX x
  exact (List.length_filter_le _ _).trans (by simp)

theorem ps_le' (x : List ℕ) (s : ℕ) : ps x s ≤ s * NGX x := by
  induction s with
  | zero => simp [Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord.psum]
  | succ s ih => rw [ps_succ, Nat.succ_mul]; have := dg_le' x s; omega

theorem ps_le_sq' (x : List ℕ) : ps x (NGX x) ≤ NGX x * NGX x := ps_le' x _

theorem bok (x : List ℕ) {B : ℕ} (hB : bnd x ≤ B) : BOK x B := by
  have hP := ps_le_sq' x
  have hsq : (NGX x + 1) * (NGX x + 1) = NGX x * NGX x + 2 * NGX x + 1 := by ring
  have hM : ∀ v ∈ x, v ≤ Mmax x := fun v hv => le_Mmax hv
  unfold bnd at hB
  have hW : (x.length + Mmax x + 4) * (x.length + Mmax x + 4) ≥ Mmax x + 4 := by nlinarith
  refine ⟨⟨⟨⟨fun v hv => by have := hM v hv; omega, by omega⟩, by omega, by omega⟩, by omega⟩,
    by omega⟩

theorem bnd_le_Bv (x : List ℕ) : bnd x ≤ Bv (x.length :: x) := by simp [Bv]; omega

/-! ### Sizes -/

theorem neX_le4 (x : List ℕ) : neX x ≤ 4 * x.length :=
  (neX_le x).trans (ProgElb.length_elL x)

theorem NGX_le (x : List ℕ) : NGX x ≤ 2 ^ qX x * (4 * x.length * (2 * qX x)) := by
  unfold NGX CX kX
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (neX_le4 x))

theorem limX_le' (x : List ℕ) : limX x ≤ x.length + 2 * qX x := ProgElb.limX_le x

/-- On an instance: the atoms are at most the parameter, the symbols at most the length. -/
theorem inst_facts {x : List ℕ} (hx : x ∈ MathFinal.Src.Domain) :
    qX x ≤ MathFinal.Src.param x ∧ sX x ≤ x.length := by
  obtain ⟨y, A, xs, ψ, hy, hxe, hq, hn, ha, hmc⟩ := MathFinal.domain_cases hx
  have hI : MathFinal.Inst x y A xs ψ := ⟨hy, hxe, hq, hn, ha⟩
  refine ⟨?_, ?_⟩
  · show qX x ≤ Lax496464.WH_B3_LogicProblems.mcParam x
    rw [hI.qX_eq, Lax496464Proofs.WHierarchy.Logic.Words.mcParam_eq hmc,
      Lax496464Proofs.WHierarchy.Logic.SatFacts.size_exBlock]
    have := MathFinal.nA_le_size ψ; omega
  · obtain ⟨blocks, hsw⟩ := hI.sw
    rw [hsw.sX_eq]
    have := hsw.length_y; have := hsw.length_le; omega

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Bounds
