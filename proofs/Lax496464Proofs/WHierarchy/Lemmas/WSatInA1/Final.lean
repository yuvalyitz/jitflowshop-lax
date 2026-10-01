import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Time
import Lax496464Proofs.WHierarchy.Machine.LastEntry

/-! # `p-WSat(d-CNF) ∈ A[1]`

The reduction `red d` from `p-WSat(d-CNF)` to `p-MC(Σ_1)` (`Defs`) is correct (`Reduction`), has a
parameter bounded by a computable function of `k`, and is computed by the IMP+ program `cmd d` in
fixed-parameter time: its cost is `8000 · Pk(k)³ · (|x| + 1)²` with `Pk(k) = (d + 2)^(k+1) (k + 2)^(d+3)`
(the `d^k` branch words of the bounded search tree make it fixed-parameter, not polynomial). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_B2_FirstOrder
open Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgOk
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Cost
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Reduction Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Time

variable {d : ℕ}

/-- The value bound, as a function of the tape. -/
def Bt (d : ℕ) (y : List ℕ) : ℕ := Bv d (bitSize y.tail) (kOf y.tail)

/-- The cost, as a function of the tape. -/
def Kt (d : ℕ) (y : List ℕ) : ℕ := Kall (clOf y.tail) d (kOf y.tail)

theorem two_pow_le_Bv (d n k : ℕ) : 2 ^ n ≤ Bv d n k := by
  unfold Bv
  have h2 : 1 ≤ (n + 4) ^ (d + k + 5) := Nat.one_le_pow _ _ (by omega)
  have h3 := one_le_Pk d k
  have : 2 ^ n ≤ 2 ^ n * (n + 4) ^ (d + k + 5) * Pk d k := by
    calc 2 ^ n = 2 ^ n * 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3
  have e : 16 * 2 ^ n * (n + 4) ^ (d + k + 5) * Pk d k =
      16 * (2 ^ n * (n + 4) ^ (d + k + 5) * Pk d k) := by ring
  omega

/-- The facts about an instance word. -/
theorem inst_facts (α : Lax429075.CNF.Formula) (k : ℕ) :
    (codesOf α).length + nL (codesOf α) + 2 ≤ bitSize (wordOf' (codesOf α) k) ∧
      ∀ v ∈ wordOf' (codesOf α) k, v < 2 ^ bitSize (wordOf' (codesOf α) k) :=
  ⟨by rw [← length_wordOf']; exact length_le_bitSize _, fun v hv => lt_two_pow_bitSize hv⟩

theorem solves (d : ℕ) :
    Solves layout (cmd d) (Tapes (pWSat {α | IsDCNF d α}).Domain) (fun y => red d y.tail) (Bt d)
      (Kt d) := by
  refine ⟨cmd_ok d, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    simp only [Bt, List.tail_cons]
    have h1 := two_pow_le_Bv d (bitSize x) (kOf x)
    rcases List.mem_cons.mp hv with rfl | hv
    · have := length_le_bitSize x
      have : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
      omega
    · have := lt_two_pow_bitSize hv; omega
  · rintro y ⟨x, ⟨α, hα, k, rfl⟩, rfl⟩
    simp only [Bt, Kt, List.tail_cons]
    rw [encode_eq, clOf_wordOf', kOf_wordOf']
    obtain ⟨hlen, hent⟩ := inst_facts α k
    obtain ⟨σ', hr, ho⟩ := cmd_run (d := d) (dcnf_codesOf hα) (bb_Bv (d := d) hlen hent)
    refine ⟨_, σ', hr, ?_⟩
    rw [ho, ← encode_eq, red_eq]

/-- **Step 3: the reduction is computable in fixed-parameter time.** -/
theorem fptTimeOn_red (d : ℕ) :
    FptTimeOn (pWSat {α | IsDCNF d α}).Domain (pWSat {α | IsDCNF d α}).param (red d) := by
  refine fptTimeOn_of_solves (L := layout) (c := cmd d) (B := Bt d) (K := Kt d) (f := ff d)
    (d := 2) (computable_ff d) (solves d) ?_ ?_ ?_
  · rintro x ⟨α, hα, k, rfl⟩
    have hp : (pWSat {α | IsDCNF d α}).param (encode α ++ [k]) = k := by simp [pWSat]
    simp only [Bt, List.tail_cons, fptBound, hp]
    rw [encode_eq, kOf_wordOf']
    set n := bitSize (wordOf' (codesOf α) k)
    have h1 := Bv_ge' d n k
    have h2 := Bv_le d n k
    have h3 := exp_le d n k
    have h4 := span_le (Bv d n k) h1
    have h5 : 2 ^ (7 + n + (n + 4) * (d + k + 5) + Pk d k) ≤ 2 ^ (ff d k * (n + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) h3
    exact ⟨by omega, max_le (by omega) (by omega)⟩
  · rintro x ⟨α, hα, k, rfl⟩
    have hp : (pWSat {α | IsDCNF d α}).param (encode α ++ [k]) = k := by simp [pWSat]
    simp only [Kt, List.tail_cons, fptBound, hp, Layout.const]
    rw [encode_eq, clOf_wordOf', kOf_wordOf']
    obtain ⟨hlen, -⟩ := inst_facts α k
    have := cost_le (d := d) (k := k) hlen
    unfold Kall ff
    have h1 : 1 ≤ Pk d k ^ 3 * (bitSize (wordOf' (codesOf α) k) + 1) ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (by have := one_le_Pk d k; positivity)
    have e1 : 8000 * Pk d k ^ 3 * (bitSize (wordOf' (codesOf α) k) + 1) ^ 2 =
        8000 * (Pk d k ^ 3 * (bitSize (wordOf' (codesOf α) k) + 1) ^ 2) := by ring
    have e2 : 90000 * Pk d k ^ 3 * (bitSize (wordOf' (codesOf α) k) + 1) ^ 2 =
        90000 * (Pk d k ^ 3 * (bitSize (wordOf' (codesOf α) k) + 1) ^ 2) := by ring
    omega
  · rintro x ⟨α, hα, k, rfl⟩ v hv
    have hp : (pWSat {α | IsDCNF d α}).param (encode α ++ [k]) = k := by simp [pWSat]
    simp only [fptBound, hp]
    rw [red_eq] at hv
    rw [encode_eq]
    obtain ⟨hlen, hent⟩ := inst_facts α k
    obtain ⟨σ', ⟨kk, -, hbs⟩, ho⟩ := cmd_run (d := d) (dcnf_codesOf hα) (bb_Bv (d := d) hlen hent)
    rw [← ho] at hv
    have hlt := bigStepB_out hbs (by simp [initEnv]) v hv
    set n := bitSize (wordOf' (codesOf α) k)
    have h2 := Bv_le d n k
    have h3 := exp_le d n k
    have h5 : 2 ^ (7 + n + (n + 4) * (d + k + 5) + Pk d k) ≤ 2 ^ (ff d k * (n + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) h3
    omega

/-- **`p-WSat(d-CNF) ≤fpt p-MC(Σ_1)`**, as an fpt-reduction. -/
theorem isFptReduction (d : ℕ) :
    IsFptReduction (pWSat {α | IsDCNF d α}) (pMC {φ | IsSigma 1 φ}) (red d) :=
  ⟨isReduction d, paramBounded d, fptTimeOn_red d⟩

/--
---
conclusion: Lax496464.WH_D08_WSatInA1.pWSat_mem_A1
---
**`p-WSat(d-CNF) ∈ A[1]`** (Flum–Grohe, Theorem 6.28). The reduction maps `(α, k)` to the
structure whose universe is the literal occurrences of `α` plus a padding element `z`, with the
first occurrences of the variables (`C`), the negative parts of the clauses as padded tuples (`N`),
and for every clause and every branch word `b < d^k` of the bounded search tree the pair of its
negative part and the found hitting set of the positive parts of the clauses with that negative
part (`Lr`); and to the `Σ_1`-sentence
`∃ x̄ w ȳ (Z w ∧ ⋀ C xᵢ ∧ ⋀_{j<i} ¬ xᵢ = xⱼ ∧ ⋀_t (¬ N v_t ∨ (Lr v_t y_t ∧ ⋀_j ⋁_i y_{t,j} = xᵢ)))`,
`t` ranging over the maps `{0,…,d} → {x_0,…,x_{k-1},w}`. It is computed in time
`O(Pk(k)³ · |x|²)`.
-/
theorem pWSat_mem_A1 (d : ℕ) : pWSat {α | IsDCNF d α} ∈ A 1 :=
  ⟨Lax496464Proofs.WHierarchy.Machine.LastEntry.polyTimeOn_last _, _, Set.mem_singleton _,
    red d, isFptReduction d⟩

example : type_of% @Lax496464.WH_D08_WSatInA1.pWSat_mem_A1 := @pWSat_mem_A1

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Final
