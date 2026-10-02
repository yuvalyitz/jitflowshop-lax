import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.ComputableBounds
import Lax496464.WH_D07_DefinabilityToWSat

/-!
# `p-WD_φ ≤fpt p-WSat(d-CNF)` for `Π_1`-Sentences `φ` (Flum–Grohe, Lemma 6.37)

The reduction `R (dataOf xs ψ s)` of `Reduction` is computed by the IMP+ program `prog` within
`400 · (Cc · (|x| + 1) · (k + 1))^(r+s+2)` steps with values below `Bv`: fixed-parameter time.

The time is fixed-parameter, not polynomial: a structure may have a universe far larger than its
word (its size is written in binary), so the reduction works with `|x| + s·k + r` of the elements
outside the relations, which is enough by the interchangeability of isolated elements
(`Semantics.witness_iff`); the formula then has `(2|x| + s·k + r)^s` variables.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Machine.ImpBridge
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Correct Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Reduction
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds

/-! ### Outputs are below the bound -/

theorem bigStepB_out {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    ∀ v ∈ σ'.out, v ∈ σ.out ∨ v < B := by
  induction h with
  | skip => exact fun v hv => Or.inl hv
  | assign _ => exact fun v hv => Or.inl hv
  | store _ _ _ => exact fun v hv => Or.inl hv
  | seq _ _ ih ih' => intro v hv; rcases ih' v hv with h | h; exacts [ih v h, Or.inr h]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => intro v hv; rcases ih' v hv with h | h; exacts [ih v h, Or.inr h]
  | while_false _ => exact fun v hv => Or.inl hv
  | read _ => exact fun v hv => Or.inl hv
  | write h =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inl hv
    · simp at hv; subst hv; exact Or.inr (Expr.lt_of_evalB h)

theorem run_out {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    ∀ v ∈ σ'.out, v ∈ σ.out ∨ v < B := by
  obtain ⟨k, -, hb⟩ := h
  exact bigStepB_out hb

/-! ### The literals of the formula's CNF -/

theorem cnfOk {xs : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs)
    {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl)
    (hfit : fitW (dataOf xs ψ s) x) {B : ℕ} (hB : BF (dataOf xs ψ s) x B) :
    CnfOk (dataOf xs ψ s) x B := by
  intro C hC
  have hfacts := lit_facts hq he hfit C hC
  have hidx := idxs_lt (s := s) hq hv C hC
  refine ⟨fun l hl => ⟨fun i js h => ?_, fun js h => (hfacts l hl).2 js h,
    fun j hj => hidx l hl j hj⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (hfacts l hl).1 i js h
    exact ⟨by rw [he.spW_eq]; exact h1, by rw [he.arity h1]; exact h2⟩
  · have h1 := List.length_filter_le isXLit C
    have h2 : C.length ≤ ((dataOf xs ψ s).cnf.map List.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hC)
    have := hB.const; unfold cD at this; omega

/-! ### The value bound in bits -/

/-- The bit constant of the value bound. -/
def Hc (D : Data) : ℕ := D.s + cD D + 7

/-- The linear factor of the value bound's bit length. -/
def Cv (D : Data) : ℕ := (Hc D + 1) * (D.r + D.s + 1) + D.cnf.length + 10

theorem Bv_bits (D : Data) (x : List ℕ) :
    max (Bv D x) (layout.span (Bv D x)) ≤ 2 ^ (Cv D * (bitSize x + 1)) := by
  set b := bitSize x
  set H := Hc D
  have hl := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have hm := mx_lt x
  have hb : b < 2 ^ b := Nat.lt_two_pow_self
  have hH : H < 2 ^ H := Nat.lt_two_pow_self
  have hP : Wv D x + 1 ≤ 2 ^ (b + H) := by
    rw [pow_add]
    have h1 : Wv D x + 1 ≤ H * 2 ^ b := by
      unfold Wv
      have : (D.s + 1) * mx x ≤ (D.s + 1) * 2 ^ b := Nat.mul_le_mul_left _ hm.le
      have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      have h3 : (cD D + 4) ≤ (cD D + 4) * 2 ^ b := Nat.le_mul_of_pos_right _ h2
      have h4 : H * 2 ^ b = (D.s + 1) * 2 ^ b + 2 * 2 ^ b + (cD D + 4) * 2 ^ b := by
        simp only [H, Hc]; ring
      omega
    calc Wv D x + 1 ≤ H * 2 ^ b := h1
      _ ≤ 2 ^ H * 2 ^ b := Nat.mul_le_mul_right _ hH.le
      _ = 2 ^ b * 2 ^ H := Nat.mul_comm _ _
  set P := 2 ^ (b + H) with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hq1 : (Wv D x + 1) ^ (D.r + D.s) ≤ P ^ (D.r + D.s + 1) :=
    (Nat.pow_le_pow_left hP _).trans (Nat.pow_le_pow_right hP1 (by omega))
  have hq2 : P ≤ P ^ (D.r + D.s + 1) := by
    have := Nat.pow_le_pow_right hP1 (show 1 ≤ D.r + D.s + 1 by omega); simpa using this
  have hm2 : D.cnf.length + 2 + 4 ≤ 2 ^ (D.cnf.length + 4) := by
    have := Nat.lt_two_pow_self (n := D.cnf.length + 2)
    have h2 : 2 ^ (D.cnf.length + 4) = 2 ^ (D.cnf.length + 2) * 4 := by
      rw [show D.cnf.length + 4 = (D.cnf.length + 2) + 2 by ring, pow_add]; norm_num
    omega
  have hBv : Bv D x ≤ P ^ (D.r + D.s + 1) * 2 ^ (D.cnf.length + 4) := by
    unfold Bv
    have : (Wv D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) ≤
        P ^ (D.r + D.s + 1) * (D.cnf.length + 2) := Nat.mul_le_mul_right _ hq1
    have h4 : P ^ (D.r + D.s + 1) * (D.cnf.length + 2 + 4) ≤
        P ^ (D.r + D.s + 1) * 2 ^ (D.cnf.length + 4) := Nat.mul_le_mul_left _ hm2
    nlinarith
  have hexp : P ^ (D.r + D.s + 1) * 2 ^ (D.cnf.length + 4) =
      2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 4) := by
    rw [hPdef, ← pow_mul, ← pow_add]; ring_nf
  rw [hexp] at hBv
  have hspan : layout.span (Bv D x) ≤ 2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 10) := by
    simp only [Layout.span, layout, scalars, List.length_cons, List.length_nil]
    have h1 : 2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 10) =
        2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 4) * 64 := by
      rw [show (b + H) * (D.r + D.s + 1) + D.cnf.length + 10 =
        ((b + H) * (D.r + D.s + 1) + D.cnf.length + 4) + 6 by ring, pow_add]; norm_num
    have h2 : 1 ≤ 2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 4) := Nat.one_le_two_pow
    omega
  have hle : (b + H) * (D.r + D.s + 1) + D.cnf.length + 10 ≤ Cv D * (b + 1) := by
    unfold Cv
    have : (b + H) * (D.r + D.s + 1) ≤ (H + 1) * (D.r + D.s + 1) * (b + 1) := by
      have : b + H ≤ (H + 1) * (b + 1) := by nlinarith
      calc (b + H) * (D.r + D.s + 1) ≤ (H + 1) * (b + 1) * (D.r + D.s + 1) :=
            Nat.mul_le_mul_right _ this
        _ = (H + 1) * (D.r + D.s + 1) * (b + 1) := by ring
    have h2 : D.cnf.length + 10 ≤ (D.cnf.length + 10) * (b + 1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hmono := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hle
  have hmono' : 2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 4) ≤
      2 ^ ((b + H) * (D.r + D.s + 1) + D.cnf.length + 10) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact max_le (by omega) (by omega)

/-! ### The time -/

/-- The fixed-parameter factor. -/
def fK (D : Data) (k : ℕ) : ℕ := (4001 * Cc D ^ ee D + Cv D) * (k + 1) ^ ee D

theorem computable_fK (D : Data) : Computable (fK D) := by
  unfold fK
  refine Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const _) ?_
  exact Lax496464Proofs.WHierarchy.ComputableBounds.computable_pow _
    (Lax496464Proofs.WHierarchy.ComputableBounds.computable_add Computable.id (Computable.const 1))

theorem solves (D : Data) (P : Set (List ℕ))
    (hP : ∀ x ∈ P, Good x ∧ (fitW D x → CnfOk D x (Bv D x))) :
    Solves layout (prog D) (Tapes P) (fun y => R D y.tail) (fun y => Bv D y.tail)
      (fun y => Kprog D y.tail) := by
  refine ⟨ok_prog D, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have hB := BF_Bv D x
    simp only [List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := hB.len; omega
    · exact hB.entries v hv
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hg, hC⟩ := hP x hx
    obtain ⟨σ', hr, ho⟩ := prog_run (BF_Bv D x) hg hC
    exact ⟨_, σ', hr, ho⟩

theorem fptTimeOn {xs : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
    (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) :
    FptTimeOn (pWD (Formula.allBlock xs ψ) s).Domain (pWD (Formula.allBlock xs ψ) s).param
      (R (dataOf xs ψ s)) := by
  set D := dataOf xs ψ s with hD
  have hP : ∀ x ∈ (pWD (Formula.allBlock xs ψ) s).Domain,
      Good x ∧ (fitW D x → CnfOk D x (Bv D x)) := by
    rintro x ⟨A, k, hxe⟩
    obtain ⟨bl, he⟩ := exists_enc hxe
    exact ⟨good_of_enc he, fun hfit => cnfOk hq hv he hfit (BF_Bv D x)⟩
  have hkey : ∀ x ∈ (pWD (Formula.allBlock xs ψ) s).Domain,
      (pWD (Formula.allBlock xs ψ) s).param x = kW x := by
    rintro x ⟨A, k, hxe⟩
    obtain ⟨bl, he⟩ := exists_enc hxe
    rw [Lax496464Proofs.WHierarchy.Logic.Words.pWD_param_eq _ _ hxe, he.kW_eq]
  have hbits : ∀ x ∈ (pWD (Formula.allBlock xs ψ) s).Domain,
      max (Bv D x) (layout.span (Bv D x)) ≤
        2 ^ fptBound (fK D) (ee D) ((pWD (Formula.allBlock xs ψ) s).param x) (bitSize x) := by
    intro x hx
    refine (Bv_bits D x).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    unfold fptBound fK
    rw [hkey x hx]
    have h1 : Cv D ≤ (4001 * Cc D ^ ee D + Cv D) * (kW x + 1) ^ ee D := by
      have : 1 ≤ (kW x + 1) ^ ee D := Nat.one_le_pow _ _ (by omega)
      calc Cv D ≤ 4001 * Cc D ^ ee D + Cv D := by omega
        _ ≤ (4001 * Cc D ^ ee D + Cv D) * (kW x + 1) ^ ee D := Nat.le_mul_of_pos_right _ this
    have h2 : bitSize x + 1 ≤ (bitSize x + 1) ^ ee D := by
      have := Nat.pow_le_pow_right (show 1 ≤ bitSize x + 1 by omega)
        (show 1 ≤ ee D by unfold ee; omega)
      simpa using this
    exact Nat.mul_le_mul h1 h2
  refine fptTimeOn_of_solves (f := fK D) (d := ee D) (computable_fK D)
    (solves D _ hP) (fun x hx => ⟨?_, ?_⟩) (fun x hx => ?_) (fun x hx v hv => ?_)
  · simp only [List.tail_cons]; have := (BF_Bv D x).len; omega
  · simp only [List.tail_cons]; exact hbits x hx
  · simp only [List.tail_cons, Layout.const]
    have h1 := Kprog_le D x (hP x hx).1
    have h2 := Tq_le D x
    unfold fptBound fK
    rw [hkey x hx]
    have h3 : 10 * (400 * Tq D x ^ ee D) + 1 ≤
        (4001 * Cc D ^ ee D + Cv D) * (kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D := by
      have hpos : 1 ≤ (kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e1 : (4001 * Cc D ^ ee D + Cv D) * (kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D =
          4001 * (Cc D ^ ee D * (kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D) +
            Cv D * ((kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D) := by ring
      have hCv : 1 ≤ Cv D := by unfold Cv; omega
      have : 1 ≤ Cv D * ((kW x + 1) ^ ee D * (bitSize x + 1) ^ ee D) :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    omega
  · obtain ⟨σ', hr, ho⟩ := prog_run (BF_Bv D x) (hP x hx).1 (hP x hx).2
    have hlt : v < Bv D x := by
      rw [← ho] at hv
      rcases run_out hr v hv with h | h
      · simp [initEnv] at h
      · exact h
    exact lt_of_lt_of_le hlt ((le_max_left _ _).trans (hbits x hx))

/--
---
conclusion: Lax496464.WH_D07_DefinabilityToWSat.pWD_le_pWSat
---
**`p-WD_φ ≤fpt p-WSat(d-CNF)`** for every `Π_1`-sentence `φ = ∀ xs ψ` (Flum–Grohe, Lemma 6.37),
with `d = 2 + (the total length of the clauses of a CNF of ψ)`. The formula has a variable for
each `s`-tuple of the elements `U` (the elements `0, …, L-1`, `L = min(|A|, |x| + s·k + r)`, and
every element occurring in a relation), a clause per assignment of elements of `U` to the variables
and clause of the CNF (its `X`-literals, or `Y₀ ∨ ¬Y₀` when a literal without `X` holds), and the
clauses `Y ∨ ¬Y`; `k` stays `k`. Elements outside `U` are isolated and interchangeable, so a witness
exists iff one exists within `U`. The map is computed in fixed-parameter time by an IMP+ program.
-/
theorem pWD_le_pWSat {φ : Formula} (s : ℕ) (hφ : IsPi 1 φ) (hs : IsSentence φ) :
    ∃ d, pWD φ s ≤ᶠᵖᵗ pWSat {α | IsDCNF d α} := by
  obtain ⟨xs, ψ, rfl, hq, hv⟩ := decompose hφ hs
  exact ⟨dBound (dataOf xs ψ s), R (dataOf xs ψ s),
    ⟨isReduction hq hv, paramBounded _ s _, fptTimeOn hq hv⟩⟩

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final
