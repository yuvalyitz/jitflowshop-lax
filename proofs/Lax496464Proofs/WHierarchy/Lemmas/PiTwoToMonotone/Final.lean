import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PBounds
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Reduction
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464.WH_E2_HittingSetW2Complete

/-!
# `p-WD_φ ≤fpt p-WSat(monotone)` for `Π₂`-Sentences `φ` (Flum–Grohe, Theorem 7.1(1), `t = 2`)

## The Reduction

`φ = ∀ x̄ ∃ ȳ ψ(X)`, `ψ` quantifier-free, `X` of arity `s`; an instance `(A, k)`.

1. **Elements.** The universe size is a number of the word, so the reduction works with the list
   `U` of `n` elements of `Lemmas/WDToWSat` (`0, …, L-1` for `L = min(|A|, |x| + s·k + r)`, and every
   entry of the word below `|A|`); the elements outside `U` are isolated and interchangeable, and
   `U` has room for the `s·k` elements of a witness and the `r = |x̄| + |ȳ|` values of the variables,
   which is what a `Π₂` condition needs (`Pi2.witness_iff`, via `Pi2.pi2_compress`).
2. **Tuples, sets.** A tuple over `U` is a code `c < N = n^s`; a set of `k` tuples is an increasing
   list `t_0 < … < t_{k-1}` of codes.
3. **Blocks.** A block `b < W = (k+1)^D` names `D` indices in `{0, …, k}` (`k` = unused), and values
   `v < C = (N+1)^D` give each slot a code. The variable `Z(b, v) = 1 + b + W·v` says "block `b` has
   values `v`" (`0` is a dummy). `D = 2·#(X-atoms of ψ) + 2`.
4. **The monotone formula** (`Cnf.Par.alpha`), weight `W`: a clause per block (one true value per
   block, so exactly one, as the weight is the number of blocks), a clause per pair of blocks with
   conflicting values (so the true values come from one increasing `t`, `Blocks.exists_valid`), and
   per universal assignment `za` the clause of all `Z(b, v)` that make `ψ` true under some
   existential assignment `zb`, decided by a three-valued evaluation of `ψ` in which an `X`-atom
   `u ∈ t` is decided when a used slot has the value `u`, `u ∉ t` when `u` lies below index 0,
   above index `k-1` or strictly between the values of two consecutive indices
   (`Blocks.dec`, `Eval.ev`). Sound for the true block values (`Blocks.dec_sound`); complete since
   the indices around the `X`-atoms of `ψ` (at most `D`) form a block (`Blocks.dec_complete`).
   `Correct.witness_iff_weightSat`: satisfiable with weight `W` iff a witness exists.
5. The new parameter is `W = (k+1)^D`; when `ψ` does not fit the vocabulary of `A`, the reduction
   writes the no-instance `[[]]`.

Exact weight: every `Z(b, v)` occurs (in its block clause), and a satisfying set of `W` variables
has one per block, so `k = 0`, an empty universe (then `N = 0^s`), `s = 0` (`N = 1`), `k > N`
(no increasing list, the pair clauses fail) and empty quantifier blocks are all handled uniformly;
a `∀` over an empty universe is vacuous since the universal positions of shadowed variables are
kept (`Syntax.posList`).

## The Program

An IMP+ program (`PDefs.prog`), verified phase by phase (`PMain.prog_run`), runs within
`Kc · G⁵` steps (`PBounds.Kprog_le`) for `G = (c₀ (|x|+1) (k+1))^E₀`: fixed-parameter time.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Final

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Machine.ImpBridge
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (BF)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath (Good good_of_enc)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PMain Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PLayout
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PBounds Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Reduction

/-! ### The value bound -/

theorem BF.mono {D : Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output.Data} {x : List ℕ} {B B' : ℕ}
    (h : BF D x B) (hB : B ≤ B') : BF D x B' :=
  ⟨fun v hv => lt_of_lt_of_le (h.entries v hv) hB, by have := h.len; omega,
    by have := h.t0; omega, by have := h.n; omega, by have := h.pw; omega, by have := h.ucap; omega⟩

/-- **The value bound.** -/
def Bv (Dt : Data) (x : List ℕ) : ℕ :=
  Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds.Bv (wd Dt) x + big Dt x + 1

theorem BB_Bv (Dt : Data) (x : List ℕ) : BB Dt x (Bv Dt x) :=
  ⟨BF.mono (Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds.BF_Bv (wd Dt) x) (by unfold Bv; omega),
    by unfold Bv; omega⟩

/-- The exponent of the time bound. -/
def ee (Dt : Data) : ℕ := 5 * E0 Dt

/-- **The fixed-parameter factor.** -/
def fK (Dt : Data) (k : ℕ) : ℕ :=
  (10 * Kc Dt + Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) + 60) * c0 Dt ^ ee Dt *
    (k + 1) ^ ee Dt

theorem computable_fK (Dt : Data) : Computable (fK Dt) := by
  unfold fK
  refine Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const _) ?_
  exact Lax496464Proofs.WHierarchy.ComputableBounds.computable_pow _
    (Lax496464Proofs.WHierarchy.ComputableBounds.computable_add Computable.id (Computable.const 1))

/-- `G⁵` against the time bound. -/
theorem G5_le (Dt : Data) (x : List ℕ) :
    G Dt x ^ 5 ≤ c0 Dt ^ ee Dt * (kW x + 1) ^ ee Dt * (bitSize x + 1) ^ ee Dt := by
  have hl := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  unfold G Tb ee
  rw [← pow_mul, show E0 Dt * 5 = 5 * E0 Dt by ring, Nat.mul_pow, Nat.mul_pow]
  calc c0 Dt ^ (5 * E0 Dt) * ((x.length + 1) ^ (5 * E0 Dt) * (kW x + 1) ^ (5 * E0 Dt))
      ≤ c0 Dt ^ (5 * E0 Dt) * ((bitSize x + 1) ^ (5 * E0 Dt) * (kW x + 1) ^ (5 * E0 Dt)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
    _ = _ := by ring

theorem bound_ge (Dt : Data) (x : List ℕ) :
    Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) * (bitSize x + 1) + 40 * G Dt x ^ 5 +
      10 * Kc Dt * G Dt x ^ 5 ≤ fptBound (fK Dt) (ee Dt) (kW x) (bitSize x) := by
  have h5 := G5_le Dt x
  set Q := c0 Dt ^ ee Dt * (kW x + 1) ^ ee Dt * (bitSize x + 1) ^ ee Dt with hQ
  have hee : 1 ≤ ee Dt := by unfold ee E0; omega
  have hc0 : 1 ≤ c0 Dt ^ ee Dt := Nat.one_le_pow _ _ (by unfold c0; omega)
  have hk : 1 ≤ (kW x + 1) ^ ee Dt := Nat.one_le_pow _ _ (by omega)
  have hb : bitSize x + 1 ≤ (bitSize x + 1) ^ ee Dt := by
    have := Nat.pow_le_pow_right (show 1 ≤ bitSize x + 1 by omega) hee; simpa using this
  have hbQ : bitSize x + 1 ≤ Q := by
    rw [hQ]
    have : 1 ≤ c0 Dt ^ ee Dt * (kW x + 1) ^ ee Dt := Nat.mul_pos hc0 hk
    nlinarith
  have hf : fptBound (fK Dt) (ee Dt) (kW x) (bitSize x) =
      (10 * Kc Dt + Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) + 60) * Q := by
    unfold fptBound fK; rw [hQ]; ring
  rw [hf]
  have h1 : Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) * (bitSize x + 1) ≤
      Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) * Q := Nat.mul_le_mul_left _ hbQ
  nlinarith

theorem bits (Dt : Data) (x : List ℕ) :
    max (Bv Dt x) (layout.span (Bv Dt x)) ≤ 2 ^ fptBound (fK Dt) (ee Dt) (kW x) (bitSize x) := by
  have hw := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Bv_bits (wd Dt) x
  have hbig := big_le Dt x
  have hG := G_ge_one Dt x
  set A := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.Cv (wd Dt) * (bitSize x + 1) with hA
  set g := G Dt x with hg
  set Bb := 30 * g ^ 4 + 1 with hBb
  have hwB : Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds.Bv (wd Dt) x ≤ 2 ^ A :=
    (le_max_left _ _).trans hw
  have hbB : big Dt x + 1 ≤ 2 ^ Bb := by
    have := Nat.lt_two_pow_self (n := Bb); omega
  have hA1 : 2 ^ A ≤ 2 ^ (A + Bb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB1 : 2 ^ Bb ≤ 2 ^ (A + Bb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBv : Bv Dt x ≤ 2 * 2 ^ (A + Bb) := by unfold Bv; omega
  have hpos : 2 ≤ 2 ^ (A + Bb) := by
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show 1 ≤ A + Bb by omega); simpa using this
  have e8 : 2 ^ (A + Bb + 8) = 256 * 2 ^ (A + Bb) := by rw [pow_add]; ring
  have hspan : layout.span (Bv Dt x) ≤ 2 ^ (A + Bb + 8) := by
    simp only [Layout.span, layout, gScalars, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars,
      List.length_cons, List.length_nil, List.length_append]
    omega
  have hle : A + Bb + 8 ≤ fptBound (fK Dt) (ee Dt) (kW x) (bitSize x) := by
    have := bound_ge Dt x
    have g45 : g ^ 4 ≤ g ^ 5 := Nat.pow_le_pow_right hG (by omega)
    have : 1 ≤ g ^ 5 := Nat.one_le_pow _ _ hG
    rw [hBb]; nlinarith
  have hmono := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hle
  exact max_le (by omega) (hspan.trans hmono)

/-! ### The running time -/

/-- The atoms of the renamed formula fit a word that passes the fit test. -/
theorem atomsOk {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
    (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys) {x : List ℕ} (hfit : fitW (dataOf xs ys ψ s) x) :
    AtomsOk (dataOf xs ys ψ s) x (dataOf xs ys ψ s).ψ := by
  intro a ha
  have hpos := pos_lt (s := s) hq hv a ha
  have ha' := ha
  simp only [dataOf, atoms_rename, List.mem_map] at ha'
  obtain ⟨b, hb, rfl⟩ := ha'
  refine ⟨fun i js h => ?_, fun a1 a2 h => ?_, fun js h => ?_⟩
  · rcases isAtom_of_mem_atoms ψ b hb with ⟨i', zs, rfl⟩ | ⟨zs, rfl⟩ | ⟨u, w, rfl⟩
    · simp only [rename, Formula.rel.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hr := hfit.2 (i', zs.length) (List.mem_filterMap.mpr ⟨_, hb, rfl⟩)
      refine ⟨hr.1, by rw [hr.2, List.length_map], fun j hj => hpos j ?_⟩
      simp only [rename, Formula.freeVars, List.mem_toFinset]; exact hj
    · simp [rename] at h
    · simp [rename] at h
  · rcases isAtom_of_mem_atoms ψ b hb with ⟨i', zs, rfl⟩ | ⟨zs, rfl⟩ | ⟨u, w, rfl⟩
    · simp [rename] at h
    · simp [rename] at h
    · simp only [rename, Formula.eq.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hpos _ (by simp [rename, Formula.freeVars]), hpos _ (by simp [rename, Formula.freeVars])⟩
  · rcases isAtom_of_mem_atoms ψ b hb with ⟨i', zs, rfl⟩ | ⟨zs, rfl⟩ | ⟨u, w, rfl⟩
    · simp [rename] at h
    · simp only [rename, Formula.setVar.injEq] at h
      subst h
      have hs := List.all_eq_true.mp hfit.1 _ hb
      simp only [setOk, beq_iff_eq] at hs
      refine ⟨by rw [List.length_map]; exact hs, fun j hj => hpos j ?_⟩
      simp only [rename, Formula.freeVars, List.mem_toFinset]; exact hj
    · simp [rename] at h

theorem solves (Dt : Data) (P : Set (List ℕ))
    (hP : ∀ x ∈ P, Good x ∧ (fitW Dt x → AtomsOk Dt x Dt.ψ)) :
    Solves layout (prog Dt) (Tapes P) (fun y => R Dt y.tail) (fun y => Bv Dt y.tail)
      (fun y => Kprog Dt y.tail) := by
  refine ⟨ok_prog Dt, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have hB := (BB_Bv Dt x).bf
    simp only [List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := hB.len; omega
    · exact hB.entries v hv
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hg, hA⟩ := hP x hx
    obtain ⟨σ', hr, ho⟩ := prog_run (BB_Bv Dt x) hg hA
    exact ⟨_, σ', hr, ho⟩

/-- **Fixed-parameter time.** -/
theorem fptTimeOn {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
    (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys) :
    FptTimeOn (pWD (Formula.allBlock xs (Formula.exBlock ys ψ)) s).Domain
      (pWD (Formula.allBlock xs (Formula.exBlock ys ψ)) s).param (R (dataOf xs ys ψ s)) := by
  set Dt := dataOf xs ys ψ s with hDt
  set Pb := pWD (Formula.allBlock xs (Formula.exBlock ys ψ)) s with hPb
  have hP : ∀ x ∈ Pb.Domain, Good x ∧ (fitW Dt x → AtomsOk Dt x Dt.ψ) := by
    rintro x ⟨A, k, hxe⟩
    obtain ⟨bl, he⟩ := exists_enc hxe
    exact ⟨good_of_enc he, fun hfit => atomsOk hq hv hfit⟩
  have hkey : ∀ x ∈ Pb.Domain, Pb.param x = kW x := by
    rintro x ⟨A, k, hxe⟩
    obtain ⟨bl, he⟩ := exists_enc hxe
    rw [Lax496464Proofs.WHierarchy.Logic.Words.pWD_param_eq _ _ hxe, he.kW_eq]
  refine fptTimeOn_of_solves (f := fK Dt) (d := ee Dt) (computable_fK Dt)
    (solves Dt _ hP) (fun x hx => ⟨?_, ?_⟩) (fun x hx => ?_) (fun x hx v hv => ?_)
  · simp only [List.tail_cons]; have := (BB_Bv Dt x).bf.len; omega
  · simp only [List.tail_cons]; rw [hkey x hx]; exact bits Dt x
  · simp only [List.tail_cons, Layout.const]
    rw [hkey x hx]
    have h1 := Kprog_le Dt x (hP x hx).1
    have h2 := bound_ge Dt x
    have : 10 * (Kc Dt * G Dt x ^ 5) = 10 * Kc Dt * G Dt x ^ 5 := by ring
    have h3 : 1 ≤ G Dt x ^ 5 := Nat.one_le_pow _ _ (G_ge_one Dt x)
    nlinarith
  · obtain ⟨σ', hr, ho⟩ := prog_run (BB_Bv Dt x) (hP x hx).1 (hP x hx).2
    have hlt : v < Bv Dt x := by
      rw [← ho] at hv
      rcases Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Final.run_out hr v hv with h | h
      · simp [initEnv] at h
      · exact h
    rw [hkey x hx]
    exact lt_of_lt_of_le hlt ((le_max_left _ _).trans (bits Dt x))

/--
---
conclusion: Lax496464.WH_E2_HittingSetW2Complete.pWD_le_pWSat_monotone
---
**`p-WD_φ ≤fpt p-WSat(monotone CNF)`** for every `Π₂`-sentence `φ = ∀ x̄ ∃ ȳ ψ` (Flum–Grohe,
Theorem 7.1(1) for `t = 2`, via Lemma 7.2 and the Propositional Normalization Lemma 7.5). The
monotone formula has a variable for every block of `D` slots with values (`D` fixed by `ψ`), forces
one value per block by exact weight `W = (k+1)^D`, excludes conflicting pairs of block values by
monotone clauses, and has, per assignment of the universal variables, the clause of the blocks
with values that decide the `X`-atoms of `ψ` in a way making `ψ` true for some assignment of the
existential variables. It is computed in fixed-parameter time by an IMP+ program.
-/
theorem pWD_le_pWSat_monotone {φ : Formula} (s : ℕ) (hφ : IsPi 2 φ) (hs : IsSentence φ) :
    pWD φ s ≤ᶠᵖᵗ pWSat {α | IsMonotone α} := by
  obtain ⟨xs, ys, ψ, rfl, hq, hv⟩ := decompose hφ hs
  exact ⟨R (dataOf xs ys ψ s), ⟨isReduction hq hv, paramBounded _ s _, fptTimeOn hq hv⟩⟩

example : type_of% @Lax496464.WH_E2_HittingSetW2Complete.pWD_le_pWSat_monotone :=
  @pWD_le_pWSat_monotone

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Final
