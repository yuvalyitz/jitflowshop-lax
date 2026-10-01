import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PBound
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464.WH_D03_NegationElimination

/-!
# `p-MC(Σ_1) ≤fpt p-MC(Σ_1⁺)` (Flum–Grohe, Lemma 6.11)

The reduction `red` (`Math`) compresses the universe of the structure to the entries of its tuples
plus `|x|` further elements, expands it by the order `<`, and for every symbol `R` by its first
tuple, its last tuple, its consecutive pairs and `Z_R` (the universe if `R` is empty), and replaces
the formula by `phiOf`, the negation-free translation `tr` behind a block of fresh existential
quantifiers. It is correct (`Math.isReduction`), the new parameter is at most `72 k`
(`Math.paramBounded`), and the IMP+ program `cmd` computes it in `O(|x|³)` steps.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Final

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PMain
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PBound Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLayout
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr

variable {x : List ℕ}

/-- The lengths of the arrays. -/
def ext (x : List ℕ) (a : String) : ℕ :=
  if a = "a" ∨ a = "E" ∨ a = "fo" ∨ a = "R" then x.length else if a = "st" then x.length + 2 else 0

/-- The cost of the program. -/
def Kcmd (x : List ℕ) : ℕ := 16 * x.length + 7 + Kbody x

theorem entries_lt (x : List ℕ) : ∀ v ∈ x, v < Bv x := fun v hv => by
  have := le_maxEntry hv; have := Bv_big x; omega

theorem cmd_run {A : Structure} {φ : Formula} (h : EncodesMC x A φ) (hd : Dom x φ) :
    ∃ σ', Run (Bv x) cmd (initEnv (ext x) (x.length :: x)) σ' (Kcmd x) ∧ σ'.out = red x := by
  have hl := len_lt_Bv x
  set σ0 := initEnv (ext x) (x.length :: x) with hσ0
  obtain ⟨σ1, hr1, ha1, hn1, -, ho1, -, harr1⟩ :=
    readTape_spec x σ0 (entries_lt x) (by omega) rfl (by simp [σ0, initEnv, ext]) σ0 rfl
  have hE : σ1.arrs "E" = List.replicate x.length 0 := by
    rw [harr1 "E" (by decide)]; simp [σ0, initEnv, ext]
  have hfo : σ1.arrs "fo" = List.replicate x.length 0 := by
    rw [harr1 "fo" (by decide)]; simp [σ0, initEnv, ext]
  have hR : σ1.arrs "R" = List.replicate x.length 0 := by
    rw [harr1 "R" (by decide)]; simp [σ0, initEnv, ext]
  have hst : σ1.arrs "st" = List.replicate (x.length + 2) 0 := by
    rw [harr1 "st" (by decide)]; simp [σ0, initEnv, ext]
  obtain ⟨σ2, hr2, ho2⟩ := body_run h hd ha1 hn1 hE hfo hR hst
  refine ⟨σ2, hr1.seq hr2, ?_⟩
  rw [ho2, ho1]; simp [σ0, initEnv]

/-- The value bound, as a function of the tape. -/
def Btape (y : List ℕ) : ℕ := Bv y.tail

/-- The cost, as a function of the tape. -/
def Ktape (y : List ℕ) : ℕ := Kcmd y.tail

theorem solves :
    Solves layout cmd (Tapes (pMC {φ | IsSigma 1 φ}).Domain) (fun y => red y.tail) Btape Ktape := by
  refine ⟨cmd_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    simp only [Btape, List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := len_lt_Bv x; omega
    · exact entries_lt x v hv
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨A, φ, h, hd⟩ := dom_of_mem hx
    obtain ⟨σ', hr, ho⟩ := cmd_run h hd
    exact ⟨ext x, σ', hr, ho⟩

theorem out_lt {A : Structure} {φ : Formula} (h : EncodesMC x A φ) (hd : Dom x φ) :
    ∀ v ∈ red x, v < Bv x := by
  obtain ⟨σ', hr, ho⟩ := cmd_run h hd
  rw [← ho]
  exact Run.outBounded hr (by simp [initEnv])

theorem pow_bound (b c : ℕ) (hc : 20 ≤ c) : 2 * b + 20 ≤ c * (b + 1) ^ 3 := by
  have : b + 1 ≤ (b + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  nlinarith

/-- **Step 3: the reduction is computable in polynomial time.** -/
theorem polyTimeOn : PolyTimeOn (pMC {φ | IsSigma 1 φ}).Domain red := by
  refine polyTimeOn_of_solves (c₀ := 100000) (d := 3) solves (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx v hv => ?_)
  · have hB := Bv_lt x
    have hp : 2 ^ (2 * bitSize x + 20) ≤ 2 ^ (100000 * (bitSize x + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (pow_bound _ _ (by norm_num))
    simp only [Btape, List.tail_cons, Layout.span, layout, progVars, List.length_cons,
      List.length_nil]
    refine ⟨by have := len_lt_Bv x; omega, ?_⟩
    omega
  · obtain ⟨A, φ, h, hd⟩ := dom_of_mem hx
    have hK := Kbody_le hd
    have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
    simp only [Ktape, List.tail_cons, Layout.const, Kcmd]
    have h3 : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h4 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  · obtain ⟨A, φ, h, hd⟩ := dom_of_mem hx
    have := out_lt h hd v hv
    have hB := Bv_lt x
    have hp : 2 ^ (2 * bitSize x + 20) ≤ 2 ^ (100000 * (bitSize x + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (pow_bound _ _ (by norm_num))
    omega

/--
---
conclusion: Lax496464.WH_D03_NegationElimination.pMC_sigma1_le_positive
---
**`p-MC(Σ_1) ≤fpt p-MC(Σ_1⁺)`** (Flum–Grohe, Lemma 6.11). The universe is first compressed to the
entries of the tuples and `|x|` further elements (a `Σ_1`-formula of size at most `|x|` cannot
tell the difference); the structure is then expanded by the order `<` and, per symbol `R`, by its
first tuple, its last tuple, its consecutive pairs and `Z_R` (the universe if `R` is empty), and
every negative literal is replaced by a positive existential formula over these (`¬ x = y` by
`x < y ∨ y < x`). The new parameter is at most `72 k`, and the map is computed by an IMP+ program in
`O(|x|³)` steps.
-/
theorem pMC_sigma1_le_positive :
    pMC {φ | IsSigma 1 φ} ≤ᶠᵖᵗ pMC {φ | IsSigma 1 φ ∧ φ.IsPositive} :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTimeOn

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Final
