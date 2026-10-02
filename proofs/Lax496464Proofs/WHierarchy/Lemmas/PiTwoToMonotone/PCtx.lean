import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW

/-!
# The Value Bound and the Context of the Phases

`BB Dt x B`: the facts about the value bound `B` the program needs (those of `Lemmas/WDToWSat` for
the setup, and one inequality bounding the constants of the formula). `GC Dt x σ`: the arrays and
scalars set up before the phases, which every phase keeps.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs

/-- The largest constant of the formula. -/
def big (Dt : Data) (x : List ℕ) : ℕ :=
  (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C +
    (par Dt x).W * (par Dt x).C * (par Dt x).Q + (par Dt x).P +
    2 * ((par Dt x).W * (par Dt x).C + (par Dt x).W + 1) + kW x + nU Dt x ^ Dt.s +
    Dt.D * Dt.D + Dt.r + (nU Dt x ^ Dt.s + 2) ^ Dt.D + (kW x + 2) ^ Dt.D + 4

/-- **The facts about the value bound.** -/
structure BB (Dt : Data) (x : List ℕ) (B : ℕ) : Prop where
  bf : BF (wd Dt) x B
  big : big Dt x < B

/-- The scalars of the context. -/
def gcVars : List String :=
  ["w_n", "w_k", "g_NT", "g_M", "g_C", "g_k1", "g_W", "g_D", "g_DD", "g_C2", "g_WCQ", "g_P", "g_Q"]

/-- The arrays the phases may change. -/
def gcArrs : List String := ["od", "bd1", "vd1", "bd2", "vd2"]

/-- **The context of the phases.** -/
structure GC (Dt : Data) (x : List ℕ) (σ : Env) : Prop where
  ctx : Ctx (wd Dt) x σ
  k : σ.vars "w_k" = kW x
  NT : σ.vars "g_NT" = nU Dt x ^ Dt.s
  M : σ.vars "g_M" = nU Dt x ^ Dt.s + 1
  C : σ.vars "g_C" = (par Dt x).C
  k1 : σ.vars "g_k1" = kW x + 1
  W : σ.vars "g_W" = (par Dt x).W
  D : σ.vars "g_D" = Dt.D
  DD : σ.vars "g_DD" = Dt.D * Dt.D
  C2 : σ.vars "g_C2" = 2 * (par Dt x).C
  WCQ : σ.vars "g_WCQ" = (par Dt x).W * (par Dt x).C * (par Dt x).Q
  P : σ.vars "g_P" = (par Dt x).P
  Q : σ.vars "g_Q" = (par Dt x).Q
  bd1 : (σ.arrs "bd1").length = Dt.D
  vd1 : (σ.arrs "vd1").length = Dt.D
  bd2 : (σ.arrs "bd2").length = Dt.D
  vd2 : (σ.arrs "vd2").length = Dt.D

variable {Dt : Data} {x : List ℕ}

/-- The context survives a change of other scalars and of the working arrays, lengths kept. -/
theorem GC.frame {σ σ' : Env} {S A : List String} (h : GC Dt x σ) (hf : Frame S A σ σ')
    (hS : ∀ y ∈ S, y ∉ gcVars) (hA : ∀ b ∈ A, b ∈ gcArrs)
    (hlen : ∀ b ∈ gcArrs, (σ'.arrs b).length = (σ.arrs b).length) : GC Dt x σ' := by
  have hv : ∀ y ∈ gcVars, σ'.vars y = σ.vars y := fun y hy => hf.1 y fun hm => hS y hm hy
  have ha : ∀ b, b ∉ gcArrs → σ'.arrs b = σ.arrs b := fun b hb => hf.2.1 b fun hm => hb (hA b hm)
  have hna : ∀ b ∈ ["a", "bo", "U"], σ'.arrs b = σ.arrs b := fun b hb =>
    ha b (by simp [gcArrs] at hb ⊢; rcases hb with rfl | rfl | rfl <;> simp)
  have hctx : Ctx (wd Dt) x σ' :=
    ⟨by rw [hna "a" (by simp)]; exact h.ctx.a, by rw [hna "bo" (by simp)]; exact h.ctx.bo,
      by rw [hna "U" (by simp)]; exact h.ctx.U, by rw [hna "U" (by simp)]; exact h.ctx.Ulen,
      by rw [hlen "od" (by simp [gcArrs])]; exact h.ctx.odlen,
      by rw [hv "w_n" (by simp [gcVars])]; exact h.ctx.n⟩
  have hv' : ∀ y ∈ gcVars, ∀ c, σ.vars y = c → σ'.vars y = c := fun y hy c e => (hv y hy).trans e
  have hl' : ∀ b ∈ gcArrs, ∀ c, (σ.arrs b).length = c → (σ'.arrs b).length = c :=
    fun b hb c e => (hlen b hb).trans e
  exact ⟨hctx, hv' _ (by simp [gcVars]) _ h.k, hv' _ (by simp [gcVars]) _ h.NT,
    hv' _ (by simp [gcVars]) _ h.M, hv' _ (by simp [gcVars]) _ h.C,
    hv' _ (by simp [gcVars]) _ h.k1, hv' _ (by simp [gcVars]) _ h.W,
    hv' _ (by simp [gcVars]) _ h.D, hv' _ (by simp [gcVars]) _ h.DD,
    hv' _ (by simp [gcVars]) _ h.C2, hv' _ (by simp [gcVars]) _ h.WCQ,
    hv' _ (by simp [gcVars]) _ h.P, hv' _ (by simp [gcVars]) _ h.Q,
    hl' _ (by simp [gcArrs]) _ h.bd1, hl' _ (by simp [gcArrs]) _ h.vd1,
    hl' _ (by simp [gcArrs]) _ h.bd2, hl' _ (by simp [gcArrs]) _ h.vd2⟩

/-- The context survives setting a scalar outside it. -/
theorem GC.setVar {σ : Env} (h : GC Dt x σ) {y : String} (hy : y ∉ gcVars) (v : ℕ) :
    GC Dt x (σ.setVar y v) :=
  h.frame (Frame.setVar σ (S := [y]) (A := []) (by simp) v) (by simpa using hy) (by simp)
    (fun _ _ => rfl)

/-! ### Consequences of the value bound -/

section Bounds
variable {B : ℕ} (hB : BB Dt x B)
include hB

omit hB in
theorem BB.W_pos (_hB : BB Dt x B) : 0 < (par Dt x).W := Cnf.W_pos _

omit hB in
theorem BB.C_pos (_hB : BB Dt x B) : 0 < (par Dt x).C := pow_pos (by omega) _

theorem BB.big_parts : (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C +
    (par Dt x).W * (par Dt x).C * (par Dt x).Q + (par Dt x).P +
    2 * ((par Dt x).W * (par Dt x).C + (par Dt x).W + 1) + kW x + nU Dt x ^ Dt.s +
    Dt.D * Dt.D + Dt.r + (nU Dt x ^ Dt.s + 2) ^ Dt.D + (kW x + 2) ^ Dt.D + 4 < B := hB.big

theorem BB.WC_le : (par Dt x).W ≤ (par Dt x).W * (par Dt x).C :=
  Nat.le_mul_of_pos_right _ hB.C_pos

theorem BB.C_le : (par Dt x).C ≤ (par Dt x).W * (par Dt x).C :=
  Nat.le_mul_of_pos_left _ hB.W_pos

theorem BB.WCWC_le : (par Dt x).W * (par Dt x).C ≤
    (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C := by
  have h1 : 1 ≤ (par Dt x).W * (par Dt x).C := Nat.mul_pos hB.W_pos hB.C_pos
  calc (par Dt x).W * (par Dt x).C = (par Dt x).W * (par Dt x).C * 1 := by ring
    _ ≤ (par Dt x).W * (par Dt x).C * ((par Dt x).W * (par Dt x).C) := Nat.mul_le_mul_left _ h1
    _ = _ := by ring

/-- The code of a literal `Z(b, e)` and its parts. -/
theorem BB.lit_lt {b e : ℕ} (hb : b < (par Dt x).W) (he : e < (par Dt x).C) :
    2 * (1 + b + (par Dt x).W * e) < B ∧ 1 + b + (par Dt x).W * e < B ∧
      (par Dt x).W * e < B ∧ 1 + b < B := by
  have h1 : (par Dt x).W * e + (par Dt x).W ≤ (par Dt x).W * (par Dt x).C := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ he
  have := hB.big_parts
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem BB.count_lt : (par Dt x).W + (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C +
    (par Dt x).P < B ∧ (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C < B ∧
    (par Dt x).W * (par Dt x).C * (par Dt x).W < B ∧ (par Dt x).W * (par Dt x).C < B := by
  have := hB.big_parts; have := hB.WC_le; have := hB.WCWC_le
  have h3 : (par Dt x).W * (par Dt x).C * (par Dt x).W ≤
      (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C :=
    Nat.le_mul_of_pos_right _ hB.C_pos
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem BB.WCQ_lt : (par Dt x).W * (par Dt x).C * (par Dt x).Q < B := by
  have := hB.big_parts; omega

theorem BB.small : (par Dt x).W + 1 < B ∧ (par Dt x).C + 1 < B ∧ 2 * (par Dt x).C < B ∧
    (par Dt x).P + 1 < B ∧
    kW x + 2 < B ∧ nU Dt x ^ Dt.s + 2 < B ∧ Dt.D * Dt.D + Dt.D + 1 < B ∧ Dt.r < B ∧
    (nU Dt x ^ Dt.s + 2) ^ Dt.D < B ∧ (kW x + 2) ^ Dt.D < B := by
  have := hB.big_parts; have := hB.WC_le; have := hB.C_le
  have hD : Dt.D ≤ Dt.D * Dt.D ∨ Dt.D = 0 := by
    rcases Nat.eq_zero_or_pos Dt.D with h | h
    · right; exact h
    · left; exact Nat.le_mul_of_pos_left _ h
  have hD2 : Dt.D ≤ (kW x + 2) ^ Dt.D := by
    calc Dt.D ≤ 2 ^ Dt.D := Nat.lt_two_pow_self.le
      _ ≤ (kW x + 2) ^ Dt.D := Nat.pow_le_pow_left (by omega) _
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

theorem BB.Q_lt : (par Dt x).Q + 1 < B := by
  have := hB.big_parts
  have h1 : (par Dt x).Q ≤ (par Dt x).W * (par Dt x).C * (par Dt x).Q := by
    have := Nat.mul_pos hB.W_pos hB.C_pos
    exact Nat.le_mul_of_pos_left _ this
  omega

end Bounds

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx
