import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PMain
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # Bounds for the time statement

A bounded run writes only values below its bound (`Run.outBounded`); the value bound and the cost
are polynomial in the bit size of the word. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PBound

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax759944.BinaryWordEncoding
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PForm Lax496464Proofs.WHierarchy.Lemmas.NegElim.PMain
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math

theorem BigStepB.outBounded {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) (hσ : ∀ v ∈ σ.out, v < B) : ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact hσ
  | assign _ => exact hσ
  | store _ _ _ => exact hσ
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read _ => exact hσ
  | write h =>
      intro v hv
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hσ v hv
      · exact (Expr.eval_and_lt_of_evalB h).2

theorem Run.outBounded {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hσ : ∀ v ∈ σ.out, v < B) : ∀ v ∈ σ'.out, v < B := by
  obtain ⟨_, _, hbs⟩ := h; exact BigStepB.outBounded hbs hσ

/-! ### The value bound -/

theorem maxEntry_lt (x : List ℕ) : maxEntry x < 2 ^ bitSize x := by
  have h : maxEntry x ≤ 2 ^ bitSize x - 1 := maxEntry_le fun v hv => by
    have := Lax496464Proofs.WHierarchy.Machine.SizeFacts.lt_two_pow_bitSize hv; omega
  have := Nat.one_le_two_pow (n := bitSize x)
  omega

theorem Bv_lt (x : List ℕ) : 6 * Bv x + 100 ≤ 2 ^ (2 * bitSize x + 20) := by
  have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have hM := maxEntry_lt x
  set b := bitSize x
  have h1 : x.length + 2 < 2 ^ (b + 2) := by
    have := Nat.lt_two_pow_self (n := b + 2); omega
  have h2 : (x.length + 2) * (x.length + 2) ≤ 2 ^ (b + 2) * 2 ^ (b + 2) :=
    Nat.mul_le_mul h1.le h1.le
  rw [← pow_add] at h2
  have h3 : 2 ^ b ≤ 2 ^ (2 * b + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (b + 2 + (b + 2)) = 2 ^ (2 * b + 4) := by ring_nf
  have h5 : 2 ^ (2 * b + 20) = 2 ^ (2 * b + 4) * 2 ^ 16 := by rw [← pow_add]
  have h6 : 1 ≤ 2 ^ (2 * b + 4) := Nat.one_le_two_pow
  unfold Bv
  have : 64 * (x.length + 2) * (x.length + 2) = 64 * ((x.length + 2) * (x.length + 2)) := by ring
  rw [this]
  omega

/-! ### The cost -/

theorem Kbody_le {x : List ℕ} {φ : Formula} (hd : Dom x φ) : Kbody x ≤ 6000 * (x.length + 1) ^ 3 := by
  have hs : sOf x ≤ x.length := by have := hd.hdr; omega
  have hT : nT x ≤ x.length := by have := nT_le hd; omega
  have hM := MOf_le hd
  have hc : (Cond.lt (L 0) (V "h")).size = 3 := rfl
  unfold Kbody Kw Kd Kneg
  rw [hc]
  set n := x.length
  have e3 : (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) := by ring
  rw [e3]
  have p1 : (44 * n + 60 + 4) * sOf x ≤ (44 * n + 64) * n := Nat.mul_le_mul (by omega) hs
  have p2 : (34 * n + 30 + 4) * nT x ≤ (34 * n + 34) * n := Nat.mul_le_mul (by omega) hT
  have p3 : (44 * n + 30 + 4) * nT x ≤ (44 * n + 34) * n := Nat.mul_le_mul (by omega) hT
  have p4 : ((24 + 4) * MOf x + 10 + 4) * MOf x ≤ (56 * n + 14) * (2 * n) :=
    Nat.mul_le_mul (by omega) hM
  have p5 : (700 * (n + 1) * (n + 1) + 100 + 100 + 4) * sOf x ≤
      (700 * (n + 1) * (n + 1) + 204) * n := Nat.mul_le_mul (by omega) hs
  have p6 : (24 + 4) * (2 * (n - bo x (sOf x))) ≤ 56 * n := by omega
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PBound
