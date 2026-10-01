import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgMain
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds

/-! # The cost of the program is fixed-parameter

With `X = n + 1` for the bit size `n` of the input and `P = Pk d k`, the cost is at most
`8000 · P³ · X²`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Cost

open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgStruct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm2 Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgMain

variable {cl : List (List ℕ)} {d k X P : ℕ}

theorem one_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem kparse_le (hm : cl.length ≤ X) (hL : nL cl ≤ X) (hX : 1 ≤ X) :
    Kparse cl ≤ 130 * (X * X) := by
  unfold Kparse KpLoop Kcopy
  have := Nat.mul_le_mul (show 34 * nL cl + 6 + 40 + 4 ≤ 34 * X + 50 by omega) hm
  nlinarith

theorem kconst_le (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P) : Kconst d k ≤ 250 * P := by
  unfold Kconst; omega

theorem kfirsts_le (hsz : sz cl d k ≤ 4 * (X * P)) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    (34 * sz cl d k + 24) * sz cl d k + 6 ≤ 800 * (X * X * (P * P)) := by
  have h1 : sz cl d k * sz cl d k ≤ 16 * (X * X * (P * P)) := by
    calc sz cl d k * sz cl d k ≤ (4 * (X * P)) * (4 * (X * P)) := Nat.mul_le_mul hsz hsz
      _ = 16 * (X * X * (P * P)) := by ring
  have h2 : 1 ≤ X * X * (P * P) := one_le_mul (one_le_mul hX hX) (one_le_mul hP hP)
  have h3 : X * P ≤ X * X * (P * P) := by
    calc X * P = X * P * 1 := by ring
      _ ≤ X * P * (X * P) := Nat.mul_le_mul_left _ (one_le_mul hX hP)
      _ = X * X * (P * P) := by ring
  nlinarith

theorem knrows_le (hm : cl.length ≤ X) (hdP : d + 2 ≤ P) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    KnRows cl d ≤ 120 * (X * P) := by
  unfold KnRows Kkey
  have h1 : (44 * (d + 1) + 6 + 64) * cl.length ≤ (44 * P + 70) * X :=
    Nat.mul_le_mul (by omega) hm
  have h2 : 1 ≤ X * P := one_le_mul hX hP
  have e : (44 * P + 70) * X = 44 * (X * P) + 70 * X := by ring
  have h3 : X ≤ X * P := Nat.le_mul_of_pos_right X (by omega)
  omega

theorem khit_le (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P) : Khit d k ≤ 70 * (P * P) := by
  unfold Khit
  have h1 := Nat.mul_le_mul (show 24 * k + 44 ≤ 24 * P by omega) (show d ≤ P by omega)
  have e : 24 * P * P = 24 * (P * P) := by ring
  have h2 : 1 ≤ P * P := one_le_mul (by omega) (by omega)
  omega

theorem ksim_le (hm : cl.length ≤ X) (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P) (hX : 1 ≤ X) :
    Ksim cl d k ≤ 400 * (X * (P * P)) := by
  have hk := khit_le hdP hkP
  have hP : 1 ≤ P := by omega
  have h2 : 1 ≤ P * P := one_le_mul hP hP
  have hg : Kgrp d k ≤ 170 * (P * P) := by unfold Kgrp; omega
  unfold Ksim Kpad
  have h1 : (Kgrp d k + 44) * cl.length ≤ (214 * (P * P)) * X := Nat.mul_le_mul (by omega) hm
  have e : (214 * (P * P)) * X = 214 * (X * (P * P)) := by ring
  have h3 : 1 ≤ X * (P * P) := one_le_mul hX h2
  have h4 : P ≤ X * (P * P) := by
    calc P ≤ P * P := Nat.le_mul_of_pos_left P (by omega)
      _ ≤ X * (P * P) := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem klrows_le (hm : cl.length ≤ X) (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P) (hdk : d ^ k ≤ P)
    (hX : 1 ≤ X) : KlRows cl d k ≤ 1000 * (X * X * (P * P * P)) := by
  have hs := ksim_le hm hdP hkP hX
  have hP : 1 ≤ P := by omega
  have h3 : 1 ≤ X * (P * P) := one_le_mul hX (one_le_mul hP hP)
  have hb : KbLoop cl d k ≤ 410 * (X * (P * P * P)) := by
    unfold KbLoop
    have h1 : (Ksim cl d k + 4) * d ^ k ≤ (404 * (X * (P * P))) * P :=
      Nat.mul_le_mul (by omega) hdk
    have h4 : 1 ≤ X * (P * P * P) := one_le_mul hX (one_le_mul (one_le_mul hP hP) hP)
    have e : (404 * (X * (P * P))) * P = 404 * (X * (P * P * P)) := by ring
    omega
  unfold KlRows
  have h4 : 1 ≤ X * (P * P * P) := one_le_mul hX (one_le_mul (one_le_mul hP hP) hP)
  have h1 : (KbLoop cl d k + 8) * cl.length ≤ (418 * (X * (P * P * P))) * X :=
    Nat.mul_le_mul (by omega) hm
  have e : (418 * (X * (P * P * P))) * X = 418 * (X * X * (P * P * P)) := by ring
  have h5 : 1 ≤ X * X * (P * P * P) := one_le_mul (one_le_mul hX hX) (one_le_mul (one_le_mul hP hP) hP)
  omega

theorem kstruct_le (hsz : sz cl d k ≤ 4 * (X * P)) (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P)
    (hX : 1 ≤ X) : KstructOut cl d k ≤ 2400 * (X * (P * P)) := by
  have hP : 1 ≤ P := by omega
  unfold KstructOut Kemit Kdig
  have h1 : (34 * (d + k + 2) + 20 + 44) * sz cl d k ≤ (68 * P + 64) * (4 * (X * P)) :=
    Nat.mul_le_mul (by omega) hsz
  have e : (68 * P + 64) * (4 * (X * P)) = 272 * (X * (P * P)) + 256 * (X * P) := by ring
  have h2 : X * P ≤ X * (P * P) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left P (by omega))
  have h3 : 1 ≤ X * P := one_le_mul hX hP
  have h4 : 44 * sz cl d k ≤ 176 * (X * P) := by omega
  omega

theorem kform_le (hdP : d + 2 ≤ P) (hkP : k + 2 ≤ P) (hFF : FF d k ≤ P)
    (hnv : nv d k + 1 ≤ 3 * P) : KformOut d k ≤ 1000 * (P * P * P) := by
  have hP : 1 ≤ P := by omega
  have hpp : 1 ≤ P * P := one_le_mul hP hP
  have hppp : 1 ≤ P * P * P := one_le_mul hpp hP
  have hcl : Kcl d k ≤ 250 * (P * P) := by
    unfold Kcl Kyin
    have h1 : (30 + 4) * (k + 1) + 6 + 30 + 4 ≤ 40 * P := by omega
    have h2 : ((30 + 4) * (k + 1) + 6 + 30 + 4) * (k + 1) ≤ (40 * P) * P :=
      Nat.mul_le_mul h1 (by omega)
    have e : (40 * P) * P = 40 * (P * P) := by ring
    have h3 : P ≤ P * P := Nat.le_mul_of_pos_left P (by omega)
    omega
  have he : KeOut d k ≤ 280 * (P * P * P) := by
    unfold KeOut
    have h1 : (2 + (Kcl d k + 4) + 4) * FF d k ≤ (260 * (P * P)) * P :=
      Nat.mul_le_mul (by omega) hFF
    have e : (260 * (P * P)) * P = 260 * (P * P * P) := by ring
    omega
  unfold KformOut
  have h3 : (34 * k + 6 + 8 + 4) * k ≤ (34 * P) * P := Nat.mul_le_mul (by omega) (by omega)
  have e : (34 * P) * P = 34 * (P * P) := by ring
  have h4 : P ≤ P * P := Nat.le_mul_of_pos_left P (by omega)
  have h5 : P * P ≤ P * P * P := Nat.le_mul_of_pos_right _ (by omega)
  omega

set_option maxHeartbeats 1000000 in
theorem cost_le {n : ℕ} (hlen : cl.length + nL cl + 2 ≤ n) :
    16 * (cl.length + nL cl + 2) + 7 + Kbody cl d k ≤ 8000 * Pk d k ^ 3 * (n + 1) ^ 2 := by
  have hP1 : 1 ≤ Pk d k := one_le_Pk d k
  have hdP : d + 2 ≤ Pk d k := d_le_Pk d k
  have hkP : k + 2 ≤ Pk d k := k_le_Pk d k
  have hdk : d ^ k ≤ Pk d k := pow_le_Pk_left le_rfl
  have hFF : FF d k ≤ Pk d k := pow_le_Pk_right (i := d + 1) (by omega)
  have hnv : nv d k + 1 ≤ 3 * Pk d k := nv_le_Pk d k
  have hm : cl.length ≤ n + 1 := by omega
  have hL : nL cl ≤ n + 1 := by omega
  have hX1 : 1 ≤ n + 1 := by omega
  have hsz : sz cl d k ≤ 4 * ((n + 1) * Pk d k) := by
    have := Nat.mul_le_mul hm hdk
    unfold sz; nlinarith
  have c1 := kparse_le hm hL hX1
  have hmL : cl.length + nL cl + 2 ≤ n + 1 := by omega
  have c2 := kconst_le hdP hkP
  have c3 := kfirsts_le hsz hX1 hP1
  have c4 := knrows_le hm hdP hX1 hP1
  have c5 := klrows_le hm hdP hkP hdk hX1
  have c6 := kstruct_le hsz hdP hkP hX1
  have c7 := kform_le hdP hkP hFF hnv
  generalize Pk d k = P at *
  generalize n + 1 = X at *
  have hPP : P ≤ P * P := Nat.le_mul_of_pos_left P (by omega)
  have hPPP : P * P ≤ P * P * P := Nat.le_mul_of_pos_right (P * P) (by omega)
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have e1 : 8000 * P ^ 3 * X ^ 2 = 8000 * (X * X * (P * P * P)) := by ring
  rw [e1]
  have g1 : X * X ≤ X * X * (P * P * P) := Nat.le_mul_of_pos_right _ (by positivity)
  have g2 : X * X * (P * P) ≤ X * X * (P * P * P) := Nat.mul_le_mul_left _ hPPP
  have g3 : X * (P * P) ≤ X * X * (P * P * P) :=
    (Nat.mul_le_mul_right _ hXX).trans (Nat.mul_le_mul_left _ hPPP)
  have g4 : X * P ≤ X * X * (P * P * P) :=
    (Nat.mul_le_mul_right _ hXX).trans (Nat.mul_le_mul_left _ (hPP.trans hPPP))
  have g5 : P * P * P ≤ X * X * (P * P * P) := Nat.le_mul_of_pos_left _ (by positivity)
  have g6 : P ≤ P * P * P := hPP.trans hPPP
  have g7 : X ≤ X * X * (P * P * P) := hXX.trans g1
  unfold Kbody
  omega

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Cost
