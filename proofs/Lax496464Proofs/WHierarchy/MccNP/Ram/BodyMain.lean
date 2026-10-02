import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead

/-!
# The Specification of `body`

The passes of `body` composed: on a valid word it appends the word of the multicoloured graph to
the output within `Kbody x` steps.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow Lax496464Proofs.WHierarchy.MccNP.Ram.BodyPass
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead
open Lax496464

/-- The exact cost the walk proves. -/
def Ksum (x : List ℕ) : ℕ :=
  (11 * (order x + kOf x) + 40) + K1 (nOf x) + 10 + K1 (nOf x) + K3 (nOf x) + K4 (nOf x) + 10

theorem Mx_eq' {x : List ℕ} (hx : Valid x) : Mx x = psum x (nOf x) := (Mx_eq hx).symm

theorem bok_of {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : Bbody x < B) : BOK x B := by
  unfold Bbody at hB; rw [Mx_eq' hx] at hB
  show x.length + kOf x * order x + psum x (nOf x) + 2 < B
  omega

set_option maxHeartbeats 2000000 in
theorem body_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : Bbody x < B) :
    Spec B (fun σ => σ.arrs "a" = x) body
      (fun σ σ' => σ'.out = σ.out ++ WH_F2_MccConstruction.word (Shape.decode x) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ ∀ y, y ∉ bodyVars → σ'.vars y = σ.vars y)
      ((11 * (order x + kOf x) + 40) + K1 (nOf x) + 10 + K1 (nOf x) + K3 (nOf x) + K4 (nOf x) + 10) := by
  have hbok := bok_of hx hB
  have hb : x.length + nOf x + psum x (nOf x) + 2 < B := hbok
  have hb2 : x.length + nOf x + 2 < B := hbok.row
  have hw := word_eq hx
  have hlen := hx.2.1
  unfold body
  run_vcg [header_spec hx hb2, pass1_spec hx hbok, pass2_spec hx hbok, pass3_spec hx hbok,
    pass4_spec hx hbok]
  all_goals (try simp only [Ctx, Keep, headVars, pass1Vars, pass2Vars, pass3Vars, pass4Vars, rowVars, adjVars, bodyVars] at *); all_goals (simp_all; try omega)

theorem Ksum_eq (x : List ℕ) : Ksum x =
    912 * (nOf x * nOf x) + 102 * nOf x + 11 * (order x + kOf x) + 88 := by
  unfold Ksum K1 K3 K4 Krow
  ring

theorem total_le (k n : ℕ) :
    912 * (k * n * (k * n)) + 102 * (k * n) + 11 * (n + k) + 88 ≤
      1200 * ((k + 1) ^ 2 * ((n + 1 + n * n + k + 1) + 1)) := by
  set P := (k + 1) ^ 2 * ((n + 1 + n * n + k + 1) + 1) with hP
  have hkk : k * k ≤ (k + 1) ^ 2 := by nlinarith
  have hnn : n * n ≤ n + 1 + n * n + k + 1 + 1 := by omega
  have hNN : k * n * (k * n) ≤ P := by
    have := Nat.mul_le_mul hkk hnn
    calc k * n * (k * n) = (k * k) * (n * n) := by ring
      _ ≤ _ := this
  have hN : k * n ≤ P := Nat.mul_le_mul (by nlinarith) (by omega)
  have hn : n ≤ P := by
    have := Nat.mul_le_mul (show 1 ≤ (k + 1) ^ 2 from Nat.one_le_pow _ _ (by omega)) (show n ≤ n + 1 + n * n + k + 1 + 1 by omega)
    simpa using this
  have hk : k ≤ P := by
    have := Nat.mul_le_mul (show k ≤ (k + 1) ^ 2 by nlinarith) (show 1 ≤ n + 1 + n * n + k + 1 + 1 by omega)
    simpa using this
  have h1 : 1 ≤ P := by
    have := Nat.mul_le_mul (show 1 ≤ (k + 1) ^ 2 from Nat.one_le_pow _ _ (by omega)) (show 1 ≤ n + 1 + n * n + k + 1 + 1 by omega)
    simpa using this
  omega

theorem Ksum_le {x : List ℕ} (hx : Valid x) : Ksum x ≤ Kbody x := by
  have h := total_le (kOf x) (order x)
  have hlen := hx.2.1
  have e1 : Ksum x = 912 * (kOf x * order x * (kOf x * order x)) + 102 * (kOf x * order x) +
      11 * (order x + kOf x) + 88 := by
    rw [Ksum_eq]; rfl
  have e2 : Kbody x = 1200 * ((kOf x + 1) ^ 2 * ((order x + 1 + order x * order x + kOf x + 1) + 1)) := by
    unfold Kbody bodyC; rw [hlen]; ring
  rw [e1, e2]; exact h

theorem body_spec_proof {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : Bbody x < B) :
    Spec B (fun σ => σ.arrs "a" = x) body
      (fun σ σ' => σ'.out = σ.out ++ WH_F2_MccConstruction.word (Shape.decode x) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ ∀ y, y ∉ bodyVars → σ'.vars y = σ.vars y)
      (Kbody x) :=
  Spec.mono (body_value hx hB) (Ksum_le hx)

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMain
