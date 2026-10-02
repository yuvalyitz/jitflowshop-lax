import Lax496464Proofs.Ram.D2Scan1
import Lax496464Proofs.Ram.ListUtil

/-!
# Theorem 2's Machine, Part 3: Is the Number a Code?

`vphase` decides, for a number `zc ≠ top` (so `m ≥ 1`), whether it is the code of a set, from the
`VALID` entry of the number `zsuf` obtained by dropping its first digit (`D2Valid.isCode_iff`;
`zsuf > zc`, so that entry has been filled already), and stores the answer at `VALID[zc]`.
-/

namespace Lax496464Proofs.Ram.D2Valid1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Scan1 (mod_eq_sub digE)

/-- The first digit, the second digit, the number without the first digit, and the verdict. -/
def vphase : Com :=
  .seq (.assign "zx1" (.bin .div (V "zc") (.get "PW" (.bin .sub (V "m") (.lit 1)))))
    (.seq (.ite (.lt (V "m") (.lit 2)) (.assign "zx2" (V "n"))
        (.seq (.assign "zt"
            (.bin .div (V "zc") (.get "PW" (.bin .sub (V "m") (.lit 2)))))
          (.assign "zx2" digE)))
      (.seq (.assign "zt" (.bin .div (V "zc") (.get "PW" (.bin .sub (V "m") (.lit 1)))))
        (.seq (.assign "zsuf"
            (.bin .add (.bin .mul (.bin .sub (V "zc")
              (.bin .mul (V "zt") (.get "PW" (.bin .sub (V "m") (.lit 1))))) (V "nb")) (V "n")))
          (.seq (.assign "zv" (.lit 0))
            (.seq (.ite (.lt (V "zx1") (V "zx2"))
                (.ite (.eq (.get "VALID" (V "zsuf")) (.lit 1)) (.assign "zv" (.lit 1)) .skip)
                .skip)
              (.store "VALID" (V "zc") (V "zv")))))))

/-- The second digit, as the machine computes it. -/
def x2v (n m c : ℕ) : ℕ :=
  if m < 2 then n else c / (n + 1) ^ (m - 2) - c / (n + 1) ^ (m - 2) / (n + 1) * (n + 1)

/-- The number without the first digit, as the machine computes it. -/
def sufv (n m c : ℕ) : ℕ :=
  (c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) + n

theorem x2v_eq (n m c : ℕ) (hm : 1 ≤ m) : x2v n m c = x2 n m c := by
  unfold x2v x2
  by_cases h : m < 2
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), ← mod_eq_sub]

theorem sufv_eq (n m c : ℕ) : sufv n m c = sufc n m c := by
  unfold sufv sufc
  rw [← mod_eq_sub]

theorem no_lt {j o q : ℕ} (h : o ≤ j + q) : ¬ (j < o - q) := by omega

set_option maxHeartbeats 4000000 in
theorem vphase_raw {B : ℕ} (hB : 2 < B) (n m c : ℕ) (PWl Vl : List ℕ) (hm : 1 ≤ m)
    (hPWl : PWl.length = m + 1) (hPW : ∀ i ≤ m, PWl.getD i 0 = (n + 1) ^ i)
    (hcB : c < B) (hpB : ∀ i ≤ m, (n + 1) ^ i < B) (hsufB : sufv n m c < B) (hnB : n + 1 < B) (hmB : m < B)
    (hVl : sufv n m c < Vl.length) (hcl : c < Vl.length) (hVB : ∀ i, Vl.getD i 0 < B) :
    Spec B (fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = n + 1 ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧
        σ.arrs "PW" = PWl ∧ σ.arrs "VALID" = Vl) vphase
      (fun _σ σ' => σ'.arrs "VALID" = Vl.set c
          (if c / (n + 1) ^ (m - 1) < x2v n m c ∧ Vl.getD (sufv n m c) 0 = 1 then 1 else 0) ∧
        σ'.vars "zx1" = c / (n + 1) ^ (m - 1)) 100 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hzc, hnb, hn, hm', hPWσ, hVσ⟩ := hσ
  have hP1 : (σ.arrs "PW").getD (m - 1) 0 = (n + 1) ^ (m - 1) := by
    rw [hPWσ]; exact hPW _ (by omega)
  have hl1 : m - 1 < (σ.arrs "PW").length := by rw [hPWσ, hPWl]; omega
  have hPB1 : (n + 1) ^ (m - 1) < B := hpB _ (by omega)
  have hzt : c / (n + 1) ^ (m - 1) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hcB
  have hzt2 : c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1) < B :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) hcB
  have hsub : c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1) < B :=
    lt_of_le_of_lt (Nat.sub_le _ _) hcB
  have hmul : (c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) < B := by
    have : (c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) ≤ sufv n m c := by
      unfold sufv; omega
    omega
  have hsufB' : (c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) + n < B := hsufB
  have hVvB := hVB (sufv n m c)
  have hVl' : (c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) + n < (σ.arrs "VALID").length := by
    rw [hVσ]; exact hVl
  have hVc : c < (σ.arrs "VALID").length := by rw [hVσ]; exact hcl
  have hVget : (σ.arrs "VALID").getD ((c - c / (n + 1) ^ (m - 1) * (n + 1) ^ (m - 1)) * (n + 1) + n) 0
      = Vl.getD (sufv n m c) 0 := by rw [hVσ]; rfl
  unfold x2v
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · simp only [hm2, if_true]
    run_vcg
    all_goals (simp_all)
    all_goals (try omega)
    all_goals (try (rw [if_neg (fun h => by have := h.1; omega)]))
  · simp only [not_lt.mpr hm2, if_false]
    have hP3 : (σ.arrs "PW").getD (m - 2) 0 = (n + 1) ^ (m - 2) := by
      rw [hPWσ]; exact hPW _ (by omega)
    have hl3 : m - 2 < (σ.arrs "PW").length := by rw [hPWσ, hPWl]; omega
    have hz3 : c / (n + 1) ^ (m - 2) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hcB
    have hz4 : c / (n + 1) ^ (m - 2) / (n + 1) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hz3
    have hz5 : c / (n + 1) ^ (m - 2) / (n + 1) * (n + 1) < B :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) hz3
    have hz6 : c / (n + 1) ^ (m - 2) - c / (n + 1) ^ (m - 2) / (n + 1) * (n + 1) < B :=
      lt_of_le_of_lt (Nat.sub_le _ _) hz3
    run_vcg
    all_goals (simp_all)
    all_goals (try omega)
    all_goals (try (congr 1; split_ifs with h <;> first | rfl | exact absurd h.1 (no_lt (by assumption))))

/-- `vphase`, with the digits as `D2Valid` names them. -/
theorem vphase_spec {B : ℕ} (hB : 2 < B) (n m c : ℕ) (PWl Vl : List ℕ) (hm : 1 ≤ m)
    (hPWl : PWl.length = m + 1) (hPW : ∀ i ≤ m, PWl.getD i 0 = (n + 1) ^ i)
    (hcB : c < B) (hpB : ∀ i ≤ m, (n + 1) ^ i < B) (hsufB : sufc n m c < B) (hnB : n + 1 < B)
    (hmB : m < B) (hVl : sufc n m c < Vl.length) (hcl : c < Vl.length)
    (hVB : ∀ i, Vl.getD i 0 < B) :
    Spec B (fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = n + 1 ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧
        σ.arrs "PW" = PWl ∧ σ.arrs "VALID" = Vl) vphase
      (fun _σ σ' => σ'.arrs "VALID" = Vl.set c
          (if x1 n m c < x2 n m c ∧ Vl.getD (sufc n m c) 0 = 1 then 1 else 0) ∧
        σ'.vars "zx1" = x1 n m c) 100 := by
  have h := vphase_raw hB n m c PWl Vl hm hPWl hPW hcB hpB (by rw [sufv_eq]; exact hsufB) hnB hmB
    (by rw [sufv_eq]; exact hVl) hcl hVB
  refine h.post ?_
  intro σ σ' _ ⟨h1, h2⟩
  rw [x2v_eq n m c hm, sufv_eq] at h1
  exact ⟨h1, h2⟩

end Lax496464Proofs.Ram.D2Valid1
