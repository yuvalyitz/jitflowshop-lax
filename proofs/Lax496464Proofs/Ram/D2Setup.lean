import Lax496464Proofs.Ram.D2Scan1
import Lax496464Proofs.Ram.ListUtil
import Lax496464Proofs.Ram.D2Count

/-!
# Theorem 2's Machine, Part 5: the Powers of `n+1`, and the Code of the First `m` Indices

`PW[i] = (n+1)^i` for `i ≤ m` (`pwSetup`), and `zk`, the number of the set `{0,…,min m n - 1}` — the
thresholds the table is read off at (`code0Loop`).  Both cost `O(m)`.
-/

namespace Lax496464Proofs.Ram.D2Setup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Scan

/-- One power. -/
def pwBody : Com :=
  .seq (.store "PW" (.bin .add (V "pi") (.lit 1)) (.bin .mul (.get "PW" (V "pi")) (V "nb")))
    (bump "pi")

/-- `PW[0] := 1`, then the rest. -/
def pwSetup : Com :=
  .seq (.store "PW" (.lit 0) (.lit 1))
    (.seq (.assign "pi" (.lit 0)) (.while (.lt (V "pi") (V "m")) pwBody))

def PInv (n m : ℕ) (σ : Env) : Prop :=
  σ.vars "nb" = n + 1 ∧ σ.vars "m" = m ∧ (σ.arrs "PW").length = m + 1 ∧ σ.vars "pi" ≤ m ∧
    ∀ i, i ≤ σ.vars "pi" → (σ.arrs "PW").getD i 0 = (n + 1) ^ i

theorem pwBody_spec {B : ℕ} (hB : 2 < B) (n m : ℕ) (hpB : ∀ i ≤ m, (n + 1) ^ i < B)
    (hmB : m < B) :
    Spec B (fun σ => PInv n m σ ∧ σ.vars "pi" < m) pwBody
      (fun σ σ' => PInv n m σ' ∧ σ'.vars "pi" = σ.vars "pi" + 1) 30 := by
  refine Spec.of_exists fun σ ⟨⟨hnb, hm, hlen, hle, hall⟩, hlt⟩ => ?_
  have hp : (σ.arrs "PW").getD (σ.vars "pi") 0 = (n + 1) ^ σ.vars "pi" := hall _ le_rfl
  have hl1 : σ.vars "pi" < (σ.arrs "PW").length := by omega
  have hl2 : σ.vars "pi" + 1 < (σ.arrs "PW").length := by omega
  have hb1 := hpB (σ.vars "pi") (by omega)
  have hb2 := hpB (σ.vars "pi" + 1) (by omega)
  have hpw : (n + 1) ^ (σ.vars "pi" + 1) = (n + 1) ^ σ.vars "pi" * (n + 1) := pow_succ _ _
  have hnbB : n + 1 < B := by have := hpB 1 (by omega); simpa using this
  run_vcg
  all_goals (simp_all)
  all_goals
    unfold PInv
    refine ⟨by simpa using hnb, by simpa using hm, by simpa using hlen, by simp; omega, ?_⟩
    intro i hi
    simp only [arrs_setVar, arrs_setArr, vars_setVar, if_true] at hi ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hi) with hi' | hi'
    · rw [getD_set_ne _ _ _ _ (by omega)]; exact hall i (by omega)
    · subst hi'; rw [getD_set_self _ _ _ (by omega), hpw]

/-- The whole set-up. -/
theorem pwSetup_spec {B : ℕ} (hB : 2 < B) (n m : ℕ) (hpB : ∀ i ≤ m, (n + 1) ^ i < B)
    (hmB : m < B) :
    Spec B (fun σ => σ.vars "nb" = n + 1 ∧ σ.vars "m" = m ∧ (σ.arrs "PW").length = m + 1)
      pwSetup (fun _ σ' => PInv n m σ' ∧ σ'.vars "pi" = m) (2 + ((30 + 4) * m + 6) + 1 + 4) := by
  have hloop := Spec.forRangeZero (B := B) (c := pwBody) "pi" "m" (PInv n m) m 30 hmB
    (fun σ h => h.2.2.2.1) (fun σ h => h.2.1) (pwBody_spec hB n m hpB hmB)
  refine Spec.of_exists fun σ ⟨hnb, hm, hlen⟩ => ?_
  have hl0 : 0 < (σ.arrs "PW").length := by omega
  have r0 := Run.store (B := B) (σ := σ) (a := "PW") (i := .lit 0) (e := .lit 1) (idx := 0) (v := 1)
    (evalB_lit (by omega)) (evalB_lit (by omega)) hl0
  obtain ⟨σ1, hr1, hI1, hpi1⟩ := hloop.run (σ := σ.setArr "PW" 0 1)
    (by
      refine ⟨by simpa using hnb, by simpa using hm, by simpa using hlen, by simp, ?_⟩
      intro i hi
      simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr] at hi ⊢
      have : i = 0 := by omega
      subst this
      rw [getD_set_self _ _ _ hl0]; simp)
  exact ⟨σ1, _, r0.seq hr1 |>.mono (by simp only [Expr.size]; omega), le_rfl, hI1, hpi1⟩


/-! ## The number of the first `m` indices -/

/-- The `i`-th digit of the set `{0, …, min m n - 1}`. -/
def dgt (n i : ℕ) : ℕ := if i < n then i else n

/-- `zk := zk * nb + dgt i`. -/
def codeBody : Com :=
  .seq (.ite (.lt (V "zi2") (V "n"))
      (.assign "zk" (.bin .add (.bin .mul (V "zk") (V "nb")) (V "zi2")))
      (.assign "zk" (.bin .add (.bin .mul (V "zk") (V "nb")) (V "n"))))
    (bump "zi2")

def CInv (n m : ℕ) (σ : Env) : Prop :=
  σ.vars "nb" = n + 1 ∧ σ.vars "m" = m ∧ σ.vars "n" = n ∧ σ.vars "zi2" ≤ m ∧
    σ.vars "zk" = enc (n + 1) ((List.range (σ.vars "zi2")).map (dgt n))

theorem dgt_lt (n i : ℕ) : dgt n i < n + 1 := by unfold dgt; split_ifs <;> omega

theorem enc_dgt_lt (n k : ℕ) : enc (n + 1) ((List.range k).map (dgt n)) < (n + 1) ^ k := by
  have := enc_lt (b := n + 1) (L := (List.range k).map (dgt n))
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact dgt_lt n i)
  simpa using this

theorem codeBody_spec {B : ℕ} (hB : 2 < B) (n m : ℕ) (hpB : ∀ i ≤ m, (n + 1) ^ i < B)
    (hmB : m < B) :
    Spec B (fun σ => CInv n m σ ∧ σ.vars "zi2" < m) codeBody
      (fun σ σ' => CInv n m σ' ∧ σ'.vars "zi2" = σ.vars "zi2" + 1) 30 := by
  refine Spec.of_exists fun σ ⟨⟨hnb, hm, hn, hle, hk⟩, hlt⟩ => ?_
  have hlt1 := enc_dgt_lt n (σ.vars "zi2")
  have hlt2 := enc_dgt_lt n (σ.vars "zi2" + 1)
  have hb1 := hpB (σ.vars "zi2") (by omega)
  have hb2 := hpB (σ.vars "zi2" + 1) (by omega)
  have hnbB : n + 1 < B := by have := hpB 1 (by omega); simpa using this
  have hstep : enc (n + 1) ((List.range (σ.vars "zi2" + 1)).map (dgt n)) =
      enc (n + 1) ((List.range (σ.vars "zi2")).map (dgt n)) * (n + 1) + dgt n (σ.vars "zi2") := by
    rw [List.range_succ, List.map_append, List.map_singleton, enc_snoc]
  by_cases hzn : σ.vars "zi2" < n
  · have hd : dgt n (σ.vars "zi2") = σ.vars "zi2" := by simp [dgt, hzn]
    rw [hstep] at hlt2
    rw [hd] at hstep hlt2
    run_vcg
    all_goals first
      | (rw [hk, hnb]; omega)
      | (unfold CInv; simp [hk, hnb, hn, hm, hstep]; omega)
  · have hd : dgt n (σ.vars "zi2") = n := by simp [dgt, hzn]
    rw [hstep] at hlt2
    rw [hd] at hstep hlt2
    run_vcg
    all_goals first
      | (rw [hk, hnb]; omega)
      | (unfold CInv; simp [hk, hnb, hn, hm, hstep]; omega)


/-- `zk := 0`, then the digits. -/
def code0Loop : Com :=
  .seq (.assign "zk" (.lit 0))
    (.seq (.assign "zi2" (.lit 0)) (.while (.lt (V "zi2") (V "m")) codeBody))

theorem map_dgt_range (n m : ℕ) :
    (List.range m).map (dgt n) = lstOf n m (List.range (min m n)) := by
  have hlen : (lstOf n m (List.range (min m n))).length = m := by simp [lstOf]
  apply List.ext_getElem
  · rw [hlen]; simp
  · intro i h1 h2
    have hi : i < m := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, lstOf]
    rw [List.getElem_append]
    split_ifs with hi'
    · simp at hi'
      simp [dgt]; omega
    · simp at hi'
      simp [dgt]; omega

theorem code0Loop_spec {B : ℕ} (hB : 2 < B) (n m : ℕ) (hpB : ∀ i ≤ m, (n + 1) ^ i < B)
    (hmB : m < B) :
    Spec B (fun σ => σ.vars "nb" = n + 1 ∧ σ.vars "m" = m ∧ σ.vars "n" = n) code0Loop
      (fun _ σ' => σ'.vars "zk" = codeL n m (List.range (min m n))) (2 + ((30 + 4) * m + 6) + 1 + 4) := by
  have hloop := Spec.forRangeZero (B := B) (c := codeBody) "zi2" "m" (CInv n m) m 30 hmB
    (fun σ h => h.2.2.2.1) (fun σ h => h.2.1) (codeBody_spec hB n m hpB hmB)
  refine Spec.of_exists fun σ ⟨hnb, hm, hn⟩ => ?_
  have r0 := Run.assign (B := B) (σ := σ) (x := "zk") (e := .lit 0) (v := 0) (evalB_lit (by omega))
  obtain ⟨σ1, hr1, hI1, hi1⟩ := hloop.run (σ := σ.setVar "zk" 0)
    (by
      refine ⟨by simpa using hnb, by simpa using hm, by simpa using hn, by simp, ?_⟩
      simp)
  refine ⟨σ1, _, (r0.seq hr1).mono (by simp only [Expr.size]; omega), le_rfl, ?_⟩
  have := hI1.2.2.2.2
  rw [hi1, map_dgt_range] at this
  rw [this]; rfl

end Lax496464Proofs.Ram.D2Setup
