import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1

/-! # Σ₁[2] model checking to Clique: the atom test

The pieces of the atom test: ordering the two values by row (`ordA_spec`), the truth value the
valuation gives the atom (`abt_spec`), the arity of the atom's symbol (`asa_spec`), the final
comparison (`fin_spec`), and the branch that computes the truth of the atom (`iteB_spec`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem ordA_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "r1" < B ∧ σ.vars "r2" < B ∧ σ.vars "av1" < B ∧ σ.vars "av2" < B)
      (.ite (.lt (V "r1") (V "r2")) (.seq (.assign "aw1" (V "av1")) (.assign "aw2" (V "av2")))
        (.seq (.assign "aw1" (V "av2")) (.assign "aw2" (V "av1"))))
      (fun σ σ' => σ' = (σ.setVar "aw1" (if σ.vars "r1" < σ.vars "r2" then σ.vars "av1"
        else σ.vars "av2")).setVar "aw2" (if σ.vars "r1" < σ.vars "r2" then σ.vars "av2"
        else σ.vars "av1")) 20 := by
  run_vcg
  all_goals first
    | (simp_all; done)
    | (rw [if_neg (by simp_all), if_neg (by simp_all)]; simp)

theorem abt_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "c1" < B ∧ σ.vars "am1" < B ∧ 2 < B)
      (.seq (.assign "ah" (.shiftr (V "c1") (V "am1")))
        (.assign "abt" (.sub (V "ah") (.mul (.div (V "ah") (.lit 2)) (.lit 2)))))
      (fun σ σ' => σ' = (σ.setVar "ah" (σ.vars "c1" / 2 ^ σ.vars "am1")).setVar "abt"
        (bitv (σ.vars "c1") (σ.vars "am1"))) 20 := by
  intro σ ⟨h1, h2, h3⟩
  have hd : σ.vars "c1" / 2 ^ σ.vars "am1" < B := lt_of_le_of_lt (Nat.div_le_self _ _) h1
  run_vcg
  all_goals (try simp)
  all_goals first
    | omega
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) hd
    | exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) hd
    | exact lt_of_le_of_lt (Nat.sub_le _ _) hd
    | exact ProgEval1.bitv_eq _ _ |>.symm
    | (rw [ProgEval1.bitv_eq])

theorem asa_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "am1" < B ∧ σ.vars "am1" < (σ.arrs "ar").length ∧
        (σ.arrs "ar").getD (σ.vars "am1") 0 < B)
      (.assign "asa" (.get "ar" (V "am1")))
      (fun σ σ' => σ' = σ.setVar "asa" ((σ.arrs "ar").getD (σ.vars "am1") 0)) 5 := by
  run_vcg
  all_goals simp

theorem fin_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "atr" < B ∧ σ.vars "abt" < B ∧ 1 < B)
      (.ite (.eq (V "atr") (V "abt")) (.assign "gf" (.lit 1)) .skip)
      (fun σ σ' => σ' = if σ.vars "atr" = σ.vars "abt" then σ.setVar "gf" 1 else σ) 10 := by
  run_vcg
  all_goals simp_all

/-- The branch that computes the truth of the atom. -/
def iteB : Com :=
  .ite (.eq (V "asa") (.lit 0))
    (.ite (.eq (V "aw1") (V "aw2")) (.assign "atr" (.lit 1)) (.assign "atr" (.lit 0))) scanC

set_option maxHeartbeats 2000000 in
theorem iteB_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.vars "am1" < (σ.arrs "ab").length ∧ σ.vars "am1" < B ∧
        (σ.arrs "ab").getD (σ.vars "am1") 0 ≤ x.length ∧ σ.vars "asa" ≤ Mmax x ∧
        σ.vars "aw1" < B ∧ σ.vars "aw2" < B) iteB
      (fun σ σ' => σ'.vars "atr" = (if σ.vars "asa" = 0 then
          (if σ.vars "aw1" = σ.vars "aw2" then 1 else 0)
        else if memX x ((σ.arrs "ab").getD (σ.vars "am1") 0) (σ.vars "asa") (σ.vars "aw1")
          (σ.vars "aw2") then 1 else 0)) ((60 + 4) * x.length + 80) := by
  have hW := hB.2
  intro σ ⟨ha, hn, hml, hmB, hsb, hsa, hw1, hw2⟩
  have hsaB : σ.vars "asa" < B := by nlinarith
  have hB2 : 2 < B := by nlinarith
  by_cases h0 : σ.vars "asa" = 0
  · have hc0 : (Cond.eq (V "asa") (.lit 0)).evalB B σ = some true := by
      rw [evalB_condEq (evalB_var hsaB) (evalB_lit (by omega))]; simp [h0]
    by_cases hw : σ.vars "aw1" = σ.vars "aw2"
    · have hc1 : (Cond.eq (V "aw1") (V "aw2")).evalB B σ = some true := by
        rw [evalB_condEq (evalB_var hw1) (evalB_var hw2)]; simp [hw]
      have r := Run.ite_true (c := .assign "atr" (.lit 1)) (d := .assign "atr" (.lit 0)) hc1
        (Run.assign (x := "atr") (σ := σ) (evalB_lit (n := 1) (B := B) (by omega)))
      refine ⟨_, (Run.ite_true (d := scanC) hc0 r).mono (by simp), ?_⟩
      simp [h0, hw]
    · have hc1 : (Cond.eq (V "aw1") (V "aw2")).evalB B σ = some false := by
        rw [evalB_condEq (evalB_var hw1) (evalB_var hw2)]; simp [hw]
      have r := Run.ite_false (c := .assign "atr" (.lit 1)) (d := .assign "atr" (.lit 0)) hc1
        (Run.assign (x := "atr") (σ := σ) (evalB_lit (n := 0) (B := B) (by omega)))
      refine ⟨_, (Run.ite_true (d := scanC) hc0 r).mono (by simp), ?_⟩
      simp [h0, hw]
  · have hc0 : (Cond.eq (V "asa") (.lit 0)).evalB B σ = some false := by
      rw [evalB_condEq (evalB_var hsaB) (evalB_lit (by omega))]; simp [h0]
    obtain ⟨σ', r, h⟩ := scanC_spec hB σ ⟨ha, hn, hml, hmB, hsb, hsa, hw1, hw2⟩
    refine ⟨_, (Run.ite_false (c := .ite (.eq (V "aw1") (V "aw2")) (.assign "atr" (.lit 1))
      (.assign "atr" (.lit 0))) hc0 r).mono (by simp; omega), ?_⟩
    show σ'.vars "atr" = _
    rw [h, if_neg h0]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj2
