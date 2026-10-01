import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj3

/-! # Σ₁[2] model checking to Clique: the rows, the whole adjacency test

`rowsC_spec`: the test on the rows of two vertices (different rows, equal values on rows of the same
variable, and the atom test of `ProgAdj3`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj4

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj3
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem setVar_setVar' (σ : Env) (y : String) (a b : ℕ) :
    (σ.setVar y a).setVar y b = σ.setVar y b := by
  cases σ; simp only [Env.setVar, Env.mk.injEq, and_true]
  funext z; split_ifs <;> rfl

set_option maxHeartbeats 2000000 in
theorem rowsA_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "e1" < (σ.arrs "el").length ∧ σ.vars "e2" < (σ.arrs "el").length ∧
        σ.vars "r1" < (σ.arrs "vs").length ∧ σ.vars "r2" < (σ.arrs "vs").length ∧
        σ.vars "e1" < B ∧ σ.vars "e2" < B ∧ σ.vars "r1" < B ∧ σ.vars "r2" < B ∧ 1 < B ∧
        (σ.arrs "el").getD (σ.vars "e1") 0 < B ∧ (σ.arrs "el").getD (σ.vars "e2") 0 < B ∧
        (σ.arrs "vs").getD (σ.vars "r1") 0 < B ∧ (σ.arrs "vs").getD (σ.vars "r2") 0 < B)
      rowsA
      (fun σ σ' => σ' = (((((σ.setVar "av1" ((σ.arrs "el").getD (σ.vars "e1") 0)).setVar "av2"
        ((σ.arrs "el").getD (σ.vars "e2") 0)).setVar "az1" ((σ.arrs "vs").getD (σ.vars "r1") 0)).setVar
        "az2" ((σ.arrs "vs").getD (σ.vars "r2") 0)).setVar "ace"
        (if (σ.arrs "vs").getD (σ.vars "r1") 0 = (σ.arrs "vs").getD (σ.vars "r2") 0 ∧
          (σ.arrs "el").getD (σ.vars "e1") 0 ≠ (σ.arrs "el").getD (σ.vars "e2") 0 then 0 else 1)))
      40 := by
  unfold rowsA
  run_vcg
  all_goals first
    | (simp_all; done)
    | (rw [if_pos (by simp_all)]; simp [setVar_setVar'])

theorem amC_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "r1" < B ∧ σ.vars "r2" < B ∧ 2 < B)
      (.seq (.assign "am1" (.div (V "r1") (.lit 2))) (.assign "am2" (.div (V "r2") (.lit 2))))
      (fun σ σ' => σ' = (σ.setVar "am1" (σ.vars "r1" / 2)).setVar "am2" (σ.vars "r2" / 2)) 20 := by
  run_vcg
  all_goals first
    | omega
    | simp_all

/-- The context of the row test. -/
def RC (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
    σ.arrs "ab" = pad (tok x).ab (x.length + 1) ∧ σ.arrs "ar" = pad (tok x).ar (x.length + 1) ∧
    σ.arrs "el" = pad (elL x) (ProgElb.elN x) ∧ σ.arrs "vs" = pad (tok x).vs (2 * x.length + 2) ∧
    σ.vars "e1" < (elL x).length ∧ σ.vars "e2" < (elL x).length ∧
    σ.vars "r1" < 2 * qX x ∧ σ.vars "r2" < 2 * qX x

set_option maxHeartbeats 4000000 in
/-- **The row test.** -/
theorem rowsC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => RC x σ ∧ σ.vars "c1" < B)
      rowsC
      (fun σ σ' => σ'.vars "gf" =
        if (tok x).vs.getD (σ.vars "r1") 0 = (tok x).vs.getD (σ.vars "r2") 0 ∧
          (elL x).getD (σ.vars "e1") 0 ≠ (elL x).getD (σ.vars "e2") 0 then σ.vars "gf"
        else if σ.vars "r1" / 2 = σ.vars "r2" / 2 then
          (if atomOK (paramsX x) (σ.vars "c1") (σ.vars "r1") (σ.vars "r2")
            ((elL x).getD (σ.vars "e1") 0) ((elL x).getD (σ.vars "e2") 0) then 1 else σ.vars "gf")
        else 1) ((60 + 4) * x.length + 300) := by
  have hW := hB.2
  have hL := ProgTok2.HB.len hB
  have hB2 : 2 < B := by nlinarith
  have hqL := ProgElb.qX_le x
  have hsm := tok_small x
  have hshape := (ProgTokLoop.tok_shape x).1
  have helL := ProgElb.length_elL x
  have hMB : Mmax x < B := by nlinarith
  have h4L : 4 * x.length + 2 < B := by nlinarith
  intro σ ⟨⟨ha, hn, hab, har, hel, hvs, he1, he2, hr1, hr2⟩, hc1⟩
  have hvsl : (tok x).vs.length = 2 * qX x := hshape.2.1
  have lel : (σ.arrs "el").length = ProgElb.elN x := by
    rw [hel, length_pad (by unfold ProgElb.elN; omega)]
  have lvs : (σ.arrs "vs").length = 2 * x.length + 2 := by rw [hvs, length_pad (by omega)]
  have gel : ∀ e, (σ.arrs "el").getD e 0 = (elL x).getD e 0 := fun e => by rw [hel, getD_pad]
  have gvs : ∀ r, (σ.arrs "vs").getD r 0 = (tok x).vs.getD r 0 := fun r => by rw [hvs, getD_pad]
  have bel : ∀ e, (elL x).getD e 0 ≤ Mmax x := fun e => getD_le_of (elL_le x) e
  have bvs : ∀ r, (tok x).vs.getD r 0 ≤ Mmax x := fun r => getD_le_of hsm.2.2 r
  obtain ⟨σ1, r1, e1⟩ := rowsA_spec (B := B) σ ⟨by rw [lel]; unfold ProgElb.elN; omega,
    by rw [lel]; unfold ProgElb.elN; omega, by rw [lvs]; omega, by rw [lvs]; omega,
    by unfold ProgElb.elN at *; omega, by unfold ProgElb.elN at *; omega, by omega, by omega,
    by omega, by rw [gel]; have := bel (σ.vars "e1"); omega,
    by rw [gel]; have := bel (σ.vars "e2"); omega,
    by rw [gvs]; have := bvs (σ.vars "r1"); omega, by rw [gvs]; have := bvs (σ.vars "r2"); omega⟩
  rw [gel, gel, gvs, gvs] at e1
  set V1 := (elL x).getD (σ.vars "e1") 0 with hV1
  set V2 := (elL x).getD (σ.vars "e2") 0 with hV2
  set Z1 := (tok x).vs.getD (σ.vars "r1") 0 with hZ1
  set Z2 := (tok x).vs.getD (σ.vars "r2") 0 with hZ2
  have hace : σ1.vars "ace" = if Z1 = Z2 ∧ V1 ≠ V2 then 0 else 1 := by rw [e1]; simp
  have hgf1 : σ1.vars "gf" = σ.vars "gf" := by rw [e1]; simp
  have hc : ∀ k : ℕ, k < B → (Cond.eq (V "ace") (.lit k)).evalB B σ1 =
      some (decide ((if Z1 = Z2 ∧ V1 ≠ V2 then 0 else 1) = k)) := by
    intro k hk
    have := evalB_condEq (B := B) (evalB_var (x := "ace") (σ := σ1) (by rw [hace]; split_ifs <;> omega))
      (evalB_lit (σ := σ1) hk)
    rw [this, hace]
    cases hh : ((if Z1 = Z2 ∧ V1 ≠ V2 then 0 else 1) == k) <;> simp_all
  by_cases hbad : Z1 = Z2 ∧ V1 ≠ V2
  · refine ⟨σ1, (r1.seq (Run.ite_false (by rw [hc 1 (by omega)]; simp [hbad]) Run.skip)).mono
      (by simp), ?_⟩
    show σ1.vars "gf" = _
    rw [if_pos hbad, hgf1]
  · have hcond := hc 1 (by omega)
    rw [if_neg hbad] at hcond
    obtain ⟨σ2, r2, e2⟩ := amC_spec (B := B) σ1 ⟨by rw [e1]; simp; omega, by rw [e1]; simp; omega,
      hB2⟩
    have hm1 : σ2.vars "am1" = σ.vars "r1" / 2 := by rw [e2, e1]; simp
    have hm2 : σ2.vars "am2" = σ.vars "r2" / 2 := by rw [e2, e1]; simp
    have hcm : (Cond.eq (V "am1") (V "am2")).evalB B σ2 =
        some (decide (σ.vars "r1" / 2 = σ.vars "r2" / 2)) := by
      have := evalB_condEq (B := B) (evalB_var (x := "am1") (σ := σ2) (by rw [hm1]; omega))
        (evalB_var (x := "am2") (σ := σ2) (by rw [hm2]; omega))
      rw [this, hm1, hm2]
      cases hh : (σ.vars "r1" / 2 == σ.vars "r2" / 2) <;> simp_all
    by_cases hmm : σ.vars "r1" / 2 = σ.vars "r2" / 2
    · obtain ⟨σ3, r3, h3⟩ := atomC_spec hB σ2 ⟨by rw [e2, e1]; simp [ha], by rw [e2, e1]; simp [hn],
        by rw [e2, e1]; simp [hab], by rw [e2, e1]; simp [har], by rw [hm1, e2, e1]; simp,
        by rw [hm1]; omega, by rw [e2, e1]; simp; omega, by rw [e2, e1]; simp; omega,
        by rw [e2, e1]; simp; have := bel (σ.vars "e1"); omega,
        by rw [e2, e1]; simp; have := bel (σ.vars "e2"); omega, by rw [e2, e1]; simpa using hc1⟩
      refine ⟨σ3, (r1.seq (Run.ite_true (by rw [hcond]; simp)
        (r2.seq (Run.ite_true (by rw [hcm]; simp [hmm]) r3)))).mono (by simp; omega), ?_⟩
      show σ3.vars "gf" = _
      rw [h3, if_neg hbad, if_pos hmm, e2, e1]
      simp [hV1, hV2]
    · have r3 : Run B (.assign "gf" (.lit 1)) σ2 (σ2.setVar "gf" 1) 2 := by
        have := Run.assign (x := "gf") (σ := σ2) (evalB_lit (n := 1) (B := B) (by omega))
        simpa using this
      refine ⟨_, (r1.seq (Run.ite_true (by rw [hcond]; simp)
        (r2.seq (Run.ite_false (c := atomC) (by rw [hcm]; simp [hmm]) r3)))).mono
        (by simp), ?_⟩
      show (σ2.setVar "gf" 1).vars "gf" = _
      rw [if_neg hbad, if_neg hmm]; simp

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj4
