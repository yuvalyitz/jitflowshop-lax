import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRel

/-! # Σ₁[2] model checking to Clique: equations, other nodes, one tokenizer step

`eqC_spec` and `otherC_spec`: the tokenizer steps for an equation and for any other node;
`tokStepC_spec`: one step of the tokenizer at a position inside the word. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok3

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2

theorem eqTail_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zq" < (σ.arrs "ab").length ∧ σ.vars "zq" < (σ.arrs "ar").length ∧
        σ.vars "zq" + 1 < B ∧ σ.vars "zp" + 3 < B)
      (.seq (.store "ab" (V "zq") (.lit 0)) (.seq (.store "ar" (V "zq") (.lit 0))
        (.seq (bump "zq") (.assign "zp" (.add (V "zp") (.lit 3))))))
      (fun σ σ' => σ' = (((σ.setArr "ab" (σ.vars "zq") 0).setArr "ar" (σ.vars "zq") 0).setVar "zq"
        (σ.vars "zq" + 1)).setVar "zp" (σ.vars "zp" + 3)) 30 := by
  run_vcg
  all_goals simp_all

theorem otherTail_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zp" + 1 < B) (.assign "zp" (.add (V "zp") (.lit 1)))
      (fun σ σ' => σ' = σ.setVar "zp" (σ.vars "zp" + 1)) 10 := by
  run_vcg
  all_goals simp_all

set_option maxHeartbeats 4000000 in
/-- **An equation.** -/
theorem eqC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) (st : TS) :
    Spec B (fun σ => CorrX x st σ) eqC (fun _ σ' => Corr x (eqStep x st) σ') 200 := by
  have hent := hB.1
  have hL := HB.len hB
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  have h0 : 0 < B := by omega
  intro σ hσ
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, hpL, hndL, habnd, hvsl, harl,
    snt, sna, svs, sab, sar, lnt, lna, lvs, lab, lar, lbs, gbs⟩ := hσ
  obtain ⟨σ1, r1, e1⟩ := rdV_spec hent h0 "zy1" "zp" 1 σ ⟨ha, hn, by omega, by omega⟩
  obtain ⟨σ2, r2, e2⟩ := rdV_spec hent h0 "zy2" "zp" 2 σ1 ⟨by simp [e1, ha], by simp [e1, hn],
    by simp [e1]; omega, by omega⟩
  obtain ⟨σ3, r3, e3⟩ := pushNodeLit_spec (B := B) 2 σ2 ⟨by simp [e2, e1, hT, lnt, hnt]; omega,
    by simp [e2, e1, hT, lna, hna]; omega, by simp [e2, e1, hT]; omega, by omega,
    by simp [e2, e1, hq]; omega⟩
  obtain ⟨σ4, r4, e4⟩ := pushVars_spec (B := B) σ3 ⟨by simp [e3, e2, e1, hq, lvs, hvs]; omega,
    by simp [e3, e2, e1, hq]; omega, by simp [e3, e2, e1, hrdB], by simp [e3, e2, hrdB]⟩
  obtain ⟨σ5, r5, e5⟩ := eqTail_spec (B := B) σ4 ⟨by simp [e4, e3, e2, e1, hq, hab, lab]; omega,
    by simp [e4, e3, e2, e1, hq, har, lar]; omega, by simp [e4, e3, e2, e1, hq]; omega,
    by simp [e4, e3, e2, e1, hp]; omega⟩
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by norm_num), ?_⟩
  rw [e5, e4, e3, e2, e1]
  simp only [Corr, eqStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp [ha, hn, hs, hbs, hp, hT, hq, hfl])
  · rw [hnt, snt 2 st.ab.length]; simp
  · rw [hna, sna 2 st.ab.length]; simp
  · rw [hvs, svs]
  · rw [hab, sab]
  · rw [har, sar]

set_option maxHeartbeats 4000000 in
/-- **Any other node.** -/
theorem otherC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) (st : TS) :
    Spec B (fun σ => CorrX x st σ ∧ σ.vars "zg" = rd x st.p) otherC
      (fun _ σ' => Corr x (otherStep x st) σ') 50 := by
  have hent := hB.1
  have hL := HB.len hB
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  intro σ ⟨hσ, hg⟩
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, hpL, hndL, habnd, hvsl, harl,
    snt, sna, svs, sab, sar, lnt, lna, lvs, lab, lar, lbs, gbs⟩ := hσ
  obtain ⟨σ1, r1, e1⟩ := pushNodeG_spec (B := B) σ ⟨by rw [hT, hnt, lnt]; omega,
    by rw [hT, hna, lna]; omega, by rw [hT]; omega, by rw [hg]; exact hrdB _⟩
  obtain ⟨σ2, r2, e2⟩ := otherTail_spec (B := B) σ1 (by simp [e1, hp]; omega)
  refine ⟨_, (r1.seq r2).mono (by norm_num), ?_⟩
  rw [e2, e1]
  simp only [Corr, otherStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp [ha, hn, hs, hbs, hp, hT, hq, hfl, hab, har, hvs])
  · rw [hnt, hg, snt (rd x st.p) 0]; simp
  · rw [hna, sna (rd x st.p) 0]; simp

theorem corrX_setVar {x : List ℕ} {st : TS} {σ : Env} (h : CorrX x st σ) (v : ℕ) :
    CorrX x st (σ.setVar "zg" v) := by
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, rest⟩ := h
  exact ⟨ha, by simp [hn], by simp [hs], hbs, by simp [hp], by simp [hT], by simp [hq],
    by simp [hfl], hnt, hna, hvs, hab, har, rest⟩

theorem corr_setVar_zp {x : List ℕ} {st : TS} {σ : Env} (h : CorrX x st σ) (v : ℕ) :
    Corr x { st with p := st.p + 2 } ((σ.setVar "zg" v).setVar "zp" (σ.vars "zp" + 2)) := by
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, -⟩ := h
  exact ⟨ha, by simp [hn], by simp [hs], hbs, by simp [hp], by simp [hT], by simp [hq],
    by simp [hfl], hnt, hna, hvs, hab, har⟩

set_option maxHeartbeats 4000000 in
/-- **One step of the tokenizer**, at a position inside the word. -/
theorem tokStepC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) (st : TS) :
    Spec B (fun σ => CorrX x st σ) tokStepC (fun _ σ' => Corr x (tokStep x st) σ') 260 := by
  have hent := hB.1
  have hL := HB.len hB
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  intro σ hσ
  have hσ' := hσ
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, hpL, -⟩ := hσ'
  have hg : x.getD st.p 0 = rd x st.p := rfl
  have r1 : Run B (.assign "zg" (.get "a" (V "zp"))) σ (σ.setVar "zg" (rd x st.p)) 3 := by
    have := Run.assign (B := B) (x := "zg") (σ := σ) (e := .get "a" (V "zp")) (v := rd x st.p)
      (by
        rw [evalB_get_iff]
        refine ⟨st.p, ?_, ?_, ?_⟩
        · rw [evalB_var_iff, hp]; omega
        · rw [ha, List.getElem?_eq_getElem hpL, ← List.getD_eq_getElem _ 0 hpL]; rfl
        · exact hrdB _)
    simpa using this
  set σ1 := σ.setVar "zg" (rd x st.p) with hσ1
  have hts : tokStep x st = if rd x st.p = 6 then { st with p := st.p + 2 }
      else if rd x st.p = 0 then relStep x st else if rd x st.p = 2 then eqStep x st
      else otherStep x st := by
    simp only [tokStep, if_pos hpL]
  have hc : ∀ k : ℕ, k < B → (Cond.eq (V "zg") (.lit k)).evalB B σ1 = some (decide (rd x st.p = k)) := by
    intro k hk
    have := evalB_condEq (B := B) (evalB_var (x := "zg") (σ := σ1) (by simp [σ1]; exact hrdB _))
      (evalB_lit (σ := σ1) hk)
    rw [this]
    cases hh : (rd x st.p == k) <;> simp_all [σ1]
  have hX1 : CorrX x st σ1 := corrX_setVar hσ _
  have hzg : σ1.vars "zg" = rd x st.p := by simp [σ1]
  have hp2 : σ.vars "zp" + 2 < B := by omega
  by_cases h6 : rd x st.p = 6
  · have hz1 : σ1.vars "zp" = σ.vars "zp" := by simp [σ1]
    have hv : (Expr.add (V "zp") (.lit 2)).evalB B σ1 = some (σ.vars "zp" + 2) := by
      have := evalB_bin (op := .add) (evalB_var (x := "zp") (σ := σ1) (B := B) (by omega))
        (evalB_lit (n := 2) (σ := σ1) (B := B) (by omega)) (by simp; omega)
      rw [hz1] at this; exact this
    have r2 : Run B (.assign "zp" (.add (V "zp") (.lit 2))) σ1 (σ1.setVar "zp" (σ.vars "zp" + 2)) 4 := by
      have := Run.assign (B := B) (x := "zp") (σ := σ1) hv
      simpa using this
    refine ⟨_, (r1.seq (Run.ite_true (by rw [hc 6 (by omega)]; simp [h6]) r2)).mono
      (by simp), ?_⟩
    rw [hts, if_pos h6, hσ1]
    exact corr_setVar_zp hσ _
  · by_cases h0 : rd x st.p = 0
    · obtain ⟨σ2, r2, h2⟩ := ProgRel.relC_spec hB st σ1 hX1
      refine ⟨_, (r1.seq (Run.ite_false (by rw [hc 6 (by omega)]; simp [h6])
        (Run.ite_true (by rw [hc 0 (by omega)]; simp [h0]) r2))).mono (by simp), ?_⟩
      rw [hts, if_neg h6, if_pos h0]; exact h2
    · by_cases h2 : rd x st.p = 2
      · obtain ⟨σ2, r2, hq2⟩ := eqC_spec hB st σ1 hX1
        refine ⟨_, (r1.seq (Run.ite_false (by rw [hc 6 (by omega)]; simp [h6])
          (Run.ite_false (by rw [hc 0 (by omega)]; simp [h0])
            (Run.ite_true (by rw [hc 2 (by omega)]; simp [h2]) r2)))).mono (by simp), ?_⟩
        rw [hts, if_neg h6, if_neg h0, if_pos h2]; exact hq2
      · obtain ⟨σ2, r2, hq2⟩ := otherC_spec hB st σ1 ⟨hX1, hzg⟩
        refine ⟨_, (r1.seq (Run.ite_false (by rw [hc 6 (by omega)]; simp [h6])
          (Run.ite_false (by rw [hc 0 (by omega)]; simp [h0])
            (Run.ite_false (by rw [hc 2 (by omega)]; simp [h2]) r2)))).mono (by simp), ?_⟩
        rw [hts, if_neg h6, if_neg h0, if_neg h2]; exact hq2

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok3
