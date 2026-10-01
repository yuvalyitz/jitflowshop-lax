import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2

/-! # Σ₁[2] model checking to Clique: a relation atom

`relC_spec`: the tokenizer step for a relation atom records its node, its two variables, and the
block start and arity of its symbol. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2

set_option maxHeartbeats 4000000 in
/-- **A relation atom.** -/
theorem relC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) (st : TS) :
    Spec B (fun σ => CorrX x st σ) relC (fun _ σ' => Corr x (relStep x st) σ') 200 := by
  have hent := hB.1
  have hL := HB.len hB
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  have hpB : ∀ i, hp x i < B := hp_lt_of hB
  have h0 : 0 < B := by omega
  have hLM : x.length + Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds.Mmax x + 4 < B := by
    have := hB.2; nlinarith
  intro σ hσ
  obtain ⟨ha, hn, hs, hbs, hp, hT, hq, hfl, hnt, hna, hvs, hab, har, hpL, hndL, habnd, hvsl, harl,
    snt, sna, svs, sab, sar, lnt, lna, lvs, lab, lar, lbs, gbs⟩ := hσ
  obtain ⟨σ1, r1, e1⟩ := rdV_spec hent h0 "zi" "zp" 1 σ ⟨ha, hn, by omega, by omega⟩
  obtain ⟨σ2, r2, e2⟩ := rdV_spec hent h0 "zn" "zp" 2 σ1 ⟨by simp [e1, ha], by simp [e1, hn],
    by simp [e1]; omega, by omega⟩
  obtain ⟨σ3, r3, e3⟩ := relVars_spec hB σ2 ⟨by simp [e2, e1, ha], by simp [e2, e1, hn],
    by simp [e2, e1]; omega, by omega, by simp [e2, hrdB]⟩
  obtain ⟨σ4, r4, e4⟩ := pushNodeLit_spec (B := B) 0 σ3 ⟨by simp [e3, e2, e1, hT, lnt, hnt]; omega,
    by simp [e3, e2, e1, hT, lna, hna]; omega, by simp [e3, e2, e1, hT]; omega, by omega,
    by simp [e3, e2, e1, hq]; omega⟩
  obtain ⟨σ5, r5, e5⟩ := pushVars_spec (B := B) σ4 ⟨by simp [e4, e3, e2, e1, hq, lvs, hvs]; omega,
    by simp [e4, e3, e2, e1, hq]; omega,
    by simp [e4, e3]; split_ifs <;> first | omega | exact hrdB _,
    by simp [e4, e3]; split_ifs <;> first | omega | exact hrdB _⟩
  obtain ⟨σ6, r6, ⟨hab6, har6, hfl6⟩, hkv, hka, hki, hko⟩ :=
    relSym_spec hB st.ab st.ar st.fl σ5 ⟨by simp [e5, e4, e3, e2, e1, ha],
      by simp [e5, e4, e3, e2, e1, hn], by simp [e5, e4, e3, e2, e1, hs],
      by simp [e5, e4, e3, e2, e1, hbs], by simp [e5, e4, e3, e2, e1, hab],
      by simp [e5, e4, e3, e2, e1, har], by simp [e5, e4, e3, e2, e1, hq], harl, by omega,
      by simp [e5, e4, e3, e2, e1, hfl], by simp [e5, e4, e3, e2, e1, hrdB],
      by simp [e5, e4, e3, e2, hrdB]⟩
  obtain ⟨σ7, r7, e7⟩ := relTail_spec (B := B) σ6 ⟨by rw [hkv _ (by decide)]; simp [e5, e4, e3, e2, e1, hq]; omega,
    by rw [hkv _ (by decide), hkv _ (by decide)]; simp [e5, e4, e3, e2, e1, hp]
       have := rd_le_Mmax x (st.p + 2); omega,
    by rw [hkv _ (by decide)]; simp [e5, e4, e3, e2, e1, hn]; omega,
    by rw [hkv _ (by decide)]; simp [e5, e4, e3, e2, hrdB]⟩
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (by norm_num), ?_⟩
  have hv6 : ∀ y, y ≠ "zw" → y ≠ "zfl" → σ6.vars y = σ5.vars y := fun y h1 h2 =>
    hkv y (by simp [h1, h2])
  have ha6 : ∀ a, a ≠ "ab" → a ≠ "ar" → σ6.arrs a = σ5.arrs a := fun a h1 h2 =>
    hka a (by simp [h1, h2])
  have v5 : ∀ y, y ≠ "zT" → y ≠ "zi" → y ≠ "zn" → y ≠ "zy1" → y ≠ "zy2" →
      σ5.vars y = σ.vars y := by
    intro y h1 h2 h3 h4 h5; rw [e5, e4, e3, e2, e1]; simp [h1, h2, h3, h4, h5]
  have zi5 : σ5.vars "zi" = rd x (st.p + 1) := by rw [e5, e4, e3, e2, e1]; simp [hp]
  have zn5 : σ5.vars "zn" = rd x (st.p + 2) := by rw [e5, e4, e3, e2, e1]; simp [hp]
  rw [e7]
  simp only [Corr, relStep, vars_setVar, arrs_setVar]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha6 "a" (by decide) (by decide), e5, e4, e3, e2, e1]; simp [ha]
  · (try simp); rw [hv6 _ (by decide) (by decide), v5 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hn]
  · (try simp); rw [hv6 _ (by decide) (by decide), v5 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hs]
  · rw [ha6 "bs" (by decide) (by decide), e5, e4, e3, e2, e1]; simp [hbs]
  · rw [hv6 "zn" (by decide) (by decide), hv6 "rt_n" (by decide) (by decide),
      hv6 "zp" (by decide) (by decide), zn5, v5 "rt_n" (by decide) (by decide) (by decide)
      (by decide) (by decide), v5 "zp" (by decide) (by decide) (by decide) (by decide) (by decide),
      hn, hp]
    simp
  · (try simp); rw [hv6 _ (by decide) (by decide), e5, e4]; simp [e3, e2, e1, hT]
  · (try simp); rw [hv6 _ (by decide) (by decide), v5 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hq]
  · (try simp); rw [hfl6, zi5, zn5, rd_one_add]
  · rw [ha6 "nt" (by decide) (by decide), e5, e4]; simp [e3, e2, e1, hnt, hT]
    rw [snt 0 st.ab.length]; simp
  · rw [ha6 "na" (by decide) (by decide), e5, e4]; simp [e3, e2, e1, hna, hT, hq]
    rw [sna 0 st.ab.length]; simp
  · rw [ha6 "vs" (by decide) (by decide), e5, e4]; simp [e3, e2, e1, hvs, hq, svs, hp]
  · rw [hab6, zi5]
  · rw [har6, zi5, rd_one_add]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRel
