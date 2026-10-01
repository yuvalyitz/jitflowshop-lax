import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj4

/-! # Σ₁[2] model checking to Clique: the adjacency test computes `adjX`

`adjCom_spec`: the whole adjacency test sets `gf` to `adjX x u v`, and it assigns only the scalars
`adjVars`, stores into no array, reads no input and writes no output. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj4
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem okv_le (x : List ℕ) (c : ℕ) : okv x c ≤ 1 := by
  rw [ProgEval3.okv_eq_sfx]
  have hb := ProgEval2.bits_sfx x c (tok x).nd.length le_rfl
  cases h : ProgEval2.sfx x c (tok x).nd.length with
  | nil => simp
  | cons v t => rw [h] at hb; simpa using hb v List.mem_cons_self

theorem neX_le (x : List ℕ) : neX x ≤ (elL x).length := by
  unfold neX; split_ifs <;> omega

/-- The context of the adjacency test. -/
def AC (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
    σ.arrs "ab" = pad (tok x).ab (x.length + 1) ∧ σ.arrs "ar" = pad (tok x).ar (x.length + 1) ∧
    σ.arrs "el" = pad (elL x) (ProgElb.elN x) ∧ σ.arrs "vs" = pad (tok x).vs (2 * x.length + 2) ∧
    σ.arrs "ok" = (List.range (CX x)).map (okv x) ∧ σ.vars "zk" = kX x ∧ σ.vars "zne" = neX x

/-- The value bound the adjacency test needs. -/
def AB (x : List ℕ) (B : ℕ) : Prop := HB x B ∧ NGX x < B ∧ CX x < B

set_option maxHeartbeats 4000000 in
theorem testC_spec {x : List ℕ} {B : ℕ} (hB : AB x B) {u w : ℕ} (hu : u < NGX x)
    (hw : w < NGX x) :
    Spec B (fun σ => AC x σ ∧ σ.vars "r1" = rowOf (paramsX x) u ∧
        σ.vars "e1" = eltOf (paramsX x) u ∧ σ.vars "c1" = compOf (paramsX x) u ∧
        σ.vars "r2" = rowOf (paramsX x) w ∧ σ.vars "e2" = eltOf (paramsX x) w ∧
        σ.vars "c2" = compOf (paramsX x) w)
      testC (fun _ σ' => σ'.vars "gf" = if adjX x u w then 1 else 0) ((60 + 4) * x.length + 400) := by
  obtain ⟨hH, hNG, hC⟩ := hB
  have hW := hH.2
  have hB2 : 2 < B := by nlinarith
  have hL := ProgTok2.HB.len hH
  have hqL := ProgElb.qX_le x
  set P := paramsX x with hP
  have hu' : u < CX x * (P.ne * P.k) := hu
  have hw' : w < CX x * (P.ne * P.k) := hw
  have hcu := compOf_lt P hu'
  have hcw := compOf_lt P hw'
  have heu := eltOf_lt P hu'
  have hew := eltOf_lt P hw'
  have hru := rowOf_lt P hu'
  have hrw := rowOf_lt P hw'
  have hne : P.ne ≤ (elL x).length := neX_le x
  have hk : P.k = 2 * qX x := rfl
  intro σ ⟨hac, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨ha, hn, hab, har, hel, hvs, hok, hzk, hzne⟩ := hac
  have r0 : Run B (.assign "gf" (.lit 0)) σ (σ.setVar "gf" 0) 2 := by
    have := Run.assign (x := "gf") (σ := σ) (evalB_lit (n := 0) (B := B) (by omega))
    simpa using this
  set σ0 := σ.setVar "gf" 0 with hσ0
  have v0 : ∀ y, y ≠ "gf" → σ0.vars y = σ.vars y := fun y hy => by simp [hσ0, hy]
  have hcc : (Cond.eq (V "c1") (V "c2")).evalB B σ0 =
      some (decide (compOf P u = compOf P w)) := by
    rw [evalB_condEq (evalB_var (x := "c1") (σ := σ0) (by rw [v0 _ (by decide), h3]; omega))
      (evalB_var (x := "c2") (σ := σ0) (by rw [v0 _ (by decide), h6]; omega)),
      v0 _ (by decide), v0 _ (by decide), h3, h6]
    cases hh : (compOf P u == compOf P w) <;> simp_all
  have hadj : adjX x u w = adjP P u w := rfl
  unfold adjP at hadj
  by_cases hc : compOf P u = compOf P w
  · rw [if_pos hc] at hadj
    -- read ok[c1]
    have hokl : (σ0.arrs "ok").length = CX x := by simp [hσ0, hok]
    have hokv : (σ0.arrs "ok").getD (σ0.vars "c1") 0 = okv x (compOf P u) := by
      simp only [hσ0, arrs_setVar, vars_setVar]
      rw [if_neg (by decide), h3, hok, List.getD_eq_getElem _ _ (by simpa using hcu)]
      simp
    have hokB := okv_le x (compOf P u)
    have r1 : Run B (.assign "ao" (.get "ok" (V "c1"))) σ0
        (σ0.setVar "ao" (okv x (compOf P u))) 3 := by
      have := Run.assign (x := "ao") (σ := σ0) (e := .get "ok" (V "c1")) (B := B)
        (v := okv x (compOf P u)) (by
          rw [← hokv]
          have hlt : σ0.vars "c1" < (σ0.arrs "ok").length := by
            rw [hokl, v0 _ (by decide), h3]; exact hcu
          exact evalB_get (evalB_var (by rw [v0 _ (by decide), h3]; omega))
            (by rw [List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt])
            (by rw [hokv]; omega))
      simpa using this
    set σ1 := σ0.setVar "ao" (okv x (compOf P u)) with hσ1
    have v1 : ∀ y, y ≠ "gf" → y ≠ "ao" → σ1.vars y = σ.vars y := fun y hy hy' => by
      simp [hσ1, hσ0, hy, hy']
    have hco : (Cond.eq (V "ao") (.lit 1)).evalB B σ1 = some (decide (okv x (compOf P u) = 1)) := by
      rw [evalB_condEq (evalB_var (x := "ao") (σ := σ1) (by simp [hσ1]; omega))
        (evalB_lit (n := 1) (σ := σ1) (by omega))]
      cases hh : (okv x (compOf P u) == 1) <;> simp_all
    by_cases ho : okv x (compOf P u) = 1
    · have hPo : P.ok (compOf P u) = 1 := ho
      rw [if_pos hPo] at hadj
      have hcr : (Cond.eq (V "r1") (V "r2")).evalB B σ1 =
          some (decide (rowOf P u = rowOf P w)) := by
        rw [evalB_condEq (evalB_var (x := "r1") (σ := σ1) (by rw [v1 _ (by decide) (by decide), h1]; omega))
          (evalB_var (x := "r2") (σ := σ1) (by rw [v1 _ (by decide) (by decide), h4]; omega)),
          v1 _ (by decide) (by decide), v1 _ (by decide) (by decide), h1, h4]
        cases hh : (rowOf P u == rowOf P w) <;> simp_all
      by_cases hr : rowOf P u = rowOf P w
      · rw [if_pos hr] at hadj
        refine ⟨σ1, (r0.seq (Run.ite_true (by rw [hcc]; simp [hc])
          (r1.seq (Run.ite_true (by rw [hco]; simp [ho])
            (Run.ite_true (d := rowsC) (by rw [hcr]; simp [hr]) Run.skip))))).mono ?_, ?_⟩
        · simp
        · show σ1.vars "gf" = _
          rw [hadj]; simp [hσ1, hσ0]
      · rw [if_neg hr] at hadj
        obtain ⟨σ2, r2, h2'⟩ := rowsC_spec hH σ1 ⟨⟨by simp [hσ1, hσ0, ha], by simp [hσ1, hσ0, hn],
          by simp [hσ1, hσ0, hab], by simp [hσ1, hσ0, har], by simp [hσ1, hσ0, hel],
          by simp [hσ1, hσ0, hvs], by rw [v1 _ (by decide) (by decide), h2]; omega,
          by rw [v1 _ (by decide) (by decide), h5]; omega,
          by rw [v1 _ (by decide) (by decide), h1, ← hk]; exact hru,
          by rw [v1 _ (by decide) (by decide), h4, ← hk]; exact hrw⟩,
          by rw [v1 _ (by decide) (by decide), h3]; omega⟩
        refine ⟨σ2, (r0.seq (Run.ite_true (by rw [hcc]; simp [hc])
          (r1.seq (Run.ite_true (by rw [hco]; simp [ho])
            (Run.ite_false (c := .skip) (by rw [hcr]; simp [hr]) r2))))).mono ?_, ?_⟩
        · simp; omega
        · show σ2.vars "gf" = _
          rw [h2', hadj]
          simp only [v1 _ (by decide) (by decide : "r1" ≠ "ao"), v1 "r2" (by decide) (by decide),
            v1 "e1" (by decide) (by decide), v1 "e2" (by decide) (by decide),
            v1 "c1" (by decide) (by decide), h1, h2, h3, h4, h5]
          have hgf1 : σ1.vars "gf" = 0 := by simp [hσ1, hσ0]
          rw [hgf1]
          show (if P.vs (rowOf P u) = P.vs (rowOf P w) ∧ valOf P u ≠ valOf P w then 0
            else if rowOf P u / 2 = rowOf P w / 2 then
              (if atomOK P (compOf P u) (rowOf P u) (rowOf P w) (valOf P u) (valOf P w) then 1 else 0)
            else 1) = _
          by_cases hb : P.vs (rowOf P u) = P.vs (rowOf P w) ∧ valOf P u ≠ valOf P w
          · simp [hb]
          · simp only [if_neg hb]
            by_cases hm : rowOf P u / 2 = rowOf P w / 2
            · simp only [if_pos hm]
            · simp [hm]
    · have hPo : ¬ P.ok (compOf P u) = 1 := ho
      rw [if_neg hPo] at hadj
      refine ⟨σ1, (r0.seq (Run.ite_true (by rw [hcc]; simp [hc])
        (r1.seq (Run.ite_false (by rw [hco]; simp [ho]) Run.skip)))).mono ?_, ?_⟩
      · simp
      · show σ1.vars "gf" = _
        rw [hadj]; simp [hσ1, hσ0]
  · rw [if_neg hc] at hadj
    refine ⟨σ0, (r0.seq (Run.ite_false (by rw [hcc]; simp [hc]) Run.skip)).mono ?_, ?_⟩
    · simp
    · show σ0.vars "gf" = _
      rw [hadj]; simp [hσ0]

/-- The scalars the adjacency test may assign. -/
def adjVars : List String :=
  ["r1", "t1", "e1", "c1", "r2", "t2", "e2", "c2", "gf", "ao", "av1", "av2", "az1", "az2", "ace",
    "am1", "am2", "aw1", "aw2", "ah", "abt", "asa", "atr", "asb", "acnt", "asj", "apos", "au1",
    "au2"]

/-- The cost of the adjacency test. -/
def Kadj (x : List ℕ) : ℕ := 100 + ((60 + 4) * x.length + 400)

set_option maxHeartbeats 2000000 in
theorem adjCom_spec {x : List ℕ} {B : ℕ} (hB : AB x B) :
    Spec B (fun σ => AC x σ ∧ σ.vars "gs" < NGX x ∧ σ.vars "gt" < NGX x) adjCom
      (fun σ σ' => σ'.vars "gf" = if adjX x (σ.vars "gs") (σ.vars "gt") then 1 else 0) (Kadj x) := by
  have hL := ProgTok2.HB.len hB.1
  have hqL := ProgElb.qX_le x
  have helL := ProgElb.length_elL x
  have hne := neX_le x
  have hW := hB.1.2
  have h4 : 4 * x.length + 2 < B := by nlinarith
  have hNG := hB.2.1
  intro σ ⟨hac, hu, hw⟩
  have hk : σ.vars "zk" = kX x := hac.2.2.2.2.2.2.2.1
  have hne' : σ.vars "zne" = neX x := hac.2.2.2.2.2.2.2.2
  obtain ⟨σ1, r1, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := decC_spec (B := B) σ
    (decC_pre (by omega) (by omega) (by rw [hk]; unfold kX; omega) (by rw [hne']; omega))
  have fv : ∀ y, y ∉ decC.wvars → σ1.vars y = σ.vars y := fun y hy => r1.frame_var y hy
  have fa : ∀ a, a ∉ decC.warrs → σ1.arrs a = σ.arrs a := fun a ha => r1.frame_arr a (by
    simp [decC, Com.warrs] at ha ⊢)
  have hac1 : AC x σ1 := by
    obtain ⟨ha, hn, hab, har, hel, hvs, hok, hzk, hzne⟩ := hac
    refine ⟨by rw [fa "a" (by simp [decC, Com.warrs])]; exact ha,
      by rw [fv "rt_n" (by decide)]; exact hn,
      by rw [fa "ab" (by simp [decC, Com.warrs])]; exact hab,
      by rw [fa "ar" (by simp [decC, Com.warrs])]; exact har,
      by rw [fa "el" (by simp [decC, Com.warrs])]; exact hel,
      by rw [fa "vs" (by simp [decC, Com.warrs])]; exact hvs,
      by rw [fa "ok" (by simp [decC, Com.warrs])]; exact hok,
      by rw [fv "zk" (by decide)]; exact hzk, by rw [fv "zne" (by decide)]; exact hzne⟩
  simp only [hk, hne'] at d1 d2 d3 d4 d5 d6
  obtain ⟨σ2, r2, h2⟩ := testC_spec hB hu hw σ1 ⟨hac1, d1, d2, d3, d4, d5, d6⟩
  exact ⟨σ2, (r1.seq r2).mono (by unfold Kadj; omega), h2⟩

theorem adjCom_wvars : ∀ y ∈ adjCom.wvars, y ∈ adjVars := by decide

theorem adjCom_warrs : adjCom.warrs = [] := by decide

theorem adjCom_reads : ¬ adjCom.reads := by decide

theorem adjCom_noWrite : adjCom.NoWrite := by decide

theorem adjCom_spec' {x : List ℕ} {B : ℕ} (hB : AB x B) :
    Spec B (fun σ => AC x σ ∧ σ.vars "gs" < NGX x ∧ σ.vars "gt" < NGX x) adjCom
      (fun σ σ' => σ'.vars "gf" = (if adjX x (σ.vars "gs") (σ.vars "gt") then 1 else 0) ∧
        Keep adjVars σ σ' ∧ σ'.out = σ.out) (Kadj x) := by
  refine Spec.post (Spec.frame (adjCom_spec hB)) fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ => ⟨hq, ?_, ?_⟩
  · refine ⟨fun y hy => hv y fun hm => hy (adjCom_wvars y hm), funext fun a => ha a ?_,
      hi adjCom_reads⟩
    rw [adjCom_warrs]; simp
  · exact ho adjCom_noWrite

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5
