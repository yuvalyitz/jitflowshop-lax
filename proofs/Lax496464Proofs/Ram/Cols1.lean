import Lax496464Proofs.Ram.Col1
import Lax496464Proofs.Ram.Sort

/-!
# All the columns

The table's column `W'` is `colStep` of column `W' − 1`. The machine computes them in turn,
keeping only two — that is the whole space — and records whether any column `W'' ≥ W` has a
non-`−∞` first entry. This file has the two facts about `colStep` that make the two-column
machine sound (it depends on the previous column only where `nxt` looks, and stays below
`inf`) and the loop over the columns.
-/

namespace Lax496464Proofs.Ram.Cols1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Dp1 Lax496464Proofs.Ram.Col1 Lax496464Proofs.Ram.ListUtil

section colStepFacts

variable {n inf : ℕ} {nxt pF qF dF : ℕ → ℕ}

theorem colStep_congr {prev prev' : ℕ → ℕ}
    (h : ∀ j, j < n → prev (nxt j) = prev' (nxt j)) :
    ∀ j, colStep n inf nxt pF qF dF prev j = colStep n inf nxt pF qF dF prev' j := by
  intro j
  induction' hk : n - j using Nat.strong_induction_on with k ih generalizing j
  by_cases hj : n ≤ j
  · rw [colStep_of_le hj, colStep_of_le hj]
  · rw [colStep_of_lt (prev := prev) (j := j) (by omega), colStep_of_lt (prev := prev') (j := j) (by omega),
      h j (by omega), ih (n - (j + 1)) (by omega) (j + 1) rfl]

theorem colStep_le {prev : ℕ → ℕ} (hd : ∀ j, j < n → dF j + 1 ≤ inf) :
    ∀ j, colStep n inf nxt pF qF dF prev j ≤ inf := by
  intro j
  induction' hk : n - j using Nat.strong_induction_on with k ih generalizing j
  by_cases hj : n ≤ j
  · rw [colStep_of_le hj]; omega
  · rw [colStep_of_lt (prev := prev) (j := j) (by omega)]
    have h1 := ih (n - (j + 1)) (by omega) (j + 1) rfl
    have h2 := fNat_le inf (prev (nxt j)) (dF j) (qF j) (pF j)
    have h3 := hd j (by omega)
    exact max_le h1 (by omega)

theorem colAll_le (hd : ∀ j, j < n → dF j + 1 ≤ inf) (W' : ℕ) (t : ℕ) :
    colAll n inf nxt pF qF dF W' t ≤ inf := by
  cases W' with
  | zero => simp [colAll]
  | succ W1 => exact colStep_le hd t

end colStepFacts

/-! ## Copying a column, and filling one -/

/-- `PC := CC`, entry by entry. -/
def copyCol : Com :=
  .seq (.assign "ck" (.lit 0))
    (.while (.lt (V "ck") (V "sn1"))
      (.seq (.store "PC" (V "ck") (.get "CC" (V "ck"))) (bump "ck")))

theorem copyCol_spec {B : ℕ} (hB : 1 < B) (S : List ℕ) (hnB : S.length < B)
    (hS : ∀ v ∈ S, v < B) :
    Spec B (fun σ => σ.arrs "CC" = S ∧ (σ.arrs "PC").length = S.length ∧
        σ.vars "sn1" = S.length) copyCol
      (fun _ σ' => σ'.arrs "PC" = S ∧ σ'.arrs "CC" = S ∧ σ'.vars "sn1" = S.length)
      ((20 + 4) * S.length + 6) := by
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq (.store "PC" (V "ck") (.get "CC" (V "ck"))) (bump "ck")) "ck" "sn1"
    (fun σ => σ.arrs "CC" = S ∧ (σ.arrs "PC").length = S.length ∧ σ.vars "sn1" = S.length ∧
      σ.vars "ck" ≤ S.length ∧ (σ.arrs "PC").take (σ.vars "ck") = S.take (σ.vars "ck"))
    S.length 20 hnB (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1) (by
      refine Spec.of_exists fun σ ⟨⟨hCC, hPCl, hsn, hle, htk⟩, hlt⟩ => ?_
      have hvi : (V "ck").evalB B σ = some (σ.vars "ck") :=
        evalB_var (B := B) (σ := σ) (x := "ck") (by omega)
      have hcell : σ.vars "ck" < S.length := by omega
      have hg : (Expr.get "CC" (V "ck")).evalB B σ = some (S.getD (σ.vars "ck") 0) := by
        have := RunStep.eval_get B σ "CC" (V "ck") (σ.vars "ck") hvi (by rw [hCC]; exact hcell)
          (by rw [hCC]; exact hS _ (by rw [List.getD_eq_getElem _ _ hcell]; exact List.getElem_mem hcell))
        rwa [hCC] at this
      have r1 := Run.store (B := B) (σ := σ) (a := "PC") (i := V "ck") (e := .get "CC" (V "ck"))
        (idx := σ.vars "ck") (v := S.getD (σ.vars "ck") 0) hvi hg (by omega)
      set σa : Env := σ.setArr "PC" (σ.vars "ck") (S.getD (σ.vars "ck") 0) with hσa
      have hvia : (V "ck").evalB B σa = some (σ.vars "ck") := by
        have : σa.vars "ck" = σ.vars "ck" := by simp [hσa]
        exact this ▸ evalB_var (B := B) (σ := σa) (x := "ck") (by rw [this]; omega)
      have hl1 : (Expr.lit 1).evalB B σa = some 1 := evalB_lit hB
      have r2 := Run.assign (B := B) (σ := σa) (x := "ck") (e := .bin .add (V "ck") (.lit 1))
        (v := σ.vars "ck" + 1) (evalB_bin hvia hl1 (by show σ.vars "ck" + 1 < B; omega))
      refine ⟨_, 20, (r1.seq r2).mono ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.size]; omega
      · simp [hσa, hCC]
      · simp [hσa, hPCl]
      · simp [hσa, hsn]
      · simp [hσa]; omega
      · simp only [hσa, arrs_setVar, arrs_setArr, vars_setVar, if_true]
        rw [Lax496464Proofs.Ram.Sort.take_set_succ _ (by omega), htk,
          Lax496464Proofs.Ram.Sort.take_getD_succ S hcell]
      · simp [hσa])
  refine (hloop.conseq ?_ ?_ le_rfl)
  · rintro σ ⟨hCC, hPCl, hsn⟩
    exact ⟨by simpa using hCC, by simpa using hPCl, by simpa using hsn, by simp, by simp⟩
  · rintro σ σ' - ⟨⟨hCC, hPCl, hsn, hle, htk⟩, hsi⟩
    rw [hsi] at htk
    refine ⟨?_, hCC, hsn⟩
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at htk
    exact htk

/-- `PC := [inf, …, inf]`: column `0`, where every entry is `+∞`. -/
def fillInf : Com :=
  .seq (.assign "ck" (.lit 0))
    (.while (.lt (V "ck") (V "sn1"))
      (.seq (.store "PC" (V "ck") (V "cinf")) (bump "ck")))

theorem fillInf_spec {B : ℕ} (hB : 1 < B) (inf len : ℕ) (hnB : len < B) (hi : inf < B) :
    Spec B (fun σ => (σ.arrs "PC").length = len ∧ σ.vars "sn1" = len ∧ σ.vars "cinf" = inf)
      fillInf
      (fun _ σ' => σ'.arrs "PC" = List.replicate len inf ∧ σ'.vars "sn1" = len ∧
        σ'.vars "cinf" = inf) ((20 + 4) * len + 6) := by
  have hloop := Spec.forRangeZero (B := B)
    (c := .seq (.store "PC" (V "ck") (V "cinf")) (bump "ck")) "ck" "sn1"
    (fun σ => (σ.arrs "PC").length = len ∧ σ.vars "sn1" = len ∧ σ.vars "cinf" = inf ∧
      σ.vars "ck" ≤ len ∧ (σ.arrs "PC").take (σ.vars "ck") = (List.replicate len inf).take (σ.vars "ck"))
    len 20 hnB (fun σ h => h.2.2.2.1) (fun σ h => h.2.1) (by
      refine Spec.of_exists fun σ ⟨⟨hPCl, hsn, hinf, hle, htk⟩, hlt⟩ => ?_
      have hvi : (V "ck").evalB B σ = some (σ.vars "ck") :=
        evalB_var (B := B) (σ := σ) (x := "ck") (by omega)
      have hvc : (V "cinf").evalB B σ = some inf :=
        hinf ▸ evalB_var (B := B) (σ := σ) (x := "cinf") (by rw [hinf]; exact hi)
      have r1 := Run.store (B := B) (σ := σ) (a := "PC") (i := V "ck") (e := V "cinf")
        (idx := σ.vars "ck") (v := inf) hvi hvc (by omega)
      set σa : Env := σ.setArr "PC" (σ.vars "ck") inf with hσa
      have hvia : (V "ck").evalB B σa = some (σ.vars "ck") := by
        have : σa.vars "ck" = σ.vars "ck" := by simp [hσa]
        exact this ▸ evalB_var (B := B) (σ := σa) (x := "ck") (by rw [this]; omega)
      have hl1 : (Expr.lit 1).evalB B σa = some 1 := evalB_lit hB
      have r2 := Run.assign (B := B) (σ := σa) (x := "ck") (e := .bin .add (V "ck") (.lit 1))
        (v := σ.vars "ck" + 1) (evalB_bin hvia hl1 (by show σ.vars "ck" + 1 < B; omega))
      refine ⟨_, 20, (r1.seq r2).mono ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.size]; omega
      · simp [hσa, hPCl]
      · simp [hσa, hsn]
      · simp [hσa, hinf]
      · simp [hσa]; omega
      · simp only [hσa, arrs_setVar, arrs_setArr, vars_setVar, if_true]
        rw [Lax496464Proofs.Ram.Sort.take_set_succ _ (by omega), htk]
        have h1 : (List.replicate len inf).take (σ.vars "ck" + 1) =
            (List.replicate len inf).take (σ.vars "ck") ++ [inf] := by
          rw [List.take_replicate, List.take_replicate, min_eq_left (by omega), min_eq_left (by omega),
            List.replicate_succ']
        rw [h1]
      · simp [hσa])
  refine (hloop.conseq ?_ ?_ le_rfl)
  · rintro σ ⟨hPCl, hsn, hinf⟩
    exact ⟨by simpa using hPCl, by simpa using hsn, by simpa using hinf, by simp, by simp⟩
  · rintro σ σ' - ⟨⟨hPCl, hsn, hinf, hle, htk⟩, hsi⟩
    rw [hsi] at htk
    refine ⟨?_, hsn, hinf⟩
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp)] at htk
    exact htk

/-- After the column `wc + 1`: if `wc + 1 ≥ W` and its first entry is not `−∞`, the answer is yes. -/
def ansCheck : Com :=
  .seq (.assign "c0" (.get "CC" (.lit 0)))
    (.seq (.assign "cwp" (.bin .add (V "wc") (.lit 1)))
      (.ite (.lt (V "cwp") (V "W")) .skip
        (.ite (.eq (V "c0") (.lit 0)) .skip (.assign "ans" (.lit 1)))))

theorem ansCheck_spec {B : ℕ} (hB : 2 < B) (CL : List ℕ) (w W0 a0 : ℕ) (hl : 0 < CL.length)
    (hc0 : CL.getD 0 0 < B) (hwB : w + 1 < B) (hWB : W0 < B) :
    Spec B (fun σ => σ.arrs "CC" = CL ∧ σ.vars "wc" = w ∧ σ.vars "W" = W0 ∧ σ.vars "ans" = a0)
      ansCheck
      (fun σ σ' => σ'.vars "ans" = (if ¬ (w + 1 < W0) ∧ CL.getD 0 0 ≠ 0 then 1 else a0) ∧
        (∀ y, y ≠ "c0" → y ≠ "cwp" → y ≠ "ans" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 30 := by
  run_vcg
  all_goals (simp_all)

/-- The table's columns, with the four arrays read as functions. -/
def CA (n inf : ℕ) (NX PS QS DS : List ℕ) : ℕ → ℕ → ℕ :=
  colAll n inf (fun j => NX.getD j 0) (fun j => PS.getD j 0) (fun j => QS.getD j 0)
    (fun j => DS.getD j 0)

theorem _root_.Lax496464Proofs.Ram.Col1.Dat.withPC {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (h : Dat B inf n NX PS QS DS PC)
    (PC' : List ℕ) (hl : PC'.length = n + 1) (hb : ∀ t, t ≤ n → PC'.getD t 0 ≤ inf) :
    Dat B inf n NX PS QS DS PC' :=
  { h with lenC := hl, bC := hb }

/-- The column `w + 1` is `colStep` of the column `w`, whichever list holds column `w`. -/
theorem cst_eq_CA {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (hd : Dat B inf n NX PS QS DS PC) (w : ℕ)
    (hPC : ∀ t, t ≤ n → PC.getD t 0 = CA n inf NX PS QS DS w t) (t : ℕ) :
    cst n inf NX PS QS DS PC t = CA n inf NX PS QS DS (w + 1) t := by
  unfold cst CA colAll
  exact colStep_congr (fun j hj => hPC (NX.getD j 0) (hd.nxt j hj).2) t

/-- What the loop over columns keeps. -/
def OJ (inf n W0 : ℕ) (NX PS QS DS : List ℕ) (σ : Env) : Prop :=
  σ.arrs "NX" = NX ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧ σ.arrs "DS" = DS ∧
  σ.vars "sn" = n ∧ σ.vars "sn1" = n + 1 ∧ σ.vars "cinf" = inf ∧ σ.vars "W" = W0 ∧
  (σ.arrs "CC").length = n + 1 ∧ (σ.arrs "PC").length = n + 1 ∧ σ.vars "wc" ≤ n ∧
  (∀ t, t ≤ n → (σ.arrs "PC").getD t 0 = CA n inf NX PS QS DS (σ.vars "wc") t) ∧
  (σ.vars "ans" = 1 ∨ σ.vars "ans" = 0) ∧
  (σ.vars "ans" = 1 ↔ ∃ W'', W0 ≤ W'' ∧ W'' ≤ σ.vars "wc" ∧
    CA n inf NX PS QS DS W'' 0 ≠ 0)

/-- One column: compute it, note whether it answers yes, and keep it for the next. -/
def colsBody : Com := .seq colCol (.seq ansCheck (.seq copyCol (bump "wc")))

theorem colsBody_spec {B inf n W0 : ℕ} {NX PS QS DS PC0 : List ℕ}
    (hd : Dat B inf n NX PS QS DS PC0) (hW : W0 < B) :
    Spec B (fun σ => OJ inf n W0 NX PS QS DS σ ∧ σ.vars "wc" < n) colsBody
      (fun σ σ' => OJ inf n W0 NX PS QS DS σ' ∧ σ'.vars "wc" = σ.vars "wc" + 1)
      (2 + (1 + 1) + ((160 + 4) * n + 6) + 30 + ((20 + 4) * (n + 1) + 6) + 4) := by
  have hB1 : 1 < B := by have := hd.two; omega
  have hcle : ∀ W' t, CA n inf NX PS QS DS W' t ≤ inf :=
    fun W' t => colAll_le (fun j hj => by have := hd.infd j hj; omega) W' t
  refine Spec.of_exists fun σ ⟨⟨hNX, hPS, hQS, hDS, hsn, hsn1, hinf, hWv, hCCl, hPCl, hwc, hPCv,
    hans, hansiff⟩, hlt⟩ => ?_
  set w := σ.vars "wc" with hw
  have hdp : Dat B inf n NX PS QS DS (σ.arrs "PC") :=
    hd.withPC _ hPCl (fun t ht => by rw [hPCv t ht]; exact hcle _ _)
  obtain ⟨σ1, hr1, ⟨hNX1, hPS1, hQS1, hDS1, hPC1, hsn1', hinf1, hCC1l, hCC1v⟩, hfv1, hfa1, -, -⟩ :=
    (colCol_spec hdp).frame.run ⟨hNX, hPS, hQS, hDS, rfl, hsn, hinf, hCCl⟩
  have hCA1 : ∀ t, t ≤ n → (σ1.arrs "CC").getD t 0 = CA n inf NX PS QS DS (w + 1) t :=
    fun t ht => (hCC1v t ht).trans (cst_eq_CA hdp w hPCv t)
  have hwc1 : σ1.vars "wc" = w := hfv1 "wc" (by decide)
  have hW1 : σ1.vars "W" = W0 := by rw [hfv1 "W" (by decide), hWv]
  have hans1 : σ1.vars "ans" = σ.vars "ans" := hfv1 "ans" (by decide)
  have hsn11 : σ1.vars "sn1" = n + 1 := by rw [hfv1 "sn1" (by decide), hsn1]
  have hPCσ1 : σ1.arrs "PC" = σ.arrs "PC" := hfa1 "PC" (by decide)
  have hnB := hd.nB
  have hcc0 : (σ1.arrs "CC").getD 0 0 = CA n inf NX PS QS DS (w + 1) 0 := hCA1 0 (by omega)
  obtain ⟨σ2, hr2, hans2, hfv2, harr2, hinp2, hout2⟩ :=
    (ansCheck_spec (B := B) hd.two (σ1.arrs "CC") w W0 (σ.vars "ans") (by omega)
      (by rw [hcc0]; have := hcle (w + 1) 0; have := hd.infB; omega) (by omega) hW).run
      (σ := σ1) ⟨rfl, hwc1, hW1, hans1⟩
  have hCC2 : σ2.arrs "CC" = σ1.arrs "CC" := by rw [harr2]
  have hS : ∀ v ∈ σ1.arrs "CC", v < B := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
    have htn : t ≤ n := by omega
    have := hCA1 t htn
    rw [List.getD_eq_getElem _ _ ht] at this
    have := hcle (w + 1) t
    have := hd.infB
    omega
  obtain ⟨σ3, hr3, ⟨hPC3, hCC3, hsn13⟩, hfv3, hfa3, -, -⟩ :=
    (copyCol_spec hB1 (σ1.arrs "CC") (by omega) hS).frame.run (σ := σ2)
      ⟨hCC2, by rw [harr2, hPCσ1, hPCl, hCC1l], by rw [hfv2 "sn1" (by decide) (by decide) (by decide), hsn11, hCC1l]⟩
  have hl1 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit hB1
  have hwc3 : σ3.vars "wc" = w := by
    rw [hfv3 "wc" (by decide), hfv2 "wc" (by decide) (by decide) (by decide), hwc1]
  have hvw : (V "wc").evalB B σ3 = some w := hwc3 ▸ evalB_var (B := B) (σ := σ3) (x := "wc")
    (by rw [hwc3]; omega)
  have rd := Run.assign (B := B) (σ := σ3) (x := "wc") (e := .bin .add (V "wc") (.lit 1))
    (v := w + 1) (evalB_bin hvw hl1 (by show w + 1 < B; omega))
  set σ4 : Env := σ3.setVar "wc" (w + 1) with hσ4
  refine ⟨σ4, _, (hr1.seq (hr2.seq (hr3.seq rd))).mono ?_, le_rfl, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · have hv : ∀ y, y ∉ colCol.wvars → y ≠ "c0" → y ≠ "cwp" → y ≠ "ans" →
        y ∉ copyCol.wvars → y ≠ "wc" → σ4.vars y = σ.vars y := fun y h1 h2 h3 h4 h5 h6 => by
      simp only [hσ4, vars_setVar, if_neg h6]
      rw [hfv3 y h5, hfv2 y h2 h3 h4, hfv1 y h1]
    have ha : ∀ a, a ∉ colCol.warrs → a ≠ "PC" → σ4.arrs a = σ.arrs a := fun a h1 h2 => by
      simp only [hσ4, arrs_setVar]
      rw [hfa3 a (by intro h; exact h2 (by simpa [copyCol, Com.warrs] using h)), harr2, hfa1 a h1]
    have hPCσ4 : σ4.arrs "PC" = σ1.arrs "CC" := by simp [hσ4, hPC3]
    have hwc4 : σ4.vars "wc" = w + 1 := by simp [hσ4]
    refine ⟨by rw [ha "NX" (by decide) (by decide)]; exact hNX,
      by rw [ha "PS" (by decide) (by decide)]; exact hPS,
      by rw [ha "QS" (by decide) (by decide)]; exact hQS,
      by rw [ha "DS" (by decide) (by decide)]; exact hDS,
      by rw [hv "sn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsn,
      by simp only [hσ4, vars_setVar]; simp [hsn13, hCC1l],
      by rw [hv "cinf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinf,
      by rw [hv "W" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hWv,
      by simp [hσ4, hCC3, hCC1l],
      by rw [hPCσ4, hCC1l],
      by rw [hwc4]; omega,
      fun t ht => by rw [hPCσ4, hwc4]; exact hCA1 t ht,
      ?_, ?_⟩
    · have hA4 : σ4.vars "ans" = (if ¬ (w + 1 < W0) ∧ (σ1.arrs "CC").getD 0 0 ≠ 0 then 1 else σ.vars "ans") := by
        simp only [hσ4, vars_setVar]
        rw [if_neg (by decide), hfv3 "ans" (by decide), hans2]
      rw [hA4]
      split_ifs
      · exact Or.inl rfl
      · exact hans
    · have hA4 : σ4.vars "ans" = (if ¬ (w + 1 < W0) ∧ (σ1.arrs "CC").getD 0 0 ≠ 0 then 1 else σ.vars "ans") := by
        simp only [hσ4, vars_setVar]
        rw [if_neg (by decide), hfv3 "ans" (by decide), hans2]
      rw [hA4, hwc4, hcc0]
      by_cases hc : ¬ (w + 1 < W0) ∧ CA n inf NX PS QS DS (w + 1) 0 ≠ 0
      · rw [if_pos hc]
        exact ⟨fun _ => ⟨w + 1, by omega, le_rfl, hc.2⟩, fun _ => rfl⟩
      · rw [if_neg hc]
        constructor
        · intro h1
          obtain ⟨W'', h2, h3, h4⟩ := hansiff.mp h1
          exact ⟨W'', h2, by omega, h4⟩
        · rintro ⟨W'', h2, h3, h4⟩
          apply hansiff.mpr
          rcases Nat.lt_or_ge W'' (w + 1) with hlt' | hge'
          · exact ⟨W'', h2, by omega, h4⟩
          · exfalso
            have : W'' = w + 1 := by omega
            subst this
            exact hc ⟨by omega, h4⟩
  · simp [hσ4]

/-- All the columns. -/
def colsLoop : Com := .seq (.assign "wc" (.lit 0)) (.while (.lt (V "wc") (V "sn")) colsBody)

/-- The cost of the loop over columns. -/
def colsCost (n : ℕ) : ℕ :=
  ((2 + (1 + 1) + ((160 + 4) * n + 6) + 30 + ((20 + 4) * (n + 1) + 6) + 4) + 4) * n + 6

theorem colsLoop_spec {B inf n W0 : ℕ} {NX PS QS DS PC0 : List ℕ}
    (hd : Dat B inf n NX PS QS DS PC0) (hW : W0 < B) (hinf1 : 1 < inf) :
    Spec B (fun σ => σ.arrs "NX" = NX ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧ σ.arrs "DS" = DS ∧
        σ.vars "sn" = n ∧ σ.vars "sn1" = n + 1 ∧ σ.vars "cinf" = inf ∧ σ.vars "W" = W0 ∧
        (σ.arrs "CC").length = n + 1 ∧ σ.arrs "PC" = List.replicate (n + 1) inf ∧
        (σ.vars "ans" = 1 ∨ σ.vars "ans" = 0) ∧ (σ.vars "ans" = 1 ↔ W0 = 0)) colsLoop
      (fun _ σ' => σ'.vars "wc" = n ∧ (σ'.vars "ans" = 1 ∨ σ'.vars "ans" = 0) ∧
        (σ'.vars "ans" = 1 ↔ ∃ W'', W0 ≤ W'' ∧ W'' ≤ n ∧ CA n inf NX PS QS DS W'' 0 ≠ 0))
      (colsCost n) := by
  have hloop := Spec.forRangeZero (B := B) (c := colsBody) "wc" "sn"
    (OJ inf n W0 NX PS QS DS) n
    (2 + (1 + 1) + ((160 + 4) * n + 6) + 30 + ((20 + 4) * (n + 1) + 6) + 4)
    (by have := hd.nB; omega) (fun σ h => h.2.2.2.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.1)
    (colsBody_spec hd hW)
  refine (hloop.conseq ?_ ?_ (by unfold colsCost; omega))
  · rintro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
      by simpa using h5, by simpa using h6, by simpa using h7, by simpa using h8,
      by simpa using h9, by simp [h10], by simp,
      fun t ht => ?_, by simpa using h11, ?_⟩
    · simp only [arrs_setVar, vars_setVar, if_true, h10, CA, colAll]
      rw [List.getD_replicate _ (by omega)]
    · simp only [vars_setVar, if_true]
      rw [show (∃ W'' : ℕ, W0 ≤ W'' ∧ W'' ≤ 0 ∧ CA n inf NX PS QS DS W'' 0 ≠ 0) ↔ W0 = 0 from ?_]
      · simpa using h12
      · constructor
        · rintro ⟨W'', h1', h2', -⟩; omega
        · intro h; exact ⟨0, by omega, le_rfl, by simp [CA, colAll]; omega⟩
  · rintro σ σ' - ⟨hOJ, hwc⟩
    exact ⟨hwc, hOJ.2.2.2.2.2.2.2.2.2.2.2.2.1,
      by have := hOJ.2.2.2.2.2.2.2.2.2.2.2.2.2; rw [hwc] at this; exact this⟩

end Lax496464Proofs.Ram.Cols1
