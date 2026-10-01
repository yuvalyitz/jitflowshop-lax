import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS

/-! # Phase 7: the blocks of the binary symbols `E_l`

For each `l < r`: count the tuples of arity above `l` (`eCountC`), write the count, then walk the
blocks again and write, for each such tuple, its entry `l` and its new element (`eEmitC`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutE

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-- The number of tuples of arity above `l` among the symbols below `k`. -/
def ecntP (x : List ℕ) (l k : ℕ) : ℕ :=
  ((List.range k).map fun i => if l < arOf x i then cntOf x i else 0).sum

/-- The entries of the block of `E_l` from symbol `i`. -/
def ef (x : List ℕ) (l i : ℕ) : List ℕ :=
  if l < arOf x i then (List.range (cntOf x i)).flatMap fun j => [entOf x i j l, nOf x + poOf x i + j]
  else []

/-- The entries of the block of `E_l` from the symbols below `k`. -/
def eL (x : List ℕ) (l k : ℕ) : List ℕ := (List.range k).flatMap (ef x l)

theorem ecntP_succ (x : List ℕ) (l k : ℕ) :
    ecntP x l (k + 1) = ecntP x l k + if l < arOf x k then cntOf x k else 0 := by
  simp [ecntP, List.range_succ]

theorem eL_succ (x : List ℕ) (l k : ℕ) : eL x l (k + 1) = eL x l k ++ ef x l k := by
  simp [eL, List.range_succ]

theorem ecntP_le (x : List ℕ) (l : ℕ) : ∀ k, ecntP x l k ≤ poOf x k
  | 0 => le_rfl
  | k + 1 => by
    rw [ecntP_succ, poOf_succ]
    have := ecntP_le x l k
    split_ifs <;> omega

/-! ### Counting -/

/-- The invariant of the count. -/
def ECI (x : List ℕ) (l : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_l" = l ∧ σ.vars "ic_i" ≤ sOf x ∧
    σ.vars "ic_b2" = bo x (σ.vars "ic_i") ∧ σ.vars "ic_e" = ecntP x l (σ.vars "ic_i")

set_option maxHeartbeats 2000000 in
theorem ecBody_spec (hd : Dom x φ) (hB : BOK x B) (l : ℕ) (hl : l < x.length) :
    Spec B (fun σ => ECI x l σ ∧ σ.vars "ic_i" < sOf x) ecBody
      (fun σ σ' => ECI x l σ' ∧ σ'.vars "ic_i" = σ.vars "ic_i" + 1) 40 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h3 := hz.t_le
  unfold ecBody
  refine Spec.pre (P := fun σ => ECI x l σ ∧ σ.vars "ic_i" < sOf x ∧
      σ.vars "ic_b2" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_b2") 0 = cntOf x (σ.vars "ic_i") ∧
      1 + σ.vars "ic_i" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (1 + σ.vars "ic_i") 0 = arOf x (σ.vars "ic_i") ∧
      cntOf x (σ.vars "ic_i") < B ∧ arOf x (σ.vars "ic_i") < B ∧ l < B ∧
      ecntP x l (σ.vars "ic_i") + cntOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b2" + 1 < B ∧ cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b2" + 1 + cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      1 + σ.vars "ic_i" < B ∧ σ.vars "ic_i" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [ECI] at *; simp_all [Env.setVar, bo_succ, ecntP_succ]; try omega)
  · rintro σ ⟨⟨ha, hs, hl', hi, hbo, he⟩, hlt⟩
    have hh1 := bo_lt hd (i := σ.vars "ic_i") (by omega)
    have hh2 := bo_succ_le hd (i := σ.vars "ic_i") (by omega)
    rw [bo_succ] at hh2
    have hpm : poOf x (σ.vars "ic_i" + 1) ≤ poOf x (sOf x) :=
      (dataOf x 0).po_mono (show σ.vars "ic_i" + 1 ≤ sOf x by omega)
    rw [poOf_succ] at hpm
    have hep := ecntP_le x l (σ.vars "ic_i")
    unfold tOf at h3
    refine ⟨⟨ha, hs, hl', hi, hbo, he⟩, hlt, ?_, ?_, ?_, ?_, getD_lt hB _, getD_lt hB _, by omega,
      by omega, ?_, ?_, ?_, by omega, by omega⟩
    · rw [ha, hbo]; exact hh1
    · rw [ha, hbo]; rfl
    · rw [ha]; omega
    · rw [ha]; rfl
    · rw [hbo]; omega
    · omega
    · rw [hbo]; omega

theorem eCountC_value (hd : Dom x φ) (hB : BOK x B) (l : ℕ) (hl : l < x.length) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_l" = l) eCountC
      (fun _ σ' => σ'.vars "ic_e" = ecntP x l (sOf x)) (10 + (40 + 4) * sOf x + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le
  have hloop := Spec.forRangeZero (B := B) (c := ecBody) "ic_i" "ic_s" (ECI x l) (sOf x) 40
    (by omega) (fun σ h => h.2.2.2.1) (fun σ h => h.2.1) (ecBody_spec hd hB l hl)
  unfold eCountC
  run_vcg [hloop]
  all_goals (simp only [ECI] at *; simp_all [Env.setVar, bo_zero]; try omega)
  all_goals (simp [ecntP])

/-- The scalars `eCountC` assigns. -/
def ecVars : List String := ["ic_e", "ic_b2", "ic_i", "ic_c", "ic_w"]

theorem eCountC_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_l" < x.length) eCountC
      (fun σ σ' => σ'.vars "ic_e" = ecntP x (σ.vars "ic_l") (sOf x) ∧ Keep ecVars σ σ' ∧
        σ'.out = σ.out) (10 + (40 + 4) * sOf x + 6) := by
  intro σ hσ
  have h := Spec.keepOut (eCountC_value hd hB (σ.vars "ic_l") hσ.2.2) ecVars
    (by intro y hy; simp [eCountC, ecLoop, ecBody, bump, Com.wvars] at hy; simp [ecVars]; tauto)
    (by simp [eCountC, ecLoop, ecBody, bump, Com.warrs])
    (by simp [eCountC, ecLoop, ecBody, bump, Com.reads])
    (by simp [eCountC, ecLoop, ecBody, bump, Com.NoWrite])
  exact h σ ⟨hσ.1, hσ.2.1, rfl⟩

/-! ### Writing the pairs -/

/-- The invariant of the pairs of one symbol. -/
def PI (x : List ℕ) (l i : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "ic_b2" = bo x i ∧ σ.vars "ic_w" = arOf x i ∧ σ.vars "ic_l" = l ∧
    σ.vars "ic_N" = nOf x ∧ σ.vars "ic_g2" = poOf x i ∧ σ.vars "ic_c" = cntOf x i ∧
    σ.vars "ic_j" ≤ cntOf x i ∧
    σ.out = out0 ++ (List.range (σ.vars "ic_j")).flatMap
      fun j => [entOf x i j l, nOf x + poOf x i + j]

set_option maxHeartbeats 2000000 in
theorem pairBody_spec (hd : Dom x φ) (hB : BOK x B) {l i : ℕ} (hi : i < sOf x)
    (hl : l < arOf x i) (out0 : List ℕ) :
    Spec B (fun σ => PI x l i out0 σ ∧ σ.vars "ic_j" < cntOf x i) pairBody
      (fun σ σ' => PI x l i out0 σ' ∧ σ'.vars "ic_j" = σ.vars "ic_j" + 1) 40 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h3 := hz.t_le; have h4 := hz.n_le
  unfold pairBody
  refine Spec.pre (P := fun σ => PI x l i out0 σ ∧ σ.vars "ic_j" < cntOf x i ∧
      bo x i + 1 + σ.vars "ic_j" * arOf x i + l < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (bo x i + 1 + σ.vars "ic_j" * arOf x i + l) 0 =
        entOf x i (σ.vars "ic_j") l ∧
      entOf x i (σ.vars "ic_j") l < B ∧ bo x i + 1 + σ.vars "ic_j" * arOf x i + l < B ∧
      nOf x + poOf x i + σ.vars "ic_j" + 1 < B ∧ arOf x i < B ∧
      σ.vars "ic_j" * arOf x i < B) ?_ ?_
  · run_vcg
    all_goals (simp only [PI] at *; simp_all [Env.setVar, List.range_succ]; try omega)
  · rintro σ ⟨hP, hlt⟩
    have ha := hP.1
    have hpos := ent_pos_lt x hlt hl
    have hh2 := bo_succ_le hd hi
    have hpm : poOf x (i + 1) ≤ poOf x (sOf x) := (dataOf x 0).po_mono (by omega)
    rw [poOf_succ] at hpm
    unfold tOf at h3
    refine ⟨hP, hlt, by rw [ha]; omega, by rw [ha]; rfl, getD_lt hB _, by omega, by omega,
      getD_lt hB _, by omega⟩

theorem pairLoop_value (hd : Dom x φ) (hB : BOK x B) {l i : ℕ} (hi : i < sOf x)
    (hl : l < arOf x i) (out0 : List ℕ) :
    Spec B (fun σ => PI x l i out0 (σ.setVar "ic_j" 0)) pairLoop
      (fun _ σ' => σ'.out = out0 ++ (List.range (cntOf x i)).flatMap
        fun j => [entOf x i j l, nOf x + poOf x i + j]) ((40 + 4) * x.length + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h3 := hz.t_le
  have hpm : poOf x (i + 1) ≤ poOf x (sOf x) := (dataOf x 0).po_mono (by omega)
  rw [poOf_succ] at hpm
  unfold tOf at h3
  refine Spec.mono (Spec.post (Spec.forRangeZero "ic_j" "ic_c" (PI x l i out0) (cntOf x i) 40
    (by omega) (fun σ h => h.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.2.2.1)
    (pairBody_spec hd hB hi hl out0)) ?_) ?_
  · rintro σ σ' - ⟨hP, hj⟩
    rw [hP.2.2.2.2.2.2.2.2, hj]
  · have := Nat.mul_le_mul_left (40 + 4) (show cntOf x i ≤ x.length by omega)
    omega

/-- The pairs of the symbol in `ic_i`, relative to the state. -/
theorem pairLoop_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_i" < sOf x ∧
        σ.vars "ic_b2" = bo x (σ.vars "ic_i") ∧ σ.vars "ic_w" = arOf x (σ.vars "ic_i") ∧
        σ.vars "ic_l" < arOf x (σ.vars "ic_i") ∧ σ.vars "ic_N" = nOf x ∧
        σ.vars "ic_g2" = poOf x (σ.vars "ic_i") ∧ σ.vars "ic_c" = cntOf x (σ.vars "ic_i"))
      pairLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range (cntOf x (σ.vars "ic_i"))).flatMap
          (fun j => [entOf x (σ.vars "ic_i") j (σ.vars "ic_l"),
            nOf x + poOf x (σ.vars "ic_i") + j]) ∧ Keep ["ic_j"] σ σ')
      ((40 + 4) * x.length + 6) := by
  rintro σ ⟨ha, hi, hbo, hw, hl, hN, hg, hc⟩
  have h := Spec.keep (pairLoop_value hd hB hi hl σ.out) ["ic_j"]
    (by intro y hy; simpa [pairLoop, pairBody, bump, Com.wvars] using hy)
    (by simp [pairLoop, pairBody, bump, Com.warrs]) (by simp [pairLoop, pairBody, bump, Com.reads])
  obtain ⟨σ', hr, hq, hk⟩ := h σ (by simp [PI, Env.setVar, ha, hbo, hw, hN, hg, hc])
  exact ⟨σ', hr, hq, hk⟩

/-! ### Writing the block of `E_l` -/

/-- The invariant of the walk writing the block of `E_l`. -/
def EEI (x : List ℕ) (l : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧ σ.vars "ic_l" = l ∧
    σ.vars "ic_i" ≤ sOf x ∧ σ.vars "ic_b2" = bo x (σ.vars "ic_i") ∧
    σ.vars "ic_g2" = poOf x (σ.vars "ic_i") ∧ σ.out = out0 ++ eL x l (σ.vars "ic_i")

theorem ef_pos {x : List ℕ} {l i : ℕ} (h : l < arOf x i) :
    ef x l i = (List.range (cntOf x i)).flatMap fun j => [entOf x i j l, nOf x + poOf x i + j] :=
  if_pos h

theorem ef_neg {x : List ℕ} {l i : ℕ} (h : ¬ l < arOf x i) : ef x l i = [] := if_neg h

/-- The cost of one turn of the walk. -/
def Kee (x : List ℕ) : ℕ := (40 + 4) * x.length + 100

set_option maxHeartbeats 4000000 in
theorem eeBody_spec (hd : Dom x φ) (hB : BOK x B) (l : ℕ) (hl : l < x.length) (out0 : List ℕ) :
    Spec B (fun σ => EEI x l out0 σ ∧ σ.vars "ic_i" < sOf x) eeBody
      (fun σ σ' => EEI x l out0 σ' ∧ σ'.vars "ic_i" = σ.vars "ic_i" + 1) (Kee x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h3 := hz.t_le; have h4 := hz.n_le
  unfold eeBody Kee
  refine Spec.pre (P := fun σ => EEI x l out0 σ ∧ σ.vars "ic_i" < sOf x ∧
      σ.vars "ic_b2" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_b2") 0 = cntOf x (σ.vars "ic_i") ∧
      1 + σ.vars "ic_i" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (1 + σ.vars "ic_i") 0 = arOf x (σ.vars "ic_i") ∧
      cntOf x (σ.vars "ic_i") < B ∧ arOf x (σ.vars "ic_i") < B ∧ l < B ∧
      poOf x (σ.vars "ic_i") + cntOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b2" + 1 < B ∧ cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b2" + 1 + cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      1 + σ.vars "ic_i" < B ∧ σ.vars "ic_i" + 1 < B) ?_ ?_
  · run_vcg [pairLoop_spec hd hB]
    all_goals (simp only [EEI, Keep] at *; simp_all [Env.setVar, bo_succ, poOf_succ, eL_succ, ef_pos, ef_neg]; try omega)
  · rintro σ ⟨⟨ha, hs, hN, hl', hi, hbo, hg, ho⟩, hlt⟩
    have hh1 := bo_lt hd (i := σ.vars "ic_i") (by omega)
    have hh2 := bo_succ_le hd (i := σ.vars "ic_i") (by omega)
    rw [bo_succ] at hh2
    have hpm : poOf x (σ.vars "ic_i" + 1) ≤ poOf x (sOf x) :=
      (dataOf x 0).po_mono (show σ.vars "ic_i" + 1 ≤ sOf x by omega)
    rw [poOf_succ] at hpm
    unfold tOf at h3
    refine ⟨⟨ha, hs, hN, hl', hi, hbo, hg, ho⟩, hlt, ?_, ?_, ?_, ?_, getD_lt hB _, getD_lt hB _,
      by omega, by omega, ?_, ?_, ?_, by omega, by omega⟩
    · rw [ha, hbo]; exact hh1
    · rw [ha, hbo]; rfl
    · rw [ha]; omega
    · rw [ha]; rfl
    · rw [hbo]; omega
    · omega
    · rw [hbo]; omega

/-- The cost of `eEmitC`. -/
def Kemit (x : List ℕ) : ℕ := 10 + (Kee x + 4) * sOf x + 6

theorem eEmitC_value (hd : Dom x φ) (hB : BOK x B) (l : ℕ) (hl : l < x.length)
    (out0 : List ℕ) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧
        σ.vars "ic_l" = l ∧ σ.out = out0) eEmitC
      (fun _ σ' => σ'.out = out0 ++ eL x l (sOf x)) (Kemit x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le
  have hloop := Spec.forRangeZero (B := B) (c := eeBody) "ic_i" "ic_s" (EEI x l out0) (sOf x)
    (Kee x) (by omega) (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.1) (eeBody_spec hd hB l hl out0)
  unfold eEmitC Kemit
  run_vcg [hloop]
  all_goals (simp only [EEI] at *; simp_all [Env.setVar, bo_zero]; try omega)
  all_goals (simp [eL, poOf])

/-- The scalars `eEmitC` assigns. -/
def eeVars : List String := ["ic_g2", "ic_b2", "ic_i", "ic_c", "ic_w", "ic_j"]

theorem eEmitC_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧
        σ.vars "ic_l" < x.length) eEmitC
      (fun σ σ' => σ'.out = σ.out ++ eL x (σ.vars "ic_l") (sOf x) ∧ Keep eeVars σ σ')
      (Kemit x) := by
  intro σ hσ
  have h := Spec.keep (eEmitC_value hd hB (σ.vars "ic_l") hσ.2.2.2 σ.out) eeVars
    (by intro y hy; simp [eEmitC, eeLoop, eeBody, pairLoop, pairBody, bump, Com.wvars] at hy
        simp [eeVars]; tauto)
    (by simp [eEmitC, eeLoop, eeBody, pairLoop, pairBody, bump, Com.warrs])
    (by simp [eEmitC, eeLoop, eeBody, pairLoop, pairBody, bump, Com.reads])
  exact h σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, rfl, rfl⟩

/-! ### All the blocks of the `E_l` -/

/-- What `eOut` writes. -/
def eAll (x : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun l => ecntP x l (sOf x) :: eL x l (sOf x)

theorem eAll_succ (x : List ℕ) (k : ℕ) :
    eAll x (k + 1) = eAll x k ++ (ecntP x k (sOf x) :: eL x k (sOf x)) := by
  simp [eAll, List.range_succ]

/-- The invariant of `eOut`. -/
def EO (x : List ℕ) (φ : Formula) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x φ σ ∧ σ.vars "ic_l" ≤ rOf φ ∧ σ.out = out0 ++ eAll x (σ.vars "ic_l")

/-- The cost of one turn of `eOut`. -/
def KeB (x : List ℕ) : ℕ := (10 + (40 + 4) * sOf x + 6) + 2 + Kemit x + 4

set_option maxHeartbeats 4000000 in
theorem eBody_spec (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => EO x φ out0 σ ∧ σ.vars "ic_l" < rOf φ) eBody
      (fun σ σ' => EO x φ out0 σ' ∧ σ'.vars "ic_l" = σ.vars "ic_l" + 1) (KeB x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h2 := hz.r_le; have h3 := hz.t_le
  unfold eBody KeB
  refine Spec.pre (P := fun σ => EO x φ out0 σ ∧ σ.vars "ic_l" < rOf φ ∧
    ecntP x (σ.vars "ic_l") (sOf x) < B ∧ σ.vars "ic_l" + 1 < B) ?_ ?_
  · run_vcg [eCountC_spec hd hB, eEmitC_spec hd hB]
    all_goals (simp only [EO, Ctx, Keep, ecVars, eeVars] at *; simp_all [Env.setVar, eAll_succ]; try omega)
  · rintro σ ⟨hE, hlt⟩
    have := ecntP_le x (σ.vars "ic_l") (sOf x)
    unfold tOf at h3
    exact ⟨hE, hlt, by omega, by omega⟩

/-- The cost of `eOut`. -/
def Ke (x : List ℕ) (φ : Formula) : ℕ := (KeB x + 4) * rOf φ + 6

theorem eOut_value (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x φ σ ∧ σ.out = out0) eOut
      (fun _ σ' => σ'.out = out0 ++ eAll x (rOf φ)) (Ke x φ) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h2 := hz.r_le
  refine Spec.post (Spec.pre (Spec.forRangeZero "ic_l" "ic_r" (EO x φ out0) (rOf φ) (KeB x)
    (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2.2.2.2.2.2.2.2) (eBody_spec hd hB out0)) ?_) ?_
  · rintro σ ⟨hc, ho⟩
    simp only [EO, Ctx, Env.setVar] at hc ⊢
    simp_all [eAll]
  · rintro σ σ' - ⟨⟨-, -, ho⟩, hl⟩
    rw [ho, hl]

theorem eOut_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) eOut
      (fun σ σ' => σ'.out = σ.out ++ eAll x (rOf φ) ∧ Keep ("ic_l" :: ecVars ++ eeVars) σ σ')
      (Ke x φ) := by
  intro σ hσ
  have h := Spec.keep (eOut_value hd hB σ.out) ("ic_l" :: ecVars ++ eeVars)
    (by intro y hy
        simp [eOut, eBody, eCountC, ecLoop, ecBody, eEmitC, eeLoop, eeBody, pairLoop, pairBody,
          bump, Com.wvars] at hy
        simp [ecVars, eeVars]; tauto)
    (by simp [eOut, eBody, eCountC, ecLoop, ecBody, eEmitC, eeLoop, eeBody, pairLoop, pairBody,
          bump, Com.warrs])
    (by simp [eOut, eBody, eCountC, ecLoop, ecBody, eEmitC, eeLoop, eeBody, pairLoop, pairBody,
          bump, Com.reads])
  exact h σ ⟨hσ, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutE
