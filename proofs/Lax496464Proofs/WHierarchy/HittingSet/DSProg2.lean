import Lax496464Proofs.WHierarchy.HittingSet.DSProg1

/-! # Hitting Set to Dominating Set: the program, part 2

The two passes writing the neighbour lists: for each element `u`, the other elements and then the
sets `NN + hs_own[p]` of the positions with `fp_f[p] = u` (`tgtELoop`); for each set `j`, the
first occurrences `fp_f[p]` of its positions (`tgtSLoop`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSProg2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V bump)

theorem filter_snoc (f : ℕ → Bool) (p : ℕ) :
    (List.range (p + 1)).filter f = (List.range p).filter f ++ (if f p then [p] else []) := by
  rw [List.range_succ, List.filter_append]
  cases h : f p <;> simp [h]

theorem getD_mem_of_lt {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-! ## The other elements -/

def vBody : Com := .seq (.ite (.eq (V "ds_v") (V "ds_u")) .skip (.write (V "ds_v"))) (bump "ds_v")
def vLoop : Com := .seq (.assign "ds_v" (.lit 0)) (.while (.lt (V "ds_v") (V "fp_NN")) vBody)

def VI (NN u : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "fp_NN" = NN ∧ σ.vars "ds_u" = u ∧ σ.vars "ds_v" ≤ NN ∧
    σ.out = out0 ++ (List.range (σ.vars "ds_v")).filter fun v => v ≠ u

theorem vBody_spec {B : ℕ} (NN u : ℕ) (out0 : List ℕ) (hB : NN + 1 < B) (hu : u < B) :
    Spec B (fun σ => VI NN u out0 σ ∧ σ.vars "ds_v" < NN) vBody
      (fun σ σ' => VI NN u out0 σ' ∧ σ'.vars "ds_v" = σ.vars "ds_v" + 1) 14 := by
  refine Spec.pre (P := fun σ => VI NN u out0 σ ∧ σ.vars "ds_v" < NN ∧ σ.vars "ds_v" + 1 < B ∧
    1 < B ∧ σ.vars "ds_u" < B) ?_
    (fun σ ⟨h1, h2⟩ => ⟨h1, h2, by omega, by omega, by rw [h1.2.1]; exact hu⟩)
  run_vcg
  all_goals
    obtain ⟨h1, h2, h3, h4⟩ := ‹VI NN u out0 σ›
  · have hc := ‹σ.vars "ds_v" = σ.vars "ds_u"›
    refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega,
      ?_⟩, by simp [Env.setVar]⟩
    simp only [Env.setVar, if_true]
    try simp only [↓reduceIte]
    rw [filter_snoc, h4]
    simp [hc, h2]
  · have hc := ‹¬σ.vars "ds_v" = σ.vars "ds_u"›
    refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega,
      ?_⟩, by simp [Env.setVar]⟩
    simp only [Env.setVar, if_true]
    try simp only [↓reduceIte]
    rw [filter_snoc, h4]
    rw [h2] at hc
    simp [hc]

theorem vLoop_spec {B : ℕ} (NN : ℕ) (hB : NN + 1 < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN ∧ σ.vars "ds_u" < B) vLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range NN).filter (fun v => v ≠ σ.vars "ds_u") ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_v" → σ'.vars y = σ.vars y) (18 * NN + 6) := by
  intro σ ⟨h1, hu⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, ho⟩, hv'⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_v" "fp_NN" (VI NN (σ.vars "ds_u") σ.out) NN 14 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1)
      (vBody_spec NN _ σ.out hB hu)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar], by simp [Env.setVar],
        by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hv'], ?_, hi (by simp [vBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [vBody, Com.warrs])
  · intro y hy; exact hv y (by simp [vBody, Com.wvars, hy])

/-! ## The sets of an element -/

def pBody : Com :=
  .seq (.ite (.eq (.get "fp_f" (V "ds_p")) (V "ds_u"))
      (.write (.add (V "fp_NN") (.get "hs_own" (V "ds_p")))) .skip) (bump "ds_p")
def pLoop : Com := .seq (.assign "ds_p" (.lit 0)) (.while (.lt (V "ds_p") (V "hs_t")) pBody)

/-- The sets of element `u`, as vertices. -/
def setsOfL (F O : List ℕ) (NN T u : ℕ) : List ℕ :=
  ((List.range T).filter fun p => F.getD p 0 = u).map fun p => NN + O.getD p 0

def PI (F O : List ℕ) (NN T u : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "fp_NN" = NN ∧ σ.vars "hs_t" = T ∧
    σ.vars "ds_u" = u ∧ σ.vars "ds_p" ≤ T ∧ σ.out = out0 ++ setsOfL F O NN (σ.vars "ds_p") u

theorem pBody_spec {B : ℕ} (F O : List ℕ) (NN T u : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B) (hB : T + NN + 1 < B)
    (hu : u < B) :
    Spec B (fun σ => PI F O NN T u out0 σ ∧ σ.vars "ds_p" < T) pBody
      (fun σ σ' => PI F O NN T u out0 σ' ∧ σ'.vars "ds_p" = σ.vars "ds_p" + 1) 20 := by
  refine Spec.pre (P := fun σ => PI F O NN T u out0 σ ∧ σ.vars "ds_p" < T ∧
    σ.vars "ds_p" + 1 < B ∧ 1 < B ∧ σ.vars "ds_u" < B ∧ σ.vars "fp_NN" < B ∧
    σ.vars "ds_p" < (σ.arrs "fp_f").length ∧ σ.vars "ds_p" < (σ.arrs "hs_own").length ∧
    (σ.arrs "fp_f").getD (σ.vars "ds_p") 0 < B ∧ (σ.arrs "hs_own").getD (σ.vars "ds_p") 0 < B ∧
    σ.vars "fp_NN" + (σ.arrs "hs_own").getD (σ.vars "ds_p") 0 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ‹PI F O NN T u out0 σ›
    · have hc := ‹(σ.arrs "fp_f").getD (σ.vars "ds_p") 0 = σ.vars "ds_u"›
      rw [h1, h5] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar, h5], by simp [Env.setVar]; omega, ?_⟩,
        by simp [Env.setVar]⟩
      simp only [Env.setVar, if_true]
      try simp only [↓reduceIte]
      rw [h7, setsOfL, setsOfL, filter_snoc, decide_eq_true hc]
      simp [h3, h2]
    · have hc := ‹¬(σ.arrs "fp_f").getD (σ.vars "ds_p") 0 = σ.vars "ds_u"›
      rw [h1, h5] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar, h5], by simp [Env.setVar]; omega, ?_⟩,
        by simp [Env.setVar]⟩
      simp only [Env.setVar, if_true]
      try simp only [↓reduceIte]
      rw [h7, setsOfL, setsOfL, filter_snoc, decide_eq_false hc]
      simp
  · rintro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hlt⟩
    have hv1 := hFB _ (getD_mem_of_lt (l := F) (i := σ.vars "ds_p") (by omega))
    have hv2 := hOB _ (getD_mem_of_lt (l := O) (i := σ.vars "ds_p") (by omega))
    refine ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hlt, by omega, by omega, by omega, by omega,
      by rw [h1]; omega, by rw [h2]; omega, by rw [h1]; exact hv1, by rw [h2]; omega,
      by rw [h3, h2]; exact hv2⟩

theorem pLoop_spec {B : ℕ} (F O : List ℕ) (NN T : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B) (hB : T + NN + 1 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "fp_NN" = NN ∧
        σ.vars "hs_t" = T ∧ σ.vars "ds_u" < B) pLoop
      (fun σ σ' => σ'.out = σ.out ++ setsOfL F O NN T (σ.vars "ds_u") ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_p" → σ'.vars y = σ.vars y) (24 * T + 6) := by
  intro σ ⟨h1, h2, h3, h4, hu⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, -, -, ho⟩, hp⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_p" "hs_t" (PI F O NN T (σ.vars "ds_u") σ.out) T 20
      (by omega) (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.1)
      (pBody_spec F O NN T _ σ.out hF hO hFB hOB hB hu)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar], by simp [Env.setVar],
        by simp [Env.setVar, setsOfL]⟩
  refine ⟨σ', r, by rw [ho, hp], ?_, hi (by simp [pBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [pBody, Com.warrs])
  · intro y hy; exact hv y (by simp [pBody, Com.wvars, hy])

/-! ## The neighbour lists of the elements -/

def tgtEBody : Com := .seq vLoop (.seq pLoop (bump "ds_u"))
def tgtELoop : Com := .seq (.assign "ds_u" (.lit 0)) (.while (.lt (V "ds_u") (V "fp_NN")) tgtEBody)

/-- The neighbour list of element `u`. -/
def eBlkL (F O : List ℕ) (NN T u : ℕ) : List ℕ :=
  (List.range NN).filter (fun v => v ≠ u) ++ setsOfL F O NN T u

def TEI (F O : List ℕ) (NN T : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "fp_NN" = NN ∧ σ.vars "hs_t" = T ∧
    σ.vars "ds_u" ≤ NN ∧ σ.out = out0 ++ (List.range (σ.vars "ds_u")).flatMap (eBlkL F O NN T)

theorem tgtEBody_spec {B : ℕ} (F O : List ℕ) (NN T : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B)
    (hB : T + NN + 1 < B) :
    Spec B (fun σ => TEI F O NN T out0 σ ∧ σ.vars "ds_u" < NN) tgtEBody
      (fun σ σ' => TEI F O NN T out0 σ' ∧ σ'.vars "ds_u" = σ.vars "ds_u" + 1)
      (18 * NN + 24 * T + 20) := by
  intro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
  obtain ⟨σ1, r1, ho1, ha1, -, hv1⟩ := (vLoop_spec (B := B) NN (by omega)).run (σ := σ)
    ⟨h3, by omega⟩
  have e1 : ∀ y, y ≠ "ds_v" → σ1.vars y = σ.vars y := hv1
  obtain ⟨σ2, r2, ho2, ha2, -, hv2⟩ :=
    (pLoop_spec (B := B) F O NN T hF hO hFB hOB hB).run (σ := σ1)
      ⟨by rw [ha1, h1], by rw [ha1, h2], by rw [e1 _ (by decide), h3],
        by rw [e1 _ (by decide), h4], by rw [e1 _ (by decide)]; omega⟩
  have e2 : ∀ y, y ≠ "ds_v" → y ≠ "ds_p" → σ2.vars y = σ.vars y := by
    intro y h h'; rw [hv2 y h', e1 y h]
  have hu2 : σ2.vars "ds_u" = σ.vars "ds_u" := e2 _ (by decide) (by decide)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "ds_u") (e := .add (V "ds_u") (.lit 1))
    (v := σ.vars "ds_u" + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "ds_u") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [hu2]; simp; omega)
      rw [hu2] at this; simpa using this)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [Env.setVar]⟩
  · simp [Env.setVar, ha2, ha1, h1]
  · simp [Env.setVar, ha2, ha1, h2]
  · simp [Env.setVar]; rw [e2 _ (by decide) (by decide), h3]
  · simp [Env.setVar]; rw [e2 _ (by decide) (by decide), h4]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar, if_true]
    try simp only [↓reduceIte]
    rw [ho2, ho1, h6, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      e1 _ (by decide), eBlkL, List.append_assoc, List.append_assoc]

theorem tgtELoop_spec {B : ℕ} (F O : List ℕ) (NN T : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B)
    (hB : T + NN + 1 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "fp_NN" = NN ∧
        σ.vars "hs_t" = T) tgtELoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range NN).flatMap (eBlkL F O NN T) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_u" → y ≠ "ds_v" → y ≠ "ds_p" → σ'.vars y = σ.vars y)
      ((18 * NN + 24 * T + 24) * NN + 6) := by
  intro σ ⟨h1, h2, h3, h4⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, -, ho⟩, hu⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_u" "fp_NN" (TEI F O NN T σ.out) NN (18 * NN + 24 * T + 20)
      (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.1)
      (tgtEBody_spec F O NN T σ.out hF hO hFB hOB hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hu], ?_, hi (by simp [tgtEBody, vLoop, vBody, pLoop, pBody, Com.reads]),
    ?_⟩
  · funext a; exact ha a (by simp [tgtEBody, vLoop, vBody, pLoop, pBody, Com.warrs])
  · intro y hy1 hy2 hy3
    exact hv y (by simp [tgtEBody, vLoop, vBody, pLoop, pBody, Com.wvars, hy1, hy2, hy3])

/-! ## The neighbour lists of the sets -/

def sBody : Com :=
  .seq (.ite (.eq (.get "hs_own" (V "ds_p")) (V "ds_j")) (.write (.get "fp_f" (V "ds_p"))) .skip)
    (bump "ds_p")
def sLoop : Com := .seq (.assign "ds_p" (.lit 0)) (.while (.lt (V "ds_p") (V "hs_t")) sBody)

/-- The neighbour list of set `j`. -/
def sBlkL (F O : List ℕ) (T j : ℕ) : List ℕ :=
  ((List.range T).filter fun p => O.getD p 0 = j).map fun p => F.getD p 0

def SI (F O : List ℕ) (T j : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "hs_t" = T ∧ σ.vars "ds_j" = j ∧
    σ.vars "ds_p" ≤ T ∧ σ.out = out0 ++ sBlkL F O (σ.vars "ds_p") j

theorem sBody_spec {B : ℕ} (F O : List ℕ) (T j : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, v < B) (hB : T + 1 < B)
    (hj : j < B) :
    Spec B (fun σ => SI F O T j out0 σ ∧ σ.vars "ds_p" < T) sBody
      (fun σ σ' => SI F O T j out0 σ' ∧ σ'.vars "ds_p" = σ.vars "ds_p" + 1) 20 := by
  refine Spec.pre (P := fun σ => SI F O T j out0 σ ∧ σ.vars "ds_p" < T ∧
    σ.vars "ds_p" + 1 < B ∧ 1 < B ∧ σ.vars "ds_j" < B ∧
    σ.vars "ds_p" < (σ.arrs "fp_f").length ∧ σ.vars "ds_p" < (σ.arrs "hs_own").length ∧
    (σ.arrs "fp_f").getD (σ.vars "ds_p") 0 < B ∧ (σ.arrs "hs_own").getD (σ.vars "ds_p") 0 < B)
    ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ‹SI F O T j out0 σ›
    · have hc := ‹(σ.arrs "hs_own").getD (σ.vars "ds_p") 0 = σ.vars "ds_j"›
      rw [h2, h4] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, if_true]
      try simp only [↓reduceIte]
      rw [h6, sBlkL, sBlkL, filter_snoc, decide_eq_true hc]
      simp [h1]
    · have hc := ‹¬(σ.arrs "hs_own").getD (σ.vars "ds_p") 0 = σ.vars "ds_j"›
      rw [h2, h4] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, if_true]
      try simp only [↓reduceIte]
      rw [h6, sBlkL, sBlkL, filter_snoc, decide_eq_false hc]
      simp
  · rintro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
    have hv1 := hFB _ (getD_mem_of_lt (l := F) (i := σ.vars "ds_p") (by omega))
    have hv2 := hOB _ (getD_mem_of_lt (l := O) (i := σ.vars "ds_p") (by omega))
    refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt, by omega, by omega, by omega,
      by rw [h1]; omega, by rw [h2]; omega, by rw [h1]; exact hv1, by rw [h2]; exact hv2⟩

theorem sLoop_spec {B : ℕ} (F O : List ℕ) (T : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, v < B) (hB : T + 1 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "hs_t" = T ∧
        σ.vars "ds_j" < B) sLoop
      (fun σ σ' => σ'.out = σ.out ++ sBlkL F O T (σ.vars "ds_j") ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_p" → σ'.vars y = σ.vars y) (24 * T + 6) := by
  intro σ ⟨h1, h2, h3, hj⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, -, ho⟩, hp⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_p" "hs_t" (SI F O T (σ.vars "ds_j") σ.out) T 20
      (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.1)
      (sBody_spec F O T _ σ.out hF hO hFB hOB hB hj)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar, sBlkL]⟩
  refine ⟨σ', r, by rw [ho, hp], ?_, hi (by simp [sBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [sBody, Com.warrs])
  · intro y hy; exact hv y (by simp [sBody, Com.wvars, hy])

def tgtSBody : Com := .seq sLoop (bump "ds_j")
def tgtSLoop : Com := .seq (.assign "ds_j" (.lit 0)) (.while (.lt (V "ds_j") (V "hs_m")) tgtSBody)

def TSI (F O : List ℕ) (T m : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "hs_t" = T ∧ σ.vars "hs_m" = m ∧
    σ.vars "ds_j" ≤ m ∧ σ.out = out0 ++ (List.range (σ.vars "ds_j")).flatMap (sBlkL F O T)

theorem tgtSBody_spec {B : ℕ} (F O : List ℕ) (T m : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, v < B) (hB : T + m + 1 < B) :
    Spec B (fun σ => TSI F O T m out0 σ ∧ σ.vars "ds_j" < m) tgtSBody
      (fun σ σ' => TSI F O T m out0 σ' ∧ σ'.vars "ds_j" = σ.vars "ds_j" + 1) (24 * T + 10) := by
  intro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
  obtain ⟨σ1, r1, ho1, ha1, -, hv1⟩ :=
    (sLoop_spec (B := B) F O T hF hO hFB hOB (by omega)).run (σ := σ) ⟨h1, h2, h3, by omega⟩
  have e1 : ∀ y, y ≠ "ds_p" → σ1.vars y = σ.vars y := hv1
  have hj1 : σ1.vars "ds_j" = σ.vars "ds_j" := e1 _ (by decide)
  have r2 := Run.assign (B := B) (σ := σ1) (x := "ds_j") (e := .add (V "ds_j") (.lit 1))
    (v := σ.vars "ds_j" + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ1) (evalB_var (x := "ds_j") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [hj1]; simp; omega)
      rw [hj1] at this; simpa using this)
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Env.setVar]⟩
  · simp [Env.setVar, ha1, h1]
  · simp [Env.setVar, ha1, h2]
  · simp [Env.setVar]; rw [e1 _ (by decide), h3]
  · simp [Env.setVar]; rw [e1 _ (by decide), h4]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar, if_true]
    try simp only [↓reduceIte]
    rw [ho1, h6, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem tgtSLoop_spec {B : ℕ} (F O : List ℕ) (T m : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, v < B) (hB : T + m + 1 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "hs_t" = T ∧
        σ.vars "hs_m" = m) tgtSLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range m).flatMap (sBlkL F O T) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_j" → y ≠ "ds_p" → σ'.vars y = σ.vars y) ((24 * T + 14) * m + 6) := by
  intro σ ⟨h1, h2, h3, h4⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, -, ho⟩, hj⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_j" "hs_m" (TSI F O T m σ.out) m (24 * T + 10)
      (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.1)
      (tgtSBody_spec F O T m σ.out hF hO hFB hOB hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar, h4], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hj], ?_, hi (by simp [tgtSBody, sLoop, sBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [tgtSBody, sLoop, sBody, Com.warrs])
  · intro y hy1 hy2
    exact hv y (by simp [tgtSBody, sLoop, sBody, Com.wvars, hy1, hy2])

end Lax496464Proofs.WHierarchy.HittingSet.DSProg2
