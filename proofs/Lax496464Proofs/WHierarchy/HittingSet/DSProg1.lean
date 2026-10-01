import Lax496464Proofs.WHierarchy.HittingSet.ReadNat

/-! # Hitting Set to Dominating Set: the program, part 1

The test for an empty set (`emCheck`), and the two passes writing the offsets of the graph word:
for each element `u` its degree `NN - 1 + #{p : fp_f[p] = u}` (`offELoop`), for each set `j` its size
`hs_off[j+1] - hs_off[j]` (`offSLoop`), each added to the running offset `ds_o` and written.

The specifications are stated for arbitrary contents `F` of `fp_f`, `O` of `hs_own` and `OFF` of
`hs_off`; `DSFinal` puts in the arrays of the instance. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSProg1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V bump)

/-! ## Is some set empty? -/

def emBody : Com :=
  .seq (.ite (.eq (.get "hs_off" (.add (V "ds_j") (.lit 1))) (.get "hs_off" (V "ds_j")))
    (.assign "ds_em" (.lit 1)) .skip) (bump "ds_j")
def emLoop : Com := .seq (.assign "ds_j" (.lit 0)) (.while (.lt (V "ds_j") (V "hs_m")) emBody)

/-- `ds_em := 1` if two consecutive offsets are equal, `0` otherwise. -/
def emCheck : Com := .seq (.assign "ds_em" (.lit 0)) emLoop

/-- Some set before `j` is empty. -/
def Emp (OFF : List ℕ) (j : ℕ) : Prop := ∃ j' < j, OFF.getD (j' + 1) 0 = OFF.getD j' 0

instance (OFF : List ℕ) (j : ℕ) : Decidable (Emp OFF j) := by unfold Emp; infer_instance

def EmI (OFF : List ℕ) (m : ℕ) (σ : Env) : Prop :=
  σ.arrs "hs_off" = OFF ∧ σ.vars "hs_m" = m ∧ σ.vars "ds_j" ≤ m ∧
    σ.vars "ds_em" = if Emp OFF (σ.vars "ds_j") then 1 else 0

theorem emp_succ (OFF : List ℕ) (j : ℕ) :
    Emp OFF (j + 1) ↔ Emp OFF j ∨ OFF.getD (j + 1) 0 = OFF.getD j 0 := by
  constructor
  · rintro ⟨j', hj', h⟩
    rcases Nat.lt_or_ge j' j with h1 | h1
    · exact Or.inl ⟨j', h1, h⟩
    · right; rwa [show j' = j by omega] at h
  · rintro (⟨j', hj', h⟩ | h)
    · exact ⟨j', by omega, h⟩
    · exact ⟨j, by omega, h⟩

theorem emBody_spec {B : ℕ} (OFF : List ℕ) (m : ℕ) (hl : OFF.length = m + 1)
    (hOB : ∀ v ∈ OFF, v < B) (hB : m + 1 < B) :
    Spec B (fun σ => EmI OFF m σ ∧ σ.vars "ds_j" < m) emBody
      (fun σ σ' => EmI OFF m σ' ∧ σ'.vars "ds_j" = σ.vars "ds_j" + 1) 20 := by
  have hget : ∀ i < OFF.length, OFF.getD i 0 < B := fun i hi =>
    hOB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  refine Spec.pre (P := fun σ => EmI OFF m σ ∧ σ.vars "ds_j" < m ∧ σ.vars "ds_j" + 1 < B ∧
    1 < B ∧ σ.vars "ds_j" + 1 < (σ.arrs "hs_off").length ∧
    σ.vars "ds_j" < (σ.arrs "hs_off").length ∧
    (σ.arrs "hs_off").getD (σ.vars "ds_j" + 1) 0 < B ∧
    (σ.arrs "hs_off").getD (σ.vars "ds_j") 0 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4⟩ := ‹EmI OFF m σ›
    · have hc := ‹(σ.arrs "hs_off").getD (σ.vars "ds_j" + 1) 0 =
        (σ.arrs "hs_off").getD (σ.vars "ds_j") 0›
      rw [h1] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega,
        ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, if_true, String.reduceEq, if_false]
      try simp only [↓reduceIte]
      rw [if_pos ((emp_succ OFF _).mpr (Or.inr hc))]
    · have hc := ‹¬(σ.arrs "hs_off").getD (σ.vars "ds_j" + 1) 0 =
        (σ.arrs "hs_off").getD (σ.vars "ds_j") 0›
      rw [h1] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega,
        ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, if_false]
      try simp only [↓reduceIte]
      rw [h4]
      by_cases he : Emp OFF (σ.vars "ds_j")
      · rw [if_pos he, if_pos ((emp_succ OFF _).mpr (Or.inl he))]
      · rw [if_neg he, if_neg (fun h => ((emp_succ OFF _).mp h).elim he hc)]
  · rintro σ ⟨⟨h1, h2, h3, h4⟩, hlt⟩
    refine ⟨⟨h1, h2, h3, h4⟩, hlt, by omega, by omega, by rw [h1]; omega, by rw [h1]; omega,
      by rw [h1]; exact hget _ (by omega), by rw [h1]; exact hget _ (by omega)⟩

theorem emCheck_spec {B : ℕ} (OFF : List ℕ) (m : ℕ) (hl : OFF.length = m + 1)
    (hOB : ∀ v ∈ OFF, v < B) (hB : m + 1 < B) :
    Spec B (fun σ => σ.arrs "hs_off" = OFF ∧ σ.vars "hs_m" = m) emCheck
      (fun σ σ' => (σ'.vars "ds_em" = if Emp OFF m then 1 else 0) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "ds_em" → y ≠ "ds_j" → σ'.vars y = σ.vars y) (24 * m + 8) := by
  intro σ ⟨h1, h2⟩
  have r1 := Run.assign (B := B) (σ := σ) (x := "ds_em") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  obtain ⟨σ2, r2, ⟨⟨-, -, -, hem⟩, hj⟩, hv, ha, hi, ho⟩ :=
    (Spec.forRangeZero (B := B) "ds_j" "hs_m" (EmI OFF m) m 20 (by omega) (fun _ h => h.2.2.1)
      (fun _ h => h.2.1) (emBody_spec OFF m hl hOB hB)).frame.run (σ := σ.setVar "ds_em" 0)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, Emp]⟩
  refine ⟨σ2, (r1.seq r2).mono (by simp; omega), by rw [hem, hj], ?_, ?_, ?_, ?_⟩
  · funext a; rw [ha a (by simp [emBody, Com.warrs])]; rfl
  · rw [hi (by simp [emBody, Com.reads])]; rfl
  · rw [ho (by simp [emBody, Com.NoWrite])]; rfl
  · intro y hy1 hy2
    rw [hv y (by simp [emBody, Com.wvars, hy1, hy2])]
    simp only [Env.setVar, if_neg hy1]

/-! ## Counting the positions whose first occurrence is `u` -/

/-- The number of positions below `T` whose entry of `F` is `u`. -/
def cntL (F : List ℕ) (T u : ℕ) : ℕ := ((List.range T).filter fun p => F.getD p 0 = u).length

theorem cntL_succ (F : List ℕ) (T u : ℕ) :
    cntL F (T + 1) u = cntL F T u + if F.getD T 0 = u then 1 else 0 := by
  unfold cntL
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : F.getD T 0 = u
  · rw [if_pos h]
    simp only [List.filter_cons, List.filter_nil, h, decide_true, if_true, List.length_singleton]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, h, decide_false]; simp

theorem cntL_le (F : List ℕ) (T u : ℕ) : cntL F T u ≤ T := by
  unfold cntL; exact (List.length_filter_le _ _).trans (by simp)

def cntBody : Com :=
  .seq (.ite (.eq (.get "fp_f" (V "ds_p")) (V "ds_u")) (bump "ds_c") .skip) (bump "ds_p")
def cntLoop : Com := .seq (.assign "ds_p" (.lit 0)) (.while (.lt (V "ds_p") (V "hs_t")) cntBody)

def CI (F : List ℕ) (T u : ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = T ∧ σ.vars "ds_u" = u ∧ σ.vars "ds_p" ≤ T ∧
    σ.vars "ds_c" = cntL F (σ.vars "ds_p") u

theorem cntBody_spec {B : ℕ} (F : List ℕ) (T u : ℕ) (hF : F.length = T) (hFB : ∀ v ∈ F, v < B)
    (hB : T + 1 < B) (hu : u < B) :
    Spec B (fun σ => CI F T u σ ∧ σ.vars "ds_p" < T) cntBody
      (fun σ σ' => CI F T u σ' ∧ σ'.vars "ds_p" = σ.vars "ds_p" + 1) 20 := by
  refine Spec.pre (P := fun σ => CI F T u σ ∧ σ.vars "ds_p" < T ∧ σ.vars "ds_p" + 1 < B ∧
    1 < B ∧ σ.vars "ds_c" + 1 < B ∧ σ.vars "ds_u" < B ∧
    σ.vars "ds_p" < (σ.arrs "fp_f").length ∧ (σ.arrs "fp_f").getD (σ.vars "ds_p") 0 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4, h5⟩ := ‹CI F T u σ›
    · have hc := ‹(σ.arrs "fp_f").getD (σ.vars "ds_p") 0 = σ.vars "ds_u"›
      rw [h1, h3] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, if_false, if_true, h5, cntL_succ, if_pos hc]
      try simp
    · have hc := ‹¬(σ.arrs "fp_f").getD (σ.vars "ds_p") 0 = σ.vars "ds_u"›
      rw [h1, h3] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, if_false, if_true, h5, cntL_succ, if_neg hc]
      try simp
  · rintro σ ⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩
    have hc := cntL_le F (σ.vars "ds_p") u
    refine ⟨⟨h1, h2, h3, h4, h5⟩, hlt, by omega, by omega, by omega, by omega, by rw [h1]; omega,
      by rw [h1]; exact hFB _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)⟩

theorem cntLoop_spec {B : ℕ} (F : List ℕ) (T : ℕ) (hF : F.length = T) (hFB : ∀ v ∈ F, v < B)
    (hB : T + 1 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = T ∧ σ.vars "ds_c" = 0 ∧
        σ.vars "ds_u" < B) cntLoop
      (fun σ σ' => σ'.vars "ds_c" = cntL F T (σ.vars "ds_u") ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "ds_p" → y ≠ "ds_c" → σ'.vars y = σ.vars y) (24 * T + 6) := by
  intro σ ⟨h1, h2, h3, hu⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, hc⟩, hp⟩, hv, ha, hi, ho⟩ :=
    (Spec.forRangeZero (B := B) "ds_p" "hs_t" (CI F T (σ.vars "ds_u")) T 20 (by omega)
      (fun _ h => h.2.2.2.1) (fun _ h => h.2.1)
      (cntBody_spec F T _ hF hFB hB hu)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar], by simp [Env.setVar, h3, cntL]⟩
  refine ⟨σ', r, by rw [hc, hp], ?_, hi (by simp [cntBody, Com.reads]),
    ho (by simp [cntBody, Com.NoWrite]), ?_⟩
  · funext a; exact ha a (by simp [cntBody, Com.warrs])
  · intro y hy1 hy2; exact hv y (by simp [cntBody, Com.wvars, hy1, hy2])

/-! ## The offsets of the elements -/

/-- A prefix sum. -/
def psum (a : ℕ → ℕ) (i : ℕ) : ℕ := ((List.range i).map a).sum

theorem psum_succ (a : ℕ → ℕ) (i : ℕ) : psum a (i + 1) = psum a i + a i := by
  simp [psum, List.range_succ]

theorem psum_mono (a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : psum a i ≤ psum a j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · rw [psum_succ]; have := ih (by omega); omega
      · rw [show i = j + 1 by omega]

/-- The degree of element `u`. -/
def eLen (F : List ℕ) (NN T u : ℕ) : ℕ := NN - 1 + cntL F T u

def offEBody : Com :=
  .seq (.assign "ds_c" (.lit 0))
    (.seq cntLoop
      (.seq (.assign "ds_o" (.add (V "ds_o") (.add (.sub (V "fp_NN") (.lit 1)) (V "ds_c"))))
        (.seq (.write (V "ds_o")) (bump "ds_u"))))
def offELoop : Com := .seq (.assign "ds_u" (.lit 0)) (.while (.lt (V "ds_u") (V "fp_NN")) offEBody)

def OEI (F : List ℕ) (NN T : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = T ∧ σ.vars "fp_NN" = NN ∧ σ.vars "ds_u" ≤ NN ∧
    σ.vars "ds_o" = psum (eLen F NN T) (σ.vars "ds_u") ∧
    σ.out = out0 ++ (List.range (σ.vars "ds_u")).map fun u => psum (eLen F NN T) (u + 1)

theorem offEBody_spec {B : ℕ} (F : List ℕ) (NN T : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hFB : ∀ v ∈ F, v < B) (hB : T + NN + 1 < B) (hS : psum (eLen F NN T) NN < B) :
    Spec B (fun σ => OEI F NN T out0 σ ∧ σ.vars "ds_u" < NN) offEBody
      (fun σ σ' => OEI F NN T out0 σ' ∧ σ'.vars "ds_u" = σ.vars "ds_u" + 1) (24 * T + 60) := by
  intro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
  set u := σ.vars "ds_u" with hu_def
  have r1 := Run.assign (B := B) (σ := σ) (x := "ds_c") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  obtain ⟨σ2, r2, hc2, ha2, -, ho2, hv2⟩ :=
    (cntLoop_spec (B := B) F T hF hFB (by omega)).run (σ := σ.setVar "ds_c" 0)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar]; omega⟩
  have hu2 : (σ.setVar "ds_c" 0).vars "ds_u" = u := by simp [Env.setVar, hu_def]
  rw [hu2] at hc2
  have e2 : ∀ y, y ≠ "ds_p" → y ≠ "ds_c" → σ2.vars y = σ.vars y := by
    intro y h h'; rw [hv2 y h h']; simp [Env.setVar, h']
  have hmono := psum_mono (eLen F NN T) (show u + 1 ≤ NN by omega)
  rw [psum_succ] at hmono
  have hN2 : σ2.vars "fp_NN" = NN := by rw [e2 _ (by decide) (by decide), h3]
  have ho2' : σ2.vars "ds_o" = psum (eLen F NN T) u := by rw [e2 _ (by decide) (by decide), h5]
  have hcl := cntL_le F T u
  have hel : eLen F NN T u = NN - 1 + cntL F T u := rfl
  have hval : σ2.vars "ds_o" + (σ2.vars "fp_NN" - 1 + σ2.vars "ds_c") =
      psum (eLen F NN T) (u + 1) := by
    rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), hc2, h5, h3, psum_succ]; rfl
  have r3 := Run.assign (B := B) (σ := σ2) (x := "ds_o")
    (e := .add (V "ds_o") (.add (.sub (V "fp_NN") (.lit 1)) (V "ds_c")))
    (v := psum (eLen F NN T) (u + 1)) (by
      rw [← hval]
      refine evalB_bin (evalB_var (by omega)) (evalB_bin (evalB_bin (evalB_var (by omega))
        (evalB_lit (by omega)) (by simp; omega)) (evalB_var (by omega)) (by simp; omega))
        (by simp; omega))
  set σ3 := σ2.setVar "ds_o" (psum (eLen F NN T) (u + 1)) with hσ3
  have r4 := Run.write (B := B) (σ := σ3) (e := V "ds_o") (v := psum (eLen F NN T) (u + 1))
    (by have : σ3.vars "ds_o" = psum (eLen F NN T) (u + 1) := by simp [hσ3, Env.setVar]
        rw [← this]; exact evalB_var (by rw [this]; omega))
  set σ4 : Env := { σ3 with out := σ3.out ++ [psum (eLen F NN T) (u + 1)] } with hσ4
  have h4u : σ4.vars "ds_u" = u := by
    simp [hσ4, hσ3, Env.setVar]; rw [e2 _ (by decide) (by decide)]
  have r5 := Run.assign (B := B) (σ := σ4) (x := "ds_u") (e := .add (V "ds_u") (.lit 1))
    (v := u + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ4) (evalB_var (x := "ds_u") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h4u]; simp; omega)
      rw [h4u] at this; simpa using this)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [Env.setVar, hu_def]⟩
  · simp [Env.setVar, hσ4, hσ3, ha2, h1]
  · simp [Env.setVar, hσ4, hσ3]; rw [e2 _ (by decide) (by decide), h2]
  · simp [Env.setVar, hσ4, hσ3]; rw [e2 _ (by decide) (by decide), h3]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hσ4, hσ3]
  · simp [Env.setVar, hσ4, hσ3, ho2, h6, List.range_succ]

theorem offELoop_spec {B : ℕ} (F : List ℕ) (NN T : ℕ) (hF : F.length = T)
    (hFB : ∀ v ∈ F, v < B) (hB : T + NN + 1 < B) (hS : psum (eLen F NN T) NN < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = T ∧ σ.vars "fp_NN" = NN ∧
        σ.vars "ds_o" = 0) offELoop
      (fun σ σ' => σ'.vars "ds_o" = psum (eLen F NN T) NN ∧
        σ'.out = σ.out ++ (List.range NN).map (fun u => psum (eLen F NN T) (u + 1)) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_u" → y ≠ "ds_p" → y ≠ "ds_c" → y ≠ "ds_o" → σ'.vars y = σ.vars y)
      ((24 * T + 64) * NN + 6) := by
  intro σ ⟨h1, h2, h3, h4⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, hoo, ho⟩, hu⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_u" "fp_NN" (OEI F NN T σ.out) NN (24 * T + 60) (by omega)
      (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1)
      (offEBody_spec F NN T σ.out hF hFB hB hS)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp [Env.setVar], by simp [Env.setVar, h4, psum], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [hoo, hu], by rw [ho, hu], ?_,
    hi (by simp [offEBody, cntLoop, cntBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [offEBody, cntLoop, cntBody, Com.warrs])
  · intro y hy1 hy2 hy3 hy4
    exact hv y (by simp [offEBody, cntLoop, cntBody, Com.wvars, hy1, hy2, hy3, hy4])

/-! ## The offsets of the sets -/

/-- The size of set `j`, from the offsets. -/
def sLen (OFF : List ℕ) (j : ℕ) : ℕ := OFF.getD (j + 1) 0 - OFF.getD j 0

def offSBody : Com :=
  .seq (.assign "ds_o" (.add (V "ds_o")
      (.sub (.get "hs_off" (.add (V "ds_j") (.lit 1))) (.get "hs_off" (V "ds_j")))))
    (.seq (.write (V "ds_o")) (bump "ds_j"))
def offSLoop : Com := .seq (.assign "ds_j" (.lit 0)) (.while (.lt (V "ds_j") (V "hs_m")) offSBody)

def OSI (OFF : List ℕ) (m base : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "hs_off" = OFF ∧ σ.vars "hs_m" = m ∧ σ.vars "ds_j" ≤ m ∧
    σ.vars "ds_o" = base + psum (sLen OFF) (σ.vars "ds_j") ∧
    σ.out = out0 ++ (List.range (σ.vars "ds_j")).map fun j => base + psum (sLen OFF) (j + 1)

theorem offSBody_spec {B : ℕ} (OFF : List ℕ) (m base : ℕ) (out0 : List ℕ)
    (hl : OFF.length = m + 1) (hOB : ∀ v ∈ OFF, v < B) (hB : m + 1 < B)
    (hS : base + psum (sLen OFF) m < B) :
    Spec B (fun σ => OSI OFF m base out0 σ ∧ σ.vars "ds_j" < m) offSBody
      (fun σ σ' => OSI OFF m base out0 σ' ∧ σ'.vars "ds_j" = σ.vars "ds_j" + 1) 20 := by
  have hget : ∀ i < OFF.length, OFF.getD i 0 < B := fun i hi =>
    hOB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  refine Spec.pre (P := fun σ => OSI OFF m base out0 σ ∧ σ.vars "ds_j" < m ∧
    σ.vars "ds_j" + 1 < B ∧ 1 < B ∧ σ.vars "ds_j" + 1 < (σ.arrs "hs_off").length ∧
    σ.vars "ds_j" < (σ.arrs "hs_off").length ∧
    (σ.arrs "hs_off").getD (σ.vars "ds_j" + 1) 0 < B ∧
    (σ.arrs "hs_off").getD (σ.vars "ds_j") 0 < B ∧
    σ.vars "ds_o" + ((σ.arrs "hs_off").getD (σ.vars "ds_j" + 1) 0 -
      (σ.arrs "hs_off").getD (σ.vars "ds_j") 0) < B ∧ σ.vars "ds_o" < B) ?_ ?_
  · run_vcg
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ‹OSI OFF m base out0 σ›
      have hs : sLen OFF (σ.vars "ds_j") =
          OFF.getD (σ.vars "ds_j" + 1) 0 - OFF.getD (σ.vars "ds_j") 0 := rfl
      have hps := psum_succ (sLen OFF) (σ.vars "ds_j")
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega,
        ?_, ?_⟩, by simp [Env.setVar]⟩
      · simp only [Env.setVar, if_true, String.reduceEq, if_false]
        try simp only [↓reduceIte]
        rw [h4, h1, hps, hs]; omega
      · simp only [Env.setVar, if_true, String.reduceEq, if_false]
        try simp only [↓reduceIte]
        rw [h5, h1, h4, List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
          hps, hs]
        congr 2
        simp only [List.cons.injEq, and_true]
        omega
    · simp only [Env.setVar, if_true]
      assumption
  · rintro σ ⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩
    have hmono := psum_mono (sLen OFF) (show σ.vars "ds_j" + 1 ≤ m by omega)
    rw [psum_succ] at hmono
    refine ⟨⟨h1, h2, h3, h4, h5⟩, hlt, by omega, by omega, by rw [h1]; omega, by rw [h1]; omega,
      by rw [h1]; exact hget _ (by omega), by rw [h1]; exact hget _ (by omega), ?_, ?_⟩
    · have hs : sLen OFF (σ.vars "ds_j") =
          OFF.getD (σ.vars "ds_j" + 1) 0 - OFF.getD (σ.vars "ds_j") 0 := rfl
      rw [h1, h4]; omega
    · rw [h4]; omega

theorem offSLoop_spec {B : ℕ} (OFF : List ℕ) (m base : ℕ) (hl : OFF.length = m + 1)
    (hOB : ∀ v ∈ OFF, v < B) (hB : m + 1 < B) (hS : base + psum (sLen OFF) m < B) :
    Spec B (fun σ => σ.arrs "hs_off" = OFF ∧ σ.vars "hs_m" = m ∧ σ.vars "ds_o" = base) offSLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range m).map (fun j => base + psum (sLen OFF) (j + 1)) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_j" → y ≠ "ds_o" → σ'.vars y = σ.vars y) (24 * m + 6) := by
  intro σ ⟨h1, h2, h3⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, -, ho⟩, hj⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "ds_j" "hs_m" (OSI OFF m base σ.out) m 20 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (offSBody_spec OFF m base σ.out hl hOB hB hS)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, h3, psum], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hj], ?_, hi (by simp [offSBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [offSBody, Com.warrs])
  · intro y hy1 hy2; exact hv y (by simp [offSBody, Com.wvars, hy1, hy2])

end Lax496464Proofs.WHierarchy.HittingSet.DSProg1
