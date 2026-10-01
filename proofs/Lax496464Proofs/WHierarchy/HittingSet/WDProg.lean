import Lax496464Proofs.WHierarchy.HittingSet.Firsts
import Lax496464Proofs.WHierarchy.HittingSet.Parse

/-! # Hitting Set to weighted definability: the program

After the reader and `Firsts.prep`, `outWD` writes the word of the structure of the compressed
instance followed by its weight: the header `3, 1, 1, 2, NN + m`, the `VERT` block
`NN, 0, …, NN-1`, the `EDGE` block `m, NN, …, NN+m-1`, the `I` block `T` followed by the pairs
`fp_f[p], NN + hs_own[p]`, and `fp_kk`. When `k > n` the program writes a fixed no-instance
instead. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WDProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V bump)
open Lax496464Proofs.WHierarchy.HittingSet.Parse Lax496464Proofs.WHierarchy.HittingSet.Firsts

/-! ## The three blocks -/

def vertBody : Com := .seq (.write (V "o_i")) (bump "o_i")
def vertLoop : Com := .seq (.assign "o_i" (.lit 0)) (.while (.lt (V "o_i") (V "fp_NN")) vertBody)

def edgeBody : Com := .seq (.write (.add (V "fp_NN") (V "o_i"))) (bump "o_i")
def edgeLoop : Com := .seq (.assign "o_i" (.lit 0)) (.while (.lt (V "o_i") (V "hs_m")) edgeBody)

def incBody : Com :=
  .seq (.write (.get "fp_f" (V "o_i")))
    (.seq (.write (.add (V "fp_NN") (.get "hs_own" (V "o_i")))) (bump "o_i"))
def incLoop : Com := .seq (.assign "o_i" (.lit 0)) (.while (.lt (V "o_i") (V "hs_t")) incBody)

/-- The pairs of the `I` block. -/
def incList (F O : List ℕ) (NN T : ℕ) : List ℕ :=
  (List.range T).flatMap fun p => [F.getD p 0, NN + O.getD p 0]

theorem incList_succ (F O : List ℕ) (NN T : ℕ) :
    incList F O NN (T + 1) = incList F O NN T ++ [F.getD T 0, NN + O.getD T 0] := by
  simp [incList, List.range_succ]

section loops

variable {B : ℕ}

def VI (NN : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "fp_NN" = NN ∧ σ.vars "o_i" ≤ NN ∧ σ.out = out0 ++ List.range (σ.vars "o_i")

theorem vertBody_spec (NN : ℕ) (out0 : List ℕ) (hB : NN + 1 < B) :
    Spec B (fun σ => VI NN out0 σ ∧ σ.vars "o_i" < NN) vertBody
      (fun σ σ' => VI NN out0 σ' ∧ σ'.vars "o_i" = σ.vars "o_i" + 1) 10 := by
  refine Spec.pre (P := fun σ => VI NN out0 σ ∧ σ.vars "o_i" < NN ∧ σ.vars "o_i" + 1 < B ∧
    1 < B) ?_ (fun σ ⟨h1, h2⟩ => ⟨h1, h2, by omega, by omega⟩)
  run_vcg
  obtain ⟨h1, h2, h3⟩ := ‹VI NN out0 σ›
  refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
  simp [Env.setVar, h3, List.range_succ]

theorem vertLoop_spec (NN : ℕ) (hB : NN + 1 < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN) vertLoop
      (fun σ σ' => σ'.out = σ.out ++ List.range NN ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "o_i" → σ'.vars y = σ.vars y) (14 * NN + 6) := by
  intro σ hσ
  obtain ⟨σ', r, ⟨⟨-, -, ho⟩, hi⟩, hv, ha, hin, -⟩ :=
    (Spec.forRangeZero (B := B) "o_i" "fp_NN" (VI NN σ.out) NN 10 (by omega) (fun _ h => h.2.1)
      (fun _ h => h.1) (vertBody_spec NN σ.out hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, hσ], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hi], ?_, hin (by simp [vertBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [vertBody, Com.warrs])
  · intro y hy; exact hv y (by simp [vertBody, Com.wvars, hy])

def EI (NN m : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "fp_NN" = NN ∧ σ.vars "hs_m" = m ∧ σ.vars "o_i" ≤ m ∧
    σ.out = out0 ++ (List.range (σ.vars "o_i")).map (NN + ·)

theorem edgeBody_spec (NN m : ℕ) (out0 : List ℕ) (hB : NN + m + 1 < B) :
    Spec B (fun σ => EI NN m out0 σ ∧ σ.vars "o_i" < m) edgeBody
      (fun σ σ' => EI NN m out0 σ' ∧ σ'.vars "o_i" = σ.vars "o_i" + 1) 12 := by
  refine Spec.pre (P := fun σ => EI NN m out0 σ ∧ σ.vars "o_i" < m ∧ σ.vars "o_i" + 1 < B ∧
    1 < B ∧ σ.vars "fp_NN" + σ.vars "o_i" < B ∧ σ.vars "fp_NN" < B) ?_
    (fun σ ⟨h1, h2⟩ => ⟨h1, h2, by omega, by omega, by rw [h1.1]; omega, by rw [h1.1]; omega⟩)
  run_vcg
  obtain ⟨h1, h2, h3, h4⟩ := ‹EI NN m out0 σ›
  refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega, ?_⟩,
    by simp [Env.setVar]⟩
  simp [Env.setVar, h4, List.range_succ, h1]

theorem edgeLoop_spec (NN m : ℕ) (hB : NN + m + 1 < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN ∧ σ.vars "hs_m" = m) edgeLoop
      (fun σ σ' => σ'.out = σ.out ++ (List.range m).map (NN + ·) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ ∀ y, y ≠ "o_i" → σ'.vars y = σ.vars y) (16 * m + 6) := by
  intro σ hσ
  obtain ⟨σ', r, ⟨⟨-, -, -, ho⟩, hi⟩, hv, ha, hin, -⟩ :=
    (Spec.forRangeZero (B := B) "o_i" "hs_m" (EI NN m σ.out) m 12 (by omega) (fun _ h => h.2.2.1)
      (fun _ h => h.2.1) (edgeBody_spec NN m σ.out hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, hσ.1], by simp [Env.setVar, hσ.2], by simp [Env.setVar],
        by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hi], ?_, hin (by simp [edgeBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [edgeBody, Com.warrs])
  · intro y hy; exact hv y (by simp [edgeBody, Com.wvars, hy])

def II (F O : List ℕ) (NN T : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "fp_NN" = NN ∧ σ.vars "hs_t" = T ∧ σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧
    σ.vars "o_i" ≤ T ∧ σ.out = out0 ++ incList F O NN (σ.vars "o_i")

theorem incBody_spec (F O : List ℕ) (NN T : ℕ) (out0 : List ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B) (hB : T + 1 < B)
    (hN : NN < B) :
    Spec B (fun σ => II F O NN T out0 σ ∧ σ.vars "o_i" < T) incBody
      (fun σ σ' => II F O NN T out0 σ' ∧ σ'.vars "o_i" = σ.vars "o_i" + 1) 16 := by
  refine Spec.pre (P := fun σ => II F O NN T out0 σ ∧ σ.vars "o_i" < T ∧ σ.vars "o_i" + 1 < B ∧
    1 < B ∧ σ.vars "fp_NN" < B ∧ σ.vars "o_i" < (σ.arrs "fp_f").length ∧
    σ.vars "o_i" < (σ.arrs "hs_own").length ∧ (σ.arrs "fp_f").getD (σ.vars "o_i") 0 < B ∧
    (σ.arrs "hs_own").getD (σ.vars "o_i") 0 < B ∧
    σ.vars "fp_NN" + (σ.arrs "hs_own").getD (σ.vars "o_i") 0 < B) ?_ ?_
  · run_vcg
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ‹II F O NN T out0 σ›
    refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
      by simp [Env.setVar, h4], by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
    simp [Env.setVar, h6, incList_succ, h1, h3, h4]
  · rintro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
    have hv : F.getD (σ.vars "o_i") 0 < B :=
      hFB _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    have hw : NN + O.getD (σ.vars "o_i") 0 < B :=
      hOB _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt, by omega, by omega, by rw [h1]; exact hN,
      by rw [h3]; omega, by rw [h4]; omega, by rw [h3]; exact hv, by rw [h4]; omega,
      by rw [h1, h4]; exact hw⟩

theorem incLoop_spec (F O : List ℕ) (NN T : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B) (hB : T + 1 < B)
    (hN : NN < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN ∧ σ.vars "hs_t" = T ∧ σ.arrs "fp_f" = F ∧
        σ.arrs "hs_own" = O) incLoop
      (fun σ σ' => σ'.out = σ.out ++ incList F O NN T ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ ∀ y, y ≠ "o_i" → σ'.vars y = σ.vars y) (20 * T + 6) := by
  intro σ hσ
  obtain ⟨σ', r, ⟨⟨-, -, -, -, -, ho⟩, hi⟩, hv, ha, hin, -⟩ :=
    (Spec.forRangeZero (B := B) "o_i" "hs_t" (II F O NN T σ.out) T 16 (by omega)
      (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.1)
      (incBody_spec F O NN T σ.out hF hO hFB hOB hB hN)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, hσ.1], by simp [Env.setVar, hσ.2.1], by simp [Env.setVar, hσ.2.2.1],
        by simp [Env.setVar, hσ.2.2.2], by simp [Env.setVar], by simp [Env.setVar, incList]⟩
  refine ⟨σ', r, by rw [ho, hi], ?_, hin (by simp [incBody, Com.reads]), ?_⟩
  · funext a; exact ha a (by simp [incBody, Com.warrs])
  · intro y hy; exact hv y (by simp [incBody, Com.wvars, hy])

end loops

/-! ## The word -/

/-- Write the word of the compressed structure and its weight. -/
def outWD : Com :=
  .seq (.write (.lit 3)) (.seq (.write (.lit 1)) (.seq (.write (.lit 1)) (.seq (.write (.lit 2))
  (.seq (.write (.add (V "fp_NN") (V "hs_m")))
  (.seq (.write (V "fp_NN")) (.seq vertLoop
  (.seq (.write (V "hs_m")) (.seq edgeLoop
  (.seq (.write (V "hs_t")) (.seq incLoop (.write (V "fp_kk"))))))))))))

/-- What `outWD` writes. -/
def outList (F O : List ℕ) (NN m T kk : ℕ) : List ℕ :=
  [3, 1, 1, 2, NN + m, NN] ++ List.range NN ++ [m] ++ (List.range m).map (NN + ·) ++ [T] ++
    incList F O NN T ++ [kk]

theorem outWD_spec {B : ℕ} (F O : List ℕ) (NN m T kk : ℕ) (hF : F.length = T)
    (hO : O.length = T) (hFB : ∀ v ∈ F, v < B) (hOB : ∀ v ∈ O, NN + v < B)
    (hB : NN + m + T + kk + 4 < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN ∧ σ.vars "hs_m" = m ∧ σ.vars "hs_t" = T ∧
        σ.arrs "fp_f" = F ∧ σ.arrs "hs_own" = O ∧ σ.vars "fp_kk" = kk) outWD
      (fun σ σ' => σ'.out = σ.out ++ outList F O NN m T kk)
      (14 * NN + 16 * m + 20 * T + 60) := by
  run_vcg [vertLoop_spec (B := B) NN (by omega), edgeLoop_spec (B := B) NN m (by omega),
    incLoop_spec (B := B) F O NN T hF hO hFB hOB (by omega) (by omega)]
  all_goals (simp_all [outList]; try omega)

/-- The fixed no-instance. -/
def writeNo : Com :=
  .seq (.write (.lit 3)) (.seq (.write (.lit 1)) (.seq (.write (.lit 1)) (.seq (.write (.lit 2))
  (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0))
    (.write (.lit 1)))))))))

theorem writeNo_spec {B : ℕ} (hB : 3 < B) :
    Spec B (fun _ => True) writeNo (fun σ σ' => σ'.out = σ.out ++ [3, 1, 1, 2, 0, 0, 0, 0, 1]) 20 := by
  run_vcg
  simp

/-- The compressed dimensions, the first occurrences, and the word. -/
def wdMain : Com := .seq prep outWD

/-- **The program of the reduction.** -/
def wdProg : Com := .seq readHS (.ite (.lt (V "hs_n") (V "hs_k")) writeNo wdMain)

/-- The scalars of the program. -/
def wdVars : List String := parseVars ++ Firsts.prepVars ++ ["o_i"]

/-- The arrays of the program. -/
def wdArrs : List String := ["hs_off", "hs_mem", "hs_own", "fp_f"]

/-- A bound on the entries of the word written. -/
theorem outList_le (F O : List ℕ) (NN m T kk M : ℕ) (hF : ∀ v ∈ F, v ≤ M)
    (hO : ∀ v ∈ O, NN + v ≤ M) (h1 : NN + m ≤ M) (hT : T ≤ M) (hkk : kk ≤ M) (h3 : 3 ≤ M)
    (hFl : F.length = T) (hOl : O.length = T) :
    ∀ v ∈ outList F O NN m T kk, v ≤ M := by
  simp only [outList, incList, List.forall_mem_append, List.forall_mem_cons, List.mem_range,
    List.mem_map, List.mem_flatMap, forall_exists_index, and_imp]
  and_intros
  all_goals first
    | omega
    | (intro x hx; exact absurd hx List.not_mem_nil)
    | (intro x hx; omega)
    | (intro x y hy hxy; omega)
    | (intro x y hy hx
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
       rcases hx with rfl | rfl
       · exact hF _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
       · exact hO _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))

end Lax496464Proofs.WHierarchy.HittingSet.WDProg
