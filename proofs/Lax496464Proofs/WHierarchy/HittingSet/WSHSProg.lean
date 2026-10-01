import Lax496464Proofs.WHierarchy.HittingSet.WSHSRead
import Lax496464Proofs.WHierarchy.HittingSet.DSHSProg

/-! # Weighted monotone satisfiability to Hitting Set: the program

After the reader (`WSHSRead.wsRead`) and the first occurrences (`Firsts.firstsLoop`), the program
copies the first occurrences into `es_val`, counts the positions that are first occurrences — the
number of variables — and then writes either the fixed no-instance (when `k` exceeds it) or the
codes of `T`, `c`, `k` followed by the sets with `EmitSets.setsLoop`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WSHSProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax429075.CNF Lax496464.WH_C3_WeightedSat Lax496464.WH_C2_HittingSet
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.WSHSMath Lax496464Proofs.WHierarchy.HittingSet.WSHSRead
open Lax496464Proofs.WHierarchy.HittingSet.EmitSets
open Lax496464Proofs.WHierarchy.HittingSet.EmitNat (V bump emitNat)

def copyBody : Com := .seq (.store "es_val" (V "ws_i") (.get "fp_f" (V "ws_i"))) (bump "ws_i")
def copyF : Com := .seq (.assign "ws_i" (.lit 0)) (.while (.lt (V "ws_i") (V "hs_t")) copyBody)

def countBody : Com :=
  .seq (.ite (.eq (.get "fp_f" (V "ws_i")) (V "ws_i")) (bump "ws_d") .skip) (bump "ws_i")
def countD : Com := .seq (.assign "ws_i" (.lit 0)) (.while (.lt (V "ws_i") (V "hs_t")) countBody)

def wsHeader : Com :=
  .seq (.seq (.assign "en_v" (V "hs_t")) emitNat) (.seq (.seq (.assign "en_v" (V "ws_c")) emitNat)
    (.seq (.assign "en_v" (V "ws_k")) emitNat))

def wsSetup : Com :=
  .seq (.assign "es_U" (V "hs_t")) (.seq (.assign "es_m" (V "ws_c")) (.assign "es_self" (.lit 0)))

def writeNoHS : Com :=
  .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 1)) (.seq (.write (.lit 0))
    (.write (.lit 1)))))

def wsEmit : Com := .seq wsSetup (.seq wsHeader setsLoop)

/-- **The program of the reduction.** -/
def wsProg : Com :=
  .seq wsRead (.seq Firsts.firstsLoop (.seq copyF (.seq (.assign "ws_d" (.lit 0)) (.seq countD
    (.ite (.lt (V "ws_d") (V "ws_k")) writeNoHS wsEmit)))))

/-! ## Copying -/

def CI (F : List ℕ) (N : ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = N ∧ σ.vars "ws_i" ≤ N ∧ (σ.arrs "es_val").length = N ∧
    ∀ p < σ.vars "ws_i", (σ.arrs "es_val").getD p 0 = F.getD p 0

theorem copyBody_spec {B : ℕ} (F : List ℕ) (N : ℕ) (hF : F.length = N) (hFB : ∀ v ∈ F, v < B)
    (hB : N + 2 < B) :
    Spec B (fun σ => CI F N σ ∧ σ.vars "ws_i" < N) copyBody
      (fun σ σ' => CI F N σ' ∧ σ'.vars "ws_i" = σ.vars "ws_i" + 1) 12 := by
  refine Spec.pre (P := fun σ => (CI F N σ ∧ σ.vars "ws_i" < N) ∧ σ.vars "ws_i" + 1 < B ∧
    σ.vars "ws_i" < (σ.arrs "es_val").length ∧ σ.vars "ws_i" < (σ.arrs "fp_f").length ∧
    (σ.arrs "fp_f").getD (σ.vars "ws_i") 0 < B ∧ 1 < B) ?_ ?_
  · run_vcg
    obtain ⟨h1, h2, h3, h4, h5⟩ := ‹CI F N σ›
    have e1 : ∀ p, p < σ.vars "ws_i" + 1 → ((σ.arrs "es_val").set (σ.vars "ws_i")
        ((σ.arrs "fp_f").getD (σ.vars "ws_i") 0)).getD p 0 = F.getD p 0 := by
      intro p hp
      rcases Nat.lt_or_ge p (σ.vars "ws_i") with h | h
      · rw [DSHSProg.getD_set_other _ _ (by omega)]; exact h5 p h
      · rw [show p = σ.vars "ws_i" by omega, DSHSProg.getD_set_self _ _ (by omega), h1]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [Env.setVar, Env.setArr, h1]
    · simp [Env.setVar, Env.setArr, h2]
    · simp [Env.setVar, Env.setArr]; omega
    · simp [Env.setVar, Env.setArr, h4]
    · intro p hp
      simp only [Env.setVar, Env.setArr, ↓reduceIte] at hp ⊢
      exact e1 p hp
    · simp [Env.setVar, Env.setArr]
  · rintro σ ⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩
    refine ⟨⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩, by omega, by omega, by rw [h1]; omega, ?_, by omega⟩
    rw [h1, List.getD_eq_getElem _ _ (by omega)]
    exact hFB _ (List.getElem_mem _)

theorem copyF_spec {B : ℕ} (F : List ℕ) (N : ℕ) (hF : F.length = N) (hFB : ∀ v ∈ F, v < B)
    (hB : N + 2 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = N ∧ (σ.arrs "es_val").length = N) copyF
      (fun σ σ' => σ'.arrs "es_val" = F ∧ (∀ b, b ≠ "es_val" → σ'.arrs b = σ.arrs b) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ y, y ≠ "ws_i" → σ'.vars y = σ.vars y)
      (16 * N + 6) := by
  intro σ ⟨h1, h2, h3⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, hl', hc⟩, hi⟩, hv, ha, hin, ho⟩ :=
    (Spec.forRangeZero (B := B) "ws_i" "hs_t" (CI F N) N 12 (by omega) (fun _ h => h.2.2.1)
      (fun _ h => h.2.1) (copyBody_spec F N hF hFB hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, h3], by simp [Env.setVar]⟩
  refine ⟨σ', r, WSHSRead.list_eq_getD (by rw [hl', hF]) fun p hp => hc p (by omega),
    fun b hb => ha b ?_, hin (by simp [copyBody, Com.reads]), ho (by simp [copyBody, Com.NoWrite]),
    fun y hy => hv y (by simp [copyBody, Com.wvars, hy])⟩
  simp [copyBody, Com.warrs, hb]

/-! ## Counting the variables -/

/-- The positions below `i` that are fixed points of `F`. -/
def fixCount (F : List ℕ) (i : ℕ) : ℕ := ((List.range i).filter fun p => F.getD p 0 = p).length

theorem fixCount_succ (F : List ℕ) (i : ℕ) :
    fixCount F (i + 1) = fixCount F i + if F.getD i 0 = i then 1 else 0 := by
  unfold fixCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : F.getD i 0 = i
  · rw [if_pos h]
    simp only [List.filter_cons, List.filter_nil, h, decide_true, if_true, List.length_singleton]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, h, decide_false]; simp

theorem fixCount_le (F : List ℕ) (i : ℕ) : fixCount F i ≤ i := by
  unfold fixCount; exact (List.length_filter_le _ _).trans (by simp)

def DI (F : List ℕ) (N : ℕ) (σ : Env) : Prop :=
  σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = N ∧ σ.vars "ws_i" ≤ N ∧
    σ.vars "ws_d" = fixCount F (σ.vars "ws_i")

theorem countBody_spec {B : ℕ} (F : List ℕ) (N : ℕ) (hF : F.length = N) (hFB : ∀ v ∈ F, v < B)
    (hB : N + 2 < B) :
    Spec B (fun σ => DI F N σ ∧ σ.vars "ws_i" < N) countBody
      (fun σ σ' => DI F N σ' ∧ σ'.vars "ws_i" = σ.vars "ws_i" + 1) 20 := by
  refine Spec.pre (P := fun σ => (DI F N σ ∧ σ.vars "ws_i" < N) ∧ σ.vars "ws_i" + 1 < B ∧
    σ.vars "ws_d" + 1 < B ∧ σ.vars "ws_i" < (σ.arrs "fp_f").length ∧
    (σ.arrs "fp_f").getD (σ.vars "ws_i") 0 < B ∧ 1 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4⟩ := ‹DI F N σ›
    · have hc := ‹(σ.arrs "fp_f").getD (σ.vars "ws_i") 0 = σ.vars "ws_i"›
      rw [h1] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega, ?_⟩,
        by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [fixCount_succ, if_pos hc, h4]
    · have hc := ‹¬(σ.arrs "fp_f").getD (σ.vars "ws_i") 0 = σ.vars "ws_i"›
      rw [h1] at hc
      refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar]; omega, ?_⟩,
        by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [fixCount_succ, if_neg hc, h4]; rfl
  · rintro σ ⟨⟨h1, h2, h3, h4⟩, hlt⟩
    have := fixCount_le F (σ.vars "ws_i")
    refine ⟨⟨⟨h1, h2, h3, h4⟩, hlt⟩, by omega, by omega, by rw [h1]; omega, ?_, by omega⟩
    rw [h1, List.getD_eq_getElem _ _ (by omega)]
    exact hFB _ (List.getElem_mem _)

theorem countD_spec {B : ℕ} (F : List ℕ) (N : ℕ) (hF : F.length = N) (hFB : ∀ v ∈ F, v < B)
    (hB : N + 2 < B) :
    Spec B (fun σ => σ.arrs "fp_f" = F ∧ σ.vars "hs_t" = N ∧ σ.vars "ws_d" = 0) countD
      (fun σ σ' => σ'.vars "ws_d" = fixCount F N ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        σ'.out = σ.out ∧ ∀ y, y ≠ "ws_i" → y ≠ "ws_d" → σ'.vars y = σ.vars y) (24 * N + 6) := by
  intro σ ⟨h1, h2, h3⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, hd⟩, hi⟩, hv, ha, hin, ho⟩ :=
    (Spec.forRangeZero (B := B) "ws_i" "hs_t" (DI F N) N 20 (by omega) (fun _ h => h.2.2.1)
      (fun _ h => h.2.1) (countBody_spec F N hF hFB hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, h3, fixCount]⟩
  refine ⟨σ', r, by rw [hd, hi], funext fun a => ha a (by simp [countBody, Com.warrs]),
    hin (by simp [countBody, Com.reads]), ho (by simp [countBody, Com.NoWrite]),
    fun y h1 h2 => hv y (by simp [countBody, Com.wvars, h1, h2])⟩

theorem fixCount_firsts (l : List ℕ) : fixCount (Firsts.firsts l) l.length = l.toFinset.card := by
  rw [← countFirst_eq]
  unfold fixCount countFirst
  congr 1
  refine List.filter_congr fun p hp => ?_
  rw [List.mem_range] at hp
  rw [List.getD_eq_getElem _ _ (by simpa [Firsts.firsts] using hp)]
  simp [Firsts.firsts]

/-! ## The fixed no-instance -/

theorem writeNoHS_spec {B : ℕ} (hB : 1 < B) :
    Spec B (fun _ => True) writeNoHS (fun σ σ' => σ'.out = σ.out ++ [0, 0, 1, 0, 1]) 10 := by
  run_vcg
  simp

theorem word_noInst : word noInst 1 = [0, 0, 1, 0, 1] := by
  rw [Form.word_eq]
  simp [noInst, Form.restSets, bitsNat, digit]

end Lax496464Proofs.WHierarchy.HittingSet.WSHSProg
