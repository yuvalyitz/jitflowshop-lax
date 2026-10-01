import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetMath
import Lax496464Proofs.WHierarchy.Machine.ReadTape

/-! # Multicoloured Clique to p-Clique: the IMP+ program

Read the tape into `a`, compute the declared length `3 + n + 2m` of the graph block, write the
block, and write the last entry. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetMath

abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- The body of the copy loop. -/
def copyBody : Com := .seq (.write (.get "a" (V "f_i"))) (bump "f_i")

/-- Writes `a[0], …, a[f_L - 1]`. -/
def copyLoop : Com := .seq (.assign "f_i" (.lit 0)) (.while (.lt (V "f_i") (V "f_L")) copyBody)

/-- The block length `3 + a[0] + 2 a[1]`. -/
def lenExpr : Expr := .add (.add (.lit 3) (.get "a" (.lit 0))) (.mul (.lit 2) (.get "a" (.lit 1)))

/-- **The program.** -/
def prog : Com :=
  .seq readTape (.seq (.assign "f_L" lenExpr)
    (.seq copyLoop (.write (.get "a" (.sub (V "rt_n") (.lit 1))))))

/-- The copy invariant. -/
def CI (x : List ℕ) (L : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "f_L" = L ∧ σ.vars "f_i" ≤ L ∧ σ.out = x.take (σ.vars "f_i")

theorem take_succ_getD (x : List ℕ) {i : ℕ} (h : i < x.length) :
    x.take (i + 1) = x.take i ++ [x.getD i 0] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp

theorem getD_lt {x : List ℕ} {B i : ℕ} (hB : ∀ v ∈ x, v < B) (h0 : 0 < B) : x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact hB _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]; exact h0

theorem copyBody_spec {x : List ℕ} {L B : ℕ} (hL : L ≤ x.length) (hB : ∀ v ∈ x, v < B)
    (hxB : x.length < B) :
    Spec B (fun σ => CI x L σ ∧ σ.vars "f_i" < L) copyBody
      (fun σ σ' => CI x L σ' ∧ σ'.vars "f_i" = σ.vars "f_i" + 1) 12 := by
  unfold copyBody
  refine Spec.pre (P := fun σ => CI x L σ ∧ σ.vars "f_i" < L ∧
    x.getD (σ.vars "f_i") 0 < B ∧
    x.take (σ.vars "f_i" + 1) = x.take (σ.vars "f_i") ++ [x.getD (σ.vars "f_i") 0]) ?_ ?_
  · run_vcg
    all_goals (simp only [CI] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨hI, hlt⟩
    exact ⟨hI, hlt, getD_lt hB (by omega), take_succ_getD x (by omega)⟩

theorem copyLoop_spec {x : List ℕ} {L B : ℕ} (hL : L ≤ x.length) (hB : ∀ v ∈ x, v < B)
    (hxB : x.length < B) :
    Spec B (fun σ => CI x L (σ.setVar "f_i" 0)) copyLoop
      (fun _ σ' => CI x L σ' ∧ σ'.vars "f_i" = L) (16 * L + 6) :=
  Spec.forRangeZero "f_i" "f_L" (CI x L) L 12 (by omega) (fun _ h => h.2.2.1)
    (fun _ h => h.2.1) (copyBody_spec hL hB hxB)

theorem last_eq_getD {x : List ℕ} (h : x ≠ []) : x.getD (x.length - 1) 0 = x.getLast?.getD 0 := by
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · exact absurd rfl h
  · simp

/-- **The run.** On a word whose declared block fits in it, the program writes `forget x`. -/
theorem prog_spec (x : List ℕ) (σ0 : Env) {B : ℕ} (hB : ∀ v ∈ x, v < B) (hxB : x.length + 1 < B)
    (hL : blockLen x ≤ x.length) (hne : x ≠ [])
    (hinp : σ0.inp = x.length :: x) (ha : σ0.arrs "a" = List.replicate x.length 0)
    (hout : σ0.out = []) :
    Spec B (fun σ => σ = σ0) prog (fun _ σ' => σ'.out = forget x)
      (32 * x.length + 60) := by
  have hL' : 3 + x.getD 0 0 + 2 * x.getD 1 0 ≤ x.length := hL
  have hlast := last_eq_getD hne
  have hlen1 : 1 ≤ x.length := by
    rcases x with _ | ⟨a, t⟩
    · exact absurd rfl hne
    · simp
  have hr := readTape_spec x σ0 (fun v hv => hB v hv) (by omega) hinp ha
  have hA : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [])
      (.assign "f_L" lenExpr)
      (fun σ σ' => σ' = σ.setVar "f_L" (blockLen x)) 20 := by
    have h0 : x.getD 0 0 < B := getD_lt hB (by omega)
    have h1 : x.getD 1 0 < B := getD_lt hB (by omega)
    refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ 3 + x.getD 0 0 + 2 * x.getD 1 0 ≤ x.length ∧
      x.length + 1 < B) ?_ (fun σ h => ⟨h.1, hL', hxB⟩)
    unfold lenExpr
    run_vcg
    all_goals (simp_all [blockLen]; try omega)
  have hC := copyLoop_spec (x := x) (L := blockLen x) hL (fun v hv => hB v hv) (by omega)
  have hW : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.out = x.take (blockLen x))
      (.write (.get "a" (.sub (V "rt_n") (.lit 1))))
      (fun _ σ' => σ'.out = forget x) 10 := by
    refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.out = x.take (blockLen x) ∧ 1 ≤ x.length ∧ x.length + 1 < B ∧
        x.getD (x.length - 1) 0 < B) ?_ (fun σ h => ⟨h.1, h.2.1, h.2.2, hlen1, hxB,
          getD_lt hB (by omega)⟩)
    run_vcg
    all_goals (simp_all [forget]; try omega)
  have hC' : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [] ∧
        σ.vars "f_L" = blockLen x) copyLoop
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "rt_n" = x.length ∧
        σ'.out = x.take (blockLen x)) (16 * blockLen x + 6) := by
    refine Spec.post (Spec.pre hC.frame ?_) ?_
    · rintro σ ⟨ha', _, ho, hLv⟩
      refine ⟨by simp [Env.setVar, ha'], by simp [Env.setVar, hLv], by simp [Env.setVar], ?_⟩
      simp [Env.setVar, ho]
    · rintro σ σ' ⟨_, hn, _, _⟩ ⟨⟨⟨ha', _, _, ho⟩, hi⟩, hv, -⟩
      refine ⟨ha', ?_, by rw [ho, hi]⟩
      rw [hv "rt_n" (by simp [copyLoop, copyBody, bump, Com.wvars]), hn]
  have hCW := Spec.seq hC' hW (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  have hACW : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [])
      (.seq (.assign "f_L" lenExpr) (.seq copyLoop (.write (.get "a" (.sub (V "rt_n") (.lit 1))))))
      (fun _ σ' => σ'.out = forget x) (20 + (16 * blockLen x + 6 + 10)) := by
    refine Spec.seq hA hCW ?_ (fun _ _ _ _ _ h => h)
    rintro σ σ' ⟨ha', hn, ho⟩ rfl
    exact ⟨by simp [Env.setVar, ha'], by simp [Env.setVar, hn], by simp [Env.setVar, ho],
      by simp [Env.setVar]⟩
  unfold prog
  refine Spec.mono (Spec.seq hr hACW ?_ (fun _ _ _ _ _ h => h)) (by omega)
  rintro σ σ' rfl ⟨ha', hn, _, ho, _⟩
  exact ⟨ha', hn, by rw [ho, hout]⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ForgetProg
