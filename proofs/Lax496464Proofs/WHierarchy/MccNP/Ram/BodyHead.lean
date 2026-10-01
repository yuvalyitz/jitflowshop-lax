import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyPass

/-!
# The header of `body`

The loop over a run of ones, and `header`, which reads `n` and `k` off the word and sets the
positions of the matrix and the number `N = k n` of vertices.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRow Lax496464Proofs.WHierarchy.MccNP.Ram.BodyPass

/-- The invariant of a run of ones. -/
def RunI (cnt off : String) (A : List ℕ) (o r : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = A ∧ σ.vars off = o ∧ σ.vars cnt ≤ r

theorem getElem?_of_lt {A : List ℕ} {k : ℕ} (h : k < A.length) : A[k]? = some (A.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem runOnes_cond {B : ℕ} (cnt off : String) (_hne : cnt ≠ off) {A : List ℕ} {o r : ℕ}
    (hA : ∀ v ∈ A, v < B) (hlt : o + r < A.length) (hor : o + r < B) (h1B : 1 < B)
    {σ : Env} (hI : RunI cnt off A o r σ) :
    (Cond.eq (.get "a" (.add (V off) (V cnt))) (.lit 1)).evalB B σ =
      some (A.getD (o + σ.vars cnt) 0 == 1) := by
  obtain ⟨ha, ho, hc⟩ := hI
  have hk : o + σ.vars cnt < A.length := by omega
  have hv : A.getD (o + σ.vars cnt) 0 < B := by
    apply hA
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact List.getElem_mem _
  refine evalB_condEq (m := A.getD (o + σ.vars cnt) 0) (n := 1) ?_ (evalB_lit h1B)
  have hi : (V off |>.add (V cnt)).evalB B σ = some (o + σ.vars cnt) := by
    have := evalB_bin (op := .add) (evalB_var (B := B) (x := off) (σ := σ) (by omega)) (evalB_var (B := B) (x := cnt) (σ := σ) (by omega)) (by simp; omega)
    simpa [ho] using this
  exact evalB_get hi (by rw [ha]; exact getElem?_of_lt hk) hv

theorem runOnes_value {B : ℕ} (cnt off : String) (hne : cnt ≠ off) {A : List ℕ} {o r : ℕ}
    (hA : ∀ v ∈ A, v < B) (hlt : o + r < A.length) (hor : o + r < B) (h1B : 1 < B)
    (hones : ∀ i < r, A.getD (o + i) 0 = 1) (hstop : A.getD (o + r) 0 ≠ 1) :
    Spec B (fun σ => σ.arrs "a" = A ∧ σ.vars off = o ∧ σ.vars cnt = 0) (runOnes cnt off)
      (fun _ σ' => σ'.vars cnt = r) (11 * r + 7) := by
  unfold runOnes
  have hbody : Spec B (fun σ => RunI cnt off A o r σ ∧
      (Cond.eq (.get "a" (.add (V off) (V cnt))) (.lit 1)).evalB B σ = some true) (bump cnt)
      (fun σ σ' => RunI cnt off A o r σ' ∧ r - σ'.vars cnt < r - σ.vars cnt) 4 := by
    intro σ ⟨hI, hc⟩
    rw [runOnes_cond cnt off hne hA hlt hor h1B hI] at hc
    have hc' : A.getD (o + σ.vars cnt) 0 = 1 := by simpa using hc
    obtain ⟨ha, ho, hcl⟩ := hI
    have hlt' : σ.vars cnt < r := by
      rcases Nat.lt_or_ge (σ.vars cnt) r with h | h
      · exact h
      · have : σ.vars cnt = r := by omega
        rw [this] at hc'; exact absurd hc' hstop
    refine ⟨σ.setVar cnt (σ.vars cnt + 1), ?_, ?_⟩
    · refine (Run.assign (v := σ.vars cnt + 1) ?_).mono (by simp [Expr.size])
      exact evalB_bin (evalB_var (by omega)) (evalB_lit h1B) (by simp; omega)
    · simp [RunI, Env.setVar, ha, ho, hne.symm]; omega
  have hw := Spec.while_count (B := B)
    (P := fun σ => σ.arrs "a" = A ∧ σ.vars off = o ∧ σ.vars cnt = 0)
    (b := Cond.eq (.get "a" (.add (V off) (V cnt))) (.lit 1)) (c := bump cnt)
    (K := 11 * r + 7) (RunI cnt off A o r) (fun σ => r - σ.vars cnt) 4
    (fun σ hI => ⟨_, runOnes_cond cnt off hne hA hlt hor h1B hI⟩) hbody
    (fun σ h => ⟨h.1, h.2.1, by rw [h.2.2]; omega⟩)
    (fun σ h => by simp [h.2.2])
  refine hw.post fun σ σ' _ ⟨hI, hf⟩ => ?_
  rw [runOnes_cond cnt off hne hA hlt hor h1B hI] at hf
  have hf' : ¬ A.getD (o + σ'.vars cnt) 0 = 1 := by simpa using hf
  have hcl := hI.2.2
  rcases Nat.lt_or_ge (σ'.vars cnt) r with h | h
  · exact absurd (hones _ h) hf'
  · omega

theorem runOnes_spec {B : ℕ} (cnt off : String) (hne : cnt ≠ off) {A : List ℕ} {o r : ℕ}
    (hA : ∀ v ∈ A, v < B) (hlt : o + r < A.length) (hor : o + r < B) (h1B : 1 < B)
    (hones : ∀ i < r, A.getD (o + i) 0 = 1) (hstop : A.getD (o + r) 0 ≠ 1) :
    Spec B (fun σ => σ.arrs "a" = A ∧ σ.vars off = o ∧ σ.vars cnt = 0) (runOnes cnt off)
      (fun σ σ' => σ'.vars cnt = r ∧ Keep [cnt] σ σ' ∧ σ'.out = σ.out) (11 * r + 7) := by
  refine Spec.post (Spec.keep (runOnes_value cnt off hne hA hlt hor h1B hones hstop) [cnt]
    ?_ ?_ ?_).frame ?_
  · intro y hy; simpa [runOnes, bump, Com.wvars] using hy
  · simp [runOnes, bump, Com.warrs]
  · simp [runOnes, bump, Com.reads]
  · rintro σ σ' _ ⟨⟨hq, hk⟩, -, -, -, ho⟩
    exact ⟨hq, hk, ho (by simp [runOnes, bump, Com.NoWrite])⟩

/-- The leading ones of a word. -/
theorem getD_takeWhile_run (l : List ℕ) (i : ℕ) (h : i < (l.takeWhile fun v => v == 1).length) :
    l.getD i 0 = 1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    by_cases ha : a = 1
    · subst ha
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.takeWhile_cons, beq_self_eq_true, if_true, List.length_cons] at h
        simpa using ih i (by omega)
    · simp [ha] at h

theorem getD_lt_order {x : List ℕ} {i : ℕ} (h : i < order x) : x.getD i 0 = 1 :=
  getD_takeWhile_run x i h

theorem getD_lt_kOf {x : List ℕ} {i : ℕ} (h : i < kOf x) :
    x.getD (order x + 1 + order x * order x + i) 0 = 1 := by
  have := getD_takeWhile_run (x.drop (order x + 1 + order x * order x)) i h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this

/-- The scalars the header assigns. -/
def headVars : List String := ["b_o", "b_n", "b_base", "b_K0", "b_k", "b_N"]

theorem entries_le_one {x : List ℕ} (hx : Valid x) : ∀ v ∈ x, v ≤ 1 := by
  intro v hv
  rw [← Shape.word_decode hx] at hv
  simp only [Lax496464.WH_F1_IndependentSetMatrix.word, List.mem_map] at hv
  obtain ⟨b, -, rfl⟩ := hv
  unfold Lax496464.WH_F1_IndependentSetMatrix.bitNat
  split <;> omega

set_option maxHeartbeats 1000000 in
theorem header_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B) :
    Spec B (fun σ => σ.arrs "a" = x) header
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_k" = kOf x ∧ σ'.vars "b_K0" = order x + 1 + order x * order x ∧
        Keep headVars σ σ' ∧ σ'.out = σ.out) (11 * (order x + kOf x) + 40) := by
  have hlen := hx.2.1
  have hsq := sq_bound hx
  have hA : ∀ v ∈ x, v < B := fun v hv => by have := entries_le_one hx v hv; omega
  have h1 := runOnes_spec (B := B) "b_n" "b_o" (by decide) (A := x) (o := 0) (r := order x)
    hA (by omega) (by omega) (by omega) (fun i hi => by simpa using getD_lt_order hi)
    (by simpa using (by rw [hx.1]; omega : x.getD (order x) 0 ≠ 1))
  have h2 := runOnes_spec (B := B) "b_k" "b_o" (by decide) (A := x)
    (o := order x + 1 + order x * order x) (r := kOf x)
    hA (by omega) (by omega) (by omega) (fun i hi => getD_lt_kOf hi)
    (by rw [hx.2.2.1]; omega)
  unfold header
  run_vcg [h1, h2]
  all_goals (simp only [Keep, Ctx, headVars] at *; simp_all [Env.setVar, nOf]; try omega)

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead
