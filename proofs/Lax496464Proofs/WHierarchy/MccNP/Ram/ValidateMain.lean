import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateMat

/-!
# The validator around the matrix loop

The checks that the matrix fits into the word and follows a zero, and, after the matrix, the run
of ones for `k` ending in the last entry `0`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {B : ℕ} {x : List ℕ}

theorem finalGate_core (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_k" ≤ x.length ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) finalGate
      (fun σ σ' => (σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_k" + 1 = x.length ∧
          x.getD (σ.vars "v_k") 0 = 0)) ∧ (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) 30 := by
  have hB0 : 0 < B := by omega
  unfold finalGate
  run_vcg
  all_goals (
    have ha := ‹σ.arrs "a" = x›
    have hL := ‹σ.vars "L" = x.length›
    have hk := ‹σ.vars "v_k" ≤ x.length›
    have hok := ‹σ.vars "ok" = 0 ∨ σ.vars "ok" = 1›
    first
    | omega
    | (rw [ha]; omega)
    | (rw [ha]; exact getD_lt_B hy hB0 _)
    | (simp_all [Env.setVar]; try omega))

theorem finalGate_frm (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_k" ≤ x.length ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) finalGate
      (fun σ σ' => ((σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_k" + 1 = x.length ∧
          x.getD (σ.vars "v_k") 0 = 0)) ∧ (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ∧
          Frm ["ok"] σ σ') 30 := by
  refine Spec.frm (finalGate_core hy hB) _ ?_ ?_ ?_ ?_
  · intro z hz
    simp [finalGate, fail, Com.wvars] at hz
    simp [hz]
  · simp [finalGate, fail, Com.warrs]
  · simp [finalGate, fail, Com.reads]
  · simp [finalGate, fail, Com.NoWrite]

/-- After the matrix loop: the second run of ones and the final gate. -/
theorem runFinal_spec (N : ℕ) (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) (.seq (runFrom "v_k" (V "v_s")) finalGate)
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧
          N + 1 + N * N + tw x (N + 1 + N * N) + 1 = x.length ∧
          x.getD (N + 1 + N * N + tw x (N + 1 + N * N)) 0 = 0)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧
        Frm ["v_k", "v_go", "ok"] σ σ'') (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30) := by
  have h2 := runFrom_spec (B := B) (y := x) "v_k" (by decide) (by decide) hy hB (V "v_s")
    (N + 1 + N * N) (by omega)
  have h3 := finalGate_frm hy hB
  refine Spec.seq (P := fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
      σ.vars "v_s" = N + 1 + N * N ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
    (h2.pre ?_) h3 ?_ ?_
  · rintro σ ⟨ha, hL, hs, -⟩
    refine ⟨ha, hL, ?_⟩
    rw [← hs]
    exact evalB_var (by rw [hs]; omega)
  · rintro σ σ' ⟨ha, hL, hs, hok⟩ ⟨⟨hk, hgo⟩, hf⟩
    have hL' : σ'.vars "L" = x.length := by rw [hf.2.2.2 "L" (by simp)]; exact hL
    have ha' : σ'.arrs "a" = x := by rw [congrFun hf.1 "a"]; exact ha
    have hok' : σ'.vars "ok" = σ.vars "ok" := hf.2.2.2 "ok" (by simp)
    have := tw_le' (y := x) (s := N + 1 + N * N) (by omega)
    exact ⟨ha', hL', by omega, by rw [hok']; exact hok⟩
  · rintro σ σ' σ'' ⟨ha, hL, hs, hok⟩ ⟨⟨hk, hgo⟩, hf⟩ ⟨⟨hi, hok2⟩, hf2⟩
    have hok' : σ'.vars "ok" = σ.vars "ok" := hf.2.2.2 "ok" (by simp)
    refine ⟨⟨?_, hok2⟩, ?_⟩
    · rw [hi, hok', hk]
    · refine (hf.mono (by simp)).trans (hf2.mono (by simp))

/-- The whole rest once the matrix fits (`afterMat`). -/
theorem afterMat_spec (N : ℕ) (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) afterMat
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ (∀ t < N * N, Cell x N t) ∧
          N + 1 + N * N + tw x (N + 1 + N * N) + 1 = x.length ∧
          x.getD (N + 1 + N * N + tw x (N + 1 + N * N)) 0 = 0)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧
        Frm ["v_t", "v_u", "v_w", "v_c", "v_d", "ok", "v_k", "v_go"] σ σ'')
      (204 * (N * N) + 6 + (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30)) := by
  have h1 := matLoop_spec (B := B) (x := x) N hy hB hN
  have h2 := runFinal_spec (B := B) (x := x) N hy hB hN
  unfold afterMat
  refine Spec.seq (P := fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
    (h1.pre (fun σ h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩)) h2 ?_ ?_
  · rintro σ σ' ⟨ha, hL, hn, hnn, hs, hok⟩ ⟨⟨-, hok'⟩, hf⟩
    refine ⟨by rw [congrFun hf.1 "a"]; exact ha, by rw [hf.2.2.2 "L" (by simp)]; exact hL,
      by rw [hf.2.2.2 "v_s" (by simp)]; exact hs, hok'⟩
  · rintro σ σ' σ'' ⟨ha, hL, hn, hnn, hs, hok⟩ ⟨⟨hiff, hok1⟩, hf⟩ ⟨⟨hiff2, hok2⟩, hf2⟩
    refine ⟨⟨?_, hok2⟩, ?_⟩
    · rw [hiff2, hiff]
      tauto
    · exact (hf.mono (by simp)).trans (hf2.mono (by simp))

/-- The machine's form of validity at `n = N`. -/
def VC (x : List ℕ) (N : ℕ) : Prop :=
  N + 1 + N * N < x.length ∧ x.getD N 0 = 0 ∧ (∀ t < N * N, Cell x N t) ∧
    N + 1 + N * N + tw x (N + 1 + N * N) + 1 = x.length ∧
    x.getD (N + 1 + N * N + tw x (N + 1 + N * N)) 0 = 0

theorem valid_iff_VC (x : List ℕ) : Shape.Valid x ↔ VC x (Shape.order x) := valid_iff x

/-- The ok-flag frame of the whole tail. -/
abbrev SAll : List String := ["v_t", "v_u", "v_w", "v_c", "v_d", "ok", "v_k", "v_go"]

theorem condA_eval {N : ℕ} {σ : Env} (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (ha : σ.arrs "a" = x) (hn : σ.vars "v_n" = N) (hN : N < x.length) :
    (Cond.eq (.get "a" (V "v_n")) (.lit 0)).evalB B σ = some (x.getD N 0 == 0) := by
  have hB0 : 0 < B := by omega
  have hv : (V "v_n").evalB B σ = some (σ.vars "v_n") := evalB_var (by rw [hn]; omega)
  rw [hn] at hv
  refine evalB_condEq (m := x.getD N 0) (n := 0) ?_ (evalB_lit hB0)
  refine evalB_get (k := N) hv ?_ (getD_lt_B hy hB0 _)
  rw [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hN]
  rfl

theorem fail_spec {P : Env → Prop} (hB : 1 < B) :
    Spec B P fail (fun σ σ' => σ' = σ.setVar "ok" 0) (1 + 1) :=
  Spec.assign (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))

/-- Cost of `checkA`. -/
def KA (x : List ℕ) (N : ℕ) : ℕ :=
  1 + 4 + (204 * (N * N) + 6 + (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30))

theorem checkA_spec (N : ℕ) (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) checkA
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ x.getD N 0 = 0 ∧
          (∀ t < N * N, Cell x N t) ∧
          N + 1 + N * N + tw x (N + 1 + N * N) + 1 = x.length ∧
          x.getD (N + 1 + N * N + tw x (N + 1 + N * N)) 0 = 0)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧ Frm SAll σ σ'')
      (KA x N) := by
  have hcA := afterMat_spec (B := B) N hy hB hN
  have hcf := fail_spec (B := B) (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
    σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
    (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) (by omega)
  unfold checkA
  refine Spec.ite (P := fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) ?_ ?_ ?_
  · intro σ ⟨ha, hL, hn, hnn, hs, hok⟩
    exact ⟨_, condA_eval hy hB ha hn (by omega)⟩
  · refine (Spec.mono hcA (K' := 204 * (N * N) + 6 +
      (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30)) le_rfl).conseq (fun σ h => h.1) ?_ le_rfl
    intro σ σ' ⟨⟨ha, hL, hn, hnn, hs, hok⟩, hc⟩ hq
    rw [condA_eval hy hB ha hn (by omega)] at hc
    have hc' : x.getD N 0 = 0 := by simpa using hc
    obtain ⟨⟨h1, h2⟩, hf⟩ := hq
    refine ⟨⟨?_, h2⟩, hf.mono (by simp)⟩
    rw [h1]; tauto
  · refine (Spec.mono hcf (K' := 204 * (N * N) + 6 +
      (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30)) (by omega)).conseq (fun σ h => h.1) ?_ le_rfl
    intro σ σ' ⟨⟨ha, hL, hn, hnn, hs, hok⟩, hc⟩ hq
    rw [condA_eval hy hB ha hn (by omega)] at hc
    have hc' : ¬ x.getD N 0 = 0 := by simpa using hc
    subst hq
    refine ⟨⟨?_, by simp⟩, ?_⟩
    · simp; tauto
    · refine ⟨rfl, rfl, rfl, ?_⟩
      intro z hz
      simp [Env.setVar]
      intro h; subst h; simp at hz

/-- Cost of `checkS`, in the length alone. -/
def KS0 (x : List ℕ) : ℕ :=
  1 + 4 + (204 * x.length + 6 + (1 + 1 + 2 + (24 * (x.length + 1) + 4) + 30))

def KS (x : List ℕ) : ℕ := 1 + 3 + KS0 x

theorem checkS_spec (N : ℕ) (hy : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hNB : N + 1 + N * N < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) checkS
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ VC x N)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧ Frm SAll σ σ'')
      (KS x) := by
  have hcf := fail_spec (B := B) (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
    σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
    (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) (by omega)
  unfold checkS KS
  refine Spec.ite (P := fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ σ.vars "v_s" = N + 1 + N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) ?_ ?_ ?_
  · intro σ ⟨ha, hL, hn, hnn, hs, hok⟩
    exact ⟨_, evalB_condLt (evalB_var (by rw [hs]; exact hNB)) (evalB_var (by rw [hL]; omega))⟩
  · rintro σ ⟨⟨ha, hL, hn, hnn, hs, hok⟩, hc⟩
    have hc' : (Cond.lt (V "v_s") (V "L")).evalB B σ = some (decide (σ.vars "v_s" < σ.vars "L")) :=
      evalB_condLt (evalB_var (by rw [hs]; exact hNB)) (evalB_var (by rw [hL]; omega))
    rw [hc'] at hc
    have hlt : N + 1 + N * N < x.length := by
      have : decide (σ.vars "v_s" < σ.vars "L") = true := by simpa using hc
      simp only [decide_eq_true_eq] at this
      omega
    obtain ⟨σ', hr, ⟨h1, h2⟩, hf⟩ := checkA_spec N hy hB hlt σ ⟨ha, hL, hn, hnn, hs, hok⟩
    refine ⟨σ', hr.mono (by unfold KA KS0; omega), ⟨?_, h2⟩, hf⟩
    rw [h1]
    unfold VC
    tauto
  · rintro σ ⟨⟨ha, hL, hn, hnn, hs, hok⟩, hc⟩
    have hc' : (Cond.lt (V "v_s") (V "L")).evalB B σ = some (decide (σ.vars "v_s" < σ.vars "L")) :=
      evalB_condLt (evalB_var (by rw [hs]; exact hNB)) (evalB_var (by rw [hL]; omega))
    rw [hc'] at hc
    have hlt : ¬ N + 1 + N * N < x.length := by
      have : decide (σ.vars "v_s" < σ.vars "L") = false := by simpa using hc
      simp only [decide_eq_false_iff_not] at this
      omega
    obtain ⟨σ', hr, hq⟩ := hcf σ ⟨ha, hL, hn, hnn, hs, hok⟩
    subst hq
    refine ⟨_, hr.mono (by unfold KS0; omega), ⟨?_, by simp⟩, ?_⟩
    · simp only [vars_setVar, if_true]
      constructor
      · intro h; omega
      · rintro ⟨-, h, -⟩; exact absurd h hlt
    · refine ⟨rfl, rfl, rfl, ?_⟩
      intro z hz
      simp [Env.setVar]
      intro h; subst h; simp at hz

end Lax496464Proofs.WHierarchy.MccNP.Validate
