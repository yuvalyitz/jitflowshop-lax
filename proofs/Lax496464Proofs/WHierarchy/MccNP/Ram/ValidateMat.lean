import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateRun

/-!
# The Matrix Loop of the Validator

One matrix cell per turn: each entry is `0` or `1`, the diagonal is zero, and the matrix is
symmetric.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {B : ℕ} {x : List ℕ}

theorem mat_facts {n t : ℕ} (ht : t < n * n) :
    t / n < n ∧ t % n < n ∧ t / n * n ≤ t ∧ t - t / n * n = t % n ∧
      t % n * n + t / n < n * n ∧ (t - t / n * n) * n + t / n < n * n ∧ t / n ≤ t := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at ht
    · exact h
  have h1 : t / n < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at ht; exact ht)
  have h2 : t % n < n := Nat.mod_lt _ hn
  have h3 : t / n * n + t % n = t := Nat.div_add_mod' t n
  have h4 : t - t / n * n = t % n := by omega
  refine ⟨h1, h2, by omega, h4, ?_, ?_, Nat.div_le_self _ _⟩
  · have := Validate.lt_sq (u := t % n) (v := t / n) h2 h1
    exact this
  · rw [h4]
    exact Validate.lt_sq (u := t % n) (v := t / n) h2 h1

/-- Precondition of the read phase, with the arithmetic facts precomputed. -/
def ReadPre (N : ℕ) (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "v_n" = N ∧ σ.vars "v_t" < N * N ∧
  σ.vars "v_t" / σ.vars "v_n" < σ.vars "v_n" ∧
  σ.vars "v_t" % σ.vars "v_n" < σ.vars "v_n" ∧
  σ.vars "v_t" / σ.vars "v_n" * σ.vars "v_n" ≤ σ.vars "v_t" ∧
  σ.vars "v_t" - σ.vars "v_t" / σ.vars "v_n" * σ.vars "v_n" = σ.vars "v_t" % σ.vars "v_n" ∧
  σ.vars "v_t" % σ.vars "v_n" * σ.vars "v_n" + σ.vars "v_t" / σ.vars "v_n" <
    σ.vars "v_n" * σ.vars "v_n" ∧
  σ.vars "v_t" / σ.vars "v_n" ≤ σ.vars "v_t"

theorem readPre_of {N : ℕ} {σ : Env} (ha : σ.arrs "a" = x) (hn : σ.vars "v_n" = N)
    (ht : σ.vars "v_t" < N * N) : ReadPre N x σ := by
  have := mat_facts (n := σ.vars "v_n") (t := σ.vars "v_t") (by rw [hn]; exact ht)
  exact ⟨ha, hn, ht, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2⟩

theorem getElem?_getD_lt_B (hy : ∀ v ∈ x, v < B) (hB0 : 0 < B) (k : ℕ) : x[k]?.getD 0 < B := by
  have := getD_lt_B hy hB0 k
  simpa [List.getD_eq_getElem?_getD] using this

theorem matRead_spec (N : ℕ) (hx : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (ReadPre N x) matRead
      (fun σ σ' => σ'.vars "v_c" = x.getD (N + 1 + σ.vars "v_t") 0 ∧
        σ'.vars "v_d" = x.getD (N + 1 + (σ.vars "v_t" % N * N + σ.vars "v_t" / N)) 0 ∧
        σ'.vars "v_u" = σ.vars "v_t" / N ∧ σ'.vars "v_w" = σ.vars "v_t" % N)
      100 := by
  have hB0 : 0 < B := by omega
  unfold matRead
  run_vcg
  all_goals (
    obtain ⟨ha, hn, ht, f1, f2, f3, f4, f5, f7⟩ := ‹ReadPre N x σ›
    rw [hn] at f1 f2 f3 f4 f5 f7
    try simp [Env.setVar, ha, hn, f4]
    try refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | omega
      | exact getElem?_getD_lt_B hx hB0 _
      | (congr 2; omega)
      | exact (lt_of_le_of_lt (Nat.le_add_right _ _) f5).trans (by omega))

theorem matGates_core (hB : 2 < B) :
    Spec B (fun σ => (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧ σ.vars "v_c" < B ∧ σ.vars "v_d" < B ∧
        σ.vars "v_u" < B ∧ σ.vars "v_w" < B) matGates
      (fun σ σ' => (σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_c" < 2 ∧
          σ.vars "v_c" = σ.vars "v_d" ∧ (σ.vars "v_u" = σ.vars "v_w" → σ.vars "v_c" = 0))) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) 60 := by
  unfold matGates
  run_vcg
  all_goals (simp_all [Env.setVar]; try omega)

theorem matRead_frm (N : ℕ) (hx : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (ReadPre N x) matRead
      (fun σ σ' => (σ'.vars "v_c" = x.getD (N + 1 + σ.vars "v_t") 0 ∧
        σ'.vars "v_d" = x.getD (N + 1 + (σ.vars "v_t" % N * N + σ.vars "v_t" / N)) 0 ∧
        σ'.vars "v_u" = σ.vars "v_t" / N ∧ σ'.vars "v_w" = σ.vars "v_t" % N) ∧
        Frm ["v_u", "v_w", "v_c", "v_d"] σ σ')
      100 := by
  refine Spec.frm (matRead_spec N hx hB hN) _ ?_ ?_ ?_ ?_
  · intro z hz
    simp [matRead, Com.wvars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp [matRead, Com.warrs]
  · simp [matRead, Com.reads]
  · simp [matRead, Com.NoWrite]

theorem matGates_frm (hB : 2 < B) :
    Spec B (fun σ => (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧ σ.vars "v_c" < B ∧ σ.vars "v_d" < B ∧
        σ.vars "v_u" < B ∧ σ.vars "v_w" < B) matGates
      (fun σ σ' => ((σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_c" < 2 ∧
          σ.vars "v_c" = σ.vars "v_d" ∧ (σ.vars "v_u" = σ.vars "v_w" → σ.vars "v_c" = 0))) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ∧ Frm ["ok"] σ σ') 60 := by
  refine Spec.frm (matGates_core hB) _ ?_ ?_ ?_ ?_
  · intro z hz
    simp [matGates, fail, Com.wvars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp [matGates, fail, Com.warrs]
  · simp [matGates, fail, Com.reads]
  · simp [matGates, fail, Com.NoWrite]

theorem bump_frm (v : String) :
    Spec B (fun σ => σ.vars v + 1 < B) (bump v)
      (fun σ σ' => σ'.vars v = σ.vars v + 1 ∧ Frm [v] σ σ') 4 := by
  intro σ h
  refine ⟨σ.setVar v (σ.vars v + 1), ?_, ?_⟩
  · have : (Expr.bin .add (V v) (.lit 1)).evalB B σ = some (σ.vars v + 1) :=
      evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) h
    exact (Run.assign (x := v) this).mono (by simp)
  · refine ⟨by simp, rfl, rfl, rfl, ?_⟩
    intro z hz
    simp only [List.mem_singleton] at hz
    simp [Env.setVar, hz]

/-- The invariant of the matrix loop; `ok0` is the value of `ok` on entry. -/
def MI (x : List ℕ) (N ok0 : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧ σ.vars "v_t" ≤ N * N ∧
    (σ.vars "ok" = 1 ↔ (ok0 = 1 ∧ ∀ t < σ.vars "v_t", Cell x N t)) ∧
    (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)

theorem cell_iff {N t c d u w : ℕ} {x : List ℕ} (hc : c = x.getD (N + 1 + t) 0)
    (hd : d = x.getD (N + 1 + (t % N * N + t / N)) 0) (hu : u = t / N) (hw : w = t % N) :
    (c < 2 ∧ c = d ∧ (u = w → c = 0)) ↔ Cell x N t := by
  subst hc hd hu hw
  unfold Cell
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem matBody_spec (N ok0 : ℕ) (hx : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (fun σ => MI x N ok0 σ ∧ σ.vars "v_t" < N * N) matBody
      (fun σ σ' => MI x N ok0 σ' ∧ σ'.vars "v_t" = σ.vars "v_t" + 1) 200 := by
  have hB0 : 0 < B := by omega
  have h1 := (matRead_frm (B := B) N hx hB hN).pre
    (P' := fun σ => MI x N ok0 σ ∧ σ.vars "v_t" < N * N)
    (fun σ ⟨hI, ht⟩ => readPre_of hI.1 hI.2.1 ht)
  have h2 := matGates_frm (B := B) (by omega)
  have h3 := bump_frm (B := B) "v_t"
  have h23 : Spec B (fun σ => ((σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧ σ.vars "v_c" < B ∧
        σ.vars "v_d" < B ∧ σ.vars "v_u" < B ∧ σ.vars "v_w" < B) ∧ σ.vars "v_t" + 1 < B)
      (.seq matGates (bump "v_t"))
      (fun σ σ'' => (σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_c" < 2 ∧
          σ.vars "v_c" = σ.vars "v_d" ∧ (σ.vars "v_u" = σ.vars "v_w" → σ.vars "v_c" = 0))) ∧
        (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1) ∧ σ''.vars "v_t" = σ.vars "v_t" + 1 ∧
        Frm ["ok", "v_t"] σ σ'') (60 + 4) := by
    refine Spec.seq (P := fun σ => ((σ.vars "ok" = 0 ∨ σ.vars "ok" = 1) ∧ σ.vars "v_c" < B ∧
        σ.vars "v_d" < B ∧ σ.vars "v_u" < B ∧ σ.vars "v_w" < B) ∧ σ.vars "v_t" + 1 < B)
      (Q := fun σ σ' => ((σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ σ.vars "v_c" < 2 ∧
          σ.vars "v_c" = σ.vars "v_d" ∧ (σ.vars "v_u" = σ.vars "v_w" → σ.vars "v_c" = 0))) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ∧ Frm ["ok"] σ σ')
      (h2.pre (fun σ h => h.1)) h3 ?_ ?_
    · intro σ σ' hP hQ
      have := hQ.2.2.2.2 "v_t" (by simp)
      omega
    · intro σ σ' σ'' hP hQ hR
      have hok : σ''.vars "ok" = σ'.vars "ok" := hR.2.2.2.2 "ok" (by simp)
      have hvt : σ'.vars "v_t" = σ.vars "v_t" := hQ.2.2.2.2 "v_t" (by simp)
      refine ⟨by rw [hok]; exact hQ.1.1, by rw [hok]; exact hQ.1.2, by omega, ?_⟩
      exact (hQ.2.mono (by simp)).trans (hR.2.mono (by simp))
  unfold matBody
  refine Spec.mono (Spec.seq h1 h23 ?_ ?_) (by omega)
  · intro σ σ' ⟨hI, ht⟩ ⟨hq, hf⟩
    obtain ⟨-, -, -, -, -, hok⟩ := hI
    obtain ⟨hc, hd, hu, hw⟩ := hq
    have hcB : σ'.vars "v_c" < B := by rw [hc]; exact getD_lt_B hx hB0 _
    have hdB : σ'.vars "v_d" < B := by rw [hd]; exact getD_lt_B hx hB0 _
    have hok' : σ'.vars "ok" = σ.vars "ok" := hf.2.2.2 "ok" (by simp)
    have hvt : σ'.vars "v_t" = σ.vars "v_t" := hf.2.2.2 "v_t" (by simp)
    have := mat_facts (n := N) (t := σ.vars "v_t") ht
    refine ⟨⟨by rw [hok']; exact hok, hcB, hdB, ?_, ?_⟩, by omega⟩
    · rw [hu]; omega
    · rw [hw]; omega
  · intro σ σ' σ'' ⟨hI, ht⟩ ⟨hq, hf⟩ hr
    obtain ⟨ha, hn, hnn, hle, hokiff, hok01⟩ := hI
    obtain ⟨hc, hd, hu, hw⟩ := hq
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
    have hok' : σ'.vars "ok" = σ.vars "ok" := hf.2.2.2 "ok" (by simp)
    have hvt : σ'.vars "v_t" = σ.vars "v_t" := hf.2.2.2 "v_t" (by simp)
    have hcell := cell_iff (N := N) (t := σ.vars "v_t") hc hd hu hw
    have hnewt : σ''.vars "v_t" = σ.vars "v_t" + 1 := by
      have := hr4.2.2.2 "v_t"
      omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hr2⟩, hnewt⟩
    · exact (congrFun hr4.1 "a").trans ((congrFun hf.1 "a").trans ha)
    · rw [hr4.2.2.2 "v_n" (by simp), hf.2.2.2 "v_n" (by simp)]; exact hn
    · rw [hr4.2.2.2 "v_nn" (by simp), hf.2.2.2 "v_nn" (by simp)]; exact hnn
    · omega
    · rw [hr1, hok', hokiff, hcell, hnewt]
      constructor
      · rintro ⟨⟨h0, hall⟩, hcl⟩
        refine ⟨h0, fun t ht => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
        · exact hall t h
        · subst h; exact hcl
      · rintro ⟨h0, hall⟩
        exact ⟨⟨h0, fun t ht => hall t (by omega)⟩, hall _ (by omega)⟩

theorem matLoop_spec (N : ℕ) (hx : ∀ v ∈ x, v < B) (hB : x.length + 2 < B)
    (hN : N + 1 + N * N < x.length) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) matLoop
      (fun σ σ' => ((σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ ∀ t < N * N, Cell x N t)) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ∧
        Frm ["v_t", "v_u", "v_w", "v_c", "v_d", "ok"] σ σ')
      (204 * (N * N) + 6) := by
  have hNB : N * N < B := by omega
  have hcore := fun (ok0 : ℕ) => Spec.forRangeZero (B := B) (c := matBody) "v_t" "v_nn"
    (MI x N ok0) (N * N) 200 hNB (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1)
    (matBody_spec (B := B) N ok0 hx hB hN)
  have h1 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) matLoop
      (fun σ σ' => (σ'.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ ∀ t < N * N, Cell x N t)) ∧
        (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ((200 + 4) * (N * N) + 6) := by
    intro σ hσ
    obtain ⟨ha, hn, hnn, hok⟩ := hσ
    obtain ⟨σ', hr, hI, hxt⟩ := hcore (σ.vars "ok") σ (by
      refine ⟨by simpa using ha, by simpa using hn, by simpa using hnn, by simp, ?_, by simpa using hok⟩
      simp)
    obtain ⟨-, -, -, -, hiff, hok'⟩ := hI
    refine ⟨σ', hr, ?_, hok'⟩
    rw [hiff, hxt]
  refine Spec.frm (Spec.mono h1 (K' := 204 * (N * N) + 6) (by omega)) _ ?_ ?_ ?_ ?_
  · intro z hz
    simp [matLoop, matBody, matRead, matGates, fail, Com.wvars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp [matLoop, matBody, matRead, matGates, fail, Com.warrs]
  · simp [matLoop, matBody, matRead, matGates, fail, Com.reads]
  · simp [matLoop, matBody, matRead, matGates, fail, Com.NoWrite]

end Lax496464Proofs.WHierarchy.MccNP.Validate
