import Lax496464Proofs.Ram.T4Step

/-!
# Theorem 4's Machine, Part 4: `stepJob` Takes `MI k` to `MI (k+1)`
-/

namespace Lax496464Proofs.Ram.T4Job

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Greedy Lax496464.EstOrder
open Lax496464Proofs.Ram.SegProg Lax496464Proofs.Ram.T4Trees
open Lax496464Proofs.Ram.T4Defs Lax496464Proofs.Ram.T4Model Lax496464Proofs.Ram.T4Expire
open Lax496464Proofs.Ram.T4Step

/-- The sequence of sets extended by one more. -/
def extendS {J : Instance} (S : ℕ → Finset J.Job) (k : ℕ) (A' : Finset J.Job) :
    ℕ → Finset J.Job := fun i => if i = k + 1 then A' else S i

theorem extendS_steps {J : Instance} {p k : ℕ} (hk : k < J.jobs) (S : ℕ → Finset J.Job)
    (A' : Finset J.Job)
    (hsteps : ∀ i (hi : i < J.jobs), i < k → Step J p (S i) (S (i + 1)) ⟨i, hi⟩)
    (hstep : Step J p (S k) A' ⟨k, hk⟩) :
    ∀ i (hi : i < J.jobs), i < k + 1 → Step J p (extendS S k A' i) (extendS S k A' (i + 1)) ⟨i, hi⟩ := by
  intro i hi hik
  rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hlt | rfl
  · have h1 : i ≠ k + 1 := by omega
    have h2 : i + 1 ≠ k + 1 := by omega
    simp only [extendS, if_neg h1, if_neg h2]
    exact hsteps i hi hlt
  · have h1 : i ≠ i + 1 := by omega
    simp only [extendS, if_neg h1, if_true]
    exact hstep

theorem extendS_zero {J : Instance} {S : ℕ → Finset J.Job} (k : ℕ) (A' : Finset J.Job)
    (h0 : S 0 = ∅) : extendS S k A' 0 = ∅ := by
  simp [extendS, h0]

theorem extendS_succ {J : Instance} (S : ℕ → Finset J.Job) (k : ℕ) (A' : Finset J.Job) :
    extendS S k A' (k + 1) = A' := by simp [extendS]

theorem bumpJJ_run {B k : ℕ} {σ : Env} (hjj : σ.vars "jj" = k) (hkB : k + 1 < B) (hB1 : 1 < B) :
    Run B (bump "jj") σ (σ.setVar "jj" (k + 1)) 4 := by
  have h1 : (V "jj").evalB B σ = some k := hjj ▸ evalB_var (by rw [hjj]; omega)
  exact Run.assign (v := k + 1) (evalB_bin h1 (evalB_lit hB1) (by rw [Bop.apply_add]; exact hkB))

/-- **One job.** The invariant before job `k` becomes the invariant before job `k + 1`, the
set moves as `Greedy.Step` says, and the cost is paid for by the potential. -/
theorem stepJob_run {J : Instance} {p h BIG B k : ℕ} (hest : EstOrdered J)
    (hq : ∀ i : J.Job, 0 < J.q i) (hN : Num2 J B h BIG p) (hk : k < J.jobs) {σ : Env}
    (hM : MI J p h BIG B k σ) :
    ∃ (σ' : Env) (K : ℕ), Run B stepJob σ σ' K ∧ MI J p h BIG B (k + 1) σ' ∧
      K + Kpop h * σ'.vars "run" ≤ Kpop h * σ.vars "run" + Kbody h := by
  obtain ⟨hS, hp0, hjj, S, Act, hS0, hsteps, hInv, hsz, hrun, hX, hY⟩ := hM
  obtain ⟨σ3, K3, hr3, hMid, hok, hK3⟩ := mid_run hk hN (S k) Act hS hp0 hjj hsz hrun hX hY
  have hsm := hN.toNum.small
  have hB1 : 1 < B := by omega
  have hkB : k + 1 < B := by omega
  have hcardA : (S k).card + 1 ≤ J.jobs := by
    have hkA : (⟨k, hk⟩ : J.Job) ∉ S k := fun h => by have := hInv.before _ h; simp at this
    have := Finset.card_le_univ (insert (⟨k, hk⟩ : J.Job) (S k))
    rw [Finset.card_insert_of_notMem hkA] at this; simpa using this
  have hcardL : (live Act ⟨k, hk⟩).card + 1 ≤ J.jobs := by
    have hkA : (⟨k, hk⟩ : J.Job) ∉ live Act ⟨k, hk⟩ := fun h => by
      have := hInv.before _ (hInv.sub (mem_live.mp h).1); simp at this
    have := Finset.card_le_univ (insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩))
    rw [Finset.card_insert_of_notMem hkA] at this; simpa using this
  obtain ⟨hS3, hp3, hjj3, hsz3, hrun3, hX3, hY3, hok3⟩ := hMid
  by_cases hcond : (((S k).card : ℤ) + 1) * p ≤ s (⟨k, hk⟩ : J.Job) ∧
      (live Act ⟨k, hk⟩).card < J.machines
  · -- the job is added
    have hok1 : σ3.vars "ok" = 1 := by rw [hok, if_pos hcond]
    obtain ⟨hstep, hInv', hc1, hc2⟩ := step_add hest hk hInv hcond
    obtain ⟨σ4, K4, hr4, hS4, hp4, hjj4, hsz4, hrun4, hX4, hY4, hK4⟩ :=
      branch_add_run hk hN.toNum ⟨hS3, hp3, hjj3, hsz3, hrun3, hX3, hY3, hok3⟩ hok1 hcardA hcardL
    have hr5 := bumpJJ_run (B := B) hjj4 hkB hB1
    refine ⟨_, _, hr3.seq (hr4.seq hr5), ⟨hS4.of_run hr5 (by decide) (by decide), ?_, ?_,
      extendS S k (insert ⟨k, hk⟩ (S k)), insert ⟨k, hk⟩ (live Act ⟨k, hk⟩),
      extendS_zero k _ hS0, extendS_steps hk S _ hsteps hstep, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hr5.frame_var "p0" (by decide)]; exact hp4
    · simp
    · rw [extendS_succ]; exact hInv'
    · rw [extendS_succ]; simp [hsz4, hc1]
    · simp [hrun4, hc2]
    · unfold TreeOK; rw [hr5.frame_arr "TX" (by decide)]; exact hX4
    · unfold TreeOK; rw [hr5.frame_arr "TY" (by decide)]; exact hY4
    · simp only [vars_setVar, if_neg (by decide : ("run" : String) ≠ "jj")]
      rw [hrun4, Nat.mul_succ]; rw [hrun3] at hK3
      unfold Kbody
      omega
  · -- the job is added and a job of largest due date dropped
    have hok0 : σ3.vars "ok" ≠ 1 := by rw [hok, if_neg hcond]; omega
    have hcond' : s (⟨k, hk⟩ : J.Job) < (((S k).card : ℤ) + 1) * p ∨
        J.machines ≤ (live Act ⟨k, hk⟩).card := by
      rw [not_and_or] at hcond
      rcases hcond with h1 | h2
      · exact Or.inl (not_le.mp h1)
      · exact Or.inr (not_lt.mp h2)
    obtain ⟨σ4, K4, c, hr4, hcmem, hcmax, hS4, hp4, hjj4, hsz4, hrun4, hX4, hY4, hK4⟩ :=
      branch_drop_run hk hN.toNum ⟨hS3, hp3, hjj3, hsz3, hrun3, hX3, hY3, hok3⟩ hok0
    have hcmax' : ∀ i ∈ insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩), (J.d i : ℤ) ≤ J.d c :=
      fun i hi => by exact_mod_cast hcmax i hi
    obtain ⟨hstep, hInv', hc1, hc2⟩ := step_drop hest hq hk hInv hcond' hcmem hcmax'
    have hr5 := bumpJJ_run (B := B) hjj4 hkB hB1
    refine ⟨_, _, hr3.seq (hr4.seq hr5), ⟨hS4.of_run hr5 (by decide) (by decide), ?_, ?_,
      extendS S k ((insert ⟨k, hk⟩ (S k)).erase c), (insert ⟨k, hk⟩ (live Act ⟨k, hk⟩)).erase c,
      extendS_zero k _ hS0, extendS_steps hk S _ hsteps hstep, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hr5.frame_var "p0" (by decide)]; exact hp4
    · simp
    · rw [extendS_succ]; exact hInv'
    · rw [extendS_succ]; simp [hsz4, hc1]
    · simp [hrun4, hc2]
    · unfold TreeOK; rw [hr5.frame_arr "TX" (by decide)]; exact hX4
    · unfold TreeOK; rw [hr5.frame_arr "TY" (by decide)]; exact hY4
    · simp only [vars_setVar, if_neg (by decide : ("run" : String) ≠ "jj")]
      rw [hrun4]; rw [hrun3] at hK3
      unfold Kbody
      omega

/-! ## The outer loop -/

/-- Consider every job in turn. -/
def mainLoop : Com := .seq (.assign "jj" (.lit 0)) (.while (.lt (V "jj") (V "n")) stepJob)

/-- **All jobs.** From the state before job `0` to the state before job `n`, at cost
`n · (Kbody + 4)`. -/
theorem mainLoop_run {J : Instance} {p h BIG B : ℕ} (hest : EstOrdered J)
    (hq : ∀ i : J.Job, 0 < J.q i) (hN : Num2 J B h BIG p) {σ : Env}
    (hM : MI J p h BIG B 0 (σ.setVar "jj" 0)) :
    ∃ (σ' : Env) (K : ℕ), Run B mainLoop σ σ' K ∧ MI J p h BIG B J.jobs σ' ∧
      K ≤ (Kbody h + 4) * J.jobs + 6 := by
  have hsm := hN.toNum.small
  have hB1 : 1 < B := by omega
  have hnB := hN.toNum.jobs_lt
  have hr0 : Run B (.assign "jj" (.lit 0)) σ (σ.setVar "jj" 0) 2 := Run.assign (evalB_lit (by omega))
  have hloop := Spec.while_potential (B := B) (P := fun σ' => MI J p h BIG B 0 σ')
    (K := (Kbody h + 4) * J.jobs + 4)
    (b := .lt (V "jj") (V "n")) (c := stepJob)
    (fun σ => ∃ k, k ≤ J.jobs ∧ MI J p h BIG B k σ)
    (fun σ => (J.jobs - σ.vars "jj") * (Kbody h + 4) + Kpop h * σ.vars "run")
    (fun σ ⟨k, hkn, hMk⟩ => by
      obtain ⟨hS, -, hjj, -⟩ := hMk
      exact evalB_condLt_vars (by rw [hjj]; omega) (by rw [hS.n]; exact hnB))
    (fun σ ⟨k, hkn, hMk⟩ hcond => by
      have hMk' := hMk
      obtain ⟨hS, hp0, hjj, -⟩ := hMk
      have hlt := lt_of_condLt_true hcond
      rw [hjj, hS.n] at hlt
      obtain ⟨σ', K, hr, hM', hK⟩ := stepJob_run hest hq hN hlt hMk'
      refine ⟨σ', K, hr, ⟨k + 1, by omega, hM'⟩, ?_⟩
      obtain ⟨-, -, hjj', -⟩ := hM'
      show 1 + (Cond.lt (V "jj") (V "n")).size + K + ((J.jobs - σ'.vars "jj") * (Kbody h + 4) +
        Kpop h * σ'.vars "run") ≤ (J.jobs - σ.vars "jj") * (Kbody h + 4) + Kpop h * σ.vars "run"
      rw [hjj', hjj]
      have : (J.jobs - k) * (Kbody h + 4) = (J.jobs - (k + 1)) * (Kbody h + 4) + (Kbody h + 4) := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [this]
      have hb : (Cond.lt (V "jj") (V "n")).size = 3 := by simp [Cond.size, Expr.size]
      rw [hb]
      omega)
    (fun σ h' => ⟨0, Nat.zero_le _, h'⟩)
    (fun σ hM0 => by
      obtain ⟨hS, hp0, hjj, S, Act, hS0, hst, hInv, hsz, hrun, hX, hY⟩ := hM0
      have hAct : Act = ∅ := by
        have := hInv.sub
        rw [hS0] at this
        exact Finset.subset_empty.mp this
      have hb : (Cond.lt (V "jj") (V "n")).size = 3 := by simp [Cond.size, Expr.size]
      show (J.jobs - σ.vars "jj") * (Kbody h + 4) + Kpop h * σ.vars "run" + 1 +
        (Cond.lt (V "jj") (V "n")).size ≤ (Kbody h + 4) * J.jobs + 4
      rw [hb, hjj, hrun, hAct]; simp [Nat.mul_comm])
  obtain ⟨σ', hr, ⟨k, hkn, hM'⟩, hfalse⟩ := hloop.run hM
  have hjj' := hM'.2.2.1
  have hge := le_of_condLt_false hfalse
  rw [hjj', hM'.1.n] at hge
  have hkeq : k = J.jobs := le_antisymm hkn hge
  subst hkeq
  refine ⟨σ', _, hr0.seq hr, hM', by omega⟩

end Lax496464Proofs.Ram.T4Job
