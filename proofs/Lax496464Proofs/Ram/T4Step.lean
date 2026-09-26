import Lax496464Proofs.Ram.T4Expire

/-!
# Theorem 4's machine, part 3: one job

`stepJob` considers job `jj`: expire, decide whether it fits (`okCom`), insert it into both
trees, and either count it or drop the running job of largest due date. `stepJob_run` says that
this takes the invariant `MI k` to `MI (k+1)`, the sets moving as `Greedy.Step` says, and that
its cost is paid by the potential.
-/

namespace Lax496464Proofs.Ram.T4Step

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Greedy
open Lax496464Proofs.Ram.SegTree Lax496464Proofs.Ram.SegProg Lax496464Proofs.Ram.T4Trees
open Lax496464Proofs.Ram.T4Defs Lax496464Proofs.Ram.T4Model Lax496464Proofs.Ram.T4Expire

def okRun : Com := .ite (.lt (V "run") (V "m")) (.assign "ok" (.lit 1)) .skip

/-- `ok := 1` iff `q ≤ d`, and either `p = 0` or `sz + 1 ≤ (d - q) / p`, and `run < m`. -/
def okCom : Com :=
  .seq (.assign "ok" (.lit 0))
    (.ite (.lt (.get "DS" (V "jj")) (.get "QS" (V "jj"))) .skip
      (.ite (.eq (V "p0") (.lit 0)) okRun
        (.seq (.assign "ta" (.bin .div (.bin .sub (.get "DS" (V "jj")) (.get "QS" (V "jj")))
            (V "p0")))
          (.ite (.lt (V "sz") (V "ta")) okRun .skip))))

theorem okCom_spec {B : ℕ} (dk qk p sz run m : ℕ) (hB : 1 < B) :
    Spec B (fun σ => (σ.arrs "DS").getD (σ.vars "jj") 0 = dk ∧
        σ.vars "jj" < (σ.arrs "DS").length ∧ (σ.arrs "QS").getD (σ.vars "jj") 0 = qk ∧
        σ.vars "jj" < (σ.arrs "QS").length ∧ σ.vars "p0" = p ∧ σ.vars "sz" = sz ∧
        σ.vars "run" = run ∧ σ.vars "m" = m ∧ σ.vars "jj" < B ∧ dk < B ∧ qk < B ∧ p < B ∧
        sz < B ∧ run < B ∧ m < B) okCom
      (fun σ σ' => σ'.vars "ok" =
          (if qk ≤ dk ∧ (p = 0 ∨ sz < (dk - qk) / p) ∧ run < m then 1 else 0)
        ∧ (∀ y, y ≠ "ok" → y ≠ "ta" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs) 40 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hd, hjd, hq, hjq, hp, hsz, hrun, hm, hjj, hdB, hqB, hpB, hszB, hrunB, hmB⟩ := hσ
  run_vcg
  all_goals (simp_all)
  all_goals first | omega | exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- **The condition of the greedy's first case, in natural numbers.** -/
theorem cond_iff (sz p d q : ℕ) :
    (((sz : ℤ) + 1) * p ≤ (d : ℤ) - q) ↔ (q ≤ d ∧ (p = 0 ∨ sz < (d - q) / p)) := by
  by_cases hp : p = 0
  · subst hp; constructor
    · intro h; exact ⟨by omega, Or.inl rfl⟩
    · rintro ⟨h, -⟩; simp; omega
  · constructor
    · intro h
      have hq : q ≤ d := by
        by_contra hn
        have : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
        nlinarith
      refine ⟨hq, Or.inr ?_⟩
      have : (sz + 1) * p ≤ d - q := by
        have h2 : (((sz + 1 : ℕ) : ℤ)) * p ≤ ((d - q : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hq]; linarith
        exact_mod_cast h2
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hp)).mpr this
    · rintro ⟨hq, hs⟩
      rcases hs with h0 | hs
      · exact absurd h0 hp
      · have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hp)).mp (Nat.succ_le_of_lt hs)
        have h2 : (((sz + 1 : ℕ) : ℤ)) * p ≤ ((d - q : ℕ) : ℤ) := by exact_mod_cast this
        push_cast [Nat.cast_sub hq] at h2
        linarith

/-! ## Inserting the job into both trees -/

/-- `TX[jj] := d + 1` and `TY[jj] := BIG - d`. -/
def insertJ : Com :=
  .seq (.assign "tp" (V "jj"))
    (.seq (.assign "tv" (.bin .add (.get "DS" (V "jj")) (.lit 1)))
      (.seq (tset "TX")
        (.seq (.assign "tv" (.bin .sub (V "cinf") (.get "DS" (V "jj")))) (tset "TY"))))

theorem insertJ_spec {B : ℕ} (h k dk big : ℕ) (f g : ℕ → ℕ) (hB : 2 * 2 ^ h + 2 < B)
    (hk : k < 2 ^ h) (hdB : dk + 1 < B) (hbigB : big < B) :
    Spec B (fun σ => σ.vars "tN" = 2 ^ h ∧ σ.vars "th" = h ∧ σ.vars "jj" = k ∧
        σ.vars "cinf" = big ∧ (σ.arrs "DS").getD k 0 = dk ∧ k < (σ.arrs "DS").length ∧
        TreeOK "TX" h f B σ ∧ TreeOK "TY" h g B σ) insertJ
      (fun _σ σ' => TreeOK "TX" h (upd f k (dk + 1)) B σ' ∧ TreeOK "TY" h (upd g k (big - dk)) B σ' ∧
        σ'.vars "tN" = 2 ^ h ∧ σ'.vars "th" = h) (2 * (68 * h + 40) + 20) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hN, hth, hjj, hbig, hd, hjd, hX, hY⟩ := hσ
  have hkB : k < B := by have := Nat.lt_two_pow_self (n := h); omega
  have hdB' : dk < B := by omega
  have hdget : (σ.arrs "DS")[k]? = some dk := by
    rw [List.getElem?_eq_getElem hjd]; rw [List.getD_eq_getElem _ _ hjd] at hd; rw [hd]
  have hvJ : (V "jj").evalB B σ = some k := hjj ▸ evalB_var (by rw [hjj]; exact hkB)
  have hr1 : Run B (.assign "tp" (V "jj")) σ (σ.setVar "tp" k) 2 := Run.assign (v := k) hvJ
  set σ1 := σ.setVar "tp" k with hσ1
  have hvJ1 : (V "jj").evalB B σ1 = some k := by
    have : σ1.vars "jj" = k := by simp [hσ1, hjj]
    exact this ▸ evalB_var (by rw [this]; exact hkB)
  have hg1 : (Expr.get "DS" (V "jj")).evalB B σ1 = some dk :=
    evalB_get hvJ1 (by
      have : σ1.arrs "DS" = σ.arrs "DS" := by simp [hσ1]
      rw [this]; exact hdget) hdB'

  have hr2 : Run B (.assign "tv" (.bin .add (.get "DS" (V "jj")) (.lit 1))) σ1
      (σ1.setVar "tv" (dk + 1)) (1 + (Expr.bin .add (.get "DS" (V "jj")) (.lit 1)).size) :=
    Run.assign (v := dk + 1) (evalB_bin hg1 (evalB_lit (by omega)) (by rw [Bop.apply_add]; omega))
  set σ2 := σ1.setVar "tv" (dk + 1) with hσ2
  have hX2 : TreeOK "TX" h f B σ2 := by simpa [hσ2, hσ1, TreeOK] using hX
  have hY2 : TreeOK "TY" h g B σ2 := by simpa [hσ2, hσ1, TreeOK] using hY
  obtain ⟨σ3, hr3, hX3⟩ := (tset_tree "TX" h k (dk + 1) f hB hdB hk).run
    ⟨by simp [hσ2, hσ1, hN], by simp [hσ2, hσ1, hth], by simp [hσ2, hσ1], by simp [hσ2], hX2⟩
  have hY3 : TreeOK "TY" h g B σ3 := by
    have := hr3.frame_arr "TY" (by decide)
    unfold TreeOK; rw [this]; exact hY2
  have hbig3 : σ3.vars "cinf" = big := by
    rw [hr3.frame_var "cinf" (by decide)]; simp [hσ2, hσ1, hbig]
  have hjj3 : σ3.vars "jj" = k := by
    rw [hr3.frame_var "jj" (by decide)]; simp [hσ2, hσ1, hjj]
  have hvc : (V "cinf").evalB B σ3 = some big := hbig3 ▸ evalB_var (by rw [hbig3]; exact hbigB)
  have hvj3 : (V "jj").evalB B σ3 = some k := hjj3 ▸ evalB_var (by rw [hjj3]; exact hkB)
  have hg3 : (Expr.get "DS" (V "jj")).evalB B σ3 = some dk :=
    evalB_get hvj3 (by
      have : σ3.arrs "DS" = σ.arrs "DS" := by
        rw [hr3.frame_arr "DS" (by decide)]; simp [hσ2, hσ1]
      rw [this]; exact hdget) hdB'
  have hr4 : Run B (.assign "tv" (.bin .sub (V "cinf") (.get "DS" (V "jj")))) σ3
      (σ3.setVar "tv" (big - dk)) (1 + (Expr.bin .sub (V "cinf") (.get "DS" (V "jj"))).size) :=
    Run.assign (v := big - dk) (evalB_bin hvc hg3 (by rw [Bop.apply_sub]; omega))
  set σ4 := σ3.setVar "tv" (big - dk) with hσ4
  have hY4 : TreeOK "TY" h g B σ4 := by simpa [hσ4, TreeOK] using hY3
  obtain ⟨σ5, hr5, hY5⟩ := (tset_tree "TY" h k (big - dk) g hB (by omega) hk).run
    ⟨by simp [hσ4]; rw [hr3.frame_var "tN" (by decide)]; simp [hσ2, hσ1, hN],
     by simp [hσ4]; rw [hr3.frame_var "th" (by decide)]; simp [hσ2, hσ1, hth],
     by simp [hσ4]; rw [hr3.frame_var "tp" (by decide)]; simp [hσ2, hσ1], by simp [hσ4], hY4⟩
  have hX5 : TreeOK "TX" h (upd f k (dk + 1)) B σ5 := by
    have := hr5.frame_arr "TX" (by decide)
    unfold TreeOK; rw [this]; simpa [hσ4, TreeOK] using hX3
  refine ⟨σ5, _, (hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5)))).mono (by simp [Expr.size]; omega), le_rfl, hX5, hY5, ?_, ?_⟩
  · rw [hr5.frame_var "tN" (by decide)]; simp [hσ4]; rw [hr3.frame_var "tN" (by decide)]
    simp [hσ2, hσ1, hN]
  · rw [hr5.frame_var "th" (by decide)]; simp [hσ4]; rw [hr3.frame_var "th" (by decide)]
    simp [hσ2, hσ1, hth]

/-! ## Dropping the running job of largest due date -/

/-- Descend `TX` to a job of largest due date and clear its leaf from both trees. -/
def dropMax : Com := .seq (tfind "TX") dropLeaf

theorem dropMax_run {J : Instance} {h BIG B : ℕ} (hN : Num J B h BIG) (Ac : Finset J.Job)
    (hne : Ac.Nonempty) {σ : Env} (htN : σ.vars "tN" = 2 ^ h) (hth : σ.vars "th" = h)
    (hX : TreeOK "TX" h (lfX J Ac) B σ) (hY : TreeOK "TY" h (lfY J BIG Ac) B σ) :
    ∃ (σ' : Env) (K : ℕ) (c : J.Job), Run B dropMax σ σ' K ∧ c ∈ Ac ∧ (∀ i ∈ Ac, J.d i ≤ J.d c) ∧
      TreeOK "TX" h (lfX J (Ac.erase c)) B σ' ∧ TreeOK "TY" h (lfY J BIG (Ac.erase c)) B σ' ∧
      K ≤ 180 * h + 98 := by
  obtain ⟨σ1, hr1, hlo, hhi, hval, hT1⟩ :=
    (tfind_spec "TX" h (σ.arrs "TX") hX.1 hN.tree hX.2.2).run ⟨hth, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = σ1.vars "ti" - 2 ^ h := ⟨_, rfl⟩
  have hℓ : ℓ < 2 ^ h := by omega
  have hti1 : σ1.vars "ti" = 2 ^ h + ℓ := by omega
  obtain ⟨hk', hmem, hmax⟩ := x_max_leaf hX.1 hX.2.1 hN.cap hℓ (by rw [← hti1]; exact hval)
    (root_ne_zero_of_nonempty hX.1 hX.2.1 hN.cap hne)
  have hX1 : TreeOK "TX" h (lfX J Ac) B σ1 := by
    unfold TreeOK; rw [hr1.frame_arr "TX" (by decide)]; exact hX
  have hY1 : TreeOK "TY" h (lfY J BIG Ac) B σ1 := by
    unfold TreeOK; rw [hr1.frame_arr "TY" (by decide)]; exact hY
  have hN1 : σ1.vars "tN" = 2 ^ h := by rw [hr1.frame_var "tN" (by decide)]; exact htN
  have hth1 : σ1.vars "th" = h := by rw [hr1.frame_var "th" (by decide)]; exact hth
  obtain ⟨σ2, hr2, hX2, hY2, -, -⟩ :=
    (dropLeaf_spec h ℓ (lfX J Ac) (lfY J BIG Ac) hN.tree hℓ).run ⟨hN1, hth1, hti1, hX1, hY1⟩
  rw [lfX_erase hk'] at hX2
  rw [lfY_erase hk'] at hY2
  exact ⟨σ2, _, ⟨ℓ, hk'⟩, hr1.seq hr2, hmem, hmax, hX2, hY2, by omega⟩

/-! ## The state around one job -/

/-- The numeric side conditions of one job, on top of `Num`. -/
structure Num2 (J : Instance) (B h BIG p : ℕ) : Prop extends Num J B h BIG where
  pB : p < B
  mB : J.machines < B

theorem _root_.Lax496464Proofs.Ram.T4Expire.Num.jobs_lt {J : Instance} {B h BIG : ℕ} (hN : Num J B h BIG) : J.jobs < B := by
  have := hN.cap; have := Nat.lt_two_pow_self (n := h); have := hN.tree; omega

theorem _root_.Lax496464Proofs.Ram.T4Expire.Stat.dD {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : (σ.arrs "DS").getD k 0 = J.d ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, hs.d_get hk]; rfl

theorem _root_.Lax496464Proofs.Ram.T4Expire.Stat.qD {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : (σ.arrs "QS").getD k 0 = J.q ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, hs.q_get hk]; rfl

theorem _root_.Lax496464Proofs.Ram.T4Expire.Stat.dLen {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : k < (σ.arrs "DS").length := by rw [hs.ds]; simp [hk]

theorem _root_.Lax496464Proofs.Ram.T4Expire.Stat.qLen {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : k < (σ.arrs "QS").length := by rw [hs.qs]; simp [hk]

/-- The state after the job has been inserted, before the branch. -/
def Mid (J : Instance) (p h BIG B k : ℕ) (hk : k < J.jobs) (A Act1 : Finset J.Job) (σ : Env) :
    Prop :=
  Stat J h BIG σ ∧ σ.vars "p0" = p ∧ σ.vars "jj" = k ∧ σ.vars "sz" = A.card ∧
    σ.vars "run" = Act1.card ∧
    TreeOK "TX" h (lfX J (insert ⟨k, hk⟩ Act1)) B σ ∧
    TreeOK "TY" h (lfY J BIG (insert ⟨k, hk⟩ Act1)) B σ ∧ σ.vars "ok" ≤ 1

/-- The branch: count the job, or drop the running job of largest due date. -/
def branch : Com :=
  .ite (.eq (V "ok") (.lit 1)) (.seq (bump "sz") (bump "run")) dropMax

/-- The whole of one job. -/
def stepJob : Com :=
  .seq (.seq expire (.seq okCom insertJ)) (.seq branch (bump "jj"))

/-- Expire, decide whether the job fits, insert it. -/
theorem mid_run {J : Instance} {p h BIG B k : ℕ} (hk : k < J.jobs) (hN : Num2 J B h BIG p)
    (A Act : Finset J.Job) {σ : Env} (hS : Stat J h BIG σ) (hp0 : σ.vars "p0" = p)
    (hjj : σ.vars "jj" = k) (hsz : σ.vars "sz" = A.card) (hrun : σ.vars "run" = Act.card)
    (hX : TreeOK "TX" h (lfX J Act) B σ) (hY : TreeOK "TY" h (lfY J BIG Act) B σ) :
    ∃ (σ3 : Env) (K : ℕ), Run B (.seq expire (.seq okCom insertJ)) σ σ3 K ∧
      Mid J p h BIG B k hk A (live Act ⟨k, hk⟩) σ3 ∧
      σ3.vars "ok" = (if ((A.card : ℤ) + 1) * p ≤ s (⟨k, hk⟩ : J.Job) ∧
        (live Act ⟨k, hk⟩).card < J.machines then 1 else 0) ∧
      K + Kpop h * σ3.vars "run" ≤ Kpop h * σ.vars "run" +
        (40 + (2 * (68 * h + 40) + 20)) + 1 + expireCond.size := by
  have hnB := hN.toNum.jobs_lt
  have hkB : k < B := by omega
  have hB1 : 1 < B := by have := hN.tree; omega
  -- expire
  have hEI : EI J h BIG B k hk Act A.card σ :=
    ⟨hS, hjj, hsz, Act, Finset.filter_subset _ _, Finset.Subset.refl _,
      fun i hi hin => absurd hi hin, hrun, hX, hY⟩
  obtain ⟨σ1, K1, hr1, hS1, hjj1, hsz1, hrun1, hX1, hY1, hK1⟩ :=
    expire_run hk hN.toNum Act A.card hEI
  have hp01 : σ1.vars "p0" = p := by rw [hr1.frame_var "p0" (by decide)]; exact hp0
  -- ok
  have hdk := hS1.dD hk
  have hqk := hS1.qD hk
  have hcardA : A.card ≤ J.jobs := by
    have := Finset.card_le_univ A; simpa using this
  have hcardL : (live Act ⟨k, hk⟩).card ≤ J.jobs := by
    have := Finset.card_le_univ (live Act ⟨k, hk⟩); simpa using this
  obtain ⟨σ2, hr2, hok, hfr2, harr2⟩ := (okCom_spec (B := B) (J.d ⟨k, hk⟩) (J.q ⟨k, hk⟩) p A.card
    (live Act ⟨k, hk⟩).card J.machines hB1).run
    ⟨by rw [hjj1]; exact hdk, by rw [hjj1]; exact hS1.dLen hk,
     by rw [hjj1]; exact hqk, by rw [hjj1]; exact hS1.qLen hk, hp01, hsz1, hrun1,
     hS1.m, by rw [hjj1]; exact hkB, by have := hN.big ⟨k, hk⟩; have := hN.bigB; omega,
     by have := hN.bigq ⟨k, hk⟩; omega, hN.pB, by omega, by omega, hN.mB⟩
  have hcond : ((J.q ⟨k, hk⟩ ≤ J.d ⟨k, hk⟩ ∧ (p = 0 ∨ A.card < (J.d ⟨k, hk⟩ - J.q ⟨k, hk⟩) / p) ∧
      (live Act ⟨k, hk⟩).card < J.machines)) ↔ (((A.card : ℤ) + 1) * p ≤ s (⟨k, hk⟩ : J.Job) ∧
        (live Act ⟨k, hk⟩).card < J.machines) := by
    unfold s
    have hc := cond_iff A.card p (J.d ⟨k, hk⟩) (J.q ⟨k, hk⟩)
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨hc.mpr ⟨h1, h2⟩, h3⟩
    · rintro ⟨h1, h3⟩; obtain ⟨a, b⟩ := hc.mp h1; exact ⟨a, b, h3⟩
  -- insert
  have hjj2 : σ2.vars "jj" = k := by rw [hfr2 "jj" (by decide) (by decide)]; exact hjj1
  have hS2 : Stat J h BIG σ2 := ⟨by rw [hfr2 "n" (by decide) (by decide)]; exact hS1.n,
    by rw [hfr2 "m" (by decide) (by decide)]; exact hS1.m,
    by rw [hfr2 "tN" (by decide) (by decide)]; exact hS1.tN,
    by rw [hfr2 "th" (by decide) (by decide)]; exact hS1.th,
    by rw [hfr2 "cinf" (by decide) (by decide)]; exact hS1.big,
    by rw [harr2]; exact hS1.ds, by rw [harr2]; exact hS1.qs⟩
  have hX2 : TreeOK "TX" h (lfX J (live Act ⟨k, hk⟩)) B σ2 := by unfold TreeOK; rw [harr2]; exact hX1
  have hY2 : TreeOK "TY" h (lfY J BIG (live Act ⟨k, hk⟩)) B σ2 := by
    unfold TreeOK; rw [harr2]; exact hY1
  have hkcap : k < 2 ^ h := lt_of_lt_of_le hk hN.cap
  obtain ⟨σ3, hr3, hX3, hY3, hN3, hth3⟩ := (insertJ_spec (B := B) h k (J.d ⟨k, hk⟩) BIG
    (lfX J (live Act ⟨k, hk⟩)) (lfY J BIG (live Act ⟨k, hk⟩)) hN.tree hkcap
    (by have := hN.dsum ⟨k, hk⟩; omega) hN.bigB).run
    ⟨hS2.tN, hS2.th, hjj2, hS2.big, by rw [hS2.ds]; simp [Dp1.dv, hk],
      hS2.dLen hk, hX2, hY2⟩
  rw [lfX_insert hk] at hX3
  rw [lfY_insert hk] at hY3
  have hall := hr1.seq (hr2.seq hr3)
  have hrun3 : σ3.vars "run" = (live Act ⟨k, hk⟩).card := by
    rw [hr3.frame_var "run" (by decide), hfr2 "run" (by decide) (by decide)]; exact hrun1
  refine ⟨σ3, _, hall, ⟨hS2.of_run hr3 (by decide) (by decide), ?_, ?_, ?_, hrun3, hX3, hY3, ?_⟩, ?_, ?_⟩
  · rw [hr3.frame_var "p0" (by decide), hfr2 "p0" (by decide) (by decide)]; exact hp01
  · rw [hr3.frame_var "jj" (by decide)]; exact hjj2
  · rw [hr3.frame_var "sz" (by decide), hfr2 "sz" (by decide) (by decide)]; exact hsz1
  · rw [hr3.frame_var "ok" (by decide), hok]; split_ifs <;> omega
  · rw [hr3.frame_var "ok" (by decide), hok]
    exact if_congr hcond rfl rfl
  · rw [hrun3]
    rw [hrun1] at hK1
    omega

theorem _root_.Lax496464Proofs.Ram.T4Expire.Num.small {J : Instance} {B h BIG : ℕ} (hN : Num J B h BIG) : J.jobs + 1 < B := by
  have := hN.cap; have := Nat.lt_two_pow_self (n := h); have := hN.tree
  have := Nat.one_le_two_pow (n := h); omega

/-- The first case of the branch: count the job. -/
theorem branch_add_run {J : Instance} {p h BIG B k : ℕ} (hk : k < J.jobs) (hN : Num J B h BIG)
    {A Act1 : Finset J.Job} {σ : Env} (hM : Mid J p h BIG B k hk A Act1 σ)
    (hok : σ.vars "ok" = 1) (hlt : A.card + 1 ≤ J.jobs) (hlt2 : Act1.card + 1 ≤ J.jobs) :
    ∃ (σ' : Env) (K : ℕ), Run B branch σ σ' K ∧ Stat J h BIG σ' ∧ σ'.vars "p0" = p ∧
      σ'.vars "jj" = k ∧ σ'.vars "sz" = A.card + 1 ∧ σ'.vars "run" = Act1.card + 1 ∧
      TreeOK "TX" h (lfX J (insert ⟨k, hk⟩ Act1)) B σ' ∧
      TreeOK "TY" h (lfY J BIG (insert ⟨k, hk⟩ Act1)) B σ' ∧ K ≤ 12 := by
  obtain ⟨hS, hp0, hjj, hsz, hrun, hX, hY, hokle⟩ := hM
  have hsm := hN.small
  have hB1 : 1 < B := by omega
  have hokB : σ.vars "ok" < B := by rw [hok]; exact hB1
  have hc : (Cond.eq (V "ok") (.lit 1)).evalB B σ = some true := by
    rw [evalB_condEq (evalB_var hokB) (evalB_lit hB1), hok]; rfl
  have hszB : σ.vars "sz" < B := by rw [hsz]; omega
  have hr1 : Run B (bump "sz") σ (σ.setVar "sz" (σ.vars "sz" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hszB) (evalB_lit hB1) (by rw [Bop.apply_add]; omega))
  set σ1 := σ.setVar "sz" (σ.vars "sz" + 1) with hσ1
  have hrun1 : σ1.vars "run" = Act1.card := by simp [hσ1, hrun]
  have hrunB : σ1.vars "run" < B := by rw [hrun1]; omega
  have hr2 : Run B (bump "run") σ1 (σ1.setVar "run" (σ1.vars "run" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hrunB) (evalB_lit hB1) (by rw [Bop.apply_add]; omega))
  have hbody := hr1.seq hr2
  have hall : Run B branch σ (σ1.setVar "run" (σ1.vars "run" + 1)) (1 + (Cond.eq (V "ok") (.lit 1)).size + (4 + 4)) :=
    Run.ite_true hc hbody
  refine ⟨_, _, hall, hS.of_run hbody (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody.frame_var "p0" (by decide)]; exact hp0
  · rw [hbody.frame_var "jj" (by decide)]; exact hjj
  · simp [hσ1, hsz]
  · simp [hσ1, hrun]
  · unfold TreeOK; rw [hbody.frame_arr "TX" (by decide)]; exact hX
  · unfold TreeOK; rw [hbody.frame_arr "TY" (by decide)]; exact hY
  · simp [Cond.size, Expr.size]

/-- The second case of the branch: drop the running job of largest due date. -/
theorem branch_drop_run {J : Instance} {p h BIG B k : ℕ} (hk : k < J.jobs)
    (hN : Num J B h BIG) {A Act1 : Finset J.Job} {σ : Env} (hM : Mid J p h BIG B k hk A Act1 σ)
    (hok : σ.vars "ok" ≠ 1) :
    ∃ (σ' : Env) (K : ℕ) (c : J.Job), Run B branch σ σ' K ∧
      c ∈ insert (⟨k, hk⟩ : J.Job) Act1 ∧ (∀ i ∈ insert (⟨k, hk⟩ : J.Job) Act1, J.d i ≤ J.d c) ∧
      Stat J h BIG σ' ∧ σ'.vars "p0" = p ∧ σ'.vars "jj" = k ∧ σ'.vars "sz" = A.card ∧
      σ'.vars "run" = Act1.card ∧
      TreeOK "TX" h (lfX J ((insert ⟨k, hk⟩ Act1).erase c)) B σ' ∧
      TreeOK "TY" h (lfY J BIG ((insert ⟨k, hk⟩ Act1).erase c)) B σ' ∧ K ≤ 180 * h + 102 := by
  obtain ⟨hS, hp0, hjj, hsz, hrun, hX, hY, hokle⟩ := hM
  have hsm := hN.small
  have hB1 : 1 < B := by omega
  have hokB : σ.vars "ok" < B := by omega
  have hc : (Cond.eq (V "ok") (.lit 1)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var hokB) (evalB_lit hB1)]
    simp [hok]
  obtain ⟨σ1, K1, c, hr1, hcmem, hcmax, hX1, hY1, hK1⟩ := dropMax_run (J := J) hN
    (insert ⟨k, hk⟩ Act1) ⟨⟨k, hk⟩, Finset.mem_insert_self _ _⟩ hS.tN hS.th hX hY
  have hall : Run B branch σ σ1 (1 + (Cond.eq (V "ok") (.lit 1)).size + K1) :=
    Run.ite_false hc hr1
  refine ⟨σ1, _, c, hall, hcmem, fun i hi => ?_, hS.of_run hr1 (by decide) (by decide), ?_, ?_, ?_,
    ?_, hX1, hY1, ?_⟩
  · exact_mod_cast hcmax i hi
  · rw [hr1.frame_var "p0" (by decide)]; exact hp0
  · rw [hr1.frame_var "jj" (by decide)]; exact hjj
  · rw [hr1.frame_var "sz" (by decide)]; exact hsz
  · rw [hr1.frame_var "run" (by decide)]; exact hrun
  · simp [Cond.size, Expr.size]; omega

/-- The invariant of the outer loop, before job `k`. -/
def MI (J : Instance) (p h BIG B k : ℕ) (σ : Env) : Prop :=
  Stat J h BIG σ ∧ σ.vars "p0" = p ∧ σ.vars "jj" = k ∧
    ∃ (S : ℕ → Finset J.Job) (Act : Finset J.Job), S 0 = ∅ ∧
      (∀ i (hi : i < J.jobs), i < k → Step J p (S i) (S (i + 1)) ⟨i, hi⟩) ∧
      Inv J k (S k) Act ∧ σ.vars "sz" = (S k).card ∧ σ.vars "run" = Act.card ∧
      TreeOK "TX" h (lfX J Act) B σ ∧ TreeOK "TY" h (lfY J BIG Act) B σ

/-- The constant cost of one job apart from what the potential pays. -/
def Kbody (h : ℕ) : ℕ :=
  (40 + (2 * (68 * h + 40) + 20)) + 1 + expireCond.size + (180 * h + 102) + 4 + Kpop h

end Lax496464Proofs.Ram.T4Step
