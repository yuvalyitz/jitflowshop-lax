import Lax496464Proofs.Ram.T4Defs
import Lax496464Proofs.Ram.Dp1

/-!
# Theorem 4's Machine, Part 2: Expiring the Jobs That Have Ended

Before job `k` is considered, every member of the active set whose due date is at most the
start time of job `k` is removed from both trees and from the running count. The loop stops as
soon as the smallest due date left (`BIG − root` of `TY`) exceeds that start time. Its cost is
paid by the potential `Kpop · run`: each turn removes one running job.
-/

namespace Lax496464Proofs.Ram.T4Expire

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464Proofs.Ram.SegTree Lax496464Proofs.Ram.SegProg Lax496464Proofs.Ram.T4Trees
open Lax496464Proofs.Ram.T4Defs Lax496464Proofs.Ram.T4Model
open Lax496464Proofs.Ram.Dp1 (dv qv)

/-- The facts about the machine's state that never change during the greedy. -/
structure Stat (J : Instance) (h BIG : ℕ) (σ : Env) : Prop where
  n : σ.vars "n" = J.jobs
  m : σ.vars "m" = J.machines
  tN : σ.vars "tN" = 2 ^ h
  th : σ.vars "th" = h
  big : σ.vars "cinf" = BIG
  ds : σ.arrs "DS" = (List.range J.jobs).map (dv J)
  qs : σ.arrs "QS" = (List.range J.jobs).map (qv J)

/-- The numeric side conditions: everything the two trees and the comparisons compute fits. -/
structure Num (J : Instance) (B h BIG : ℕ) : Prop where
  tree : 2 * 2 ^ h + 2 < B
  cap : J.jobs ≤ 2 ^ h
  big : ∀ i : J.Job, J.d i < BIG
  bigq : ∀ i : J.Job, BIG + J.q i < B
  dsum : ∀ i : J.Job, J.d i + BIG + 1 < B
  bigB : BIG < B

theorem Stat.of_run {J : Instance} {h BIG B K : ℕ} {c : Com} {σ σ' : Env} (hs : Stat J h BIG σ)
    (hr : Run B c σ σ' K) (hv : ∀ y ∈ ["n", "m", "tN", "th", "cinf"], y ∉ c.wvars)
    (ha : ∀ a ∈ ["DS", "QS"], a ∉ c.warrs) : Stat J h BIG σ' :=
  ⟨by rw [hr.frame_var "n" (hv _ (by simp))]; exact hs.n,
   by rw [hr.frame_var "m" (hv _ (by simp))]; exact hs.m,
   by rw [hr.frame_var "tN" (hv _ (by simp))]; exact hs.tN,
   by rw [hr.frame_var "th" (hv _ (by simp))]; exact hs.th,
   by rw [hr.frame_var "cinf" (hv _ (by simp))]; exact hs.big,
   by rw [hr.frame_arr "DS" (ha _ (by simp))]; exact hs.ds,
   by rw [hr.frame_arr "QS" (ha _ (by simp))]; exact hs.qs⟩

theorem Stat.d_get {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : (σ.arrs "DS")[k]? = some (J.d ⟨k, hk⟩) := by
  rw [hs.ds, List.getElem?_map, List.getElem?_range hk]; simp [dv, hk]

theorem Stat.q_get {J : Instance} {h BIG : ℕ} {σ : Env} (hs : Stat J h BIG σ) {k : ℕ}
    (hk : k < J.jobs) : (σ.arrs "QS")[k]? = some (J.q ⟨k, hk⟩) := by
  rw [hs.qs, List.getElem?_map, List.getElem?_range hk]; simp [qv, hk]

/-! ## The loop -/

/-- Some running job has a due date at most the start of job `jj`: `BIG + q < d + root + 1`. -/
def expireCond : Cond :=
  .lt (.bin .add (V "cinf") (.get "QS" (V "jj")))
    (.bin .add (.bin .add (.get "DS" (V "jj")) (.get "TY" (.lit 1))) (.lit 1))

/-- Remove the job with the smallest due date from both trees and from the running count. -/
def expireBody : Com :=
  .seq (tfind "TY") (.seq dropLeaf (.assign "run" (.bin .sub (V "run") (.lit 1))))

/-- The expiry loop. -/
def expire : Com := .while expireCond expireBody

theorem expireCond_eval {B : ℕ} {σ : Env} {big q d y1 : ℕ} (hbig : σ.vars "cinf" = big)
    (hqk : (σ.arrs "QS")[σ.vars "jj"]? = some q) (hdk : (σ.arrs "DS")[σ.vars "jj"]? = some d)
    (hy : (σ.arrs "TY")[1]? = some y1) (hjj : σ.vars "jj" < B) (hbigB : big < B) (hqB : q < B)
    (hdB : d < B) (hyB : y1 < B) (hs1 : big + q < B) (hs2 : d + y1 < B) (hs3 : d + y1 + 1 < B)
    (h1 : 1 < B) : expireCond.evalB B σ = some (decide (big + q < d + y1 + 1)) := by
  have e1 : (V "cinf").evalB B σ = some big := hbig ▸ evalB_var (by rw [hbig]; exact hbigB)
  have e2 : (Expr.get "QS" (V "jj")).evalB B σ = some q := evalB_get (evalB_var hjj) hqk hqB
  have e3 : (Expr.bin .add (V "cinf") (.get "QS" (V "jj"))).evalB B σ = some (big + q) :=
    evalB_bin e1 e2 hs1
  have e4 : (Expr.get "DS" (V "jj")).evalB B σ = some d := evalB_get (evalB_var hjj) hdk hdB
  have e5 : (Expr.get "TY" (.lit 1)).evalB B σ = some y1 := evalB_get (evalB_lit h1) hy hyB
  have e6 : (Expr.bin .add (.get "DS" (V "jj")) (.get "TY" (.lit 1))).evalB B σ = some (d + y1) :=
    evalB_bin e4 e5 hs2
  have e7 : (Expr.bin .add (.bin .add (.get "DS" (V "jj")) (.get "TY" (.lit 1))) (.lit 1)).evalB B σ
      = some (d + y1 + 1) := evalB_bin e6 (evalB_lit h1) hs3
  exact evalB_condLt e3 e7

/-- Body cost. -/
def Kb (h : ℕ) : ℕ := 180 * h + 102

/-- Cost of one turn plus the loop test, paid per running job. -/
def Kpop (h : ℕ) : ℕ := Kb h + 1 + expireCond.size

/-- The loop invariant, for job `k` and the set `Act` that was active when it began. -/
def EI (J : Instance) (h BIG B k : ℕ) (hk : k < J.jobs) (Act : Finset J.Job) (sz0 : ℕ)
    (σ : Env) : Prop :=
  Stat J h BIG σ ∧ σ.vars "jj" = k ∧ σ.vars "sz" = sz0 ∧
    ∃ Ac : Finset J.Job, live Act ⟨k, hk⟩ ⊆ Ac ∧ Ac ⊆ Act ∧
      (∀ i ∈ Act, i ∉ Ac → (J.d i : ℤ) ≤ s (⟨k, hk⟩ : J.Job)) ∧
      σ.vars "run" = Ac.card ∧ TreeOK "TX" h (lfX J Ac) B σ ∧
      TreeOK "TY" h (lfY J BIG Ac) B σ

theorem y1_le {T : List ℕ} {h : ℕ} (hc : Cons T h) {J : Instance} {BIG : ℕ} {Ac : Finset J.Job}
    (hl : Leaves T h (lfY J BIG Ac)) : T.getD 1 0 ≤ BIG := by
  obtain ⟨i, h1, h2, h3⟩ := hc.exists_leaf
  rw [← h3, show i = 2 ^ h + (i - 2 ^ h) by omega, hl _ (by omega)]
  unfold lfY
  split_ifs <;> omega

/-- One turn of the expiry loop. -/
theorem expire_step {J : Instance} {h BIG B k : ℕ} (hk : k < J.jobs) (hN : Num J B h BIG)
    (Act : Finset J.Job) (sz0 : ℕ) {σ : Env} (hI : EI J h BIG B k hk Act sz0 σ)
    (hcond : expireCond.evalB B σ = some true) :
    ∃ σ' K, Run B expireBody σ σ' K ∧ EI J h BIG B k hk Act sz0 σ' ∧
      K ≤ Kb h ∧ σ'.vars "run" + 1 = σ.vars "run" := by
  obtain ⟨hS, hjj, hsz, Ac, hsub1, hsub2, hover, hrun, hX, hY⟩ := hI
  have hh1 : 1 < B := by have := hN.tree; omega
  have hjjB : σ.vars "jj" < B := by
    rw [hjj]; have := hN.cap; have := Nat.lt_two_pow_self (n := h); have := hN.tree; omega
  have hlen1 : 1 < (σ.arrs "TY").length := by
    rw [hY.1.1]; have := Nat.one_le_two_pow (n := h); omega
  have hy1B : (σ.arrs "TY").getD 1 0 < B := by
    apply hY.2.2; rw [List.getD_eq_getElem _ _ hlen1]
    exact List.getElem_mem _
  have hy1le : (σ.arrs "TY").getD 1 0 ≤ BIG := y1_le hY.1 hY.2.1
  have hy1get : (σ.arrs "TY")[1]? = some ((σ.arrs "TY").getD 1 0) := by
    rw [List.getD_eq_getElem _ _ hlen1]; exact List.getElem?_eq_getElem hlen1
  have hqk := hS.q_get hk
  have hdk := hS.d_get hk
  rw [hjj] at hjjB
  have hev := expireCond_eval (B := B) (σ := σ) (big := BIG) (q := J.q ⟨k, hk⟩) (d := J.d ⟨k, hk⟩)
    (y1 := (σ.arrs "TY").getD 1 0) hS.big (by rw [hjj]; exact hqk) (by rw [hjj]; exact hdk) hy1get
    (by rw [hjj]; exact hjjB) hN.bigB (by have := hN.bigq ⟨k, hk⟩; omega)
    (by have := hN.dsum ⟨k, hk⟩; omega) hy1B (hN.bigq ⟨k, hk⟩)
    (by have := hN.dsum ⟨k, hk⟩; omega) (by have := hN.dsum ⟨k, hk⟩; omega) hh1
  rw [hev] at hcond
  have hlt : BIG + J.q ⟨k, hk⟩ < J.d ⟨k, hk⟩ + (σ.arrs "TY").getD 1 0 + 1 := by
    exact decide_eq_true_iff.mp (Option.some.inj hcond)
  have hne : Ac.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h0 := y_root_zero hY.1 hY.2.1
    rw [h0] at hlt
    have := hN.big ⟨k, hk⟩
    omega
  -- descend TY
  obtain ⟨σ1, hr1, hlo, hhi, hval, hTY1⟩ :=
    (tfind_spec "TY" h (σ.arrs "TY") hY.1 hN.tree hY.2.2).run ⟨hS.th, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = σ1.vars "ti" - 2 ^ h := ⟨_, rfl⟩
  have hℓ : ℓ < 2 ^ h := by omega
  have hti1 : σ1.vars "ti" = 2 ^ h + ℓ := by omega
  obtain ⟨hk', hmem, hmin⟩ := y_min_leaf hY.1 hN.big hY.2.1 hN.cap hℓ
    (by rw [← hti1]; exact hval) (y_root_ne_zero_of_nonempty hY.1 hN.big hY.2.1 hN.cap hne)
  have hrootv : (σ.arrs "TY").getD 1 0 = BIG - J.d ⟨ℓ, hk'⟩ := by
    have := hY.2.1 ℓ hℓ
    rw [← hti1, hval] at this
    rw [this]; simp [lfY, hk', hmem]
  have hdc : (J.d ⟨ℓ, hk'⟩ : ℤ) ≤ s (⟨k, hk⟩ : J.Job) := by
    have := hN.big ⟨ℓ, hk'⟩
    have := hN.big ⟨k, hk⟩
    unfold s
    rw [hrootv] at hlt
    omega
  -- drop the leaf
  have hStat1 : Stat J h BIG σ1 := hS.of_run hr1 (by decide) (by decide)
  have hX1 : TreeOK "TX" h (lfX J Ac) B σ1 := by
    unfold TreeOK; rw [hr1.frame_arr "TX" (by decide)]; exact hX
  have hY1 : TreeOK "TY" h (lfY J BIG Ac) B σ1 := by
    unfold TreeOK; rw [hr1.frame_arr "TY" (by decide)]; exact hY
  obtain ⟨σ2, hr2, hX2, hY2, hN2, hth2⟩ :=
    (dropLeaf_spec h ℓ (lfX J Ac) (lfY J BIG Ac) hN.tree hℓ).run
      ⟨hStat1.tN, hStat1.th, hti1, hX1, hY1⟩
  rw [lfX_erase hk'] at hX2
  rw [lfY_erase hk'] at hY2
  -- run := run - 1
  have hrun1 : σ2.vars "run" = Ac.card := by
    rw [hr2.frame_var "run" (by decide), hr1.frame_var "run" (by decide)]; exact hrun
  have hcpos : 1 ≤ Ac.card := Finset.card_pos.mpr hne
  have hrunB : σ2.vars "run" < B := by
    rw [hrun1]
    have := Finset.card_le_univ Ac
    simp only [Fintype.card_fin] at this
    have := hN.cap; have := Nat.lt_two_pow_self (n := h); have := hN.tree; omega
  have hr3 : Run B (.assign "run" (.bin .sub (V "run") (.lit 1))) σ2
      (σ2.setVar "run" (σ2.vars "run" - 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hrunB) (evalB_lit hh1) (by rw [Bop.apply_sub]; omega))
  have hall : Run B expireBody σ (σ2.setVar "run" (σ2.vars "run" - 1))
      (44 * h + 12 + (136 * h + 86 + 4)) := hr1.seq (hr2.seq hr3)
  have hStat3 : Stat J h BIG (σ2.setVar "run" (σ2.vars "run" - 1)) :=
    hS.of_run hall (by decide) (by decide)
  refine ⟨_, _, hall, ⟨hStat3, ?_, ?_, ⟨Ac.erase ⟨ℓ, hk'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · rw [hall.frame_var "jj" (by decide)]; exact hjj
  · rw [hall.frame_var "sz" (by decide)]; exact hsz
  · intro i hi
    have hnl : (⟨ℓ, hk'⟩ : J.Job) ∉ live Act ⟨k, hk⟩ := fun hl => by
      have := (mem_live.mp hl).2
      omega
    have hi' := hsub1 hi
    refine Finset.mem_erase.mpr ⟨?_, hi'⟩
    rintro rfl; exact hnl hi
  · exact (Finset.erase_subset _ _).trans hsub2
  · intro i hiAct hin
    by_cases hic : i = ⟨ℓ, hk'⟩
    · subst hic; exact hdc
    · exact hover i hiAct (fun hm => hin (Finset.mem_erase.mpr ⟨hic, hm⟩))
  · simp [hrun1, Finset.card_erase_of_mem hmem]
  · exact ⟨by simpa using hX2.1, by simpa using hX2.2.1, by simpa using hX2.2.2⟩
  · exact ⟨by simpa using hY2.1, by simpa using hY2.2.1, by simpa using hY2.2.2⟩
  · unfold Kb; omega
  · simp [hrun1]; omega

theorem EI.eval {J : Instance} {h BIG B k : ℕ} {hk : k < J.jobs} (hN : Num J B h BIG)
    {Act : Finset J.Job} {sz0 : ℕ} {σ : Env} (hI : EI J h BIG B k hk Act sz0 σ) :
    expireCond.evalB B σ = some (decide (BIG + J.q ⟨k, hk⟩ < J.d ⟨k, hk⟩ +
      (σ.arrs "TY").getD 1 0 + 1)) := by
  obtain ⟨hS, hjj, hsz, Ac, hsub1, hsub2, hover, hrun, hX, hY⟩ := hI
  have hh1 : 1 < B := by have := hN.tree; omega
  have hjjB : σ.vars "jj" < B := by
    rw [hjj]; have := hN.cap; have := Nat.lt_two_pow_self (n := h); have := hN.tree; omega
  have hlen1 : 1 < (σ.arrs "TY").length := by
    rw [hY.1.1]; have := Nat.one_le_two_pow (n := h); omega
  have hy1B : (σ.arrs "TY").getD 1 0 < B := by
    apply hY.2.2; rw [List.getD_eq_getElem _ _ hlen1]
    exact List.getElem_mem _
  have hy1get : (σ.arrs "TY")[1]? = some ((σ.arrs "TY").getD 1 0) := by
    rw [List.getD_eq_getElem _ _ hlen1]; exact List.getElem?_eq_getElem hlen1
  have hy1le : (σ.arrs "TY").getD 1 0 ≤ BIG := y1_le hY.1 hY.2.1
  exact expireCond_eval (B := B) (σ := σ) (big := BIG) (q := J.q ⟨k, hk⟩) (d := J.d ⟨k, hk⟩)
    (y1 := (σ.arrs "TY").getD 1 0) hS.big (by rw [hjj]; exact hS.q_get hk)
    (by rw [hjj]; exact hS.d_get hk) hy1get (by rw [hjj] at hjjB ⊢; exact hjjB) hN.bigB
    (by have := hN.bigq ⟨k, hk⟩; omega) (by have := hN.dsum ⟨k, hk⟩; omega) hy1B
    (hN.bigq ⟨k, hk⟩) (by have := hN.dsum ⟨k, hk⟩; omega)
    (by have := hN.dsum ⟨k, hk⟩; omega) hh1

/-- **The loop ends with exactly the live jobs**, and paid for itself. -/
theorem expire_run {J : Instance} {h BIG B k : ℕ} (hk : k < J.jobs) (hN : Num J B h BIG)
    (Act : Finset J.Job) (sz0 : ℕ) {σ : Env} (hI : EI J h BIG B k hk Act sz0 σ) :
    ∃ σ' K, Run B expire σ σ' K ∧ Stat J h BIG σ' ∧ σ'.vars "jj" = k ∧ σ'.vars "sz" = sz0 ∧
      σ'.vars "run" = (live Act ⟨k, hk⟩).card ∧
      TreeOK "TX" h (lfX J (live Act ⟨k, hk⟩)) B σ' ∧
      TreeOK "TY" h (lfY J BIG (live Act ⟨k, hk⟩)) B σ' ∧
      K + Kpop h * σ'.vars "run" ≤ Kpop h * σ.vars "run" + 1 + expireCond.size := by
  have hloop := Run.while_potential (B := B) (b := expireCond) (c := expireBody)
    (EI J h BIG B k hk Act sz0) (fun σ => Kpop h * σ.vars "run")
    (fun σ hI => ⟨_, hI.eval hN⟩)
    (fun σ hI hcond => by
      obtain ⟨σ', K, hr, hI', hK, hrun⟩ := expire_step hk hN Act sz0 hI hcond
      refine ⟨σ', K, hr, hI', ?_⟩
      have : Kpop h * σ.vars "run" = Kpop h * σ'.vars "run" + Kpop h := by
        rw [← hrun, Nat.mul_add, Nat.mul_one]
      show 1 + expireCond.size + K + Kpop h * σ'.vars "run" ≤ Kpop h * σ.vars "run"
      rw [this]; unfold Kpop; omega) hI
  obtain ⟨σ', K, hr, hI', hfalse, hpay⟩ := hloop
  have hev := hI'.eval hN
  obtain ⟨hS', hjj', hsz', Ac, hsub1, hsub2, hover, hrun', hX', hY'⟩ := hI'
  have heq : Ac = live Act ⟨k, hk⟩ := by
    apply Finset.Subset.antisymm _ hsub1
    intro i hi
    rw [mem_live]
    refine ⟨hsub2 hi, ?_⟩
    obtain ⟨c, hcAc, hroot, hcmin⟩ := y_root_min hY'.1 hN.big hY'.2.1 hN.cap ⟨i, hi⟩
    rw [hev] at hfalse
    have hnlt : ¬ (BIG + J.q ⟨k, hk⟩ < J.d ⟨k, hk⟩ + (σ'.arrs "TY").getD 1 0 + 1) := by
      have := Option.some.inj hfalse
      simpa using this
    rw [hroot] at hnlt
    have h1 := hN.big c
    have h2 := hcmin i hi
    unfold s
    omega
  subst heq
  exact ⟨σ', K, hr, hS', hjj', hsz', hrun', hX', hY', by simpa using hpay⟩

end Lax496464Proofs.Ram.T4Expire
