import Lax496464Proofs.Ram.PrintNat
import Lax496464Proofs.Ram.Program
import Lax496464Proofs.Ram.InstanceWord

/-!
# The Bit-Printing Output Stage

`Program.finalOut_spec`'s `header`/`dumps`/`target'` `write` the reduction's numbers raw to the
output tape. A Turing-machine composition needs the output already as zeros and ones — each
number as its self-delimiting code (`BitsNat.bitsNat`), so the whole output is
`(decisionWord ..).flatMap bitsNat`, which is `natBits` of the word `encodeDecisionInstance`
names. `printTail` here is the same output stage as `header; dumps; target'`, with each `write v`
replaced by `vv := v; printNat` (`Ram/PrintNat.lean`).
-/

namespace Lax496464Proofs.Ram.PrintTail

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.PrintNat (printNat printNat_spec)
open Lax496464Proofs.Ram.BitsNat (bitsNat)

abbrev V (s : String) : Expr := .var s

/-- Print the value of `e` in its self-delimiting code. -/
def printExpr (e : Expr) : Com := .seq (.assign "vv" e) printNat

theorem printExpr_run {B : ℕ} (hB : 2 < B) {e : Expr} {σ : Env} {v : ℕ}
    (he : e.evalB B σ = some v) (hvB : v < B) :
    ∃ σ', Run B (printExpr e) σ σ' (1 + e.size + (42 * v.size + 24)) ∧
      σ'.out = σ.out ++ bitsNat v ∧
      (∀ y, y ≠ "vv" → y ∉ printNat.wvars → σ'.vars y = σ.vars y) ∧
      (∀ a, a ∉ printNat.warrs → σ'.arrs a = σ.arrs a) ∧
      (¬ printNat.reads → σ'.inp = σ.inp) := by
  have hr1 := Run.assign (x := "vv") he
  obtain ⟨σ2, hr2, hq, hfv, hfa, hfi, -⟩ :=
    ((printNat_spec (B := B) (v := v) hB hvB).frame).run
      (σ := σ.setVar "vv" v) (by simp [Env.setVar])
  refine ⟨σ2, hr1.seq hr2, ?_, ?_, ?_, ?_⟩
  · rw [hq]; simp [Env.setVar]
  · intro y hy hyw; rw [hfv y hyw]; simp [Env.setVar, hy]
  · intro a ha; rw [hfa a ha]; simp [Env.setVar]
  · intro hc; rw [hfi hc]; simp [Env.setVar]

theorem printNat_wvars_sub : ∀ y ∈ printNat.wvars, y ∈ ["tt", "cnt", "jj", "xx"] := by decide
theorem printNat_warrs_nil : ∀ a, a ∉ printNat.warrs := by
  intro a; have : printNat.warrs = [] := by decide
  rw [this]; simp
theorem printNat_reads : ¬ printNat.reads := by decide

/-- The scratch scalars `printExpr` may change. -/
theorem printExpr_run' {B : ℕ} (hB : 2 < B) {e : Expr} {σ : Env} {v : ℕ}
    (he : e.evalB B σ = some v) (hvB : v < B) :
    ∃ σ', Run B (printExpr e) σ σ' (1 + e.size + (42 * v.size + 24)) ∧
      σ'.out = σ.out ++ bitsNat v ∧
      (∀ y, y ∉ ["vv", "tt", "cnt", "jj", "xx"] → σ'.vars y = σ.vars y) ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp := by
  obtain ⟨σ', hr, ho, hv, ha, hi⟩ := printExpr_run hB he hvB
  refine ⟨σ', hr, ho, fun y hy => hv y ?_ ?_, fun a => ha a (printNat_warrs_nil a),
    hi printNat_reads⟩
  · intro h; exact hy (by simp [h])
  · intro h; exact hy (by have := printNat_wvars_sub y h; simp at this ⊢; tauto)

def printBody (ix : String) (e : Expr) : Com :=
  .seq (printExpr e) (.assign ix (.bin .add (V ix) (.lit 1)))

def printLoop (ix bd : String) (e : Expr) : Com :=
  .seq (.assign ix (.lit 0)) (.while (.lt (V ix) (V bd)) (printBody ix e))

variable {B : ℕ}

/-- **A block, printed.** -/
theorem printLoop_spec (ix bd : String) (hix : ix ∉ ["vv", "tt", "cnt", "jj", "xx"])
    (N S : ℕ) (f : ℕ → ℕ) (e : Expr) (hB : 2 < B) (out₀ : List ℕ) (Base : Env → Prop)
    (hNB : N < B) (hfB : ∀ s < N, f s < B) (hfS : ∀ s < N, (f s).size ≤ S)
    (hes : e.size ≤ 2)
    (hbase : ∀ σ σ', Base σ →
      (∀ y, y ∉ [ix, "vv", "tt", "cnt", "jj", "xx"] → σ'.vars y = σ.vars y) →
      (∀ a, σ'.arrs a = σ.arrs a) → σ'.inp = σ.inp → Base σ')
    (hbd : ∀ σ, Base σ → σ.vars bd = N)
    (heval : ∀ σ, Base σ → σ.vars ix < N → e.evalB B σ = some (f (σ.vars ix))) :
    Spec B (fun σ => Base σ ∧ σ.out = out₀) (printLoop ix bd e)
      (fun _ σ' => Base σ' ∧ σ'.vars ix = N ∧
        σ'.out = out₀ ++ ((List.range N).map f).flatMap bitsNat)
      ((42 * S + 31 + 4) * N + 6) := by
  classical
  set I : Env → Prop := fun σ =>
    Base σ ∧ σ.vars ix ≤ N ∧
      σ.out = out₀ ++ ((List.range (σ.vars ix)).map f).flatMap bitsNat with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ix < N) (printBody ix e)
      (fun σ σ' => I σ' ∧ σ'.vars ix = σ.vars ix + 1) (42 * S + 31) := by
    refine Spec.of_exists fun σ ⟨⟨hBs, hle, ho⟩, hlt⟩ => ?_
    have hone : (1 : ℕ) < B := by omega
    have he := heval σ hBs hlt
    obtain ⟨σ2, hr2, ho2, hv2, ha2, hi2⟩ :=
      printExpr_run' hB he (hfB _ hlt)
    have hix2 : σ2.vars ix = σ.vars ix := hv2 ix hix
    have hlit : (Expr.lit 1).evalB B σ2 = some 1 := by
      simp only [Expr.evalB]; exact fit_self hone
    have hvar : (V ix).evalB B σ2 = some (σ.vars ix) :=
      by rw [← hix2]; exact evalB_var (by rw [hix2]; omega)
    have ha := Run.assign (B := B) (σ := σ2) (x := ix) (e := .bin .add (V ix) (.lit 1))
      (v := σ.vars ix + 1) (evalB_bin hvar hlit (by simpa using (by omega : σ.vars ix + 1 < B)))
    have hsz := hfS _ hlt
    refine ⟨_, _, hr2.seq ha, ?_, ⟨?_, ?_, ?_⟩, by simp⟩
    · simp only [Expr.size]
      have := hes
      omega
    · refine hbase σ _ hBs (fun y hy => ?_) (fun a => ?_) ?_
      · have hy' : y ∉ ["vv", "tt", "cnt", "jj", "xx"] := fun h => hy (by simp at h ⊢; tauto)
        have hyne : y ≠ ix := fun h => hy (by simp [h])
        simp [Env.setVar, hyne, hv2 y hy']
      · simp [Env.setVar, ha2]
      · simp [hi2]
    · simp [Env.setVar]; omega
    · simp only [Env.setVar, if_true]
      simp only [ho2, ho]
      simp [List.range_succ, List.flatMap_append]
  refine (Spec.forRangeZero ix bd I N (42 * S + 31) hNB (fun _ h => h.2.1)
    (fun _ h => hbd _ h.1) hbody).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hBs, ho⟩
    refine ⟨?_, by simp [Env.setVar], by simp [Env.setVar, ho]⟩
    exact hbase σ _ hBs (fun y hy => by
      have hyne : y ≠ ix := fun h => hy (by simp [h])
      simp [Env.setVar, hyne]) (fun a => by simp [Env.setVar]) (by simp [Env.setVar])
  · rintro σ σ' - ⟨⟨hBs, -, ho⟩, hix'⟩
    exact ⟨hBs, hix', by rw [ho, hix']⟩

/-! ## The whole printing stage -/

open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.Gen (Ctx Done Bnd)
open Lax496464Proofs.Ram.Program (OB eval_arr)

/-- The threshold `R·m·(2k − 1)`, computed into `"x2"` (`Program.target'` minus its `write`). -/
def targetPrep : Com :=
  .seq (.assign "x1" (.bin .sub (.bin .mul (.lit 2) (V "k")) (.lit 1)))
    (.seq (.assign "x2" (.bin .mul (V "R") (V "m")))
      (.assign "x2" (.bin .mul (V "x2") (V "x1"))))

/-- The whole output stage, in bits. -/
def printTail : Com :=
  .seq (printExpr (V "nj")) (.seq (printExpr (V "k"))
    (.seq (printLoop "s" "nj" (.get "PA" (V "s")))
      (.seq (printLoop "s" "nj" (.get "QA" (V "s")))
        (.seq (printLoop "s" "nj" (.get "DA" (V "s")))
          (.seq (printLoop "s" "nj" (.lit 1))
            (.seq targetPrep (printExpr (V "x2"))))))))

variable {P : Instance} {k : ℕ}

theorem OB_congr' {σ σ' : Env} (h : OB P k σ)
    (hv : ∀ y, y ∉ ["s", "vv", "tt", "cnt", "jj", "xx"] → σ'.vars y = σ.vars y)
    (ha : ∀ a, σ'.arrs a = σ.arrs a) : OB P k σ' := by
  obtain ⟨hC, hD, h1, h2⟩ := h
  refine ⟨hC.congr (fun y hy => hv y ?_) (fun a _ => ha a) (by rw [ha]) (by rw [ha])
    (by rw [ha]), ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · unfold Done; rw [ha, ha, ha]; exact hD
  · rw [hv "nj" (by decide)]; exact h1
  · rw [hv "k" (by decide)]; exact h2

theorem targetPrep_spec {B : ℕ} (hk2 : 2 ≤ k) (hRm2 : R P k * P.m < B) (hk2B : 2 * k < B)
    (htg : target P k < B) (hone : 1 < B) (hRB : R P k < B) (hmB : P.m < B) :
    Spec B (fun σ => σ.vars "R" = R P k ∧ σ.vars "m" = P.m ∧ σ.vars "k" = k) targetPrep
      (fun _ σ' => σ'.vars "x2" = target P k) 30 := by
  have hx : 2 * k - 1 < B := by omega
  have ht : target P k = R P k * P.m * (2 * k - 1) := rfl
  run_vcg
  all_goals (simp_all)

theorem printTail_spec {B : ℕ} (hb : Bnd P k B) (hk2 : 2 ≤ k) :
    Spec B (fun σ => OB P k σ ∧ σ.out = []) printTail
      (fun _ σ' => σ'.out =
        (Lax496464Proofs.Ram.InstanceWord.decisionWord (construct P k) (target P k)).flatMap
          bitsNat)
      (3 * (42 * B.size + 26) + 4 * ((42 * B.size + 31 + 4) * numJobs P k + 6) + 30) := by
  have hone := hb.one
  have hB2 : 2 < B := by have := hb.slack; omega
  have hnjB := hb.nj
  have hjobs := hb.jobs
  have hk2B := hb.k2_lt
  have hRB := hb.r_lt
  have htg := hb.tg_lt
  have hRm : R P k * P.m ≤ R P k * P.m * (2 * k - 1) := by
    rcases Nat.eq_zero_or_pos (R P k * P.m) with h | h
    · rw [h]; omega
    · exact Nat.le_mul_of_pos_right _ (by omega)
  have hRm2 : R P k * P.m < B := by
    have : target P k = R P k * P.m * (2 * k - 1) := rfl
    omega
  have hsz : ∀ v, v < B → v.size ≤ B.size := fun v hv => Nat.size_le_size hv.le
  refine Spec.of_exists fun σ ⟨hOB, hout⟩ => ?_
  -- nj
  have he1 : (V "nj").evalB B σ = some (numJobs P k) := by
    have := evalB_var (B := B) (σ := σ) (x := "nj") (by rw [hOB.2.2.1]; exact hnjB)
    rw [hOB.2.2.1] at this; exact this
  obtain ⟨σ1, hr1, ho1, hv1, ha1, hi1⟩ := printExpr_run' hB2 he1 hnjB
  have hO1 : OB P k σ1 := OB_congr' hOB (fun y hy => hv1 y (fun h => hy (by simp at h ⊢; tauto)))
    ha1
  -- k
  have he2 : (V "k").evalB B σ1 = some k := by
    have hk1 : σ1.vars "k" = k := by rw [hO1.2.2.2]
    have := evalB_var (B := B) (σ := σ1) (x := "k") (by rw [hk1]; omega)
    rw [hk1] at this; exact this
  obtain ⟨σ2, hr2, ho2, hv2, ha2, hi2⟩ := printExpr_run' hB2 he2 (by omega)
  have hO2 : OB P k σ2 := OB_congr' hO1 (fun y hy => hv2 y (fun h => hy (by simp at h ⊢; tauto)))
    ha2
  -- the four blocks
  have mk : ∀ (f : ℕ → ℕ) (e : Expr), e.size ≤ 2 → (∀ s < numJobs P k, f s < B) →
      (∀ σ : Env, OB P k σ → σ.vars "s" < numJobs P k → e.evalB B σ = some (f (σ.vars "s"))) →
      ∀ o' : List ℕ,
      Spec B (fun σ => OB P k σ ∧ σ.out = o') (printLoop "s" "nj" e)
        (fun _ σ' => OB P k σ' ∧ σ'.vars "s" = numJobs P k ∧
          σ'.out = o' ++ ((List.range (numJobs P k)).map f).flatMap bitsNat)
        ((42 * B.size + 31 + 4) * numJobs P k + 6) := by
    intro f e hes hf heval o'
    exact printLoop_spec "s" "nj" (by decide) (numJobs P k) B.size f e hB2 o' (OB P k) hnjB hf
      (fun s hs => hsz _ (hf s hs)) hes
      (fun σ σ' h hv ha _ => OB_congr' h (fun y hy => hv y (by simp at hy ⊢; tauto)) ha)
      (fun σ h => h.2.2.1) heval
  have dP := mk (jp P k) (.get "PA" (V "s")) (by simp [Expr.size]) (fun s hs => (hjobs s hs).1)
    (fun σ h hs => eval_arr "PA" (jp P k) (h.ctx.hPA) (fun s hs => (h.done s hs).1)
      (fun s hs => (hjobs s hs).1) hnjB hs)
  have dQ := mk (jq P k) (.get "QA" (V "s")) (by simp [Expr.size]) (fun s hs => (hjobs s hs).2.1)
    (fun σ h hs => eval_arr "QA" (jq P k) (h.ctx.hQA) (fun s hs => (h.done s hs).2.1)
      (fun s hs => (hjobs s hs).2.1) hnjB hs)
  have dD := mk (jd P k) (.get "DA" (V "s")) (by simp [Expr.size]) (fun s hs => (hjobs s hs).2.2)
    (fun σ h hs => eval_arr "DA" (jd P k) (h.ctx.hDA) (fun s hs => (h.done s hs).2.2)
      (fun s hs => (hjobs s hs).2.2) hnjB hs)
  have dW := mk (fun _ => 1) (.lit 1) (by simp [Expr.size]) (fun s hs => hone)
    (fun σ h hs => evalB_lit hone)
  obtain ⟨σ3, hr3, hO3, -, ho3⟩ := (dP σ2.out).run ⟨hO2, rfl⟩
  obtain ⟨σ4, hr4, hO4, -, ho4⟩ := (dQ σ3.out).run ⟨hO3, rfl⟩
  obtain ⟨σ5, hr5, hO5, -, ho5⟩ := (dD σ4.out).run ⟨hO4, rfl⟩
  obtain ⟨σ6, hr6, hO6, -, ho6⟩ := (dW σ5.out).run ⟨hO5, rfl⟩
  -- the threshold
  obtain ⟨σ7, hr7, hx7, hfv7, hfa7, hfi7, hfo7⟩ :=
    (targetPrep_spec (P := P) hk2 hRm2 hk2B htg hone hRB hb.m_lt).frame.run (σ := σ6)
      ⟨hO6.ctx.hR, hO6.ctx.hm, hO6.2.2.2⟩
  have hout7 : σ7.out = σ6.out := hfo7 (by simp [Com.NoWrite, targetPrep])
  have he8 : (V "x2").evalB B σ7 = some (target P k) := by
    have := evalB_var (B := B) (σ := σ7) (x := "x2") (by rw [hx7]; exact htg)
    rw [hx7] at this; exact this
  obtain ⟨σ8, hr8, ho8, -, -, -⟩ := printExpr_run' hB2 he8 htg
  refine ⟨σ8, _, ?_, le_rfl, ?_⟩
  · show Run B printTail σ σ8 _
    unfold printTail
    refine (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq hr8))))))).mono ?_
    have h1 := hsz _ hnjB
    have h2 := hsz k (by omega)
    have h3 := hsz _ htg
    simp only [Expr.size]
    omega
  · have hd := Lax496464Proofs.Ram.Program.decisionWord_construct (P := P) (k := k)
    rw [hd]
    rw [ho8, hout7, ho6, ho5, ho4, ho3, ho2, ho1, hout]
    simp [List.flatMap_append]

end Lax496464Proofs.Ram.PrintTail
