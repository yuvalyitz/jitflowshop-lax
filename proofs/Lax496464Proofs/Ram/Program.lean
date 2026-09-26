import Lax496464Proofs.Ram.Gen
import Lax496464Proofs.Ram.ReadHS
import Lax496464Proofs.Ram.Emit
import Lax496464Proofs.Ram.Reduction
import Lax496464Proofs.Ram.Build
import Lax496464Proofs.Ram.CsrWord

/-!
# The reduction's program

`readHS`, then `build`, then the constants of the construction, then the three generation
passes, and finally the four blocks and the target written from the arrays.
-/

namespace Lax496464Proofs.Ram.Program

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.Construction Lax496464Proofs.Ram.Gen
  Lax496464Proofs.Ram.Values

/-- The constants: `R`, `Q`, `dc = R·m·n`, `sc = R·|memberList|` and the number of jobs. -/
def consts : Com :=
  .seq (.assign "x1" (.bin .sub (V "n") (.lit 1)))
  (.seq (.assign "x1" (.bin .mul (V "k") (V "x1")))
  (.seq (.assign "R" (.bin .add (V "x1") (.lit 2)))
  (.seq (.assign "x1" (.bin .sub (V "k") (.lit 1)))
  (.seq (.assign "x2" (.bin .add (V "n") (.lit 1)))
  (.seq (.assign "Q" (.bin .mul (V "x1") (V "x2")))
  (.seq (.assign "dc" (.bin .mul (V "R") (V "m")))
  (.seq (.assign "dc" (.bin .mul (V "dc") (V "n")))
  (.seq (.assign "sc" (.bin .mul (V "R") (V "Lc")))
  (.seq (.assign "nj" (.bin .add (V "sc") (V "dc")))
        (.assign "nj" (.bin .add (V "nj") (V "dc"))))))))))))

variable {P : Lax496464.HittingSet.Instance} {k : ℕ}

theorem consts_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    Spec B (fun σ => σ.vars "n" = P.n ∧ σ.vars "m" = P.m ∧ σ.vars "k" = k ∧
        σ.vars "Lc" = (memberList P).length) consts
      (fun σ σ' => σ'.vars "R" = R P k ∧ σ'.vars "Q" = Q P k ∧
        σ'.vars "dc" = dumCount P k ∧ σ'.vars "sc" = selCount P k ∧
        σ'.vars "nj" = numJobs P k ∧
        (∀ y, y ≠ "x1" → y ≠ "x2" → y ≠ "R" → y ≠ "Q" → y ≠ "dc" → y ≠ "sc" → y ≠ "nj" →
          σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 100 := by
  have hone := hb.one
  have hnB := hb.n_lt
  have hnj := hb.nj
  have hn : 1 ≤ P.n := by omega
  have hR := hb.r_lt
  have hQ := hb.q_lt
  have hmB := hb.m_lt
  have hlcB := hb.lc_lt
  have hRm' : R P k * P.m ≤ R P k * P.m * P.n := Nat.le_mul_of_pos_right _ hn
  have hkB : k < B := by omega
  have hnQ := n_succ_le_Q (P := P) hk
  have hdc : dumCount P k = R P k * P.m * P.n := rfl
  have hRm : R P k * P.m ≤ dumCount P k := by
    rw [hdc]; exact Nat.le_mul_of_pos_right _ hn
  have hsc : selCount P k = R P k * (memberList P).length := rfl
  have hnj' : numJobs P k = selCount P k + dumCount P k + dumCount P k := by
    simp only [numJobs]; omega
  have hkR : k * (P.n - 1) + 2 = R P k := rfl
  have hQd : (k - 1) * (P.n + 1) = Q P k := rfl
  refine Spec.pre (P := fun σ => σ.vars "n" = P.n ∧ σ.vars "m" = P.m ∧ σ.vars "k" = k ∧
      σ.vars "Lc" = (memberList P).length) ?_ (fun _ h => h)
  run_vcg
  all_goals (simp_all)
  all_goals omega

/-! ## The output -/

open Lax496464Proofs.Ram.Emit (emitLoop emitLoop_spec)

/-- The two header entries: the number of jobs and the number of machines. -/
def header : Com := .seq (.write (V "nj")) (.write (V "k"))

/-- The four blocks, each written from its array. -/
def dumps : Com :=
  .seq (emitLoop "s" "nj" (.get "PA" (V "s")))
    (.seq (emitLoop "s" "nj" (.get "QA" (V "s")))
      (.seq (emitLoop "s" "nj" (.get "DA" (V "s")))
        (emitLoop "s" "nj" (.lit 1))))

/-- The threshold: `R·m·(2k − 1)`. -/
def target' : Com :=
  .seq (.assign "x1" (.bin .sub (.bin .mul (.lit 2) (V "k")) (.lit 1)))
    (.seq (.assign "x2" (.bin .mul (V "R") (V "m")))
      (.seq (.assign "x2" (.bin .mul (V "x2") (V "x1"))) (.write (V "x2"))))

/-- What `dumps` needs to keep true. -/
def OB (P : Lax496464.HittingSet.Instance) (k : ℕ) (σ : Env) : Prop :=
  Ctx P k σ ∧ Done P k σ (numJobs P k) ∧ σ.vars "nj" = numJobs P k ∧ σ.vars "k" = k

theorem OB.ctx {σ : Env} (h : OB P k σ) : Ctx P k σ := h.1
theorem OB.done {σ : Env} (h : OB P k σ) : Done P k σ (numJobs P k) := h.2.1

theorem OB.setVar {σ : Env} (h : OB P k σ) {y : String} (v : ℕ)
    (hy : y ∉ ["n", "m", "Q", "R", "Lc", "sc", "dc", "nj", "k"]) : OB P k (σ.setVar y v) := by
  obtain ⟨hC, hD, h1, h2⟩ := h
  have hne : ∀ z ∈ ["n", "m", "Q", "R", "Lc", "sc", "dc", "nj", "k"], z ≠ y :=
    fun z hz h => hy (h ▸ hz)
  refine ⟨hC.setVar v (fun hh => hy (by simp at hh ⊢; tauto)), hD, ?_, ?_⟩
  · simp [hne "nj" (by simp), h1]
  · simp [hne "k" (by simp), h2]

theorem OB.out {σ : Env} (h : OB P k σ) (o : List ℕ) : OB P k { σ with out := o } := by
  obtain ⟨hC, hD, h1, h2⟩ := h
  exact ⟨hC.congr (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl, hD, h1, h2⟩

theorem _root_.Lax496464Proofs.Ram.Gen.Ctx.hPA {σ : Env} (h : Ctx P k σ) : (σ.arrs "PA").length = numJobs P k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h
theorem _root_.Lax496464Proofs.Ram.Gen.Ctx.hQA {σ : Env} (h : Ctx P k σ) : (σ.arrs "QA").length = numJobs P k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h
theorem _root_.Lax496464Proofs.Ram.Gen.Ctx.hDA {σ : Env} (h : Ctx P k σ) : (σ.arrs "DA").length = numJobs P k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h; exact h

theorem eval_arr {B N : ℕ} (a : String) (f : ℕ → ℕ) {σ : Env} (hlen : (σ.arrs a).length = N)
    (hcell : ∀ s < N, (σ.arrs a).getD s 0 = f s) (hfB : ∀ s < N, f s < B) (hNB : N < B)
    (hs : σ.vars "s" < N) : (Expr.get a (V "s")).evalB B σ = some (f (σ.vars "s")) := by
  have hv : (V "s").evalB B σ = some (σ.vars "s") := evalB_var (by omega)
  have h := RunStep.eval_get B σ a (V "s") (σ.vars "s") hv (by omega)
    (by rw [hcell _ hs]; exact hfB _ hs)
  rw [hcell _ hs] at h
  exact h

theorem dumps_spec {B : ℕ} (hb : Bnd P k B) (o : List ℕ) :
    Spec B (fun σ => OB P k σ ∧ σ.out = o) dumps
      (fun _ σ' => OB P k σ' ∧ σ'.out = o ++ ((List.range (numJobs P k)).map (jp P k) ++
        ((List.range (numJobs P k)).map (jq P k) ++ ((List.range (numJobs P k)).map (jd P k) ++
          (List.range (numJobs P k)).map (fun _ => 1)))))
      (4 * ((1 + 3 + 4 + 4) * numJobs P k + 6)) := by
  have hone := hb.one
  have hnjB := hb.nj
  have hjobs := hb.jobs
  have mk : ∀ (a : String) (f : ℕ → ℕ),
      (∀ σ : Env, OB P k σ → (σ.arrs a).length = numJobs P k) →
      (∀ σ : Env, OB P k σ → ∀ s < numJobs P k, (σ.arrs a).getD s 0 = f s) →
      (∀ s < numJobs P k, f s < B) → ∀ o' : List ℕ,
      Spec B (fun σ => OB P k σ ∧ σ.out = o') (emitLoop "s" "nj" (.get a (V "s")))
        (fun _ σ' => OB P k σ' ∧ σ'.vars "s" = numJobs P k ∧
          σ'.out = o' ++ (List.range (numJobs P k)).map f)
        ((1 + 2 + 4 + 4) * numJobs P k + 6) := by
    intro a f hl hc hf o'
    exact emitLoop_spec "s" "nj" (by decide) (numJobs P k) f (.get a (V "s")) o' (OB P k) hnjB
      (fun σ v h => h.setVar v (by decide)) (fun σ o h => h.out o) (fun σ h => h.2.2.1)
      (fun σ h hs => eval_arr a f (hl σ h) (hc σ h) hf hnjB hs)
  have dP := mk "PA" (jp P k) (fun σ h => h.ctx.hPA) (fun σ h s hs => (h.done s hs).1)
    (fun s hs => (hjobs s hs).1)
  have dQ := mk "QA" (jq P k) (fun σ h => h.ctx.hQA) (fun σ h s hs => (h.done s hs).2.1)
    (fun s hs => (hjobs s hs).2.1)
  have dD := mk "DA" (jd P k) (fun σ h => h.ctx.hDA) (fun σ h s hs => (h.done s hs).2.2)
    (fun s hs => (hjobs s hs).2.2)
  have dW : ∀ o' : List ℕ, Spec B (fun σ => OB P k σ ∧ σ.out = o') (emitLoop "s" "nj" (.lit 1))
      (fun _ σ' => OB P k σ' ∧ σ'.vars "s" = numJobs P k ∧
        σ'.out = o' ++ (List.range (numJobs P k)).map (fun _ => 1))
      ((1 + 1 + 4 + 4) * numJobs P k + 6) := fun o' =>
    emitLoop_spec "s" "nj" (by decide) (numJobs P k) (fun _ => 1) (.lit 1) o' (OB P k) hnjB
      (fun σ v h => h.setVar v (by decide)) (fun σ o h => h.out o) (fun σ h => h.2.2.1)
      (fun σ h hs => evalB_lit hone)
  refine Spec.of_exists fun σ ⟨hOB, hout⟩ => ?_
  obtain ⟨σ1, hr1, hO1, -, ho1⟩ := (dP o).run ⟨hOB, hout⟩
  obtain ⟨σ2, hr2, hO2, -, ho2⟩ := (dQ σ1.out).run ⟨hO1, rfl⟩
  obtain ⟨σ3, hr3, hO3, -, ho3⟩ := (dD σ2.out).run ⟨hO2, rfl⟩
  obtain ⟨σ4, hr4, hO4, -, ho4⟩ := (dW σ3.out).run ⟨hO3, rfl⟩
  refine ⟨σ4, _, (hr1.seq (hr2.seq (hr3.seq hr4))).mono ?_, le_rfl, hO4, ?_⟩
  · omega
  · rw [ho4, ho3, ho2, ho1]; simp only [List.append_assoc]

theorem header_spec {B : ℕ} (hnjB : numJobs P k < B) (hkB : k < B) :
    Spec B (fun σ => σ.vars "nj" = numJobs P k ∧ σ.vars "k" = k ∧ σ.out = []) header
      (fun σ σ' => σ'.out = [numJobs P k, k] ∧ σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp) 10 := by
  run_vcg
  all_goals simp_all

theorem target_spec {B : ℕ} (hk2 : 2 ≤ k) (hRm2 : R P k * P.m < B) (hk2B : 2 * k < B)
    (htg : target P k < B) (hone : 1 < B) (hRB : R P k < B) (hmB : P.m < B) (o : List ℕ) :
    Spec B (fun σ => σ.vars "R" = R P k ∧ σ.vars "m" = P.m ∧ σ.vars "k" = k ∧ σ.out = o)
      target' (fun _σ σ' => σ'.out = o ++ [target P k]) 30 := by
  have hx : 2 * k - 1 < B := by omega
  have ht : target P k = R P k * P.m * (2 * k - 1) := rfl
  run_vcg
  all_goals (simp_all)

theorem finalOut_spec {B : ℕ} (hb : Bnd P k B) (hk2 : 2 ≤ k) :
    Spec B (fun σ => OB P k σ ∧ σ.out = []) (.seq header (.seq dumps target'))
      (fun _ σ' => σ'.out = [numJobs P k, k] ++ ((List.range (numJobs P k)).map (jp P k) ++
        ((List.range (numJobs P k)).map (jq P k) ++ ((List.range (numJobs P k)).map (jd P k) ++
          (List.range (numJobs P k)).map (fun _ => 1)))) ++ [target P k])
      (10 + (4 * ((1 + 3 + 4 + 4) * numJobs P k + 6) + 30)) := by
  have hone := hb.one
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
  refine Spec.of_exists fun σ ⟨hOB, hout⟩ => ?_
  obtain ⟨σ1, hr1, ho1, hv1, ha1, hi1⟩ :=
    (header_spec (P := P) (k := k) hb.nj (by omega)).run ⟨hOB.2.2.1, hOB.2.2.2, hout⟩
  have hO1 : OB P k σ1 ∧ σ1.out = [numJobs P k, k] := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ho1⟩
    · exact hOB.ctx.congr (fun y _ => by rw [hv1]) (fun a _ => by rw [ha1]) (by rw [ha1])
        (by rw [ha1]) (by rw [ha1])
    · unfold Done; rw [ha1]; exact hOB.done
    · rw [hv1]; exact hOB.2.2.1
    · rw [hv1]; exact hOB.2.2.2
  obtain ⟨σ2, hr2, hO2, ho2⟩ := (dumps_spec hb [numJobs P k, k]).run hO1
  obtain ⟨σ3, hr3, ho3⟩ := (target_spec (P := P) hk2 hRm2 hk2B htg hone hRB hb.m_lt σ2.out).run
    ⟨hO2.ctx.hR, hO2.ctx.hm, hO2.2.2.2, rfl⟩
  refine ⟨σ3, _, (hr1.seq (hr2.seq hr3)).mono ?_, le_rfl, ?_⟩
  · omega
  · rw [ho3, ho2]

/-! ## The whole program -/

open Lax496464Proofs.Ram.ReadHS (readHS readHS_spec)
open Lax496464Proofs.Ram.Build (build build_spec RC CurInv Offs costBuild)

/-- **The reduction's program.** -/
def prog : Com :=
  .seq readHS (.seq build (.seq consts (.seq gen (.seq header (.seq dumps target')))))

theorem offs_of_encodes {x : List ℕ} {P : Lax496464.HittingSet.Instance} {k : ℕ}
    (h : Encodes x P k) : Offs x where
  mono := fun j hj => by
    rw [h.setCount_eq] at hj; exact h.offset_mono j hj
  le_last := by
    have key : ∀ d j, j + d = setCount x → offset x j ≤ offset x (setCount x) := by
      intro d
      induction d with
      | zero => intro j hj; rw [show setCount x = j by omega]
      | succ d ih =>
        intro j hj
        have h1 : offset x j ≤ offset x (j + 1) := by
          rw [h.setCount_eq] at hj; exact h.offset_mono j (by omega)
        exact h1.trans (ih (j + 1) (by omega))
    intro j hj
    exact key (setCount x - j) j (by omega)

theorem length_memberList_le {x : List ℕ} {P : Lax496464.HittingSet.Instance} {k : ℕ}
    (h : Encodes x P k) : (memberList P).length ≤ P.n * P.m := by
  have := Build.length_prefixPairs_le (x := x) (setCount x)
  rw [← Build.wmemberList_eq_prefix (x := x), Members.wmemberList_eq h, h.setCount_eq,
    h.universeSize_eq] at this
  rw [Nat.mul_comm]; exact this

theorem decisionWord_construct :
    InstanceWord.decisionWord (construct P k) (target P k) =
      [numJobs P k, k] ++ ((List.range (numJobs P k)).map (jp P k) ++
        ((List.range (numJobs P k)).map (jq P k) ++ ((List.range (numJobs P k)).map (jd P k) ++
          (List.range (numJobs P k)).map (fun _ => 1)))) ++ [target P k] := by
  have hb : ∀ g : ℕ → ℕ, InstanceWord.blk (construct P k)
      (fun t : Fin (construct P k).jobs => g t) = (List.range (numJobs P k)).map g := fun g => by
    show (List.finRange (numJobs P k)).map (fun t : Fin (numJobs P k) => g t) = _
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  unfold InstanceWord.decisionWord InstanceWord.instanceWord
  have hp : (construct P k).p = fun t : Fin (construct P k).jobs => jp P k t := rfl
  have hq : (construct P k).q = fun t : Fin (construct P k).jobs => jq P k t := rfl
  have hd : (construct P k).d = fun t : Fin (construct P k).jobs => jd P k t := rfl
  have hw : (construct P k).w = fun t : Fin (construct P k).jobs => (fun _ : ℕ => 1) t := rfl
  rw [hp, hq, hd, hw, hb (jp P k), hb (jq P k), hb (jd P k), hb (fun _ => 1)]
  rfl

/-- The cost bound of `prog`, as the sum of its phases. -/
def progCost (P : Lax496464.HittingSet.Instance) (k : ℕ) (x : List ℕ) : ℕ :=
  (12 * (setCount x + 1) + 6 + (12 * offset x (setCount x) + 6) + 20) +
  (costBuild (universeSize x) (setCount x) (offset x (setCount x)) +
  (100 +
  ((2 + (((400 + 4) * (memberList P).length + 6 + 4 + 4) * R P k + 6)) +
    (costDum P.n P.m (R P k) + costDum P.n P.m (R P k)) +
  (10 + (4 * ((1 + 3 + 4 + 4) * numJobs P k + 6) + 30)))))

theorem _root_.Lax496464Proofs.Ram.Gen.Bnd.small {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    P.m + 2 < B ∧ P.n * P.m + 1 < B := by
  have hnj := hb.nj
  have hs := hb.slack
  have hR : 2 ≤ R P k := by unfold R; omega
  have hd : dumCount P k = R P k * P.m * P.n := rfl
  have hle : dumCount P k ≤ numJobs P k := by simp only [numJobs]; omega
  have h4 : 2 * (P.m * P.n) ≤ R P k * P.m * P.n := by
    calc 2 * (P.m * P.n) ≤ R P k * (P.m * P.n) := Nat.mul_le_mul_right _ hR
      _ = R P k * P.m * P.n := by ring
  rcases Nat.eq_zero_or_pos (P.m * P.n) with h0 | h0
  · have hm0 : P.m = 0 ∨ P.n = 0 := Nat.mul_eq_zero.mp h0
    rcases hm0 with hm0 | hn0
    · refine ⟨by omega, ?_⟩; rw [hm0]; omega
    · omega
  · have hm1 : 1 ≤ P.m := Nat.pos_of_ne_zero (fun h1 => by rw [h1] at h0; simp at h0)
    have hn1 : 2 ≤ P.n := by omega
    have : 4 * P.m ≤ 2 * (P.m * P.n) := by nlinarith
    refine ⟨by omega, ?_⟩
    rw [Nat.mul_comm]; omega

theorem prog_spec {B : ℕ} {x : List ℕ} (h : Encodes x P k) (hxB : ∀ v ∈ x, v < B)
    (hb : Bnd P k B) (hLB : offset x (setCount x) + 1 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "OFF").length = P.m + 1 ∧
        (σ.arrs "MEM").length = offset x P.m ∧ (σ.arrs "MJ").length = P.n * P.m ∧
        (σ.arrs "MI").length = P.n * P.m ∧ (σ.arrs "PA").length = numJobs P k ∧
        (σ.arrs "QA").length = numJobs P k ∧ (σ.arrs "DA").length = numJobs P k)
      prog (fun _ σ' => σ'.out = InstanceWord.decisionWord (construct P k) (target P k))
      (progCost P k x) := by
  have hone := hb.one
  have hk2 := h.size_bounds.1
  have hkn := h.size_bounds.2
  have hn : universeSize x = P.n := h.universeSize_eq
  have hm : setCount x = P.m := h.setCount_eq
  have hlen : x.length = 4 + setCount x + offset x (setCount x) := by
    rw [h.length_eq, hm]
  obtain ⟨hmB2, hnmB⟩ := hb.small hk2 hkn
  have hmB : setCount x + 2 < B := by rw [hm]; exact hmB2
  have hnmB' : universeSize x * setCount x + 1 < B := by rw [hn, hm]; exact hnmB
  have hnB : universeSize x < B := by rw [hn]; exact hb.n_lt
  have hLB' : offset x (setCount x) < B := by omega
  have hoffs := offs_of_encodes h
  have hread := (readHS_spec (x := x) hxB hone hlen hmB hLB).frame
  have hbuild := (build_spec (x := x) hxB hone hoffs hLB' hnB hnmB' (by omega)).frame
  have hcons := consts_spec hb hk2 hkn
  have hgen := (gen_spec hb hk2 hkn).frame
  have hfin := finalOut_spec hb hk2
  refine Spec.of_exists fun σ ⟨hinp, hout, hOFF, hMEM, hMJ, hMI, hPA, hQA, hDA⟩ => ?_
  -- reading the word
  obtain ⟨σ1, hr1, ⟨hRC, hk1, hin1, hout1⟩, hfv1, hfa1, -, -⟩ :=
    hread.run ⟨hinp, hout, by rw [hm]; exact hOFF, by rw [hm]; exact hMEM⟩
  -- building the membership pairs
  obtain ⟨σ2, hr2, ⟨hRC2, hCur2⟩, hfv2, hfa2, -, hfo2⟩ := hbuild.run ⟨hRC, by
      rw [hfa1 "MJ" (by decide), hMJ, hn, hm], by rw [hfa1 "MI" (by decide), hMI, hn, hm]⟩
  have hout2 : σ2.out = [] := by rw [hfo2 (by decide), hout1]
  -- the constants
  have hn2 : σ2.vars "n" = P.n := by rw [hRC2.1, hn]
  have hm2 : σ2.vars "m" = P.m := by rw [hRC2.2.1, hm]
  have hk2v : σ2.vars "k" = k := by
    rw [hfv2 "k" (by decide), hk1, h.solutionSize_eq]
  have hwml : Members.wmemberList x = memberList P := Members.wmemberList_eq h
  have hLc2 : σ2.vars "Lc" = (memberList P).length := by rw [hCur2.1, hwml]
  obtain ⟨σ3, hr3, hR3, hQ3, hdc3, hsc3, hnj3, hfv3, hfa3, hinp3, hout3⟩ :=
    hcons.run ⟨hn2, hm2, hk2v, hLc2⟩
  -- the context of the generation passes
  have hcap := length_memberList_le h
  have hCtx3 : Ctx P k σ3 := by
    refine ⟨?_, ?_, hQ3, hR3, ?_, hsc3, hdc3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfv3 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hn2]
    · rw [hfv3 "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hm2]
    · rw [hfv3 "Lc" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hLc2]
    · rw [hfa3]; have := hCur2.2.2.1; rw [hn, hm] at this; omega
    · rw [hfa3]; have := hCur2.2.2.2; rw [hn, hm] at this; omega
    · intro u hu; rw [hfa3]
      have := (hCur2.2.1 u (by rw [hwml]; exact hu)).1
      rw [hwml] at this; exact this
    · intro u hu; rw [hfa3]
      have := (hCur2.2.1 u (by rw [hwml]; exact hu)).2
      rw [hwml] at this; exact this
    · rw [hfa3, hfa2 "PA" (by decide), hfa1 "PA" (by decide)]; exact hPA
    · rw [hfa3, hfa2 "QA" (by decide), hfa1 "QA" (by decide)]; exact hQA
    · rw [hfa3, hfa2 "DA" (by decide), hfa1 "DA" (by decide)]; exact hDA
  have hDone3 : Done P k σ3 0 := fun s hs => absurd hs (Nat.not_lt_zero _)
  obtain ⟨σ4, hr4, ⟨hCtx4, hDone4, ht4⟩, hgfv, hgfa, -, hgfo⟩ := hgen.run ⟨hCtx3, hDone3⟩
  have hOB4 : OB P k σ4 := by
    refine ⟨hCtx4, hDone4, ?_, ?_⟩
    · rw [hgfv "nj" (by decide), hnj3]
    · rw [hgfv "k" (by decide), hfv3 "k" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hk2v]
  have hout4 : σ4.out = [] := by
    rw [hgfo (by decide), hout3, hout2]
  obtain ⟨σ5, hr5, hout5⟩ := hfin.run ⟨hOB4, hout4⟩
  refine ⟨σ5, _, (hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5)))).mono ?_, le_rfl, ?_⟩
  · unfold progCost; omega
  · rw [hout5, decisionWord_construct]

end Lax496464Proofs.Ram.Program
