import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.FormEnc
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

/-! # Phase 10: the code of the sentence

The quantifier block (`qOut_spec`) and the conjuncts of the sentence that do not depend on the
clauses (`cOut_spec`, `dOut_spec`, `vtOut_spec`, `ytOut_spec`, `yOut_spec`), each written by a
counted loop (`wloop`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.FormEnc
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

variable {d k B : ℕ}

/-- **A loop that writes `f i` in turn `i`.** -/
theorem wloop (i n : String) (N : ℕ) (I : Env → Prop) (f : ℕ → List ℕ) (out0 : List ℕ) {body : Com}
    {Kb : ℕ} (hN : N < B) (hn : ∀ σ, I σ → σ.vars n = N)
    (hbody : Spec B (fun σ => (I σ ∧ σ.vars i ≤ N ∧
        σ.out = out0 ++ (List.range (σ.vars i)).flatMap f) ∧ σ.vars i < N) body
      (fun σ σ' => (I σ' ∧ σ'.vars i ≤ N ∧ σ'.out = out0 ++ (List.range (σ'.vars i)).flatMap f) ∧
        σ'.vars i = σ.vars i + 1) Kb) :
    Spec B (fun σ => I (σ.setVar i 0) ∧ σ.out = out0) (loop i n body)
      (fun _ σ' => I σ' ∧ σ'.out = out0 ++ (List.range N).flatMap f) ((Kb + 4) * N + 6) := by
  refine Spec.post (Spec.pre (Spec.forRangeZero i n
    (fun σ => I σ ∧ σ.vars i ≤ N ∧ σ.out = out0 ++ (List.range (σ.vars i)).flatMap f) N Kb hN
    (fun σ h => h.2.1) (fun σ h => hn σ h.1) hbody) ?_) ?_
  · rintro σ ⟨hI, ho⟩
    exact ⟨hI, by simp [Env.setVar], by simp [Env.setVar, ho]⟩
  · rintro σ σ' - ⟨⟨hI, -, ho⟩, hi⟩
    exact ⟨hI, by rw [ho, hi]⟩

/-- The constants the sentence is written with. -/
def FC (d k : ℕ) (σ : Env) : Prop :=
  σ.vars "w_k" = k ∧ σ.vars "w_K1" = k + 1 ∧ σ.vars "w_F" = FF d k ∧ σ.vars "w_nv" = nv d k ∧
    σ.vars "w_d1" = d + 1

/-- The bounds the sentence needs. -/
structure FB (d k B : ℕ) : Prop where
  nv : nv d k + 1 < B
  small : d + k + 6 < B

theorem FF_le_nv (d k : ℕ) : FF d k ≤ nv d k := by
  unfold nv; nlinarith

/-! ### The quantifiers -/

theorem qOut_spec (hF : FB d k B) (out0 : List ℕ) :
    Spec B (fun σ => FC d k σ ∧ σ.out = out0) qOut
      (fun _ σ' => FC d k σ' ∧ σ'.out = out0 ++ qW d k) ((10 + 4) * nv d k + 6) := by
  have h1 := hF.nv
  have h2 := hF.small
  refine Spec.pre (Spec.post (wloop "w_v" "w_nv" (nv d k) (FC d k) (fun v => [6, v]) out0
    (Kb := 10) (by omega) (fun σ h => h.2.2.2.1) ?_) (fun _ _ _ h => by rw [qW]; exact h)) ?_
  · refine Spec.pre (P := fun σ => ((FC d k σ ∧ σ.vars "w_v" ≤ nv d k ∧
        σ.out = out0 ++ (List.range (σ.vars "w_v")).flatMap fun v => [6, v]) ∧
        σ.vars "w_v" < nv d k) ∧ 6 < B) ?_ (fun σ h => ⟨h, by omega⟩)
    run_vcg
    all_goals (try simp only [FC] at *)
    all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)
  · rintro σ ⟨hC, ho⟩
    refine ⟨?_, ho⟩
    obtain ⟨a, b, c, e, f⟩ := hC
    exact ⟨by simp [Env.setVar, a], by simp [Env.setVar, b], by simp [Env.setVar, c],
      by simp [Env.setVar, e], by simp [Env.setVar, f]⟩

theorem FC_set {σ : Env} (h : FC d k σ) {y : String} (hy : y ∉ ["w_k", "w_K1", "w_F", "w_nv", "w_d1"])
    (v : ℕ) : FC d k (σ.setVar y v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨a, b, c, e, f⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Env.setVar] <;>
    simp [Ne.symm hy.1, Ne.symm hy.2.1, Ne.symm hy.2.2.1, Ne.symm hy.2.2.2.1, Ne.symm hy.2.2.2.2,
      a, b, c, e, f]

theorem mod_eq_sub' (a n : ℕ) : a - a / n * n = a % n := by rw [Nat.mod_def, Nat.mul_comm]

theorem flatMap_singleton' (l : List ℕ) (f : ℕ → ℕ) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

/-! ### The distinctness conjuncts -/

theorem cOut_spec (hF : FB d k B) (out0 : List ℕ) :
    Spec B (fun σ => FC d k σ ∧ σ.out = out0) cOut
      (fun _ σ' => FC d k σ' ∧ σ'.out = out0 ++ cW k) ((25 + 4) * k + 6) := by
  have h2 := hF.small
  refine Spec.pre (Spec.post (wloop "w_ii" "w_k" k (FC d k) (fun i => [4, 0, 1, 1, i]) out0
    (Kb := 25) (by omega) (fun σ h => h.1) ?_) (fun _ _ _ h => by rw [cW]; exact h))
    (fun σ ⟨h, ho⟩ => ⟨FC_set h (by decide) 0, ho⟩)
  run_vcg [writeLits_spec [4, 0, 1, 1] (B := B) (by simp; omega)]
  all_goals (try simp only [FC] at *)
  all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)

theorem dInner_spec (hF : FB d k B) :
    Spec B (fun σ => FC d k σ ∧ σ.vars "w_ii" < k) dInner
      (fun σ σ' => (FC d k σ' ∧ σ'.vars "w_ii" = σ.vars "w_ii") ∧ σ'.out = σ.out ++
        (List.range (σ.vars "w_ii")).flatMap fun j => [4, 3, 2, σ.vars "w_ii", j])
      ((30 + 4) * k + 6) := by
  have h2 := hF.small
  rintro σ ⟨hC, hi⟩
  set i := σ.vars "w_ii" with hidef
  have h := wloop (B := B) "w_jj" "w_ii" i (fun σ => FC d k σ ∧ σ.vars "w_ii" = i)
    (fun j => [4, 3, 2, i, j]) σ.out (Kb := 30)
    (body := .seq (writeLits [4, 3, 2]) (.seq (.write (V "w_ii"))
      (.seq (.write (V "w_jj")) (bump "w_jj")))) (by omega) (fun σ h => h.2) (by
      run_vcg [writeLits_spec [4, 3, 2] (B := B) (by simp; omega)]
      all_goals (try simp only [FC] at *)
      all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)) σ
    ⟨⟨FC_set hC (by decide) 0, by simp [Env.setVar, hidef]⟩, rfl⟩
  obtain ⟨σ', r, h1, h2⟩ := h
  exact ⟨σ', r.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ hi.le) 6), h1, h2⟩

theorem dOut_spec (hF : FB d k B) (out0 : List ℕ) :
    Spec B (fun σ => FC d k σ ∧ σ.out = out0) dOut
      (fun _ σ' => FC d k σ' ∧ σ'.out = out0 ++ dW k) (((34 * k + 6 + 8) + 4) * k + 6) := by
  have h2 := hF.small
  refine Spec.pre (Spec.post (wloop "w_ii" "w_k" k (FC d k)
    (fun i => (List.range i).flatMap fun j => [4, 3, 2, i, j]) out0
    (Kb := (34 * k + 6) + 8) (by omega) (fun σ h => h.1) ?_) (fun _ _ _ h => by rw [dW]; exact h))
    (fun σ ⟨h, ho⟩ => ⟨FC_set h (by decide) 0, ho⟩)
  refine Spec.pre (P := fun σ => (FC d k σ ∧ σ.vars "w_ii" < k) ∧ σ.vars "w_ii" ≤ k ∧
    σ.out = out0 ++ (List.range (σ.vars "w_ii")).flatMap
      (fun i => (List.range i).flatMap fun j => [4, 3, 2, i, j]) ∧ σ.vars "w_ii" + 1 < B) ?_
    (fun σ h => ⟨⟨h.1.1, h.2⟩, h.1.2.1, h.1.2.2, by omega⟩)
  run_vcg [dInner_spec hF]
  all_goals (try simp only [FC] at *)
  all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)

/-! ### The conjunct of one map `t` -/

/-- The context of the conjunct of the map in `w_t`. -/
def TC (d k : ℕ) (σ : Env) : Prop := FC d k σ ∧ σ.vars "w_t" < FF d k

theorem TC_keep {σ σ' : Env} (h : TC d k σ)
    (hv : ∀ y ∈ ["w_k", "w_K1", "w_F", "w_nv", "w_d1", "w_t"], σ'.vars y = σ.vars y) :
    TC d k σ' := by
  obtain ⟨⟨a, b, c, e, f⟩, g⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> (rw [hv _ (by simp)]; assumption)

def VI (d k t : ℕ) (σ : Env) : Prop :=
  TC d k σ ∧ σ.vars "w_t" = t ∧ σ.vars "w_e" = t / (k + 1) ^ σ.vars "w_p"

theorem vtBody_spec (hF : FB d k B) {t : ℕ} (ht : t < FF d k) (out0 : List ℕ) :
    Spec B (fun σ => (VI d k t σ ∧ σ.vars "w_p" ≤ d + 1 ∧
        σ.out = out0 ++ (List.range (σ.vars "w_p")).flatMap fun p => [t / (k + 1) ^ p % (k + 1)]) ∧
        σ.vars "w_p" < d + 1)
      (.seq (.write (modE (V "w_e") (V "w_K1")))
        (.seq (.assign "w_e" (.div (V "w_e") (V "w_K1"))) (bump "w_p")))
      (fun σ σ' => (VI d k t σ' ∧ σ'.vars "w_p" ≤ d + 1 ∧
        σ'.out = out0 ++ (List.range (σ'.vars "w_p")).flatMap fun p => [t / (k + 1) ^ p % (k + 1)]) ∧
        σ'.vars "w_p" = σ.vars "w_p" + 1) 20 := by
  have h1 := hF.nv
  have h2 := hF.small
  have hFn := FF_le_nv d k
  refine Spec.pre (P := fun σ => ((VI d k t σ ∧ σ.vars "w_p" ≤ d + 1 ∧
      σ.out = out0 ++ (List.range (σ.vars "w_p")).flatMap fun p => [t / (k + 1) ^ p % (k + 1)]) ∧
      σ.vars "w_p" < d + 1) ∧ σ.vars "w_e" < B ∧ σ.vars "w_e" / σ.vars "w_K1" < B ∧
      σ.vars "w_e" / σ.vars "w_K1" * σ.vars "w_K1" < B ∧
      σ.vars "w_e" - σ.vars "w_e" / σ.vars "w_K1" * σ.vars "w_K1" =
        t / (k + 1) ^ σ.vars "w_p" % (k + 1) ∧
      σ.vars "w_e" / σ.vars "w_K1" = t / (k + 1) ^ (σ.vars "w_p" + 1) ∧
      σ.vars "w_K1" < B ∧ σ.vars "w_p" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (try simp only [VI, TC, FC] at *)
    all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)
  · rintro σ ⟨⟨⟨hT, htv, he⟩, hp, ho⟩, hlt⟩
    have hK := hT.1.2.1
    have e1 : t / (k + 1) ^ σ.vars "w_p" ≤ t := Nat.div_le_self _ _
    have e2 : t / (k + 1) ^ σ.vars "w_p" / (k + 1) ≤ t / (k + 1) ^ σ.vars "w_p" :=
      Nat.div_le_self _ _
    have e3 : t / (k + 1) ^ σ.vars "w_p" / (k + 1) * (k + 1) ≤ t / (k + 1) ^ σ.vars "w_p" :=
      Nat.div_mul_le_self _ _
    refine ⟨⟨⟨⟨hT, htv, he⟩, hp, ho⟩, hlt⟩, by rw [he]; omega, by rw [he, hK]; omega,
      by rw [he, hK]; omega,
      by rw [he, hK, mod_eq_sub'],
      by rw [he, hK, Nat.div_div_eq_div_mul, pow_succ], by rw [hK]; omega, by omega⟩

theorem vtOut_spec (hF : FB d k B) :
    Spec B (TC d k) vtOut
      (fun σ σ' => TC d k σ' ∧ σ'.vars "w_t" = σ.vars "w_t" ∧
        σ'.out = σ.out ++ vt d k (σ.vars "w_t")) (2 + ((20 + 4) * (d + 1) + 6)) := by
  have h1 := hF.nv
  have h2 := hF.small
  have hFn := FF_le_nv d k
  intro σ hT
  set t := σ.vars "w_t" with htdef
  have ht : t < FF d k := hT.2
  have r1 : Run B (.assign "w_e" (V "w_t")) σ (σ.setVar "w_e" t) 2 :=
    Run.assign (evalB_var (by omega))
  have hI : VI d k t ((σ.setVar "w_e" t).setVar "w_p" 0) := by
    refine ⟨TC_keep hT (fun y hy => ?_), by simp [Env.setVar, htdef], by simp [Env.setVar]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ', r2, ⟨hT', ht', -⟩, ho⟩ := wloop (B := B) "w_p" "w_d1" (d + 1) (VI d k t)
    (fun p => [t / (k + 1) ^ p % (k + 1)]) σ.out (Kb := 20) (by omega)
    (fun σ h => h.1.1.2.2.2.2) (vtBody_spec hF ht σ.out) (σ.setVar "w_e" t) ⟨hI, by simp [Env.setVar]⟩
  refine ⟨σ', r1.seq r2, hT', by rw [ht'], ?_⟩
  rw [ho, flatMap_singleton']; rfl

theorem yv_B (hF : FB d k B) {t j : ℕ} (ht : t < FF d k) (hj : j < k + 1) :
    t * (k + 1) < B ∧ (k + 1) + t * (k + 1) < B ∧ yv k t j < B := by
  have h1 := hF.nv
  have := yv_lt d k ht hj
  unfold yv at this ⊢; omega

def YI (d k t : ℕ) (σ : Env) : Prop := TC d k σ ∧ σ.vars "w_t" = t

/-- The facts about `y_{w_t, w_jj}` a writer needs. -/
def YF (k B : ℕ) (σ : Env) : Prop :=
  σ.vars "w_t" * σ.vars "w_K1" < B ∧ σ.vars "w_K1" + σ.vars "w_t" * σ.vars "w_K1" < B ∧
    σ.vars "w_K1" + σ.vars "w_t" * σ.vars "w_K1" + σ.vars "w_jj" =
      yv k (σ.vars "w_t") (σ.vars "w_jj") ∧ yv k (σ.vars "w_t") (σ.vars "w_jj") < B ∧
    σ.vars "w_K1" < B ∧ σ.vars "w_t" < B ∧ σ.vars "w_jj" + 1 < B

theorem yF_of (hF : FB d k B) {σ : Env} (hT : TC d k σ) (hj : σ.vars "w_jj" < k + 1) :
    YF k B σ := by
  have h2 := hF.small
  have h1 := hF.nv
  have hFn := FF_le_nv d k
  obtain ⟨b1, b2, b3⟩ := yv_B hF hT.2 hj
  have hK := hT.1.2.1
  have ht := hT.2
  refine ⟨by rw [hK]; exact b1, by rw [hK]; exact b2, by rw [hK]; rfl, b3, by rw [hK]; omega,
    by omega, by omega⟩

theorem ytBody_spec (hF : FB d k B) {t : ℕ} (out0 : List ℕ) :
    Spec B (fun σ => (YI d k t σ ∧ σ.vars "w_jj" ≤ k + 1 ∧
        σ.out = out0 ++ (List.range (σ.vars "w_jj")).flatMap fun j => [yv k t j]) ∧
        σ.vars "w_jj" < k + 1) (.seq (.write yvE) (bump "w_jj"))
      (fun σ σ' => (YI d k t σ' ∧ σ'.vars "w_jj" ≤ k + 1 ∧
        σ'.out = out0 ++ (List.range (σ'.vars "w_jj")).flatMap fun j => [yv k t j]) ∧
        σ'.vars "w_jj" = σ.vars "w_jj" + 1) 20 := by
  refine Spec.pre (P := fun σ => ((YI d k t σ ∧ σ.vars "w_jj" ≤ k + 1 ∧
      σ.out = out0 ++ (List.range (σ.vars "w_jj")).flatMap fun j => [yv k t j]) ∧
      σ.vars "w_jj" < k + 1) ∧ YF k B σ) ?_ (fun σ h => ⟨h, yF_of hF h.1.1.1 h.2⟩)
  run_vcg
  all_goals (try simp only [YI, TC, FC, YF] at *)
  all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)

theorem ytOut_spec (hF : FB d k B) :
    Spec B (TC d k) ytOut
      (fun σ σ' => TC d k σ' ∧ σ'.vars "w_t" = σ.vars "w_t" ∧
        σ'.out = σ.out ++ yt k (σ.vars "w_t")) ((20 + 4) * (k + 1) + 6) := by
  have h2 := hF.small
  intro σ hT
  set t := σ.vars "w_t" with htdef
  have hI : YI d k t (σ.setVar "w_jj" 0) := by
    refine ⟨TC_keep hT (fun y hy => ?_), by simp [Env.setVar, htdef]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ', r, ⟨hT', ht'⟩, ho⟩ := wloop (B := B) "w_jj" "w_K1" (k + 1) (YI d k t)
    (fun j => [yv k t j]) σ.out (Kb := 20) (by omega) (fun σ h => h.1.1.2.1)
    (ytBody_spec hF σ.out) σ ⟨hI, rfl⟩
  exact ⟨σ', r, hT', by rw [ht'], by rw [ho, flatMap_singleton']; rfl⟩

def YJ (d k t j : ℕ) (σ : Env) : Prop := YI d k t σ ∧ σ.vars "w_jj" = j ∧ j < k + 1

theorem yInBody_spec (hF : FB d k B) {t j : ℕ} (out0 : List ℕ) :
    Spec B (fun σ => (YJ d k t j σ ∧ σ.vars "w_ii" ≤ k + 1 ∧
        σ.out = out0 ++ (List.range (σ.vars "w_ii")).flatMap fun i => [5, 2, yv k t j, i]) ∧
        σ.vars "w_ii" < k + 1)
      (.seq (writeLits [5, 2]) (.seq (.write yvE) (.seq (.write (V "w_ii")) (bump "w_ii"))))
      (fun σ σ' => (YJ d k t j σ' ∧ σ'.vars "w_ii" ≤ k + 1 ∧
        σ'.out = out0 ++ (List.range (σ'.vars "w_ii")).flatMap fun i => [5, 2, yv k t j, i]) ∧
        σ'.vars "w_ii" = σ.vars "w_ii" + 1) 30 := by
  have h2 := hF.small
  refine Spec.pre (P := fun σ => ((YJ d k t j σ ∧ σ.vars "w_ii" ≤ k + 1 ∧
      σ.out = out0 ++ (List.range (σ.vars "w_ii")).flatMap fun i => [5, 2, yv k t j, i]) ∧
      σ.vars "w_ii" < k + 1) ∧ YF k B σ ∧ σ.vars "w_ii" + 1 < B)
    ?_ (fun σ h => ⟨h, yF_of hF h.1.1.1.1 (by rw [h.1.1.2.1]; exact h.1.1.2.2), by omega⟩)
  run_vcg [writeLits_spec [5, 2] (B := B) (by simp; omega)]
  all_goals (try simp only [YJ, YI, TC, FC, YF] at *)
  all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)

theorem yInner_spec (hF : FB d k B) :
    Spec B (fun σ => TC d k σ ∧ σ.vars "w_jj" < k + 1) yInner
      (fun σ σ' => (TC d k σ' ∧ σ'.vars "w_t" = σ.vars "w_t" ∧ σ'.vars "w_jj" = σ.vars "w_jj") ∧
        σ'.out = σ.out ++ yInW k (σ.vars "w_t") (σ.vars "w_jj")) ((30 + 4) * (k + 1) + 6) := by
  have h2 := hF.small
  rintro σ ⟨hT, hj⟩
  set t := σ.vars "w_t" with htdef
  set j := σ.vars "w_jj" with hjdef
  have hI : YJ d k t j (σ.setVar "w_ii" 0) := by
    refine ⟨⟨TC_keep hT (fun y hy => ?_), by simp [Env.setVar, htdef]⟩,
      by simp [Env.setVar, hjdef], hj⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ', r, ⟨⟨hT', ht'⟩, hj', -⟩, ho⟩ := wloop (B := B) "w_ii" "w_K1" (k + 1) (YJ d k t j)
    (fun i => [5, 2, yv k t j, i]) σ.out (Kb := 30) (by omega) (fun σ h => h.1.1.1.2.1)
    (yInBody_spec hF σ.out) σ ⟨hI, rfl⟩
  exact ⟨σ', r, ⟨hT', by rw [ht'], by rw [hj']⟩, by rw [ho]; rfl⟩

def Kyin (k : ℕ) : ℕ := (30 + 4) * (k + 1) + 6

theorem yOutBody_spec (hF : FB d k B) {t : ℕ} (out0 : List ℕ) :
    Spec B (fun σ => (YI d k t σ ∧ σ.vars "w_jj" ≤ k + 1 ∧
        σ.out = out0 ++ (List.range (σ.vars "w_jj")).flatMap
          fun j => 4 :: (yInW k t j ++ [3, 2, 0, 0])) ∧ σ.vars "w_jj" < k + 1)
      (.seq (.write (.lit 4)) (.seq yInner (.seq (writeLits [3, 2, 0, 0]) (bump "w_jj"))))
      (fun σ σ' => (YI d k t σ' ∧ σ'.vars "w_jj" ≤ k + 1 ∧
        σ'.out = out0 ++ (List.range (σ'.vars "w_jj")).flatMap
          fun j => 4 :: (yInW k t j ++ [3, 2, 0, 0])) ∧
        σ'.vars "w_jj" = σ.vars "w_jj" + 1) (Kyin k + 30) := by
  have h2 := hF.small
  refine Spec.pre (P := fun σ => ((YI d k t σ ∧ σ.vars "w_jj" ≤ k + 1 ∧
      σ.out = out0 ++ (List.range (σ.vars "w_jj")).flatMap
        fun j => 4 :: (yInW k t j ++ [3, 2, 0, 0])) ∧ σ.vars "w_jj" < k + 1) ∧
      σ.vars "w_jj" + 1 < B ∧ 4 < B) ?_ (fun σ h => ⟨h, by omega, by omega⟩)
  unfold Kyin
  run_vcg [yInner_spec hF, writeLits_spec [3, 2, 0, 0] (B := B) (by simp; omega)]
  all_goals (try simp only [YI, TC, FC] at *)
  all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)

theorem yOut_spec (hF : FB d k B) :
    Spec B (TC d k) yOut
      (fun σ σ' => TC d k σ' ∧ σ'.vars "w_t" = σ.vars "w_t" ∧
        σ'.out = σ.out ++ yW k (σ.vars "w_t")) ((Kyin k + 30 + 4) * (k + 1) + 6 + 10) := by
  have h2 := hF.small
  intro σ hT
  set t := σ.vars "w_t" with htdef
  have hI : YI d k t (σ.setVar "w_jj" 0) := by
    refine ⟨TC_keep hT (fun y hy => ?_), by simp [Env.setVar, htdef]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ1, r1, ⟨hT1, ht1⟩, ho1⟩ := wloop (B := B) "w_jj" "w_K1" (k + 1) (YI d k t)
    (fun j => 4 :: (yInW k t j ++ [3, 2, 0, 0])) σ.out (Kb := Kyin k + 30) (by omega)
    (fun σ h => h.1.1.2.1) (yOutBody_spec hF σ.out) σ ⟨hI, rfl⟩
  obtain ⟨σ2, r2, rfl⟩ := writeLits_spec (B := B) [2, 0, 0] (by simp; omega) σ1 trivial
  refine ⟨_, (r1.seq r2).mono (by simp), hT1, by rw [ht1], ?_⟩
  simp only [ho1, yW, List.append_assoc, htdef]

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm
