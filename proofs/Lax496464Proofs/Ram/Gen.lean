import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.Values
import Lax496464Proofs.Ram.ListUtil

/-!
# Generating the jobs of Section 8 into three arrays

The reduction of Section 8 writes four blocks of `N = R·|memberList| + 2·R·m·n` numbers:
the preprocessing times, the processing times, the due dates and the weights. The first three
are computed here into arrays `PA`, `QA`, `DA`, in job order, so that the writer of the four
blocks is four flat loops over arrays.

A job is reached by counters, never by division: the selection jobs by a segment `r` and a
position `u` of the membership list, a dummy by a segment, a set and an element. All three
passes fill the arrays contiguously, so what a pass has done at any moment is the prefix
`Done t`.
-/

namespace Lax496464Proofs.Ram.Gen

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.Construction Lax496464Proofs.Ram.Values
open Lax496464Proofs.Ram.ListUtil

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-! ## 1. What is fixed, and what has been done -/

variable (P : Lax496464.HittingSet.Instance) (k : ℕ)

/-- The three arrays hold the first `t` jobs. -/
def DoneA (pa qa da : List ℕ) (t : ℕ) : Prop :=
  ∀ s < t, pa.getD s 0 = jp P k s ∧ qa.getD s 0 = jq P k s ∧ da.getD s 0 = jd P k s

/-- The state holds the first `t` jobs. -/
def Done (σ : Env) (t : ℕ) : Prop := DoneA P k (σ.arrs "PA") (σ.arrs "QA") (σ.arrs "DA") t

/-- What no generation pass changes: the constants, the membership arrays and the lengths
of the three output arrays. -/
def Ctx (σ : Env) : Prop :=
  σ.vars "n" = P.n ∧ σ.vars "m" = P.m ∧ σ.vars "Q" = Q P k ∧ σ.vars "R" = R P k ∧
  σ.vars "Lc" = (memberList P).length ∧ σ.vars "sc" = selCount P k ∧
  σ.vars "dc" = dumCount P k ∧
  (memberList P).length ≤ (σ.arrs "MJ").length ∧
  (memberList P).length ≤ (σ.arrs "MI").length ∧
  (∀ u < (memberList P).length, (σ.arrs "MJ").getD u 0 = (ent P u).1) ∧
  (∀ u < (memberList P).length, (σ.arrs "MI").getD u 0 = (ent P u).2) ∧
  (σ.arrs "PA").length = numJobs P k ∧ (σ.arrs "QA").length = numJobs P k ∧
  (σ.arrs "DA").length = numJobs P k

variable {P k}

theorem Ctx.congr {σ σ' : Env} (h : Ctx P k σ)
    (hv : ∀ y ∈ ["n", "m", "Q", "R", "Lc", "sc", "dc"], σ'.vars y = σ.vars y)
    (ha : ∀ a ∈ ["MJ", "MI"], σ'.arrs a = σ.arrs a)
    (hp : (σ'.arrs "PA").length = (σ.arrs "PA").length)
    (hq : (σ'.arrs "QA").length = (σ.arrs "QA").length)
    (hd : (σ'.arrs "DA").length = (σ.arrs "DA").length) : Ctx P k σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have e1 := hv "n" (by simp); have e2 := hv "m" (by simp); have e3 := hv "Q" (by simp)
  have e4 := hv "R" (by simp); have e5 := hv "Lc" (by simp); have e6 := hv "sc" (by simp)
  have e7 := hv "dc" (by simp)
  have f1 := ha "MJ" (by simp); have f2 := ha "MI" (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, h1]
  · rw [e2, h2]
  · rw [e3, h3]
  · rw [e4, h4]
  · rw [e5, h5]
  · rw [e6, h6]
  · rw [e7, h7]
  · rw [f1]; exact h8
  · rw [f2]; exact h9
  · rw [f1]; exact h10
  · rw [f2]; exact h11
  · rw [hp, h12]
  · rw [hq, h13]
  · rw [hd, h14]

theorem Ctx.hn {σ : Env} (h : Ctx P k σ) : σ.vars "n" = P.n := h.1
theorem Ctx.hm {σ : Env} (h : Ctx P k σ) : σ.vars "m" = P.m := h.2.1
theorem Ctx.hQ {σ : Env} (h : Ctx P k σ) : σ.vars "Q" = Q P k := h.2.2.1
theorem Ctx.hR {σ : Env} (h : Ctx P k σ) : σ.vars "R" = R P k := h.2.2.2.1
theorem DoneA.step {pa qa da : List ℕ} {t : ℕ} (hD : DoneA P k pa qa da t)
    (hp : t < pa.length) (hq : t < qa.length) (hd : t < da.length) {a b c : ℕ}
    (ha : a = jp P k t) (hb : b = jq P k t) (hc : c = jd P k t) :
    DoneA P k (pa.set t a) (qa.set t b) (da.set t c) (t + 1) := by
  intro s hs
  rcases Nat.lt_or_ge s t with h | h
  · rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega),
      getD_set_ne _ _ _ _ (by omega)]
    exact hD s h
  · obtain rfl : s = t := by omega
    rw [getD_set_self _ _ _ hp, getD_set_self _ _ _ hq, getD_set_self _ _ _ hd]
    exact ⟨ha, hb, hc⟩

/-! ## 2. The bounds the values must respect -/

/-- Everything a generation pass needs of the bound `B` on the values it may compute: the
constants of the construction and every entry of the three blocks are below it. -/
structure Bnd (P : Lax496464.HittingSet.Instance) (k B : ℕ) : Prop where
  one : 1 < B
  nj : numJobs P k < B
  n_lt : P.n < B
  m_lt : P.m < B
  q_lt : Q P k < B
  r_lt : R P k < B
  lc_lt : (memberList P).length < B
  slack : 8 < B
  k2_lt : 2 * k < B
  tg_lt : target P k < B
  jobs : ∀ s < numJobs P k, jp P k s < B ∧ jq P k s < B ∧ jd P k s < B

theorem Q_pos (hk : 2 ≤ k) : 0 < Q P k := by
  unfold Q
  exact Nat.mul_pos (by omega) (by omega)

theorem n_succ_le_Q (hk : 2 ≤ k) : P.n + 1 ≤ Q P k := by
  unfold Q
  calc P.n + 1 = 1 * (P.n + 1) := (Nat.one_mul _).symm
    _ ≤ (k - 1) * (P.n + 1) := Nat.mul_le_mul_right _ (by omega)

/-- The seven numbers an epoch's constants are built from are below `B`, because some
dummy job of the epoch has an entry that is at least as large. -/
theorem Bnd.epoch {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) {r j : ℕ}
    (hr : r < R P k) (hj : j < P.m) :
    r * P.m + (j + 1) < B ∧ r * P.m < B ∧ (r * P.m + (j + 1)) * Q P k < B ∧
    (r * P.m + (j + 1)) * (r * P.m + (j + 1)) < B ∧
    (r * P.m + (j + 1)) * (r * P.m + (j + 1)) * Q P k < B ∧ P.n + 1 < B ∧
    (r * P.m + (j + 1)) * (P.n + 1) < B ∧
    r < B ∧ j < B ∧ P.m < B ∧ Q P k < B ∧ P.n < B := by
  have hn : 0 < P.n := by omega
  have hdl := dum_lt (P := P) (k := k) hr hj hn
  have ht : selCount P k + 1 * dumCount P k + (0 + P.n * (j + P.m * r)) < numJobs P k := by
    have := hdl; simp only [numJobs]; omega
  have hslot := slot_dum (P := P) (k := k) (a := 1) (r := r) (j := j) (i := 0) (Or.inr rfl) hr hj hn
  obtain ⟨hp, hq, hd⟩ := hb.jobs _ ht
  rw [jp_dum hslot] at hp
  rw [jq_dumB hslot] at hq
  rw [jd_dumB hslot] at hd
  have hQ := Q_pos (P := P) hk
  have hnQ := n_succ_le_Q (P := P) hk
  set X := r * P.m + (j + 1) with hX
  have hX1 : 1 ≤ X := by omega
  have hXQ : X ≤ X * Q P k := Nat.le_mul_of_pos_right _ hQ
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_right _ hX1
  have hXXQ : X * X ≤ X * X * Q P k := Nat.le_mul_of_pos_right _ hQ
  have hQX : Q P k ≤ X * Q P k := Nat.le_mul_of_pos_left _ hX1
  have hrm : 0 < P.m := by omega
  have hrX : r ≤ r * P.m := Nat.le_mul_of_pos_right _ hrm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hp, ?_, ?_, hb.m_lt, hb.q_lt, hb.n_lt⟩ <;> omega

/-! ## 3. Storing one job -/

/-- Store the three numbers of job `t`, held in `a`, `b` and `c`, and move `t` on. -/
def storeTriple : Com :=
  .seq (.store "PA" (V "t") (V "a"))
    (.seq (.store "QA" (V "t") (V "b"))
      (.seq (.store "DA" (V "t") (V "c")) (bump "t")))

theorem storeTriple_spec {B : ℕ} (hb : Bnd P k B) (t : ℕ) (ht : t < numJobs P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ t ∧ σ.vars "t" = t ∧ σ.vars "a" = jp P k t ∧
        σ.vars "b" = jq P k t ∧ σ.vars "c" = jd P k t)
      storeTriple
      (fun σ σ' => Ctx P k σ' ∧ Done P k σ' (t + 1) ∧ σ'.vars "t" = t + 1 ∧
        (∀ y, y ≠ "t" → σ'.vars y = σ.vars y) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        (∀ a, a ≠ "PA" → a ≠ "QA" → a ≠ "DA" → σ'.arrs a = σ.arrs a)) 20 := by
  obtain ⟨hp, hq, hd⟩ := hb.jobs t ht
  refine Spec.pre (P := fun σ => Ctx P k σ ∧ Done P k σ t ∧ σ.vars "t" = t ∧
      σ.vars "a" = jp P k t ∧ σ.vars "b" = jq P k t ∧ σ.vars "c" = jd P k t ∧
      t < (σ.arrs "PA").length ∧ t < (σ.arrs "QA").length ∧ t < (σ.arrs "DA").length ∧
      t + 1 < B ∧ jp P k t < B ∧ jq P k t < B ∧ jd P k t < B ∧ t < B) ?_ ?_
  · run_vcg
    rename_i hC hD ht' ha hb' hc hlp hlq hld hB1 hB2 hB3 hB4 hB5
    subst ht'
    simp only [vars_setArr, arrs_setArr, arrs_setVar, vars_setVar, inp_setArr, inp_setVar,
      out_setArr, out_setVar, if_true]
    refine ⟨?_, ?_, trivial, ?_, trivial, trivial, ?_⟩
    · refine hC.congr (fun y hy => ?_) (fun a ha => ?_) (by simp) (by simp) (by simp)
      · have : y ≠ "t" := by rintro rfl; simp at hy
        simp [this]
      · have h1 : a ≠ "PA" := by rintro rfl; simp at ha
        have h2 : a ≠ "QA" := by rintro rfl; simp at ha
        have h3 : a ≠ "DA" := by rintro rfl; simp at ha
        simp [h1, h2, h3]
    · unfold Done
      simp only [arrs_setVar, arrs_setArr]
      simpa using DoneA.step hD hlp hlq hld ha hb' hc
    · intro y hy; simp [hy]
    · intro a h1 h2 h3; simp [h1, h2, h3]
  · rintro σ ⟨hC, hD, ht', ha, hb', hc⟩
    have hnj := hb.nj
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13, h14⟩ := id hC
    exact ⟨hC, hD, ht', ha, hb', hc, by omega, by omega, by omega, by omega, hp, hq, hd, by omega⟩

/-! ## 4. The constants of an epoch -/

/-- The four numbers that depend on the epoch alone: `g = rm + j + 1`, `gQ`, `g²Q` and
`g(n+1)`. -/
def epoch : Com :=
  .seq (.assign "g" (.bin .add (.bin .mul (V "r") (V "m")) (.bin .add (V "j") (.lit 1))))
  (.seq (.assign "gq" (.bin .mul (V "g") (V "Q")))
  (.seq (.assign "gg" (.bin .mul (V "g") (V "g")))
  (.seq (.assign "GG" (.bin .mul (V "gg") (V "Q")))
   (.assign "gn" (.bin .mul (V "g") (.bin .add (V "n") (.lit 1)))))))

theorem epoch_spec {B : ℕ} (r j m Q n : ℕ)
    (hbd : r * m + (j + 1) < B ∧ r * m < B ∧ (r * m + (j + 1)) * Q < B ∧
      (r * m + (j + 1)) * (r * m + (j + 1)) < B ∧
      (r * m + (j + 1)) * (r * m + (j + 1)) * Q < B ∧ n + 1 < B ∧
      (r * m + (j + 1)) * (n + 1) < B ∧
      r < B ∧ j < B ∧ m < B ∧ Q < B ∧ n < B) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "r" = r ∧ σ.vars "j" = j ∧ σ.vars "m" = m ∧ σ.vars "Q" = Q ∧
      σ.vars "n" = n) epoch
      (fun σ σ' => σ'.vars "g" = r * m + (j + 1) ∧ σ'.vars "gq" = (r * m + (j + 1)) * Q ∧
        σ'.vars "GG" = (r * m + (j + 1)) * (r * m + (j + 1)) * Q ∧
        σ'.vars "gn" = (r * m + (j + 1)) * (n + 1) ∧
        (∀ y, y ≠ "g" → y ≠ "gq" → y ≠ "gg" → y ≠ "GG" → y ≠ "gn" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, v1, v2, v3, v4, v5⟩ := hbd
  run_vcg
  all_goals simp_all

/-! ## 5. The values of a selection job -/

/-- Read the pair at position `u` of the membership list and compute `a`, `b`, `c`, the
three numbers of the selection job of segment `r` at that position. -/
def selVals : Com :=
  .seq (.assign "j" (.get "MJ" (V "u")))
  (.seq (.assign "e" (.get "MI" (V "u")))
  (.seq epoch
  (.seq (.assign "b" (.bin .add (V "gq") (V "gq")))
  (.seq (.assign "b" (.bin .add (V "b") (V "Q")))
  (.seq (.assign "a" (.lit 0))
  (.seq (.assign "c" (.bin .add (V "GG") (V "b")))
  (.seq (.assign "e" (.bin .add (V "e") (.lit 1)))
        (.assign "c" (.bin .add (V "c") (V "e"))))))))))

theorem selVals_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) (r u : ℕ)
    (hr : r < R P k) (hu : u < (memberList P).length) :
    Spec B (fun σ => Ctx P k σ ∧ σ.vars "r" = r ∧ σ.vars "u" = u) selVals
      (fun σ σ' => σ'.vars "a" = jp P k ((memberList P).length * r + u) ∧
        σ'.vars "b" = jq P k ((memberList P).length * r + u) ∧
        σ'.vars "c" = jd P k ((memberList P).length * r + u) ∧
        (∀ y, y ≠ "j" → y ≠ "e" → y ≠ "g" → y ≠ "gq" → y ≠ "gg" → y ≠ "GG" → y ≠ "gn" →
          y ≠ "a" → y ≠ "b" → y ≠ "c" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 300 := by
  obtain ⟨hjm, hen⟩ := ent_lt (P := P) hu
  have hE := hb.epoch hk hkn hr hjm
  have hslot := slot_sel (k := k) hu hr
  have hjp := jp_sel hslot
  have hjq := jq_sel hslot
  have hjd := jd_sel hslot
  have hnj := hb.nj
  have hlcB := hb.lc_lt
  obtain ⟨hpB, hqB, hdB⟩ := hb.jobs ((memberList P).length * r + u) (by
    have := slot_sel_lt (P := P) (k := k) hu hr; omega)
  refine Spec.pre (P := fun σ => Ctx P k σ ∧ σ.vars "r" = r ∧ σ.vars "u" = u ∧
      (∀ h : u < (σ.arrs "MJ").length, (σ.arrs "MJ")[u] = (ent P u).1) ∧
      (∀ h : u < (σ.arrs "MI").length, (σ.arrs "MI")[u] = (ent P u).2)) ?_ ?_
  · run_vcg [epoch_spec (B := B) r (ent P u).1 P.m (Q P k) P.n hE (by omega)]
    all_goals (simp only [Ctx] at *; simp_all)
    all_goals omega
  · rintro σ ⟨hC, hr', hu'⟩
    refine ⟨hC, hr', hu', fun h => ?_, fun h => ?_⟩
    · have := hC.2.2.2.2.2.2.2.2.2.1 u hu
      rw [List.getD_eq_getElem _ _ h] at this; exact this
    · have := hC.2.2.2.2.2.2.2.2.2.2.1 u hu
      rw [List.getD_eq_getElem _ _ h] at this; exact this

/-! ## 6. One selection job, end to end -/

/-- Compute and store the selection job of segment `r` at position `u`, and move `u` on. -/
def selElem : Com := .seq selVals (.seq storeTriple (bump "u"))

theorem selElem_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) (r u : ℕ)
    (hr : r < R P k) (hu : u < (memberList P).length) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ ((memberList P).length * r + u) ∧
        σ.vars "r" = r ∧ σ.vars "u" = u ∧ σ.vars "t" = (memberList P).length * r + u)
      selElem
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' ((memberList P).length * r + u + 1) ∧
        σ'.vars "r" = r ∧ σ'.vars "u" = u + 1 ∧
        σ'.vars "t" = (memberList P).length * r + u + 1) 400 := by
  have hnj := hb.nj
  have hlcB := hb.lc_lt
  have hone := hb.one
  have ht := slot_sel_lt (P := P) (k := k) hu hr
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hC, hD, hr', hu', ht'⟩ := hσ
  obtain ⟨σ1, hr1, ha, hb1, hc, hfr, harr, hinp, hout⟩ :=
    (selVals_spec hb hk hkn r u hr hu).run ⟨hC, hr', hu'⟩
  have hC1 : Ctx P k σ1 := hC.congr (fun y hy => by
      apply hfr <;> (rintro rfl; simp at hy))
    (fun a _ => by rw [harr]) (by rw [harr]) (by rw [harr]) (by rw [harr])
  have hD1 : Done P k σ1 ((memberList P).length * r + u) := by
    unfold Done; rw [harr]; exact hD
  have hfrt := hfr "t" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ2, hr2, hC2, hD2, ht2, hfr2, hinp2, hout2, harr2⟩ :=
    (storeTriple_spec hb ((memberList P).length * r + u) ht).run
      ⟨hC1, hD1, by rw [hfrt, ht'], ha, hb1, hc⟩
  have hu2 : σ2.vars "u" = u := by
    rw [hfr2 "u" (by decide), hfr "u" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu']
  have hr2' : σ2.vars "r" = r := by
    rw [hfr2 "r" (by decide), hfr "r" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr']
  have hlit : (Expr.lit 1).evalB B σ2 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "u").evalB B σ2 = some u :=
    hu2 ▸ evalB_var (by rw [hu2]; omega)
  have hr3 := Run.assign (B := B) (σ := σ2) (x := "u") (e := .bin .add (V "u") (.lit 1))
    (v := u + 1) (evalB_bin hvar hlit (by show u + 1 < B; omega))
  refine ⟨_, _, (hr1.seq (hr2.seq hr3)), ?_, ?_⟩
  · simp only [Expr.size]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine hC2.congr (fun y hy => ?_) (fun a _ => by simp) (by simp) (by simp) (by simp)
      have : y ≠ "u" := by rintro rfl; simp at hy
      simp [this]
    · exact hD2
    · simpa using hr2'
    · simp
    · simpa using ht2

/-! ## 7. The selection pass -/

theorem Ctx.setVar {σ : Env} (h : Ctx P k σ) {x : String} (v : ℕ)
    (hx : x ∉ ["n", "m", "Q", "R", "Lc", "sc", "dc"]) : Ctx P k (σ.setVar x v) :=
  h.congr (fun y hy => by
      have : y ≠ x := by rintro rfl; exact hx hy
      simp [this]) (fun a _ => rfl) rfl rfl rfl

/-- The row of segment `r`: every position of the membership list. -/
def selInner : Com :=
  .seq (.assign "u" (.lit 0)) (.while (.lt (V "u") (V "Lc")) selElem)

theorem selInner_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) (r : ℕ)
    (hr : r < R P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ ((memberList P).length * r) ∧
        σ.vars "r" = r ∧ σ.vars "t" = (memberList P).length * r)
      selInner
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' ((memberList P).length * r + (memberList P).length) ∧
        σ'.vars "r" = r ∧ σ'.vars "t" = (memberList P).length * r + (memberList P).length)
      ((400 + 4) * (memberList P).length + 6) := by
  refine (Spec.forRangeZero (B := B) "u" "Lc"
    (fun σ => Ctx P k σ ∧ Done P k σ ((memberList P).length * r + σ.vars "u") ∧
      σ.vars "r" = r ∧ σ.vars "t" = (memberList P).length * r + σ.vars "u" ∧
      σ.vars "u" ≤ (memberList P).length)
    (memberList P).length 400 hb.lc_lt (fun _ h => h.2.2.2.2)
    (fun _ h => h.1.2.2.2.2.1) ?_).conseq ?_ ?_ le_rfl
  · refine Spec.of_exists fun σ ⟨⟨hC, hD, hr', ht', hle⟩, hlt⟩ => ?_
    obtain ⟨σ', hrun, hC', hD', hr'', hu'', ht''⟩ :=
      (selElem_spec hb hk hkn r (σ.vars "u") hr hlt).run ⟨hC, hD, hr', rfl, ht'⟩
    refine ⟨σ', _, hrun, le_rfl, ⟨hC', ?_, hr'', ?_, by omega⟩, hu''⟩
    · rw [hu'']; exact hD'
    · rw [hu'', ht'']; omega
  · rintro σ ⟨hC, hD, hr', ht'⟩
    refine ⟨hC.setVar 0 (by decide), ?_, by simpa using hr', by simpa using ht', by simp⟩
    · simp only [vars_setVar, if_true, Nat.add_zero]; exact hD
  · rintro σ σ' - ⟨⟨hC, hD, hr', ht', -⟩, hu⟩
    rw [hu] at hD ht'
    exact ⟨hC, hD, hr', ht'⟩

/-- One segment: the row, then the next segment. -/
def selRow : Com := .seq selInner (bump "r")

theorem selRow_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    Spec B (fun σ => (Ctx P k σ ∧ Done P k σ ((memberList P).length * σ.vars "r") ∧
        σ.vars "t" = (memberList P).length * σ.vars "r" ∧ σ.vars "r" ≤ R P k) ∧
        σ.vars "r" < R P k) selRow
      (fun σ σ' => (Ctx P k σ' ∧ Done P k σ' ((memberList P).length * σ'.vars "r") ∧
        σ'.vars "t" = (memberList P).length * σ'.vars "r" ∧ σ'.vars "r" ≤ R P k) ∧
        σ'.vars "r" = σ.vars "r" + 1)
      (((400 + 4) * (memberList P).length + 6) + 4) := by
  have hone := hb.one
  have hR := hb.r_lt
  refine Spec.of_exists fun σ ⟨⟨hC, hD, ht, hle⟩, hlt⟩ => ?_
  obtain ⟨σ1, hr1, hC1, hD1, hr1', ht1⟩ :=
    (selInner_spec hb hk hkn (σ.vars "r") hlt).run ⟨hC, hD, rfl, ht⟩
  have hlit : (Expr.lit 1).evalB B σ1 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "r").evalB B σ1 = some (σ.vars "r") :=
    hr1' ▸ evalB_var (by rw [hr1']; omega)
  have hr2 := Run.assign (B := B) (σ := σ1) (x := "r") (e := .bin .add (V "r") (.lit 1))
    (v := σ.vars "r" + 1) (evalB_bin hvar hlit (by show σ.vars "r" + 1 < B; omega))
  refine ⟨_, _, hr1.seq hr2, ?_, ?_, by simp⟩
  · simp only [Expr.size]; omega
  · refine ⟨hC1.setVar _ (by decide), ?_, ?_, by simp; omega⟩
    · simp only [vars_setVar, if_true]
      have : (memberList P).length * σ.vars "r" + (memberList P).length =
          (memberList P).length * (σ.vars "r" + 1) := by ring
      rw [← this]; exact hD1
    · simp only [vars_setVar, if_true]
      have : σ1.vars "t" = (memberList P).length * (σ.vars "r" + 1) := by rw [ht1]; ring
      simpa using this

/-- The selection pass: segment after segment, position after position. -/
def selPass : Com :=
  .seq (.assign "t" (.lit 0))
    (.seq (.assign "r" (.lit 0)) (.while (.lt (V "r") (V "R")) selRow))

theorem selPass_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ 0) selPass
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (selCount P k) ∧ σ'.vars "t" = selCount P k)
      (2 + (((400 + 4) * (memberList P).length + 6 + 4 + 4) * R P k + 6)) := by
  have hone := hb.one
  have hloop := Spec.forRangeZero (B := B) "r" "R"
    (fun σ => Ctx P k σ ∧ Done P k σ ((memberList P).length * σ.vars "r") ∧
        σ.vars "t" = (memberList P).length * σ.vars "r" ∧ σ.vars "r" ≤ R P k)
    (R P k) (((400 + 4) * (memberList P).length + 6) + 4) hb.r_lt (fun _ h => h.2.2.2)
    (fun _ h => h.1.hR) (selRow_spec hb hk hkn)
  have hassign := Spec.assign (B := B) (P := fun σ => Ctx P k σ ∧ Done P k σ 0) (x := "t")
    (e := .lit 0) (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))
  refine (hassign.seq hloop (fun σ σ' hσ h => ?_)
    (fun σ σ' σ'' _ _ h2 => ?_)).mono ?_
  · obtain ⟨hC, hD⟩ := hσ
    subst h
    refine ⟨hC.setVar _ (by decide), ?_, by simp, by simp⟩
    · simp only [vars_setVar, if_true, Nat.mul_zero]; exact hD
  · obtain ⟨⟨hC, hD, ht, -⟩, hr⟩ := h2
    rw [hr] at hD ht
    have hsc : selCount P k = (memberList P).length * R P k := by
      simp [selCount, Nat.mul_comm]
    rw [hsc]
    exact ⟨hC, hD, ht⟩
  · simp only [Expr.size]; omega

/-! ## 8. The dummy passes

The two dummy families are generated by the same three nested loops, over segments, sets
and elements; they differ in the four commands that compute the three numbers of one job,
and in where in the arrays the family begins. Both are parameters here. -/

/-- The constants of the epoch `(r, j)` are in place. -/
def Ep (r j : ℕ) (σ : Env) : Prop :=
  σ.vars "gq" = (r * P.m + (j + 1)) * Q P k ∧
  σ.vars "GG" = (r * P.m + (j + 1)) * (r * P.m + (j + 1)) * Q P k ∧
  σ.vars "gn" = (r * P.m + (j + 1)) * (P.n + 1)

/-- What a command computing the three numbers of a dummy job of family `base` owes. -/
def ValsSpec (B base : ℕ) (vals : Com) (Kv : ℕ) : Prop :=
  ∀ r j i : ℕ, r < R P k → j < P.m → i < P.n →
    Spec B (fun σ => Ctx P k σ ∧ Ep (P := P) (k := k) r j σ ∧ σ.vars "i" = i) vals
      (fun σ σ' => σ'.vars "a" = jp P k (base + (i + P.n * (j + P.m * r))) ∧
        σ'.vars "b" = jq P k (base + (i + P.n * (j + P.m * r))) ∧
        σ'.vars "c" = jd P k (base + (i + P.n * (j + P.m * r))) ∧
        (∀ y, y ≠ "e" → y ≠ "a" → y ≠ "b" → y ≠ "c" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) Kv

/-- One dummy job: compute its numbers, store them, move the element on. -/
def dumElem (vals : Com) : Com := .seq vals (.seq storeTriple (bump "i"))

theorem dumElem_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B)
    (hv : ValsSpec (P := P) (k := k) B base vals Kv) (r j i : ℕ) (hr : r < R P k)
    (hj : j < P.m) (hi : i < P.n) (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ (base + (i + P.n * (j + P.m * r))) ∧
        Ep (P := P) (k := k) r j σ ∧ σ.vars "i" = i ∧ σ.vars "r" = r ∧ σ.vars "j" = j ∧
        σ.vars "t" = base + (i + P.n * (j + P.m * r)))
      (dumElem vals)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (base + (i + P.n * (j + P.m * r)) + 1) ∧
        Ep (P := P) (k := k) r j σ' ∧ σ'.vars "i" = i + 1 ∧ σ'.vars "r" = r ∧
        σ'.vars "j" = j ∧ σ'.vars "t" = base + (i + P.n * (j + P.m * r)) + 1)
      (Kv + 20 + 4) := by
  have hone := hb.one
  have hnB := hb.n_lt
  have ht : base + (i + P.n * (j + P.m * r)) < numJobs P k := by
    have := dum_lt (P := P) (k := k) hr hj hi
    have h2 : P.n * P.m * R P k = dumCount P k := by simp only [dumCount]; ring
    omega
  refine Spec.of_exists fun σ ⟨hC, hD, hE, hi', hr', hj', ht'⟩ => ?_
  obtain ⟨σ1, hr1, ha, hb1, hc, hfr, harr, hinp, hout⟩ :=
    (hv r j i hr hj hi).run ⟨hC, hE, hi'⟩
  have hC1 : Ctx P k σ1 := hC.congr (fun y hy => by
      apply hfr <;> (rintro rfl; simp at hy))
    (fun a _ => by rw [harr]) (by rw [harr]) (by rw [harr]) (by rw [harr])
  have hD1 : Done P k σ1 (base + (i + P.n * (j + P.m * r))) := by
    unfold Done; rw [harr]; exact hD
  have hfrt := hfr "t" (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ2, hr2, hC2, hD2, ht2, hfr2, hinp2, hout2, harr2⟩ :=
    (storeTriple_spec hb (base + (i + P.n * (j + P.m * r))) ht).run
      ⟨hC1, hD1, by rw [hfrt, ht'], ha, hb1, hc⟩
  have hfi : σ2.vars "i" = i := by
    rw [hfr2 "i" (by decide), hfr "i" (by decide) (by decide) (by decide) (by decide), hi']
  have hfrr : σ2.vars "r" = r := by
    rw [hfr2 "r" (by decide), hfr "r" (by decide) (by decide) (by decide) (by decide), hr']
  have hfj : σ2.vars "j" = j := by
    rw [hfr2 "j" (by decide), hfr "j" (by decide) (by decide) (by decide) (by decide), hj']
  have hlit : (Expr.lit 1).evalB B σ2 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "i").evalB B σ2 = some i :=
    hfi ▸ evalB_var (by rw [hfi]; omega)
  have hr3 := Run.assign (B := B) (σ := σ2) (x := "i") (e := .bin .add (V "i") (.lit 1))
    (v := i + 1) (evalB_bin hvar hlit (by show i + 1 < B; omega))
  refine ⟨_, _, (hr1.seq (hr2.seq hr3)), ?_, ?_⟩
  · simp only [Expr.size]; omega
  · refine ⟨?_, hD2, ?_, by simp, by simpa using hfrr, by simpa using hfj, by simpa using ht2⟩
    · refine hC2.congr (fun y hy => ?_) (fun a _ => by simp) (by simp) (by simp) (by simp)
      have : y ≠ "i" := by rintro rfl; simp at hy
      simp [this]
    · obtain ⟨e1, e2, e3⟩ := hE
      have g1 := hfr "gq" (by decide) (by decide) (by decide) (by decide)
      have g2 := hfr "GG" (by decide) (by decide) (by decide) (by decide)
      have g3 := hfr "gn" (by decide) (by decide) (by decide) (by decide)
      refine ⟨?_, ?_, ?_⟩
      · simp only [vars_setVar]; rw [if_neg (by decide), hfr2 "gq" (by decide), g1, e1]
      · simp only [vars_setVar]; rw [if_neg (by decide), hfr2 "GG" (by decide), g2, e2]
      · simp only [vars_setVar]; rw [if_neg (by decide), hfr2 "gn" (by decide), g3, e3]

/-- The elements of one epoch. -/
def dumI (vals : Com) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) (dumElem vals))

theorem dumI_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B)
    (hv : ValsSpec (P := P) (k := k) B base vals Kv) (r j : ℕ) (hr : r < R P k)
    (hj : j < P.m) (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ (base + P.n * (j + P.m * r)) ∧
        Ep (P := P) (k := k) r j σ ∧ σ.vars "r" = r ∧ σ.vars "j" = j ∧
        σ.vars "t" = base + P.n * (j + P.m * r))
      (dumI vals)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (base + P.n * (j + P.m * r) + P.n) ∧
        Ep (P := P) (k := k) r j σ' ∧ σ'.vars "r" = r ∧ σ'.vars "j" = j ∧
        σ'.vars "t" = base + P.n * (j + P.m * r) + P.n)
      ((Kv + 20 + 4 + 4) * P.n + 6) := by
  refine (Spec.forRangeZero (B := B) "i" "n"
    (fun σ => Ctx P k σ ∧ Done P k σ (base + (σ.vars "i" + P.n * (j + P.m * r))) ∧
      Ep (P := P) (k := k) r j σ ∧ σ.vars "r" = r ∧ σ.vars "j" = j ∧
      σ.vars "t" = base + (σ.vars "i" + P.n * (j + P.m * r)) ∧ σ.vars "i" ≤ P.n)
    P.n (Kv + 20 + 4) hb.n_lt (fun _ h => h.2.2.2.2.2.2) (fun _ h => h.1.hn) ?_).conseq ?_ ?_ le_rfl
  · refine Spec.of_exists fun σ ⟨⟨hC, hD, hE, hr', hj', ht', hle⟩, hlt⟩ => ?_
    obtain ⟨σ', hrun, hC', hD', hE', hi', hr'', hj'', ht''⟩ :=
      (dumElem_spec hb hv r j (σ.vars "i") hr hj hlt hbase).run ⟨hC, hD, hE, rfl, hr', hj', ht'⟩
    refine ⟨σ', _, hrun, le_rfl, ⟨hC', ?_, hE', hr'', hj'', ?_, by omega⟩, hi'⟩
    · rw [hi', show base + (σ.vars "i" + 1 + P.n * (j + P.m * r)) =
        base + (σ.vars "i" + P.n * (j + P.m * r)) + 1 by omega]
      exact hD'
    · rw [hi', ht'']; omega
  · rintro σ ⟨hC, hD, hE, hr', hj', ht'⟩
    refine ⟨hC.setVar 0 (by decide), ?_, ?_, by simpa using hr', by simpa using hj', ?_, by simp⟩
    · simp only [vars_setVar, if_true, Nat.zero_add]; exact hD
    · obtain ⟨e1, e2, e3⟩ := hE
      exact ⟨by simpa using e1, by simpa using e2, by simpa using e3⟩
    · simpa using ht'
  · rintro σ σ' - ⟨⟨hC, hD, hE, hr', hj', ht', -⟩, hi⟩
    rw [hi] at hD ht'
    refine ⟨hC, ?_, hE, hr', hj', ?_⟩
    · rw [show base + (P.n + P.n * (j + P.m * r)) = base + P.n * (j + P.m * r) + P.n by ring] at hD
      exact hD
    · rw [ht']; ring

/-- One epoch: its constants, then its elements, then the next set. -/
def dumJBody (vals : Com) : Com := .seq epoch (.seq (dumI vals) (bump "j"))

theorem dumJBody_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B) (hk : 2 ≤ k)
    (hkn : k ≤ P.n) (hv : ValsSpec (P := P) (k := k) B base vals Kv) (r : ℕ)
    (hr : r < R P k) (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => (Ctx P k σ ∧ Done P k σ (base + P.n * (σ.vars "j" + P.m * r)) ∧
        σ.vars "r" = r ∧ σ.vars "t" = base + P.n * (σ.vars "j" + P.m * r) ∧
        σ.vars "j" ≤ P.m) ∧ σ.vars "j" < P.m) (dumJBody vals)
      (fun σ σ' => (Ctx P k σ' ∧ Done P k σ' (base + P.n * (σ'.vars "j" + P.m * r)) ∧
        σ'.vars "r" = r ∧ σ'.vars "t" = base + P.n * (σ'.vars "j" + P.m * r) ∧
        σ'.vars "j" ≤ P.m) ∧ σ'.vars "j" = σ.vars "j" + 1)
      (60 + ((Kv + 20 + 4 + 4) * P.n + 6) + 4) := by
  have hone := hb.one
  have hmB := hb.m_lt
  refine Spec.of_exists fun σ ⟨⟨hC, hD, hr', ht', hle⟩, hlt⟩ => ?_
  obtain ⟨σ1, hrun1, hg, hgq, hGG, hgn, hfr, harr, hinp, hout⟩ :=
    (epoch_spec (B := B) r (σ.vars "j") P.m (Q P k) P.n (hb.epoch hk hkn hr hlt) hone).run
      ⟨hr', rfl, hC.hm, hC.hQ, hC.hn⟩
  have hC1 : Ctx P k σ1 := hC.congr (fun y hy => by
      apply hfr <;> (rintro rfl; simp at hy))
    (fun a _ => by rw [harr]) (by rw [harr]) (by rw [harr]) (by rw [harr])
  have hD1 : Done P k σ1 (base + P.n * (σ.vars "j" + P.m * r)) := by
    unfold Done; rw [harr]; exact hD
  have hr1 : σ1.vars "r" = r := by
    rw [hfr "r" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr'
  have hj1 : σ1.vars "j" = σ.vars "j" :=
    hfr "j" (by decide) (by decide) (by decide) (by decide) (by decide)
  have ht1 : σ1.vars "t" = base + P.n * (σ.vars "j" + P.m * r) := by
    rw [hfr "t" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht'
  obtain ⟨σ2, hrun2, hC2, hD2, hE2, hr2, hj2, ht2⟩ :=
    (dumI_spec hb hv r (σ.vars "j") hr hlt hbase).run
      ⟨hC1, hD1, ⟨hgq, hGG, hgn⟩, hr1, hj1, ht1⟩
  have hlit : (Expr.lit 1).evalB B σ2 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "j").evalB B σ2 = some (σ.vars "j") :=
    hj2 ▸ evalB_var (by rw [hj2]; omega)
  have hrun3 := Run.assign (B := B) (σ := σ2) (x := "j") (e := .bin .add (V "j") (.lit 1))
    (v := σ.vars "j" + 1) (evalB_bin hvar hlit (by show σ.vars "j" + 1 < B; omega))
  refine ⟨_, _, hrun1.seq (hrun2.seq hrun3), ?_, ?_, by simp⟩
  · simp only [Expr.size]; omega
  · refine ⟨hC2.setVar _ (by decide), ?_, ?_, ?_, ?_⟩
    · simp only [vars_setVar, if_true]
      rw [show base + P.n * (σ.vars "j" + 1 + P.m * r) =
        base + P.n * (σ.vars "j" + P.m * r) + P.n by ring]
      exact hD2
    · simpa using hr2
    · simp only [vars_setVar, if_true]
      rw [show base + P.n * (σ.vars "j" + 1 + P.m * r) =
        base + P.n * (σ.vars "j" + P.m * r) + P.n by ring]
      exact ht2
    · simp only [vars_setVar, if_true]; omega

/-- The epochs of one segment. -/
def dumJ (vals : Com) : Com :=
  .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "m")) (dumJBody vals))

/-- The cost of one epoch, with `Kv` the cost of the command computing one job. -/
def costJBody (Kv n : ℕ) : ℕ := 60 + ((Kv + 20 + 4 + 4) * n + 6) + 4

theorem dumJ_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B) (hk : 2 ≤ k)
    (hkn : k ≤ P.n) (hv : ValsSpec (P := P) (k := k) B base vals Kv) (r : ℕ)
    (hr : r < R P k) (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ (base + P.n * (P.m * r)) ∧
        σ.vars "r" = r ∧ σ.vars "t" = base + P.n * (P.m * r))
      (dumJ vals)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (base + P.n * (P.m * r) + P.n * P.m) ∧
        σ'.vars "r" = r ∧ σ'.vars "t" = base + P.n * (P.m * r) + P.n * P.m)
      ((costJBody Kv P.n + 4) * P.m + 6) := by
  refine (Spec.forRangeZero (B := B) "j" "m"
    (fun σ => Ctx P k σ ∧ Done P k σ (base + P.n * (σ.vars "j" + P.m * r)) ∧
      σ.vars "r" = r ∧ σ.vars "t" = base + P.n * (σ.vars "j" + P.m * r) ∧
      σ.vars "j" ≤ P.m)
    P.m (costJBody Kv P.n) hb.m_lt (fun _ h => h.2.2.2.2) (fun _ h => h.1.hm)
    (dumJBody_spec hb hk hkn hv r hr hbase)).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hC, hD, hr', ht'⟩
    refine ⟨hC.setVar 0 (by decide), ?_, by simpa using hr', ?_, by simp⟩
    · simp only [vars_setVar, if_true, Nat.zero_add]; exact hD
    · simpa using ht'
  · rintro σ σ' - ⟨⟨hC, hD, hr', ht', -⟩, hj⟩
    rw [hj] at hD ht'
    rw [show base + P.n * (P.m + P.m * r) = base + P.n * (P.m * r) + P.n * P.m by ring] at hD ht'
    exact ⟨hC, hD, hr', ht'⟩

/-- One segment, then the next. -/
def dumRBody (vals : Com) : Com := .seq (dumJ vals) (bump "r")

theorem dumRBody_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B) (hk : 2 ≤ k)
    (hkn : k ≤ P.n) (hv : ValsSpec (P := P) (k := k) B base vals Kv)
    (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => (Ctx P k σ ∧ Done P k σ (base + P.n * P.m * σ.vars "r") ∧
        σ.vars "t" = base + P.n * P.m * σ.vars "r" ∧ σ.vars "r" ≤ R P k) ∧
        σ.vars "r" < R P k) (dumRBody vals)
      (fun σ σ' => (Ctx P k σ' ∧ Done P k σ' (base + P.n * P.m * σ'.vars "r") ∧
        σ'.vars "t" = base + P.n * P.m * σ'.vars "r" ∧ σ'.vars "r" ≤ R P k) ∧
        σ'.vars "r" = σ.vars "r" + 1)
      ((costJBody Kv P.n + 4) * P.m + 6 + 4) := by
  have hone := hb.one
  have hR := hb.r_lt
  refine Spec.of_exists fun σ ⟨⟨hC, hD, ht, hle⟩, hlt⟩ => ?_
  have e1 : base + P.n * P.m * σ.vars "r" = base + P.n * (P.m * σ.vars "r") := by ring
  obtain ⟨σ1, hr1, hC1, hD1, hr1', ht1⟩ :=
    (dumJ_spec hb hk hkn hv (σ.vars "r") hlt hbase).run ⟨hC, by rw [← e1]; exact hD, rfl,
      by rw [← e1]; exact ht⟩
  have hlit : (Expr.lit 1).evalB B σ1 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "r").evalB B σ1 = some (σ.vars "r") :=
    hr1' ▸ evalB_var (by rw [hr1']; omega)
  have hr2 := Run.assign (B := B) (σ := σ1) (x := "r") (e := .bin .add (V "r") (.lit 1))
    (v := σ.vars "r" + 1) (evalB_bin hvar hlit (by show σ.vars "r" + 1 < B; omega))
  have e2 : base + P.n * (P.m * σ.vars "r") + P.n * P.m =
      base + P.n * P.m * (σ.vars "r" + 1) := by ring
  refine ⟨_, _, hr1.seq hr2, ?_, ?_, by simp⟩
  · simp only [Expr.size]; omega
  · refine ⟨hC1.setVar _ (by decide), ?_, ?_, by simp; omega⟩
    · simp only [vars_setVar, if_true]; rw [← e2]; exact hD1
    · simp only [vars_setVar, if_true]; rw [← e2]; exact ht1

/-- **A dummy pass**: every segment, set and element, the numbers of each job computed by
`vals` and stored where the job belongs. -/
def dumPass (vals : Com) : Com :=
  .seq (.assign "r" (.lit 0)) (.while (.lt (V "r") (V "R")) (dumRBody vals))

theorem dumPass_spec {B base Kv : ℕ} {vals : Com} (hb : Bnd P k B) (hk : 2 ≤ k)
    (hkn : k ≤ P.n) (hv : ValsSpec (P := P) (k := k) B base vals Kv)
    (hbase : base + P.n * P.m * R P k ≤ numJobs P k) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ base ∧ σ.vars "t" = base)
      (dumPass vals)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (base + P.n * P.m * R P k) ∧
        σ'.vars "t" = base + P.n * P.m * R P k)
      (((costJBody Kv P.n + 4) * P.m + 6 + 4 + 4) * R P k + 6) := by
  refine (Spec.forRangeZero (B := B) "r" "R"
    (fun σ => Ctx P k σ ∧ Done P k σ (base + P.n * P.m * σ.vars "r") ∧
      σ.vars "t" = base + P.n * P.m * σ.vars "r" ∧ σ.vars "r" ≤ R P k)
    (R P k) ((costJBody Kv P.n + 4) * P.m + 6 + 4) hb.r_lt (fun _ h => h.2.2.2)
    (fun _ h => h.1.hR) (dumRBody_spec hb hk hkn hv hbase)).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hC, hD, ht⟩
    refine ⟨hC.setVar 0 (by decide), ?_, ?_, by simp⟩
    · simp only [vars_setVar, if_true, Nat.mul_zero, Nat.add_zero]; exact hD
    · simp only [vars_setVar]; simpa using ht
  · rintro σ σ' - ⟨⟨hC, hD, ht, -⟩, hr⟩
    rw [hr] at hD ht
    exact ⟨hC, hD, ht⟩

/-! ## 9. The two dummy families -/

/-- The numbers of a job of the first dummy family: `g(n+1)`, `gQ`, and `g²Q + gQ + i + 1`. -/
def valsA : Com :=
  .seq (.assign "a" (V "gn"))
  (.seq (.assign "b" (V "gq"))
  (.seq (.assign "e" (.bin .add (V "i") (.lit 1)))
  (.seq (.assign "c" (.bin .add (V "GG") (V "gq")))
        (.assign "c" (.bin .add (V "c") (V "e"))))))

theorem valsA_spec {B : ℕ} (hb : Bnd P k B) :
    ValsSpec (P := P) (k := k) B (selCount P k) valsA 100 := by
  intro r j i hr hj hi
  have hnB := hb.n_lt
  have hone := hb.one
  have hnj : selCount P k + (i + P.n * (j + P.m * r)) < numJobs P k := by
    have := dum_lt (P := P) (k := k) hr hj hi
    simp only [numJobs]; omega
  have hslot := slot_dum (P := P) (k := k) (a := 0) (r := r) (j := j) (i := i) (Or.inl rfl) hr hj hi
  simp only [zero_mul, add_zero, zero_add] at hslot
  have hjp := jp_dum (a := 0) (by simpa using hslot)
  have hjq := jq_dumA hslot
  have hjd := jd_dumA hslot
  obtain ⟨hpB, hqB, hdB⟩ := hb.jobs _ hnj
  refine Spec.pre (P := fun σ => Ctx P k σ ∧ Ep (P := P) (k := k) r j σ ∧ σ.vars "i" = i)
    ?_ (fun _ h => h)
  run_vcg
  all_goals (simp only [Ctx, Ep] at *; simp_all)
  all_goals omega

/-- The numbers of a job of the second dummy family: `g(n+1)`, `gQ + Q`, and
`g²Q + (2gQ + Q) + i + 1`. -/
def valsB : Com :=
  .seq (.assign "a" (V "gn"))
  (.seq (.assign "b" (.bin .add (V "gq") (V "Q")))
  (.seq (.assign "e" (.bin .add (V "gq") (V "gq")))
  (.seq (.assign "e" (.bin .add (V "e") (V "Q")))
  (.seq (.assign "c" (.bin .add (V "GG") (V "e")))
  (.seq (.assign "e" (.bin .add (V "i") (.lit 1)))
        (.assign "c" (.bin .add (V "c") (V "e"))))))))

theorem valsB_spec {B : ℕ} (hb : Bnd P k B) :
    ValsSpec (P := P) (k := k) B (selCount P k + dumCount P k) valsB 100 := by
  intro r j i hr hj hi
  have hnB := hb.n_lt
  have hone := hb.one
  have hnj : selCount P k + dumCount P k + (i + P.n * (j + P.m * r)) < numJobs P k := by
    have := dum_lt (P := P) (k := k) hr hj hi
    simp only [numJobs]; omega
  have hslot := slot_dum (P := P) (k := k) (a := 1) (r := r) (j := j) (i := i) (Or.inr rfl) hr hj hi
  simp only [one_mul] at hslot
  have hjp := jp_dum (a := 1) hslot
  have hjq := jq_dumB hslot
  have hjd := jd_dumB hslot
  obtain ⟨hpB, hqB, hdB⟩ := hb.jobs _ hnj
  refine Spec.pre (P := fun σ => Ctx P k σ ∧ Ep (P := P) (k := k) r j σ ∧ σ.vars "i" = i)
    ?_ (fun _ h => h)
  run_vcg
  all_goals (simp only [Ctx, Ep] at *; simp_all)
  all_goals omega

/-! ## 10. All three passes -/

/-- The three passes, one after the other. -/
def gen : Com := .seq selPass (.seq (dumPass valsA) (dumPass valsB))

/-- The cost of a dummy pass. -/
def costDum (n m R : ℕ) : ℕ := ((costJBody 100 n + 4) * m + 6 + 4 + 4) * R + 6

theorem gen_spec {B : ℕ} (hb : Bnd P k B) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    Spec B (fun σ => Ctx P k σ ∧ Done P k σ 0) gen
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (numJobs P k) ∧ σ'.vars "t" = numJobs P k)
      ((2 + (((400 + 4) * (memberList P).length + 6 + 4 + 4) * R P k + 6)) +
        (costDum P.n P.m (R P k) + costDum P.n P.m (R P k))) := by
  have hdc : dumCount P k = P.n * P.m * R P k := by simp only [dumCount]; ring
  have hnj : numJobs P k = selCount P k + dumCount P k + dumCount P k := by
    simp only [numJobs]; omega
  have hA := dumPass_spec (B := B) (base := selCount P k) hb hk hkn (valsA_spec hb)
    (by omega)
  have hB := dumPass_spec (B := B) (base := selCount P k + dumCount P k) hb hk hkn
    (valsB_spec hb) (by omega)
  have hA' : Spec B (fun σ => Ctx P k σ ∧ Done P k σ (selCount P k) ∧ σ.vars "t" = selCount P k)
      (dumPass valsA)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (selCount P k + dumCount P k) ∧
        σ'.vars "t" = selCount P k + dumCount P k) (costDum P.n P.m (R P k)) := by
    refine hA.post (fun σ σ' _ h => ?_)
    rw [hdc]; exact h
  have hB' : Spec B (fun σ => Ctx P k σ ∧ Done P k σ (selCount P k + dumCount P k) ∧
        σ.vars "t" = selCount P k + dumCount P k)
      (dumPass valsB)
      (fun _ σ' => Ctx P k σ' ∧ Done P k σ' (numJobs P k) ∧ σ'.vars "t" = numJobs P k)
      (costDum P.n P.m (R P k)) := by
    refine hB.post (fun σ σ' _ h => ?_)
    rw [hnj, hdc]; rw [hdc] at h; exact h
  exact (selPass_spec hb hk hkn).seq (hA'.seq hB' (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

end Lax496464Proofs.Ram.Gen
