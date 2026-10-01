import Lax496464Proofs.WHierarchy.HittingSet.EmitNat
import Lax496464Proofs.WHierarchy.HittingSet.SetsMath

/-! # Writing the sets of a Hitting Set word, in IMP+

`setsLoop` writes `SetsMath.setsOut U m (inSetB VAL OFF self)`: for every set `j < m`, it counts the
candidates `a < U` that pass the membership test, writes the count, and then writes the candidates
that pass, in increasing order, each in the self-delimiting code. The test scans the positions
`OFF[j] ≤ q < OFF[j+1]` of the value array for the value `a` (and accepts `a = j` when `self`).

The inputs are the scalars `es_U`, `es_m`, `es_self` and the arrays `es_val` (the values `VAL`)
and `es_off` (the offsets `OFF`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.EmitSets

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitNat (V bump emitNat emitNat_spec)

/-! ## Writing a number, with its frame -/

theorem emitNat_frame {B : ℕ} (S : ℕ) :
    Spec B (fun σ => σ.vars "en_v" + 4 < B ∧ (σ.vars "en_v").size ≤ S) emitNat
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (σ.vars "en_v") ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ ∀ y, y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → σ'.vars y = σ.vars y)
      (48 * S + 40) := by
  refine (emitNat_spec S).frame.post ?_
  rintro σ σ' - ⟨ho, hv, ha, hi, -⟩
  refine ⟨ho, funext fun a => ha a (by simp [emitNat, EmitNat.sizeLoop, EmitNat.sizeBody,
    EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, Com.warrs]),
    hi (by simp [emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody,
      EmitNat.digLoop, EmitNat.digBody, Com.reads]), fun y h1 h2 h3 => hv y ?_⟩
  simp [emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody,
    EmitNat.digLoop, EmitNat.digBody, Com.wvars, h1, h2, h3]

/-! ## The membership test -/

def scanBody : Com :=
  .seq (.ite (.eq (.get "es_val" (V "es_p")) (V "es_a")) (.assign "es_c" (.lit 1)) .skip)
    (bump "es_p")
def scanLoop : Com := .seq (.assign "es_p" (V "es_lo")) (.while (.lt (V "es_p") (V "es_hi")) scanBody)

/-- `es_c := 1` if `es_a` lies in set `es_j`, `0` otherwise. -/
def testCom : Com :=
  .seq (.assign "es_c" (.lit 0))
    (.seq (.ite (.eq (V "es_self") (.lit 1))
        (.ite (.eq (V "es_a") (V "es_j")) (.assign "es_c" (.lit 1)) .skip) .skip) scanLoop)

/-- The context: the inputs are in place. -/
def Ctx (VAL OFF : List ℕ) (self : Bool) (U m : ℕ) (σ : Env) : Prop :=
  σ.arrs "es_val" = VAL ∧ σ.arrs "es_off" = OFF ∧ σ.vars "es_U" = U ∧ σ.vars "es_m" = m ∧
    σ.vars "es_self" = (if self then 1 else 0)

/-- The bounds the programs need: offsets at most `H`, values and `U`, `m`, `H` below `B`. -/
structure Bounds (VAL OFF : List ℕ) (U m H B : ℕ) : Prop where
  off_len : m + 1 ≤ OFF.length
  off_le : ∀ j ≤ m, OFF.getD j 0 ≤ H
  off_mono : ∀ j < m, OFF.getD j 0 ≤ OFF.getD (j + 1) 0
  val_len : H ≤ VAL.length
  val_lt : ∀ v ∈ VAL, v < B
  U_lt : U + H + m + 4 < B

/-- The part of the test decided so far. -/
def Part (VAL OFF : List ℕ) (self : Bool) (j a p : ℕ) : Prop :=
  (self = true ∧ a = j) ∨ ∃ q < p, OFF.getD j 0 ≤ q ∧ VAL.getD q 0 = a

instance (VAL OFF : List ℕ) (self : Bool) (j a p : ℕ) : Decidable (Part VAL OFF self j a p) := by
  unfold Part; infer_instance

def SI (VAL OFF : List ℕ) (self : Bool) (j a : ℕ) (σ : Env) : Prop :=
  σ.arrs "es_val" = VAL ∧ σ.vars "es_a" = a ∧ σ.vars "es_hi" = OFF.getD (j + 1) 0 ∧
    OFF.getD j 0 ≤ σ.vars "es_p" ∧ σ.vars "es_p" ≤ OFF.getD (j + 1) 0 ∧
    σ.vars "es_c" = if Part VAL OFF self j a (σ.vars "es_p") then 1 else 0

theorem part_succ (VAL OFF : List ℕ) (self : Bool) (j a p : ℕ) (hp : OFF.getD j 0 ≤ p) :
    Part VAL OFF self j a (p + 1) ↔ Part VAL OFF self j a p ∨ VAL.getD p 0 = a := by
  unfold Part
  constructor
  · rintro (h | ⟨q, hq, h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_or_ge q p with h | h
      · exact Or.inl (Or.inr ⟨q, h, h1, h2⟩)
      · right; rwa [show q = p by omega] at h2
  · rintro ((h | ⟨q, hq, h1, h2⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, h1, h2⟩
    · exact Or.inr ⟨p, by omega, hp, h⟩

theorem scanBody_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H j a : ℕ)
    (hb : Bounds VAL OFF U m H B) (hj : j < m) :
    Spec B (fun σ => SI VAL OFF self j a σ ∧ σ.vars "es_p" < OFF.getD (j + 1) 0 ∧ a < B) scanBody
      (fun σ σ' => (SI VAL OFF self j a σ' ∧ a < B) ∧ σ'.vars "es_p" = σ.vars "es_p" + 1) 20 := by
  have hH := hb.off_le (j + 1) (by omega)
  have hV := hb.val_len
  have hU := hb.U_lt
  refine Spec.pre (P := fun σ => (SI VAL OFF self j a σ ∧ σ.vars "es_p" < OFF.getD (j + 1) 0 ∧
    a < B) ∧ σ.vars "es_p" + 1 < B ∧ 1 < B ∧ σ.vars "es_a" < B ∧
    σ.vars "es_p" < (σ.arrs "es_val").length ∧ (σ.arrs "es_val").getD (σ.vars "es_p") 0 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ‹SI VAL OFF self j a σ›
      have h8 : a < B := ‹a < B›
    · have hc := ‹(σ.arrs "es_val").getD (σ.vars "es_p") 0 = σ.vars "es_a"›
      rw [h1, h2] at hc
      refine ⟨⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega, by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; omega, ?_⟩, h8⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [if_pos ((part_succ VAL OFF self j a _ h4).mpr (Or.inr hc))]
    · have hc := ‹¬(σ.arrs "es_val").getD (σ.vars "es_p") 0 = σ.vars "es_a"›
      rw [h1, h2] at hc
      refine ⟨⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar, h3],
        by simp only [Env.setVar, ↓reduceIte]; omega, by simp only [Env.setVar, ↓reduceIte]; omega, ?_⟩, h8⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [h6]
      by_cases hp : Part VAL OFF self j a (σ.vars "es_p")
      · rw [if_pos hp, if_pos ((part_succ VAL OFF self j a _ h4).mpr (Or.inl hp))]
      · rw [if_neg hp, if_neg (fun h => ((part_succ VAL OFF self j a _ h4).mp h).elim hp hc)]
  · rintro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
    refine ⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩, by omega, by omega, by rw [h2]; exact h8,
      by rw [h1]; omega, ?_⟩
    rw [h1, List.getD_eq_getElem _ _ (by omega)]
    exact hb.val_lt _ (List.getElem_mem _)

/-- The scan, from wherever it stands to the end of the set. -/
theorem scanWhile_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j a : ℕ} (hj : j < m) :
    Spec B (fun σ => SI VAL OFF self j a σ ∧ a < B)
      (.while (.lt (.var "es_p") (.var "es_hi")) scanBody)
      (fun σ σ' => (SI VAL OFF self j a σ' ∧ a < B) ∧ σ'.vars "es_p" = OFF.getD (j + 1) 0 ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "es_c" → y ≠ "es_p" → σ'.vars y = σ.vars y) (24 * H + 30) := by
  have hU' := hb.U_lt
  have hH := hb.off_le (j + 1) (by omega)
  refine (Spec.forRange (B := B) (c := scanBody) (P := fun σ => (SI VAL OFF self j a σ ∧ a < B))
      "es_p" "es_hi" (fun σ => SI VAL OFF self j a σ ∧ a < B) (OFF.getD (j + 1) 0) 20
      (24 * H + 30)
      (fun _ h => by have := h.1.2.2.2.2.1; omega)
      (fun _ h => by rw [h.1.2.2.1]; omega) (fun _ h => h.1.2.2.1) (fun _ h => h.1.2.2.2.2.1)
      (by
        refine (scanBody_spec VAL OFF self U m H j a hb hj).pre ?_
        rintro σ ⟨⟨hI, ha'⟩, hlt⟩
        exact ⟨hI, hlt, ha'⟩)
      (fun _ h => h)
      (fun σ' h => by
        have h1 := h.1.2.2.2.1
        have : (20 + 4) * (OFF.getD (j + 1) 0 - σ'.vars "es_p") ≤ 24 * H :=
          Nat.mul_le_mul_left _ (by omega)
        omega)).frame.post ?_
  rintro σ σ' - ⟨⟨hI, hp⟩, hv, ha, hi, ho⟩
  refine ⟨hI, hp, funext fun a => ha a (by simp [scanBody, Com.warrs]),
    hi (by simp [scanBody, Com.reads]), ho (by simp [scanBody, Com.NoWrite]),
    fun y h1 h2 => hv y (by simp [scanBody, Com.wvars, h1, h2])⟩

/-- The test, for set `j` and candidate `a`. -/
theorem testCom_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j a : ℕ} (hj : j < m) (ha : a < U) :
    Spec B (fun σ => Ctx VAL OFF self U m σ ∧ σ.vars "es_j" = j ∧ σ.vars "es_a" = a ∧
        σ.vars "es_lo" = OFF.getD j 0 ∧ σ.vars "es_hi" = OFF.getD (j + 1) 0) testCom
      (fun σ σ' => (σ'.vars "es_c" = if inSetB VAL OFF self j a then 1 else 0) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "es_c" → y ≠ "es_p" → σ'.vars y = σ.vars y) (24 * H + 50) := by
  intro σ ⟨⟨hv, ho, hU, hm, hs⟩, hjj, haa, hlo, hhi⟩
  have hU' := hb.U_lt
  have hH := hb.off_le (j + 1) (by omega)
  have hH0 := hb.off_le j (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "es_c") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  set σ1 := σ.setVar "es_c" 0 with hσ1
  have h1s : σ1.vars "es_self" = if self then 1 else 0 := by simp [hσ1, Env.setVar, hs]
  have h1a : σ1.vars "es_a" = a := by simp [hσ1, Env.setVar, haa]
  have h1j : σ1.vars "es_j" = j := by simp [hσ1, Env.setVar, hjj]
  -- the self test
  obtain ⟨σ2, r2, h2c, h2v1, h2a1, h2o1, h2i1⟩ : ∃ σ2, Run B (.ite (.eq (V "es_self") (.lit 1))
      (.ite (.eq (V "es_a") (V "es_j")) (.assign "es_c" (.lit 1)) .skip) .skip) σ1 σ2 12 ∧
      (σ2.vars "es_c" = if self = true ∧ a = j then 1 else 0) ∧
      (∀ y, y ≠ "es_c" → σ2.vars y = σ1.vars y) ∧ σ2.arrs = σ1.arrs ∧ σ2.out = σ1.out ∧
      σ2.inp = σ1.inp := by
    have es : (Cond.eq (V "es_self") (.lit 1)).evalB B σ1 = some (decide (self = true)) := by
      rw [evalB_condEq (evalB_var (by rw [h1s]; split_ifs <;> omega)) (evalB_lit (by omega)), h1s]
      cases self <;> simp
    have ea : (Cond.eq (V "es_a") (V "es_j")).evalB B σ1 = some (decide (a = j)) := by
      rw [evalB_condEq (evalB_var (by rw [h1a]; omega)) (evalB_var (by rw [h1j]; omega)), h1a, h1j]
      by_cases h : a = j <;> simp [h]
    have hc1 : σ1.vars "es_c" = 0 := by simp [hσ1, Env.setVar]
    by_cases hself : self = true
    · have es' : (Cond.eq (V "es_self") (.lit 1)).evalB B σ1 = some true := by
        rw [es, decide_eq_true hself]
      by_cases haj : a = j
      · have ea' : (Cond.eq (V "es_a") (V "es_j")).evalB B σ1 = some true := by
          rw [ea, decide_eq_true haj]
        refine ⟨_, (Run.ite_true es' (Run.ite_true ea' (Run.assign (v := 1)
          (evalB_lit (by omega))))).mono (by simp), by simp [Env.setVar, hself, haj],
          fun y hy => by simp [Env.setVar, hy], rfl, rfl, rfl⟩
      · have ea' : (Cond.eq (V "es_a") (V "es_j")).evalB B σ1 = some false := by
          rw [ea, decide_eq_false haj]
        exact ⟨_, (Run.ite_true es' (Run.ite_false ea' Run.skip)).mono (by simp),
          by rw [hc1]; simp [haj], fun _ _ => rfl, rfl, rfl, rfl⟩
    · have es' : (Cond.eq (V "es_self") (.lit 1)).evalB B σ1 = some false := by
        rw [es, decide_eq_false hself]
      exact ⟨_, (Run.ite_false es' Run.skip).mono (by simp), by rw [hc1]; simp [hself],
        fun _ _ => rfl, rfl, rfl, rfl⟩
  have h2v : ∀ y, y ≠ "es_c" → σ2.vars y = σ.vars y := by
    intro y hy; rw [h2v1 y hy]; simp [hσ1, Env.setVar, hy]
  have h2a : σ2.arrs = σ.arrs := by rw [h2a1]; rfl
  have h2o : σ2.out = σ.out := by rw [h2o1]; rfl
  have h2i : σ2.inp = σ.inp := by rw [h2i1]; rfl
  -- the scan
  have hlo2 : σ2.vars "es_lo" = OFF.getD j 0 := by rw [h2v _ (by decide), hlo]
  have r3 := Run.assign (B := B) (σ := σ2) (x := "es_p") (e := V "es_lo") (v := OFF.getD j 0)
    (by rw [← hlo2]; exact evalB_var (by rw [hlo2]; omega))
  set σ3 := σ2.setVar "es_p" (OFF.getD j 0) with hσ3
  have e3v : ∀ y, y ≠ "es_p" → σ3.vars y = σ2.vars y := by
    intro y hy; simp only [hσ3, Env.setVar, if_neg hy]
  have e3p : σ3.vars "es_p" = OFF.getD j 0 := by simp only [hσ3, Env.setVar, if_true]
  have e3a : σ3.arrs = σ2.arrs := rfl
  have e3o : σ3.out = σ2.out := rfl
  have e3i : σ3.inp = σ2.inp := rfl
  clear_value σ3
  have hstart : (if self = true ∧ a = j then 1 else 0) =
      if Part VAL OFF self j a (OFF.getD j 0) then 1 else 0 := by
    congr 1
    apply propext
    unfold Part
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨q, hq, h1, -⟩)
      · exact h
      · omega
  obtain ⟨σ4, r4, ⟨⟨⟨-, -, -, -, -, hc4⟩, -⟩, hp4, ha4, hi4, ho4, hv4⟩⟩ :=
    (scanWhile_spec (B := B) VAL OFF self U m H hb (a := a) hj).run (σ := σ3)
      ⟨⟨by rw [e3a, h2a, hv], by rw [e3v _ (by decide), h2v _ (by decide), haa],
        by rw [e3v _ (by decide), h2v _ (by decide), hhi], by rw [e3p],
        by rw [e3p]; exact hb.off_mono j hj, by
          rw [e3v _ (by decide), e3p, h2c, hstart]⟩, by omega⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by simp; omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc4, hp4]
    congr 1
    apply propext
    rw [inSetB_iff]
    rfl
  · rw [ha4, e3a, h2a]
  · rw [hi4, e3i, h2i]
  · rw [ho4, e3o, h2o]
  · intro y h1 h2
    rw [hv4 y h1 h2, e3v y h2]; exact h2v y h1

/-! ## Counting and writing the members of one set -/

def countBody : Com :=
  .seq testCom (.seq (.assign "es_cnt" (.add (V "es_cnt") (V "es_c"))) (bump "es_a"))
def countLoop : Com := .seq (.assign "es_a" (.lit 0)) (.while (.lt (V "es_a") (V "es_U")) countBody)

def emitIf : Com := .ite (.eq (V "es_c") (.lit 1)) (.seq (.assign "en_v" (V "es_a")) emitNat) .skip
def writeBody : Com := .seq testCom (.seq emitIf (bump "es_a"))
def writeLoop : Com := .seq (.assign "es_a" (.lit 0)) (.while (.lt (V "es_a") (V "es_U")) writeBody)

/-- The members of set `j`. -/
def memsJ (VAL OFF : List ℕ) (self : Bool) (U j : ℕ) : List ℕ :=
  (List.range U).filter (inSetB VAL OFF self j)

theorem filter_succ (f : ℕ → Bool) (a : ℕ) :
    (List.range (a + 1)).filter f = (List.range a).filter f ++ (if f a then [a] else []) := by
  rw [List.range_succ, List.filter_append]
  cases h : f a <;> simp [h]

/-- The state inside set `j`: its bounds are in `es_lo`, `es_hi`. -/
def JCtx (VAL OFF : List ℕ) (self : Bool) (U m j : ℕ) (σ : Env) : Prop :=
  Ctx VAL OFF self U m σ ∧ σ.vars "es_j" = j ∧ σ.vars "es_lo" = OFF.getD j 0 ∧
    σ.vars "es_hi" = OFF.getD (j + 1) 0

theorem jctx_keep {VAL OFF : List ℕ} {self : Bool} {U m j : ℕ} {σ σ' : Env}
    (h : JCtx VAL OFF self U m j σ) (ha : σ'.arrs = σ.arrs)
    (hv : ∀ y, y ≠ "es_c" → y ≠ "es_p" → y ≠ "es_a" → y ≠ "es_cnt" → y ≠ "en_v" → y ≠ "en_u" →
      y ≠ "en_s" → y ≠ "en_i" → σ'.vars y = σ.vars y) : JCtx VAL OFF self U m j σ' := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8⟩ := h
  refine ⟨⟨by rw [ha, h1], by rw [ha, h2], ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals
    first
      | (rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; assumption)

def CI (VAL OFF : List ℕ) (self : Bool) (U m j : ℕ) (σ : Env) : Prop :=
  JCtx VAL OFF self U m j σ ∧ σ.vars "es_a" ≤ U ∧
    σ.vars "es_cnt" = ((List.range (σ.vars "es_a")).filter (inSetB VAL OFF self j)).length

theorem countBody_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j : ℕ} (hj : j < m) :
    Spec B (fun σ => CI VAL OFF self U m j σ ∧ σ.vars "es_a" < U) countBody
      (fun σ σ' => CI VAL OFF self U m j σ' ∧ σ'.vars "es_a" = σ.vars "es_a" + 1)
      (24 * H + 60) := by
  intro σ ⟨⟨hJ, hle, hcnt⟩, hlt⟩
  have hU := hb.U_lt
  set a := σ.vars "es_a" with ha_def
  obtain ⟨σ1, r1, hc1, ha1, -, -, hv1⟩ :=
    (testCom_spec (B := B) VAL OFF self U m H hb hj hlt).run (σ := σ)
      ⟨hJ.1, hJ.2.1, rfl, hJ.2.2.1, hJ.2.2.2⟩
  have hcl := List.length_filter_le (inSetB VAL OFF self j) (List.range a)
  simp only [List.length_range] at hcl
  have hcnt1 : σ1.vars "es_cnt" = σ.vars "es_cnt" := hv1 _ (by decide) (by decide)
  have hc1le : σ1.vars "es_c" ≤ 1 := by rw [hc1]; split_ifs <;> omega
  have r2 := Run.assign (B := B) (σ := σ1) (x := "es_cnt") (e := .add (V "es_cnt") (V "es_c"))
    (v := σ1.vars "es_cnt" + σ1.vars "es_c")
    (evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by simp; omega))
  set σ2 := σ1.setVar "es_cnt" (σ1.vars "es_cnt" + σ1.vars "es_c") with hσ2
  have h2a : σ2.vars "es_a" = a := by simp only [hσ2, Env.setVar]; simp; exact hv1 _ (by decide) (by decide)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "es_a") (e := .add (V "es_a") (.lit 1))
    (v := a + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "es_a") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h2a]; simp; omega)
      rw [h2a] at this; simpa using this)
  have e3a : (σ2.setVar "es_a" (a + 1)).vars "es_a" = a + 1 := by simp [Env.setVar]
  have e3c : (σ2.setVar "es_a" (a + 1)).vars "es_cnt" = σ1.vars "es_cnt" + σ1.vars "es_c" := by
    simp [hσ2, Env.setVar]
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ⟨?_, ?_, ?_⟩, by rw [e3a]⟩
  · refine jctx_keep hJ (by simp [hσ2, Env.setVar, ha1]) fun y h1 h2 h3 h4 _ _ _ _ => ?_
    simp only [Env.setVar, if_neg h3, hσ2, if_neg h4]
    exact hv1 y h1 h2
  · rw [e3a]; omega
  · rw [e3a, e3c, filter_succ, List.length_append, hcnt1, hcnt, hc1]
    split_ifs <;> simp

theorem countLoop_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j : ℕ} (hj : j < m) :
    Spec B (fun σ => JCtx VAL OFF self U m j σ ∧ σ.vars "es_cnt" = 0) countLoop
      (fun σ σ' => σ'.vars "es_cnt" = (memsJ VAL OFF self U j).length ∧
        JCtx VAL OFF self U m j σ' ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "es_c" → y ≠ "es_p" → y ≠ "es_a" → y ≠ "es_cnt" → σ'.vars y = σ.vars y)
      ((24 * H + 64) * U + 6) := by
  intro σ ⟨hJ, h0⟩
  have hU := hb.U_lt
  obtain ⟨σ', r, ⟨⟨hJ', -, hc⟩, ha⟩, hv, harr, hi, ho⟩ :=
    (Spec.forRangeZero (B := B) "es_a" "es_U" (CI VAL OFF self U m j) U (24 * H + 60) (by omega)
      (fun _ h => h.2.1) (fun _ h => h.1.1.2.2.1)
      (countBody_spec VAL OFF self U m H hb hj)).frame.run (σ := σ)
      ⟨jctx_keep hJ rfl fun y _ _ h3 _ _ _ _ _ => by simp [Env.setVar, h3],
        by simp [Env.setVar], by simp [Env.setVar, h0]⟩
  refine ⟨σ', r, by rw [hc, ha]; rfl, hJ', funext fun a => harr a (by simp [countBody, testCom,
      scanLoop, scanBody, Com.warrs]), hi (by simp [countBody, testCom, scanLoop, scanBody,
      Com.reads]), ho (by simp [countBody, testCom, scanLoop, scanBody, Com.NoWrite]), ?_⟩
  intro y h1 h2 h3 h4
  exact hv y (by simp [countBody, testCom, scanLoop, scanBody, Com.wvars, h1, h2, h3, h4])

def WI (VAL OFF : List ℕ) (self : Bool) (U m j : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  JCtx VAL OFF self U m j σ ∧ σ.vars "es_a" ≤ U ∧
    σ.out = out0 ++ ((List.range (σ.vars "es_a")).filter (inSetB VAL OFF self j)).flatMap bitsNat

theorem writeBody_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j : ℕ} (hj : j < m) (out0 : List ℕ) :
    Spec B (fun σ => WI VAL OFF self U m j out0 σ ∧ σ.vars "es_a" < U) writeBody
      (fun σ σ' => WI VAL OFF self U m j out0 σ' ∧ σ'.vars "es_a" = σ.vars "es_a" + 1)
      (24 * H + 48 * U + 110) := by
  intro σ ⟨⟨hJ, hle, hout⟩, hlt⟩
  have hU := hb.U_lt
  set a := σ.vars "es_a" with ha_def
  obtain ⟨σ1, r1, hc1, ha1, -, ho1, hv1⟩ :=
    (testCom_spec (B := B) VAL OFF self U m H hb hj hlt).run (σ := σ)
      ⟨hJ.1, hJ.2.1, rfl, hJ.2.2.1, hJ.2.2.2⟩
  have hJ1 : JCtx VAL OFF self U m j σ1 :=
    jctx_keep hJ ha1 fun y h1 h2 _ _ _ _ _ _ => hv1 y h1 h2
  have ha1' : σ1.vars "es_a" = a := hv1 _ (by decide) (by decide)
  -- the conditional write
  obtain ⟨σ2, r2, ho2, ha2, hv2⟩ : ∃ σ2, Run B emitIf σ1 σ2 (48 * U + 50) ∧
      σ2.out = σ1.out ++ (if inSetB VAL OFF self j a then bitsNat a else []) ∧
      σ2.arrs = σ1.arrs ∧
      ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → σ2.vars y = σ1.vars y := by
    by_cases hin : inSetB VAL OFF self j a = true
    · have hc : (Cond.eq (V "es_c") (.lit 1)).evalB B σ1 = some true := by
        rw [evalB_condEq (evalB_var (by rw [hc1, if_pos hin]; omega)) (evalB_lit (by omega)),
          hc1, if_pos hin]; simp
      have ra := Run.assign (B := B) (σ := σ1) (x := "en_v") (e := V "es_a") (v := a)
        (by rw [← ha1']; exact evalB_var (by rw [ha1']; omega))
      have hsz : a.size ≤ U := (Words.size_le_self a).trans hlt.le
      obtain ⟨σ2, re, hoe, hae, -, hve⟩ := (emitNat_frame (B := B) U).run
        (σ := σ1.setVar "en_v" a) ⟨by simp [Env.setVar]; omega, by simp [Env.setVar]; exact hsz⟩
      refine ⟨σ2, (Run.ite_true hc (ra.seq re)).mono (by simp; omega), ?_, by rw [hae]; rfl, ?_⟩
      · rw [hoe, if_pos hin]; simp [Env.setVar]
      · intro y h1 h2 h3 h4
        rw [hve y h2 h3 h4]; simp [Env.setVar, h1]
    · have hc : (Cond.eq (V "es_c") (.lit 1)).evalB B σ1 = some false := by
        rw [evalB_condEq (evalB_var (by rw [hc1, if_neg hin]; omega)) (evalB_lit (by omega)),
          hc1, if_neg hin]; simp
      refine ⟨σ1, (Run.ite_false hc Run.skip).mono (by simp), by rw [if_neg hin]; simp, rfl,
        fun _ _ _ _ _ => rfl⟩
  have ha2' : σ2.vars "es_a" = a := by
    rw [hv2 _ (by decide) (by decide) (by decide) (by decide), ha1']
  have r3 := Run.assign (B := B) (σ := σ2) (x := "es_a") (e := .add (V "es_a") (.lit 1))
    (v := a + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "es_a") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [ha2']; simp; omega)
      rw [ha2'] at this; simpa using this)
  have e3a : (σ2.setVar "es_a" (a + 1)).vars "es_a" = a + 1 := by simp [Env.setVar]
  have e3o : (σ2.setVar "es_a" (a + 1)).out = σ2.out := rfl
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp; omega), ⟨?_, ?_, ?_⟩, by rw [e3a]⟩
  · refine jctx_keep hJ1 (by simp [Env.setVar, ha2]) fun y _ _ h3 _ h5 h6 h7 h8 => ?_
    simp only [Env.setVar, if_neg h3]
    exact hv2 y h5 h6 h7 h8
  · rw [e3a]; omega
  · rw [e3a, e3o, ho2, ho1, hout, filter_succ, List.flatMap_append]
    by_cases hin : inSetB VAL OFF self j a = true
    · simp [hin]
    · simp [hin]

theorem writeLoop_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) {j : ℕ} (hj : j < m) :
    Spec B (fun σ => JCtx VAL OFF self U m j σ) writeLoop
      (fun σ σ' => σ'.out = σ.out ++ (memsJ VAL OFF self U j).flatMap bitsNat ∧
        JCtx VAL OFF self U m j σ' ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "es_c" → y ≠ "es_p" → y ≠ "es_a" → y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" →
          y ≠ "en_i" → σ'.vars y = σ.vars y)
      ((24 * H + 48 * U + 114) * U + 6) := by
  intro σ hJ
  have hU := hb.U_lt
  obtain ⟨σ', r, ⟨⟨hJ', -, ho⟩, ha⟩, hv, harr, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "es_a" "es_U" (WI VAL OFF self U m j σ.out) U
      (24 * H + 48 * U + 110) (by omega)
      (fun _ h => h.2.1) (fun _ h => h.1.1.2.2.1)
      (writeBody_spec VAL OFF self U m H hb hj σ.out)).frame.run (σ := σ)
      ⟨jctx_keep hJ rfl fun y _ _ h3 _ _ _ _ _ => by simp [Env.setVar, h3],
        by simp [Env.setVar], by simp [Env.setVar]⟩
  have hw : writeBody = .seq testCom (.seq emitIf (bump "es_a")) := rfl
  refine ⟨σ', r, by rw [ho, ha]; rfl, hJ', funext fun a => harr a (by simp [writeBody, emitIf, emitNat,
      EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
      EmitNat.digBody, testCom, scanLoop, scanBody, Com.warrs]),
    hi (by simp [writeBody, emitIf, emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
      EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, testCom, scanLoop, scanBody,
      Com.reads]), ?_⟩
  intro y h1 h2 h3 h4 h5 h6 h7
  exact hv y (by simp [writeBody, emitIf, emitNat, EmitNat.sizeLoop, EmitNat.sizeBody,
    EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, testCom, scanLoop,
    scanBody, Com.wvars, h1, h2, h3, h4, h5, h6, h7])

/-! ## All the sets -/

def setBody : Com :=
  .seq (.assign "es_lo" (.get "es_off" (V "es_j")))
  (.seq (.assign "es_hi" (.get "es_off" (.add (V "es_j") (.lit 1))))
  (.seq (.assign "es_cnt" (.lit 0))
  (.seq countLoop
  (.seq (.assign "en_v" (V "es_cnt"))
  (.seq emitNat
  (.seq writeLoop (bump "es_j")))))))

/-- **Write the sets.** -/
def setsLoop : Com := .seq (.assign "es_j" (.lit 0)) (.while (.lt (V "es_j") (V "es_m")) setBody)

def SSI (VAL OFF : List ℕ) (self : Bool) (U m : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx VAL OFF self U m σ ∧ σ.vars "es_j" ≤ m ∧
    σ.out = out0 ++ (List.range (σ.vars "es_j")).flatMap
      fun j => setBits ((List.range U).filter (inSetB VAL OFF self j))

/-- The cost of one set. -/
def Kset (U H : ℕ) : ℕ := (48 * H + 48 * U + 178) * U + 48 * U + 68

/-- The scalars of the emission. -/
def emitVars : List String :=
  ["es_j", "es_lo", "es_hi", "es_cnt", "es_a", "es_c", "es_p", "en_v", "en_u", "en_s", "en_i"]

theorem ctx_keep {VAL OFF : List ℕ} {self : Bool} {U m : ℕ} {σ σ' : Env}
    (h : Ctx VAL OFF self U m σ) (ha : σ'.arrs = σ.arrs)
    (hv : ∀ y, y ∉ emitVars → σ'.vars y = σ.vars y) : Ctx VAL OFF self U m σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [ha, h1], by rw [ha, h2], by rw [hv _ (by decide), h3], by rw [hv _ (by decide), h4],
    by rw [hv _ (by decide), h5]⟩

theorem setBody_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) (out0 : List ℕ) :
    Spec B (fun σ => SSI VAL OFF self U m out0 σ ∧ σ.vars "es_j" < m) setBody
      (fun σ σ' => SSI VAL OFF self U m out0 σ' ∧ σ'.vars "es_j" = σ.vars "es_j" + 1)
      (Kset U H) := by
  intro σ ⟨⟨hC, hjm, hout⟩, hlt⟩
  have hU := hb.U_lt
  set j := σ.vars "es_j" with hj_def
  have hoffl := hb.off_len
  have hH0 := hb.off_le j (by omega)
  have hH1 := hb.off_le (j + 1) (by omega)
  have hC' := hC
  obtain ⟨hv, ho, hUU, hm, hs⟩ := hC'
  -- the bounds of the set
  have g0 : (Expr.get "es_off" (V "es_j")).evalB B σ = some (OFF.getD j 0) := by
    have := RunStep.eval_get B σ "es_off" (V "es_j") j (evalB_var (by omega))
      (by rw [ho]; omega) (by rw [ho]; omega)
    rwa [ho] at this
  have r1 := Run.assign (B := B) (σ := σ) (x := "es_lo") g0
  set σ1 := σ.setVar "es_lo" (OFF.getD j 0) with hσ1
  have h1j : σ1.vars "es_j" = j := by simp [hσ1, Env.setVar, hj_def]
  have h1o : σ1.arrs "es_off" = OFF := by simp [hσ1, Env.setVar, ho]
  have g1 : (Expr.get "es_off" (.add (V "es_j") (.lit 1))).evalB B σ1 = some (OFF.getD (j + 1) 0) := by
    have := RunStep.eval_get B σ1 "es_off" (.add (V "es_j") (.lit 1)) (j + 1)
      (by
        have := evalB_bin (B := B) (op := .add) (σ := σ1) (evalB_var (x := "es_j") (by omega))
          (evalB_lit (n := 1) (by omega)) (by rw [h1j]; simp; omega)
        rw [h1j] at this; simpa using this)
      (by rw [h1o]; omega) (by rw [h1o]; omega)
    rwa [h1o] at this
  have r2 := Run.assign (B := B) (σ := σ1) (x := "es_hi") g1
  set σ2 := (σ1.setVar "es_hi" (OFF.getD (j + 1) 0)).setVar "es_cnt" 0 with hσ2
  have r3 := Run.assign (B := B) (σ := σ1.setVar "es_hi" (OFF.getD (j + 1) 0)) (x := "es_cnt")
    (e := .lit 0) (v := 0) (evalB_lit (by omega))
  have hJ2 : JCtx VAL OFF self U m j σ2 := by
    refine ⟨ctx_keep hC (by simp [hσ2, hσ1, Env.setVar]) fun y hy => ?_, ?_, ?_, ?_⟩
    · simp only [emitVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ2, hσ1, Env.setVar, hy.2.1, hy.2.2.1, hy.2.2.2.1]
    · simp [hσ2, hσ1, Env.setVar, hj_def]
    · simp [hσ2, hσ1, Env.setVar]
    · simp [hσ2, hσ1, Env.setVar]
  -- counting
  have hjm' : j < m := hlt
  obtain ⟨σ3, r4, hc3, hJ3, ha3, -, ho3, hv3⟩ :=
    (countLoop_spec (B := B) VAL OFF self U m H hb hjm').run (σ := σ2)
      ⟨hJ2, by simp [hσ2, Env.setVar]⟩
  have hml : (memsJ VAL OFF self U j).length ≤ U := by
    unfold memsJ; exact (List.length_filter_le _ _).trans (by simp)
  have r5 := Run.assign (B := B) (σ := σ3) (x := "en_v") (e := V "es_cnt")
    (v := (memsJ VAL OFF self U j).length) (by rw [← hc3]; exact evalB_var (by rw [hc3]; omega))
  obtain ⟨σ4, r6, ho4, ha4, -, hv4⟩ := (emitNat_frame (B := B) U).run
    (σ := σ3.setVar "en_v" (memsJ VAL OFF self U j).length)
    ⟨by simp [Env.setVar]; omega,
      by simp [Env.setVar]; exact (Words.size_le_self _).trans hml⟩
  have hJ4 : JCtx VAL OFF self U m j σ4 := by
    refine jctx_keep hJ3 (by rw [ha4]; rfl) fun y _ _ _ _ h5 h6 h7 h8 => ?_
    rw [hv4 y h6 h7 h8]; simp [Env.setVar, h5]
  -- writing
  obtain ⟨σ5, r7, ho5, hJ5, ha5, -, hv5⟩ :=
    (writeLoop_spec (B := B) VAL OFF self U m H hb hjm').run (σ := σ4) hJ4
  have h5j : σ5.vars "es_j" = j := hJ5.2.1
  have r8 := Run.assign (B := B) (σ := σ5) (x := "es_j") (e := .add (V "es_j") (.lit 1))
    (v := j + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ5) (evalB_var (x := "es_j") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h5j]; simp; omega)
      rw [h5j] at this; simpa using this)
  have e9j : (σ5.setVar "es_j" (j + 1)).vars "es_j" = j + 1 := by simp [Env.setVar]
  have e9o : (σ5.setVar "es_j" (j + 1)).out = σ5.out := rfl
  have hprod : (24 * H + 64) * U + (24 * H + 48 * U + 114) * U = (48 * H + 48 * U + 178) * U := by
    ring
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono ?_,
    ⟨?_, ?_, ?_⟩, by rw [e9j]⟩
  · simp only [Kset, size_var, size_lit, size_get, size_bin]; omega
  · refine ctx_keep hJ5.1 (by simp [Env.setVar]) fun y hy => ?_
    simp only [emitVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Env.setVar, if_neg hy.1]
  · rw [e9j]; omega
  · have e4v : (σ3.setVar "en_v" (memsJ VAL OFF self U j).length).vars "en_v" =
        (memsJ VAL OFF self U j).length := by simp [Env.setVar]
    have e4o : (σ3.setVar "en_v" (memsJ VAL OFF self U j).length).out = σ3.out := rfl
    have e2o : σ2.out = σ.out := rfl
    rw [e9j, e9o, ho5, ho4, e4v, e4o, ho3, e2o, hout, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, setBits]
    simp [memsJ, List.append_assoc]

/-- **The sets are written**, in the format of a Hitting Set word; the program touches no array and
no scalar outside `emitVars`. -/
theorem setsLoop_spec {B : ℕ} (VAL OFF : List ℕ) (self : Bool) (U m H : ℕ)
    (hb : Bounds VAL OFF U m H B) :
    Spec B (fun σ => Ctx VAL OFF self U m σ) setsLoop
      (fun σ σ' => σ'.out = σ.out ++ setsOut U m (inSetB VAL OFF self) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ ∀ y, y ∉ emitVars → σ'.vars y = σ.vars y)
      ((Kset U H + 4) * m + 6) := by
  intro σ hC
  have hU := hb.U_lt
  obtain ⟨σ', r, ⟨⟨-, -, ho⟩, hj⟩, hv, ha, hi, -⟩ :=
    (Spec.forRangeZero (B := B) "es_j" "es_m" (SSI VAL OFF self U m σ.out) m (Kset U H) (by omega)
      (fun _ h => h.2.1) (fun _ h => h.1.2.2.2.1)
      (setBody_spec VAL OFF self U m H hb σ.out)).frame.run (σ := σ)
      ⟨ctx_keep hC rfl fun y hy => by
          simp only [emitVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          simp [Env.setVar, hy.1], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, by rw [ho, hj]; rfl, ?_, ?_, ?_⟩
  · funext a; exact ha a (by simp [setBody, countLoop, countBody, writeLoop, writeBody, emitIf,
      emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody,
      EmitNat.digLoop, EmitNat.digBody, testCom, scanLoop, scanBody, Com.warrs])
  · exact hi (by simp [setBody, countLoop, countBody, writeLoop, writeBody, emitIf,
      emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody,
      EmitNat.digLoop, EmitNat.digBody, testCom, scanLoop, scanBody, Com.reads])
  · intro y hy
    simp only [emitVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact hv y (by simp [setBody, countLoop, countBody, writeLoop, writeBody, emitIf,
      emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody,
      EmitNat.digLoop, EmitNat.digBody, testCom, scanLoop, scanBody, Com.wvars, hy])

end Lax496464Proofs.WHierarchy.HittingSet.EmitSets
