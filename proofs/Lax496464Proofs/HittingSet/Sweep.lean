import Lax496464Proofs.HittingSet.Mark

/-!
# Sweeping the Marks

One pass over the universe: a marked element is written and unmarked. The elements come
out in increasing order, and the marks are all clear afterwards.
-/

namespace Lax496464Proofs.HittingSet.Sweep

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax496464Proofs.HittingSet.Emit Lax496464Proofs.HittingSet.Mark

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- Write `e` and clear its mark. -/
def emitE : Com := .seq (setNat (V "e")) (.store "mark" (V "e") (.lit 0))

def sweepBody : Com := .seq (.ite (.eq (.get "mark" (V "e")) (.lit 1)) emitE .skip) (bump "e")

def sweepLoop : Com := .seq (.assign "e" (.lit 0)) (.while (.lt (V "e") (V "nn")) sweepBody)

variable {B : ℕ}

/-- The invariant of the sweep, relative to the entry state `σ0`. -/
structure SInv (n Lm : ℕ) (E : List ℕ) (σ0 σ : Env) : Prop where
  hn : σ.vars "nn" = n
  he : σ.vars "e" ≤ n
  hlen : (σ.arrs "mark").length = Lm
  hmark : ∀ e' < Lm, (σ.arrs "mark").getD e' 0 = if σ.vars "e" ≤ e' ∧ e' ∈ E then 1 else 0
  hout : σ.out = σ0.out ++
    ((List.range (σ.vars "e")).filter fun x => decide (x ∈ E)).flatMap bitsNat
  kvars : ∀ v, v ∉ "e" :: SN → σ.vars v = σ0.vars v
  karrs : ∀ a, a ≠ "mark" → σ.arrs a = σ0.arrs a
  kinp : σ.inp = σ0.inp

/-- The cost of one element. -/
def Ksweep (S : ℕ) : ℕ := 48 * S + 60

theorem filter_range_succ_mem (E : List ℕ) {e : ℕ} (he : e ∈ E) :
    (List.range (e + 1)).filter (fun x => decide (x ∈ E)) =
      (List.range e).filter (fun x => decide (x ∈ E)) ++ [e] := by
  rw [List.range_succ, List.filter_append, List.filter_singleton, decide_eq_true he]; rfl

theorem filter_range_succ_not_mem (E : List ℕ) {e : ℕ} (he : e ∉ E) :
    (List.range (e + 1)).filter (fun x => decide (x ∈ E)) =
      (List.range e).filter (fun x => decide (x ∈ E)) := by
  rw [List.range_succ, List.filter_append, List.filter_singleton, decide_eq_false he]; simp

theorem sweepBody_spec (n Lm S : ℕ) (E : List ℕ) (σ0 : Env) (_hE : ∀ x ∈ E, x < n)
    (hnL : n ≤ Lm) (hLB : Lm + 2 < B) (hnB : n + 4 < B) (hS : n.size ≤ S) :
    Spec B (fun σ => SInv n Lm E σ0 σ ∧ σ.vars "e" < n) sweepBody
      (fun σ σ' => SInv n Lm E σ0 σ' ∧ σ'.vars "e" = σ.vars "e" + 1) (Ksweep S) := by
  intro σ ⟨I, hlt⟩
  obtain ⟨e, hed⟩ : ∃ e, σ.vars "e" = e := ⟨_, rfl⟩
  rw [hed] at hlt
  have heL : e < Lm := by omega
  have heB : e < B := by omega
  have eve : (V "e").evalB B σ = some e := by rw [← hed]; exact evalB_var (by omega)
  have hmk := I.hmark e heL
  rw [hed] at hmk
  have evmk : (Expr.get "mark" (V "e")).evalB B σ = some ((σ.arrs "mark").getD e 0) :=
    RunStep.eval_get B σ "mark" (V "e") e eve (by rw [I.hlen]; exact heL)
      (by rw [hmk]; split_ifs <;> omega)
  have evm : (Cond.eq (.get "mark" (V "e")) (.lit 1)).evalB B σ =
      some ((σ.arrs "mark").getD e 0 == 1) := evalB_condEq evmk (evalB_lit (by omega))
  have hstep : ∀ σ1 : Env, σ1.vars "e" = e →
      Run B (bump "e") σ1 (σ1.setVar "e" (e + 1)) 4 := fun σ1 h1 => by
    have := Run.assign (B := B) (σ := σ1) (x := "e") (e := .bin .add (V "e") (.lit 1))
      (RunStep.eval_add B σ1 (V "e") (.lit 1) e 1 (by rw [← h1]; exact evalB_var (by rw [h1]; omega))
        (evalB_lit (by omega)) (by omega))
    simpa [Expr.size] using this
  by_cases hin : e ∈ E
  · -- marked: write and clear
    rw [if_pos ⟨le_rfl, hin⟩] at hmk
    have htrue : (Cond.eq (.get "mark" (V "e")) (.lit 1)).evalB B σ = some true := by
      rw [evm, hmk]; rfl
    obtain ⟨σ1, r1, o1, k1⟩ := setNat_emits (B := B) (V "e") (fun σ => σ.vars "e") S
      (fun σ => σ.vars "e" = e) (fun σ h => evalB_var_eq rfl (by rw [h]; omega))
      (fun σ h => ⟨by rw [h]; omega, by rw [h]; exact le_trans (Nat.size_le_size (by omega)) hS⟩)
      σ hed
    have e1 : σ1.vars "e" = e := by rw [k1.var (by simp [SN]), hed]
    have a1 : σ1.arrs = σ.arrs := k1.2.1
    have rst : Run B (.store "mark" (V "e") (.lit 0)) σ1 (σ1.setArr "mark" e 0) 5 :=
      (Run.store (by rw [← e1]; exact evalB_var (by rw [e1]; omega)) (evalB_lit (by omega))
        (by rw [a1, I.hlen]; exact heL)).mono (by simp [Expr.size])
    have rite : Run B (.ite (.eq (.get "mark" (V "e")) (.lit 1)) emitE .skip) σ (σ1.setArr "mark" e 0)
        (1 + (Cond.eq (.get "mark" (V "e")) (.lit 1)).size + ((V "e").size + 48 * S + 41 + 5)) :=
      Run.ite_true htrue (r1.seq rst)
    have e2 : (σ1.setArr "mark" e 0).vars "e" = e := by simp [Env.setArr, e1]
    refine ⟨_, (rite.seq (hstep _ e2)).mono (by simp [Ksweep, Cond.size, Expr.size]; omega),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Env.setVar, hed]⟩
    all_goals simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
    · rw [k1.var (by simp [SN])]; exact I.hn
    · omega
    · rw [a1, List.length_set]; exact I.hlen
    · intro e' he'
      rw [a1]
      by_cases h' : e' = e
      · subst h'; rw [getD_set_eq _ (by rw [I.hlen]; exact heL)]
        rw [if_neg (by omega)]
      · rw [getD_set_ne _ h', I.hmark e' he', hed]
        by_cases h1 : e ≤ e' ∧ e' ∈ E
        · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
        · rw [if_neg h1, if_neg (fun h2 => h1 ⟨by omega, h2.2⟩)]
    · rw [o1, I.hout, hed, filter_range_succ_mem E hin, List.flatMap_append, List.append_assoc]
      simp [hed]
    · intro v hv
      have h1 : v ≠ "e" := fun h => hv (h ▸ by simp)
      rw [if_neg h1, k1.var (fun h => hv (List.mem_cons_of_mem _ h))]; exact I.kvars v hv
    · intro a ha; rw [if_neg ha, a1]; exact I.karrs a ha
    · rw [k1.2.2]; exact I.kinp
  · -- unmarked: skip
    rw [if_neg (fun h => hin h.2)] at hmk
    have hfalse : (Cond.eq (.get "mark" (V "e")) (.lit 1)).evalB B σ = some false := by
      rw [evm, hmk]; rfl
    have rite : Run B (.ite (.eq (.get "mark" (V "e")) (.lit 1)) emitE .skip) σ σ
        (1 + (Cond.eq (.get "mark" (V "e")) (.lit 1)).size + 1) :=
      Run.ite_false hfalse Run.skip
    refine ⟨_, (rite.seq (hstep σ hed)).mono (by simp [Ksweep, Cond.size, Expr.size]),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Env.setVar, hed]⟩
    all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    · exact I.hn
    · omega
    · exact I.hlen
    · intro e' he'
      rw [I.hmark e' he', hed]
      by_cases h1 : e ≤ e' ∧ e' ∈ E
      · have h1' : e + 1 ≤ e' := by
          rcases Nat.eq_or_lt_of_le h1.1 with h | h
          · exact absurd (h ▸ h1.2) hin
          · omega
        rw [if_pos h1, if_pos ⟨h1', h1.2⟩]
      · rw [if_neg h1, if_neg (fun h2 => h1 ⟨by omega, h2.2⟩)]
    · rw [I.hout, hed, filter_range_succ_not_mem E hin]
    · intro v hv
      have h1 : v ≠ "e" := fun h => hv (h ▸ by simp)
      rw [if_neg h1]; exact I.kvars v hv
    · exact I.karrs
    · exact I.kinp

theorem sweepLoop_spec (n Lm S : ℕ) (E : List ℕ) (σ0 : Env) (hE : ∀ x ∈ E, x < n)
    (hnL : n ≤ Lm) (hLB : Lm + 2 < B) (hnB : n + 4 < B) (hS : n.size ≤ S) :
    Spec B (fun σ => SInv n Lm E σ0 (σ.setVar "e" 0)) sweepLoop
      (fun _ σ' => SInv n Lm E σ0 σ' ∧ σ'.vars "e" = n) ((Ksweep S + 4) * n + 6) :=
  Spec.forRangeZero "e" "nn" (SInv n Lm E σ0) n (Ksweep S) (by omega)
    (fun _ h => h.he) (fun _ h => h.hn) (sweepBody_spec n Lm S E σ0 hE hnL hLB hnB hS)

/-- A mark vector with every entry `0` is the zero vector. -/
theorem mark_eq_replicate {l : List ℕ} {Lm : ℕ} (hlen : l.length = Lm)
    (h : ∀ e < Lm, l.getD e 0 = 0) : l = List.replicate Lm 0 := by
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have := h i (by omega)
  rw [List.getD_eq_getElem _ _ h1] at this
  rw [this, List.getElem_replicate]

/-- **The sweep**, from a state whose marks are exactly the elements of `E`. -/
theorem sweepLoop_run (n Lm S : ℕ) (E : List ℕ) (σ : Env) (hE : ∀ x ∈ E, x < n)
    (hnL : n ≤ Lm) (hLB : Lm + 2 < B) (hnB : n + 4 < B) (hS : n.size ≤ S)
    (hn : σ.vars "nn" = n) (hlen : (σ.arrs "mark").length = Lm)
    (hmark : ∀ e' < Lm, (σ.arrs "mark").getD e' 0 = if e' ∈ E then 1 else 0) :
    ∃ σ', Run B sweepLoop σ σ' ((Ksweep S + 4) * n + 6) ∧
      σ'.out = σ.out ++ ((List.range n).filter fun x => decide (x ∈ E)).flatMap bitsNat ∧
      σ'.arrs "mark" = List.replicate Lm 0 ∧
      (∀ v, v ∉ "e" :: SN → σ'.vars v = σ.vars v) ∧
      (∀ a, a ≠ "mark" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp := by
  obtain ⟨σ', r, I, he⟩ := sweepLoop_spec (B := B) n Lm S E σ hE hnL hLB hnB hS σ
    ⟨by simp [Env.setVar, hn], by simp, by simpa [Env.setVar] using hlen,
     fun e' he' => by simpa [Env.setVar] using hmark e' he', by simp [Env.setVar],
     fun v hv => by
       have h1 : v ≠ "e" := fun h => hv (h ▸ List.mem_cons_self ..)
       simp [Env.setVar, h1],
     fun a _ => rfl, rfl⟩
  refine ⟨σ', r, by rw [I.hout, he], mark_eq_replicate I.hlen fun e' he' => ?_, I.kvars, I.karrs,
    I.kinp⟩
  rw [I.hmark e' he', he]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have := hE e' h2; omega

end Lax496464Proofs.HittingSet.Sweep
