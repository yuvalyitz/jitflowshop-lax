import Lax496464Proofs.HittingSet.Arrays
import Lax496464Proofs.HittingSet.Front
import Lax496464Proofs.HittingSet.Emit

/-!
# Marking the elements of a clause

One pass over the positions: at a position of clause `c`, the element of its literal is
marked, and counted if it was not marked before.
-/

namespace Lax496464Proofs.HittingSet.Mark

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax496464.HittingSetFromSat
open Lax496464Proofs.HittingSet.Emit Lax496464Proofs.HittingSet.Front Lax496464Proofs.HittingSet.Arrays

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- The element at position `p`, from the arrays. -/
def elemAt (vr sg : List ℕ) (p : ℕ) : ℕ := 2 * vr.getD p 0 + (1 - sg.getD p 0)

/-- The elements of clause `c` among the first `p` positions. -/
def elemsUpTo (vr sg cl : List ℕ) (c p : ℕ) : List ℕ :=
  ((List.range p).filter fun q => decide (cl.getD q 0 = c)).map (elemAt vr sg)

/-- The number of elements below `n` in a list. -/
def cntOf (n : ℕ) (E : List ℕ) : ℕ := ((List.range n).filter fun e => decide (e ∈ E)).length

theorem elemsUpTo_zero (vr sg cl : List ℕ) (c : ℕ) : elemsUpTo vr sg cl c 0 = [] := by
  simp [elemsUpTo]

theorem elemsUpTo_succ (vr sg cl : List ℕ) (c p : ℕ) :
    elemsUpTo vr sg cl c (p + 1) =
      elemsUpTo vr sg cl c p ++ (if cl.getD p 0 = c then [elemAt vr sg p] else []) := by
  unfold elemsUpTo
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  by_cases h : cl.getD p 0 = c
  · rw [if_pos h, List.filter_singleton, decide_eq_true h]; rfl
  · rw [if_neg h, List.filter_singleton, decide_eq_false h]; rfl

theorem cntOf_zero (n : ℕ) : cntOf n [] = 0 := by simp [cntOf]

theorem cntOf_append_mem (n : ℕ) (E : List ℕ) {e : ℕ} (he : e ∈ E) :
    cntOf n (E ++ [e]) = cntOf n E := by
  unfold cntOf
  congr 1
  refine List.filter_congr fun x _ => ?_
  simp only [List.mem_append, List.mem_singleton, decide_eq_decide]
  constructor
  · rintro (h | rfl) <;> assumption
  · exact Or.inl

theorem cntOf_append_new (n : ℕ) (E : List ℕ) {e : ℕ} (he : e ∉ E) (hn : e < n) :
    cntOf n (E ++ [e]) = cntOf n E + 1 := by
  unfold cntOf
  induction n with
  | zero => simp at hn
  | succ n ih =>
      rw [List.range_succ, List.filter_append, List.filter_append, List.length_append,
        List.length_append]
      by_cases hen : e = n
      · subst hen
        have h1 : (List.filter (fun x => decide (x ∈ E ++ [e])) [e]).length = 1 := by simp
        have h2 : (List.filter (fun x => decide (x ∈ E)) [e]).length = 0 := by simp [he]
        have h3 : (List.filter (fun x => decide (x ∈ E ++ [e])) (List.range e)).length =
            (List.filter (fun x => decide (x ∈ E)) (List.range e)).length := by
          congr 1
          refine List.filter_congr fun x hx => ?_
          have : x < e := List.mem_range.mp hx
          simp only [List.mem_append, List.mem_singleton, decide_eq_decide]
          constructor
          · rintro (h | rfl); exact h; omega
          · exact Or.inl
        omega
      · have := ih (by omega)
        have h1 : (List.filter (fun x => decide (x ∈ E ++ [e])) [n]).length =
            (List.filter (fun x => decide (x ∈ E)) [n]).length := by
          simp [List.filter_singleton, Ne.symm hen]
        omega

/-- Marking `e` in a mark vector. -/
theorem getD_set_eq (l : List ℕ) {e : ℕ} (he : e < l.length) (v : ℕ) :
    (l.set e v).getD e 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self he]; rfl

theorem getD_set_ne (l : List ℕ) {e e' : ℕ} (h : e' ≠ e) (v : ℕ) :
    (l.set e v).getD e' 0 = l.getD e' 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]; rfl

/-! ### The program -/

/-- The test and update of the mark of `e`. -/
def markE : Com :=
  .ite (.eq (.get "mark" (V "e")) (.lit 0)) (.seq (.store "mark" (V "e") (.lit 1)) (bump "cnt")) .skip

/-- The element of the position, then its mark. -/
def elemE : Com :=
  .seq (.assign "e" (.bin .add (.bin .mul (.lit 2) (.get "vr" (V "p")))
      (.bin .sub (.lit 1) (.get "sg" (V "p"))))) markE

def markBody : Com := .seq (.ite (.eq (.get "cl" (V "p")) (V "c")) elemE .skip) (bump "p")

def markLoop : Com := .seq (.assign "p" (.lit 0)) (.while (.lt (V "p") (V "k")) markBody)

variable {B : ℕ}

/-- The fixed data of the pass: the arrays, with their entries bounded. -/
structure Data (k n Lm : ℕ) (vr sg cl : List ℕ) (B : ℕ) : Prop where
  hvr : k ≤ vr.length
  hsg : k ≤ sg.length
  hcl : k ≤ cl.length
  hel : ∀ q < k, elemAt vr sg q < n
  hbvr : ∀ q < k, vr.getD q 0 < B
  hbsg : ∀ q < k, sg.getD q 0 ≤ 1
  hbcl : ∀ q < k, cl.getD q 0 < B
  hnL : n ≤ Lm
  hLB : Lm + 2 < B
  hkB : k + 1 < B

/-- The invariant of the pass, relative to the entry state `σ0`. -/
structure MInv (k n Lm c : ℕ) (vr sg cl : List ℕ) (σ0 σ : Env) : Prop where
  hk : σ.vars "k" = k
  hc : σ.vars "c" = c
  hp : σ.vars "p" ≤ k
  hvr : σ.arrs "vr" = vr
  hsg : σ.arrs "sg" = sg
  hcl : σ.arrs "cl" = cl
  hlen : (σ.arrs "mark").length = Lm
  hmark : ∀ e < Lm, (σ.arrs "mark").getD e 0 =
    if e ∈ elemsUpTo vr sg cl c (σ.vars "p") then 1 else 0
  hcnt : σ.vars "cnt" = cntOf n (elemsUpTo vr sg cl c (σ.vars "p"))
  kvars : ∀ v, v ∉ ["p", "e", "cnt"] → σ.vars v = σ0.vars v
  karrs : ∀ a, a ≠ "mark" → σ.arrs a = σ0.arrs a
  kinp : σ.inp = σ0.inp
  kout : σ.out = σ0.out

theorem mem_elemsUpTo_lt {k n Lm : ℕ} {vr sg cl : List ℕ} (D : Data k n Lm vr sg cl B)
    {c p : ℕ} (hp : p ≤ k) {e : ℕ} (he : e ∈ elemsUpTo vr sg cl c p) : e < n := by
  unfold elemsUpTo at he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  have := List.mem_range.mp (List.mem_filter.mp hq).1
  exact D.hel q (by omega)

/-- The cost of one position. -/
def Kmark : ℕ := 60

theorem markBody_spec (k n Lm c : ℕ) (vr sg cl : List ℕ) (σ0 : Env)
    (D : Data k n Lm vr sg cl B) (hcB : c < B) :
    Spec B (fun σ => MInv k n Lm c vr sg cl σ0 σ ∧ σ.vars "p" < k) markBody
      (fun σ σ' => MInv k n Lm c vr sg cl σ0 σ' ∧ σ'.vars "p" = σ.vars "p" + 1) Kmark := by
  intro σ ⟨I, hlt⟩
  obtain ⟨p, hpd⟩ : ∃ p, σ.vars "p" = p := ⟨_, rfl⟩
  rw [hpd] at hlt
  have hkB := D.hkB
  have hLB := D.hLB
  have hnL := D.hnL
  have hpB : p < B := by omega
  have evp : (V "p").evalB B σ = some p := by rw [← hpd]; exact evalB_var (by omega)
  -- cl[p] == c
  have evcl : (Expr.get "cl" (V "p")).evalB B σ = some (cl.getD p 0) := by
    have := RunStep.eval_get B σ "cl" (V "p") p evp (by rw [I.hcl]; have := D.hcl; omega)
      (by rw [I.hcl]; exact D.hbcl p hlt)
    rwa [I.hcl] at this
  have evc : (Cond.eq (.get "cl" (V "p")) (V "c")).evalB B σ = some (cl.getD p 0 == c) :=
    evalB_condEq evcl (by rw [← I.hc]; exact evalB_var (by rw [I.hc]; exact hcB))
  -- the step of the invariant, common to all branches
  have hstep : ∀ σ1 : Env, σ1.vars "p" = p →
      Run B (bump "p") σ1 (σ1.setVar "p" (p + 1)) 4 := fun σ1 h1 => by
    have := Run.assign (B := B) (σ := σ1) (x := "p") (e := .bin .add (V "p") (.lit 1))
      (RunStep.eval_add B σ1 (V "p") (.lit 1) p 1 (by rw [← h1]; exact evalB_var (by rw [h1]; omega))
        (evalB_lit (by omega)) (by omega))
    simpa [Expr.size] using this
  by_cases hclp : cl.getD p 0 = c
  · -- a position of clause `c`
    obtain ⟨e, hed⟩ : ∃ e, elemAt vr sg p = e := ⟨_, rfl⟩
    have hel := D.hel p hlt
    have hsgb := D.hbsg p hlt
    unfold elemAt at hel
    have heN : e < n := by rw [← hed]; unfold elemAt; exact hel
    have heL : e < Lm := by omega
    have heB : e < B := by omega
    have evvr : (Expr.get "vr" (V "p")).evalB B σ = some (vr.getD p 0) := by
      have := RunStep.eval_get B σ "vr" (V "p") p evp (by rw [I.hvr]; have := D.hvr; omega)
        (by rw [I.hvr]; exact D.hbvr p hlt)
      rwa [I.hvr] at this
    have evsg : (Expr.get "sg" (V "p")).evalB B σ = some (sg.getD p 0) := by
      have := RunStep.eval_get B σ "sg" (V "p") p evp (by rw [I.hsg]; have := D.hsg; omega)
        (by rw [I.hsg]; have := D.hbsg p hlt; omega)
      rwa [I.hsg] at this
    have heval : (Expr.bin .add (.bin .mul (.lit 2) (.get "vr" (V "p")))
        (.bin .sub (.lit 1) (.get "sg" (V "p")))).evalB B σ = some e := by
      rw [← hed]; unfold elemAt
      have h2 : 2 * vr.getD p 0 < B := by omega
      exact RunStep.eval_add B σ _ _ (2 * vr.getD p 0) (1 - sg.getD p 0)
        (RunStep.eval_mul B σ _ _ 2 (vr.getD p 0) (evalB_lit (by omega)) evvr h2)
        (RunStep.eval_sub B σ _ _ 1 (sg.getD p 0) (evalB_lit (by omega)) evsg (by omega))
        (by omega)
    have r1 : Run B (.assign "e" (.bin .add (.bin .mul (.lit 2) (.get "vr" (V "p")))
        (.bin .sub (.lit 1) (.get "sg" (V "p"))))) σ (σ.setVar "e" e) 12 :=
      (Run.assign heval).mono (by simp [Expr.size])
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ.setVar "e" e = σ1 := ⟨_, rfl⟩
    rw [hσ1] at r1
    have v1 : ∀ v, v ≠ "e" → σ1.vars v = σ.vars v := fun v h => by
      rw [← hσ1]; simp [Env.setVar, h]
    have e1 : σ1.vars "e" = e := by rw [← hσ1]; simp [Env.setVar]
    have a1 : σ1.arrs = σ.arrs := by rw [← hσ1]; rfl
    have o1 : σ1.out = σ.out := by rw [← hσ1]; rfl
    have i1 : σ1.inp = σ.inp := by rw [← hσ1]; rfl
    have eve : (V "e").evalB B σ1 = some e := by rw [← e1]; exact evalB_var (by rw [e1]; exact heB)
    have evmk : (Expr.get "mark" (V "e")).evalB B σ1 = some ((σ.arrs "mark").getD e 0) := by
      have := RunStep.eval_get B σ1 "mark" (V "e") e eve (by rw [a1, I.hlen]; exact heL)
        (by rw [a1, I.hmark e heL]; split_ifs <;> omega)
      rwa [a1] at this
    have evm : (Cond.eq (.get "mark" (V "e")) (.lit 0)).evalB B σ1 =
        some ((σ.arrs "mark").getD e 0 == 0) := evalB_condEq evmk (evalB_lit (by omega))
    have hmk := I.hmark e heL
    rw [hpd] at hmk
    have hE : elemsUpTo vr sg cl c (p + 1) = elemsUpTo vr sg cl c p ++ [e] := by
      rw [elemsUpTo_succ, if_pos hclp, hed]
    by_cases hin : e ∈ elemsUpTo vr sg cl c p
    · -- already marked
      rw [if_pos hin] at hmk
      have hfalse : (Cond.eq (.get "mark" (V "e")) (.lit 0)).evalB B σ1 = some false := by
        rw [evm, hmk]; rfl
      have rite : Run B markE σ1 σ1 (1 + (Cond.eq (.get "mark" (V "e")) (.lit 0)).size + 1) :=
        Run.ite_false hfalse Run.skip
      have rbr : Run B elemE σ σ1 _ := r1.seq rite
      have rout : Run B (.ite (.eq (.get "cl" (V "p")) (V "c")) elemE .skip) σ σ1 _ :=
        Run.ite_true (by rw [evc, hclp, beq_self_eq_true]) rbr
      refine ⟨_, (rout.seq (hstep σ1 (by rw [v1 _ (by decide), hpd]))).mono (by
        simp [Kmark, Cond.size, Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        by simp [Env.setVar, hpd]⟩
      all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      · rw [v1 _ (by decide)]; exact I.hk
      · rw [v1 _ (by decide)]; exact I.hc
      · omega
      · rw [a1]; exact I.hvr
      · rw [a1]; exact I.hsg
      · rw [a1]; exact I.hcl
      · rw [a1]; exact I.hlen
      · intro e' he'
        rw [a1, I.hmark e' he', hpd, hE]
        simp only [List.mem_append, List.mem_singleton]
        by_cases h' : e' = e
        · subst h'; simp [hin]
        · simp [h']
      · rw [v1 _ (by decide), I.hcnt, hpd, hE, cntOf_append_mem n _ hin]
      · intro v hv
        have h1 : v ≠ "p" := fun h => hv (h ▸ by simp)
        have h2 : v ≠ "e" := fun h => hv (h ▸ by simp)
        rw [if_neg h1, v1 v h2]; exact I.kvars v hv
      · intro a ha; rw [a1]; exact I.karrs a ha
      · rw [i1]; exact I.kinp
      · rw [o1]; exact I.kout
    · -- new: mark and count
      rw [if_neg hin] at hmk
      have htrue : (Cond.eq (.get "mark" (V "e")) (.lit 0)).evalB B σ1 = some true := by
        rw [evm, hmk]; rfl
      have rst : Run B (.store "mark" (V "e") (.lit 1)) σ1 (σ1.setArr "mark" e 1) 5 :=
        (Run.store eve (evalB_lit (by omega)) (by rw [a1, I.hlen]; exact heL)).mono
          (by simp [Expr.size])
      have c1 : (σ1.setArr "mark" e 1).vars "cnt" = σ.vars "cnt" := by
        simp [Env.setArr]; exact v1 _ (by decide)
      have rcnt : Run B (bump "cnt") (σ1.setArr "mark" e 1)
          ((σ1.setArr "mark" e 1).setVar "cnt" (σ.vars "cnt" + 1)) 4 := by
        have hcB' : σ.vars "cnt" + 1 < B := by
          rw [I.hcnt]
          have : cntOf n (elemsUpTo vr sg cl c (σ.vars "p")) ≤ n := by
            unfold cntOf; exact le_trans (List.length_filter_le _ _) (by simp)
          omega
        have := Run.assign (B := B) (σ := σ1.setArr "mark" e 1) (x := "cnt")
          (e := .bin .add (V "cnt") (.lit 1))
          (RunStep.eval_add B _ (V "cnt") (.lit 1) (σ.vars "cnt") 1
            (by rw [← c1]; exact evalB_var (by rw [c1]; omega)) (evalB_lit (by omega)) (by omega))
        simpa [Expr.size] using this
      obtain ⟨σ3, hσ3⟩ : ∃ σ3, (σ1.setArr "mark" e 1).setVar "cnt" (σ.vars "cnt" + 1) = σ3 :=
        ⟨_, rfl⟩
      rw [hσ3] at rcnt
      have rite : Run B markE σ1 σ3
          (1 + (Cond.eq (.get "mark" (V "e")) (.lit 0)).size + (5 + 4)) :=
        Run.ite_true htrue (rst.seq rcnt)
      have rout : Run B (.ite (.eq (.get "cl" (V "p")) (V "c")) elemE .skip) σ σ3 _ :=
        Run.ite_true (by rw [evc, hclp, beq_self_eq_true]) (r1.seq rite)
      have v3 : ∀ v, v ≠ "cnt" → v ≠ "e" → σ3.vars v = σ.vars v := fun v h1 h2 => by
        rw [← hσ3]; simp [Env.setVar, Env.setArr, h1]; exact v1 v h2
      have cnt3 : σ3.vars "cnt" = σ.vars "cnt" + 1 := by rw [← hσ3]; simp [Env.setVar]
      have a3 : ∀ a, a ≠ "mark" → σ3.arrs a = σ.arrs a := fun a ha => by
        rw [← hσ3]; simp [Env.setVar, Env.setArr, ha, a1]
      have m3 : σ3.arrs "mark" = (σ.arrs "mark").set e 1 := by
        rw [← hσ3]; simp [Env.setVar, Env.setArr, a1]
      have o3 : σ3.out = σ.out := by rw [← hσ3]; simp [Env.setVar, Env.setArr, o1]
      have i3 : σ3.inp = σ.inp := by rw [← hσ3]; simp [Env.setVar, Env.setArr, i1]
      refine ⟨_, (rout.seq (hstep σ3 (by rw [v3 _ (by decide) (by decide), hpd]))).mono (by
        simp [Kmark, Cond.size, Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        by simp [Env.setVar, hpd]⟩
      all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      · rw [v3 _ (by decide) (by decide)]; exact I.hk
      · rw [v3 _ (by decide) (by decide)]; exact I.hc
      · omega
      · rw [a3 _ (by decide)]; exact I.hvr
      · rw [a3 _ (by decide)]; exact I.hsg
      · rw [a3 _ (by decide)]; exact I.hcl
      · rw [m3, List.length_set]; exact I.hlen
      · intro e' he'
        rw [m3, hE]
        simp only [List.mem_append, List.mem_singleton]
        by_cases h' : e' = e
        · subst h'; rw [getD_set_eq _ (by rw [I.hlen]; exact heL)]; simp
        · rw [getD_set_ne _ h', I.hmark e' he', hpd]; simp [h']
      · rw [cnt3, I.hcnt, hpd, hE, cntOf_append_new n _ hin heN]
      · intro v hv
        have h1 : v ≠ "p" := fun h => hv (h ▸ by simp)
        have h2 : v ≠ "e" := fun h => hv (h ▸ by simp)
        have h3 : v ≠ "cnt" := fun h => hv (h ▸ by simp)
        rw [if_neg h1, v3 v h3 h2]; exact I.kvars v hv
      · intro a ha; rw [a3 a ha]; exact I.karrs a ha
      · rw [i3]; exact I.kinp
      · rw [o3]; exact I.kout
  · -- another clause's position
    have rout : Run B (.ite (.eq (.get "cl" (V "p")) (V "c")) elemE .skip) σ σ
        (1 + (Cond.eq (.get "cl" (V "p")) (V "c")).size + 1) :=
      Run.ite_false (by rw [evc, beq_eq_false_iff_ne.mpr hclp]) Run.skip
    have hE : elemsUpTo vr sg cl c (p + 1) = elemsUpTo vr sg cl c p := by
      rw [elemsUpTo_succ, if_neg hclp, List.append_nil]
    refine ⟨_, (rout.seq (hstep σ hpd)).mono (by simp [Kmark, Cond.size, Expr.size]),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Env.setVar, hpd]⟩
    all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    · exact I.hk
    · exact I.hc
    · omega
    · exact I.hvr
    · exact I.hsg
    · exact I.hcl
    · exact I.hlen
    · intro e' he'; rw [I.hmark e' he', hpd, hE]
    · rw [I.hcnt, hpd, hE]
    · intro v hv
      have h1 : v ≠ "p" := fun h => hv (h ▸ by simp)
      rw [if_neg h1]; exact I.kvars v hv
    · exact I.karrs
    · exact I.kinp
    · exact I.kout

theorem markLoop_spec (k n Lm c : ℕ) (vr sg cl : List ℕ) (σ0 : Env)
    (D : Data k n Lm vr sg cl B) (hcB : c < B) :
    Spec B (fun σ => MInv k n Lm c vr sg cl σ0 (σ.setVar "p" 0)) markLoop
      (fun _ σ' => MInv k n Lm c vr sg cl σ0 σ' ∧ σ'.vars "p" = k) ((Kmark + 4) * k + 6) :=
  Spec.forRangeZero "p" "k" (MInv k n Lm c vr sg cl σ0) k Kmark (by have := D.hkB; omega)
    (fun _ h => h.hp) (fun _ h => h.hk) (markBody_spec k n Lm c vr sg cl σ0 D hcB)

/-! ### What the pass computes, for the arrays of a formula -/

theorem elemAt_eq {F : Formula} {vr sg cl : List ℕ} (P : Post F vr sg cl) {q : ℕ}
    (hq : q < (lits F).length) : elemAt vr sg q = elem ((lits F).getD q dflt) := by
  unfold elemAt elem
  rw [P.hvr q hq, P.hsg q hq]
  split_ifs <;> omega

/-- After the whole pass, the elements collected are those of clause `c`. -/
theorem mem_elemsUpTo_iff {F : Formula} {vr sg cl : List ℕ} (P : Post F vr sg cl) {c : ℕ}
    (hc : c < F.length) (e : ℕ) :
    e ∈ elemsUpTo vr sg cl c (lits F).length ↔ e ∈ (F.getD c []).map elem := by
  unfold elemsUpTo
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨q, ⟨hq, hcq⟩, rfl⟩
    refine ⟨(lits F).getD q dflt, ?_, (elemAt_eq P hq).symm⟩
    rw [mem_getD_iff_pos F hc]
    exact ⟨q, hq, by rw [← P.hcl q hq]; exact hcq, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [mem_getD_iff_pos F hc] at hl
    obtain ⟨q, hq, hcq, hlq⟩ := hl
    exact ⟨q, ⟨hq, by rw [P.hcl q hq]; exact hcq⟩, by rw [elemAt_eq P hq]; exact congrArg elem hlq⟩

end Lax496464Proofs.HittingSet.Mark
