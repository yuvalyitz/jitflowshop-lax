import Lax496464Proofs.WHierarchy.HittingSet.WSHSMath
import Lax496464Proofs.WHierarchy.HittingSet.EmitNat

/-! # Weighted monotone satisfiability to Hitting Set: reading the formula

`wsRead` reads the tape `x.length :: encode α ++ [k]`: the number `c` of clauses into `ws_c`, the
variable of every literal (its code halved) into `hs_mem`, one clause after the other, the offset of
each clause into `es_off`, the number of literals into `hs_t`, and `k` into `ws_k`
(`WSHSMath.litsL`, `WSHSMath.offL`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WSHSRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax429075.CNF Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.HittingSet.WSHSMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitNat (V bump)

def litBody : Com :=
  .seq (.read "ws_v")
    (.seq (.store "hs_mem" (V "hs_t") (.div (V "ws_v") (.lit 2))) (.seq (bump "hs_t") (bump "ws_q")))
def litLoop : Com := .seq (.assign "ws_q" (.lit 0)) (.while (.lt (V "ws_q") (V "ws_l")) litBody)
def clauseBody : Com :=
  .seq (.store "es_off" (V "ws_j") (V "hs_t")) (.seq (.read "ws_l") (.seq litLoop (bump "ws_j")))
def clauseLoop : Com := .seq (.assign "ws_j" (.lit 0)) (.while (.lt (V "ws_j") (V "ws_c")) clauseBody)

/-- **Read the formula and the weight.** -/
def wsRead : Com :=
  .seq (.read "ws_len") (.seq (.read "ws_c") (.seq (.assign "hs_t" (.lit 0))
    (.seq clauseLoop (.seq (.store "es_off" (V "ws_c") (V "hs_t")) (.read "ws_k")))))

theorem getD_set_self (l : List ℕ) {i : ℕ} (v : ℕ) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_other (l : List ℕ) {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem litCode_div (l : Literal) : litCode l / 2 = l.index := by
  unfold litCode; split_ifs <;> omega

/-- The arrays: offsets of the clauses before `j`, variables of the positions before `t`. -/
def Arrs (α : Formula) (j t : ℕ) (σ : Env) : Prop :=
  (σ.arrs "es_off").length = α.length + 1 ∧ (∀ i < j, (σ.arrs "es_off").getD i 0 = cOff α i) ∧
    (σ.arrs "hs_mem").length = T α ∧ ∀ p < t, (σ.arrs "hs_mem").getD p 0 = (litsL α).getD p 0

/-- Part-way through clause `j`. -/
def LitI (α : Formula) (k j : ℕ) (hj : j < α.length) (σ : Env) : Prop :=
  σ.vars "ws_c" = α.length ∧ σ.vars "ws_j" = j ∧ σ.vars "ws_l" = (α[j]).length ∧
    σ.vars "ws_q" ≤ (α[j]).length ∧ σ.vars "hs_t" = cOff α j + σ.vars "ws_q" ∧
    σ.inp = ((α[j]).drop (σ.vars "ws_q")).map litCode ++ (α.drop (j + 1)).flatMap encC ++ [k] ∧
    Arrs α (j + 1) (σ.vars "hs_t") σ

/-- Part-way through the clauses. -/
def ClI (α : Formula) (k : ℕ) (σ : Env) : Prop :=
  σ.vars "ws_c" = α.length ∧ σ.vars "ws_j" ≤ α.length ∧ σ.vars "hs_t" = cOff α (σ.vars "ws_j") ∧
    σ.inp = (α.drop (σ.vars "ws_j")).flatMap encC ++ [k] ∧ Arrs α (σ.vars "ws_j") (σ.vars "hs_t") σ

/-- The value bound: codes, lengths and counts below `B`. -/
structure Fits (α : Formula) (k B : ℕ) : Prop where
  code_lt : ∀ C ∈ α, ∀ l ∈ C, litCode l < B
  T_lt : T α + α.length + 2 < B
  k_lt : k < B

theorem cOff_le_T (α : Formula) {j : ℕ} (hj : j ≤ α.length) : cOff α j ≤ T α := by
  rw [← cOff_length]; exact cOff_mono α hj

theorem pos_lt_T (α : Formula) {j q : ℕ} (hj : j < α.length) (hq : q < (α[j]).length) :
    cOff α j + q < T α := by
  have := cOff_le_T α (show j + 1 ≤ α.length by omega)
  rw [cOff_succ α hj] at this; omega

theorem litBody_spec {B : ℕ} (α : Formula) (k : ℕ) {j : ℕ} (hj : j < α.length) (hB : Fits α k B) :
    Spec B (fun σ => LitI α k j hj σ ∧ σ.vars "ws_q" < (α[j]).length) litBody
      (fun σ σ' => LitI α k j hj σ' ∧ σ'.vars "ws_q" = σ.vars "ws_q" + 1) 16 := by
  intro σ ⟨⟨hc, hjj, hl, hq, ht, hinp, hml, hoff, hmeml, hmem⟩, hlt⟩
  have hT := hB.T_lt
  set q := σ.vars "ws_q" with hq_def
  set lit := (α[j])[q] with hlit
  have hpos := pos_lt_T α hj hlt
  have hinp' : σ.inp = litCode lit :: (((α[j]).drop (q + 1)).map litCode ++
      (α.drop (j + 1)).flatMap encC ++ [k]) := by
    rw [hinp, List.drop_eq_getElem_cons hlt]; rfl
  have hcode : litCode lit < B := hB.code_lt _ (List.getElem_mem hj) _ (List.getElem_mem hlt)
  have r1 := Run.read (B := B) (σ := σ) (x := "ws_v") hinp'
  set σ1 : Env := { σ.setVar "ws_v" (litCode lit) with
    inp := ((α[j]).drop (q + 1)).map litCode ++ (α.drop (j + 1)).flatMap encC ++ [k] } with hσ1
  have h1t : σ1.vars "hs_t" = cOff α j + q := by simp [hσ1, Env.setVar, ht]
  have h1v : σ1.vars "ws_v" = litCode lit := by simp [hσ1, Env.setVar]
  have h1m : (σ1.arrs "hs_mem").length = T α := by simp [hσ1, Env.setVar, hmeml]
  have ev : (Expr.div (V "ws_v") (.lit 2)).evalB B σ1 = some lit.index := by
    rw [← litCode_div lit, ← h1v]
    exact evalB_bin (evalB_var (by rw [h1v]; exact hcode)) (evalB_lit (by omega))
      (by simp only [Bop.apply_div, h1v]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hcode)
  have r2 := Run.store (B := B) (σ := σ1) (a := "hs_mem") (i := V "hs_t") (e := .div (V "ws_v") (.lit 2))
    (evalB_var (by rw [h1t]; omega)) ev (by rw [h1m, h1t]; exact hpos)
  rw [h1t] at r2
  set σ2 := σ1.setArr "hs_mem" (cOff α j + q) lit.index with hσ2
  have h2t : σ2.vars "hs_t" = cOff α j + q := h1t
  have r3 := Run.assign (B := B) (σ := σ2) (x := "hs_t") (e := .add (V "hs_t") (.lit 1))
    (v := cOff α j + q + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "hs_t") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h2t]; simp; omega)
      rw [h2t] at this; simpa using this)
  set σ3 := σ2.setVar "hs_t" (cOff α j + q + 1) with hσ3
  have h3q : σ3.vars "ws_q" = q := by simp [hσ3, hσ2, hσ1, Env.setVar, Env.setArr, hq_def]
  have r4 := Run.assign (B := B) (σ := σ3) (x := "ws_q") (e := .add (V "ws_q") (.lit 1))
    (v := q + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ3) (evalB_var (x := "ws_q") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h3q]; simp; have := (α[j]).length; omega)
      rw [h3q] at this; simpa using this)
  set σ4 := σ3.setVar "ws_q" (q + 1) with hσ4
  have f_var : ∀ y, y ≠ "ws_v" → y ≠ "hs_t" → y ≠ "ws_q" → σ4.vars y = σ.vars y := by
    intro y h1 h2 h3; simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, Env.setArr, h1, h2, h3]
  have f_t : σ4.vars "hs_t" = cOff α j + q + 1 := by simp [hσ4, hσ3, Env.setVar]
  have f_q : σ4.vars "ws_q" = q + 1 := by simp [hσ4, Env.setVar]
  have f_mem : σ4.arrs "hs_mem" = (σ.arrs "hs_mem").set (cOff α j + q) lit.index := by
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, Env.setArr]
  have f_off : σ4.arrs "es_off" = σ.arrs "es_off" := by
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, Env.setArr]
  have f_inp : σ4.inp = ((α[j]).drop (q + 1)).map litCode ++ (α.drop (j + 1)).flatMap encC ++ [k] := by
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, Env.setArr]
  clear_value σ4
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by simp), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, f_q⟩
  · rw [f_var _ (by decide) (by decide) (by decide), hc]
  · rw [f_var _ (by decide) (by decide) (by decide), hjj]
  · rw [f_var _ (by decide) (by decide) (by decide), hl]
  · rw [f_q]; omega
  · rw [f_t, f_q]; omega
  · rw [f_inp, f_q]
  · rw [f_off, hml]
  · intro i hi; rw [f_off]; exact hoff i hi
  · rw [f_mem, List.length_set, hmeml]
  · intro p hp
    rw [f_t] at hp
    rw [f_mem]
    rcases Nat.lt_or_ge p (cOff α j + q) with h | h
    · rw [getD_set_other _ _ (by omega)]; exact hmem p (by rw [ht]; exact h)
    · rw [show p = cOff α j + q by omega, getD_set_self _ _ (by rw [hmeml]; exact hpos),
        litsL_getD α hj hlt]

theorem litLoop_spec {B : ℕ} (α : Formula) (k : ℕ) {j : ℕ} (hj : j < α.length) (hB : Fits α k B) :
    Spec B (fun σ => LitI α k j hj (σ.setVar "ws_q" 0)) litLoop
      (fun _ σ' => LitI α k j hj σ' ∧ σ'.vars "ws_q" = (α[j]).length)
      (20 * (α[j]).length + 6) := by
  have hT := hB.T_lt
  have := cOff_le_T α (show j + 1 ≤ α.length by omega)
  rw [cOff_succ α hj] at this
  exact Spec.forRangeZero "ws_q" "ws_l" (LitI α k j hj) (α[j]).length 16 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (litBody_spec α k hj hB)

theorem clauseBody_spec {B : ℕ} (α : Formula) (k : ℕ) (hB : Fits α k B) :
    Spec B (fun σ => ClI α k σ ∧ σ.vars "ws_j" < α.length) clauseBody
      (fun σ σ' => ClI α k σ' ∧ σ'.vars "ws_j" = σ.vars "ws_j" + 1) (20 * T α + 20) := by
  intro σ ⟨⟨hc, hjl, ht, hinp, hml, hoff, hmeml, hmem⟩, hlt⟩
  have hT := hB.T_lt
  set j := σ.vars "ws_j" with hj_def
  have hCT : (α[j]).length ≤ T α := by
    have := cOff_le_T α (show j + 1 ≤ α.length by omega)
    rw [cOff_succ α hlt] at this; omega
  have htT := cOff_le_T α hjl
  -- store the offset
  have r1 := Run.store (B := B) (σ := σ) (a := "es_off") (i := V "ws_j") (e := V "hs_t")
    (evalB_var (by omega)) (evalB_var (by rw [ht]; omega)) (by rw [hml]; omega)
  rw [ht] at r1
  set σ1 := σ.setArr "es_off" j (cOff α j) with hσ1
  have hinp1 : σ1.inp = (α[j]).length :: ((α[j]).map litCode ++
      ((α.drop (j + 1)).flatMap encC ++ [k])) := by
    rw [show σ1.inp = σ.inp from rfl, hinp, List.drop_eq_getElem_cons hlt]
    simp only [List.flatMap_cons, encC, List.cons_append, List.append_assoc]
  have r2 := Run.read (B := B) (σ := σ1) (x := "ws_l") hinp1
  set σ2 : Env := { σ1.setVar "ws_l" (α[j]).length with
    inp := (α[j]).map litCode ++ ((α.drop (j + 1)).flatMap encC ++ [k]) } with hσ2
  obtain ⟨σ3, r3, ⟨hc3, hj3, -, -, ht3, hinp3, hml3, hoff3, hmeml3, hmem3⟩, hq3⟩ :=
    (litLoop_spec (B := B) α k hlt hB).run (σ := σ2)
      ⟨by simp [hσ2, hσ1, Env.setVar, Env.setArr, hc], by simp [hσ2, hσ1, Env.setVar, Env.setArr, hj_def],
        by simp [hσ2, hσ1, Env.setVar, Env.setArr], by simp [Env.setVar],
        by simp [hσ2, hσ1, Env.setVar, Env.setArr, ht], by simp [hσ2, Env.setVar],
        by simp [hσ2, hσ1, Env.setVar, Env.setArr, hml],
        by
          intro i hi
          simp only [hσ2, hσ1, Env.setVar, Env.setArr, if_true]
          rcases Nat.lt_or_ge i j with h | h
          · rw [getD_set_other _ _ (by omega)]; exact hoff i h
          · rw [show i = j by omega, getD_set_self _ _ (by rw [hml]; omega)],
        by simp [hσ2, hσ1, Env.setVar, Env.setArr, hmeml],
        by
          intro p hp
          have hp' : p < σ.vars "hs_t" := by
            simp only [hσ2, hσ1, Env.setVar, String.reduceEq, ↓reduceIte] at hp
            simpa [Env.setArr] using hp
          simp only [hσ2, hσ1, Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
          exact hmem p hp'⟩
  have hj3' : σ3.vars "ws_j" = j := hj3
  have r4 := Run.assign (B := B) (σ := σ3) (x := "ws_j") (e := .add (V "ws_j") (.lit 1))
    (v := j + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ3) (evalB_var (x := "ws_j") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [hj3']; simp; omega)
      rw [hj3'] at this; simpa using this)
  have e4j : (σ3.setVar "ws_j" (j + 1)).vars "ws_j" = j + 1 := by simp [Env.setVar]
  have e4v : ∀ y, y ≠ "ws_j" → (σ3.setVar "ws_j" (j + 1)).vars y = σ3.vars y := by
    intro y hy; simp [Env.setVar, hy]
  have e4a : (σ3.setVar "ws_j" (j + 1)).arrs = σ3.arrs := rfl
  have e4i : (σ3.setVar "ws_j" (j + 1)).inp = σ3.inp := rfl
  have ht4 : σ3.vars "hs_t" = cOff α (j + 1) := by rw [ht3, hq3, cOff_succ α hlt]
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, e4j⟩
  · have : 20 * (α[j]).length ≤ 20 * T α := Nat.mul_le_mul_left _ hCT
    simp; omega
  · rw [e4v _ (by decide), hc3]
  · rw [e4j]; omega
  · rw [e4v _ (by decide), e4j, ht4]
  · rw [e4i, e4j, hinp3, hq3, List.drop_length, List.map_nil, List.nil_append]
  · rw [e4j, e4v _ (by decide), ht4]
    simp only [Arrs, e4a]
    exact ⟨hml3, hoff3, hmeml3, fun p hp => hmem3 p (by rw [ht3, hq3, ← cOff_succ α hlt]; exact hp)⟩

theorem clauseLoop_spec {B : ℕ} (α : Formula) (k : ℕ) (hB : Fits α k B) :
    Spec B (fun σ => ClI α k (σ.setVar "ws_j" 0)) clauseLoop
      (fun _ σ' => ClI α k σ' ∧ σ'.vars "ws_j" = α.length)
      ((20 * T α + 24) * α.length + 6) := by
  have hT := hB.T_lt
  exact Spec.forRangeZero "ws_j" "ws_c" (ClI α k) α.length (20 * T α + 20) (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (clauseBody_spec α k hB)

/-- What the reader ends with. -/
def Read (α : Formula) (k : ℕ) (σ : Env) : Prop :=
  σ.vars "ws_c" = α.length ∧ σ.vars "ws_k" = k ∧ σ.vars "hs_t" = T α ∧
    σ.arrs "es_off" = offL α ∧ σ.arrs "hs_mem" = litsL α ∧ σ.inp = []

theorem list_eq_getD {l l' : List ℕ} (hl : l.length = l'.length)
    (h : ∀ p < l.length, l.getD p 0 = l'.getD p 0) : l = l' := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := h i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- The cost of the reader. -/
def Kread (α : Formula) : ℕ := (20 * T α + 24) * α.length + 20

theorem wsRead_core {B : ℕ} (α : Formula) (k L : ℕ) (hB : Fits α k B) :
    Spec B (fun σ => σ.inp = L :: encode α ++ [k] ∧ (σ.arrs "es_off").length = α.length + 1 ∧
        (σ.arrs "hs_mem").length = T α) wsRead (fun _ σ' => Read α k σ') (Kread α) := by
  intro σ ⟨hinp, hol, hml⟩
  have hT := hB.T_lt
  have r1 := Run.read (B := B) (σ := σ) (x := "ws_len") (rest := encode α ++ [k]) hinp
  have r2 := Run.read (B := B) (σ := { σ.setVar "ws_len" L with inp := encode α ++ [k] })
    (x := "ws_c") (v := α.length) (rest := α.flatMap encC ++ [k]) (by simp [encode_eq])
  set σ2 : Env := { ({ σ.setVar "ws_len" L with inp := encode α ++ [k] } : Env).setVar "ws_c"
    α.length with inp := α.flatMap encC ++ [k] } with hσ2
  have r3 := Run.assign (B := B) (σ := σ2) (x := "hs_t") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  obtain ⟨σ4, r4, ⟨hc4, -, ht4, hinp4, hol4, hoff4, hml4, hmem4⟩, hj4⟩ :=
    (clauseLoop_spec (B := B) α k hB).run (σ := σ2.setVar "hs_t" 0)
      ⟨by simp [hσ2, Env.setVar], by simp [Env.setVar], by simp [hσ2, Env.setVar, cOff],
        by simp [hσ2, Env.setVar], by simp [hσ2, Env.setVar, hol], by simp [Env.setVar],
        by simp [hσ2, Env.setVar, hml], by simp [Env.setVar]⟩
  rw [hj4] at ht4 hinp4 hoff4
  rw [cOff_length] at ht4
  have hc4' : σ4.vars "ws_c" = α.length := hc4
  have r5 := Run.store (B := B) (σ := σ4) (a := "es_off") (i := V "ws_c") (e := V "hs_t")
    (evalB_var (by omega)) (evalB_var (by omega)) (by rw [hol4, hc4']; omega)
  rw [hc4', ht4] at r5
  set σ5 := σ4.setArr "es_off" α.length (T α) with hσ5
  have hinp5 : σ5.inp = [k] := by rw [show σ5.inp = σ4.inp from rfl, hinp4]; simp
  have r6 := Run.read (B := B) (σ := σ5) (x := "ws_k") hinp5
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Kread; simp; omega
  · simp [Env.setVar, hσ5, Env.setArr, hc4']
  · simp [Env.setVar]
  · simp [Env.setVar, hσ5, Env.setArr, ht4]
  · simp only [Env.setVar, hσ5, Env.setArr, if_true]
    refine list_eq_getD (by simp [hol4, offL]) fun i hi => ?_
    rw [List.length_set, hol4] at hi
    rw [offL_getD α (by omega)]
    rcases Nat.lt_or_ge i α.length with h | h
    · rw [getD_set_other _ _ (by omega)]; exact hoff4 i h
    · rw [show i = α.length by omega, getD_set_self _ _ (by omega), cOff_length]
  · simp only [Env.setVar, hσ5, Env.setArr, String.reduceEq, ↓reduceIte]
    exact list_eq_getD (by rw [hml4]; rfl) fun p hp => hmem4 p (by rw [ht4, ← hml4]; exact hp)
  · simp

end Lax496464Proofs.WHierarchy.HittingSet.WSHSRead
