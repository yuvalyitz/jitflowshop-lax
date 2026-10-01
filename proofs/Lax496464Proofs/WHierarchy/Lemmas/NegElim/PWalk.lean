import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PTr
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr

/-! # One turn of the walk, for every kind of token

One turn for each kind of first pending formula (`turn_rel`, `turn_sv`, `turn_eq`, `turn_neg`,
`turn_and`, `turn_or`, `turn_ex`, `turn_all`), assembled into `trBody_spec`; `trLoop_spec`: at the
end of the walk the whole translation has been written. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWalk

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PTr Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex

variable {x T0 : List ℕ} {ctot : ℕ} {out0 : List ℕ}

theorem pb_le (b : Bool) : pb b ≤ 1 := by cases b <;> simp [pb]

theorem Kneg_le_Kd {r : ℕ} (hr : r ≤ x.length) : Kneg r + 28 * r + 200 ≤ Kd x := by
  have := Kneg_mono hr; unfold Kd; omega

/-- The facts one turn starts from: the first pending formula `f` with polarity `pol`, at
position `p`, the others `rest`. -/
structure Turn (x : List ℕ) (ctot : ℕ) (pol : Bool) (f : Formula) (rest : List (Bool × Formula))
    (p c : ℕ) (st : List ℕ) : Prop where
  drop : x.drop p = f.encode ++ pend rest
  len : p + (f.encode.length + (pend rest).length) = x.length
  stl : st.length = x.length + 2
  stk : st.take rest.length = stackOf rest
  top : st.getD rest.length 0 = pb pol
  cB : c + 2 * x.length + 1 < Bv x

theorem Turn.hh {pol : Bool} {f : Formula} {rest : List (Bool × Formula)} {p c : ℕ} {st : List ℕ}
    (t : Turn x ctot pol f rest p c st) : rest.length + 2 < x.length + 2 ∧ p < x.length := by
  have := length_le_pend rest
  have := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f)
  have := t.len
  omega

/-- The statement of one turn from the state `σ`, with the pointer at `p`. -/
def TurnGoal (x T0 : List ℕ) (ctot : ℕ) (out0 : List ℕ) (p : ℕ) (σ : Env) : Prop :=
  Spec (Bv x) (fun τ => τ = σ) trBody
    (fun _ σ' => TI x T0 ctot out0 σ' ∧ x.length - σ'.vars "p" < x.length - p) (Kd x + 60)

set_option maxHeartbeats 4000000 in
theorem turn_rel {pol : Bool} {i : ℕ} {ys : List ℕ} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .rel i ys) :: rest) E σ)
    (t : Turn x ctot pol (.rel i ys) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  obtain ⟨r, hrdef⟩ : ∃ r, ys.length = r := ⟨_, rfl⟩
  have hl := len_lt_Bv x
  have hbig := Bv_big x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hcode : (Formula.rel i ys).encode = 0 :: i :: r :: ys := by rw [← hrdef]; rfl
  have hd := t.drop
  rw [hcode] at hd
  have hlen := t.len
  rw [hcode] at hlen
  simp only [List.length_cons] at hlen
  have g0 : x.getD p 0 = 0 := by have := drop_getD hd 0; simpa using this
  have g1 : x.getD (p + 1) 0 = i := by have := drop_getD hd 1; simpa using this
  have g2 : x.getD (p + 2) 0 = r := by have := drop_getD hd 2; simpa using this
  have hys : ysOf x p r = ys := by
    apply List.ext_getElem (by simp [hrdef])
    intro l h1 h2
    simp only [ysOf, getElem_seqL, seqE, if_true]
    have := drop_getD hd (l + 3)
    rw [show p + (l + 3) = p + 3 + l by ring] at this
    rw [this, List.getD_eq_getElem?_getD]
    simp [List.getElem?_append_left h2, List.getElem?_eq_getElem h2]
  have hi5 : 5 * i + 5 < Bv x := by
    have := getD_le_maxEntry x (p + 1); rw [g1] at this; omega
  have hcB := t.cB
  have hstl := t.stl
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 0) dispatch
      (fun τ σ' => σ'.out = τ.out ++ (tr pol (.rel i (ysOf x p r)) c).encode ∧
        AP x (p + 3 + r) (c + cnt pol (.rel i (ysOf x p r))) rest.length st σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega)
      (fun _ => armPre ((relBr_spec pol rfl g1 g2 (by omega) hi5 (by omega) (by omega)).mono
        (Kneg_le_Kd (by omega))))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun n0 _ _ _ _ _ => absurd rfl n0)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 3 + r) = pend rest := by
    have := drop_append (l₁ := 0 :: i :: r :: ys) hd
    simp only [List.length_cons, hrdef] at this
    rw [show p + 3 + r = p + (r + 1 + 1 + 1) by ring]; exact this
  rw [hys] at hQ1 hQ2
  refine ⟨σ', hrun, ⟨rest, _, WS_next hw rest _ _ _ st hQ2 (by rw [hQ1, hτ]) (by omega) hdr t.stl
    t.stk (by rfl) (by simp only [cntL_cons]; omega)⟩, ?_⟩
  rw [hQ2.2.1]; omega

theorem tr_setVar (pol : Bool) (ys : List ℕ) (c : ℕ) : tr pol (.setVar ys) c = .setVar ys := by
  cases pol <;> rfl

set_option maxHeartbeats 4000000 in
theorem turn_sv {pol : Bool} {ys : List ℕ} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .setVar ys) :: rest) E σ)
    (t : Turn x ctot pol (.setVar ys) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  obtain ⟨r, hrdef⟩ : ∃ r, ys.length = r := ⟨_, rfl⟩
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hcode : (Formula.setVar ys).encode = 1 :: r :: ys := by rw [← hrdef]; rfl
  have hd := t.drop
  rw [hcode] at hd
  have hlen := t.len
  rw [hcode] at hlen
  simp only [List.length_cons] at hlen
  have g0 : x.getD p 0 = 1 := by have := drop_getD hd 0; simpa using this
  have g1 : x.getD (p + 1) 0 = r := by have := drop_getD hd 1; simpa using this
  have hys : seqL x 0 (p + 2) r = ys := by
    apply List.ext_getElem (by simp [hrdef])
    intro l h1 h2
    simp only [getElem_seqL, seqE, if_true]
    have := drop_getD hd (l + 2)
    rw [show p + (l + 2) = p + 2 + l by ring] at this
    rw [this, List.getD_eq_getElem?_getD]
    simp [List.getElem?_append_left h2, List.getElem?_eq_getElem h2]
  have hstl := t.stl
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 1) dispatch
      (fun τ σ' => σ'.out = τ.out ++ (Formula.setVar (seqL x 0 (p + 2) r)).encode ∧
        AP x (p + 2 + r) c rest.length st σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide))
      (fun _ => armPre ((svBr_spec g1 (by omega) (by omega)).mono (by unfold Kd; omega)))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ n1 _ _ _ _ => absurd rfl n1)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 2 + r) = pend rest := by
    have := drop_append (l₁ := 1 :: r :: ys) hd
    simp only [List.length_cons, hrdef] at this
    rw [show p + 2 + r = p + (r + 1 + 1) by ring]; exact this
  rw [hys] at hQ1
  have hQ2' : AP x (p + 2 + r) (c + cnt pol (.setVar ys)) rest.length st σ' := by
    have : cnt pol (.setVar ys) = 0 := by cases pol <;> rfl
    rw [this, Nat.add_zero]; exact hQ2
  refine ⟨σ', hrun, ⟨rest, _, WS_next hw rest _ _ _ st hQ2' (by rw [hQ1, hτ]) (by omega) hdr t.stl
    t.stk (by rw [trL_atom, tr_setVar]) (by simp only [cntL_cons]; omega)⟩, ?_⟩
  rw [hQ2.2.1]; omega

set_option maxHeartbeats 4000000 in
theorem turn_eq {pol : Bool} {u v : ℕ} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .eq u v) :: rest) E σ)
    (t : Turn x ctot pol (.eq u v) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.length_nil] at hd hlen
  have g0 : x.getD p 0 = 2 := by have := drop_getD hd 0; simpa using this
  have g1 : x.getD (p + 1) 0 = u := by have := drop_getD hd 1; simpa using this
  have g2 : x.getD (p + 2) 0 = v := by have := drop_getD hd 2; simpa using this
  have hstl := t.stl
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 2) dispatch
      (fun τ σ' => σ'.out = τ.out ++ (tr pol (.eq u v) c).encode ∧
        AP x (p + 3) c rest.length st σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => armPre ((eqBr_spec pol rfl u v g1 g2 (by omega)).mono (by unfold Kd; omega)))
      (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ n2 _ _ _ => absurd rfl n2)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 3) = pend rest := by
    have := drop_append (l₁ := [2, u, v]) hd
    simpa using this
  have hQ2' : AP x (p + 3) (c + cnt pol (.eq u v)) rest.length st σ' := by
    have : cnt pol (.eq u v) = 0 := by cases pol <;> rfl
    rw [this, Nat.add_zero]; exact hQ2
  refine ⟨σ', hrun, ⟨rest, _, WS_next hw rest _ _ _ st hQ2' (by rw [hQ1, hτ]) (by omega) hdr t.stl
    t.stk (by rw [trL_atom]) (by simp only [cntL_cons]; omega)⟩, ?_⟩
  rw [hQ2.2.1]; omega

theorem pb_not (b : Bool) : 1 - pb b = pb (!b) := by cases b <;> rfl

set_option maxHeartbeats 4000000 in
theorem turn_neg {pol : Bool} {f : Formula} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .neg f) :: rest) E σ)
    (t : Turn x ctot pol (.neg f) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.cons_append] at hd hlen
  have g0 : x.getD p 0 = 3 := by have := drop_getD hd 0; simpa using this
  have hstl := t.stl
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 3) dispatch
      (fun τ σ' => σ'.out = τ.out ∧
        AP x (p + 1) c (rest.length + 1) (st.set rest.length (1 - pb pol)) σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
      (fun _ => armPre ((negBr_spec (pb_le pol) (by omega) (by omega) (by omega)).mono
        (by unfold Kd; omega)))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ _ n3 _ _ => absurd rfl n3)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 1) = pend ((!pol, f) :: rest) := by
    have := drop_append (l₁ := [3]) hd
    simpa using this
  rw [pb_not] at hQ2
  refine ⟨σ', hrun, ⟨(!pol, f) :: rest, E ++ [], WS_next hw ((!pol, f) :: rest) [] _ _ _ hQ2
    (by rw [hQ1, hτ, List.append_nil]) (by simp; omega) hdr (by simp; omega)
    (by rw [show ((!pol, f) :: rest).length = rest.length + 1 by simp,
      take_set_one _ _ _ _ (by omega) t.stk]; simp) (by rw [trL_neg]; rfl)
    (by rw [cntL_neg])⟩, ?_⟩
  rw [hQ2.2.1]; omega

theorem tr_con_and (pol : Bool) : 5 - pb pol = if pol then 4 else 5 := by cases pol <;> rfl
theorem tr_con_or (pol : Bool) : 4 + pb pol = if pol then 5 else 4 := by cases pol <;> rfl

set_option maxHeartbeats 4000000 in
theorem turn_and {pol : Bool} {f g : Formula} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .and f g) :: rest) E σ)
    (t : Turn x ctot pol (.and f g) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.cons_append, List.length_append] at hd hlen
  have g0 : x.getD p 0 = 4 := by have := drop_getD hd 0; simpa using this
  have hstl := t.stl
  have hlp := length_le_pend rest
  have hlf := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil g)
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 4) dispatch
      (fun τ σ' => σ'.out = τ.out ++ [5 - pb pol] ∧
        AP x (p + 1) c (rest.length + 2) ((st.set rest.length (pb pol)).set (rest.length + 1) (pb pol))
          σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => armPre ((conBr_spec (.sub (L 5) (V "pl")) (5 - pb pol) (fun σ h => by
          have := pb_le pol
          rw [evalB_bin (evalB_lit (by omega)) (evalB_var (by rw [h.2.2.1]; omega))
            (by simp [h.2.2.1]; omega)]
          simp [h.2.2.1]) (pb_le pol) (by omega) (by omega) (by omega)).mono
        (by simp; unfold Kd; omega)))
      (fun h => absurd h (by decide))
      (fun _ _ _ _ n4 _ => absurd rfl n4)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 1) = pend ((pol, f) :: (pol, g) :: rest) := by
    have := drop_append (l₁ := [4]) hd
    simpa using this
  refine ⟨σ', hrun, ⟨(pol, f) :: (pol, g) :: rest, _, WS_next hw ((pol, f) :: (pol, g) :: rest)
    [5 - pb pol] _ _ _ hQ2 (by rw [hQ1, hτ]) (by simp; omega) hdr (by simp; omega)
    (by rw [show ((pol, f) :: (pol, g) :: rest).length = rest.length + 2 by simp, take_set_two _ _ _
      (by omega), t.stk]; simp) (by rw [trL_and, tr_con_and]; rfl) (by rw [cntL_and])⟩, ?_⟩
  rw [hQ2.2.1]; omega

set_option maxHeartbeats 4000000 in
theorem turn_or {pol : Bool} {f g : Formula} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .or f g) :: rest) E σ)
    (t : Turn x ctot pol (.or f g) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.cons_append, List.length_append] at hd hlen
  have g0 : x.getD p 0 = 5 := by have := drop_getD hd 0; simpa using this
  have hstl := t.stl
  have hlp := length_le_pend rest
  have hlf := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil g)
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 5) dispatch
      (fun τ σ' => σ'.out = τ.out ++ [4 + pb pol] ∧
        AP x (p + 1) c (rest.length + 2) ((st.set rest.length (pb pol)).set (rest.length + 1) (pb pol))
          σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
      (fun _ => armPre ((conBr_spec (.add (L 4) (V "pl")) (4 + pb pol) (fun σ h => by
          have := pb_le pol
          rw [evalB_bin (evalB_lit (by omega)) (evalB_var (by rw [h.2.2.1]; omega))
            (by simp [h.2.2.1]; omega)]
          simp [h.2.2.1]) (pb_le pol) (by omega) (by omega) (by omega)).mono
        (by simp; unfold Kd; omega)))
      (fun _ _ _ _ _ n5 => absurd rfl n5)
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 1) = pend ((pol, f) :: (pol, g) :: rest) := by
    have := drop_append (l₁ := [5]) hd
    simpa using this
  refine ⟨σ', hrun, ⟨(pol, f) :: (pol, g) :: rest, _, WS_next hw ((pol, f) :: (pol, g) :: rest)
    [4 + pb pol] _ _ _ hQ2 (by rw [hQ1, hτ]) (by simp; omega) hdr (by simp; omega)
    (by rw [show ((pol, f) :: (pol, g) :: rest).length = rest.length + 2 by simp, take_set_two _ _ _
      (by omega), t.stk]; simp) (by rw [trL_or, tr_con_or]; rfl) (by rw [cntL_or])⟩, ?_⟩
  rw [hQ2.2.1]; omega

set_option maxHeartbeats 4000000 in
theorem turn_ex {pol : Bool} {y : ℕ} {f : Formula} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .ex y f) :: rest) E σ)
    (t : Turn x ctot pol (.ex y f) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.cons_append] at hd hlen
  have g0 : x.getD p 0 = 6 := by have := drop_getD hd 0; simpa using this
  have g1 : x.getD (p + 1) 0 = y := by have := drop_getD hd 1; simpa using this
  have hstl := t.stl
  have hlf := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f)
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 6) dispatch
      (fun τ σ' => σ'.out = τ.out ++ [6, y] ∧
        AP x (p + 2) c (rest.length + 1) (st.set rest.length (pb pol)) σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ _ _ _ _ => (qBr_spec 6 y g1 (by omega) (by omega) (pb_le pol) (by omega) (by omega)
        (by omega)).mono (by unfold Kd; omega))
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 2) = pend ((pol, f) :: rest) := by
    have := drop_append (l₁ := [6, y]) hd
    simpa using this
  refine ⟨σ', hrun, ⟨(pol, f) :: rest, _, WS_next hw ((pol, f) :: rest) [6, y] _ _ _ hQ2
    (by rw [hQ1, hτ]) (by simp; omega) hdr (by simp; omega)
    (by rw [show ((pol, f) :: rest).length = rest.length + 1 by simp,
      take_set_one _ _ _ _ (by omega) t.stk]; simp) (by rw [trL_ex]; rfl) (by rw [cntL_ex])⟩, ?_⟩
  rw [hQ2.2.1]; omega

set_option maxHeartbeats 4000000 in
theorem turn_all {pol : Bool} {y : ℕ} {f : Formula} {rest : List (Bool × Formula)} {E : List ℕ}
    {σ : Env} (hw : WS x T0 ctot out0 ((pol, .all y f) :: rest) E σ)
    (t : Turn x ctot pol (.all y f) rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st")) :
    TurnGoal x T0 ctot out0 (σ.vars "p") σ := by
  set p := σ.vars "p" with hpdef
  set c := σ.vars "fc" with hcdef
  set st := σ.arrs "st" with hstdef
  have hl := len_lt_Bv x
  obtain ⟨hhh, hpx⟩ := t.hh
  have hd := t.drop
  have hlen := t.len
  simp only [Formula.encode, List.length_cons, List.cons_append] at hd hlen
  have g0 : x.getD p 0 = 7 := by have := drop_getD hd 0; simpa using this
  have g1 : x.getD (p + 1) 0 = y := by have := drop_getD hd 1; simpa using this
  have hstl := t.stl
  have hlf := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f)
  have hdisp : Spec (Bv x) (DC x p (pb pol) c rest.length st 7) dispatch
      (fun τ σ' => σ'.out = τ.out ++ [7, y] ∧
        AP x (p + 2) c (rest.length + 1) (st.set rest.length (pb pol)) σ') (Kd x + 24) :=
    dispatch_of (by omega) (by omega) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ _ _ _ _ => (qBr_spec 7 y g1 (by omega) (by omega) (pb_le pol) (by omega) (by omega)
        (by omega)).mono (by unfold Kd; omega))
  intro τ0 hτ0
  subst hτ0
  have hh1 : τ0.vars "h" = rest.length + 1 := by rw [hw.h]; simp
  obtain ⟨σ', hrun, τ, hτ, hQ1, hQ2⟩ := trBody_step hdisp t.top (pb_le pol) g0 (by omega) hpx
    (by omega) τ0 ⟨hw.a, rfl, rfl, hh1, rfl⟩
  have hdr : x.drop (p + 2) = pend ((pol, f) :: rest) := by
    have := drop_append (l₁ := [7, y]) hd
    simpa using this
  refine ⟨σ', hrun, ⟨(pol, f) :: rest, _, WS_next hw ((pol, f) :: rest) [7, y] _ _ _ hQ2
    (by rw [hQ1, hτ]) (by simp; omega) hdr (by simp; omega)
    (by rw [show ((pol, f) :: rest).length = rest.length + 1 by simp,
      take_set_one _ _ _ _ (by omega) t.stk]; simp) (by rw [trL_all]; rfl) (by rw [cntL_all])⟩, ?_⟩
  rw [hQ2.2.1]; omega

/-- **One turn of the walk.** -/
theorem trBody_spec (hct : ctot + 2 * x.length + 1 < Bv x) :
    Spec (Bv x) (fun σ => TI x T0 ctot out0 σ ∧
        (Cond.lt (L 0) (V "h")).evalB (Bv x) σ = some true) trBody
      (fun σ σ' => TI x T0 ctot out0 σ' ∧ x.length - σ'.vars "p" < x.length - σ.vars "p")
      (Kd x + 60) := by
  rintro σ ⟨⟨fs, E, hw⟩, hc⟩
  have hl := len_lt_Bv x
  have hfl := length_le_pend fs
  have hlen := hw.len
  have hhB : σ.vars "h" < Bv x := by rw [hw.h]; omega
  rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hhB)] at hc
  have h0 : 0 < σ.vars "h" := by simpa using hc
  rw [hw.h] at h0
  obtain ⟨⟨pol, f⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h0)
  have hst := hw.st
  simp only [List.length_cons, stackOf_cons] at hst
  obtain ⟨hstk, htop⟩ := stack_pop (f := ((pol, f) : Bool × Formula)) hst
  have hcnt := hw.cnt
  have t : Turn x ctot pol f rest (σ.vars "p") (σ.vars "fc") (σ.arrs "st") :=
    ⟨by rw [hw.drop]; rfl, by have := hw.len; simp at this; omega, hw.stl, hstk, htop,
      by simp at hcnt; omega⟩
  cases f with
  | rel i ys => exact turn_rel hw t σ rfl
  | setVar ys => exact turn_sv hw t σ rfl
  | eq u v => exact turn_eq hw t σ rfl
  | neg f => exact turn_neg hw t σ rfl
  | and f g => exact turn_and hw t σ rfl
  | or f g => exact turn_or hw t σ rfl
  | ex y f => exact turn_ex hw t σ rfl
  | all y f => exact turn_all hw t σ rfl

/-- **The walk**: at the end, the whole translation has been written. -/
theorem trLoop_spec (hct : ctot + 2 * x.length + 1 < Bv x) :
    Spec (Bv x) (TI x T0 ctot out0) (.while (.lt (L 0) (V "h")) trBody)
      (fun _ σ' => σ'.out = out0 ++ T0)
      ((1 + (Cond.lt (L 0) (V "h")).size + (Kd x + 60)) * x.length + 1 +
        (Cond.lt (L 0) (V "h")).size) := by
  have hl := len_lt_Bv x
  refine Spec.post (Spec.while_count (TI x T0 ctot out0) (fun σ => x.length - σ.vars "p")
    (Kd x + 60) (fun σ h => ?_) (trBody_spec hct) (fun _ h => h) (fun σ _ => ?_)) ?_
  · obtain ⟨fs, E, hw⟩ := h
    have hfl := length_le_pend fs
    have := hw.len
    exact evalB_condLt_isSome (evalB_lit (by omega)) (evalB_var (by rw [hw.h]; omega)) |>.imp
      fun v hv => hv.1
  · have : x.length - σ.vars "p" ≤ x.length := Nat.sub_le _ _
    have := Nat.mul_le_mul_left (1 + (Cond.lt (L 0) (V "h")).size + (Kd x + 60)) this
    omega
  · rintro σ σ' - ⟨⟨fs, E, hw⟩, hf⟩
    have hfl := length_le_pend fs
    have := hw.len
    rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hw.h]; omega))] at hf
    have h0 : σ'.vars "h" = 0 := by simpa using hf
    rw [hw.h] at h0
    have hfs : fs = [] := List.eq_nil_of_length_eq_zero h0
    subst hfs
    have := hw.tgt
    simp only [trL, List.append_nil] at this
    rw [hw.out, this]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWalk
