import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp

/-! # The walk over the formula

The invariant `WS`: the pending formulas `fs` are the rest of the code from `p`, their polarities
are on the stack (top last), the output so far `E` followed by the translations of the pending
formulas is the whole translation `T0`, and the fresh counter plus the fresh variables still to come
is `ctot`. One turn (`trBody_spec`) pops the first pending formula and handles its token. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PTr

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse

variable {x : List ℕ}

/-- The stack of polarities of the pending formulas, the first on top. -/
def stackOf (fs : List (Bool × Formula)) : List ℕ := (fs.map fun f => pb f.1).reverse

@[simp] theorem stackOf_cons (f : Bool × Formula) (fs : List (Bool × Formula)) :
    stackOf (f :: fs) = stackOf fs ++ [pb f.1] := by simp [stackOf]

@[simp] theorem length_stackOf (fs : List (Bool × Formula)) : (stackOf fs).length = fs.length := by
  simp [stackOf]

/-- **The invariant of the walk.** -/
structure WS (x T0 : List ℕ) (ctot : ℕ) (out0 : List ℕ) (fs : List (Bool × Formula)) (E : List ℕ)
    (σ : Env) : Prop where
  a : σ.arrs "a" = x
  h : σ.vars "h" = fs.length
  len : σ.vars "p" + (pend fs).length = x.length
  drop : x.drop (σ.vars "p") = pend fs
  stl : (σ.arrs "st").length = x.length + 2
  st : (σ.arrs "st").take fs.length = stackOf fs
  out : σ.out = out0 ++ E
  tgt : E ++ trL fs (σ.vars "fc") = T0
  cnt : σ.vars "fc" + cntL fs = ctot

/-- The invariant, with the pending formulas and the output hidden. -/
def TI (x T0 : List ℕ) (ctot : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  ∃ fs E, WS x T0 ctot out0 fs E σ

/-! ### Reading the code -/

theorem drop_getD {p : ℕ} {l : List ℕ} (h : x.drop p = l) (j : ℕ) :
    x.getD (p + j) 0 = l.getD j 0 := by
  rw [← h, getD_drop]

theorem drop_append {p : ℕ} {l₁ l₂ : List ℕ} (h : x.drop p = l₁ ++ l₂) :
    x.drop (p + l₁.length) = l₂ := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ### The stack -/

theorem take_set_succ (l : List ℕ) (k v : ℕ) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  rw [List.set_eq_take_append_cons_drop, if_pos hk]
  have hl : (l.take k).length = k := by simp; omega
  rw [List.take_append, hl, Nat.add_sub_cancel_left]
  simp [List.take_of_length_le (show (l.take k).length ≤ k + 1 by omega)]

theorem stack_pop {st : List ℕ} {f : Bool × Formula} {fs : List (Bool × Formula)}
    (h : st.take (fs.length + 1) = stackOf fs ++ [pb f.1]) :
    st.take fs.length = stackOf fs ∧ st.getD fs.length 0 = pb f.1 := by
  have hl : (st.take (fs.length + 1)).length = fs.length + 1 := by rw [h]; simp
  constructor
  · have := congrArg (List.take fs.length) h
    rw [List.take_take, min_eq_left (by omega), List.take_left' (by simp)] at this
    exact this
  · have hlt : fs.length < st.length := by simp at hl; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have := congrArg (fun l => l[fs.length]?) h
    simp only [List.getElem?_take, List.getElem?_eq_getElem hlt] at this
    rw [if_pos (by omega)] at this
    rw [List.getElem?_append_right (by simp)] at this
    simpa using this

/-! ### One turn, given the dispatch -/

set_option maxHeartbeats 4000000 in
theorem trBody_step {p c hh pl tag : ℕ} {st : List ℕ} {Q : Env → Env → Prop}
    (hdisp : Spec (Bv x) (DC x p pl c hh st tag) dispatch Q (Kd x + 24))
    (hpl : st.getD hh 0 = pl) (hpl1 : pl ≤ 1) (htag : x.getD p 0 = tag) (hst : hh < st.length)
    (hp : p < x.length) (hb : hh + 1 < Bv x) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "p" = p ∧ σ.vars "fc" = c ∧
        σ.vars "h" = hh + 1 ∧ σ.arrs "st" = st) trBody
      (fun σ σ' => ∃ τ, τ.out = σ.out ∧ Q τ σ') (Kd x + 60) := by
  have hl := len_lt_Bv x
  have hpl' : pl < Bv x := by omega
  have htag' : tag < Bv x := by rw [← htag]; exact getD_lt_Bv x p
  unfold trBody
  run_vcg [hdisp]
  all_goals
    (try simp only [DC, AC, Env.setVar] at *)
  all_goals first
    | (find_hyp hQ : Q _ _
       refine ⟨_, ?_, hQ⟩
       rfl)
    | (simp_all; done)
    | (simp_all; try omega)
  all_goals done

/-! ### The new invariant after one turn -/

theorem length_le_pend : ∀ fs : List (Bool × Formula), fs.length ≤ (pend fs).length
  | [] => le_refl _
  | f :: fs => by
    have := length_le_pend fs
    have := List.length_pos_iff.mpr (Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil f.2)
    simp; omega

theorem WS_next {T0 : List ℕ} {ctot : ℕ} {out0 : List ℕ} {fs : List (Bool × Formula)} {E : List ℕ}
    {σ σ' : Env} (hw : WS x T0 ctot out0 fs E σ) (fs' : List (Bool × Formula)) (piece : List ℕ)
    (p' c' : ℕ) (st' : List ℕ) (hAP : AP x p' c' fs'.length st' σ') (hout : σ'.out = σ.out ++ piece)
    (hlen : p' + (pend fs').length = x.length) (hdrop : x.drop p' = pend fs')
    (hstl : st'.length = x.length + 2) (hst : st'.take fs'.length = stackOf fs')
    (htgt : piece ++ trL fs' c' = trL fs (σ.vars "fc")) (hcnt : c' + cntL fs' = σ.vars "fc" + cntL fs) :
    WS x T0 ctot out0 fs' (E ++ piece) σ' := by
  obtain ⟨ha, hp, hc, hh, hst'⟩ := hAP
  refine ⟨ha, hh, by rw [hp]; exact hlen, by rw [hp]; exact hdrop, by rw [hst']; exact hstl,
    by rw [hst']; exact hst, by rw [hout, hw.out, List.append_assoc], ?_, ?_⟩
  · rw [hc, List.append_assoc, htgt, hw.tgt]
  · rw [hc, hcnt, hw.cnt]

theorem take_set_two (l : List ℕ) (k v : ℕ) (hk : k + 1 < l.length) :
    ((l.set k v).set (k + 1) v).take (k + 2) = l.take k ++ [v, v] := by
  rw [show k + 2 = (k + 1) + 1 by ring, take_set_succ _ _ _ (by simp; omega),
    take_set_succ _ _ _ (by omega)]
  simp

theorem take_set_one (l s : List ℕ) (k v : ℕ) (hk : k < l.length) (h : l.take k = s) :
    (l.set k v).take (k + 1) = s ++ [v] := by
  rw [take_set_succ _ _ _ hk, h]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PTr
