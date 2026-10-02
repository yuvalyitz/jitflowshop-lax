import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.SortList
import Lax496464Proofs.Ram.ListUtil
import Mathlib.Data.Nat.Log

/-!
# Bottom-Up Merge Sort on the Machine

Two arrays, `SA` holding the sequence and `SB` a buffer. A pass merges neighbouring runs of
width `w` from `SA` into `SB` and copies `SB` back; `⌈log₂ n⌉` passes sort. The comparison
of two entries is a hook, `Cmp`, so that the same sort orders jobs by a key held in other arrays.
-/

namespace Lax496464Proofs.Ram.Sort

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.SortList Lax496464Proofs.Ram.ListUtil

open Classical

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- The sort's own scalars, apart from the comparison result `sc`. -/
def SV : List String :=
  ["sn", "sw", "slo", "smid", "shi", "si", "sj", "sk", "sx", "sy", "stl", "spc", "snp"]

/-- The entries `i` to `j - 1` of a list. -/
def seg (a : List ℕ) (i j : ℕ) : List ℕ := (a.take j).drop i

theorem seg_nil {a : List ℕ} {i j : ℕ} (h : j ≤ i) : seg a i j = [] := by
  simp only [seg, List.drop_eq_nil_iff, List.length_take]; omega

theorem seg_cons {a : List ℕ} {i j : ℕ} (h : i < j) (hj : j ≤ a.length) :
    seg a i j = a.getD i 0 :: seg a (i + 1) j := by
  have hl : i < (a.take j).length := by simp only [List.length_take]; omega
  rw [seg, List.drop_eq_getElem_cons hl, List.getElem_take]
  simp [seg, List.getD_eq_getElem?_getD, show i < a.length by omega]

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- What a comparison hook owes. -/
structure Cmp (B : ℕ) (r : ℕ → ℕ → Prop) (Base : Env → Prop) where
  com : Com
  cost : ℕ
  /-- The comparison never writes the pass counters. -/
  free : "snp" ∉ com.wvars ∧ "spc" ∉ com.wvars
  /-- The entries the comparison may be applied to. -/
  good : ℕ → Prop
  spec : ∀ a b : ℕ, a < B → b < B → good a → good b →
    Spec B (fun σ => Base σ ∧ σ.vars "sx" = a ∧ σ.vars "sy" = b) com
    (fun σ σ' => Base σ' ∧ σ'.vars "sc" = (if r a b then 1 else 0) ∧
      (∀ y, y ∈ SV → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
      σ'.out = σ.out) cost

/-- What the state outside the sort must survive: the sort's scalars and its two arrays. -/
def BaseOK (Base : Env → Prop) : Prop :=
  ∀ σ σ' : Env, Base σ → (∀ y, y ∉ "sc" :: SV → σ'.vars y = σ.vars y) →
    (∀ a, a ≠ "SA" → a ≠ "SB" → σ'.arrs a = σ.arrs a) → Base σ'

/-- Take the entry of the left run? -/
def TL (r : ℕ → ℕ → Prop) (A : List ℕ) (i j mid hi : ℕ) : Prop :=
  i < mid ∧ (j = hi ∨ r (A.getD i 0) (A.getD j 0))

/-- Decide which run the next entry comes from. -/
def tlSetup (cmp : Com) : Com :=
  .ite (.lt (V "si") (V "smid"))
    (.ite (.lt (V "sj") (V "shi"))
      (.seq (.assign "sx" (.get "SA" (V "si")))
        (.seq (.assign "sy" (.get "SA" (V "sj")))
          (.seq cmp (.assign "stl" (V "sc")))))
      (.assign "stl" (.lit 1)))
    (.assign "stl" (.lit 0))

theorem tlSetup_spec {B : ℕ} {r : ℕ → ℕ → Prop} {Base : Env → Prop} (C : Cmp B r Base)
    (hBO : BaseOK Base) (hB : 1 < B) (A : List ℕ) (i j mid hi : ℕ) (hj : j ≤ hi) (hiB : i < B) (hjB : j < B)
    (hmidB : mid < B) (hhiB : hi < B) (hiA : i < mid → i < A.length)
    (hjA : j < hi → j < A.length) (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => Base σ ∧ σ.vars "si" = i ∧ σ.vars "sj" = j ∧ σ.vars "smid" = mid ∧
        σ.vars "shi" = hi ∧ σ.arrs "SA" = A) (tlSetup C.com)
      (fun σ σ' => Base σ' ∧ σ'.vars "stl" = (if TL r A i j mid hi then 1 else 0) ∧
        (∀ y, y ∈ SV → y ≠ "stl" → y ≠ "sx" → y ≠ "sy" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (20 + C.cost) := by
  have hx : i < mid → A.getD i 0 < B := fun h => by
    have := hiA h
    exact (hAB _ (by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this)).1
  have hy : j < hi → A.getD j 0 < B := fun h => by
    have := hjA h
    exact (hAB _ (by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this)).1
  have hgx : i < mid → C.good (A.getD i 0) := fun h => by
    have := hiA h
    exact (hAB _ (by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this)).2
  have hgy : j < hi → C.good (A.getD j 0) := fun h => by
    have := hjA h
    exact (hAB _ (by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this)).2
  refine Spec.of_exists fun σ ⟨hBase, hi', hj', hmid', hhi', hSA⟩ => ?_
  have hvi : (V "si").evalB B σ = some i := hi' ▸ evalB_var (by rw [hi']; exact hiB)
  have hvj : (V "sj").evalB B σ = some j := hj' ▸ evalB_var (by rw [hj']; exact hjB)
  have hvm : (V "smid").evalB B σ = some mid := hmid' ▸ evalB_var (by rw [hmid']; exact hmidB)
  have hvh : (V "shi").evalB B σ = some hi := hhi' ▸ evalB_var (by rw [hhi']; exact hhiB)
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  by_cases him : i < mid
  · have hc1 : (Cond.lt (V "si") (V "smid")).evalB B σ = some true := by
      rw [evalB_condLt hvi hvm]; simp [him]
    by_cases hjh : j < hi
    · have hc2 : (Cond.lt (V "sj") (V "shi")).evalB B σ = some true := by
        rw [evalB_condLt hvj hvh]; simp [hjh]
      have hxA : (Expr.get "SA" (V "si")).evalB B σ = some (A.getD i 0) := by
        have := RunStep.eval_get B σ "SA" (V "si") i hvi (by rw [hSA]; exact hiA him)
          (by rw [hSA]; exact hx him)
        rwa [hSA] at this
      have r1 := Run.assign (B := B) (σ := σ) (x := "sx") (e := .get "SA" (V "si"))
        (v := A.getD i 0) hxA
      set σ1 : Env := σ.setVar "sx" (A.getD i 0) with hσ1
      have hyA : (Expr.get "SA" (V "sj")).evalB B σ1 = some (A.getD j 0) := by
        have hvj1 : (V "sj").evalB B σ1 = some j := by
          have : σ1.vars "sj" = j := by simp [hσ1, hj']
          exact this ▸ evalB_var (by rw [this]; exact hjB)
        have := RunStep.eval_get B σ1 "SA" (V "sj") j hvj1 (by simp [hσ1, hSA]; exact hjA hjh)
          (by simp [hσ1, hSA]; exact hy hjh)
        simpa [hσ1, hSA] using this
      have r2 := Run.assign (B := B) (σ := σ1) (x := "sy") (e := .get "SA" (V "sj"))
        (v := A.getD j 0) hyA
      set σ2 : Env := σ1.setVar "sy" (A.getD j 0) with hσ2
      have hB2 : Base σ2 := hBO σ σ2 hBase (fun y hy => by
          have h1 : y ≠ "sx" := by rintro rfl; simp [SV] at hy
          have h2 : y ≠ "sy" := by rintro rfl; simp [SV] at hy
          simp [hσ2, hσ1, h1, h2]) (fun a _ _ => by simp [hσ2, hσ1])
      obtain ⟨σ3, hr3, hBase3, hsc3, hfr3, harr3, hinp3, hout3⟩ :=
        (C.spec (A.getD i 0) (A.getD j 0) (hx him) (hy hjh) (hgx him) (hgy hjh)).run (σ := σ2)
          ⟨hB2, by simp [hσ2, hσ1], by simp [hσ2]⟩
      have hscB : σ3.vars "sc" < B := by
        rw [hsc3]; split_ifs <;> omega
      have r4 := Run.assign (B := B) (σ := σ3) (x := "stl") (e := V "sc")
        (v := σ3.vars "sc") (evalB_var hscB)
      refine ⟨_, _, Run.ite_true hc1 (Run.ite_true hc2 (r1.seq (r2.seq (hr3.seq r4)))), ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Expr.size, Cond.size]; omega
      · exact hBO σ3 _ hBase3 (fun y hy => by
          have h1 : y ≠ "stl" := by rintro rfl; simp [SV] at hy
          simp [h1]) (fun a _ _ => by simp [harr3, hσ2, hσ1])
      · simp only [vars_setVar, if_true, hsc3]
        have : TL r A i j mid hi ↔ r (A.getD i 0) (A.getD j 0) := by
          simp [TL, him, hjh.ne]
        by_cases hr : r (A.getD i 0) (A.getD j 0)
        · rw [if_pos hr, if_pos (this.mpr hr)]
        · rw [if_neg hr, if_neg (fun h => hr (this.mp h))]
      · intro y hy h1 h2 h3
        simp only [vars_setVar]
        rw [if_neg h1, hfr3 y hy]
        simp [hσ2, hσ1, h2, h3]
      · simp [harr3, hσ2, hσ1]
      · simp [hinp3, hσ2, hσ1]
      · simp [hout3, hσ2, hσ1]
    · have hc2 : (Cond.lt (V "sj") (V "shi")).evalB B σ = some false := by
        rw [evalB_condLt hvj hvh]; simp [hjh]
      have r1 := Run.assign (B := B) (σ := σ) (x := "stl") (e := .lit 1) (v := 1) hl1
      refine ⟨_, _, Run.ite_true hc1 (Run.ite_false hc2 r1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Expr.size, Cond.size]; omega
      · exact hBO σ _ hBase (fun y hy => by
          have h1 : y ≠ "stl" := by rintro rfl; simp [SV] at hy
          simp [h1]) (fun a _ _ => rfl)
      · have : TL r A i j mid hi := ⟨him, Or.inl (by omega)⟩
        simp [this]
      · intro y _ h1 _ _; simp [h1]
      · rfl
      · rfl
      · rfl
  · have hc1 : (Cond.lt (V "si") (V "smid")).evalB B σ = some false := by
      rw [evalB_condLt hvi hvm]; simp [him]
    have r1 := Run.assign (B := B) (σ := σ) (x := "stl") (e := .lit 0) (v := 0) hl0
    refine ⟨_, _, Run.ite_false hc1 r1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]; omega
    · exact hBO σ _ hBase (fun y hy => by
        have h1 : y ≠ "stl" := by rintro rfl; simp [SV] at hy
        simp [h1]) (fun a _ _ => rfl)
    · have : ¬ TL r A i j mid hi := fun h => him h.1
      simp [this]
    · intro y _ h1 _ _; simp [h1]
    · rfl
    · rfl
    · rfl

/-! ## The merge, one entry at a time -/

variable (r : ℕ → ℕ → Prop) [DecidableRel r]

theorem merge_unfold_left {A : List ℕ} {i j mid hi : ℕ} (hm : mid ≤ A.length) (hh : hi ≤ A.length)
    (hj : j ≤ hi) (h : TL r A i j mid hi) :
    (seg A i mid).merge (seg A j hi) (cmp r) =
      A.getD i 0 :: (seg A (i + 1) mid).merge (seg A j hi) (cmp r) := by
  obtain ⟨him, hj'⟩ := h
  rw [seg_cons him hm]
  by_cases hjh : j = hi
  · subst hjh; rw [seg_nil le_rfl]; simp
  · have hjlt : j < hi := by omega
    have hr : r (A.getD i 0) (A.getD j 0) := by rcases hj' with h | h; exact absurd h hjh; exact h
    rw [seg_cons hjlt hh, List.cons_merge_cons]
    have hc : SortList.cmp r (A.getD i 0) (A.getD j 0) = true := decide_eq_true hr
    rw [if_pos hc]

theorem merge_unfold_right {A : List ℕ} {i j mid hi : ℕ} (hm : mid ≤ A.length) (hh : hi ≤ A.length)
    (hj : j < hi) (h : ¬ TL r A i j mid hi) :
    (seg A i mid).merge (seg A j hi) (cmp r) =
      A.getD j 0 :: (seg A i mid).merge (seg A (j + 1) hi) (cmp r) := by
  rw [seg_cons hj hh]
  by_cases him : i < mid
  · have hr : ¬ r (A.getD i 0) (A.getD j 0) := by
      intro hr; exact h ⟨him, Or.inr hr⟩
    rw [seg_cons him hm, List.cons_merge_cons]
    have hc : SortList.cmp r (A.getD i 0) (A.getD j 0) = false := decide_eq_false hr
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
  · rw [seg_nil (by omega)]; simp

theorem seg_set_succ (L : List ℕ) {lo k v : ℕ} (hlo : lo ≤ k) (hk : k < L.length) :
    seg (L.set k v) lo (k + 1) = seg L lo k ++ [v] := by
  have hlen : (L.take k).length = k := by simp; omega
  simp only [seg]
  rw [List.set_eq_take_append_cons_drop, if_pos hk]
  have : (L.take k ++ v :: L.drop (k + 1)).take (k + 1) = L.take k ++ [v] := by
    rw [List.take_append]
    simp [hlen]
  rw [this, List.drop_append_of_le_length (by omega)]

/-- Store the next entry of the merge, from the run the flag names, and move on. -/
def moveK : Com :=
  .seq (.ite (.eq (V "stl") (.lit 1))
      (.seq (.store "SB" (V "sk") (.get "SA" (V "si"))) (bump "si"))
      (.seq (.store "SB" (V "sk") (.get "SA" (V "sj"))) (bump "sj")))
    (bump "sk")

/-- The invariant of the merge of `[lo, mid)` and `[mid, hi)` of `A` into the buffer. -/
def MI (lo mid hi : ℕ) (A SB0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "SA" = A ∧ σ.vars "smid" = mid ∧ σ.vars "shi" = hi ∧
  lo ≤ σ.vars "si" ∧ σ.vars "si" ≤ mid ∧ mid ≤ σ.vars "sj" ∧ σ.vars "sj" ≤ hi ∧
  σ.vars "sk" = σ.vars "si" + σ.vars "sj" - mid ∧
  (σ.arrs "SB").length = SB0.length ∧ (σ.arrs "SB").take lo = SB0.take lo ∧
  seg (σ.arrs "SB") lo (σ.vars "sk") ++
      (seg A (σ.vars "si") mid).merge (seg A (σ.vars "sj") hi) (SortList.cmp r) =
    (seg A lo mid).merge (seg A mid hi) (SortList.cmp r)

theorem moveK_spec {B : ℕ} {Base : Env → Prop} (hBO : BaseOK Base) (hB : 1 < B)
    (lo mid hi : ℕ) (A SB0 : List ℕ) (_hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hhA : hi ≤ A.length) (hhS : hi ≤ SB0.length) (hhiB : hi < B) (hAB : ∀ v ∈ A, v < B) :
    Spec B (fun σ => (Base σ ∧ MI r lo mid hi A SB0 σ ∧
        σ.vars "stl" = (if TL r A (σ.vars "si") (σ.vars "sj") mid hi then 1 else 0)) ∧
        σ.vars "sk" < hi) moveK
      (fun σ σ' => Base σ' ∧ MI r lo mid hi A SB0 σ' ∧ σ'.vars "sk" = σ.vars "sk" + 1 ∧
        σ'.vars "sn" = σ.vars "sn" ∧ σ'.vars "sw" = σ.vars "sw" ∧
        σ'.vars "slo" = σ.vars "slo") 40 := by
  have hgetB : ∀ t, t < A.length → A.getD t 0 < B := fun t ht => by
    exact hAB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  refine Spec.of_exists fun σ ⟨⟨hBase, hMI, hstl⟩, hkh⟩ => ?_
  obtain ⟨hSA, hmid, hhi, hlo, him, hmj, hjh, hk, hSBl, hSBt, hinv⟩ := hMI
  have hlk : lo ≤ σ.vars "sk" := by omega
  have hkS : σ.vars "sk" < (σ.arrs "SB").length := by omega
  have hvk : (V "sk").evalB B σ = some (σ.vars "sk") := evalB_var (by omega)
  have hvstl : (V "stl").evalB B σ = some (σ.vars "stl") := evalB_var (by
    rw [hstl]; split_ifs <;> omega)
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  have hlit1 : ∀ σ' : Env, (Expr.lit 1).evalB B σ' = some 1 := fun _ => evalB_lit hB
  by_cases hTL : TL r A (σ.vars "si") (σ.vars "sj") mid hi
  · have hst : σ.vars "stl" = 1 := by rw [hstl, if_pos hTL]
    have hc : (Cond.eq (V "stl") (.lit 1)).evalB B σ = some true := by
      rw [evalB_condEq hvstl hl1, hst]; rfl
    have hiA : σ.vars "si" < A.length := by have := hTL.1; omega
    have hvi : (V "si").evalB B σ = some (σ.vars "si") := evalB_var (by omega)
    have hg : (Expr.get "SA" (V "si")).evalB B σ = some (A.getD (σ.vars "si") 0) := by
      have := RunStep.eval_get B σ "SA" (V "si") (σ.vars "si") hvi (by rw [hSA]; exact hiA)
        (by rw [hSA]; exact hgetB _ hiA)
      rwa [hSA] at this
    have r1 := Run.store (B := B) (σ := σ) (a := "SB") (i := V "sk") (e := .get "SA" (V "si"))
      (idx := σ.vars "sk") (v := A.getD (σ.vars "si") 0) hvk hg hkS
    set σa : Env := σ.setArr "SB" (σ.vars "sk") (A.getD (σ.vars "si") 0) with hσa
    have hvia : (V "si").evalB B σa = some (σ.vars "si") := by
      have : σa.vars "si" = σ.vars "si" := by simp [hσa]
      exact this ▸ evalB_var (by rw [this]; omega)
    have r2 := Run.assign (B := B) (σ := σa) (x := "si") (e := .bin .add (V "si") (.lit 1))
      (v := σ.vars "si" + 1) (evalB_bin hvia (hlit1 σa) (by show σ.vars "si" + 1 < B; omega))
    set σb : Env := σa.setVar "si" (σ.vars "si" + 1) with hσb
    have hvkb : (V "sk").evalB B σb = some (σ.vars "sk") := by
      have : σb.vars "sk" = σ.vars "sk" := by simp [hσb, hσa]
      exact this ▸ evalB_var (by rw [this]; omega)
    have r3 := Run.assign (B := B) (σ := σb) (x := "sk") (e := .bin .add (V "sk") (.lit 1))
      (v := σ.vars "sk" + 1) (evalB_bin hvkb (hlit1 σb) (by show σ.vars "sk" + 1 < B; omega))
    refine ⟨_, _, Run.seq (Run.ite_true hc (r1.seq r2)) r3 |>.mono ?_, le_rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]; omega
    · exact hBO σ _ hBase (fun y hy => by
        have h1 : y ≠ "si" := by rintro rfl; simp [SV] at hy
        have h2 : y ≠ "sk" := by rintro rfl; simp [SV] at hy
        simp [hσb, hσa, h1, h2]) (fun a h1 h2 => by simp [hσb, hσa, h2])
    · have hTL1 := hTL.1
      refine ⟨by simp [hσb, hσa, hSA], by simp [hσb, hσa, hmid], by simp [hσb, hσa, hhi],
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa, hSBl]
      · simp only [hσb, hσa, arrs_setVar, arrs_setArr, if_true]
        rw [List.take_set_of_le hlk]; exact hSBt
      · simp only [hσb, hσa, arrs_setVar, arrs_setArr, vars_setVar, vars_setArr, if_true]
        have hs1 : ("sk" = "si") = False := by decide
        have hs2 : ("sj" = "sk") = False := by decide
        have hs3 : ("sj" = "si") = False := by decide
        have hs4 : ("si" = "sk") = False := by decide
        simp only [hs2, hs3, hs4, if_false]
        have hu := merge_unfold_left r (by omega : mid ≤ A.length) hhA hjh hTL
        rw [seg_set_succ _ hlk hkS, List.append_assoc, List.singleton_append,
          ← hu]
        exact hinv
    · simp [hσb, hσa]
    · simp [hσb, hσa]
  · have hst : σ.vars "stl" = 0 := by rw [hstl, if_neg hTL]
    have hc : (Cond.eq (V "stl") (.lit 1)).evalB B σ = some false := by
      rw [evalB_condEq hvstl hl1, hst]; rfl
    have hjlt : σ.vars "sj" < hi := by
      by_contra hcon
      by_cases him2 : σ.vars "si" < mid
      · exact hTL ⟨him2, Or.inl (by omega)⟩
      · omega
    have hjA : σ.vars "sj" < A.length := by omega
    have hvj : (V "sj").evalB B σ = some (σ.vars "sj") := evalB_var (by omega)
    have hg : (Expr.get "SA" (V "sj")).evalB B σ = some (A.getD (σ.vars "sj") 0) := by
      have := RunStep.eval_get B σ "SA" (V "sj") (σ.vars "sj") hvj (by rw [hSA]; exact hjA)
        (by rw [hSA]; exact hgetB _ hjA)
      rwa [hSA] at this
    have r1 := Run.store (B := B) (σ := σ) (a := "SB") (i := V "sk") (e := .get "SA" (V "sj"))
      (idx := σ.vars "sk") (v := A.getD (σ.vars "sj") 0) hvk hg hkS
    set σa : Env := σ.setArr "SB" (σ.vars "sk") (A.getD (σ.vars "sj") 0) with hσa
    have hvja : (V "sj").evalB B σa = some (σ.vars "sj") := by
      have : σa.vars "sj" = σ.vars "sj" := by simp [hσa]
      exact this ▸ evalB_var (by rw [this]; omega)
    have r2 := Run.assign (B := B) (σ := σa) (x := "sj") (e := .bin .add (V "sj") (.lit 1))
      (v := σ.vars "sj" + 1) (evalB_bin hvja (hlit1 σa) (by show σ.vars "sj" + 1 < B; omega))
    set σb : Env := σa.setVar "sj" (σ.vars "sj" + 1) with hσb
    have hvkb : (V "sk").evalB B σb = some (σ.vars "sk") := by
      have : σb.vars "sk" = σ.vars "sk" := by simp [hσb, hσa]
      exact this ▸ evalB_var (by rw [this]; omega)
    have r3 := Run.assign (B := B) (σ := σb) (x := "sk") (e := .bin .add (V "sk") (.lit 1))
      (v := σ.vars "sk" + 1) (evalB_bin hvkb (hlit1 σb) (by show σ.vars "sk" + 1 < B; omega))
    refine ⟨_, _, Run.seq (Run.ite_false hc (r1.seq r2)) r3 |>.mono ?_, le_rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]; omega
    · exact hBO σ _ hBase (fun y hy => by
        have h1 : y ≠ "sj" := by rintro rfl; simp [SV] at hy
        have h2 : y ≠ "sk" := by rintro rfl; simp [SV] at hy
        simp [hσb, hσa, h1, h2]) (fun a h1 h2 => by simp [hσb, hσa, h2])
    · refine ⟨by simp [hσb, hσa, hSA], by simp [hσb, hσa, hmid], by simp [hσb, hσa, hhi],
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa]; omega
      · simp [hσb, hσa, hSBl]
      · simp only [hσb, hσa, arrs_setVar, arrs_setArr, if_true]
        rw [List.take_set_of_le hlk]; exact hSBt
      · simp only [hσb, hσa, arrs_setVar, arrs_setArr, vars_setVar, vars_setArr, if_true]
        have hs2 : ("sj" = "sk") = False := by decide
        have hs3 : ("si" = "sk") = False := by decide
        have hs4 : ("si" = "sj") = False := by decide
        have hs5 : ("sk" = "sj") = False := by decide
        simp only [hs2, hs3, hs4, if_false]
        have hu := merge_unfold_right r (by omega : mid ≤ A.length) hhA hjlt hTL
        rw [seg_set_succ _ hlk hkS, List.append_assoc, List.singleton_append, ← hu]
        exact hinv
    · simp [hσb, hσa]
    · simp [hσb, hσa]

/-- One step of the merge. -/
def mergeBody (cmp : Com) : Com := .seq (tlSetup cmp) moveK

/-- The merge of the two runs into the buffer. -/
def mergeLoop (cmp : Com) : Com := .while (.lt (V "sk") (V "shi")) (mergeBody cmp)

theorem mergeBody_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) (lo mid hi : ℕ) (A SB0 : List ℕ) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hhA : hi ≤ A.length) (hhS : hi ≤ SB0.length) (hhiB : hi < B) (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => (Base σ ∧ MI r lo mid hi A SB0 σ) ∧ σ.vars "sk" < hi) (mergeBody C.com)
      (fun σ σ' => (Base σ' ∧ MI r lo mid hi A SB0 σ') ∧ σ'.vars "sk" = σ.vars "sk" + 1 ∧
        σ'.vars "sn" = σ.vars "sn" ∧ σ'.vars "sw" = σ.vars "sw" ∧
        σ'.vars "slo" = σ.vars "slo")
      (20 + C.cost + 40) := by
  refine Spec.of_exists fun σ ⟨⟨hBase, hMI⟩, hkh⟩ => ?_
  have hMI' := hMI
  obtain ⟨hSA, hmid, hhi, hlo, him, hmj, hjh, hk, hSBl, hSBt, hinv⟩ := hMI'
  obtain ⟨σ1, hr1, hBase1, hstl1, hfr1, harr1, hinp1, hout1⟩ :=
    (tlSetup_spec C hBO hB A (σ.vars "si") (σ.vars "sj") mid hi hjh (by omega) (by omega)
      (by omega) hhiB (fun h => by omega) (fun h => by omega) hAB).run
      ⟨hBase, rfl, rfl, hmid, hhi, hSA⟩
  have hMI1 : MI r lo mid hi A SB0 σ1 := by
    have e := fun y (hy : y ∈ SV) (h1 : y ≠ "stl") (h2 : y ≠ "sx") (h3 : y ≠ "sy") =>
      hfr1 y hy h1 h2 h3
    refine ⟨by rw [harr1]; exact hSA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e "smid" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hmid
    · rw [e "shi" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hhi
    · rw [e "si" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hlo
    · rw [e "si" (by simp [SV]) (by decide) (by decide) (by decide)]; exact him
    · rw [e "sj" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hmj
    · rw [e "sj" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hjh
    · rw [e "sk" (by simp [SV]) (by decide) (by decide) (by decide),
        e "si" (by simp [SV]) (by decide) (by decide) (by decide),
        e "sj" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hk
    · rw [harr1]; exact hSBl
    · rw [harr1]; exact hSBt
    · rw [harr1, e "si" (by simp [SV]) (by decide) (by decide) (by decide),
        e "sj" (by simp [SV]) (by decide) (by decide) (by decide),
        e "sk" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hinv
  have hstl1' : σ1.vars "stl" = (if TL r A (σ1.vars "si") (σ1.vars "sj") mid hi then 1 else 0) := by
    rw [hstl1, hfr1 "si" (by simp [SV]) (by decide) (by decide) (by decide),
      hfr1 "sj" (by simp [SV]) (by decide) (by decide) (by decide)]
  have hk1 : σ1.vars "sk" < hi := by
    rw [hfr1 "sk" (by simp [SV]) (by decide) (by decide) (by decide)]; exact hkh
  obtain ⟨σ2, hr2, hBase2, hMI2, hk2, hn2, hw2, hl2⟩ :=
    (moveK_spec r hBO hB lo mid hi A SB0 hlm hmh hhA hhS hhiB (fun v hv => (hAB v hv).1)).run
      ⟨⟨hBase1, hMI1, hstl1'⟩, hk1⟩
  refine ⟨σ2, _, (hr1.seq hr2).mono ?_, le_rfl, ⟨hBase2, hMI2⟩, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hk2, hfr1 "sk" (by simp [SV]) (by decide) (by decide) (by decide)]
  · rw [hn2, hfr1 "sn" (by simp [SV]) (by decide) (by decide) (by decide)]
  · rw [hw2, hfr1 "sw" (by simp [SV]) (by decide) (by decide) (by decide)]
  · rw [hl2, hfr1 "slo" (by simp [SV]) (by decide) (by decide) (by decide)]

theorem mergeLoop_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) (lo mid hi : ℕ) (A SB0 : List ℕ) (n0 w0 l0 : ℕ) (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hhA : hi ≤ A.length) (hhS : hi ≤ SB0.length) (hhiB : hi < B) (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => Base σ ∧ MI r lo mid hi A SB0 σ ∧ σ.vars "sk" = lo ∧ σ.vars "sn" = n0 ∧
        σ.vars "sw" = w0 ∧ σ.vars "slo" = l0) (mergeLoop C.com)
      (fun _ σ' => (Base σ' ∧ MI r lo mid hi A SB0 σ') ∧ σ'.vars "sk" = hi ∧
        σ'.vars "sn" = n0 ∧ σ'.vars "sw" = w0 ∧ σ'.vars "slo" = l0)
      ((20 + C.cost + 40 + 4) * (hi - lo) + 4) := by
  have hbody : Spec B (fun σ => (Base σ ∧ MI r lo mid hi A SB0 σ ∧ σ.vars "sn" = n0 ∧
        σ.vars "sw" = w0 ∧ σ.vars "slo" = l0) ∧ σ.vars "sk" < hi) (mergeBody C.com)
      (fun σ σ' => (Base σ' ∧ MI r lo mid hi A SB0 σ' ∧ σ'.vars "sn" = n0 ∧
        σ'.vars "sw" = w0 ∧ σ'.vars "slo" = l0) ∧ σ'.vars "sk" = σ.vars "sk" + 1)
      (20 + C.cost + 40) := by
    refine Spec.of_exists fun σ ⟨⟨hBase, hMI, hn, hw, hl⟩, hkh⟩ => ?_
    obtain ⟨σ', hr, ⟨hb', hm'⟩, hk', hn', hw', hl'⟩ :=
      (mergeBody_spec r C hBO hB lo mid hi A SB0 hlm hmh hhA hhS hhiB hAB).run
        ⟨⟨hBase, hMI⟩, hkh⟩
    exact ⟨σ', _, hr, le_rfl, ⟨hb', hm', by rw [hn', hn], by rw [hw', hw], by rw [hl', hl]⟩, hk'⟩
  have := Spec.forRange (B := B)
    (P := fun σ => Base σ ∧ MI r lo mid hi A SB0 σ ∧ σ.vars "sk" = lo ∧ σ.vars "sn" = n0 ∧
      σ.vars "sw" = w0 ∧ σ.vars "slo" = l0)
    (c := mergeBody C.com) "sk" "shi"
    (fun σ => Base σ ∧ MI r lo mid hi A SB0 σ ∧ σ.vars "sn" = n0 ∧ σ.vars "sw" = w0 ∧
      σ.vars "slo" = l0) hi
    (20 + C.cost + 40) ((20 + C.cost + 40 + 4) * (hi - lo) + 4)
    (fun σ h => by obtain ⟨-, -, -, -, h1, h2, h3, hk, -⟩ := h.2.1; omega)
    (fun σ h => by rw [h.2.1.2.2.1]; exact hhiB)
    (fun σ h => h.2.1.2.2.1) (fun σ h => by obtain ⟨-, -, -, -, h1, h2, h3, hk, -⟩ := h.2.1; omega)
    hbody
    (fun σ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) (fun σ h => by rw [h.2.2.1])
  refine this.post (fun σ σ' _ h => ?_)
  exact ⟨⟨h.1.1, h.1.2.1⟩, h.2, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩

/-! ## One block: the pair of runs starting at `slo` -/

theorem MI_final {lo mid hi : ℕ} {A SB0 : List ℕ} {σ : Env}
    (h : MI r lo mid hi A SB0 σ) (hk : σ.vars "sk" = hi) :
    seg (σ.arrs "SB") lo hi = (seg A lo mid).merge (seg A mid hi) (SortList.cmp r) := by
  obtain ⟨-, -, -, -, him, hmj, hjh, hkk, -, -, hinv⟩ := h
  have hi' : σ.vars "si" = mid := by omega
  have hj' : σ.vars "sj" = hi := by omega
  rw [hi', hj', hk, seg_nil le_rfl, seg_nil le_rfl] at hinv
  simpa using hinv

/-- Set up the next two runs: `[slo, smid)` and `[smid, shi)`, clipped to the array, and the
three cursors of the merge. -/
def blockSetup : Com :=
  .seq (.assign "smid" (.bin .add (V "slo") (V "sw")))
    (.seq (.ite (.lt (V "sn") (V "smid")) (.assign "smid" (V "sn")) .skip)
      (.seq (.assign "shi" (.bin .add (V "smid") (V "sw")))
        (.seq (.ite (.lt (V "sn") (V "shi")) (.assign "shi" (V "sn")) .skip)
          (.seq (.assign "si" (V "slo"))
            (.seq (.assign "sj" (V "smid")) (.assign "sk" (V "slo")))))))

/-- One block: set up, merge, and move `slo` on by two runs. -/
def blockBody (cmp : Com) : Com :=
  .seq blockSetup (.seq (mergeLoop cmp)
    (.seq (.assign "slo" (.bin .add (V "slo") (V "sw")))
      (.assign "slo" (.bin .add (V "slo") (V "sw")))))

theorem blockSetup_spec {B : ℕ} (lo w n : ℕ) (hb1 : lo + w < B) (hb2 : min (lo + w) n + w < B)
    (hnB : n < B) :
    Spec B (fun σ => σ.vars "slo" = lo ∧ σ.vars "sw" = w ∧ σ.vars "sn" = n) blockSetup
      (fun σ σ' => σ'.vars "smid" = min (lo + w) n ∧
        σ'.vars "shi" = min (min (lo + w) n + w) n ∧ σ'.vars "si" = lo ∧
        σ'.vars "sj" = min (lo + w) n ∧ σ'.vars "sk" = lo ∧
        (∀ y, y ≠ "smid" → y ≠ "shi" → y ≠ "si" → y ≠ "sj" → y ≠ "sk" →
          σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  run_vcg
  all_goals (simp_all)
  all_goals (try omega)

/-! ## The list side of one block -/

theorem seg_min {A : List ℕ} (i w : ℕ) : seg A i (min (i + w) A.length) = (A.drop i).take w := by
  simp only [seg]
  rw [List.drop_take]
  by_cases h : i + w ≤ A.length
  · rw [min_eq_left h]; congr 1; omega
  · rw [min_eq_right (by omega)]
    have : (A.drop i).length ≤ w := by simp only [List.length_drop]; omega
    rw [List.take_of_length_le (by simp only [List.length_drop]; omega), List.take_of_length_le this]

theorem drop_min {A : List ℕ} (i w : ℕ) : A.drop (min (i + w) A.length) = (A.drop i).drop w := by
  rw [List.drop_drop]
  by_cases h : i + w ≤ A.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

theorem take_eq_append_seg (L : List ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    L.take hi = L.take lo ++ seg L lo hi := by
  simp only [seg]
  conv_lhs => rw [← List.take_append_drop lo (L.take hi)]
  rw [List.take_take, min_eq_left h]

/-- What the block contributes: the merge of the two runs is the first output of `pass`. -/
theorem block_step (A : List ℕ) (lo w : ℕ) (hw : 0 < w) (hlo : lo < A.length) :
    let mid := min (lo + w) A.length
    let hi := min (mid + w) A.length
    SortList.pass r w (A.drop lo) =
      (seg A lo mid).merge (seg A mid hi) (SortList.cmp r) ++
        SortList.pass r w (A.drop (lo + 2 * w)) := by
  intro mid hi
  have hne : A.drop lo ≠ [] := by
    intro h; rw [List.drop_eq_nil_iff] at h; omega
  rw [SortList.pass_of_ne r hw hne]
  have h1 : seg A lo mid = (A.drop lo).take w := seg_min lo w
  have h2 : seg A mid hi = ((A.drop lo).drop w).take w := by
    have := seg_min (A := A) mid w
    rw [this, drop_min]
  rw [h1, h2]
  simp only [List.drop_drop, Nat.two_mul]

/-- The invariant of a pass of width `w` over the array `A`: the buffer holds the merged blocks
before `slo`. -/
def PI (w : ℕ) (A : List ℕ) (σ : Env) : Prop :=
  σ.arrs "SA" = A ∧ σ.vars "sw" = w ∧ σ.vars "sn" = A.length ∧
  (σ.arrs "SB").length = A.length ∧
  (σ.arrs "SB").take (min (σ.vars "slo") A.length) ++ SortList.pass r w (A.drop (σ.vars "slo")) =
    SortList.pass r w A

/-- The cost of one block, per entry it covers. -/
def blockK (cc : ℕ) : ℕ := cc + 200

theorem blockBody_run {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) (w : ℕ) (A : List ℕ) (hw : 0 < w) (hwn : w < A.length)
    (hnB : 3 * A.length + 3 < B) (hAB : ∀ v ∈ A, v < B ∧ C.good v) (σ : Env) (hBase : Base σ)
    (hPI : PI r w A σ) (hlt : σ.vars "slo" < A.length) :
    ∃ σ' K, Run B (blockBody C.com) σ σ' K ∧
      K ≤ blockK C.cost * (min (σ.vars "slo" + 2 * w) A.length - σ.vars "slo") ∧
      Base σ' ∧ PI r w A σ' ∧ σ'.vars "slo" = σ.vars "slo" + 2 * w := by
  obtain ⟨hSA, hsw, hsn, hSBl, hpi⟩ := hPI
  set lo := σ.vars "slo" with hlo
  set n := A.length with hn
  set mid := min (lo + w) n with hmid
  set hi := min (mid + w) n with hhi
  have hlm : lo ≤ mid := by omega
  have hmh : mid ≤ hi := by omega
  have hhn : hi ≤ n := by omega
  have hbB : hi < B := by omega
  obtain ⟨σ1, hr1, hm1, hh1, hi1, hj1, hk1, hfr1, harr1, hinp1, hout1⟩ :=
    (blockSetup_spec (B := B) lo w n (by omega) (by omega) (by omega)).run
      (σ := σ) ⟨rfl, hsw, hsn⟩
  have hnot : ∀ y, y ∉ "sc" :: SV → y ≠ "smid" ∧ y ≠ "shi" ∧ y ≠ "si" ∧ y ≠ "sj" ∧ y ≠ "sk" := by
    intro y hy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hy (by simp [SV, h])
  have hBase1 : Base σ1 := hBO σ σ1 hBase (fun y hy => by
      obtain ⟨a, b, c, d, e⟩ := hnot y hy
      exact hfr1 y a b c d e) (fun a _ _ => by rw [harr1])
  have hV1 : ∀ y, y ≠ "smid" → y ≠ "shi" → y ≠ "si" → y ≠ "sj" → y ≠ "sk" →
      σ1.vars y = σ.vars y := hfr1
  have hMI1 : MI r lo mid hi A (σ.arrs "SB") σ1 := by
    refine ⟨by rw [harr1]; exact hSA, hm1, hh1, by rw [hi1], by rw [hi1]; exact hlm,
      by rw [hj1], by rw [hj1]; exact hmh, by rw [hk1, hi1, hj1]; omega,
      by rw [harr1], by rw [harr1], ?_⟩
    rw [hk1, hi1, hj1, seg_nil le_rfl, List.nil_append]
  have hSB0 : hi ≤ (σ.arrs "SB").length := by omega
  obtain ⟨σ2, hr2, ⟨hBase2, hMI2⟩, hk2, hn2, hw2, hl2⟩ :=
    (mergeLoop_spec r C hBO hB lo mid hi A (σ.arrs "SB") n w lo hlm hmh (by omega) hSB0 hbB hAB).run
      (σ := σ1) ⟨hBase1, hMI1, hk1,
        (by rw [hV1 "sn" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsn),
        (by rw [hV1 "sw" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsw),
        (by rw [hV1 "slo" (by decide) (by decide) (by decide) (by decide) (by decide)])⟩
  have hfinal := MI_final r hMI2 hk2
  obtain ⟨hSA2, -, -, -, -, -, -, -, hSBl2, hSBt2, -⟩ := hMI2
  have hvl : (V "slo").evalB B σ2 = some lo := hl2 ▸ evalB_var (by rw [hl2]; omega)
  have hvw : (V "sw").evalB B σ2 = some w := hw2 ▸ evalB_var (by rw [hw2]; omega)
  have ra := Run.assign (B := B) (σ := σ2) (x := "slo") (e := .bin .add (V "slo") (V "sw"))
    (v := lo + w) (evalB_bin hvl hvw (by show lo + w < B; omega))
  set σ3 : Env := σ2.setVar "slo" (lo + w) with hσ3
  have hvl3 : (V "slo").evalB B σ3 = some (lo + w) := by
    have : σ3.vars "slo" = lo + w := by simp [hσ3]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hvw3 : (V "sw").evalB B σ3 = some w := by
    have : σ3.vars "sw" = w := by simp [hσ3, hw2]
    exact this ▸ evalB_var (by rw [this]; omega)
  have rb := Run.assign (B := B) (σ := σ3) (x := "slo") (e := .bin .add (V "slo") (V "sw"))
    (v := lo + w + w) (evalB_bin hvl3 hvw3 (by show lo + w + w < B; omega))
  set σ4 : Env := σ3.setVar "slo" (lo + w + w) with hσ4
  have hd1 : 1 ≤ hi - lo := by omega
  have hdd : min (lo + 2 * w) n - lo = hi - lo := by omega
  have hσ4l : σ4.vars "slo" = lo + w + w := by simp [hσ4, hσ3]
  refine ⟨σ4, blockK C.cost * (min (lo + 2 * w) n - lo),
    (hr1.seq (hr2.seq (ra.seq rb))).mono ?_, le_rfl, ?_, ?_, ?_⟩
  · rw [hdd]
    simp only [Expr.size, blockK]
    nlinarith [hd1]
  · exact hBO σ2 σ4 hBase2 (fun y hy => by
        have : y ≠ "slo" := fun h => hy (by simp [SV, h])
        simp [hσ4, hσ3, this]) (fun a _ _ => by simp [hσ4, hσ3])
  · refine ⟨by simp [hσ4, hσ3, hSA2], by simp [hσ4, hσ3, hw2],
      by simp [hσ4, hσ3]; exact hn2.trans hn,
      by simp [hσ4, hσ3]; rw [hSBl2, hSBl], ?_⟩
    have hmin : min (σ4.vars "slo") A.length = hi := by rw [hσ4l]; omega
    rw [hmin]
    have hslo : (σ4.vars "slo") = lo + 2 * w := by rw [hσ4l]; omega
    rw [hslo]
    have hSB4 : σ4.arrs "SB" = σ2.arrs "SB" := by simp [hσ4, hσ3]
    rw [hSB4]
    have hblk : SortList.pass r w (A.drop lo) =
        (seg A lo mid).merge (seg A mid hi) (SortList.cmp r) ++
          SortList.pass r w (A.drop (lo + 2 * w)) := block_step r A lo w hw hlt
    have hpi' : (σ.arrs "SB").take lo ++ SortList.pass r w (A.drop lo) = SortList.pass r w A := by
      have : min lo n = lo := by omega
      rw [this] at hpi; exact hpi
    rw [take_eq_append_seg _ (hlm.trans hmh), hSBt2, hfinal, List.append_assoc, ← hblk]
    exact hpi'
  · exact hσ4l.trans (by omega)

/-! ## One pass: every block -/

/-- Merge every pair of neighbouring runs of width `sw` into the buffer. -/
def blockLoop (cmp : Com) : Com := .while (.lt (V "slo") (V "sn")) (blockBody cmp)

theorem blockLoop_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) (w : ℕ) (A : List ℕ) (hw : 0 < w) (hwn : w < A.length)
    (hnB : 3 * A.length + 3 < B) (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => Base σ ∧ PI r w A σ ∧ σ.vars "slo" = 0) (blockLoop C.com)
      (fun _ σ' => Base σ' ∧ σ'.arrs "SB" = SortList.pass r w A ∧ σ'.arrs "SA" = A ∧
        σ'.vars "sn" = A.length ∧ σ'.vars "sw" = w)
      ((blockK C.cost + 4) * A.length + 4) := by
  have := Spec.while_potential (B := B) (b := .lt (V "slo") (V "sn")) (c := blockBody C.com)
    (P := fun σ => Base σ ∧ PI r w A σ ∧ σ.vars "slo" = 0)
    (fun σ => Base σ ∧ PI r w A σ ∧ σ.vars "slo" < 3 * A.length + 1)
    (fun σ => (blockK C.cost + 4) * (A.length - σ.vars "slo"))
    (fun σ h => evalB_condLt_vars (by omega) (by rw [h.2.1.2.2.1]; omega))
    (fun σ h hc => by
      have hlt : σ.vars "slo" < A.length := by
        have hv := evalB_condLt (B := B) (σ := σ) (e := V "slo") (f := V "sn")
          (evalB_var (by omega : σ.vars "slo" < B)) (evalB_var (by rw [h.2.1.2.2.1]; omega))
        rw [hv] at hc
        have := Option.some.inj hc
        have h2 : decide (σ.vars "slo" < σ.vars "sn") = true := this
        have h3 := of_decide_eq_true h2
        rw [h.2.1.2.2.1] at h3; exact h3
      obtain ⟨σ', K, hrun, hK, hb', hpi', hl'⟩ :=
        blockBody_run r C hBO hB w A hw hwn hnB hAB σ h.1 h.2.1 hlt
      refine ⟨σ', K, hrun, ⟨hb', hpi', by omega⟩, ?_⟩
      have hd1 : 1 ≤ min (σ.vars "slo" + 2 * w) A.length - σ.vars "slo" := by omega
      have hd2 : A.length - σ'.vars "slo" + (min (σ.vars "slo" + 2 * w) A.length - σ.vars "slo")
          ≤ A.length - σ.vars "slo" := by omega
      have hm := Nat.mul_le_mul_left (blockK C.cost + 4) hd2
      rw [Nat.mul_add] at hm
      simp only [Cond.size, Expr.size]
      nlinarith [hK, hm, hd1])
    (fun σ h => ⟨h.1, h.2.1, by omega⟩)
    (fun σ h => by rw [h.2.2, Nat.sub_zero])
  refine this.post (fun σ σ' hσ h => ?_)
  obtain ⟨⟨hb', hpi', hl'⟩, hc⟩ := h
  obtain ⟨hSA, hsw, hsn, hSBl, hpi⟩ := hpi'
  have hge : A.length ≤ σ'.vars "slo" := by
    have hv := evalB_condLt (B := B) (σ := σ') (e := V "slo") (f := V "sn")
      (evalB_var (by omega : σ'.vars "slo" < B)) (evalB_var (by rw [hsn]; omega))
    rw [hv] at hc
    have := Option.some.inj hc
    have h2 : decide (σ'.vars "slo" < σ'.vars "sn") = false := this
    have h3 := of_decide_eq_false h2
    rw [hsn] at h3; omega
  refine ⟨hb', ?_, hSA, hsn, hsw⟩
  rw [min_eq_right hge, List.drop_of_length_le hge, SortList.pass_nil, List.append_nil,
    List.take_of_length_le (by omega)] at hpi
  exact hpi

/-! ## Copying the buffer back -/

theorem take_set_succ (L : List ℕ) {k v : ℕ} (hk : k < L.length) :
    (L.set k v).take (k + 1) = L.take k ++ [v] := by
  have hlen : (L.take k).length = k := by simp; omega
  rw [List.set_eq_take_append_cons_drop, if_pos hk, List.take_append]
  simp [hlen]

theorem take_getD_succ (S : List ℕ) {k : ℕ} (hk : k < S.length) :
    S.take (k + 1) = S.take k ++ [S.getD k 0] := by
  rw [List.take_add_one]
  simp [List.getD_eq_getElem?_getD, hk]


/-- `SA := SB`. -/
def copyLoop : Com :=
  .seq (.assign "si" (.lit 0))
    (.while (.lt (V "si") (V "sn"))
      (.seq (.store "SA" (V "si") (.get "SB" (V "si"))) (bump "si")))

theorem copyLoop_spec {B : ℕ} {Base : Env → Prop} (hBO : BaseOK Base) (hB : 1 < B)
    (S : List ℕ) (w0 : ℕ) (hnB : S.length < B) (hS : ∀ v ∈ S, v < B) :
    Spec B (fun σ => Base σ ∧ σ.arrs "SB" = S ∧ σ.vars "sn" = S.length ∧
        (σ.arrs "SA").length = S.length ∧ σ.vars "sw" = w0) copyLoop
      (fun _ σ' => Base σ' ∧ σ'.arrs "SA" = S ∧ σ'.arrs "SB" = S ∧ σ'.vars "sn" = S.length ∧
        σ'.vars "sw" = w0) ((20 + 4) * S.length + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := .seq (.store "SA" (V "si") (.get "SB" (V "si")))
      (bump "si")) "si" "sn"
    (fun σ => Base σ ∧ σ.arrs "SB" = S ∧ σ.vars "sn" = S.length ∧
      (σ.arrs "SA").length = S.length ∧ σ.vars "sw" = w0 ∧ σ.vars "si" ≤ S.length ∧
      (σ.arrs "SA").take (σ.vars "si") = S.take (σ.vars "si"))
    S.length 20 hnB (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.1) (by
      refine Spec.of_exists fun σ ⟨⟨hBase, hSB, hsn, hSAl, hsw, hle, htk⟩, hlt⟩ => ?_
      have hvi : (V "si").evalB B σ = some (σ.vars "si") := evalB_var (by omega)
      have hcell : σ.vars "si" < S.length := by omega
      have hg : (Expr.get "SB" (V "si")).evalB B σ = some (S.getD (σ.vars "si") 0) := by
        have := RunStep.eval_get B σ "SB" (V "si") (σ.vars "si") hvi (by rw [hSB]; exact hcell)
          (by rw [hSB]; exact hS _ (by rw [List.getD_eq_getElem _ _ hcell]; exact List.getElem_mem hcell))
        rwa [hSB] at this
      have r1 := Run.store (B := B) (σ := σ) (a := "SA") (i := V "si") (e := .get "SB" (V "si"))
        (idx := σ.vars "si") (v := S.getD (σ.vars "si") 0) hvi hg (by omega)
      set σa : Env := σ.setArr "SA" (σ.vars "si") (S.getD (σ.vars "si") 0) with hσa
      have hvia : (V "si").evalB B σa = some (σ.vars "si") := by
        have : σa.vars "si" = σ.vars "si" := by simp [hσa]
        exact this ▸ evalB_var (by rw [this]; omega)
      have hl1 : (Expr.lit 1).evalB B σa = some 1 := evalB_lit hB
      have r2 := Run.assign (B := B) (σ := σa) (x := "si") (e := .bin .add (V "si") (.lit 1))
        (v := σ.vars "si" + 1) (evalB_bin hvia hl1 (by show σ.vars "si" + 1 < B; omega))
      refine ⟨_, 20, (r1.seq r2).mono ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.size]; omega
      · exact hBO σ _ hBase (fun y hy => by
          have : y ≠ "si" := fun h => hy (by simp [SV, h])
          simp [hσa, this]) (fun a h1 h2 => by simp [hσa, h1])
      · simp [hσa, hSB]
      · simp [hσa, hsn]
      · simp [hσa, hSAl]
      · simp [hσa, hsw]
      · simp [hσa]; omega
      · simp only [hσa, arrs_setVar, arrs_setArr, vars_setVar, if_true]
        rw [take_set_succ _ (by omega), take_getD_succ S hcell, htk]
      · simp [hσa])
  refine (hloop.conseq ?_ ?_ le_rfl)
  · rintro σ ⟨hBase, hSB, hsn, hSAl, hsw⟩
    refine ⟨hBO σ _ hBase (fun y hy => by
        have : y ≠ "si" := fun h => hy (by simp [SV, h])
        simp [this]) (fun a _ _ => rfl), by simpa using hSB, by simpa using hsn,
      by simpa using hSAl, by simpa using hsw, by simp, by simp⟩
  · rintro σ σ' - ⟨⟨hBase, hSB, hsn, hSAl, hsw, hle, htk⟩, hsi⟩
    rw [hsi] at htk
    have hSA : σ'.arrs "SA" = S := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at htk
      exact htk
    exact ⟨hBase, hSA, hSB, hsn, hsw⟩

/-! ## The number of passes -/

/-- `snp := ⌈log₂ sn⌉`, by doubling `sw`; `sw` ends at `2 ^ snp`. -/
def npLoop : Com :=
  .seq (.assign "sw" (.lit 1))
    (.seq (.assign "snp" (.lit 0))
      (.while (.lt (V "sw") (V "sn"))
        (.seq (.assign "sw" (.bin .mul (V "sw") (.lit 2))) (bump "snp"))))

theorem npLoop_spec {B : ℕ} (n : ℕ) (hB : 1 < B) (hnB : 2 * n + 2 < B) :
    Spec B (fun σ => σ.vars "sn" = n) npLoop
      (fun σ σ' => σ'.vars "snp" = Nat.clog 2 n ∧ σ'.vars "sw" = 2 ^ Nat.clog 2 n ∧
        σ'.vars "sn" = n ∧ (∀ y, y ≠ "sw" → y ≠ "snp" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (12 * (Nat.clog 2 n) + 20) := by
  have hone := hB
  refine Spec.of_exists fun σ hσ => ?_
  have hl1 : ∀ σ' : Env, (Expr.lit 1).evalB B σ' = some 1 := fun _ => evalB_lit hB
  have hl0 : ∀ σ' : Env, (Expr.lit 0).evalB B σ' = some 0 := fun _ => evalB_lit (by omega)
  have hl2 : ∀ σ' : Env, (Expr.lit 2).evalB B σ' = some 2 := fun _ => evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "sw") (e := .lit 1) (v := 1) (hl1 σ)
  set σ1 : Env := σ.setVar "sw" 1 with hσ1
  have r2 := Run.assign (B := B) (σ := σ1) (x := "snp") (e := .lit 0) (v := 0) (hl0 σ1)
  set σ2 : Env := σ1.setVar "snp" 0 with hσ2
  have hpc : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
      have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
      have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
        rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      omega
  have hloop := Spec.while_potential (B := B) (b := .lt (V "sw") (V "sn"))
    (c := .seq (.assign "sw" (.bin .mul (V "sw") (.lit 2))) (bump "snp"))
    (P := fun τ => τ = σ2) (K := 12 * Nat.clog 2 n + 4)
    (fun τ => τ.vars "sw" = 2 ^ τ.vars "snp" ∧ τ.vars "snp" ≤ Nat.clog 2 n ∧
      τ.vars "sn" = n ∧ (∀ y, y ≠ "sw" → y ≠ "snp" → τ.vars y = σ.vars y) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out)
    (fun τ => 12 * (Nat.clog 2 n - τ.vars "snp"))
    (fun τ h => evalB_condLt_vars (by
        have hle : 2 ^ τ.vars "snp" ≤ 2 * n + 1 :=
          (Nat.pow_le_pow_right (by norm_num) h.2.1).trans hpc
        rw [h.1]; generalize 2 ^ τ.vars "snp" = a at hle ⊢; omega) (by have := h.2.2.1; omega))
    (fun τ h hc => by
      have hlt : τ.vars "sw" < n := by
        have hv := evalB_condLt (B := B) (σ := τ) (e := V "sw") (f := V "sn")
          (evalB_var (σ := τ) (x := "sw") (by
            have hle : 2 ^ τ.vars "snp" ≤ 2 * n + 1 :=
              (Nat.pow_le_pow_right (by norm_num) h.2.1).trans hpc
            rw [h.1]; generalize 2 ^ τ.vars "snp" = a at hle ⊢; omega)) (evalB_var (σ := τ) (x := "sn") (by have := h.2.2.1; omega))
        rw [hv] at hc
        have h2 : decide (τ.vars "sw" < τ.vars "sn") = true := Option.some.inj hc
        have h3 := of_decide_eq_true h2
        rwa [h.2.2.1] at h3
      have hsn : τ.vars "snp" < Nat.clog 2 n := by
        by_contra hcon
        have : Nat.clog 2 n ≤ τ.vars "snp" := by omega
        have h4 := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).mp this
        rw [h.1] at hlt; omega
      have hpow : τ.vars "snp" < 2 ^ τ.vars "snp" := Nat.lt_two_pow_self
      have hle : 2 ^ τ.vars "snp" ≤ 2 * n + 1 :=
        (Nat.pow_le_pow_right (by norm_num) h.2.1).trans hpc
      have hswB : τ.vars "sw" < n := hlt
      have hvw : (V "sw").evalB B τ = some (τ.vars "sw") := evalB_var (by omega)
      have ra := Run.assign (B := B) (σ := τ) (x := "sw") (e := .bin .mul (V "sw") (.lit 2))
        (v := τ.vars "sw" * 2) (evalB_bin hvw (hl2 τ) (by show τ.vars "sw" * 2 < B; omega))
      set τ1 : Env := τ.setVar "sw" (τ.vars "sw" * 2) with hτ1
      have hvs : (V "snp").evalB B τ1 = some (τ.vars "snp") := by
        have : τ1.vars "snp" = τ.vars "snp" := by simp [hτ1]
        exact this ▸ evalB_var (by rw [this]; omega)
      have rb := Run.assign (B := B) (σ := τ1) (x := "snp") (e := .bin .add (V "snp") (.lit 1))
        (v := τ.vars "snp" + 1) (evalB_bin hvs (hl1 τ1) (by show τ.vars "snp" + 1 < B; omega))
      refine ⟨_, _, ra.seq rb, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [hτ1, h.1, Nat.pow_succ]
      · simp [hτ1]; omega
      · simp [hτ1, h.2.2.1]
      · intro y h1 h2; simp [hτ1, h1, h2, h.2.2.2.1 y h1 h2]
      · simp [hτ1, h.2.2.2.2.1]
      · simp [hτ1, h.2.2.2.2.2.1]
      · simp [hτ1, h.2.2.2.2.2.2]
      · simp only [Expr.size]; simp [hτ1]; omega)
    (fun τ h => by
      subst h
      refine ⟨by simp [hσ2, hσ1], by simp [hσ2, hσ1], by simp [hσ2, hσ1, hσ], ?_,
        by simp [hσ2, hσ1], by simp [hσ2, hσ1], by simp [hσ2, hσ1]⟩
      intro y h1 h2; simp [hσ2, hσ1, h1, h2])
    (fun τ h => by
      subst h
      simp only [Cond.size, Expr.size, hσ2, hσ1, vars_setVar]
      simp)
  obtain ⟨σ3, hr3, ⟨hsw, hsnp, hsn, hfr, harr, hinp, hout⟩, hfalse⟩ := hloop σ2 rfl
  have hge : n ≤ 2 ^ σ3.vars "snp" := by
    have hv := evalB_condLt (B := B) (σ := σ3) (e := V "sw") (f := V "sn")
      (evalB_var (σ := σ3) (x := "sw") (by
        have hle : 2 ^ σ3.vars "snp" ≤ 2 * n + 1 :=
          (Nat.pow_le_pow_right (by norm_num) hsnp).trans hpc
        rw [hsw]; generalize 2 ^ σ3.vars "snp" = a at hle ⊢; omega))
      (evalB_var (σ := σ3) (x := "sn") (by have := hsn; omega))
    rw [hv] at hfalse
    have h2 : decide (σ3.vars "sw" < σ3.vars "sn") = false := Option.some.inj hfalse
    have h3 := of_decide_eq_false h2
    rw [hsw, hsn] at h3; omega
  have hcl : Nat.clog 2 n ≤ σ3.vars "snp" := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hge
  have heq : σ3.vars "snp" = Nat.clog 2 n := le_antisymm hsnp hcl
  refine ⟨σ3, 12 * Nat.clog 2 n + 8, (r1.seq (r2.seq hr3)).mono ?_, by omega,
    heq, by rw [hsw, heq], hsn, hfr, harr, hinp, hout⟩
  simp only [Expr.size]; omega

/-! ## One whole pass -/

/-- Merge every pair of runs of width `sw`, and copy the buffer back. -/
def passCom (cmp : Com) : Com :=
  .seq (.assign "slo" (.lit 0)) (.seq (blockLoop cmp) copyLoop)

theorem passCom_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) (w : ℕ) (A : List ℕ) (hw : 0 < w) (hwn : w < A.length)
    (hnB : 3 * A.length + 3 < B) (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => Base σ ∧ σ.arrs "SA" = A ∧ σ.vars "sn" = A.length ∧ σ.vars "sw" = w ∧
        (σ.arrs "SB").length = A.length) (passCom C.com)
      (fun _ σ' => Base σ' ∧ σ'.arrs "SA" = SortList.pass r w A ∧
        σ'.arrs "SB" = SortList.pass r w A ∧ σ'.vars "sn" = A.length ∧ σ'.vars "sw" = w)
      (2 + (((blockK C.cost + 4) * A.length + 4) + ((20 + 4) * A.length + 6))) := by
  have hpermL : (SortList.pass r w A).length = A.length := (SortList.pass_perm r w A).length_eq
  have hpermM : ∀ v ∈ SortList.pass r w A, v < B := fun v hv =>
    (hAB v ((SortList.pass_perm r w A).mem_iff.mp hv)).1
  have hblock := blockLoop_spec r C hBO hB w A hw hwn hnB hAB
  have hcopy := copyLoop_spec (B := B) (Base := Base) hBO hB (SortList.pass r w A) w
    (by omega) hpermM
  refine Spec.of_exists fun σ ⟨hBase, hSA, hsn, hsw, hSBl⟩ => ?_
  have r1 := Run.assign (B := B) (σ := σ) (x := "slo") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  set σ1 : Env := σ.setVar "slo" 0 with hσ1
  have hBase1 : Base σ1 := hBO σ σ1 hBase (fun y hy => by
      have : y ≠ "slo" := fun h => hy (by simp [SV, h])
      simp [hσ1, this]) (fun a _ _ => rfl)
  obtain ⟨σ2, hr2, hBase2, hSB2, hSA2, hsn2, hsw2⟩ := hblock.run (σ := σ1)
    ⟨hBase1, ⟨by simpa [hσ1] using hSA, by simpa [hσ1] using hsw, by simpa [hσ1] using hsn,
      by simpa [hσ1] using hSBl, by simp [hσ1]⟩, by simp [hσ1]⟩
  obtain ⟨σ3, hr3, hBase3, hSA3, hSB3, hsn3, hsw3⟩ := hcopy.run (σ := σ2)
    ⟨hBase2, hSB2, by rw [hsn2, hpermL], by rw [hSA2]; omega, hsw2⟩
  refine ⟨σ3, _, (r1.seq (hr2.seq hr3)).mono ?_, le_rfl, hBase3, hSA3, hSB3, by rw [hsn3, hpermL], hsw3⟩
  simp only [Expr.size, hpermL]; omega

/-! ## The sort -/

/-- One pass, then double the width. -/
def passBody (cmp : Com) : Com :=
  .seq (passCom cmp) (.seq (.assign "sw" (.bin .mul (V "sw") (.lit 2))) (bump "spc"))

/-- **The sort**: `⌈log₂ n⌉` passes. -/
def sortCom (cmp : Com) : Com :=
  .seq npLoop (.seq (.assign "sw" (.lit 1))
    (.seq (.assign "spc" (.lit 0))
      (.while (.lt (V "spc") (V "snp")) (passBody cmp))))

omit [DecidableRel r] in
theorem passCom_free {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) :
    "snp" ∉ (passCom C.com).wvars ∧ "spc" ∉ (passCom C.com).wvars := by
  obtain ⟨h1, h2⟩ := C.free
  constructor <;>
  · simp [passCom, blockLoop, blockBody, blockSetup, mergeLoop, mergeBody, tlSetup, moveK,
      copyLoop, bump, Com.wvars, h1, h2]

/-- What the loop over passes keeps. -/
def OI (A : List ℕ) (σ : Env) : Prop :=
  σ.arrs "SA" = SortList.iter r A (σ.vars "spc") ∧ σ.vars "sw" = 2 ^ σ.vars "spc" ∧
  σ.vars "sn" = A.length ∧ (σ.arrs "SB").length = A.length ∧
  σ.vars "snp" = Nat.clog 2 A.length ∧ σ.vars "spc" ≤ Nat.clog 2 A.length

/-- The cost of one pass, with its doubling. -/
def passCost (cc n : ℕ) : ℕ := 2 + (((blockK cc + 4) * n + 4) + ((20 + 4) * n + 6)) + 8

theorem passBody_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) [IsTrans ℕ r] [Std.Total r] (A : List ℕ) (hnB : 3 * A.length + 3 < B)
    (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => (Base σ ∧ OI r A σ) ∧ σ.vars "spc" < Nat.clog 2 A.length) (passBody C.com)
      (fun σ σ' => (Base σ' ∧ OI r A σ') ∧ σ'.vars "spc" = σ.vars "spc" + 1)
      (passCost C.cost A.length) := by
  refine Spec.of_exists fun σ ⟨⟨hBase, hSA, hsw, hsn, hSBl, hsnp, hle⟩, hlt⟩ => ?_
  set pc := σ.vars "spc" with hpc
  set n := A.length with hn
  have hitr := SortList.iter_spec r A pc
  have hA'len : (SortList.iter r A pc).length = n := hitr.1.length_eq
  have hA'B : ∀ v ∈ SortList.iter r A pc, v < B ∧ C.good v := fun v hv => hAB v (hitr.1.mem_iff.mp hv)
  have hpown : 2 ^ pc < n := by
    by_contra hcon
    have : n ≤ 2 ^ pc := by omega
    have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).mpr this
    omega
  have hpw : 0 < 2 ^ pc := Nat.two_pow_pos pc
  obtain ⟨w, hwdef⟩ : ∃ w, w = 2 ^ pc := ⟨_, rfl⟩
  rw [← hwdef] at hpown hpw hsw
  have hpass := (passCom_spec r C hBO hB w (SortList.iter r A pc) hpw
    (by rw [hA'len]; exact hpown) (by rw [hA'len]; exact hnB) hA'B).frame
  obtain ⟨σ1, hr1, ⟨hBase1, hSA1, hSB1, hsn1, hsw1⟩, hfv, -, -, -⟩ :=
    hpass.run ⟨hBase, by rw [hSA], by rw [hsn, hA'len], by rw [hsw], by rw [hSBl, hA'len]⟩
  have hpc1 : σ1.vars "spc" = pc := hfv "spc" (passCom_free r C).2
  have hnp1 : σ1.vars "snp" = Nat.clog 2 n := by rw [hfv "snp" (passCom_free r C).1, hsnp]
  have hswv : (V "sw").evalB B σ1 = some w := hsw1 ▸ evalB_var (by rw [hsw1]; omega)
  have hl2 : (Expr.lit 2).evalB B σ1 = some 2 := evalB_lit (by omega)
  have ra := Run.assign (B := B) (σ := σ1) (x := "sw") (e := .bin .mul (V "sw") (.lit 2))
    (v := w * 2) (evalB_bin hswv hl2 (by show w * 2 < B; omega))
  set σ2 : Env := σ1.setVar "sw" (w * 2) with hσ2
  have hpcn : pc < n := by
    have : pc < 2 ^ pc := Nat.lt_two_pow_self
    omega
  have hvp : (V "spc").evalB B σ2 = some pc := by
    have : σ2.vars "spc" = pc := by simp [hσ2, hpc1]
    exact this ▸ evalB_var (by rw [this]; omega)
  have hl1 : (Expr.lit 1).evalB B σ2 = some 1 := evalB_lit hB
  have rb := Run.assign (B := B) (σ := σ2) (x := "spc") (e := .bin .add (V "spc") (.lit 1))
    (v := pc + 1) (evalB_bin hvp hl1 (by show pc + 1 < B; omega))
  refine ⟨_, passCost C.cost n, (hr1.seq (ra.seq rb)).mono ?_, le_rfl, ⟨?_, ?_⟩, ?_⟩
  · simp only [Expr.size, passCost, hA'len]; omega
  · exact hBO σ1 _ hBase1 (fun y hy => by
      have h1 : y ≠ "sw" := fun h => hy (by simp [SV, h])
      have h2 : y ≠ "spc" := fun h => hy (by simp [SV, h])
      simp [hσ2, h1, h2]) (fun a _ _ => by simp [hσ2])
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ2, hSA1, SortList.iter, ← hwdef]
    · simp [hσ2, Nat.pow_succ, hwdef]
    · simp [hσ2, hsn1]; exact hA'len
    · simp [hσ2, hSB1]; rw [(SortList.pass_perm r _ _).length_eq]; exact hA'len
    · simp [hσ2, hnp1, hn]
    · simp [hσ2]; omega
  · simp [hσ2]

/-- The cost of the sort. -/
def sortK (cc n : ℕ) : ℕ :=
  (12 * Nat.clog 2 n + 20) + 4 + ((passCost cc n + 4) * Nat.clog 2 n + 6)

theorem sort_spec {B : ℕ} {Base : Env → Prop} (C : Cmp B r Base) (hBO : BaseOK Base)
    (hB : 1 < B) [IsTrans ℕ r] [Std.Total r] (A : List ℕ) (hnB : 3 * A.length + 3 < B)
    (hAB : ∀ v ∈ A, v < B ∧ C.good v) :
    Spec B (fun σ => Base σ ∧ σ.arrs "SA" = A ∧ σ.vars "sn" = A.length ∧
        (σ.arrs "SB").length = A.length) (sortCom C.com)
      (fun _ σ' => Base σ' ∧ (σ'.arrs "SA").Perm A ∧ (σ'.arrs "SA").Pairwise r)
      (sortK C.cost A.length) := by
  have hpc : 2 ^ Nat.clog 2 A.length ≤ 2 * A.length + 1 := by
    rcases Nat.lt_or_ge A.length 2 with h | h
    · interval_cases hl : A.length <;> simp
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := A.length) (by omega)
      have hpos : 0 < Nat.clog 2 A.length := Nat.clog_pos (by norm_num) (by omega)
      have : 2 ^ Nat.clog 2 A.length = 2 * 2 ^ (Nat.clog 2 A.length).pred := by
        rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      omega
  have hclB : Nat.clog 2 A.length < B := by
    have : Nat.clog 2 A.length < 2 ^ Nat.clog 2 A.length := Nat.lt_two_pow_self
    omega
  refine Spec.of_exists fun σ ⟨hBase, hSA, hsn, hSBl⟩ => ?_
  obtain ⟨σ1, hr1, hsnp, hsw, hsn1, hfr, harr, hinp, hout⟩ :=
    (npLoop_spec (B := B) A.length hB (by omega)).run hsn
  have hBase1 : Base σ1 := hBO σ σ1 hBase (fun y hy => by
      have h1 : y ≠ "sw" := fun h => hy (by simp [SV, h])
      have h2 : y ≠ "snp" := fun h => hy (by simp [SV, h])
      exact hfr y h1 h2) (fun a _ _ => by rw [harr])
  have r2 := Run.assign (B := B) (σ := σ1) (x := "sw") (e := .lit 1) (v := 1) (evalB_lit hB)
  set σ2 : Env := σ1.setVar "sw" 1 with hσ2
  have hBase2 : Base σ2 := hBO σ1 σ2 hBase1 (fun y hy => by
      have h1 : y ≠ "sw" := fun h => hy (by simp [SV, h])
      simp [hσ2, h1]) (fun a _ _ => rfl)
  have hloop := Spec.forRangeZero (B := B) (c := passBody C.com) "spc" "snp"
    (fun τ => Base τ ∧ OI r A τ) (Nat.clog 2 A.length) (passCost C.cost A.length) hclB
    (fun τ h => h.2.2.2.2.2.2) (fun τ h => h.2.2.2.2.2.1)
    (passBody_spec r C hBO hB A hnB hAB)
  obtain ⟨σ3, hr3, ⟨hBase3, hSA3, hsw3, hsn3, hSB3, hnp3, hle3⟩, hspc3⟩ := hloop
    σ2 ⟨hBO σ2 _ hBase2 (fun y hy => by
        have h1 : y ≠ "spc" := fun h => hy (by simp [SV, h])
        simp [h1]) (fun a _ _ => rfl),
      ⟨by simp [hσ2, SortList.iter, harr, hSA], by simp [hσ2], by simp [hσ2, hsn1],
        by simp [hσ2, harr, hSBl], by simp [hσ2, hsnp], by simp⟩⟩
  have hsorted := SortList.iter_sorted r A (Nat.clog 2 A.length)
    (Nat.le_pow_clog (by norm_num) _)
  rw [hspc3] at hSA3
  refine ⟨σ3, _, (hr1.seq (r2.seq hr3)).mono ?_, le_rfl, hBase3, ?_, ?_⟩
  · simp only [Expr.size, sortK]; omega
  · rw [hSA3]; exact hsorted.1
  · rw [hSA3]; exact hsorted.2

/-! ## The cost, against `sortCost` -/

theorem sortK_le (cc n m : ℕ) (hnm : n ≤ m) :
    sortK cc n ≤ (cc + 300) * ((m + 1) * (Nat.log 2 (m + 2) + 1)) := by
  have hcl : Nat.clog 2 n ≤ Nat.log 2 (m + 2) + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (m + 2)
    omega
  set L := Nat.log 2 (m + 2) + 1 with hL
  set c := Nat.clog 2 n with hc
  have hL1 : 1 ≤ L := by omega
  unfold sortK passCost blockK
  have h1 : n * c ≤ m * L := Nat.mul_le_mul hnm hcl
  nlinarith [h1, hL1, Nat.zero_le cc, Nat.zero_le c, Nat.zero_le (cc * n), Nat.mul_le_mul_left cc h1,
    Nat.mul_le_mul_left cc (Nat.mul_le_mul_left m hcl)]

end Lax496464Proofs.Ram.Sort
