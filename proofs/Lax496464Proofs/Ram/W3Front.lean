import Lax496464Proofs.Ram.Corollary1Prog
import Lax496464Proofs.Ram.DpMArr

/-!
# Theorem 3's machine, part 1: the pieces of the front end

Theorem 3's two programs start like Theorem 4's, but for arbitrary weights and processing
times, and with one more sort. This file has the pieces:

* `dueCmp`: the comparison of two job positions `a`, `b` by `(DS[a], a)` lexicographically, as
  a comparator of `Sort.lean`, and `dueSort_spec`, the sort of `0 … n − 1` under it;
* `buildW`: the sorted weight array `WS`, and its identification with `wv J`.
-/

namespace Lax496464Proofs.Ram.W3Front

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump SV Cmp BaseOK sort_spec sortCom sortK)
open Lax496464Proofs.Ram.EstSort (estDecide fillIdent fillIdent_spec)
open Lax496464Proofs.Ram.BuildSorted (buildRow buildRow_spec)
open Lax496464Proofs.Ram.EstPermute (permute listEquiv listEquiv_apply)
open Lax496464Proofs.Ram.DpMArr (wv)
open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-! ## The comparison by due date -/

/-- Position `a` is due no later than position `b`, ties broken by the position:
`(D[a], a) ≤ (D[b], b)` lexicographically. -/
def rDue (D : List ℕ) (a b : ℕ) : Prop :=
  D.getD a 0 < D.getD b 0 ∨ (D.getD a 0 = D.getD b 0 ∧ a ≤ b)

instance (D : List ℕ) : DecidableRel (rDue D) := fun a b => by
  unfold rDue; infer_instance

instance (D : List ℕ) : IsTrans ℕ (rDue D) :=
  ⟨fun a b c hab hbc => by unfold rDue at *; omega⟩

instance (D : List ℕ) : Std.Total (rDue D) :=
  ⟨fun a b => by unfold rDue; omega⟩

/-- Load the two due dates `ct1 = DS[sx]`, `ct2 = DS[sy]`. -/
def dueLoad : Com :=
  .seq (.assign "ct1" (.get "DS" (V "sx"))) (.assign "ct2" (.get "DS" (V "sy")))

/-- Compare positions `sx` and `sy`: `sc := 1` iff `rDue DS sx sy`. -/
def dueCmp : Com := .seq dueLoad estDecide

theorem dueLoad_spec {B : ℕ} (_hB : 1 < B) (D : List ℕ) (hDB : ∀ v ∈ D, v < B) (a b : ℕ)
    (haB : a < B) (hbB : b < B) (ha : a < D.length) (hb : b < D.length) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.vars "sx" = a ∧ σ.vars "sy" = b) dueLoad
      (fun σ σ' => σ'.vars "ct1" = D.getD a 0 ∧ σ'.vars "ct2" = D.getD b 0 ∧
        (∀ y, y ≠ "ct1" → y ≠ "ct2" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 20 := by
  have hbnd : ∀ t, t < D.length → D.getD t 0 < B := fun t ht =>
    hDB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  refine Spec.of_exists fun σ ⟨hD, hsx, hsy⟩ => ?_
  have hvx : (V "sx").evalB B σ = some a :=
    hsx ▸ evalB_var (B := B) (σ := σ) (x := "sx") (by rw [hsx]; exact haB)
  have g1 : (Expr.get "DS" (V "sx")).evalB B σ = some (D.getD a 0) := by
    have := RunStep.eval_get B σ "DS" (V "sx") a hvx (by rw [hD]; exact ha)
      (by rw [hD]; exact hbnd _ ha)
    rwa [hD] at this
  have ra := Run.assign (B := B) (σ := σ) (x := "ct1") (e := .get "DS" (V "sx"))
    (v := D.getD a 0) g1
  set σ1 : Env := σ.setVar "ct1" (D.getD a 0) with hσ1
  have hD1 : σ1.arrs "DS" = D := hD
  have hvy : (V "sy").evalB B σ1 = some b := by
    have : σ1.vars "sy" = b := by simp [hσ1, hsy]
    exact this ▸ evalB_var (B := B) (σ := σ1) (x := "sy") (by rw [this]; exact hbB)
  have g2 : (Expr.get "DS" (V "sy")).evalB B σ1 = some (D.getD b 0) := by
    have := RunStep.eval_get B σ1 "DS" (V "sy") b hvy (by rw [hD1]; exact hb)
      (by rw [hD1]; exact hbnd _ hb)
    rwa [hD1] at this
  have rb := Run.assign (B := B) (σ := σ1) (x := "ct2") (e := .get "DS" (V "sy"))
    (v := D.getD b 0) g2
  refine ⟨_, _, (ra.seq rb).mono ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · simp [hσ1]
  · simp [hσ1]
  · intro y h1 h2; simp [hσ1, h1, h2]
  · simp [hσ1]
  · simp [hσ1]
  · simp [hσ1]

theorem dueDecide_spec {B : ℕ} (hB : 1 < B) (c1 c2 a b : ℕ) (haB : a < B) (hbB : b < B)
    (hc1 : c1 < B) (hc2 : c2 < B) :
    Spec B (fun σ => σ.vars "ct1" = c1 ∧ σ.vars "ct2" = c2 ∧ σ.vars "sx" = a ∧
        σ.vars "sy" = b) estDecide
      (fun σ σ' => σ'.vars "sc" = (if c1 < c2 ∨ (c1 = c2 ∧ a ≤ b) then 1 else 0) ∧
        (∀ y, y ≠ "sc" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 30 := by
  refine Spec.of_exists fun σ ⟨h1, h2, hsx, hsy⟩ => ?_
  have hv1 : (V "ct1").evalB B σ = some c1 :=
    h1 ▸ evalB_var (B := B) (σ := σ) (x := "ct1") (by rw [h1]; exact hc1)
  have hv2 : (V "ct2").evalB B σ = some c2 :=
    h2 ▸ evalB_var (B := B) (σ := σ) (x := "ct2") (by rw [h2]; exact hc2)
  have hvx : (V "sx").evalB B σ = some a :=
    hsx ▸ evalB_var (B := B) (σ := σ) (x := "sx") (by rw [hsx]; exact haB)
  have hvy : (V "sy").evalB B σ = some b :=
    hsy ▸ evalB_var (B := B) (σ := σ) (x := "sy") (by rw [hsy]; exact hbB)
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  by_cases hlt : c1 < c2
  · have hc : (Cond.lt (V "ct1") (V "ct2")).evalB B σ = some true := by
      rw [evalB_condLt hv1 hv2]; simp [hlt]
    have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 1) (v := 1) hl1
    have hr : c1 < c2 ∨ (c1 = c2 ∧ a ≤ b) := Or.inl hlt
    refine ⟨_, _, Run.ite_true hc r1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]; omega
    · simp [hr]
    · intro y hy; simp [hy]
    · rfl
    · rfl
    · rfl
  · have hc : (Cond.lt (V "ct1") (V "ct2")).evalB B σ = some false := by
      rw [evalB_condLt hv1 hv2]; simp [hlt]
    by_cases hgt : c2 < c1
    · have hc2 : (Cond.lt (V "ct2") (V "ct1")).evalB B σ = some true := by
        rw [evalB_condLt hv2 hv1]; simp [hgt]
      have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 0) (v := 0) hl0
      have hr : ¬ (c1 < c2 ∨ (c1 = c2 ∧ a ≤ b)) := by omega
      refine ⟨_, _, Run.ite_false hc (Run.ite_true hc2 r1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Expr.size, Cond.size]; omega
      · simp [hr]
      · intro y hy; simp [hy]
      · rfl
      · rfl
      · rfl
    · have hc2 : (Cond.lt (V "ct2") (V "ct1")).evalB B σ = some false := by
        rw [evalB_condLt hv2 hv1]; simp [hgt]
      have hc3 : (Cond.lt (V "sy") (V "sx")).evalB B σ = some (decide (b < a)) := by
        rw [evalB_condLt hvy hvx]
      by_cases hba : b < a
      · have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 0) (v := 0) hl0
        have hr : ¬ (c1 < c2 ∨ (c1 = c2 ∧ a ≤ b)) := by omega
        refine ⟨_, _, Run.ite_false hc (Run.ite_false hc2
          (Run.ite_true (by rw [hc3]; simp [hba]) r1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · simp [hr]
        · intro y hy; simp [hy]
        · rfl
        · rfl
        · rfl
      · have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 1) (v := 1) hl1
        have hr : c1 < c2 ∨ (c1 = c2 ∧ a ≤ b) := by omega
        refine ⟨_, _, Run.ite_false hc (Run.ite_false hc2
          (Run.ite_false (by rw [hc3]; simp [hba]) r1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · simp [hr]
        · intro y hy; simp [hy]
        · rfl
        · rfl
        · rfl

/-- What the due-date comparison needs of the state around the sort: the array `DS`. -/
def DBase (D : List ℕ) (σ : Env) : Prop := σ.arrs "DS" = D

theorem DBase_ok (D : List ℕ) : BaseOK (DBase D) := by
  intro σ σ' h _ ha
  unfold DBase at *
  rw [ha "DS" (by decide) (by decide)]; exact h

/-- The comparison of two positions by due date, as the sort's hook. -/
def dueCmpHook {B : ℕ} (hB : 1 < B) (D : List ℕ) (hDB : ∀ v ∈ D, v < B) :
    Cmp B (rDue D) (DBase D) where
  com := dueCmp
  cost := 90
  free := by decide
  good := fun v => v < D.length
  spec := fun a b haB hbB ha hb => by
    refine Spec.of_exists fun σ ⟨hbase, hsx, hsy⟩ => ?_
    have hbnd : ∀ t, t < D.length → D.getD t 0 < B := fun t ht =>
      hDB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
    obtain ⟨σ1, hr1, hct1, hct2, hfr1, harr1, hinp1, hout1⟩ :=
      (dueLoad_spec hB D hDB a b haB hbB ha hb).run ⟨hbase, hsx, hsy⟩
    obtain ⟨σ2, hr2, hsc, hfr2, harr2, hinp2, hout2⟩ :=
      (dueDecide_spec hB (D.getD a 0) (D.getD b 0) a b haB hbB (hbnd _ ha) (hbnd _ hb)).run
        ⟨hct1, hct2, by rw [hfr1 "sx" (by decide) (by decide)]; exact hsx,
          by rw [hfr1 "sy" (by decide) (by decide)]; exact hsy⟩
    refine ⟨σ2, _, (hr1.seq hr2).mono ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · unfold DBase; rw [harr2, harr1]; exact hbase
    · rw [hsc]; congr
    · intro y hy
      have h1 : y ≠ "ct1" := by rintro rfl; simp [SV] at hy
      have h2 : y ≠ "ct2" := by rintro rfl; simp [SV] at hy
      have h3 : y ≠ "sc" := by rintro rfl; simp [SV] at hy
      rw [hfr2 y h3, hfr1 y h1 h2]
    · rw [harr2, harr1]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]

/-- **The second sort**: `SA := [0, …, n − 1]`, then sorted by `(DS[a], a)`. -/
def dueSortCom : Com := .seq fillIdent (sortCom dueCmp)

theorem dueSort_spec {B : ℕ} (hB : 1 < B) (D : List ℕ) (n : ℕ) (hDl : D.length = n)
    (hDB : ∀ v ∈ D, v < B) (hnB : 3 * n + 3 < B) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ (σ.arrs "SA").length = n ∧ (σ.arrs "SB").length = n ∧
        σ.vars "sn" = n) dueSortCom
      (fun _ σ' => σ'.arrs "DS" = D ∧ (σ'.arrs "SA").Perm (List.range n) ∧
        (σ'.arrs "SA").Pairwise (rDue D))
      (((16 + 4) * n + 6) + sortK 90 n) := by
  let hC := dueCmpHook hB D hDB
  have hfill := fillIdent_spec (Base := DBase D) (DBase_ok D) hB n (by omega)
  refine Spec.of_exists fun σ ⟨hDS, hSAl, hSBl, hsn⟩ => ?_
  obtain ⟨σ1, hr1, hBase1, hSA1, hsn1, hSB1⟩ :=
    (hfill (σ.arrs "SB")).run ⟨hDS, hSAl, hsn, rfl⟩
  obtain ⟨σ2, hr2, hBase2, hperm, hsorted⟩ :=
    (sort_spec (rDue D) hC (DBase_ok D) hB (List.range n)
      (by simp; omega) (fun v hv => ⟨by simp at hv; omega, show v < D.length by
        simp at hv; omega⟩)).run
        ⟨hBase1, hSA1, by simp [hsn1], by rw [hSB1]; simpa using hSBl⟩
  have hr2' : Run B (sortCom dueCmp) σ1 σ2 (sortK 90 (List.range n).length) := hr2
  refine ⟨σ2, ((16 + 4) * n + 6) + sortK 90 n, (Run.seq hr1 hr2').mono ?_, le_rfl, hBase2, hperm,
    hsorted⟩
  simp only [List.length_range]; exact le_rfl

/-- A list sorted by `rDue D`, without repeats, is strictly increasing in the lexicographic
order of `(f k, k)`, whenever `f` agrees with `D` on its entries. -/
theorem pairwise_lex_of_rDue {D : List ℕ} {L : List ℕ} (hnd : L.Nodup)
    (hL : L.Pairwise (rDue D)) (f : ℕ → ℕ) (hf : ∀ k ∈ L, D.getD k 0 = f k) :
    L.Pairwise (fun a b => f a < f b ∨ (f a = f b ∧ a < b)) := by
  have h := hnd.and hL
  refine h.imp_of_mem ?_
  intro a b ha hb ⟨hne, hr⟩
  rw [← hf a ha, ← hf b hb]
  unfold rDue at hr
  omega

/-! ## The sorted weight array -/

/-- Fill `WS` from the decoded instance in `A` (fourth block, offset `3n`) and the sort's
permutation in `SA`. -/
def buildW : Com :=
  .seq (.assign "boff" (.bin .mul (.lit 3) (V "sn"))) (buildRow "WS")

theorem buildW_spec {B : ℕ} (hB : 1 < B) (A P WS0 : List ℕ) (n : ℕ)
    (hPl : P.length = n) (hPn : ∀ k < n, P.getD k 0 < n) (hAlen : 3 * n + n ≤ A.length)
    (hAB : ∀ v ∈ A, v < B) (hnB : 4 * n + 3 < B) (hWS0 : WS0.length = n) :
    Spec B (fun σ => σ.arrs "SA" = P ∧ σ.arrs "A" = A ∧ σ.vars "sn" = n ∧
        σ.arrs "WS" = WS0) buildW
      (fun _ σ' => σ'.arrs "WS" = (List.range n).map (fun k => A.getD (3 * n + P.getD k 0) 0) ∧
        σ'.arrs "SA" = P ∧ σ'.arrs "A" = A ∧ σ'.vars "sn" = n)
      (4 + ((20 + 4) * n + 6)) := by
  refine Spec.of_exists fun σ ⟨hSA, hA, hsn, hWS⟩ => ?_
  have hl3 : (Expr.lit 3).evalB B σ = some 3 := evalB_lit (by omega)
  have hvn : (V "sn").evalB B σ = some n :=
    hsn ▸ evalB_var (B := B) (σ := σ) (x := "sn") (by rw [hsn]; omega)
  have h3n : 3 * n < B := by omega
  have hidx : (Expr.bin Bop.mul (Expr.lit 3) (V "sn")).evalB B σ = some (3 * n) :=
    evalB_bin hl3 hvn h3n
  have r1 := Run.assign (B := B) (σ := σ) (x := "boff") (e := .bin .mul (.lit 3) (V "sn"))
    (v := 3 * n) hidx
  set σ1 : Env := σ.setVar "boff" (3 * n) with hσ1
  obtain ⟨σ2, hr2, ⟨hWS2, hSA2, hA2, hsn2, hboff2⟩, -, -, -, -⟩ :=
    (buildRow_spec hB "WS" (by decide) A P WS0 n (3 * n) hPl hPn hAlen hAB (by omega)
      (by omega) hWS0).frame.run (σ := σ1) ⟨by simp [hσ1, hSA], by simp [hσ1, hA],
      by simp [hσ1, hsn], by simp [hσ1], by simp [hσ1, hWS]⟩
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, hWS2, hSA2, hA2, hsn2⟩
  simp only [Expr.size]; omega

/-- The weights read through the permutation are `wv` of the permuted instance. -/
theorem sortedW_eq {I : Instance} {A : List ℕ}
    (hAw : ∀ j (hj : j < I.jobs), A.getD (3 * I.jobs + j) 0 = I.w ⟨j, hj⟩)
    (P : List ℕ) (hperm : P.Perm (List.range I.jobs)) :
    (List.range I.jobs).map (fun k => A.getD (3 * I.jobs + P.getD k 0) 0) =
      (List.range I.jobs).map (fun k => wv (permute I (listEquiv I.jobs P hperm)) k) := by
  have hPlen : P.length = I.jobs := by rw [hperm.length_eq]; simp
  have hPk : ∀ k, k < I.jobs → P.getD k 0 < I.jobs := by
    intro k hk
    have hkP : k < P.length := by omega
    have : P.getD k 0 ∈ P := by
      rw [List.getD_eq_getElem _ _ hkP]; exact List.getElem_mem hkP
    have := hperm.mem_iff.mp this
    simpa using this
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  have heq : (listEquiv I.jobs P hperm ⟨k, hk⟩ : Fin I.jobs) = ⟨P.getD k 0, hPk k hk⟩ :=
    Fin.ext (listEquiv_apply I.jobs P hperm ⟨k, hk⟩)
  have hwv : wv (permute I (listEquiv I.jobs P hperm)) k
      = I.w (listEquiv I.jobs P hperm ⟨k, hk⟩) := dif_pos hk
  rw [hwv, heq]
  exact hAw _ (hPk k hk)

end Lax496464Proofs.Ram.W3Front
