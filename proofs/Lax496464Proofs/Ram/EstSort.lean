import Lax496464Proofs.Ram.Sort
import Lax496464.WordEncoding

/-!
# Putting the jobs of a word into earliest-start-time order

The word presents the jobs in an arbitrary order. The dynamic programs of Sections 3–6 index
their tables by the order of the start times `s j = d j − q j`, so every one of them begins by
sorting an array of job numbers under `s`, ties broken by the number. That is a total
preorder — in fact a total order on the numbers — and this file is the relation, the
comparison of two jobs as a machine command, and the sort of `0 … n−1` under it.
-/

namespace Lax496464Proofs.Ram.EstSort

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort

/-- The decoded instance: `A[j] = p_j`, `A[n+j] = q_j`, `A[2n+j] = d_j`, `A[3n+j] = w_j`. -/
def qA (A : List ℕ) (n a : ℕ) : ℕ := A.getD (n + a) 0
def dA (A : List ℕ) (n a : ℕ) : ℕ := A.getD (2 * n + a) 0

/-- Job `a` starts no later than job `b`, ties broken by the number:
`(s a, a) ≤ (s b, b)` lexicographically, with `s = d − q` and no subtraction. -/
def rEst (A : List ℕ) (n : ℕ) (a b : ℕ) : Prop :=
  dA A n a + qA A n b < dA A n b + qA A n a ∨
    (dA A n a + qA A n b = dA A n b + qA A n a ∧ a ≤ b)

instance (A : List ℕ) (n : ℕ) : DecidableRel (rEst A n) := fun a b => by
  unfold rEst; infer_instance

instance (A : List ℕ) (n : ℕ) : IsTrans ℕ (rEst A n) :=
  ⟨fun a b c hab hbc => by unfold rEst at *; omega⟩

instance (A : List ℕ) (n : ℕ) : Std.Total (rEst A n) :=
  ⟨fun a b => by unfold rEst; omega⟩

/-- The start times are nondecreasing along a list sorted by `rEst`. -/
theorem rEst_le {A : List ℕ} {n a b : ℕ} (h : rEst A n a b) :
    (dA A n a : ℤ) - qA A n a ≤ (dA A n b : ℤ) - qA A n b := by
  unfold rEst at h; omega

/-- The two sums the comparison is made on: `ct1 = d a + q b`, `ct2 = d b + q a`. -/
def estSums : Com :=
  .seq (.assign "ct1" (.bin .add (.get "A" (.bin .add (.bin .mul (.lit 2) (V "en")) (V "sx")))
      (.get "A" (.bin .add (V "en") (V "sy")))))
    (.assign "ct2" (.bin .add (.get "A" (.bin .add (.bin .mul (.lit 2) (V "en")) (V "sy")))
      (.get "A" (.bin .add (V "en") (V "sx")))))

/-- Decide from the two sums, and from the numbers on a tie. -/
def estDecide : Com :=
  .ite (.lt (V "ct1") (V "ct2")) (.assign "sc" (.lit 1))
    (.ite (.lt (V "ct2") (V "ct1")) (.assign "sc" (.lit 0))
      (.ite (.lt (V "sy") (V "sx")) (.assign "sc" (.lit 0)) (.assign "sc" (.lit 1))))

/-- Compare jobs `sx` and `sy`: `sc := 1` iff `rEst`. -/
def estCmp : Com := .seq estSums estDecide

theorem eval_idx2 {B : ℕ} {σ : Env} {n a : ℕ} (s : String) (hen : σ.vars "en" = n)
    (hs : σ.vars s = a) (h2 : 2 * n < B) (hn : n < B) (hna : 2 * n + a < B) (hB : 2 < B) :
    (Expr.bin .add (.bin .mul (.lit 2) (V "en")) (V s)).evalB B σ = some (2 * n + a) := by
  have hl : (Expr.lit 2).evalB B σ = some 2 := evalB_lit (by omega)
  have hv : (V "en").evalB B σ = some n := hen ▸ evalB_var (B := B) (σ := σ) (x := "en") (by rw [hen]; exact hn)
  have hm := evalB_bin (op := .mul) hl hv (by show 2 * n < B; exact h2)
  have hs' : (V s).evalB B σ = some a := hs ▸ evalB_var (B := B) (σ := σ) (x := s) (by rw [hs]; omega)
  exact evalB_bin hm hs' (by show 2 * n + a < B; exact hna)

theorem eval_idx1 {B : ℕ} {σ : Env} {n a : ℕ} (s : String) (hen : σ.vars "en" = n)
    (hs : σ.vars s = a) (hn : n < B) (hna : n + a < B) :
    (Expr.bin .add (V "en") (V s)).evalB B σ = some (n + a) := by
  have hv : (V "en").evalB B σ = some n := hen ▸ evalB_var (B := B) (σ := σ) (x := "en") (by rw [hen]; exact hn)
  have hs' : (V s).evalB B σ = some a := hs ▸ evalB_var (B := B) (σ := σ) (x := s) (by rw [hs]; omega)
  exact evalB_bin hv hs' (by show n + a < B; exact hna)

theorem eval_cell {B : ℕ} {σ : Env} {Aarr : List ℕ} {idx : Expr} {k : ℕ}
    (hidx : idx.evalB B σ = some k) (hA : σ.arrs "A" = Aarr) (hk : k < Aarr.length)
    (hv : Aarr.getD k 0 < B) : (Expr.get "A" idx).evalB B σ = some (Aarr.getD k 0) := by
  have := RunStep.eval_get B σ "A" idx k hidx (by rw [hA]; exact hk) (by rw [hA]; exact hv)
  rwa [hA] at this

theorem estSums_spec {B : ℕ} (hB : 1 < B) (Aarr : List ℕ) (n : ℕ) (hlen : Aarr.length = 4 * n)
    (hAB : ∀ v ∈ Aarr, v < B) (hnB : 3 * n < B)
    (hsum : ∀ a b, a < n → b < n → dA Aarr n a + qA Aarr n b < B) (a b : ℕ)
    (ha : a < n) (hb : b < n) :
    Spec B (fun σ => σ.arrs "A" = Aarr ∧ σ.vars "en" = n ∧ σ.vars "sx" = a ∧ σ.vars "sy" = b)
      estSums
      (fun σ σ' => σ'.vars "ct1" = dA Aarr n a + qA Aarr n b ∧
        σ'.vars "ct2" = dA Aarr n b + qA Aarr n a ∧
        (∀ y, y ≠ "ct1" → y ≠ "ct2" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  have h1 := hsum a b ha hb
  have h2 := hsum b a hb ha
  have hbnd : ∀ t, t < Aarr.length → Aarr.getD t 0 < B := fun t ht =>
    hAB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  refine Spec.of_exists fun σ ⟨hA, hen, hsx, hsy⟩ => ?_
  -- the first sum
  have g1 : (Expr.get "A" (.bin .add (.bin .mul (.lit 2) (V "en")) (V "sx"))).evalB B σ
      = some (Aarr.getD (2 * n + a) 0) :=
    eval_cell (eval_idx2 "sx" hen hsx (by omega) (by omega) (by omega) (by omega)) hA (by omega)
      (hbnd _ (by omega))
  have g2 : (Expr.get "A" (.bin .add (V "en") (V "sy"))).evalB B σ = some (Aarr.getD (n + b) 0) :=
    eval_cell (eval_idx1 "sy" hen hsy (by omega) (by omega)) hA (by omega) (hbnd _ (by omega))
  have v1 := evalB_bin (op := .add) g1 g2 (by show Aarr.getD (2 * n + a) 0 + Aarr.getD (n + b) 0 < B; exact h1)
  have ra := Run.assign (B := B) (σ := σ) (x := "ct1") (e := _) (v := _) v1
  set σ1 : Env := σ.setVar "ct1" _ with hσ1
  have hA1 : σ1.arrs "A" = Aarr := hA
  have hen1 : σ1.vars "en" = n := by simp [hσ1, hen]
  have hsx1 : σ1.vars "sx" = a := by simp [hσ1, hsx]
  have hsy1 : σ1.vars "sy" = b := by simp [hσ1, hsy]
  have g3 : (Expr.get "A" (.bin .add (.bin .mul (.lit 2) (V "en")) (V "sy"))).evalB B σ1
      = some (Aarr.getD (2 * n + b) 0) :=
    eval_cell (eval_idx2 "sy" hen1 hsy1 (by omega) (by omega) (by omega) (by omega)) hA1 (by omega)
      (hbnd _ (by omega))
  have g4 : (Expr.get "A" (.bin .add (V "en") (V "sx"))).evalB B σ1 = some (Aarr.getD (n + a) 0) :=
    eval_cell (eval_idx1 "sx" hen1 hsx1 (by omega) (by omega)) hA1 (by omega) (hbnd _ (by omega))
  have v2 := evalB_bin (op := .add) g3 g4 (by show Aarr.getD (2 * n + b) 0 + Aarr.getD (n + a) 0 < B; exact h2)
  have rb := Run.assign (B := B) (σ := σ1) (x := "ct2") (e := _) (v := _) v2
  refine ⟨_, _, (ra.seq rb).mono ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · simp [hσ1, dA, qA]
  · simp [hσ1, dA, qA]
  · intro y h1 h2; simp [hσ1, h1, h2]
  · simp [hσ1]
  · simp [hσ1]
  · simp [hσ1]

theorem estDecide_spec {B : ℕ} (hB : 1 < B) (Aarr : List ℕ) (n : ℕ) (a b : ℕ) (haB : a < B)
    (hbB : b < B) :
    Spec B (fun σ => σ.vars "ct1" = dA Aarr n a + qA Aarr n b ∧
        σ.vars "ct2" = dA Aarr n b + qA Aarr n a ∧ σ.vars "ct1" < B ∧ σ.vars "ct2" < B ∧
        σ.vars "sx" = a ∧ σ.vars "sy" = b) estDecide
      (fun σ σ' => σ'.vars "sc" = (if rEst Aarr n a b then 1 else 0) ∧
        (∀ y, y ≠ "sc" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 30 := by
  refine Spec.of_exists fun σ ⟨h1, h2, hb1, hb2, hsx, hsy⟩ => ?_
  have hv1 : (V "ct1").evalB B σ = some (σ.vars "ct1") := evalB_var (B := B) (σ := σ) (x := "ct1") hb1
  have hv2 : (V "ct2").evalB B σ = some (σ.vars "ct2") := evalB_var (B := B) (σ := σ) (x := "ct2") hb2
  have hvx : (V "sx").evalB B σ = some a := hsx ▸ evalB_var (B := B) (σ := σ) (x := "sx") (by rw [hsx]; exact haB)
  have hvy : (V "sy").evalB B σ = some b := hsy ▸ evalB_var (B := B) (σ := σ) (x := "sy") (by rw [hsy]; exact hbB)
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have fin : ∀ v : ℕ, ∀ K : ℕ, Run B (.assign "sc" (.lit v)) σ (σ.setVar "sc" v) K → True := fun _ _ _ => trivial
  by_cases hlt : σ.vars "ct1" < σ.vars "ct2"
  · have hc : (Cond.lt (V "ct1") (V "ct2")).evalB B σ = some true := by
      rw [evalB_condLt hv1 hv2]; simp [hlt]
    have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 1) (v := 1) hl1
    have hr : rEst Aarr n a b := Or.inl (by omega)
    refine ⟨_, _, Run.ite_true hc r1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.size, Cond.size]; omega
    · simp [hr]
    · intro y hy; simp [hy]
    · rfl
    · rfl
    · rfl
  · have hc : (Cond.lt (V "ct1") (V "ct2")).evalB B σ = some false := by
      rw [evalB_condLt hv1 hv2]; simp [hlt]
    by_cases hgt : σ.vars "ct2" < σ.vars "ct1"
    · have hc2 : (Cond.lt (V "ct2") (V "ct1")).evalB B σ = some true := by
        rw [evalB_condLt hv2 hv1]; simp [hgt]
      have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 0) (v := 0) hl0
      have hr : ¬ rEst Aarr n a b := by unfold rEst; omega
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
        have hr : ¬ rEst Aarr n a b := by unfold rEst; omega
        refine ⟨_, _, Run.ite_false hc (Run.ite_false hc2 (Run.ite_true (by rw [hc3]; simp [hba]) r1)),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · simp [hr]
        · intro y hy; simp [hy]
        · rfl
        · rfl
        · rfl
      · have r1 := Run.assign (B := B) (σ := σ) (x := "sc") (e := .lit 1) (v := 1) hl1
        have hr : rEst Aarr n a b := by unfold rEst; omega
        refine ⟨_, _, Run.ite_false hc (Run.ite_false hc2 (Run.ite_false (by rw [hc3]; simp [hba]) r1)),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Expr.size, Cond.size]; omega
        · simp [hr]
        · intro y hy; simp [hy]
        · rfl
        · rfl
        · rfl

/-- What the comparison needs of the state around the sort. -/
def EBase (Aarr : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.arrs "A" = Aarr ∧ σ.vars "en" = n

theorem EBase_ok (Aarr : List ℕ) (n : ℕ) : BaseOK (EBase Aarr n) := by
  intro σ σ' ⟨h1, h2⟩ hv ha
  refine ⟨by rw [ha "A" (by decide) (by decide)]; exact h1, ?_⟩
  rw [hv "en" (by simp [SV])]; exact h2

/-- The comparison of two jobs of the word, as the sort's hook. -/
def estCmpHook {B : ℕ} (hB : 1 < B) (Aarr : List ℕ) (n : ℕ) (hlen : Aarr.length = 4 * n)
    (hAB : ∀ v ∈ Aarr, v < B) (hnB : 3 * n < B)
    (hsum : ∀ a b, a < n → b < n → dA Aarr n a + qA Aarr n b < B) :
    Cmp B (rEst Aarr n) (EBase Aarr n) where
  com := estCmp
  cost := 90
  free := by decide
  good := fun v => v < n
  spec := fun a b haB hbB ha hb => by
    refine Spec.of_exists fun σ ⟨⟨hA, hen⟩, hsx, hsy⟩ => ?_
    obtain ⟨σ1, hr1, hct1, hct2, hfr1, harr1, hinp1, hout1⟩ :=
      (estSums_spec hB Aarr n hlen hAB hnB hsum a b ha hb).run ⟨hA, hen, hsx, hsy⟩
    have hs1 := hsum a b ha hb
    have hs2 := hsum b a hb ha
    obtain ⟨σ2, hr2, hsc, hfr2, harr2, hinp2, hout2⟩ :=
      (estDecide_spec hB Aarr n a b haB hbB).run
        ⟨hct1, hct2, by rw [hct1]; exact hs1, by rw [hct2]; exact hs2,
          by rw [hfr1 "sx" (by decide) (by decide)]; exact hsx,
          by rw [hfr1 "sy" (by decide) (by decide)]; exact hsy⟩
    refine ⟨σ2, _, (hr1.seq hr2).mono ?_, le_rfl, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · rw [harr2, harr1]; exact hA
    · rw [hfr2 "en" (by decide), hfr1 "en" (by decide) (by decide)]; exact hen
    · rw [hsc]; congr
    · intro y hy
      have h1 : y ≠ "ct1" := by rintro rfl; simp [SV] at hy
      have h2 : y ≠ "ct2" := by rintro rfl; simp [SV] at hy
      have h3 : y ≠ "sc" := by rintro rfl; simp [SV] at hy
      rw [hfr2 y h3, hfr1 y h1 h2]
    · rw [harr2, harr1]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]

/-- `SA := [0, 1, …, sn − 1]`. -/
def fillIdent : Com :=
  .seq (.assign "si" (.lit 0))
    (.while (.lt (V "si") (V "sn")) (.seq (.store "SA" (V "si") (V "si")) (bump "si")))

theorem fillIdent_spec {B : ℕ} {Base : Env → Prop} (hBO : BaseOK Base) (hB : 1 < B) (n : ℕ)
    (hnB : n < B) (SB0 : List ℕ) :
    Spec B (fun σ => Base σ ∧ (σ.arrs "SA").length = n ∧ σ.vars "sn" = n ∧
        σ.arrs "SB" = SB0) fillIdent
      (fun _ σ' => Base σ' ∧ σ'.arrs "SA" = List.range n ∧ σ'.vars "sn" = n ∧
        σ'.arrs "SB" = SB0) ((16 + 4) * n + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := .seq (.store "SA" (V "si") (V "si")) (bump "si"))
    "si" "sn"
    (fun σ => Base σ ∧ (σ.arrs "SA").length = n ∧ σ.vars "sn" = n ∧ σ.arrs "SB" = SB0 ∧
      σ.vars "si" ≤ n ∧ (σ.arrs "SA").take (σ.vars "si") = (List.range n).take (σ.vars "si"))
    n 16 hnB (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.1) (by
      refine Spec.of_exists fun σ ⟨⟨hBase, hSAl, hsn, hSB, hle, htk⟩, hlt⟩ => ?_
      have hvi : (V "si").evalB B σ = some (σ.vars "si") := evalB_var (B := B) (σ := σ) (x := "si") (by omega)
      have r1 := Run.store (B := B) (σ := σ) (a := "SA") (i := V "si") (e := V "si")
        (idx := σ.vars "si") (v := σ.vars "si") hvi hvi (by omega)
      set σa : Env := σ.setArr "SA" (σ.vars "si") (σ.vars "si") with hσa
      have hvia : (V "si").evalB B σa = some (σ.vars "si") := by
        have : σa.vars "si" = σ.vars "si" := by simp [hσa]
        exact this ▸ evalB_var (B := B) (σ := σa) (x := "si") (by rw [this]; omega)
      have hl1 : (Expr.lit 1).evalB B σa = some 1 := evalB_lit hB
      have r2 := Run.assign (B := B) (σ := σa) (x := "si") (e := .bin .add (V "si") (.lit 1))
        (v := σ.vars "si" + 1) (evalB_bin hvia hl1 (by show σ.vars "si" + 1 < B; omega))
      refine ⟨_, 16, (r1.seq r2).mono ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.size]; omega
      · exact hBO σ _ hBase (fun y hy => by
          have : y ≠ "si" := fun h => hy (by simp [SV, h])
          simp [hσa, this]) (fun a h1 h2 => by simp [hσa, h1])
      · simp [hσa, hSAl]
      · simp [hσa, hsn]
      · simp [hσa, hSB]
      · simp [hσa]; omega
      · simp only [hσa, arrs_setVar, arrs_setArr, vars_setVar, if_true]
        rw [take_set_succ _ (by omega), htk]
        have : (List.range n).take (σ.vars "si" + 1) = (List.range n).take (σ.vars "si") ++ [σ.vars "si"] := by
          rw [List.take_range, List.take_range, min_eq_left (by omega), min_eq_left (by omega),
            List.range_succ]
        rw [this]
      · simp [hσa])
  refine (hloop.conseq ?_ ?_ le_rfl)
  · rintro σ ⟨hBase, hSAl, hsn, hSB⟩
    refine ⟨hBO σ _ hBase (fun y hy => by
        have : y ≠ "si" := fun h => hy (by simp [SV, h])
        simp [this]) (fun a _ _ => rfl), by simpa using hSAl, by simpa using hsn,
      by simpa using hSB, by simp, by simp⟩
  · rintro σ σ' - ⟨⟨hBase, hSAl, hsn, hSB, hle, htk⟩, hsi⟩
    rw [hsi] at htk
    have hSA : σ'.arrs "SA" = List.range n := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp)] at htk
      exact htk
    exact ⟨hBase, hSA, hsn, hSB⟩

/-- **Sort the jobs of the word by start time.** -/
def estSortCom : Com := .seq fillIdent (sortCom estCmp)

theorem estSort_spec {B : ℕ} (hB : 1 < B) (Aarr : List ℕ) (n : ℕ) (hlen : Aarr.length = 4 * n)
    (hAB : ∀ v ∈ Aarr, v < B) (hnB : 3 * n + 3 < B)
    (hsum : ∀ a b, a < n → b < n → dA Aarr n a + qA Aarr n b < B) :
    Spec B (fun σ => EBase Aarr n σ ∧ (σ.arrs "SA").length = n ∧ (σ.arrs "SB").length = n ∧
        σ.vars "sn" = n) estSortCom
      (fun _ σ' => EBase Aarr n σ' ∧ (σ'.arrs "SA").Perm (List.range n) ∧
        (σ'.arrs "SA").Pairwise (rEst Aarr n))
      (((16 + 4) * n + 6) + sortK 90 n) := by
  let hC := estCmpHook hB Aarr n hlen hAB (by omega) hsum
  have hfill := fillIdent_spec (Base := EBase Aarr n) (EBase_ok Aarr n) hB n (by omega)
  refine Spec.of_exists fun σ ⟨hBase, hSAl, hSBl, hsn⟩ => ?_
  obtain ⟨σ1, hr1, hBase1, hSA1, hsn1, hSB1⟩ := (hfill (σ.arrs "SB")).run ⟨hBase, hSAl, hsn, rfl⟩
  obtain ⟨σ2, hr2, hBase2, hperm, hsorted⟩ :=
    (sort_spec (rEst Aarr n) hC (EBase_ok Aarr n) hB (List.range n)
      (by simp; omega) (fun v hv => ⟨by simp at hv; omega, show v < n by simp at hv; exact hv⟩)).run
        ⟨hBase1, hSA1, by simp [hsn1], by rw [hSB1]; simpa using hSBl⟩
  have hr2' : Run B (sortCom estCmp) σ1 σ2 (sortK 90 (List.range n).length) := hr2
  refine ⟨σ2, ((16 + 4) * n + 6) + sortK 90 n, (Run.seq hr1 hr2').mono ?_, le_rfl, hBase2, hperm,
    hsorted⟩
  simp only [List.length_range]; exact le_rfl

end Lax496464Proofs.Ram.EstSort
