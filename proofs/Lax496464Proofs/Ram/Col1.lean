import Lax496464Proofs.Ram.Dp1
import Lax496464Proofs.Ram.Sort
import Lax496464Proofs.Ram.ListUtil

/-!
# One column of the one-machine table, on the machine

`fCom` computes the recursion's second branch (`Dp1.fNat`) from the code of the entry it looks
up and the three numbers of the job, in natural numbers only; `colLoop` fills a column from the
end, each entry from the one after it and one entry of the previous column.
-/

namespace Lax496464Proofs.Ram.Col1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Dp1 Lax496464Proofs.Ram.ListUtil

/-- `cf := fNat cinf ct cd cq cp`. -/
def fCom : Com :=
  .ite (.eq (V "ct") (.lit 0)) (.assign "cf" (.lit 0))
    (.ite (.eq (V "ct") (V "cinf"))
      (.seq (.assign "cw" (.bin .add (V "cp") (V "cq")))
        (.ite (.lt (V "cd") (V "cw")) (.assign "cf" (.lit 0))
          (.assign "cf" (.bin .add (.bin .sub (.bin .sub (V "cd") (V "cq")) (V "cp")) (.lit 1)))))
      (.seq (.assign "cw" (.bin .add (V "cp") (V "cq")))
        (.ite (.lt (V "cd") (V "cw")) (.assign "cf" (.lit 0))
          (.seq (.assign "cw" (.bin .add (V "cp") (.lit 1)))
            (.ite (.lt (V "ct") (V "cw")) (.assign "cf" (.lit 0))
              (.seq (.assign "ce" (.bin .sub (.bin .sub (V "ct") (.lit 1)) (V "cp")))
                (.seq (.assign "cg" (.bin .sub (.bin .sub (V "cd") (V "cq")) (V "cp")))
                  (.ite (.lt (V "ce") (V "cg"))
                    (.assign "cf" (.bin .add (V "ce") (.lit 1)))
                    (.assign "cf" (.bin .add (V "cg") (.lit 1)))))))))))

theorem fCom_spec {B : ℕ} (hB : 2 < B) (inf t d q p : ℕ) (hinfB : inf < B) (htB : t < B)
    (_hdB : d < B) (hqB : q < B) (hpB : p < B) (hsum : p + q < B) (hd1 : d + 1 < B) :
    Spec B (fun σ => σ.vars "cinf" = inf ∧ σ.vars "ct" = t ∧ σ.vars "cd" = d ∧
        σ.vars "cq" = q ∧ σ.vars "cp" = p) fCom
      (fun σ σ' => σ'.vars "cf" = fNat inf t d q p ∧
        (∀ y, y ≠ "cf" → y ≠ "cw" → y ≠ "ce" → y ≠ "cg" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  unfold fNat
  run_vcg
  all_goals (simp_all)
  all_goals (try omega)

/-- The data a column computation reads. -/
structure Dat (B inf n : ℕ) (NX PS QS DS PC : List ℕ) : Prop where
  lenP : PS.length = n
  lenQ : QS.length = n
  lenD : DS.length = n
  lenN : NX.length = n
  lenC : PC.length = n + 1
  nxt : ∀ j, j < n → j < NX.getD j 0 ∧ NX.getD j 0 ≤ n
  bP : ∀ j, j < n → PS.getD j 0 < B
  bQ : ∀ j, j < n → QS.getD j 0 < B
  bD : ∀ j, j < n → DS.getD j 0 < B
  sum : ∀ j, j < n → PS.getD j 0 + QS.getD j 0 < B
  infd : ∀ j, j < n → DS.getD j 0 + 1 < inf
  bC : ∀ t, t ≤ n → PC.getD t 0 ≤ inf
  infB : inf < B
  two : 2 < B
  nB : n + 1 < B

/-- The column being computed, as the function it should end up being. -/
def cst (n inf : ℕ) (NX PS QS DS PC : List ℕ) : ℕ → ℕ :=
  colStep n inf (fun j => NX.getD j 0) (fun j => PS.getD j 0) (fun j => QS.getD j 0)
    (fun j => DS.getD j 0) (fun t => PC.getD t 0)

theorem fNat_le (inf t d q p : ℕ) : fNat inf t d q p ≤ d + 1 := by
  unfold fNat
  split_ifs <;> omega

theorem cst_le {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (hd : Dat B inf n NX PS QS DS PC) :
    ∀ t, cst n inf NX PS QS DS PC t ≤ inf := by
  intro t
  induction' hk : n - t using Nat.strong_induction_on with k ih generalizing t
  by_cases h : n ≤ t
  · unfold cst; rw [colStep_of_le h]; omega
  · unfold cst
    rw [colStep_of_lt (by omega)]
    have h1 := ih (n - (t + 1)) (by omega) (t + 1) rfl
    have h2 := fNat_le inf (PC.getD (NX.getD t 0) 0) (DS.getD t 0) (QS.getD t 0) (PS.getD t 0)
    have h3 := hd.infd t (by omega)
    exact max_le h1 (by omega)

/-- Fetch the numbers of job `j = n − 1 − i` and the entry of the previous column it looks up. -/
def colFetch : Com :=
  .seq (.assign "cj" (.bin .sub (.bin .sub (V "sn") (.lit 1)) (V "ci")))
    (.seq (.assign "cy" (.get "NX" (V "cj")))
      (.seq (.assign "ct" (.get "PC" (V "cy")))
        (.seq (.assign "cp" (.get "PS" (V "cj")))
          (.seq (.assign "cq" (.get "QS" (V "cj")))
            (.assign "cd" (.get "DS" (V "cj")))))))

theorem colFetch_spec {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (hd : Dat B inf n NX PS QS DS PC)
    (i : ℕ) (hi : i < n) :
    Spec B (fun σ => σ.arrs "NX" = NX ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧ σ.arrs "DS" = DS ∧
        σ.arrs "PC" = PC ∧ σ.vars "sn" = n ∧ σ.vars "ci" = i) colFetch
      (fun σ σ' => σ'.vars "cj" = n - 1 - i ∧ σ'.vars "cy" = NX.getD (n - 1 - i) 0 ∧
        σ'.vars "ct" = PC.getD (NX.getD (n - 1 - i) 0) 0 ∧ σ'.vars "cp" = PS.getD (n - 1 - i) 0 ∧
        σ'.vars "cq" = QS.getD (n - 1 - i) 0 ∧ σ'.vars "cd" = DS.getD (n - 1 - i) 0 ∧
        (∀ y, y ≠ "cj" → y ≠ "cy" → y ≠ "ct" → y ≠ "cp" → y ≠ "cq" → y ≠ "cd" →
          σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  have hj : n - 1 - i < n := by omega
  have hn := hd.nxt _ hj
  have hgb : ∀ (L : List ℕ) (t : ℕ), t < L.length → (∀ v ∈ L, v < B) → L.getD t 0 < B :=
    fun L t ht hL => hL _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  have hPS := hd.bP _ hj
  have hQS := hd.bQ _ hj
  have hDS := hd.bD _ hj
  have hCb : PC.getD (NX.getD (n - 1 - i) 0) 0 ≤ inf := hd.bC _ hn.2
  have hI := hd.infB
  have hnB := hd.nB
  have hlP := hd.lenP
  have hlQ := hd.lenQ
  have hlD := hd.lenD
  have hlN := hd.lenN
  have hlC := hd.lenC
  have hNXB : NX.getD (n - 1 - i) 0 < B := by omega
  have hnx1 := hn.1
  have hnx2 := hn.2
  clear hd hn hgb
  run_vcg
  all_goals (simp_all)
  all_goals omega

/-- Store `max (CC[j+1], f)` at `CC[j]` and move the counter on. -/
def colStore : Com :=
  .seq (.assign "cn" (.get "CC" (.bin .add (V "cj") (.lit 1))))
    (.seq (.ite (.lt (V "cn") (V "cf")) (.assign "cn" (V "cf")) .skip)
      (.seq (.store "CC" (V "cj") (V "cn")) (bump "ci")))

theorem colStore_spec {B : ℕ} (hB : 1 < B) (CCl : List ℕ) (j f i : ℕ) (hj : j + 1 < CCl.length)
    (hnb : CCl.getD (j + 1) 0 < B) (hfB : f < B) (hjB : j + 1 < B) (hiB : i + 1 < B) :
    Spec B (fun σ => σ.arrs "CC" = CCl ∧ σ.vars "cj" = j ∧ σ.vars "cf" = f ∧ σ.vars "ci" = i)
      colStore
      (fun σ σ' => σ'.arrs "CC" = CCl.set j (max (CCl.getD (j + 1) 0) f) ∧ σ'.vars "ci" = i + 1 ∧
        (∀ y, y ≠ "cn" → y ≠ "ci" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "CC" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 40 := by
  run_vcg
  all_goals (simp_all)
  all_goals (try omega)
  all_goals (rw [Nat.max_eq_right (by omega)])

/-- One entry of the column, from the end. -/
def colBody : Com := .seq colFetch (.seq fCom colStore)

/-- The invariant of the column loop, after `ci` entries. -/
def CI (inf n : ℕ) (NX PS QS DS PC : List ℕ) (σ : Env) : Prop :=
  σ.arrs "NX" = NX ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧ σ.arrs "DS" = DS ∧
  σ.arrs "PC" = PC ∧ σ.vars "sn" = n ∧ σ.vars "cinf" = inf ∧ (σ.arrs "CC").length = n + 1 ∧
  σ.vars "ci" ≤ n ∧
  ∀ t, t ≤ n → n ≤ t + σ.vars "ci" → (σ.arrs "CC").getD t 0 = cst n inf NX PS QS DS PC t

theorem colBody_spec {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (hd : Dat B inf n NX PS QS DS PC) :
    Spec B (fun σ => CI inf n NX PS QS DS PC σ ∧ σ.vars "ci" < n) colBody
      (fun σ σ' => CI inf n NX PS QS DS PC σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1) 160 := by
  have hB1 : 1 < B := by have := hd.two; omega
  refine Spec.of_exists fun σ ⟨⟨hNX, hPS, hQS, hDS, hPC, hsn, hinf, hCCl, hci, hinv⟩, hlt⟩ => ?_
  set i := σ.vars "ci" with hi
  have hj : n - 1 - i < n := by omega
  obtain ⟨σ1, hr1, hcj, hcy, hct, hcp, hcq, hcd, hfr1, harr1, hinp1, hout1⟩ :=
    (colFetch_spec hd i hlt).run ⟨hNX, hPS, hQS, hDS, hPC, hsn, rfl⟩
  have hn := hd.nxt _ hj
  have hCb : PC.getD (NX.getD (n - 1 - i) 0) 0 ≤ inf := hd.bC _ hn.2
  have hI := hd.infB
  have hs1 := hd.sum _ hj
  have hd1 := hd.infd _ hj
  have hbD := hd.bD _ hj
  have hbQ := hd.bQ _ hj
  have hbP := hd.bP _ hj
  obtain ⟨σ2, hr2, hcf, hfr2, harr2, hinp2, hout2⟩ :=
    (fCom_spec hd.two inf (PC.getD (NX.getD (n - 1 - i) 0) 0) (DS.getD (n - 1 - i) 0)
      (QS.getD (n - 1 - i) 0) (PS.getD (n - 1 - i) 0) hI (by omega) hbD hbQ hbP hs1
      (by omega)).run
      ⟨by rw [hfr1 "cinf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinf,
        hct, hcd, hcq, hcp⟩
  have hfN : fNat inf (PC.getD (NX.getD (n - 1 - i) 0) 0) (DS.getD (n - 1 - i) 0)
      (QS.getD (n - 1 - i) 0) (PS.getD (n - 1 - i) 0) ≤ DS.getD (n - 1 - i) 0 + 1 := fNat_le _ _ _ _ _
  have hCC2 : σ2.arrs "CC" = σ.arrs "CC" := by rw [harr2, harr1]
  have hcj2 : σ2.vars "cj" = n - 1 - i := by
    rw [hfr2 "cj" (by decide) (by decide) (by decide) (by decide)]; exact hcj
  have hci2 : σ2.vars "ci" = i := by
    rw [hfr2 "ci" (by decide) (by decide) (by decide) (by decide),
      hfr1 "ci" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hcstle := cst_le hd (n - 1 - i + 1)
  have hjCC := hinv (n - 1 - i + 1) (by omega) (by omega)
  obtain ⟨σ3, hr3, hCC3, hci3, hfr3, harr3, hinp3, hout3⟩ :=
    (colStore_spec (B := B) hB1 (σ.arrs "CC") (n - 1 - i)
      (fNat inf (PC.getD (NX.getD (n - 1 - i) 0) 0) (DS.getD (n - 1 - i) 0)
        (QS.getD (n - 1 - i) 0) (PS.getD (n - 1 - i) 0)) i (by omega)
      (by rw [hjCC]; omega) (by omega) (by have := hd.nB; omega) (by have := hd.nB; omega)).run
      (σ := σ2)
      ⟨hCC2, hcj2, hcf, hci2⟩
  have hrest : ∀ a, a ≠ "CC" → σ3.arrs a = σ.arrs a := fun a ha => by
    rw [harr3 a ha, harr2, harr1]
  have hvar : ∀ y, y ≠ "cn" → y ≠ "ci" → y ≠ "cf" → y ≠ "cw" → y ≠ "ce" → y ≠ "cg" →
      y ≠ "cj" → y ≠ "cy" → y ≠ "ct" → y ≠ "cp" → y ≠ "cq" → y ≠ "cd" →
      σ3.vars y = σ.vars y := fun y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
    rw [hfr3 y h1 h2, hfr2 y h3 h4 h5 h6, hfr1 y h7 h8 h9 h10 h11 h12]
  refine ⟨σ3, _, (hr1.seq (hr2.seq hr3)).mono ?_, le_rfl, ?_, ?_⟩
  · omega
  · refine ⟨by rw [hrest _ (by decide)]; exact hNX, by rw [hrest _ (by decide)]; exact hPS,
      by rw [hrest _ (by decide)]; exact hQS, by rw [hrest _ (by decide)]; exact hDS,
      by rw [hrest _ (by decide)]; exact hPC,
      by rw [hvar "sn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsn,
      by rw [hvar "cinf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinf,
      by rw [hCC3, List.length_set]; exact hCCl, by rw [hci3]; omega, ?_⟩
    intro t ht hnt
    rw [hci3] at hnt
    rw [hCC3]
    by_cases htj : t = n - 1 - i
    · subst htj
      rw [getD_set_self _ _ _ (by omega), hjCC]
      unfold cst
      rw [colStep_of_lt (show n - 1 - i < n by omega)]
    · rw [getD_set_ne _ _ _ _ htj]
      exact hinv t ht (by omega)
  · exact hci3

/-- **A whole column**: the last entry is `0`, then the rest from the end. -/
def colCol : Com :=
  .seq (.store "CC" (V "sn") (.lit 0))
    (.seq (.assign "ci" (.lit 0)) (.while (.lt (V "ci") (V "sn")) colBody))

theorem colCol_spec {B inf n : ℕ} {NX PS QS DS PC : List ℕ} (hd : Dat B inf n NX PS QS DS PC) :
    Spec B (fun σ => σ.arrs "NX" = NX ∧ σ.arrs "PS" = PS ∧ σ.arrs "QS" = QS ∧ σ.arrs "DS" = DS ∧
        σ.arrs "PC" = PC ∧ σ.vars "sn" = n ∧ σ.vars "cinf" = inf ∧ (σ.arrs "CC").length = n + 1)
      colCol
      (fun _ σ' => σ'.arrs "NX" = NX ∧ σ'.arrs "PS" = PS ∧ σ'.arrs "QS" = QS ∧
        σ'.arrs "DS" = DS ∧ σ'.arrs "PC" = PC ∧ σ'.vars "sn" = n ∧ σ'.vars "cinf" = inf ∧
        (σ'.arrs "CC").length = n + 1 ∧
        ∀ t, t ≤ n → (σ'.arrs "CC").getD t 0 = cst n inf NX PS QS DS PC t)
      (2 + (1 + 1) + ((160 + 4) * n + 6)) := by
  have hB1 : 1 < B := by have := hd.two; omega
  have hloop := Spec.forRangeZero (B := B) (c := colBody) "ci" "sn"
    (fun σ => CI inf n NX PS QS DS PC σ) n 160 (by have := hd.nB; omega)
    (fun σ h => h.2.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.2.1) (colBody_spec hd)
  refine Spec.of_exists fun σ ⟨hNX, hPS, hQS, hDS, hPC, hsn, hinf, hCCl⟩ => ?_
  have hvn : (V "sn").evalB B σ = some n := hsn ▸ evalB_var (B := B) (σ := σ) (x := "sn")
    (by rw [hsn]; have := hd.nB; omega)
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.store (B := B) (σ := σ) (a := "CC") (i := V "sn") (e := .lit 0) (idx := n)
    (v := 0) hvn hl0 (by rw [hCCl]; omega)
  set σ1 : Env := σ.setArr "CC" n 0 with hσ1
  have hl0' : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
  obtain ⟨σ3, hr3, ⟨hNX3, hPS3, hQS3, hDS3, hPC3, hsn3, hinf3, hCC3, hci3, hinv3⟩, hci⟩ :=
    hloop σ1 ⟨by simp [hσ1, hNX], by simp [hσ1, hPS], by simp [hσ1, hQS], by simp [hσ1, hDS],
      by simp [hσ1, hPC], by simp [hσ1, hsn], by simp [hσ1, hinf],
      by simp [hσ1, hCCl], by simp,
      fun t ht hnt => by
        have htn : t = n := by simp at hnt; omega
        subst htn
        simp only [hσ1, arrs_setVar, arrs_setArr, if_true]
        rw [getD_set_self _ _ _ (by omega)]
        unfold cst; rw [colStep_of_le le_rfl]⟩
  refine ⟨σ3, _, ((r1.seq hr3)).mono ?_, le_rfl, hNX3, hPS3, hQS3, hDS3, hPC3, hsn3, hinf3, hCC3, ?_⟩
  · simp only [Expr.size]; omega
  · intro t ht; exact hinv3 t ht (by omega)

end Lax496464Proofs.Ram.Col1
