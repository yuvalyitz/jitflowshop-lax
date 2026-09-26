import Lax496464Proofs.Ram.Nxt1
import Mathlib.Data.Nat.Size

/-!
# Theorem 2's machine, part 4: the array `NX` in `O(n log n)`

`Nxt1.nxtLoop` fills `NX` by a scan per job, `O(n²)` in all — too slow for Theorem 2 when `m = 1`,
whose bound only leaves `O(n log n)` besides the table.  Start times are nondecreasing, so
`Fails D Q j x` (job `x` starts at or after `d j`) is monotone in `x` on `x > j`, and the first
failing `x` is found by binary search.  The result is stated as `Nxt1.Res`, so `Nxt1.res_isNxt`
applies unchanged.
-/

namespace Lax496464Proofs.Ram.D2Bsearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Nxt1 (Fails Res)

/-- One step of the search. -/
def bsBody : Com :=
  .seq (.assign "bm" (.bin .div (.bin .add (V "bl") (V "bh")) (.lit 2)))
    (.seq (.assign "ex" (.get "DS" (V "bm")))
      (.seq (.assign "qx" (.get "QS" (V "bm")))
        (.seq (.assign "tt" (.bin .add (V "dj") (V "qx")))
          (.ite (.lt (V "ex") (V "tt"))
            (.assign "bl" (.bin .add (V "bm") (.lit 1)))
            (.assign "bh" (V "bm"))))))

theorem bsBody_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n dj bl bh : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (_hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : 2 * n + 1 < B)
    (hlt : bl < bh) (hhn : bh ≤ n) (hdjB : dj < B) (hdjq : ∀ b, b < n → dj + Q.getD b 0 < B) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = dj ∧ σ.vars "bl" = bl ∧
        σ.vars "bh" = bh) bsBody
      (fun σ σ' => σ'.arrs "DS" = D ∧ σ'.arrs "QS" = Q ∧ σ'.vars "dj" = dj ∧
        (∀ y, y ≠ "bm" → y ≠ "ex" → y ≠ "qx" → y ≠ "tt" → y ≠ "bl" → y ≠ "bh" →
          σ'.vars y = σ.vars y) ∧
        (if D.getD ((bl + bh) / 2) 0 < dj + Q.getD ((bl + bh) / 2) 0
          then σ'.vars "bl" = (bl + bh) / 2 + 1 ∧ σ'.vars "bh" = bh
          else σ'.vars "bl" = bl ∧ σ'.vars "bh" = (bl + bh) / 2)) 40 := by
  have hmid : (bl + bh) / 2 < n := by omega
  have hDm : D.getD ((bl + bh) / 2) 0 < B := hDB _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hQm : Q.getD ((bl + bh) / 2) 0 < B := hQB _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hs := hdjq _ hmid
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hD, hQ, hdj, hbl, hbh⟩ := hσ
  have hDl : (bl + bh) / 2 < (σ.arrs "DS").length := by rw [hD]; omega
  have hQl : (bl + bh) / 2 < (σ.arrs "QS").length := by rw [hQ]; omega
  have hDg : (σ.arrs "DS").getD ((bl + bh) / 2) 0 = D.getD ((bl + bh) / 2) 0 := by rw [hD]
  have hQg : (σ.arrs "QS").getD ((bl + bh) / 2) 0 = Q.getD ((bl + bh) / 2) 0 := by rw [hQ]
  run_vcg
  all_goals (simp_all)

/-- The whole search for one job. -/
def bsLoop : Com := .while (.lt (V "bl") (V "bh")) bsBody

/-- What the search keeps. -/
def BInv (D Q : List ℕ) (n j dj : ℕ) (_hmono : True) (σ : Env) : Prop :=
  σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = dj ∧ j + 1 ≤ σ.vars "bl" ∧
    σ.vars "bl" ≤ σ.vars "bh" ∧ σ.vars "bh" ≤ n ∧
    (∀ x, j < x → x < σ.vars "bl" → ¬ Fails D Q j x) ∧
    (∀ x, σ.vars "bh" ≤ x → x < n → Fails D Q j x)

theorem size_half_lt (g : ℕ) (hg : 0 < g) : (g / 2).size + 1 ≤ g.size := by
  have h1 : g < 2 ^ g.size := Nat.lt_size_self g
  have hs : 0 < g.size := Nat.size_pos.mpr hg
  obtain ⟨s, hs'⟩ : ∃ s, g.size = s + 1 := ⟨g.size - 1, by omega⟩
  rw [hs'] at h1 ⊢
  have : g / 2 < 2 ^ s := by rw [pow_succ] at h1; omega
  have := Nat.size_le.mpr this
  omega

theorem size_mono' {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size :=
  Nat.size_le.mpr (lt_of_le_of_lt h (Nat.lt_size_self b))

theorem bsLoop_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n j dj : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : 2 * n + 1 < B)
    (hdjB : dj < B) (hdjq : ∀ b, b < n → dj + Q.getD b 0 < B) (hj : j < n)
    (hdj : dj = D.getD j 0)
    (hmono : ∀ x y, j < x → x ≤ y → y < n → Fails D Q j x → Fails D Q j y) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = dj ∧
        σ.vars "bl" = j + 1 ∧ σ.vars "bh" = n) bsLoop
      (fun _σ σ' => σ'.arrs "DS" = D ∧ σ'.arrs "QS" = Q ∧ σ'.vars "dj" = dj ∧
        Res D Q n j n (σ'.vars "bl"))
      (44 * n.size + 4) := by
  classical
  have hdef : ∀ σ, BInv D Q n j dj trivial σ →
      ∃ v, (Cond.lt (V "bl") (V "bh")).evalB B σ = some v := by
    rintro σ ⟨-, -, -, -, hlh, hhn, -, -⟩
    exact evalB_condLt_vars (by omega) (by omega)
  have hstep : ∀ σ, BInv D Q n j dj trivial σ → (Cond.lt (V "bl") (V "bh")).evalB B σ = some true →
      ∃ σ' K, Run B bsBody σ σ' K ∧ BInv D Q n j dj trivial σ' ∧
        1 + (Cond.lt (V "bl") (V "bh")).size + K +
          (fun σ : Env => 44 * (σ.vars "bh" - σ.vars "bl").size) σ' ≤
        (fun σ : Env => 44 * (σ.vars "bh" - σ.vars "bl").size) σ := by
    intro σ hI hv
    obtain ⟨hD, hQ, hdjσ, hjl, hlh, hhn, hlo, hhi⟩ := hI
    have hlt := lt_of_condLt_true hv
    obtain ⟨σ', hrun, ⟨hD', hQ', hdj', -, hcase⟩, -, -, -, -⟩ :=
      (bsBody_spec hB D Q n dj (σ.vars "bl") (σ.vars "bh") hlenD hlenQ hDB hQB hsum hnB hlt hhn
        hdjB hdjq).frame.run ⟨hD, hQ, hdjσ, rfl, rfl⟩
    set mid := (σ.vars "bl" + σ.vars "bh") / 2 with hmid
    have hmidn : mid < n := by omega
    have hjm : j < mid := by omega
    have hsz : (Cond.lt (V "bl") (V "bh")).size = 3 := rfl
    have hgap : 0 < σ.vars "bh" - σ.vars "bl" := by omega
    have hhalf := size_half_lt _ hgap
    have hFm : Fails D Q j mid ↔ ¬ (D.getD mid 0 < dj + Q.getD mid 0) := by
      unfold Fails; rw [hdj]
    by_cases hc : D.getD mid 0 < dj + Q.getD mid 0
    · rw [if_pos hc] at hcase
      obtain ⟨hbl', hbh'⟩ := hcase
      refine ⟨σ', 40, hrun, ⟨hD', hQ', hdj', by omega, by omega, by omega, ?_, ?_⟩, ?_⟩
      · intro x hx1 hx2
        rw [hbl'] at hx2
        intro hf
        by_cases hxm : x = mid
        · subst hxm; exact (hFm.mp hf) hc
        · have := hmono x mid hx1 (by omega) hmidn hf
          exact (hFm.mp this) hc
      · intro x hx1 hx2; rw [hbh'] at hx1; exact hhi x hx1 hx2
      · show 1 + 3 + 40 + 44 * (σ'.vars "bh" - σ'.vars "bl").size ≤ 44 * (σ.vars "bh" - σ.vars "bl").size
        rw [hbl', hbh']
        have h1 : σ.vars "bh" - (mid + 1) ≤ (σ.vars "bh" - σ.vars "bl") / 2 := by omega
        have := size_mono' h1
        omega
    · rw [if_neg hc] at hcase
      obtain ⟨hbl', hbh'⟩ := hcase
      have hfm : Fails D Q j mid := by rw [hFm]; exact hc
      refine ⟨σ', 40, hrun, ⟨hD', hQ', hdj', by omega, by omega, by omega, ?_, ?_⟩, ?_⟩
      · intro x hx1 hx2; rw [hbl'] at hx2; exact hlo x hx1 hx2
      · intro x hx1 hx2
        rw [hbh'] at hx1
        exact hmono mid x hjm hx1 hx2 hfm
      · show 1 + 3 + 40 + 44 * (σ'.vars "bh" - σ'.vars "bl").size ≤ 44 * (σ.vars "bh" - σ.vars "bl").size
        rw [hbl', hbh']
        have h1 : mid - σ.vars "bl" ≤ (σ.vars "bh" - σ.vars "bl") / 2 := by omega
        have := size_mono' h1
        omega
  have hloop := Spec.while_potential (B := B) (b := Cond.lt (V "bl") (V "bh")) (c := bsBody)
    (P := fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = dj ∧
        σ.vars "bl" = j + 1 ∧ σ.vars "bh" = n)
    (K := 44 * n.size + 4) (BInv D Q n j dj trivial)
    (fun σ : Env => 44 * (σ.vars "bh" - σ.vars "bl").size) hdef hstep
    (by
      rintro σ ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, by omega, by omega, by omega, ?_, ?_⟩
      · intro x hx1 hx2; omega
      · intro x hx1 hx2; omega)
    (by
      rintro σ ⟨h1, h2, h3, h4, h5⟩
      show 44 * (σ.vars "bh" - σ.vars "bl").size + 1 + (Cond.lt (V "bl") (V "bh")).size ≤ _
      have : (Cond.lt (V "bl") (V "bh")).size = 3 := rfl
      have := size_mono' (show σ.vars "bh" - σ.vars "bl" ≤ n by omega)
      omega)
  refine hloop.post ?_
  rintro σ σ' - ⟨⟨hD, hQ, hdjσ, hjl, hlh, hhn, hlo, hhi⟩, hfalse⟩
  have hle := le_of_condLt_false hfalse
  have heq : σ'.vars "bl" = σ'.vars "bh" := by omega
  refine ⟨hD, hQ, hdjσ, ?_⟩
  by_cases hn' : σ'.vars "bl" = n
  · exact Or.inl ⟨hn', fun x hx1 hx2 => hlo x hx1 (by omega)⟩
  · refine Or.inr ⟨by omega, by omega, by omega, ?_, fun x hx1 hx2 => hlo x hx1 hx2⟩
    exact hhi _ (by omega) (by omega)


open Lax496464Proofs.Ram.Nxt1 (NXInv)
open Lax496464Proofs.Ram.ListUtil

/-- Set up the search for job `sj`, run it, store the answer. -/
def nxBody : Com :=
  .seq (.assign "dj" (.get "DS" (V "sj")))
    (.seq (.assign "bl" (.bin .add (V "sj") (.lit 1)))
      (.seq (.assign "bh" (V "sn"))
        (.seq bsLoop (.seq (.store "NX" (V "sj") (V "bl")) (bump "sj")))))

/-- The cost of `nxBody`. -/
def nxBodyCost (n : ℕ) : ℕ := 40 + (44 * n.size + 4) + 20

theorem nxBody_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : 2 * n + 1 < B)
    (hmono : ∀ j, j < n → ∀ x y, j < x → x ≤ y → y < n → Fails D Q j x → Fails D Q j y) :
    Spec B (fun σ => NXInv D Q n σ ∧ σ.vars "sj" < n) nxBody
      (fun σ σ' => NXInv D Q n σ' ∧ σ'.vars "sj" = σ.vars "sj" + 1) (nxBodyCost n) := by
  refine Spec.of_exists fun σ ⟨⟨hD, hQ, hsn, hNXl, hsjn, hinv⟩, hlt⟩ => ?_
  set j := σ.vars "sj" with hj
  have hjD : j < D.length := by omega
  have hgetB : ∀ t, t < D.length → D.getD t 0 < B := fun t ht =>
    hDB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  have hvj : (V "sj").evalB B σ = some j := evalB_var (B := B) (σ := σ) (x := "sj") (by omega)
  have hg : (Expr.get "DS" (V "sj")).evalB B σ = some (D.getD j 0) := by
    have := RunStep.eval_get B σ "DS" (V "sj") j hvj (by rw [hD]; exact hjD)
      (by rw [hD]; exact hgetB _ hjD)
    rwa [hD] at this
  have r1 := Run.assign (B := B) (σ := σ) (x := "dj") (e := .get "DS" (V "sj"))
    (v := D.getD j 0) hg
  set σ1 : Env := σ.setVar "dj" (D.getD j 0) with hσ1
  have hvj1 : (V "sj").evalB B σ1 = some j := by
    have : σ1.vars "sj" = j := by simp [hσ1, hj]
    exact this ▸ evalB_var (B := B) (σ := σ1) (x := "sj") (by rw [this]; omega)
  have hl1 : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit hB
  have r2 := Run.assign (B := B) (σ := σ1) (x := "bl") (e := .bin .add (V "sj") (.lit 1))
    (v := j + 1) (evalB_bin hvj1 hl1 (by show j + 1 < B; omega))
  set σ2 : Env := σ1.setVar "bl" (j + 1) with hσ2
  have hvsn2 : (V "sn").evalB B σ2 = some n := by
    have : σ2.vars "sn" = n := by simp [hσ2, hσ1, hsn]
    exact this ▸ evalB_var (B := B) (σ := σ2) (x := "sn") (by rw [this]; omega)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "bh") (e := V "sn") (v := n) hvsn2
  set σ3 : Env := σ2.setVar "bh" n with hσ3
  have hD3 : σ3.arrs "DS" = D := by simp [hσ3, hσ2, hσ1, hD]
  have hQ3 : σ3.arrs "QS" = Q := by simp [hσ3, hσ2, hσ1, hQ]
  have hdjq : ∀ b, b < n → D.getD j 0 + Q.getD b 0 < B := fun b hb => hsum j b hlt hb
  obtain ⟨σ4, hr4, ⟨hD4, hQ4, hdj4, hres4⟩, hfv4, hfa4, -, -⟩ :=
    (bsLoop_spec hB D Q n j (D.getD j 0) hlenD hlenQ hDB hQB hsum hnB (hgetB j hjD) hdjq hlt rfl
      (hmono j hlt)).frame.run (σ := σ3)
      ⟨hD3, hQ3, by simp [hσ3, hσ2, hσ1], by simp [hσ3, hσ2, hj], by simp [hσ3]⟩
  have hresB : σ4.vars "bl" < B := by
    rcases hres4 with ⟨he, -⟩ | ⟨hlt', -, -, -, -⟩ <;> omega
  have hsj4 : σ4.vars "sj" = j := by
    rw [hfv4 "sj" (by decide)]; simp [hσ3, hσ2, hσ1, hj]
  have hNX4 : σ4.arrs "NX" = σ.arrs "NX" := by
    rw [hfa4 "NX" (by decide)]; simp [hσ3, hσ2, hσ1]
  have hvj4 : (V "sj").evalB B σ4 = some j := hsj4 ▸ evalB_var (B := B) (σ := σ4) (x := "sj")
    (by rw [hsj4]; omega)
  have hvres4 : (V "bl").evalB B σ4 = some (σ4.vars "bl") := evalB_var (B := B) (σ := σ4)
    (x := "bl") hresB
  have hNXl4 : j < (σ4.arrs "NX").length := by rw [hNX4]; omega
  have r5 := Run.store (B := B) (σ := σ4) (a := "NX") (i := V "sj") (e := V "bl")
    (idx := j) (v := σ4.vars "bl") hvj4 hvres4 hNXl4
  set σ5 : Env := σ4.setArr "NX" j (σ4.vars "bl") with hσ5
  have hsj5 : σ5.vars "sj" = j := by simp [hσ5, hsj4]
  have hvsj5 : (V "sj").evalB B σ5 = some j := hsj5 ▸ evalB_var (B := B) (σ := σ5) (x := "sj")
    (by rw [hsj5]; omega)
  have r6 := Run.assign (B := B) (σ := σ5) (x := "sj") (e := .bin .add (V "sj") (.lit 1))
    (v := j + 1) (evalB_bin hvsj5 (evalB_lit hB) (by show j + 1 < B; omega))
  set σ6 : Env := σ5.setVar "sj" (j + 1) with hσ6
  have hsn4 : σ4.vars "sn" = n := by
    rw [hfv4 "sn" (by decide)]; simp [hσ3, hσ2, hσ1, hsn]
  refine ⟨σ6, nxBodyCost n, (r1.seq (r2.seq (r3.seq (hr4.seq (r5.seq r6))))).mono ?_, le_rfl, ?_, ?_⟩
  · simp only [Expr.size, nxBodyCost]; omega
  · refine ⟨by simp [hσ6, hσ5, hD4], by simp [hσ6, hσ5, hQ4], by simp [hσ6, hσ5, hsn4],
      by simp [hσ6, hσ5, hNX4, hNXl], by simp [hσ6]; omega, ?_⟩
    intro j' hj'
    have hsj6 : σ6.vars "sj" = j + 1 := by simp [hσ6]
    rw [hsj6] at hj'
    rcases Nat.lt_or_ge j' j with hj'' | hj''
    · have := hinv j' hj''
      simp only [hσ6, hσ5, arrs_setVar, arrs_setArr, if_true]
      rw [getD_set_ne _ _ _ _ (by omega), hNX4]
      exact this
    · have : j' = j := by omega
      subst this
      simp only [hσ6, hσ5, arrs_setVar, arrs_setArr, if_true]
      rw [getD_set_self _ _ _ hNXl4]
      exact hres4
  · simp [hσ6]

/-- `NX` for every job. -/
def nxLoop : Com := .seq (.assign "sj" (.lit 0)) (.while (.lt (V "sj") (V "sn")) nxBody)

theorem nxLoop_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : 2 * n + 1 < B)
    (hmono : ∀ j, j < n → ∀ x y, j < x → x ≤ y → y < n → Fails D Q j x → Fails D Q j y) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "sn" = n ∧
        (σ.arrs "NX").length = n) nxLoop
      (fun _ σ' => σ'.arrs "DS" = D ∧ σ'.arrs "QS" = Q ∧ σ'.vars "sn" = n ∧
        ∀ j < n, Res D Q n j n ((σ'.arrs "NX").getD j 0))
      (2 + ((nxBodyCost n + 4) * n + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := nxBody) "sj" "sn" (NXInv D Q n) n
    (nxBodyCost n) (by omega) (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.1)
    (nxBody_spec hB D Q n hlenD hlenQ hDB hQB hsum hnB hmono)
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨hD, hQ, hsn, hNXl⟩
    exact ⟨by simpa using hD, by simpa using hQ, by simpa using hsn, by simpa using hNXl,
      by simp, by simp⟩
  · rintro σ σ' - ⟨hI, hsj⟩
    exact ⟨hI.1, hI.2.1, hI.2.2.1, fun j hj => hI.2.2.2.2.2 j (by omega)⟩

end Lax496464Proofs.Ram.D2Bsearch
