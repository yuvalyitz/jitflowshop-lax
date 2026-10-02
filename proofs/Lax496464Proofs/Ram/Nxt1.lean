import Lax496464Proofs.Ram.Cols1

/-!
# The Paper's `j₂` for Every Job, by Scanning

`nxt j` is the first job after `j` whose second operation starts at or after `d j` — that is,
the first `x > j` with `d j + q x ≤ d x` — or `n` if there is none. For each `j` the machine
scans `x = j+1, …, n−1` once, remembering the first failure; that is `O(n²)` steps in all and
needs no early exit, which keeps the loop invariant a plain description of what has been seen.
-/

namespace Lax496464Proofs.Ram.Nxt1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.ListUtil

/-- Job `x` starts at or after `d j`: the scan's stopping test, in natural numbers. -/
def Fails (D Q : List ℕ) (j x : ℕ) : Prop := ¬ (D.getD x 0 < D.getD j 0 + Q.getD x 0)

instance decFails (D Q : List ℕ) (j x : ℕ) : Decidable (Fails D Q j x) := by
  unfold Fails; infer_instance

/-- `res` is the first failing `x` among `j + 1 … ny − 1`, or `n` if none of them fails. -/
def Res (D Q : List ℕ) (n j ny res : ℕ) : Prop :=
  (res = n ∧ ∀ x, j < x → x < ny → ¬ Fails D Q j x) ∨
  (res < n ∧ j < res ∧ res < ny ∧ Fails D Q j res ∧ ∀ x, j < x → x < res → ¬ Fails D Q j x)

/-- One step of the scan. -/
def scanBody : Com :=
  .seq (.assign "dy" (.get "DS" (V "ny")))
    (.seq (.assign "qy" (.get "QS" (V "ny")))
      (.seq (.assign "tt" (.bin .add (V "dj") (V "qy")))
        (.seq (.ite (.lt (V "dy") (V "tt")) .skip
            (.ite (.eq (V "res") (V "sn")) (.assign "res" (V "ny")) .skip))
          (bump "ny"))))

theorem Res.base (D Q : List ℕ) (n j : ℕ) : Res D Q n j (j + 1) n :=
  Or.inl ⟨rfl, fun x hx1 hx2 => absurd hx2 (by omega)⟩

theorem Res.step {D Q : List ℕ} {n j ny res : ℕ} (h : Res D Q n j ny res) (hlt : ny < n)
    (hj : j < ny) :
    Res D Q n j (ny + 1) (if Fails D Q j ny then (if res = n then ny else res) else res) := by
  by_cases hf : Fails D Q j ny
  · rw [if_pos hf]
    by_cases hr : res = n
    · rw [if_pos hr]
      refine Or.inr ⟨hlt, hj, by omega, hf, fun x hx1 hx2 => ?_⟩
      rcases h with ⟨he, hall⟩ | ⟨hn, -, -, -, -⟩
      · exact hall x hx1 hx2
      · omega
    · rw [if_neg hr]
      rcases h with ⟨he, -⟩ | ⟨hn, hj', hlt', hfr, hall⟩
      · exact absurd he hr
      · exact Or.inr ⟨hn, hj', by omega, hfr, hall⟩
  · rw [if_neg hf]
    rcases h with ⟨he, hall⟩ | ⟨hn, hj', hlt', hfr, hall⟩
    · refine Or.inl ⟨he, fun x hx1 hx2 => ?_⟩
      rcases Nat.lt_or_ge x ny with h' | h'
      · exact hall x hx1 h'
      · have hx : x = ny := by omega
        subst hx; exact hf
    · exact Or.inr ⟨hn, hj', by omega, hfr, hall⟩

/-! ## The scan, on the machine -/

theorem scanBody_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n j ny res : ℕ)
    (hnyD : ny < D.length) (hnyQ : ny < Q.length) (hjD : j < D.length)
    (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B) (hsum : D.getD j 0 + Q.getD ny 0 < B)
    (hresB : res < B) (hnB : n < B) (hnyB : ny + 1 < B) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = D.getD j 0 ∧
        σ.vars "sn" = n ∧ σ.vars "ny" = ny ∧ σ.vars "res" = res) scanBody
      (fun σ σ' => σ'.vars "res" =
          (if Fails D Q j ny then (if res = n then ny else res) else res) ∧
        σ'.vars "ny" = ny + 1 ∧ σ'.arrs = σ.arrs ∧
        (∀ y, y ≠ "dy" → y ≠ "qy" → y ≠ "tt" → y ≠ "res" → y ≠ "ny" → σ'.vars y = σ.vars y) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  have hdy : D.getD ny 0 < B := hDB _ (by
    rw [List.getD_eq_getElem _ _ hnyD]; exact List.getElem_mem hnyD)
  have hqy : Q.getD ny 0 < B := hQB _ (by
    rw [List.getD_eq_getElem _ _ hnyQ]; exact List.getElem_mem hnyQ)
  refine Spec.pre (P := fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧
      σ.vars "dj" = D.getD j 0 ∧ σ.vars "sn" = n ∧ σ.vars "ny" = ny ∧ σ.vars "res" = res ∧
      ny < (σ.arrs "DS").length ∧ ny < (σ.arrs "QS").length ∧
      (σ.arrs "DS").getD ny 0 < B ∧ (σ.arrs "QS").getD ny 0 < B ∧
      D.getD j 0 + (σ.arrs "QS").getD ny 0 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [Env.setVar, Fails,
      List.getD_eq_getElem?_getD] at *)
    all_goals (try simp_all)
  · rintro σ ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, h6, by rw [h1]; omega, by rw [h2]; omega, ?_, ?_, ?_⟩
    · rw [h1]; exact hdy
    · rw [h2]; exact hqy
    · rw [h2]; exact hsum

/-! ## The scan for one job, on the machine -/

/-- Scan `j + 1 … n − 1` for the first failing entry. -/
def scanLoop : Com :=
  .seq (.assign "ny" (.bin .add (V "sj") (.lit 1)))
    (.seq (.assign "res" (V "sn")) (.while (.lt (V "ny") (V "sn")) scanBody))

/-- The invariant of the scan: `res` names the first failure seen so far, or `n` if none. -/
def SI (D Q : List ℕ) (n j : ℕ) (σ : Env) : Prop :=
  σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = D.getD j 0 ∧ σ.vars "sn" = n ∧
  j < σ.vars "ny" ∧ σ.vars "ny" ≤ n ∧ Res D Q n j (σ.vars "ny") (σ.vars "res")

theorem scanLoop_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n j : ℕ) (hjn : j < n)
    (hlen : D.length = n) (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ x, x < n → D.getD j 0 + Q.getD x 0 < B) (hnB : n + 1 < B) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = D.getD j 0 ∧
        σ.vars "sn" = n ∧ σ.vars "sj" = j) scanLoop
      (fun _ σ' => Res D Q n j n (σ'.vars "res") ∧ σ'.vars "dj" = D.getD j 0 ∧
        σ'.vars "sn" = n ∧ σ'.arrs "DS" = D ∧ σ'.arrs "QS" = Q)
      (10 + ((60 + 4) * (n - (j + 1)) + 4)) := by
  have hbody : Spec B (fun σ => SI D Q n j σ ∧ σ.vars "ny" < n) scanBody
      (fun σ σ' => SI D Q n j σ' ∧ σ'.vars "ny" = σ.vars "ny" + 1) 60 := by
    refine Spec.of_exists fun σ ⟨⟨hD, hQ, hdj, hsn, hj1, hnyn, hres⟩, hlt⟩ => ?_
    have hresn : σ.vars "res" ≤ n := by
      rcases hres with ⟨he, -⟩ | ⟨hlt', -, -, -, -⟩ <;> omega
    obtain ⟨σ', hr, hres', hny', harr, hfr, hinp, hout⟩ :=
      (scanBody_spec hB D Q n j (σ.vars "ny") (σ.vars "res") (by omega)
        (by omega) (by omega) hDB hQB (hsum _ (by omega))
        (by omega) (by omega) (by omega)).run ⟨hD, hQ, hdj, hsn, rfl, rfl⟩
    refine ⟨σ', 60, hr, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hny'⟩
    · rw [harr]; exact hD
    · rw [harr]; exact hQ
    · rw [hfr "dj" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hdj
    · rw [hfr "sn" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsn
    · omega
    · omega
    · rw [hres', hny']; exact hres.step hlt hj1
  have hloop := Spec.forRange (B := B)
    (P := fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "dj" = D.getD j 0 ∧
      σ.vars "sn" = n ∧ σ.vars "ny" = j + 1 ∧ σ.vars "res" = n)
    (c := scanBody) "ny" "sn" (SI D Q n j) n 60
    ((60 + 4) * (n - (j + 1)) + 4)
    (fun σ h => by have := h.2.2.2.2.2.1; omega) (fun σ h => by have := h.2.2.2.1; omega)
    (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.2.2.2.1) hbody
    (fun σ ⟨hD, hQ, hdj, hsn, hny, hres⟩ =>
      ⟨hD, hQ, hdj, hsn, by omega, by omega, by rw [hny, hres]; exact Res.base D Q n j⟩)
    (fun σ ⟨_, _, _, _, hny, _⟩ => by rw [hny])
  have hassign1 : Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧
      σ.vars "dj" = D.getD j 0 ∧ σ.vars "sn" = n ∧ σ.vars "sj" = j) (.assign "ny" (.bin .add (V "sj") (.lit 1)))
      (fun σ σ' => σ' = σ.setVar "ny" (j + 1)) (1 + 3) := by
    refine Spec.assign fun σ ⟨_, _, _, _, hsj⟩ => ?_
    exact evalB_bin (hsj ▸ evalB_var (B := B) (σ := σ) (x := "sj") (by rw [hsj]; omega))
      (evalB_lit (by omega)) (by show j + 1 < B; omega)
  have hassign2 : Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧
      σ.vars "dj" = D.getD j 0 ∧ σ.vars "sn" = n ∧ σ.vars "ny" = j + 1) (.assign "res" (V "sn"))
      (fun σ σ' => σ' = σ.setVar "res" (σ.vars "sn")) 2 :=
    Spec.assign fun σ ⟨_, _, _, hsn, _⟩ =>
      hsn ▸ evalB_var (B := B) (σ := σ) (x := "sn") (by rw [hsn]; omega)
  refine Spec.of_exists fun σ ⟨hD, hQ, hdj, hsn, hsj⟩ => ?_
  obtain ⟨σ1, hr1, hσ1⟩ := hassign1.run ⟨hD, hQ, hdj, hsn, hsj⟩
  subst hσ1
  obtain ⟨σ2, hr2, hσ2⟩ := hassign2.run
    (σ := σ.setVar "ny" (j + 1)) ⟨by simpa using hD, by simpa using hQ, by simpa using hdj,
      by simpa using hsn, by simp⟩
  have hσ2' : σ2 = (σ.setVar "ny" (j + 1)).setVar "res" n := by rw [hσ2]; simp [hsn]
  subst hσ2'
  obtain ⟨σ3, hr3, hI3, hny3⟩ := hloop.run (σ := (σ.setVar "ny" (j + 1)).setVar "res" n)
    ⟨by simpa using hD, by simpa using hQ, by simpa using hdj, by simpa using hsn, by simp, by simp⟩
  refine ⟨σ3, 10 + ((60 + 4) * (n - (j + 1)) + 4), (hr1.seq (hr2.seq hr3)).mono ?_, le_rfl, ?_⟩
  · omega
  · refine ⟨?_, hI3.2.2.1, hI3.2.2.2.1, hI3.1, hI3.2.1⟩
    have := hI3.2.2.2.2.2.2
    rwa [hny3] at this

/-! ## Tying the scan to the paper's `j₂` -/

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.Dp1 in
/-- Under earliest-start-time order and `q j > 0`, the scan's final result is the paper's
`j₂`, for any arrays that agree with the instance's due dates and processing times. -/
theorem res_isNxt {J : Instance} (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j)
    {j : ℕ} (h : j < J.jobs) (D Q : List ℕ) (hD : ∀ x < J.jobs, D.getD x 0 = dv J x)
    (hQ : ∀ x < J.jobs, Q.getD x 0 = qv J x) {res : ℕ} (hres : Res D Q J.jobs j J.jobs res) :
    IsNxt j h res := by
  have hqj : 0 < J.q ⟨j, h⟩ := hq ⟨j, h⟩
  have hsjd : s (⟨j, h⟩ : J.Job) < (J.d ⟨j, h⟩ : ℤ) := by unfold s; omega
  have hFails : ∀ x, j < x → ∀ hxn : x < J.jobs,
      (Fails D Q j x ↔ (J.d ⟨j, h⟩ : ℤ) ≤ s (⟨x, hxn⟩ : J.Job)) := by
    intro x hjx hxn
    unfold Fails
    rw [hD x hxn, hD j h, hQ x hxn]
    unfold dv qv
    rw [dif_pos h, dif_pos hxn, dif_pos hxn]
    have : s (⟨x, hxn⟩ : J.Job) = (J.d ⟨x, hxn⟩ : ℤ) - J.q ⟨x, hxn⟩ := rfl
    omega
  have hbelow : ∀ x : J.Job, (x : ℕ) ≤ j → s x < (J.d ⟨j, h⟩ : ℤ) := by
    intro x hxj
    rcases eq_or_lt_of_le hxj with hxj' | hxj'
    · have : x = ⟨j, h⟩ := Fin.ext hxj'
      rw [this]; exact hsjd
    · have hle : x ≤ (⟨j, h⟩ : J.Job) := Fin.mk_le_mk.mpr (by omega)
      have := hest x ⟨j, h⟩ hle
      omega
  rcases hres with ⟨heq, hall⟩ | ⟨hlt, hjr, -, hfr, hall⟩
  · refine ⟨Or.inr heq, fun x hxy => ?_⟩
    rcases Nat.lt_or_ge (x : ℕ) (j + 1) with hxj | hxj
    · exact hbelow x (by omega)
    · have hxn := x.isLt
      have hnf := hall x (by omega) (by omega)
      rw [hFails x (by omega) hxn] at hnf
      show s (⟨(x : ℕ), hxn⟩ : J.Job) < (J.d ⟨j, h⟩ : ℤ)
      omega
  · refine ⟨Or.inl ⟨by omega, ?_⟩, fun x hxy => ?_⟩
    · have := hFails res hjr (by omega)
      rw [this] at hfr
      exact hfr
    · rcases Nat.lt_or_ge (x : ℕ) (j + 1) with hxj | hxj
      · exact hbelow x (by omega)
      · have hxn := x.isLt
        have hnf := hall x (by omega) (by omega)
        rw [hFails x (by omega) hxn] at hnf
        show s (⟨(x : ℕ), hxn⟩ : J.Job) < (J.d ⟨j, h⟩ : ℤ)
        omega

/-! ## Building the whole `NX` array -/

/-- Read `D[sj]` into `dj`, run the scan, store the result into `NX[sj]`, move on. -/
def nxtBody : Com :=
  .seq (.assign "dj" (.get "DS" (V "sj")))
    (.seq scanLoop (.seq (.store "NX" (V "sj") (V "res")) (bump "sj")))

/-- The cost of `nxtBody`, uniform in `sj`: the scan's cost at `sj = 0`, which dominates. -/
def nxtBodyCost (n : ℕ) : ℕ := 20 + (10 + ((60 + 4) * n + 4)) + 20 + 4

/-- What the array-building loop keeps: `NX[0, sj)` holds the scan's result for each of those
jobs, and nothing else has changed. -/
def NXInv (D Q : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "sn" = n ∧ (σ.arrs "NX").length = n ∧
  σ.vars "sj" ≤ n ∧ ∀ j < σ.vars "sj", Res D Q n j n ((σ.arrs "NX").getD j 0)

theorem nxtBody_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : n + 1 < B) :
    Spec B (fun σ => NXInv D Q n σ ∧ σ.vars "sj" < n) nxtBody
      (fun σ σ' => NXInv D Q n σ' ∧ σ'.vars "sj" = σ.vars "sj" + 1) (nxtBodyCost n) := by
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
  have hD1 : σ1.arrs "DS" = D := by simp [hσ1, hD]
  have hQ1 : σ1.arrs "QS" = Q := by simp [hσ1, hQ]
  have hdj1 : σ1.vars "dj" = D.getD j 0 := by simp [hσ1]
  have hsn1 : σ1.vars "sn" = n := by simp [hσ1, hsn]
  have hsj1 : σ1.vars "sj" = j := by simp [hσ1, hj]
  have hNX1 : σ1.arrs "NX" = σ.arrs "NX" := by simp [hσ1]
  obtain ⟨σ2, hr2, ⟨hres2, hdj2, hsn2, hD2, hQ2⟩, hfv2, hfa2, -, -⟩ :=
    (scanLoop_spec hB D Q n j hlt hlenD hlenQ hDB hQB (fun x hx => hsum j x hlt hx) hnB).frame.run
      (σ := σ1) ⟨hD1, hQ1, hdj1, hsn1, hsj1⟩
  have hresB : σ2.vars "res" < B := by
    rcases hres2 with ⟨he, -⟩ | ⟨hlt', -, -, -, -⟩ <;> omega
  have hjB' : j < B := by omega
  have hsj2 : σ2.vars "sj" = j := by rw [hfv2 "sj" (by decide), hsj1]
  have hNX2 : σ2.arrs "NX" = σ.arrs "NX" := by rw [hfa2 "NX" (by decide), hNX1]
  have hvj2 : (V "sj").evalB B σ2 = some j := hsj2 ▸ evalB_var (B := B) (σ := σ2) (x := "sj")
    (by rw [hsj2]; omega)
  have hvres2 : (V "res").evalB B σ2 = some (σ2.vars "res") := evalB_var (B := B) (σ := σ2)
    (x := "res") hresB
  have hNXl2 : j < (σ2.arrs "NX").length := by rw [hNX2]; omega
  have r2 := Run.store (B := B) (σ := σ2) (a := "NX") (i := V "sj") (e := V "res")
    (idx := j) (v := σ2.vars "res") hvj2 hvres2 hNXl2
  set σ3 : Env := σ2.setArr "NX" j (σ2.vars "res") with hσ3
  have hD3 : σ3.arrs "DS" = D := by simp [hσ3, hD2]
  have hQ3 : σ3.arrs "QS" = Q := by simp [hσ3, hQ2]
  have hsn3 : σ3.vars "sn" = n := by simp [hσ3, hsn2]
  have hsj3 : σ3.vars "sj" = j := by simp [hσ3, hsj2]
  have hNXl3 : (σ3.arrs "NX").length = n := by
    simp only [hσ3, arrs_setArr, if_true, List.length_set]
    rw [hNX2]; exact hNXl
  have hvsj3 : (V "sj").evalB B σ3 = some j := hsj3 ▸ evalB_var (B := B) (σ := σ3) (x := "sj")
    (by rw [hsj3]; omega)
  have hl1 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit hB
  have r3 := Run.assign (B := B) (σ := σ3) (x := "sj") (e := .bin .add (V "sj") (.lit 1))
    (v := j + 1) (evalB_bin hvsj3 hl1 (by show j + 1 < B; omega))
  set σ4 : Env := σ3.setVar "sj" (j + 1) with hσ4
  have hD4 : σ4.arrs "DS" = D := by simp [hσ4, hD3]
  have hQ4 : σ4.arrs "QS" = Q := by simp [hσ4, hQ3]
  have hsn4 : σ4.vars "sn" = n := by simp [hσ4, hsn3]
  have hNXl4 : (σ4.arrs "NX").length = n := by simp [hσ4, hNXl3]
  have hsj4 : σ4.vars "sj" = j + 1 := by simp [hσ4]
  refine ⟨σ4, nxtBodyCost n, (r1.seq (hr2.seq (r2.seq r3))).mono ?_, le_rfl, ?_, ?_⟩
  · simp only [Expr.size, nxtBodyCost]; omega
  · refine ⟨hD4, hQ4, hsn4, hNXl4, by rw [hsj4]; omega, ?_⟩
    intro j' hj'
    rw [hsj4] at hj'
    rcases Nat.lt_or_ge j' j with hj'' | hj''
    · have := hinv j' hj''
      simp only [hσ4, hσ3, arrs_setVar, arrs_setArr, if_true]
      rw [getD_set_ne _ _ _ _ (by omega), hNX2]
      exact this
    · have : j' = j := by omega
      subst this
      simp only [hσ4, hσ3, arrs_setVar, arrs_setArr, if_true]
      rw [getD_set_self _ _ _ hNXl2]
      exact hres2
  · rw [hsj4]

/-- **`NX`, built once for every job.** -/
def nxtLoop : Com :=
  .seq (.assign "sj" (.lit 0)) (.while (.lt (V "sj") (V "sn")) nxtBody)

theorem nxtLoop_spec {B : ℕ} (hB : 1 < B) (D Q : List ℕ) (n : ℕ) (hlenD : D.length = n)
    (hlenQ : Q.length = n) (hDB : ∀ v ∈ D, v < B) (hQB : ∀ v ∈ Q, v < B)
    (hsum : ∀ a b, a < n → b < n → D.getD a 0 + Q.getD b 0 < B) (hnB : n + 1 < B) :
    Spec B (fun σ => σ.arrs "DS" = D ∧ σ.arrs "QS" = Q ∧ σ.vars "sn" = n ∧
        (σ.arrs "NX").length = n) nxtLoop
      (fun _ σ' => σ'.arrs "DS" = D ∧ σ'.arrs "QS" = Q ∧ σ'.vars "sn" = n ∧
        ∀ j < n, Res D Q n j n ((σ'.arrs "NX").getD j 0))
      (2 + ((nxtBodyCost n + 4) * n + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := nxtBody) "sj" "sn" (NXInv D Q n) n
    (nxtBodyCost n) (by omega) (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.1)
    (nxtBody_spec hB D Q n hlenD hlenQ hDB hQB hsum hnB)
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨hD, hQ, hsn, hNXl⟩
    exact ⟨by simpa using hD, by simpa using hQ, by simpa using hsn, by simpa using hNXl,
      by simp, by simp⟩
  · rintro σ σ' - ⟨hI, hsj⟩
    exact ⟨hI.1, hI.2.1, hI.2.2.1, fun j hj => hI.2.2.2.2.2 j (by omega)⟩

end Lax496464Proofs.Ram.Nxt1
