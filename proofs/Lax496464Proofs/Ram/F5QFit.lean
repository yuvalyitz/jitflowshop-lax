import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.ListUtil
import Lax496464Proofs.Ram.Q3Init

/-!
# Theorem 5 (profile sweep): the fit pass

`fitCom` zeroes the weight of every unfit job (`p + q > d`) in the sorted array `WS` and leaves in
the scalar `wm` the largest weight that is left (`w_max'`).
-/

namespace Lax496464Proofs.Ram.F5QFit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.Q3Init (foldr_max_take_succ foldr_max_lt')

abbrev V (s : String) : Expr := .var s

theorem getq_set (l : List ℕ) (t v j : ℕ) (ht : t < l.length) :
    (l.set t v)[j]?.getD 0 = if j = t then v else l[j]?.getD 0 := by
  by_cases h : j = t
  · subst h; rw [if_pos rfl, List.getElem?_set_self ht]; rfl
  · rw [if_neg h, List.getElem?_set_ne (Ne.symm h)]

/-- One turn: zero `WS[i]` if unfit, fold it into `wm`. -/
def fitBody : Com :=
  .seq (.ite (.lt (.get "DS" (V "i")) (.bin .add (.get "PS" (V "i")) (.get "QS" (V "i"))))
      (.store "WS" (V "i") (.lit 0)) .skip)
    (.seq (.assign "u1" (.get "WS" (V "i")))
      (.seq (.ite (.lt (V "wm") (V "u1")) (.assign "wm" (V "u1")) .skip)
        (.assign "i" (.bin .add (V "i") (.lit 1)))))

def fitCom : Com :=
  .seq (.assign "wm" (.lit 0)) (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) fitBody))

/-- The new weight of job `k`. -/
def fitVal (P Q D Wl : List ℕ) (k : ℕ) : ℕ :=
  if D.getD k 0 < P.getD k 0 + Q.getD k 0 then 0 else Wl.getD k 0

/-- The weights after the pass. -/
def fitArr (P Q D Wl : List ℕ) (n : ℕ) : List ℕ := (List.range n).map (fitVal P Q D Wl)

/-- The loop invariant. -/
def FitInv (P Q D Wl : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "PS" = P ∧ σ.arrs "QS" = Q ∧ σ.arrs "DS" = D ∧
  σ.vars "i" ≤ n ∧ (σ.arrs "WS").length = n ∧
  (∀ j, (σ.arrs "WS").getD j 0 = if j < σ.vars "i" then fitVal P Q D Wl j else Wl.getD j 0) ∧
  σ.vars "wm" = (((fitArr P Q D Wl n)).take (σ.vars "i")).foldr max 0

theorem fitBody_spec {B n : ℕ} (P Q D Wl : List ℕ) (hB : 1 < B)
    (hP : P.length = n) (hQ : Q.length = n) (hD : D.length = n) (hW : Wl.length = n)
    (hnB : n < B) (hpq : ∀ k < n, P.getD k 0 + Q.getD k 0 < B)
    (hwB : ∀ k < n, Wl.getD k 0 < B) (hdB : ∀ k < n, D.getD k 0 < B) :
    Spec B (fun σ => FitInv P Q D Wl n σ ∧ σ.vars "i" < n) fitBody
      (fun σ σ' => FitInv P Q D Wl n σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  intro σ ⟨⟨hn, hPs, hQs, hDs, hi, hWl, hWg, hwm⟩, hlt⟩
  have hiB : σ.vars "i" + 1 < B := by omega
  have hPl : (σ.arrs "PS").length = n := by rw [hPs]; exact hP
  have hQl : (σ.arrs "QS").length = n := by rw [hQs]; exact hQ
  have hDl : (σ.arrs "DS").length = n := by rw [hDs]; exact hD
  have hg := hWg (σ.vars "i")
  have hfv : ∀ k < n, fitVal P Q D Wl k < B := fun k hk => by
    unfold fitVal; split_ifs
    · omega
    · exact hwB k hk
  have hfA : ∀ v ∈ fitArr P Q D Wl n, v < B := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    exact hfv k (List.mem_range.mp hk)
  have hwmB : σ.vars "wm" < B := by
    rw [hwm]; exact foldr_max_lt' (by omega) (fun v hv => hfA v (List.mem_of_mem_take hv))
  have hfl : (fitArr P Q D Wl n).length = n := by simp [fitArr]
  have htake := foldr_max_take_succ (fitArr P Q D Wl n) (σ.vars "i") (by omega)
  have hfget : (fitArr P Q D Wl n).getD (σ.vars "i") 0 = fitVal P Q D Wl (σ.vars "i") := by
    simp only [fitArr]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]; rfl
  have hPg : (σ.arrs "PS").getD (σ.vars "i") 0 = P.getD (σ.vars "i") 0 := by rw [hPs]
  have hQg : (σ.arrs "QS").getD (σ.vars "i") 0 = Q.getD (σ.vars "i") 0 := by rw [hQs]
  have hDg : (σ.arrs "DS").getD (σ.vars "i") 0 = D.getD (σ.vars "i") 0 := by rw [hDs]
  have hWlen : σ.vars "i" < (σ.arrs "WS").length := by omega
  have hpq' := hpq _ hlt
  have hwB' := hwB _ hlt
  have hDB := hdB _ hlt
  have hWget : (σ.arrs "WS").getD (σ.vars "i") 0 = Wl.getD (σ.vars "i") 0 := by
    rw [hg, if_neg (by omega)]
  run_vcg
  all_goals simp only [FitInv, Env.setVar, Env.setArr] at *
  all_goals simp [getq_set _ _ _ _ hWlen] at *
  all_goals first
    | omega
    | skip
  all_goals simp only [hPg, hQg, hDg] at *
  · -- unfit
    have hz : fitVal P Q D Wl (σ.vars "i") = 0 := by
      unfold fitVal; simp only [List.getD_eq_getElem?_getD]; rw [if_pos (by assumption)]
    refine ⟨hn, hPs, hQs, hDs, by omega, hWl, ?_, ?_⟩
    · intro j
      by_cases hj : j = σ.vars "i"
      · rw [hj]; simp [hz]
      · rw [if_neg hj, hWg j]
        by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
    · rw [htake, hfget, hz, ← hwm]; simp
  · have hf1 : fitVal P Q D Wl (σ.vars "i") = Wl[σ.vars "i"]?.getD 0 := by
      unfold fitVal; simp only [List.getD_eq_getElem?_getD]; rw [if_neg (by omega)]
    refine ⟨hn, hPs, hQs, hDs, by omega, hWl, ?_, ?_⟩
    · intro j
      rw [hWg j]
      by_cases hj : j = σ.vars "i"
      · rw [hj, hf1]; simp
      · by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
    · rw [htake, hfget, hf1, ← hwm]; omega
  · have hf1 : fitVal P Q D Wl (σ.vars "i") = Wl[σ.vars "i"]?.getD 0 := by
      unfold fitVal; simp only [List.getD_eq_getElem?_getD]; rw [if_neg (by omega)]
    refine ⟨hn, hPs, hQs, hDs, by omega, hWl, ?_, ?_⟩
    · intro j
      rw [hWg j]
      by_cases hj : j = σ.vars "i"
      · rw [hj, hf1]; simp
      · by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
    · rw [htake, hfget, hf1, ← hwm]; omega

/-- **The fit pass.**  `WS` becomes `fitArr` and `wm` its largest entry. -/
theorem fitCom_spec {B n : ℕ} (P Q D Wl : List ℕ) (hB : 1 < B)
    (hP : P.length = n) (hQ : Q.length = n) (hD : D.length = n) (hW : Wl.length = n)
    (hnB : n < B) (hpq : ∀ k < n, P.getD k 0 + Q.getD k 0 < B)
    (hwB : ∀ k < n, Wl.getD k 0 < B) (hdB : ∀ k < n, D.getD k 0 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "PS" = P ∧ σ.arrs "QS" = Q ∧ σ.arrs "DS" = D ∧
        σ.arrs "WS" = Wl) fitCom
      (fun _ σ' => σ'.arrs "WS" = fitArr P Q D Wl n ∧
        σ'.vars "wm" = (fitArr P Q D Wl n).foldr max 0) (44 * n + 10) := by
  have hloop := Spec.forRangeZero (B := B) (c := fitBody) "i" "n" (FitInv P Q D Wl n) n 40 hnB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.1) (fitBody_spec P Q D Wl hB hP hQ hD hW hnB hpq hwB hdB)
  refine Spec.of_exists fun σ ⟨hn, hPs, hQs, hDs, hWs⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "wm") (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar "wm" 0 with hσ1
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ1, Env.setVar, hn]
    · simp [hσ1, Env.setVar, hPs]
    · simp [hσ1, Env.setVar, hQs]
    · simp [hσ1, Env.setVar, hDs]
    · simp [hσ1, Env.setVar]
    · simp [hσ1, Env.setVar, hWs, hW]
    · intro j; simp [hσ1, Env.setVar, hWs]
    · simp [hσ1, Env.setVar])
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · obtain ⟨-, -, -, -, -, hl, hg, -⟩ := hI
    rw [hi] at hg
    apply List.ext_getElem
    · simp [hl, fitArr]
    · intro j h1 h2
      have := hg j
      rw [List.getD_eq_getElem _ _ h1, if_pos (by simp [fitArr] at h2; omega)] at this
      rw [this]
      simp [fitArr]
  · obtain ⟨-, -, -, -, -, -, -, hwm⟩ := hI
    rw [hwm, hi, List.take_of_length_le (by simp [fitArr])]

end Lax496464Proofs.Ram.F5QFit
