import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.Q3Defs

/-!
# Theorem 3, Profile Sweep: the per-Job Event

The bookkeeping of one event (`prepCom`): load the job's data from the sorted arrays, compute the
new reference time `rf = d - q`, the shift `dl = min (rf - pt) qm`, advance `pt`, and the
exponent `ex = q - 1`.  Mentions scalars `jj qm pt pj qj dj wj rf dl ex`, arrays `PS QS DS WS`.
-/

namespace Lax496464Proofs.Ram.Q3Event

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax496464Proofs.Ram.Q3Defs

abbrev V (s : String) : Expr := .var s

/-- Load job `jj`'s four numbers. -/
def loadCom : Com :=
  .seq (.assign "pj" (.get "PS" (V "jj")))
    (.seq (.assign "qj" (.get "QS" (V "jj")))
      (.seq (.assign "dj" (.get "DS" (V "jj"))) (.assign "wj" (.get "WS" (V "jj")))))

/-- Reference time, shift, and exponent. -/
def refCom : Com :=
  .seq (.assign "rf" (.bin .sub (V "dj") (V "qj")))
    (.seq (.assign "dl" (.bin .sub (V "rf") (V "pt")))
      (.seq (.ite (.lt (V "qm") (V "dl")) (.assign "dl" (V "qm")) .skip)
        (.seq (.assign "pt" (V "rf")) (.assign "ex" (.bin .sub (V "qj") (.lit 1))))))

/-- Load job `jj` and compute reference time, shift and exponent. -/
def prepCom : Com := .seq loadCom refCom

theorem loadCom_spec {B j pj0 qj0 dj0 wj0 : ℕ} (_hB : 1 < B) (hjB : j < B)
    (hpj : pj0 < B) (hqj : qj0 < B) (hdj : dj0 < B) (hwj : wj0 < B) :
    Spec B (fun σ => σ.vars "jj" = j ∧
        j < (σ.arrs "PS").length ∧ j < (σ.arrs "QS").length ∧ j < (σ.arrs "DS").length ∧
        j < (σ.arrs "WS").length ∧
        (σ.arrs "PS").getD j 0 = pj0 ∧ (σ.arrs "QS").getD j 0 = qj0 ∧
        (σ.arrs "DS").getD j 0 = dj0 ∧ (σ.arrs "WS").getD j 0 = wj0) loadCom
      (fun _ σ' => σ'.vars "pj" = pj0 ∧ σ'.vars "qj" = qj0 ∧ σ'.vars "dj" = dj0 ∧
        σ'.vars "wj" = wj0) 30 := by
  refine Spec.of_exists fun σ ⟨hjj, hl1, hl2, hl3, hl4, hg1, hg2, hg3, hg4⟩ => ?_
  simp only [List.getD_eq_getElem?_getD] at hg1 hg2 hg3 hg4
  run_vcg
  all_goals (simp [Env.setVar, hjj, hg1, hg2, hg3, hg4])
  all_goals (try omega)

theorem refCom_spec {B qj0 dj0 qm pt : ℕ} (hB : 1 < B)
    (hqj : qj0 < B) (hdj : dj0 < B) (hqm : qm < B) (hptB : pt < B) :
    Spec B (fun σ => σ.vars "qj" = qj0 ∧ σ.vars "dj" = dj0 ∧ σ.vars "qm" = qm ∧
        σ.vars "pt" = pt) refCom
      (fun _ σ' => σ'.vars "rf" = dj0 - qj0 ∧ σ'.vars "dl" = min (dj0 - qj0 - pt) qm ∧
        σ'.vars "pt" = dj0 - qj0 ∧ σ'.vars "ex" = qj0 - 1) 40 := by
  refine Spec.of_exists fun σ ⟨hqjv, hdjv, hqmv, hptv⟩ => ?_
  run_vcg
  all_goals (simp_all [Env.setVar])
  all_goals (try omega)

end Lax496464Proofs.Ram.Q3Event
