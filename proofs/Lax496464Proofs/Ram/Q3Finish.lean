import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.Q3Defs
import Lax496464Proofs.Ram.ListUtil

/-!
# Theorem 3, Profile Sweep: the Read-Off (`finish`)

After the sweep, `Yes` holds exactly when some profile `x < bt` has `T[x][W] < INF`.  One scan over
the `bt` profiles, then a single `write`.  Mentions scalars `ok i bt w1 W cinf` and array `T`.
-/

namespace Lax496464Proofs.Ram.Q3Finish

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax496464Proofs.Ram.Q3Defs

abbrev V (s : String) : Expr := .var s

/-- One profile: is the cell `(i, W)` finite? -/
def finBody : Com :=
  .seq (.ite (.lt (.get "T" (.bin .add (.bin .mul (V "i") (V "w1")) (V "W"))) (V "cinf"))
      (.assign "ok" (.lit 1)) .skip)
    (.assign "i" (.bin .add (V "i") (.lit 1)))

/-- The scan: `ok` becomes `1` iff some cell `(i, W)` is `< cinf`. -/
def finScan : Com :=
  .seq (.assign "ok" (.lit 0))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "bt")) finBody))

/-- The read-off: scan, then write the flag. -/
def finishCom : Com := .seq finScan (.write (V "ok"))

/-- The scan's invariant: the flag says whether a finite cell was seen among profiles `< i`. -/
def FInv (bt w1 W INF : ℕ) (T : List ℕ) (σ : Env) : Prop :=
  σ.vars "bt" = bt ∧ σ.vars "w1" = w1 ∧ σ.vars "W" = W ∧ σ.vars "cinf" = INF ∧
  σ.arrs "T" = T ∧ σ.vars "i" ≤ bt ∧
  σ.vars "ok" = (if ∃ y < σ.vars "i", cell w1 T y W < INF then 1 else 0)

theorem exists_succ_iff {w1 W INF : ℕ} (T : List ℕ) (i : ℕ) :
    (∃ y < i + 1, cell w1 T y W < INF) ↔
      ((∃ y < i, cell w1 T y W < INF) ∨ cell w1 T i W < INF) := by
  constructor
  · rintro ⟨y, hy, h⟩
    by_cases hyi : y < i
    · exact Or.inl ⟨y, hyi, h⟩
    · have : y = i := by omega
      subst this; exact Or.inr h
  · rintro (⟨y, hy, h⟩ | h)
    · exact ⟨y, by omega, h⟩
    · exact ⟨i, by omega, h⟩

theorem finInv_hit {bt w1 W INF : ℕ} {T : List ℕ} {σ : Env} (h : FInv bt w1 W INF T σ)
    (hlt : σ.vars "i" < bt) (hc : cell w1 T (σ.vars "i") W < INF) :
    FInv bt w1 W INF T ((σ.setVar "ok" 1).setVar "i" ((σ.setVar "ok" 1).vars "i" + 1)) ∧
      ((σ.setVar "ok" 1).setVar "i" ((σ.setVar "ok" 1).vars "i" + 1)).vars "i" =
        σ.vars "i" + 1 := by
  obtain ⟨hbt, hw1, hW, hcinf, hT, hile, hok⟩ := h
  have hE := exists_succ_iff (w1 := w1) (W := W) (INF := INF) T (σ.vars "i")
  have e1 : ((σ.setVar "ok" 1).setVar "i" ((σ.setVar "ok" 1).vars "i" + 1)).vars "ok" = 1 := by
    simp [Env.setVar]
  have e2 : ((σ.setVar "ok" 1).setVar "i" ((σ.setVar "ok" 1).vars "i" + 1)).vars "i" =
      σ.vars "i" + 1 := by simp [Env.setVar]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e2⟩
  · simp [Env.setVar, hbt]
  · simp [Env.setVar, hw1]
  · simp [Env.setVar, hW]
  · simp [Env.setVar, hcinf]
  · simp [Env.setVar, hT]
  · rw [e2]; omega
  · rw [e1, e2, if_pos (hE.mpr (Or.inr hc))]

theorem finInv_miss {bt w1 W INF : ℕ} {T : List ℕ} {σ : Env} (h : FInv bt w1 W INF T σ)
    (hlt : σ.vars "i" < bt) (hc : ¬ cell w1 T (σ.vars "i") W < INF) :
    FInv bt w1 W INF T (σ.setVar "i" (σ.vars "i" + 1)) ∧
      (σ.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  obtain ⟨hbt, hw1, hW, hcinf, hT, hile, hok⟩ := h
  have hE := exists_succ_iff (w1 := w1) (W := W) (INF := INF) T (σ.vars "i")
  have e1 : (σ.setVar "i" (σ.vars "i" + 1)).vars "ok" = σ.vars "ok" := by
    simp [Env.setVar]
  have e2 : (σ.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
    simp [Env.setVar]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e2⟩
  · simp [Env.setVar, hbt]
  · simp [Env.setVar, hw1]
  · simp [Env.setVar, hW]
  · simp [Env.setVar, hcinf]
  · simp [Env.setVar, hT]
  · rw [e2]; omega
  · rw [e1, e2, hok]
    have : (∃ y < σ.vars "i" + 1, cell w1 T y W < INF) ↔ ∃ y < σ.vars "i", cell w1 T y W < INF := by
      rw [hE]; simp [hc]
    simp only [this]

theorem finBody_spec {B bt w1 W INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : w1 = W + 1)
    (hTl : T.length = bt * w1) (hTB : ∀ v ∈ T, v < B) (hbtB : bt < B) (hINF : INF < B)
    (hNB : bt * w1 < B) :
    Spec B (fun σ => FInv bt w1 W INF T σ ∧ σ.vars "i" < bt) finBody
      (fun σ σ' => FInv bt w1 W INF T σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  refine Spec.of_exists fun σ ⟨⟨hbt, hw1', hW, hcinf, hT, hile, hok⟩, hlt⟩ => ?_
  have hW1 : 0 < w1 := by omega
  have hidx : σ.vars "i" * w1 + W < bt * w1 := by
    have : (σ.vars "i" + 1) * w1 ≤ bt * w1 := Nat.mul_le_mul_right _ hlt
    have h2 : (σ.vars "i" + 1) * w1 = σ.vars "i" * w1 + w1 := by ring
    omega
  have hiw : σ.vars "i" * w1 < B := by omega
  have hiB : σ.vars "i" < B := by omega
  have hTi : σ.arrs "T" = T := hT
  have hget : cell w1 T (σ.vars "i") W = T.getD (σ.vars "i" * w1 + W) 0 := rfl
  have hgetB : T.getD (σ.vars "i" * w1 + W) 0 < B := by
    have hmem : T.getD (σ.vars "i" * w1 + W) 0 ∈ T := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    exact hTB _ hmem
  have hex : ∀ y, y < σ.vars "i" + 1 ↔ y < σ.vars "i" ∨ y = σ.vars "i" := by intro y; omega
  have hw1v : σ.vars "w1" = w1 := hw1'
  have hexists : (∃ y < σ.vars "i" + 1, cell w1 T y W < INF) ↔
      ((∃ y < σ.vars "i", cell w1 T y W < INF) ∨ cell w1 T (σ.vars "i") W < INF) := by
    constructor
    · rintro ⟨y, hy, h⟩
      rcases (hex y).mp hy with h1 | rfl
      · exact Or.inl ⟨y, h1, h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact ⟨y, by omega, h⟩
      · exact ⟨σ.vars "i", by omega, h⟩
  have hlt1 : (σ.arrs "T").getD (σ.vars "i" * σ.vars "w1" + σ.vars "W") 0 < σ.vars "cinf" ↔
      cell w1 T (σ.vars "i") W < INF := by
    rw [hT, hw1', hW, hcinf]; rfl
  have hFI : FInv bt w1 W INF T σ := ⟨hbt, hw1', hW, hcinf, hT, hile, hok⟩
  by_cases hc : cell w1 T (σ.vars "i") W < INF
  · have hc2 := hlt1.mpr hc
    run_vcg
    all_goals first
      | exact finInv_hit hFI hlt hc
      | (simp only [hw1v, hW]; omega)
      | (simp only [hw1v, hW, hT]; omega)
      | contradiction
  · have hc2 : ¬ (σ.arrs "T").getD (σ.vars "i" * σ.vars "w1" + σ.vars "W") 0 < σ.vars "cinf" :=
      fun h => hc (hlt1.mp h)
    run_vcg
    all_goals first
      | exact finInv_miss hFI hlt hc
      | (simp only [hw1v, hW]; omega)
      | (simp only [hw1v, hW, hT]; omega)
      | contradiction

/-- **The read-off is correct.** -/
theorem finishCom_spec {B bt w1 W INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : w1 = W + 1)
    (hTl : T.length = bt * w1) (hTB : ∀ v ∈ T, v < B) (hbtB : bt < B) (hINF : INF < B)
    (hNB : bt * w1 < B) :
    Spec B (fun σ => σ.vars "bt" = bt ∧ σ.vars "w1" = w1 ∧ σ.vars "W" = W ∧
        σ.vars "cinf" = INF ∧ σ.arrs "T" = T ∧ σ.out = []) finishCom
      (fun _ σ' => σ'.out = [if ∃ x < bt, cell w1 T x W < INF then 1 else 0])
      ((40 + 4) * bt + 6 + 20) := by
  have hloop := Spec.forRangeZero (B := B) (c := finBody) "i" "bt" (FInv bt w1 W INF T) bt 40 hbtB
    (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.1)
    (finBody_spec T hB hw1 hTl hTB hbtB hINF hNB)
  refine Spec.of_exists fun σ ⟨hbt, hw1', hW, hcinf, hT, hout⟩ => ?_
  have hFI : FInv bt w1 W INF T ((σ.setVar "ok" 0).setVar "i" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hbt, hw1', hW, hcinf, hT]
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r0 := Run.assign (B := B) (σ := σ) (x := "ok") (e := .lit 0) (v := 0) hl0
  obtain ⟨σ1, hr1, ⟨hbt1, hw11, hW1, hcinf1, hT1, hile1, hok1⟩, hi1⟩ :=
    hloop ((σ.setVar "ok" 0)) hFI
  have hokB : σ1.vars "ok" < B := by
    rw [hok1]; split_ifs <;> omega
  have hv : (V "ok").evalB B σ1 = some (σ1.vars "ok") := evalB_var hokB
  have r2 := Run.write (B := B) (σ := σ1) (e := V "ok") (v := σ1.vars "ok") hv
  have hout1 : σ1.out = [] := by
    have := hr1.out_eq (by decide)
    rw [this]; exact hout
  refine ⟨_, _, ((r0.seq hr1).seq r2), ?_, ?_⟩
  · simp only [Expr.size]; omega
  · simp only [hout1, List.nil_append]
    congr 1
    rw [hok1, hi1]

end Lax496464Proofs.Ram.Q3Finish
