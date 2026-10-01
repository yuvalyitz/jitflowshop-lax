import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath

/-! # Building the adjacency matrix: `fill`

`fill_spec`: from the compressed sparse row blocks of the word, `fill` builds the `n × n` adjacency
matrix `matF x` in the array `mat`, row by row. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath

/-- The value bound the body needs (besides the entries of the word). -/
def BOK (x : List ℕ) (B : ℕ) : Prop := x.length + nOf x * nOf x + 4 < B

theorem BOK.n_lt {x : List ℕ} {B : ℕ} (h : BOK x B) : nOf x + 4 < B := by
  unfold BOK at h; nlinarith

/-- The header's facts. -/
def Ctx0 (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "ci_n" = nOf x ∧ σ.vars "ci_tb" = 3 + nOf x

/-- The invariant of the loop over the block of `U`. -/
def InI (x : List ℕ) (U : ℕ) (σ : Env) : Prop :=
  Ctx0 x σ ∧ σ.vars "ci_u" = U ∧ σ.vars "ci_e" = offAt x (U + 1) ∧ offAt x U ≤ σ.vars "ci_j" ∧
    σ.vars "ci_j" ≤ offAt x (U + 1) ∧ σ.arrs "mat" = matS x U (σ.vars "ci_j")

theorem mul_add_lt_sq {n u t : ℕ} (hu : u < n) (ht : t < n) : u * n + t < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hu
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

set_option maxHeartbeats 1000000 in
theorem fillInner_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) {U : ℕ}
    (hU : U < nOf x) :
    Spec B (fun σ => InI x U σ ∧ σ.vars "ci_j" < offAt x (U + 1)) fillInner
      (fun σ σ' => InI x U σ' ∧ σ'.vars "ci_j" = σ.vars "ci_j" + 1) 20 := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hoff := hd.off_le_len (i := U + 1) (by omega)
  unfold fillInner
  refine Spec.pre (P := fun σ => InI x U σ ∧ σ.vars "ci_j" < offAt x (U + 1) ∧
      σ.vars "ci_tb" + σ.vars "ci_j" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ci_tb" + σ.vars "ci_j") 0 < nOf x ∧
      σ.vars "ci_u" * σ.vars "ci_n" + (σ.arrs "a").getD (σ.vars "ci_tb" + σ.vars "ci_j") 0 <
        (σ.arrs "mat").length ∧
      σ.vars "ci_u" * σ.vars "ci_n" + (σ.arrs "a").getD (σ.vars "ci_tb" + σ.vars "ci_j") 0 < B ∧
      (σ.arrs "mat").set (σ.vars "ci_u" * σ.vars "ci_n" +
        (σ.arrs "a").getD (σ.vars "ci_tb" + σ.vars "ci_j") 0) 1 =
        matS x U (σ.vars "ci_j" + 1) ∧
      σ.vars "ci_tb" + σ.vars "ci_j" < B ∧ nOf x < B ∧ σ.vars "ci_j" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [InI, Ctx0] at *; simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨⟨ha, hn, htb⟩, hu, he, hj1, hj2, hm⟩, hj⟩
    have hjn : σ.vars "ci_j" < offAt x (nOf x) :=
      lt_of_lt_of_le hj (hd.off_le (by omega) le_rfl)
    have htg : x.getD (3 + nOf x + σ.vars "ci_j") 0 < nOf x := hd.tgt_lt _ hjn
    have hsq := mul_add_lt_sq hU htg
    refine ⟨⟨⟨ha, hn, htb⟩, hu, he, hj1, hj2, hm⟩, hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, htb]; omega
    · rw [ha, htb]; exact htg
    · rw [ha, htb, hu, hn, hm, length_matS]; exact hsq
    · rw [ha, htb, hu, hn]; omega
    · rw [ha, htb, hu, hn, hm]; exact matS_step x hj1
    · rw [htb]; omega
    · omega
    · omega

theorem innerLoop_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) {U : ℕ}
    (hU : U < nOf x) :
    Spec B (fun σ => InI x U σ ∧ σ.vars "ci_j" = offAt x U) innerLoop
      (fun _ σ' => InI x U σ' ∧ σ'.vars "ci_j" = offAt x (U + 1)) (24 * x.length + 4) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hoff := hd.off_le_len (i := U + 1) (by omega)
  exact Spec.forRange "ci_j" "ci_e" (InI x U) (offAt x (U + 1)) 20 (24 * x.length + 4)
    (fun σ h => by have := h.2.2.2.2.1; omega)
    (fun σ h => by rw [h.2.2.1]; omega) (fun σ h => h.2.2.1) (fun σ h => h.2.2.2.2.1)
    (fillInner_spec hd hB hU) (fun σ h => h.1)
    (fun σ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 4)

/-- The block loop, stated relative to the vertex in `ci_u`. -/
theorem innerLoop_spec' {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx0 x σ ∧ σ.vars "ci_u" < nOf x ∧
        σ.vars "ci_e" = offAt x (σ.vars "ci_u" + 1) ∧ σ.vars "ci_j" = offAt x (σ.vars "ci_u") ∧
        σ.arrs "mat" = matS x (σ.vars "ci_u") (offAt x (σ.vars "ci_u")))
      innerLoop
      (fun σ σ' => Ctx0 x σ' ∧ σ'.vars "ci_u" = σ.vars "ci_u" ∧
        σ'.arrs "mat" = matS x (σ.vars "ci_u" + 1) (offAt x (σ.vars "ci_u" + 1)))
      (24 * x.length + 4) := by
  rintro σ ⟨h0, hu, he, hj, hm⟩
  obtain ⟨σ', hr, ⟨h0', hu', -, -, -, hm'⟩, hj'⟩ := innerLoop_spec hd hB hu σ
    ⟨⟨h0, rfl, he, by omega, by rw [hj]; exact hd.mono _ hu, by rw [hj]; exact hm⟩, hj⟩
  exact ⟨σ', hr, h0', hu', by rw [hm', hj', matS_next]⟩

/-- The invariant of the loop over the vertices. -/
def OutI (x : List ℕ) (σ : Env) : Prop :=
  Ctx0 x σ ∧ σ.vars "ci_u" ≤ nOf x ∧
    σ.arrs "mat" = matS x (σ.vars "ci_u") (offAt x (σ.vars "ci_u"))

set_option maxHeartbeats 1000000 in
theorem fillRow_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => OutI x σ ∧ σ.vars "ci_u" < nOf x) fillRow
      (fun σ σ' => OutI x σ' ∧ σ'.vars "ci_u" = σ.vars "ci_u" + 1) (24 * x.length + 40) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hn4 := hd.n_le
  unfold fillRow
  refine Spec.pre (P := fun σ => OutI x σ ∧ σ.vars "ci_u" < nOf x ∧
      3 + σ.vars "ci_u" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (2 + σ.vars "ci_u") 0 = offAt x (σ.vars "ci_u") ∧
      (σ.arrs "a").getD (3 + σ.vars "ci_u") 0 = offAt x (σ.vars "ci_u" + 1) ∧
      offAt x (σ.vars "ci_u") < B ∧ offAt x (σ.vars "ci_u" + 1) < B ∧ 3 + σ.vars "ci_u" < B) ?_ ?_
  · run_vcg [innerLoop_spec' hd hB]
    all_goals (simp only [OutI, Ctx0] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨⟨ha, hn, htb⟩, hu, hm⟩, hlt⟩
    have h1 := hd.off_le_len (i := σ.vars "ci_u") (by omega)
    have h2 := hd.off_le_len (i := σ.vars "ci_u" + 1) (by omega)
    refine ⟨⟨⟨ha, hn, htb⟩, hu, hm⟩, hlt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha]; omega
    · rw [ha]; rfl
    · rw [ha]; show x.getD (3 + σ.vars "ci_u") 0 = x.getD (2 + (σ.vars "ci_u" + 1)) 0
      congr 1; omega
    · omega
    · omega
    · omega

/-- The cost of `fill`. -/
def Kfill (x : List ℕ) : ℕ := (24 * x.length + 44) * nOf x + 6

theorem fill_value {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx0 x σ ∧ σ.arrs "mat" = List.replicate (nOf x * nOf x) 0) fill
      (fun _ σ' => Ctx0 x σ' ∧ σ'.arrs "mat" = matF x) (Kfill x) := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hn4 := hd.n_le
  unfold fill
  have hloop := Spec.forRangeZero (B := B) (c := fillRow) "ci_u" "ci_n" (OutI x) (nOf x)
    (24 * x.length + 40) (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2.1) (fillRow_spec hd hB)
  refine Spec.pre (Spec.post hloop ?_) ?_
  · rintro σ σ' - ⟨⟨h0, -, hm⟩, hu⟩
    rw [hu, matS_final hd] at hm
    exact ⟨h0, hm⟩
  · rintro σ ⟨⟨ha, hn, htb⟩, hm⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [Env.setVar, ha]
    · simp [Env.setVar, hn]
    · simp [Env.setVar, htb]
    · simp [Env.setVar]
    · simp [Env.setVar, hm, matS_zero]

/-- The scalars `fill` may assign. -/
def fillVars : List String := ["ci_u", "ci_j", "ci_e"]

theorem fill_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => Ctx0 x σ ∧ σ.arrs "mat" = List.replicate (nOf x * nOf x) 0) fill
      (fun σ σ' => Ctx0 x σ' ∧ σ'.arrs "mat" = matF x ∧
        (∀ y, y ∉ fillVars → σ'.vars y = σ.vars y) ∧ (∀ b, b ≠ "mat" → σ'.arrs b = σ.arrs b) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) (Kfill x) := by
  refine Spec.post (fill_value hd hB).frame ?_
  rintro σ σ' - ⟨⟨h0, hm⟩, hv, ha, hi, ho⟩
  refine ⟨h0, hm, fun y hy => hv y ?_, fun b hb => ha b ?_, hi ?_, ho ?_⟩
  · simp only [fill, fillRow, innerLoop, fillInner, bump, Com.wvars, fillVars] at hy ⊢
    simp at hy ⊢; tauto
  · simp [fill, fillRow, innerLoop, fillInner, bump, Com.warrs, hb]
  · simp [fill, fillRow, innerLoop, fillInner, bump, Com.reads]
  · simp [fill, fillRow, innerLoop, fillInner, bump, Com.NoWrite]

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill
