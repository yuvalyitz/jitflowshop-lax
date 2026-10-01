import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Passes

/-! # The whole program writes the complement word

`body_spec`: after the matrix is built, the header, the three passes and the last entry write
`complWord x` (`complWord_eq`). -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Main

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Passes

/-- The scalars the header assigns. -/
def headVars : List String := ["ci_n", "ci_tb"]

theorem header_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x) header
      (fun σ σ' => σ'.vars "ci_n" = nOf x ∧ σ'.vars "ci_tb" = 3 + nOf x ∧ Keep headVars σ σ' ∧
        σ'.out = σ.out) 20 := by
  have hn := hB.n_lt
  have hl := hd.n_le
  unfold header
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ 0 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD 0 0 = nOf x) ?_ ?_
  · run_vcg
    all_goals (try simp only [Keep, headVars] at *); all_goals (simp_all [Env.setVar]; try omega)
  · intro σ ha
    refine ⟨ha, by rw [ha]; omega, by rw [ha]; rfl⟩

theorem tailK_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) (hk : kOf x < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) tailK
      (fun σ σ' => σ'.out = σ.out ++ [kOf x] ∧ σ'.vars = σ.vars ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp) 10 := by
  have hb : x.length + nOf x * nOf x + 4 < B := hB
  have hl := hd.n_le
  unfold tailK
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
    σ.vars "rt_n" - 1 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (σ.vars "rt_n" - 1) 0 = kOf x) ?_ ?_
  · run_vcg
    all_goals (simp_all; try omega)
  · rintro σ ⟨ha, hr⟩
    refine ⟨ha, hr, by rw [ha, hr]; omega, by rw [ha, hr]; exact hd.last⟩

theorem complWord_eq (x : List ℕ) :
    complWord x = [nOf x, psum x (nOf x) / 2, 0] ++
      (List.range (nOf x)).map (fun r => psum x (r + 1)) ++
      (List.range (nOf x)).flatMap (nbW x) ++ [kOf x] := by
  unfold complWord graphWord offs tgs
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def, psum_zero]

/-- The cost of the body. -/
def Kbody (x : List ℕ) : ℕ :=
  20 + Kfill x + K1 (nOf x) + 4 + 6 + 2 + K1 (nOf x) + K3 (nOf x) + 10

set_option maxHeartbeats 4000000 in
theorem body_value {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) (hk : kOf x < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.arrs "mat" = List.replicate (nOf x * nOf x) 0 ∧
        σ.vars "rt_n" = x.length) body
      (fun σ σ' => σ'.out = σ.out ++ complWord x)
      (20 + Kfill x + K1 (nOf x) + 4 + 6 + 2 + K1 (nOf x) + K3 (nOf x) + 10) := by
  have hn := hB.n_lt
  have hps : psum x (nOf x) < B := by
    have := psum_le_sq (x := x) le_rfl; have hb : x.length + nOf x * nOf x + 4 < B := hB; omega
  have hw := complWord_eq x
  unfold body
  run_vcg [header_spec hd hB, fill_spec hd hB, pass1_spec hB, pass2_spec hB, pass3_spec hB,
    tailK_spec hd hB hk]
  all_goals (try simp only [Ctx, Ctx0, Keep, headVars, fillVars, pass1Vars, pass2Vars, pass3Vars, rowVars, adjVars] at *); all_goals (simp_all; try omega)

theorem body_spec {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) (hk : kOf x < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.arrs "mat" = List.replicate (nOf x * nOf x) 0 ∧
        σ.vars "rt_n" = x.length) body
      (fun σ σ' => σ'.out = σ.out ++ complWord x) (Kbody x) :=
  body_value hd hB hk

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Main
