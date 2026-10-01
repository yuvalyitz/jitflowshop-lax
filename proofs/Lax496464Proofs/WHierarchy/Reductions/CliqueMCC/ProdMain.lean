import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass

/-! # p-Clique to Multicoloured Clique: the body writes the word of the construction

`body_spec`: the header, the passes over the copies and the colours write `prodWord x` (`word_eq`).
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdRow
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass

/-- The scalars the header assigns. -/
def headVars : List String := ["b_N", "b_tb"]

theorem kP_lt {x : List ℕ} {B : ℕ} (hB : ∀ w ∈ x, w < B) (h0 : 0 < B) : kP x < B := by
  unfold kP
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · simpa using h0
  · simpa using hB a (by simp)

theorem header_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "b_n" = nV x ∧ σ.vars "b_k" = kP x) header
      (fun σ σ' => Ctx x σ' ∧ σ'.vars "b_k" = kP x ∧ Keep headVars σ σ' ∧ σ'.out = σ.out) 10 := by
  have hb : x.length + NOf x + 2 < B := hB.1.2.2
  have hn3 : nV x + 3 < x.length := hB.1.1.1
  have hk : kP x < B := kP_lt hB.1.2.1 (by omega)
  unfold header
  run_vcg
  all_goals (simp only [Keep, Ctx, headVars, NOf] at *; simp_all [Env.setVar]; try omega)

theorem word_eq (x : List ℕ) :
    prodWord x = [NOf x, ps x (NOf x) / 2, 0] ++
      (List.range (NOf x)).map (fun s => ps x (s + 1)) ++
      (List.range (NOf x)).flatMap (nb x) ++
      (List.range (NOf x)).map (fun s => s / nV x) ++ [kP x] := rfl

/-- The cost the walk proves. -/
def Ksum (x : List ℕ) : ℕ := 20 + K1 x + K1 x + K3 x + K4 x + 20

set_option maxHeartbeats 4000000 in
theorem body_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "b_n" = nV x ∧ σ.vars "b_k" = kP x) body
      (fun σ σ' => σ'.out = σ.out ++ prodWord x ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ ∀ y, y ∉ bodyVars → σ'.vars y = σ.vars y)
      (Ksum x) := by
  have hb : x.length + NOf x + ps x (NOf x) + 2 < B := hB.2
  have hk : kP x < B := kP_lt hB.1.2.1 (by omega)
  have hw := word_eq x
  unfold body Ksum
  run_vcg [header_spec hB, pass1_spec hB, pass2_spec hB, pass3_spec hB, pass4_spec hB]
  all_goals (try simp only [Ctx, Keep, headVars, pass1Vars, pass2Vars, pass3Vars, pass4Vars,
    rowVars, adjVars, bodyVars] at *)
  all_goals (simp_all; try omega)

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMain
