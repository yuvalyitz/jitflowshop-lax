import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass

/-! # Σ₁[2] model checking to Clique: the graph phase writes the word of the reduction

`gph_spec`: the graph phase writes the compressed sparse row word of the graph followed by `k`,
which is `reduce x` (`reduce_eq`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC

theorem reduce_eq (x : List ℕ) :
    reduce x = [NGX x, ps x (NGX x) / 2, 0] ++ (List.range (NGX x)).map (fun s => ps x (s + 1)) ++
      (List.range (NGX x)).flatMap (nb x) ++ [kX x] := rfl

/-- The cost of the graph phase. -/
def Kg (x : List ℕ) : ℕ := 10 + K1 x + 30 + K1 x + K3 x + 10

theorem write_div2 {B : ℕ} {σ : Env} (a : String) (h : σ.vars a < B) (h2 : 2 < B) :
    Run B (.write (.div (V a) (.lit 2))) σ { σ with out := σ.out ++ [σ.vars a / 2] } 4 := by
  have ha : (V a).evalB B σ = some (σ.vars a) := evalB_var h
  have hb : (Expr.lit 2).evalB B σ = some 2 := evalB_lit h2
  have := Run.write (σ := σ) (evalB_bin (op := .div) ha hb
    (by simp; exact lt_of_le_of_lt (Nat.div_le_self _ _) h))
  simpa using this

theorem write_lit {B : ℕ} {σ : Env} (n : ℕ) (h : n < B) :
    Run B (.write (.lit n)) σ { σ with out := σ.out ++ [n] } 2 := by
  have := Run.write (σ := σ) (evalB_lit (n := n) (B := B) h)
  simpa using this

set_option maxHeartbeats 2000000 in
/-- **The graph phase.** -/
theorem gph_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => AC x σ ∧ σ.vars "zC" = CX x) gph
      (fun σ σ' => σ'.out = σ.out ++ reduce x) (Kg x) := by
  have hb : x.length + NGX x + ps x (NGX x) + 2 < B := hB.2
  have hAB := hB.1.1
  have hW := hAB.1.2
  have hC := hAB.2.2
  have hL := ProgTok2.HB.len hAB.1
  have hqL := ProgElb.qX_le x
  intro σ ⟨hac, hzC⟩
  have hzk : σ.vars "zk" = kX x := hac.2.2.2.2.2.2.2.1
  have hzne : σ.vars "zne" = neX x := hac.2.2.2.2.2.2.2.2
  -- zNG := zC * (zne * zk)
  have hkB : kX x < B := by unfold kX; omega
  have hneB : neX x < B := by
    have := neX_le x; have := ProgElb.length_elL x; nlinarith
  have hprod : neX x * kX x ≤ NGX x ∨ CX x = 0 := by
    unfold NGX; rcases Nat.eq_zero_or_pos (CX x) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  have hCpos : 0 < CX x := by unfold CX; positivity
  have hnk : neX x * kX x < B := by rcases hprod with h | h <;> omega
  have r0 : Run B (.assign "zNG" (.mul (V "zC") (.mul (V "zne") (V "zk")))) σ
      (σ.setVar "zNG" (NGX x)) 6 := by
    have e1 : (V "zC").evalB B σ = some (CX x) := by rw [← hzC]; exact evalB_var (by omega)
    have e2 : (V "zne").evalB B σ = some (neX x) := by rw [← hzne]; exact evalB_var (by omega)
    have e3 : (V "zk").evalB B σ = some (kX x) := by rw [← hzk]; exact evalB_var (by omega)
    have e23 := evalB_bin (op := .mul) e2 e3 (by simpa using hnk)
    have := Run.assign (x := "zNG") (σ := σ) (evalB_bin (op := .mul) e1 e23 (by
      show CX x * (neX x * kX x) < B; unfold NGX at hb; omega))
    simpa [NGX] using this
  set σ0 := σ.setVar "zNG" (NGX x) with hσ0
  have hc0 : Ctx x σ0 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hac
    exact ⟨⟨h1, by simp [hσ0, h2], h3, h4, h5, h6, h7, by simp [hσ0, h8], by simp [hσ0, h9]⟩,
      by simp [hσ0]⟩
  obtain ⟨σ1, r1, hc1, hM1, -, ho1⟩ := pass1_spec hB σ0 hc0
  have hNG1 : σ1.vars "zNG" = NGX x := hc1.2
  have r2 := ProgPass.write_run (B := B) (σ := σ1) "zNG" (by rw [hNG1]; omega)
  set σ2 := { σ1 with out := σ1.out ++ [σ1.vars "zNG"] } with hσ2
  have r3 := write_div2 (B := B) (σ := σ2) "gM" (by simp [hσ2, hM1]; omega) (by omega)
  set σ3 := { σ2 with out := σ2.out ++ [σ2.vars "gM" / 2] } with hσ3
  have r4 := write_lit (B := B) (σ := σ3) 0 (by omega)
  set σ4 := { σ3 with out := σ3.out ++ [0] } with hσ4
  have hc4 : Ctx x σ4 := hc1
  obtain ⟨σ5, r5, hc5, ho5, -⟩ := pass2_spec hB σ4 hc4
  obtain ⟨σ6, r6, hc6, ho6, -⟩ := pass3_spec hB σ5 hc5
  have hk6 : σ6.vars "zk" = kX x := hc6.1.2.2.2.2.2.2.2.1
  have r7 := ProgPass.write_run (B := B) (σ := σ6) "zk" (by rw [hk6]; omega)
  refine ⟨_, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7))))))).mono
    (by unfold Kg; omega), ?_⟩
  show σ6.out ++ [σ6.vars "zk"] = σ.out ++ reduce x
  rw [ho6, ho5, hk6, reduce_eq]
  simp only [hσ4, hσ3, hσ2, ho1, hM1, hNG1, hσ0, out_setVar]
  simp

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph
