import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateMain

/-!
# The specification of the validator

`validate_spec_list`, composed from the specifications of its loops.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {B : ℕ} {x : List ℕ}

/-- Every scalar the validator assigns. -/
abbrev SF : List String :=
  ["ok", "v_n", "v_go", "v_nn", "v_s", "v_t", "v_u", "v_w", "v_c", "v_d", "v_k"]

theorem bnd_facts {N L B : ℕ} (hN : N ≤ L) (hB : (L + 2) ^ 2 < B) :
    L + 2 < B ∧ N * N < B ∧ N + 1 + N * N < B := by
  have h1 : N * N ≤ L * L := Nat.mul_le_mul hN hN
  have h2 : (L + 2) ^ 2 = L * L + 4 * L + 4 := by ring
  refine ⟨by omega, by omega, by omega⟩

theorem validate_spec' (hx : ∀ v ∈ x, v < B) (hB : Bval x < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "L" = x.length) validate
      (fun σ σ' => ((σ'.vars "ok" = 1 ↔ Shape.Valid x) ∧ (σ'.vars "ok" = 0 ∨ σ'.vars "ok" = 1)) ∧
        Frm SF σ σ') (Kval x) := by
  have hNL : Shape.order x ≤ x.length := by
    rw [order_eq]
    have := tw_le' (y := x) (s := 0) (Nat.zero_le _)
    omega
  obtain ⟨hB1, hbnd1, hbnd2⟩ := bnd_facts hNL hB
  have hy := hx
  have hNtw : Shape.order x = tw x 0 := order_eq x
  generalize hNdef : Shape.order x = N at *
  have hB0 : 0 < B := by omega
  have D0 : Spec B (fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length) (.assign "ok" (.lit 1))
      (fun σ σ' => σ' = σ.setVar "ok" 1) (1 + (Expr.lit 1).size) :=
    Spec.assign (f := fun _ => 1) (fun σ _ => evalB_lit (by omega))
  have D1 := runFrom_spec (B := B) (y := x) "v_n" (by decide) (by decide) hx hB1 (.lit 0) 0
    (Nat.zero_le _)
  have D2 : Spec B (fun σ : Env => σ.vars "v_n" = N) (.assign "v_nn" (.bin .mul (V "v_n") (V "v_n")))
      (fun σ σ' => σ' = σ.setVar "v_nn" (σ.vars "v_n" * σ.vars "v_n"))
      (1 + (Expr.bin .mul (V "v_n") (V "v_n")).size) :=
    Spec.assign (f := fun σ => σ.vars "v_n" * σ.vars "v_n") (fun σ h =>
      evalB_bin (evalB_var (by rw [h]; omega)) (evalB_var (by rw [h]; omega)) (by rw [h]; exact hbnd1))
  have D3 : Spec B (fun σ : Env => σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N)
      (.assign "v_s" (.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")))
      (fun σ σ' => σ' = σ.setVar "v_s" (σ.vars "v_n" + 1 + σ.vars "v_nn"))
      (1 + (Expr.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")).size) :=
    Spec.assign (f := fun σ => σ.vars "v_n" + 1 + σ.vars "v_nn") (fun σ h =>
      evalB_bin (evalB_bin (evalB_var (by rw [h.1]; omega)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; rw [h.1]; omega))
        (evalB_var (by rw [h.2]; omega)) (by simp only [Bop.apply_add]; rw [h.1, h.2]; omega))
  have D4 := checkS_spec (B := B) (x := x) N hx hB1 hbnd2
  have D34 : Spec B (fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        σ.vars "v_nn" = N * N ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (.seq (.assign "v_s" (.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn"))) checkS)
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ VC x N)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧ Frm SF σ σ'')
      (1 + (Expr.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")).size + KS x) := by
    refine Spec.seq (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
        σ.vars "v_n" = N ∧ σ.vars "v_nn" = N * N ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (D3.pre (fun σ h => ⟨h.2.2.1, h.2.2.2.1⟩)) D4 ?_ ?_
    · rintro σ σ' ⟨ha, hL, hn, hnn, hok⟩ rfl
      simp [ha, hL, hn, hnn, hok]
    · rintro σ σ' σ'' ⟨ha, hL, hn, hnn, hok⟩ rfl ⟨⟨h1, h2⟩, hf⟩
      refine ⟨⟨by simpa using h1, h2⟩, ?_⟩
      refine (Frm.mono (S := ["v_s"]) ?_ (by simp)).trans (hf.mono (by simp))
      exact ⟨rfl, rfl, rfl, fun z hz => by simp [Env.setVar]; intro h; subst h; simp at hz⟩
  have D234 : Spec B (fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧ σ.vars "v_n" = N ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (.seq (.assign "v_nn" (.bin .mul (V "v_n") (V "v_n")))
        (.seq (.assign "v_s" (.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn"))) checkS))
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ VC x N)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧ Frm SF σ σ'')
      (1 + (Expr.bin .mul (V "v_n") (V "v_n")).size +
        (1 + (Expr.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")).size + KS x)) := by
    refine Spec.seq (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
        σ.vars "v_n" = N ∧ (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (D2.pre (fun σ h => h.2.2.1)) D34 ?_ ?_
    · rintro σ σ' ⟨ha, hL, hn, hok⟩ rfl
      simp [ha, hL, hn, hok]
    · rintro σ σ' σ'' ⟨ha, hL, hn, hok⟩ rfl ⟨⟨h1, h2⟩, hf⟩
      refine ⟨⟨by simpa using h1, h2⟩, ?_⟩
      refine (Frm.mono (S := ["v_nn"]) ?_ (by simp)).trans hf
      exact ⟨rfl, rfl, rfl, fun z hz => by simp [Env.setVar]; intro h; subst h; simp at hz⟩
  have D1234 : Spec B (fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (.seq (runFrom "v_n" (.lit 0)) (.seq (.assign "v_nn" (.bin .mul (V "v_n") (V "v_n")))
        (.seq (.assign "v_s" (.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn"))) checkS)))
      (fun σ σ'' => ((σ''.vars "ok" = 1 ↔ (σ.vars "ok" = 1 ∧ VC x N)) ∧
          (σ''.vars "ok" = 0 ∨ σ''.vars "ok" = 1)) ∧ Frm SF σ σ'')
      (1 + (Expr.lit 0).size + 2 + (24 * (x.length + 1) + 4) +
        (1 + (Expr.bin .mul (V "v_n") (V "v_n")).size +
        (1 + (Expr.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")).size + KS x))) := by
    refine Spec.seq (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
        (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1))
      (D1.pre (fun σ h => ⟨h.1, h.2.1, evalB_lit (by omega)⟩)) D234 ?_ ?_
    · rintro σ σ' ⟨ha, hL, hok⟩ ⟨⟨hn, hgo⟩, hf⟩
      refine ⟨by rw [congrFun hf.1 "a"]; exact ha, by rw [hf.2.2.2 "L" (by simp)]; exact hL,
        by omega, by rw [hf.2.2.2 "ok" (by simp)]; exact hok⟩
    · rintro σ σ' σ'' ⟨ha, hL, hok⟩ ⟨⟨hn, hgo⟩, hf⟩ ⟨⟨h1, h2⟩, hf2⟩
      refine ⟨⟨by rw [h1, hf.2.2.2 "ok" (by simp)], h2⟩, ?_⟩
      exact (hf.mono (by simp)).trans hf2
  have hV : Shape.Valid x ↔ VC x N := by rw [← hNdef]; exact valid_iff_VC x
  unfold validate
  refine Spec.mono (Spec.seq (P := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length)
    (P' := fun σ : Env => σ.arrs "a" = x ∧ σ.vars "L" = x.length ∧
      (σ.vars "ok" = 0 ∨ σ.vars "ok" = 1)) D0 D1234 ?_ ?_) ?_
  · rintro σ σ' ⟨ha, hL⟩ rfl
    simp [ha, hL]
  · rintro σ σ' σ'' ⟨ha, hL⟩ rfl ⟨⟨h1, h2⟩, hf⟩
    refine ⟨⟨?_, h2⟩, ?_⟩
    · rw [h1, hV]; simp
    · refine (Frm.mono (S := ["ok"]) ?_ (by simp)).trans hf
      exact ⟨rfl, rfl, rfl, fun z hz => by simp [Env.setVar]; intro h; subst h; simp at hz⟩
  · unfold KS KS0 Kval
    simp only [Expr.size]
    omega

end Lax496464Proofs.WHierarchy.MccNP.Validate
