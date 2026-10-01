import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit

/-! # Phase 9: the word of the structure

`structOut_spec`: phase 9 writes the header and the blocks of the four relations, which is
`structWord` (`structWord_eq`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgStruct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit
open Lax496464Proofs.WHierarchy.Logic.StructureCode (blockOf wordOf)

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The context of the output phases. -/
def SC (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "hs_mem" = hs cl d k ∧ σ.arrs "fp_f" = fe cl d k

theorem structHead_spec (hB : BB cl d k B) :
    Spec B (SC cl d k) (structHead d)
      (fun σ σ' => σ' = { σ with out := σ.out ++ [4, 1, 1, d + 1, k + (d + 2), nL cl + 1, 1, nL cl] })
      (3 * 4 + 1 + 4 + 4 + 2 + 2) := by
  have hl := hB.hl
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => SC cl d k σ ∧ σ.vars "w_k" = k ∧ σ.vars "w_L" = nL cl) ?_
    (fun σ h => ⟨h, h.1.hk, h.1.hL⟩)
  intro σ ⟨hS, hk, hL⟩
  obtain ⟨σ1, r1, rfl⟩ := writeLits_spec (B := B) [4, 1, 1, d + 1]
    (by simp; omega) σ trivial
  have e1 : (Expr.add (V "w_k") (.lit (d + 2))).evalB B { σ with out := σ.out ++ [4, 1, 1, d + 1] } =
      some (k + (d + 2)) := by
    rw [← hk]; exact evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
  have e2 : (Expr.add (V "w_L") (.lit 1)).evalB B
      { σ with out := σ.out ++ [4, 1, 1, d + 1] ++ [k + (d + 2)] } = some (nL cl + 1) := by
    rw [← hL]; exact evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
  have e3 : (V "w_L").evalB B { σ with out := σ.out ++ [4, 1, 1, d + 1] ++ [k + (d + 2)] ++
      [nL cl + 1] ++ [1] } = some (nL cl) := by
    rw [← hL]; exact evalB_var (by simp; omega)
  refine ⟨_, (r1.seq ((Run.write e1).seq ((Run.write e2).seq ((Run.write (evalB_lit (by omega))).seq
    (Run.write e3))))).mono (by simp), ?_⟩
  simp

theorem emitT_spec (hB : BB cl d k B) {g a : ℕ} {e : Expr} (hg : g < B) (ha : a ≤ d + k + 2)
    (he : ∀ σ, SC cl d k σ → e.evalB B (σ.setVar "w_tg" g) = some a) :
    Spec B (SC cl d k) (emitT g e)
      (fun σ σ' => σ'.out = σ.out ++ blockOf (emitList cl d k g a) ∧ SC cl d k σ')
      (2 + (1 + e.size + Kemit cl d k)) := by
  intro σ hS
  have r1 : Run B (.assign "w_tg" (.lit g)) σ (σ.setVar "w_tg" g) 2 := Run.assign (evalB_lit hg)
  have r2 : Run B (.assign "w_ar" e) (σ.setVar "w_tg" g) ((σ.setVar "w_tg" g).setVar "w_ar" a)
      (1 + e.size) := Run.assign (he σ hS)
  obtain ⟨hC, hh, hf⟩ := hS
  have hEC : EC cl d k g ((σ.setVar "w_tg" g).setVar "w_ar" a) ∧
      ((σ.setVar "w_tg" g).setVar "w_ar" a).vars "w_ar" = a := by
    refine ⟨⟨hC.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hh],
      by simp [Env.setVar, hf], by simp [Env.setVar]⟩, by simp [Env.setVar]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ3, r3, ho3, hv3, ha3, -⟩ := emitCom_spec hB hg ha _ hEC
  refine ⟨σ3, r1.seq (r2.seq r3), by rw [ho3]; rfl, ?_, by rw [ha3]; exact hh,
    by rw [ha3]; exact hf⟩
  refine hC.keep (fun y hy => ?_) (fun a _ => by rw [ha3]; rfl)
  rw [hv3 y (by revert hy y; decide)]
  simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- The cost of the output of the structure. -/
def KstructOut (cl : List (List ℕ)) (d k : ℕ) : ℕ := 3 * Kemit cl d k + 60

theorem structWord_eq :
    structWord cl d k = [4, 1, 1, d + 1, k + (d + 2), nL cl + 1, 1, nL cl] ++
      blockOf (emitList cl d k 1 1) ++ blockOf (emitList cl d k 2 (d + 1)) ++
        blockOf (emitList cl d k 3 (d + k + 2)) := by
  simp only [structWord, wordOf, arities, tss, blockOf, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.length_cons, List.length_nil, List.cons_append,
    List.nil_append, List.append_assoc]
  congr 1
  simp only [List.cons.injEq, true_and]
  refine ⟨by ring, ?_⟩
  simp

theorem structOut_spec (hB : BB cl d k B) :
    Spec B (SC cl d k) (structOut d)
      (fun σ σ' => σ'.out = σ.out ++ structWord cl d k ∧ SC cl d k σ') (KstructOut cl d k) := by
  intro σ hS
  have hMB := hB.cb.small
  obtain ⟨σ1, r1, rfl⟩ := structHead_spec hB σ hS
  have hS1 : SC cl d k { σ with out := σ.out ++ [4, 1, 1, d + 1, k + (d + 2), nL cl + 1, 1, nL cl] } :=
    hS
  obtain ⟨σ2, r2, ho2, hS2⟩ := emitT_spec (g := 1) (a := 1) hB (by omega) (by omega)
    (fun σ _ => evalB_lit (by omega)) _ hS1
  obtain ⟨σ3, r3, ho3, hS3⟩ := emitT_spec (g := 2) (a := d + 1) hB (by omega) (by omega)
    (fun σ _ => evalB_lit (by omega)) _ hS2
  obtain ⟨σ4, r4, ho4, hS4⟩ := emitT_spec (g := 3) (a := d + k + 2) hB (by omega) (by omega)
    (fun σ h => by
      have hk' : (σ.setVar "w_tg" 3).vars "w_k" = k := by
        rw [← h.1.hk]; simp [Env.setVar]
      have := evalB_bin (B := B) (op := .add) (e := V "w_k") (f := .lit (d + 2))
        (σ := σ.setVar "w_tg" 3) (evalB_var (by rw [hk']; omega)) (evalB_lit (by omega))
        (by simp [Env.setVar]; rw [h.1.hk]; omega)
      rw [hk', Bop.apply_add, show k + (d + 2) = d + k + 2 by ring] at this; exact this) _ hS3
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by simp [KstructOut]; omega), ?_, hS4⟩
  rw [ho4, ho3, ho2, structWord_eq]
  simp

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgStruct
