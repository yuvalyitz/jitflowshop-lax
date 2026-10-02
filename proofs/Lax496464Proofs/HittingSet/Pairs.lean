import Lax496464Proofs.HittingSet.Emit
import Lax496464Proofs.HittingSet.Model

/-!
# The Pairs

For each variable `i` below `V`: the size `2`, then `2i` and `2i + 1`.
-/

namespace Lax496464Proofs.HittingSet.Pairs

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax496464Proofs.HittingSet.Emit Lax496464Proofs.HittingSet.Model

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- `2, 2i, 2i + 1`. -/
def pairEmit : Com :=
  .seq (setNat (.lit 2)) (.seq (setNat (.bin .mul (.lit 2) (V "i")))
    (setNat (.bin .add (.bin .mul (.lit 2) (V "i")) (.lit 1))))

def pairBody : Com := .seq pairEmit (bump "i")

def pairsLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "V")) pairBody)

variable {B : ℕ}

/-- The precondition of the pair of `i`: its numbers fit, with bit size at most `S`. -/
def Pi (S : ℕ) (B : ℕ) (σ : Env) : Prop :=
  2 * σ.vars "i" + 8 < B ∧ (2 * σ.vars "i" + 2).size ≤ S

theorem Pi_keep {S : ℕ} {σ σ' : Env} (k : Keep SN σ σ') (h : Pi S B σ) : Pi S B σ' := by
  unfold Pi at h ⊢; rw [k.var (by simp [SN])]; exact h

theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := Nat.size_le_size h

theorem size_two : (2 : ℕ).size = 2 := by decide

theorem pairEmit_emits (S : ℕ) (hS : 2 ≤ S) :
    Emits SN B pairEmit (Pi S B)
      (fun σ => bitsNat 2 ++ (bitsNat (2 * σ.vars "i") ++ bitsNat (2 * σ.vars "i" + 1)))
      (3 * (48 * S + 42) + 6) := by
  have e1 : Emits SN B (setNat (.lit 2)) (Pi S B) (fun _ => bitsNat 2) (48 * S + 42) :=
    (lit_emits 2 S (by rw [size_two]; exact hS)).weaken (fun σ h => by have := h.1; omega)
      (fun _ _ => rfl) le_rfl
  have e2 : Emits SN B (setNat (.bin .mul (.lit 2) (V "i"))) (Pi S B)
      (fun σ => bitsNat (2 * σ.vars "i")) ((Expr.bin .mul (.lit 2) (V "i")).size + 48 * S + 41) :=
    setNat_emits _ (fun σ => 2 * σ.vars "i") S (Pi S B)
      (fun σ h => RunStep.eval_mul B σ (.lit 2) (V "i") 2 (σ.vars "i")
        (evalB_lit (by have := h.1; omega)) (evalB_var (by have := h.1; omega))
        (by have := h.1; omega))
      (fun σ h => ⟨by have := h.1; omega, le_trans (size_mono (by omega)) h.2⟩)
  have e3 : Emits SN B (setNat (.bin .add (.bin .mul (.lit 2) (V "i")) (.lit 1))) (Pi S B)
      (fun σ => bitsNat (2 * σ.vars "i" + 1))
      ((Expr.bin .add (.bin .mul (.lit 2) (V "i")) (.lit 1)).size + 48 * S + 41) :=
    setNat_emits _ (fun σ => 2 * σ.vars "i" + 1) S (Pi S B)
      (fun σ h => RunStep.eval_add B σ _ (.lit 1) (2 * σ.vars "i") 1
        (RunStep.eval_mul B σ (.lit 2) (V "i") 2 (σ.vars "i")
          (evalB_lit (by have := h.1; omega)) (evalB_var (by have := h.1; omega))
          (by have := h.1; omega))
        (evalB_lit (by have := h.1; omega)) (by have := h.1; omega))
      (fun σ h => ⟨by have := h.1; omega, le_trans (size_mono (by omega)) h.2⟩)
  have e23 := e2.seq e3 (fun _ _ k h => Pi_keep k h)
    (fun σ σ' k => by rw [k.var (v := "i") (by simp [SN])])
  have e123 := e1.seq e23 (fun _ _ k h => ⟨Pi_keep k h.1, Pi_keep k h.2⟩)
    (fun σ σ' k => by rw [k.var (v := "i") (by simp [SN])])
  exact e123.weaken (fun σ h => ⟨h, h, h⟩) (fun _ _ => rfl) (by simp [Expr.size]; omega)

/-- The invariant of the pairs loop, relative to the entry state `σ0`. -/
structure PInv (Vv : ℕ) (σ0 : Env) (σ : Env) : Prop where
  hV : σ.vars "V" = Vv
  hi : σ.vars "i" ≤ Vv
  hout : σ.out = σ0.out ++ pairsOut (σ.vars "i")
  keep : Keep ("i" :: SN) σ0 σ

theorem pairsOut_succ (i : ℕ) :
    pairsOut (i + 1) = pairsOut i ++ (bitsNat 2 ++ (bitsNat (2 * i) ++ bitsNat (2 * i + 1))) := by
  simp [pairsOut, List.range_succ]

/-- The cost of one pair. -/
def Kpair (S : ℕ) : ℕ := 3 * (48 * S + 42) + 6 + 4

theorem pairBody_spec (Vv S : ℕ) (σ0 : Env) (hS : 2 ≤ S) (hB : 2 * Vv + 8 < B)
    (hSV : (2 * Vv + 2).size ≤ S) :
    Spec B (fun σ => PInv Vv σ0 σ ∧ σ.vars "i" < Vv) pairBody
      (fun σ σ' => PInv Vv σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (Kpair S) := by
  intro σ ⟨hI, hlt⟩
  obtain ⟨σ1, r1, e1, k1⟩ := pairEmit_emits (B := B) S hS σ
    ⟨by omega, le_trans (size_mono (by omega)) hSV⟩
  have hi1 : σ1.vars "i" = σ.vars "i" := k1.var (by simp [SN])
  have r2 : Run B (bump "i") σ1 (σ1.setVar "i" (σ.vars "i" + 1)) 4 := by
    have := Run.assign (B := B) (σ := σ1) (x := "i") (e := .bin .add (V "i") (.lit 1))
      (RunStep.eval_add B σ1 (V "i") (.lit 1) (σ.vars "i") 1
        (by rw [← hi1]; exact evalB_var (by rw [hi1]; omega)) (evalB_lit (by omega)) (by omega))
    simpa [Expr.size] using this
  refine ⟨_, r1.seq r2, ⟨?_, ?_, ?_, ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    rw [k1.var (by simp [SN]), hI.hV]
  · simp only [Env.setVar, ↓reduceIte]; omega
  · simp only [Env.setVar, ↓reduceIte]
    rw [e1, hI.hout, pairsOut_succ, List.append_assoc]
  · exact (hI.keep.trans (k1.mono fun v hv => List.mem_cons_of_mem _ hv)).trans
      (Keep.setVar (by simp) _)

theorem pairsLoop_spec (Vv S : ℕ) (σ0 : Env) (hS : 2 ≤ S) (hB : 2 * Vv + 8 < B)
    (hSV : (2 * Vv + 2).size ≤ S) :
    Spec B (fun σ => PInv Vv σ0 (σ.setVar "i" 0)) pairsLoop
      (fun _ σ' => PInv Vv σ0 σ' ∧ σ'.vars "i" = Vv) ((Kpair S + 4) * Vv + 6) :=
  Spec.forRangeZero "i" "V" (PInv Vv σ0) Vv (Kpair S) (by omega)
    (fun _ h => h.hi) (fun _ h => h.hV) (pairBody_spec Vv S σ0 hS hB hSV)

/-- **The pairs loop**, from a state holding `V`. -/
theorem pairsLoop_run (Vv S : ℕ) (σ : Env) (hS : 2 ≤ S) (hB : 2 * Vv + 8 < B)
    (hSV : (2 * Vv + 2).size ≤ S) (hV : σ.vars "V" = Vv) :
    ∃ σ', Run B pairsLoop σ σ' ((Kpair S + 4) * Vv + 6) ∧
      σ'.out = σ.out ++ pairsOut Vv ∧ Keep ("i" :: SN) σ σ' := by
  obtain ⟨σ', r, hI, hi⟩ := pairsLoop_spec (B := B) Vv S σ hS hB hSV σ
    ⟨by simp [Env.setVar, hV], by simp, by simp [Env.setVar, pairsOut], Keep.setVar (by simp) _⟩
  exact ⟨σ', r, by rw [hI.hout, hi], hI.keep⟩

end Lax496464Proofs.HittingSet.Pairs
