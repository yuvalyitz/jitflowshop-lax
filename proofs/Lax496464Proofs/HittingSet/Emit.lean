import Lax391470Proofs.EmitNat
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Mathlib.Tactic

/-!
# Emitters

A command *emits* a list if it appends that list to the output and changes nothing but a
fixed set of scratch scalars. Emitters compose. The primitive one is the archive's writer
of a number in the self-delimiting binary code, `Lax391470Proofs.EmitNat.emitNat`.
-/

namespace Lax496464Proofs.HittingSet.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.Bits Lax391470Proofs.EmitNat

/-- Nothing but the scalars in `S` changed. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ v ∉ S, σ'.vars v = σ.vars v) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

theorem Keep.trans {S : List String} {σ σ' σ'' : Env} (h : Keep S σ σ') (h' : Keep S σ' σ'') :
    Keep S σ σ'' :=
  ⟨fun v hv => (h'.1 v hv).trans (h.1 v hv), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Keep.mono {S S' : List String} {σ σ' : Env} (h : Keep S σ σ') (hS : ∀ v, v ∈ S → v ∈ S') :
    Keep S' σ σ' :=
  ⟨fun v hv => h.1 v fun hm => hv (hS v hm), h.2.1, h.2.2⟩

theorem Keep.setVar {S : List String} {σ : Env} {x : String} (hx : x ∈ S) (v : ℕ) :
    Keep S σ (σ.setVar x v) :=
  ⟨fun y hy => by
    have : y ≠ x := fun h => hy (h ▸ hx)
    simp [Env.setVar, this], rfl, rfl⟩

theorem Keep.var {S : List String} {σ σ' : Env} (h : Keep S σ σ') {v : String} (hv : v ∉ S) :
    σ'.vars v = σ.vars v := h.1 v hv

/-- `c` emits `out σ` under `P`, with scratch `S`. -/
def Emits (S : List String) (B : ℕ) (c : Com) (P : Env → Prop) (out : Env → List ℕ) (K : ℕ) :
    Prop :=
  Spec B P c (fun σ σ' => σ'.out = σ.out ++ out σ ∧ Keep S σ σ') K

variable {S : List String} {B : ℕ}

theorem Emits.seq {c d : Com} {P Q : Env → Prop} {o1 o2 : Env → List ℕ} {K1 K2 : ℕ}
    (h1 : Emits S B c P o1 K1) (h2 : Emits S B d Q o2 K2)
    (hQ : ∀ σ σ', Keep S σ σ' → Q σ → Q σ') (ho : ∀ σ σ', Keep S σ σ' → o2 σ' = o2 σ) :
    Emits S B (.seq c d) (fun σ => P σ ∧ Q σ) (fun σ => o1 σ ++ o2 σ) (K1 + K2) := by
  intro σ ⟨hP, hQ0⟩
  obtain ⟨σ1, r1, e1, k1⟩ := h1 σ hP
  obtain ⟨σ2, r2, e2, k2⟩ := h2 σ1 (hQ σ σ1 k1 hQ0)
  exact ⟨σ2, r1.seq r2, by rw [e2, e1, ho σ σ1 k1, List.append_assoc], k1.trans k2⟩

theorem Emits.weaken {c : Com} {P P' : Env → Prop} {o o' : Env → List ℕ} {K K' : ℕ}
    (h : Emits S B c P o K) (hP : ∀ σ, P' σ → P σ) (ho : ∀ σ, P' σ → o σ = o' σ) (hK : K ≤ K') :
    Emits S B c P' o' K' := by
  intro σ hσ
  obtain ⟨σ1, r1, e1, k1⟩ := h σ (hP σ hσ)
  exact ⟨σ1, r1.mono hK, by rw [e1, ho σ hσ], k1⟩

/-- A variable holding a known value evaluates to it. -/
theorem evalB_var_eq {x : String} {v : ℕ} {σ : Env} (h : σ.vars x = v) (hv : v < B) :
    (Expr.var x).evalB B σ = some v := by
  rw [← h]; exact evalB_var (by rw [h]; exact hv)

/-! ### Writing a number -/

/-- The scratch of the number writer. -/
def SN : List String := ["v", "u", "s", "i2"]

theorem mem_SN_of_wvars {y : String} (hy : y ∈ emitNat.wvars) : y ∈ SN := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.wvars, SN] at hy ⊢
  aesop

theorem warrs_emitNat : emitNat.warrs = [] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.warrs]

theorem reads_emitNat : ¬ emitNat.reads := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.reads]

/-- `emitNat` emits the code of the number in `v`. -/
theorem emitNat_emits (M : ℕ) :
    Emits SN B emitNat (fun σ => σ.vars "v" + 4 < B ∧ (σ.vars "v").size ≤ M)
      (fun σ => bitsNat (σ.vars "v")) (48 * M + 40) := by
  intro σ ⟨h1, h2⟩
  obtain ⟨σ', r, e, hv, ha, hi, -⟩ :=
    (emitNat_spec (B := B) M).frame σ ⟨h1, h2⟩
  refine ⟨σ', r, e, fun y hy => hv y fun h => hy (mem_SN_of_wvars h),
    funext fun a => ha a (by rw [warrs_emitNat]; simp), hi reads_emitNat⟩

/-- Set `v` from `ex`, then write it. -/
def setNat (ex : Expr) : Com := .seq (.assign "v" ex) emitNat

theorem setNat_emits (ex : Expr) (f : Env → ℕ) (M : ℕ) (P : Env → Prop)
    (hf : ∀ σ, P σ → ex.evalB B σ = some (f σ))
    (hb : ∀ σ, P σ → f σ + 4 < B ∧ (f σ).size ≤ M) :
    Emits SN B (setNat ex) P (fun σ => bitsNat (f σ)) (ex.size + 48 * M + 41) := by
  intro σ hσ
  obtain ⟨b1, b2⟩ := hb σ hσ
  have r1 : Run B (.assign "v" ex) σ (σ.setVar "v" (f σ)) (1 + ex.size) := Run.assign (hf σ hσ)
  obtain ⟨σ', r2, e2, k2⟩ := emitNat_emits (B := B) M (σ.setVar "v" (f σ))
    ⟨by simpa [Env.setVar] using b1, by simpa [Env.setVar] using b2⟩
  refine ⟨σ', (r1.seq r2).mono (by omega), ?_, ?_⟩
  · rw [e2]; simp [Env.setVar]
  · refine ⟨fun y hy => ?_, k2.2.1, k2.2.2⟩
    rw [k2.1 y hy]
    have : y ≠ "v" := fun h => hy (h ▸ by simp [SN])
    simp [Env.setVar, this]

/-- A literal number. -/
theorem lit_emits (n M : ℕ) (hM : n.size ≤ M) :
    Emits SN B (setNat (.lit n)) (fun _ => n + 4 < B) (fun _ => bitsNat n) (48 * M + 42) :=
  (setNat_emits (.lit n) (fun _ => n) M (fun _ => n + 4 < B)
    (fun _ h => evalB_lit (by omega)) (fun _ h => ⟨h, hM⟩)).weaken (fun _ h => h)
    (fun _ _ => rfl) (by simp [Expr.size]; omega)

end Lax496464Proofs.HittingSet.Emit
