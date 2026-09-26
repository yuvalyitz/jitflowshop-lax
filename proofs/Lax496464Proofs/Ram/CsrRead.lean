import Lax496464Proofs.Ram.Imp
import Lax496464.HittingSet
import Mathlib.Data.List.GetD

/-!
# Reading a Hitting Set word

The word of a Hitting Set instance is `n`, `m`, the `m+1` offsets, the member array as long
as the last offset says, and the solution size — read strictly in that order, so one pass
suffices and the two variable-length blocks are read by the same loop shape twice.
-/

namespace Lax496464Proofs.Ram.CsrRead

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464.HittingSet

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- Read one number into position `ix` of `arr`. -/
def readBody (ix arr : String) : Com :=
  .seq (.read "v") (.seq (.store arr (V ix) (V "v")) (bump ix))

/-- Read `bd` numbers into `arr`. -/
def readBlock (ix bd arr : String) : Com :=
  .seq (.assign ix (.lit 0)) (.while (.lt (V ix) (V bd)) (readBody ix arr))

variable {B : ℕ} {x : List ℕ}

/-- The loop's invariant, with everything the loop does not touch left to `Base`. -/
def BInv (ix arr : String) (x : List ℕ) (base N : ℕ) (Base : Env → Prop) (σ : Env) : Prop :=
  Base σ ∧ σ.vars ix ≤ N ∧ (σ.arrs arr).length = N ∧
    (∀ t < σ.vars ix, (σ.arrs arr).getD t 0 = x.getD (base + t) 0) ∧
    σ.inp = x.drop (base + σ.vars ix)

/-- What the block reader asks of the rest of the state: that it depend only on the
variables the loop does not write, on the arrays it does not store into, and not on the
input tape. -/
def Frame (ix arr : String) (Base : Env → Prop) : Prop :=
  ∀ σ σ' : Env, Base σ →
    (∀ y, y ≠ ix → y ≠ "v" → σ'.vars y = σ.vars y) →
    (∀ a, a ≠ arr → σ'.arrs a = σ.arrs a) → σ'.out = σ.out → Base σ'

theorem readBody_spec (ix _bd arr : String) (base N : ℕ) (Base : Env → Prop)
    (hixv : ix ≠ "v") (hframe : Frame ix arr Base)
    (hlen : base + N ≤ x.length) (hxB : ∀ v ∈ x, v < B) (hNB : N + 1 < B) :
    Spec B (fun σ => BInv ix arr x base N Base σ ∧ σ.vars ix < N) (readBody ix arr)
      (fun σ σ' => BInv ix arr x base N Base σ' ∧ σ'.vars ix = σ.vars ix + 1) 8 := by
  refine Spec.pre (P := fun σ => BInv ix arr x base N Base σ ∧ σ.vars ix < N ∧
      σ.inp ≠ [] ∧ σ.inp.headD 0 < B ∧ σ.vars ix < (σ.arrs arr).length ∧
      σ.vars ix + 1 < B) ?_ ?_
  · run_vcg
    · obtain ⟨hB, hle, hlength, hcell, hinp'⟩ := ‹BInv ix arr x base N Base σ›
      have hilt := ‹σ.vars ix < N›
      have hidx : base + σ.vars ix < x.length := by omega
      have haidx : σ.vars ix < (σ.arrs arr).length := by rw [hlength]; exact hilt
      simp only [BInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Env.setVar, Env.setArr] <;>
        simp [hixv]
      · refine hframe σ _ hB (fun y hy hy' => ?_) (fun a ha => ?_) rfl
        · simp [hy, hy']
        · simp [ha]
      · exact hilt
      · exact hlength
      · intro t ht
        rcases Nat.lt_or_ge t (σ.vars ix) with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell t h
        · have hte : t = σ.vars ix := by omega
          subst hte
          rw [hinp']
          simp [haidx, List.head?_drop]
      · rw [hinp', List.tail_drop]
        congr 1
    all_goals simp only [vars_setArr, Env.setVar, if_neg hixv, if_true]
    all_goals first | assumption | omega
  · rintro σ ⟨hI, hlt⟩
    obtain ⟨hB, hle, hlength, hcell, hinp'⟩ := hI
    have hidx : base + σ.vars ix < x.length := by omega
    have hne : σ.inp ≠ [] := by
      rw [hinp']; intro hc
      have hz : (x.drop (base + σ.vars ix)).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at hz; omega
    refine ⟨⟨hB, hle, hlength, hcell, hinp'⟩, hlt, hne, ?_,
      by rw [hlength]; exact hlt, by omega⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ x.drop (base + σ.vars ix) := by rw [← hinp', hh]; exact List.mem_cons_self
      exact hxB u (List.mem_of_mem_drop this)

/-- **A block, read.** -/
theorem readBlock_spec (ix bd arr : String) (base N : ℕ) (Base : Env → Prop)
    (hixv : ix ≠ "v") (hframe : Frame ix arr Base)
    (hlen : base + N ≤ x.length) (hxB : ∀ v ∈ x, v < B) (hNB : N + 1 < B)
    (hbd : ∀ σ, Base σ → σ.vars bd = N) :
    Spec B (fun σ => Base σ ∧ (σ.arrs arr).length = N ∧ σ.inp = x.drop base)
      (readBlock ix bd arr)
      (fun _ σ' => Base σ' ∧ σ'.vars ix = N ∧ (σ'.arrs arr).length = N ∧
        (∀ t < N, (σ'.arrs arr).getD t 0 = x.getD (base + t) 0) ∧
        σ'.inp = x.drop (base + N))
      (12 * N + 6) := by
  refine (Spec.forRangeZero ix bd (BInv ix arr x base N Base) N 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => hbd _ h.1)
    (readBody_spec ix bd arr base N Base hixv hframe hlen hxB hNB)).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hB, hlength, hinp'⟩
    refine ⟨hframe σ _ hB (fun y hy _ => by simp [Env.setVar, hy]) (fun a _ => rfl) rfl,
      by simp, by simpa using hlength, by simp, by simpa using hinp'⟩
  · rintro σ σ' - ⟨⟨hB, -, hlength, hcell, hinp'⟩, hix'⟩
    rw [hix'] at hcell hinp'
    exact ⟨hB, hix', hlength, hcell, hinp'⟩

end Lax496464Proofs.Ram.CsrRead
