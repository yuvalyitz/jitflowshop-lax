import Lax496464Proofs.Ram.Imp

/-!
# Writing a Block

A reduction's output is a handful of blocks, each of them a range mapped by an expression:
the `R·L` zeros of the selection jobs' preprocessing times, the `R·m·n` due dates of a
dummy family, and so on. `emitLoop` is that loop, once, with its cost and with what it
appends to the output tape.

The state the loop does not touch is left to the caller as a predicate `Base`, which has
only to be blind to the counter and to the output tape — every use here instantiates it
with "these scalars hold these numbers and these arrays hold these lists".
-/

namespace Lax496464Proofs.Ram.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Write the value of `e`, then move the counter up by one. -/
def emitBody (ix : String) (e : Expr) : Com :=
  .seq (.write e) (.assign ix (.bin .add (V ix) (.lit 1)))

/-- Write one value per index below the bound held in `bd`. -/
def emitLoop (ix bd : String) (e : Expr) : Com :=
  .seq (.assign ix (.lit 0)) (.while (.lt (V ix) (V bd)) (emitBody ix e))

variable {B : ℕ}

/-- **A block, written.** -/
theorem emitLoop_spec (ix bd : String) (_hne : ix ≠ bd) (N : ℕ) (f : ℕ → ℕ) (e : Expr)
    (out₀ : List ℕ) (Base : Env → Prop) (hNB : N < B)
    (hix : ∀ σ v, Base σ → Base (σ.setVar ix v))
    (hout : ∀ σ (o : List ℕ), Base σ → Base { σ with out := o })
    (hbd : ∀ σ, Base σ → σ.vars bd = N)
    (heval : ∀ σ, Base σ → σ.vars ix < N → e.evalB B σ = some (f (σ.vars ix))) :
    Spec B (fun σ => Base σ ∧ σ.out = out₀) (emitLoop ix bd e)
      (fun _ σ' => Base σ' ∧ σ'.vars ix = N ∧ σ'.out = out₀ ++ (List.range N).map f)
      ((1 + e.size + 4 + 4) * N + 6) := by
  classical
  set I : Env → Prop := fun σ =>
    Base σ ∧ σ.vars ix ≤ N ∧ σ.out = out₀ ++ (List.range (σ.vars ix)).map f with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ix < N) (emitBody ix e)
      (fun σ σ' => I σ' ∧ σ'.vars ix = σ.vars ix + 1) (1 + e.size + 4) := by
    refine Spec.of_exists fun σ ⟨⟨hB, hle, ho⟩, hlt⟩ => ?_
    have hone : (1 : ℕ) < B := by omega
    have hsucc : σ.vars ix + 1 < B := by omega
    have he := heval σ hB hlt
    have hw := Run.write (B := B) he
    have hlit : (Expr.lit 1).evalB B { σ with out := σ.out ++ [f (σ.vars ix)] } = some 1 := by
      simp only [Expr.evalB]; exact fit_self hone
    have hvar : (V ix).evalB B { σ with out := σ.out ++ [f (σ.vars ix)] }
        = some (σ.vars ix) := evalB_var (by simpa using (by omega : σ.vars ix < B))
    have ha := Run.assign (B := B) (σ := { σ with out := σ.out ++ [f (σ.vars ix)] })
      (x := ix) (e := .bin .add (V ix) (.lit 1)) (v := σ.vars ix + 1)
      (evalB_bin hvar hlit (by simpa using hsucc))
    refine ⟨_, _, hw.seq ha, by simp, ⟨?_, ?_, ?_⟩, by simp⟩
    · exact hix _ _ (hout _ _ hB)
    · simp; omega
    · simp [Env.setVar, ho, List.range_succ]

  refine (Spec.forRangeZero ix bd I N (1 + e.size + 4) hNB (fun _ h => h.2.1)
    (fun _ h => hbd _ h.1) hbody).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hB, ho⟩
    exact ⟨hix _ _ hB, by simp, by simp [ho]⟩
  · rintro σ σ' - ⟨⟨hB, -, ho⟩, hix'⟩
    exact ⟨hB, hix', by rw [ho, hix']⟩

end Lax496464Proofs.Ram.Emit
