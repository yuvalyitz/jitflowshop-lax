import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.ListUtil

/-!
# Copying One Array into Another

`Build.RC` (and its downstream callers) wants `"OFF"`/`"MEM"` sized *exactly* to the CSR data
they hold. `parseCom` cannot pre-size its own scratch arrays that way — it discovers the true
size (`setCount x`, `offset x (setCount x)`) only by running, so its arrays must start out
generously sized (bounded by the tape's length) to stay safe on every input, valid or not. This
file is the bridge: a generic "copy the first `N` cells of one array into another" loop, used to
move the scan's discovered CSR data into arrays already allocated at their true, exact size.
-/

namespace Lax496464Proofs.Ram.CopyArr

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Copy one cell, then move the counter up by one. -/
def copyBody (src dst ix : String) : Com :=
  .seq (.store dst (V ix) (.get src (V ix))) (.assign ix (.bin .add (V ix) (.lit 1)))

/-- Copy the first `N` (held in `bd`) cells of `src` into `dst`. -/
def copyLoop (src dst ix bd : String) : Com :=
  .seq (.assign ix (.lit 0)) (.while (.lt (V ix) (V bd)) (copyBody src dst ix))

variable {B : ℕ}

/-- **A block, copied from one array into another.** `dst`'s length is unchanged (a `store`
never resizes an array) — only its first `N` cells are overwritten, with `src`'s. -/
theorem copyLoop_spec (src dst ix bd : String) (N : ℕ) (f : ℕ → ℕ)
    (dst0 : List ℕ) (Base : Env → Prop) (hNB : N < B) (hLB : ∀ i < N, f i < B)
    (srcLen : ℕ) (hNsrc : N ≤ srcLen) (hNL : N ≤ dst0.length)
    (hix : ∀ σ v, Base σ → Base (σ.setVar ix v))
    (harr : ∀ σ i v, Base σ → Base (σ.setArr dst i v))
    (hbd : ∀ σ, Base σ → σ.vars bd = N)
    (hsrclen : ∀ σ, Base σ → (σ.arrs src).length = srcLen)
    (hsrc : ∀ σ, Base σ → ∀ i < N, (σ.arrs src).getD i 0 = f i) :
    Spec B (fun σ => Base σ ∧ σ.arrs dst = dst0) (copyLoop src dst ix bd)
      (fun _ σ' => Base σ' ∧ (σ'.arrs dst).length = dst0.length ∧
        (∀ i < N, (σ'.arrs dst).getD i 0 = f i) ∧
        (∀ i, N ≤ i → (σ'.arrs dst).getD i 0 = dst0.getD i 0))
      ((1 + 3 + 4 + 4) * N + 6) := by
  classical
  have hlenfold : ∀ n, ((List.range n).foldl (fun (l : List ℕ) i => l.set i (f i)) dst0).length
      = dst0.length := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.foldl_append]; simpa using ih
  have hgetfold : ∀ n ≤ N, ∀ i < n, ((List.range n).foldl (fun (l : List ℕ) i => l.set i (f i))
      dst0).getD i 0 = f i := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro hnN i hi
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rcases Nat.lt_or_ge i n with h | h
      · rw [getD_set_ne _ _ _ _ (by omega)]
        exact ih (by omega) i h
      · have : i = n := by omega
        subst this
        exact getD_set_self _ _ _ (by rw [hlenfold]; omega)
  set I : Env → Prop := fun σ =>
    Base σ ∧ σ.vars ix ≤ N ∧
      σ.arrs dst = (List.range (σ.vars ix)).foldl (fun l i => l.set i (f i)) dst0 with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ix < N) (copyBody src dst ix)
      (fun σ σ' => I σ' ∧ σ'.vars ix = σ.vars ix + 1) (1 + 3 + 4) := by
    refine Spec.of_exists fun σ ⟨⟨hB, hle, ho⟩, hlt⟩ => ?_
    have hidxB : σ.vars ix < B := by omega
    have hidxSrc : σ.vars ix < (σ.arrs src).length := by rw [hsrclen σ hB]; omega
    have hidxDst : σ.vars ix < (σ.arrs dst).length := by rw [ho, hlenfold]; omega
    have hgetv : (σ.arrs src).getD (σ.vars ix) 0 = f (σ.vars ix) := hsrc σ hB _ hlt
    have hk : (σ.arrs src)[σ.vars ix]? = some (f (σ.vars ix)) := by
      rw [List.getElem?_eq_getElem hidxSrc]
      congr 1
      rwa [List.getD_eq_getElem (σ.arrs src) 0 hidxSrc] at hgetv
    have hev : (Expr.get src (V ix)).evalB B σ = some (f (σ.vars ix)) :=
      evalB_get (evalB_var hidxB) hk (hLB _ hlt)
    have hstore := Run.store (B := B) (σ := σ) (a := dst) (i := V ix) (e := .get src (V ix))
      (idx := σ.vars ix) (v := f (σ.vars ix)) (evalB_var hidxB) hev hidxDst
    have hvsucc : σ.vars ix + 1 < B := by omega
    have hassign := Run.assign (B := B) (σ := σ.setArr dst (σ.vars ix) (f (σ.vars ix)))
      (x := ix) (e := .bin .add (V ix) (.lit 1)) (v := σ.vars ix + 1)
      (evalB_bin (evalB_var (by simpa using hidxB)) (evalB_lit (by omega)) (by simpa using hvsucc))
    refine ⟨_, _, hstore.seq hassign, by simp only [Expr.size]; omega, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact hix _ _ (harr _ _ _ hB)
    · simp; omega
    · have hvix : ((σ.setArr dst (σ.vars ix) (f (σ.vars ix))).setVar ix (σ.vars ix + 1)).vars ix
          = σ.vars ix + 1 := by simp [Env.setVar]
      have h1 : (σ.setArr dst (σ.vars ix) (f (σ.vars ix))).arrs dst
          = (σ.arrs dst).set (σ.vars ix) (f (σ.vars ix)) := by
        simp [Env.setArr]
      have h2 : ((σ.setArr dst (σ.vars ix) (f (σ.vars ix))).setVar ix (σ.vars ix + 1)).arrs dst
          = (σ.arrs dst).set (σ.vars ix) (f (σ.vars ix)) := by
        simp [Env.setVar]
      rw [hvix, h2, ho, List.range_succ, List.foldl_append]
      simp
    · simp [Env.setVar]
  have hgetfoldge : ∀ n ≤ N, ∀ i, n ≤ i → ((List.range n).foldl
      (fun (l : List ℕ) i => l.set i (f i)) dst0).getD i 0 = dst0.getD i 0 := by
    intro n
    induction n with
    | zero => intro _ i _; simp
    | succ n ih =>
      intro hnN i hi
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getD_set_ne _ _ _ _ (by omega)]
      exact ih (by omega) i (by omega)
  refine (Spec.forRangeZero ix bd I N (1 + 3 + 4) hNB (fun _ h => h.2.1)
    (fun _ h => hbd _ h.1) hbody).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hB, ho⟩
    exact ⟨hix _ _ hB, by simp, by simp [ho]⟩
  · rintro σ σ' - ⟨⟨hB, hle, ho⟩, hix'⟩
    refine ⟨hB, ?_, ?_, ?_⟩
    · rw [ho, hlenfold]
    · intro i hi; rw [ho, hix']; exact hgetfold N le_rfl i hi
    · intro i hi; rw [ho, hix']; exact hgetfoldge N le_rfl i hi

end Lax496464Proofs.Ram.CopyArr
