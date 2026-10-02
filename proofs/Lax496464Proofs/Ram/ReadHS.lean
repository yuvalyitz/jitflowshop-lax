import Lax496464Proofs.Ram.CsrRead
import Lax496464Proofs.Ram.Build

/-!
# Reading a Hitting Set Word

`[n, m, o₀ … o_m, member₀ … member_{L−1}, k]`: the two counts, the `m+1` offsets, the
members, and the solution size. The two variable-length blocks are read by
`CsrRead.readBlock`, once each; the last offset says how long the second is.
-/

namespace Lax496464Proofs.Ram.ReadHS

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464Proofs.Ram.Build
open Lax496464Proofs.Ram.CsrRead (readBlock readBlock_spec Frame)

/-- Read the whole word. -/
def readHS : Com :=
  .seq (.read "n") (.seq (.read "m")
    (.seq (.assign "mp1" (.bin .add (V "m") (.lit 1)))
      (.seq (readBlock "i" "mp1" "OFF")
        (.seq (.assign "L" (.get "OFF" (V "m")))
          (.seq (readBlock "i" "L" "MEM") (.read "k"))))))

variable {x : List ℕ}

theorem readHS_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B)
    (hlen : x.length = 4 + setCount x + offset x (setCount x))
    (hmB : setCount x + 2 < B) (hLB : offset x (setCount x) + 1 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "OFF").length = setCount x + 1 ∧
        (σ.arrs "MEM").length = offset x (setCount x)) readHS
      (fun _ σ' => RC x σ' ∧ σ'.vars "k" = solutionSize x ∧ σ'.inp = [] ∧ σ'.out = [])
      (12 * (setCount x + 1) + 6 + (12 * offset x (setCount x) + 6) + 20) := by
  have hx2 : 2 ≤ x.length := by omega
  obtain ⟨a, b, rest, hx⟩ : ∃ a b rest, x = a :: b :: rest := by
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hx2
    · simp at hx2
    · exact ⟨a, b, rest, rfl⟩
  have hn : universeSize x = a := by subst hx; rfl
  have hm : setCount x = b := by subst hx; rfl
  have hmem2 : a ∈ x := by subst hx; simp
  have hmem3 : b ∈ x := by subst hx; simp
  have haB := hxB a hmem2
  have hbB := hxB b hmem3
  have hframe1 : Frame "i" "OFF" (fun σ : Env => σ.vars "n" = universeSize x ∧
      σ.vars "m" = setCount x ∧ σ.vars "mp1" = setCount x + 1 ∧
      (σ.arrs "MEM").length = offset x (setCount x) ∧ σ.out = []) := by
    intro σ σ' ⟨h1, h2, h3, h4, h5⟩ hv ha ho
    refine ⟨by rw [hv "n" (by decide) (by decide), h1], by rw [hv "m" (by decide) (by decide), h2],
      by rw [hv "mp1" (by decide) (by decide), h3], by rw [ha "MEM" (by decide), h4],
      by rw [ho, h5]⟩
  have hframe2 : Frame "i" "MEM" (fun σ : Env => σ.vars "n" = universeSize x ∧
      σ.vars "m" = setCount x ∧ σ.vars "L" = offset x (setCount x) ∧
      (∀ j ≤ setCount x, (σ.arrs "OFF").getD j 0 = offset x j) ∧
      (σ.arrs "OFF").length = setCount x + 1 ∧ σ.out = []) := by
    intro σ σ' ⟨h1, h2, h3, h4, h5, h6⟩ hv ha ho
    refine ⟨by rw [hv "n" (by decide) (by decide), h1], by rw [hv "m" (by decide) (by decide), h2],
      by rw [hv "L" (by decide) (by decide), h3], by rw [ha "OFF" (by decide)]; exact h4,
      by rw [ha "OFF" (by decide), h5], by rw [ho, h6]⟩
  have rb1 := readBlock_spec (B := B) (x := x) "i" "mp1" "OFF" 2 (setCount x + 1)
    (fun σ : Env => σ.vars "n" = universeSize x ∧
      σ.vars "m" = setCount x ∧ σ.vars "mp1" = setCount x + 1 ∧
      (σ.arrs "MEM").length = offset x (setCount x) ∧ σ.out = [])
    (by decide) hframe1 (by omega) hxB (by omega) (fun σ h => h.2.2.1)
  have rb2 := readBlock_spec (B := B) (x := x) "i" "L" "MEM" (3 + setCount x)
    (offset x (setCount x))
    (fun σ : Env => σ.vars "n" = universeSize x ∧
      σ.vars "m" = setCount x ∧ σ.vars "L" = offset x (setCount x) ∧
      (∀ j ≤ setCount x, (σ.arrs "OFF").getD j 0 = offset x j) ∧
      (σ.arrs "OFF").length = setCount x + 1 ∧ σ.out = [])
    (by decide) hframe2 (by omega) hxB (by omega) (fun σ h => h.2.2.1)
  have hone := hB
  have hxr : x.drop 2 = rest := by rw [hx]; rfl
  refine Spec.of_exists fun σ ⟨hinp, hout, hOFF, hMEM⟩ => ?_
  rw [hx] at hinp
  -- the two counts
  have r1 := Run.read (B := B) (x := "n") (v := a) (rest := b :: rest) hinp
  have r2 := Run.read (B := B) (x := "m") (v := b) (rest := rest)
    (σ := { σ.setVar "n" a with inp := b :: rest }) rfl
  have hmv : (Expr.var "m").evalB B ({ ({ σ.setVar "n" a with inp := b :: rest } : Env).setVar "m" b
      with inp := rest } : Env) = some b :=
    evalB_var (by simpa [Env.setVar] using hbB)
  have hl1 : (Expr.lit 1).evalB B ({ ({ σ.setVar "n" a with inp := b :: rest } : Env).setVar "m" b
      with inp := rest } : Env) = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have r3 := Run.assign (B := B) (x := "mp1") (e := .bin .add (V "m") (.lit 1)) (v := b + 1)
    (σ := { ({ σ.setVar "n" a with inp := b :: rest } : Env).setVar "m" b with inp := rest })
    (evalB_bin hmv hl1 (by show b + 1 < B; omega))
  set σ3 : Env := ({ ({ σ.setVar "n" a with inp := b :: rest } : Env).setVar "m" b with inp := rest }
    : Env).setVar "mp1" (b + 1) with hσ3
  have hσ3n : σ3.vars "n" = universeSize x := by rw [hn]; simp [hσ3, Env.setVar]
  have hσ3m : σ3.vars "m" = setCount x := by rw [hm]; simp [hσ3, Env.setVar]
  have hσ3p : σ3.vars "mp1" = setCount x + 1 := by rw [hm]; simp [hσ3, Env.setVar]
  obtain ⟨σ4, hr4, ⟨hB4n, hB4m, hB4p, hB4M, hB4o⟩, hi4, hl4, hc4, hin4⟩ :=
    rb1.run ⟨⟨hσ3n, hσ3m, hσ3p, hMEM, hout⟩, hOFF, by rw [hxr]; rfl⟩
  -- the last offset
  have hm4 : (Expr.var "m").evalB B σ4 = some (setCount x) :=
    hB4m ▸ evalB_var (by rw [hB4m]; omega)
  have hgv : (σ4.arrs "OFF").getD (setCount x) 0 = offset x (setCount x) := by
    rw [hc4 _ (by omega)]; rfl
  have hg := RunStep.eval_get B σ4 "OFF" (.var "m") (setCount x) hm4 (by omega)
    (by rw [hgv]; omega)
  rw [hgv] at hg
  have r5 := Run.assign (B := B) (σ := σ4) (x := "L") (e := .get "OFF" (V "m"))
    (v := offset x (setCount x)) hg
  set σ5 : Env := σ4.setVar "L" (offset x (setCount x)) with hσ5
  have hin5 : σ5.inp = x.drop (3 + setCount x) := by
    rw [show σ5.inp = σ4.inp from rfl, hin4]; congr 1; omega
  obtain ⟨σ6, hr6, ⟨hB6n, hB6m, hB6L, hB6O, hB6l, hB6o⟩, hi6, hl6, hc6, hin6⟩ :=
    rb2.run (σ := σ5) ⟨⟨by simpa [hσ5, Env.setVar] using hB4n,
      by simpa [hσ5, Env.setVar] using hB4m, by simp [hσ5, Env.setVar],
      fun j hj => hc4 j (by omega), hl4, hB4o⟩, hB4M, hin5⟩
  -- the solution size
  have hkin : σ6.inp = [solutionSize x] := by
    rw [hin6]
    have hl : (x.drop (3 + setCount x + offset x (setCount x))).length = 1 := by
      simp only [List.length_drop]; omega
    obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hl
    have hh := congrArg List.head? hv
    rw [List.head?_drop] at hh
    simp only [List.head?_cons] at hh
    rw [hv]
    congr 1
    unfold solutionSize
    rw [List.getD_eq_getElem?_getD]
    have : x[3 + setCount x + offset x (setCount x)]? = some v := hh
    rw [this]; rfl
  have hsB : solutionSize x < B := by
    apply hxB
    unfold solutionSize
    rw [List.getD_eq_getElem?_getD]
    have : (x[3 + setCount x + offset x (setCount x)]?).isSome := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
    rw [hv]; exact List.mem_of_getElem? hv
  have r7 := Run.read (B := B) (x := "k") (v := solutionSize x) (rest := []) (σ := σ6) hkin
  refine ⟨_, _, ((r1.seq (r2.seq (r3.seq (hr4.seq (r5.seq (hr6.seq r7)))))).mono ?_), le_rfl,
    ?_, ?_, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hσ5, Env.setVar] using hB6n
    · simpa [hσ5, Env.setVar] using hB6m
    · intro j hj; simpa using hB6O j hj
    · intro t ht; exact hc6 t ht
    · simpa using hB6l
    · simpa using hl6
  · simp
  · simp
  · simpa using hB6o

end Lax496464Proofs.Ram.ReadHS
