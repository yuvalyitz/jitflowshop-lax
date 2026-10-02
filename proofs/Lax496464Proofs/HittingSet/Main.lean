import Lax496464Proofs.HittingSet.Front
import Lax496464Proofs.HittingSet.Pairs
import Lax496464Proofs.HittingSet.Clause

/-!
# The Program

Read the word, scan it, fall back to the formula with one empty clause if it encodes
nothing; set the dimensions; write the three numbers, the pairs and the clause sets.
-/

namespace Lax496464Proofs.HittingSet.Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax391470Proofs.Bits Lax496464.HittingSetFromSat
open Lax496464Proofs.HittingSet.Emit Lax496464Proofs.HittingSet.Front Lax496464Proofs.HittingSet.Pairs Lax496464Proofs.HittingSet.Clause
open Lax496464Proofs.HittingSet.Model Lax496464Proofs.HittingSet.Correct

abbrev V (s : String) : Expr := .var s

/-- The dimensions: `V = max mx 2`, `nn = 2V`, `m = V + C`. -/
def dims : Com :=
  .seq (.ite (.lt (V "mx") (.lit 2)) (.assign "V" (.lit 2)) (.assign "V" (V "mx")))
    (.seq (.assign "nn" (.bin .mul (.lit 2) (V "V"))) (.assign "m" (.bin .add (V "V") (V "C"))))

/-- The three numbers. -/
def head : Com := .seq (setNat (V "nn")) (.seq (setNat (V "m")) (setNat (V "V")))

def main : Com := .seq front (.seq dims (.seq head (.seq pairsLoop clauseLoop)))

/-- The bound on the values: quadratic in the length of the word. -/
def Mof (L : ℕ) : ℕ := 100 * ((L + 2) * (L + 2)) + 95

/-- The bit-size bound on every number written. -/
def Sof (L : ℕ) : ℕ := 2 * L + 8

/-- The cost of the whole program. -/
def Kmain (L : ℕ) : ℕ :=
  Kscan L + 14 + 3 * (48 * Sof L + 42) + ((Kpair (Sof L) + 4) * (L + 2) + 6) +
    ((Kclause (Sof L) L + 4) * (L + 1) + 6)

theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

theorem red_eq' (y : List ℕ) : red y = out (Fof y) := red_eq y

variable {B : ℕ}

theorem main_spec (y : List ℕ) (hyB : ∀ v ∈ y, v < B) (hBig : Mof y.length + 4 < B) :
    ∃ σ', Run B main (initEnv (ext y.length) (y.length :: y)) σ' (Kmain y.length) ∧
      σ'.out = red y := by
  obtain ⟨L, hL⟩ : ∃ L, y.length = L := ⟨_, rfl⟩
  have hM : Mof L = 100 * ((L + 2) * (L + 2)) + 95 := rfl
  have hLP : L ≤ (L + 2) * (L + 2) := by nlinarith
  rw [hL] at hBig
  obtain ⟨P, hP⟩ : ∃ P, (L + 2) * (L + 2) = P := ⟨_, rfl⟩
  rw [hP] at hLP
  rw [hM, hP] at hBig
  have hB : L + 8 < B := by omega
  obtain ⟨S, hS⟩ : ∃ S, Sof L = S := ⟨_, rfl⟩
  have hSd : S = 2 * L + 8 := by rw [← hS]; rfl
  -- read, scan, fall back
  obtain ⟨σ4, r4, Sc⟩ := scan_spec (B := B) y hyB (by omega)
  rw [hL] at r4
  obtain ⟨F, hF⟩ : ∃ F, Fof y = F := ⟨_, rfl⟩
  have hC := Sc.hC; have hk := Sc.hk; have hmx := Sc.hmx; have post := Sc.post
  have lvr := Sc.lvr; have lsg := Sc.lsg; have lcl := Sc.lcl; have hsz := Sc.hsz
  have hFl := Sc.hFl; have hbd := Sc.hbd; have hmark4 := Sc.hmark; have out4 := Sc.hout
  have inp4 := Sc.hinp
  rw [hF] at hC hk hmx post hsz hFl hbd
  rw [hL] at lvr lsg lcl hsz hFl hbd hmark4
  obtain ⟨Vv, hV⟩ : ∃ Vv, vars F = Vv := ⟨_, rfl⟩
  have hVb : bound F ≤ Vv := by rw [← hV]; exact bound_le_vars F
  have hV2 : 2 ≤ Vv := by rw [← hV]; exact two_le_vars F
  have hVL : Vv ≤ L + 2 := by rw [← hV]; unfold vars; omega
  obtain ⟨k, hkd⟩ : ∃ k, (lits F).length = k := ⟨_, rfl⟩
  rw [hkd] at hk hsz
  -- the dimensions
  have hmxB : σ4.vars "mx" < B := by rw [hmx]; omega
  have hcond : (Cond.lt (V "mx") (.lit 2)).evalB B σ4 = some (decide (bound F < 2)) := by
    rw [← hmx]; exact evalB_condLt (evalB_var hmxB) (evalB_lit (by omega))
  have rV : Run B (.ite (.lt (V "mx") (.lit 2)) (.assign "V" (.lit 2)) (.assign "V" (V "mx")))
      σ4 (σ4.setVar "V" Vv) 6 := by
    by_cases h2 : bound F < 2
    · have hVe : Vv = 2 := by rw [← hV]; unfold vars; omega
      rw [hVe]
      exact (Run.ite_true (by rw [hcond, decide_eq_true h2]) (Run.assign (evalB_lit (by omega)))).mono
        (by simp [Cond.size, Expr.size])
    · have hVe : Vv = bound F := by rw [← hV]; unfold vars; omega
      have := Run.assign (B := B) (σ := σ4) (x := "V") (e := V "mx") (evalB_var hmxB)
      rw [hmx, ← hVe] at this
      exact (Run.ite_false (by rw [hcond, decide_eq_false h2]) this).mono
        (by simp [Cond.size, Expr.size])
  obtain ⟨σ5, hσ5⟩ : ∃ σ5, σ4.setVar "V" Vv = σ5 := ⟨_, rfl⟩
  rw [hσ5] at rV
  have v5 : ∀ v, v ≠ "V" → σ5.vars v = σ4.vars v := fun v h => by rw [← hσ5]; simp [Env.setVar, h]
  have V5 : σ5.vars "V" = Vv := by rw [← hσ5]; simp [Env.setVar]
  have a5 : σ5.arrs = σ4.arrs := by rw [← hσ5]; rfl
  have o5 : σ5.out = [] := by rw [← hσ5]; simp [Env.setVar, out4]
  have i5 : σ5.inp = [] := by rw [← hσ5]; simp [Env.setVar, inp4]
  have rn : Run B (.assign "nn" (.bin .mul (.lit 2) (V "V"))) σ5 (σ5.setVar "nn" (2 * Vv)) 4 := by
    have := Run.assign (B := B) (σ := σ5) (x := "nn") (e := .bin .mul (.lit 2) (V "V"))
      (RunStep.eval_mul B σ5 (.lit 2) (V "V") 2 Vv (evalB_lit (by omega))
        (by rw [← V5]; exact evalB_var (by rw [V5]; omega)) (by omega))
    simpa [Expr.size] using this
  have C6 : (σ5.setVar "nn" (2 * Vv)).vars "C" = F.length := by
    simp [Env.setVar]; rw [v5 _ (by decide), hC]
  have V6 : (σ5.setVar "nn" (2 * Vv)).vars "V" = Vv := by simp [Env.setVar, V5]
  have rm : Run B (.assign "m" (.bin .add (V "V") (V "C"))) (σ5.setVar "nn" (2 * Vv))
      ((σ5.setVar "nn" (2 * Vv)).setVar "m" (Vv + F.length)) 4 := by
    have := Run.assign (B := B) (σ := σ5.setVar "nn" (2 * Vv)) (x := "m")
      (e := .bin .add (V "V") (V "C"))
      (RunStep.eval_add B _ (V "V") (V "C") Vv F.length
        (by rw [← V6]; exact evalB_var (by rw [V6]; omega))
        (by rw [← C6]; exact evalB_var (by rw [C6]; omega)) (by omega))
    simpa [Expr.size] using this
  obtain ⟨σ7, hσ7⟩ : ∃ σ7, (σ5.setVar "nn" (2 * Vv)).setVar "m" (Vv + F.length) = σ7 := ⟨_, rfl⟩
  rw [hσ7] at rm
  have v7 : ∀ v, v ≠ "nn" → v ≠ "m" → σ7.vars v = σ5.vars v := fun v h1 h2 => by
    rw [← hσ7]; simp [Env.setVar, h1, h2]
  have n7 : σ7.vars "nn" = 2 * Vv := by rw [← hσ7]; simp [Env.setVar]
  have m7 : σ7.vars "m" = Vv + F.length := by rw [← hσ7]; simp [Env.setVar]
  have V7 : σ7.vars "V" = Vv := by rw [v7 _ (by decide) (by decide), V5]
  have C7 : σ7.vars "C" = F.length := by rw [v7 _ (by decide) (by decide), v5 _ (by decide), hC]
  have k7 : σ7.vars "k" = k := by rw [v7 _ (by decide) (by decide), v5 _ (by decide), hk]
  have a7 : σ7.arrs = σ4.arrs := by rw [← hσ7]; simp [Env.setVar, a5]
  have o7 : σ7.out = [] := by rw [← hσ7]; simp [Env.setVar, o5]
  have i7 : σ7.inp = [] := by rw [← hσ7]; simp [Env.setVar, i5]
  -- the three numbers
  have hS2 : 2 * Vv ≤ S := by omega
  obtain ⟨σ8, r8, o8, k8⟩ := setNat_emits (B := B) (V "nn") (fun σ => σ.vars "nn") S
    (fun σ => σ.vars "nn" = 2 * Vv) (fun σ h => evalB_var_eq rfl (by rw [h]; omega))
    (fun σ h => ⟨by rw [h]; omega, by rw [h]; exact le_trans (size_le_self _) hS2⟩) σ7 n7
  have m8 : σ8.vars "m" = Vv + F.length := by rw [k8.var (by simp [SN]), m7]
  obtain ⟨σ9, r9, o9, k9⟩ := setNat_emits (B := B) (V "m") (fun σ => σ.vars "m") S
    (fun σ => σ.vars "m" = Vv + F.length)
    (fun σ h => evalB_var_eq rfl (by rw [h]; omega))
    (fun σ h => ⟨by rw [h]; omega, by rw [h]; exact le_trans (size_le_self _) (by omega)⟩) σ8 m8
  have V9 : σ9.vars "V" = Vv := by rw [k9.var (by simp [SN]), k8.var (by simp [SN]), V7]
  obtain ⟨σ10, r10, o10, k10⟩ := setNat_emits (B := B) (V "V") (fun σ => σ.vars "V") S
    (fun σ => σ.vars "V" = Vv) (fun σ h => evalB_var_eq rfl (by rw [h]; omega))
    (fun σ h => ⟨by rw [h]; omega, by rw [h]; exact le_trans (size_le_self _) (by omega)⟩) σ9 V9
  have k710 : Keep SN σ7 σ10 := k8.trans (k9.trans k10)
  have V10 : σ10.vars "V" = Vv := by rw [k710.var (by simp [SN]), V7]
  have o10' : σ10.out = bitsNat (2 * Vv) ++ bitsNat (Vv + F.length) ++ bitsNat Vv := by
    rw [o10, o9, o8, o7]; beta_reduce; rw [n7, m8, V9]; simp
  -- the pairs
  obtain ⟨σ12, r12, o12, k12⟩ := pairsLoop_run (B := B) Vv S σ10 (by omega) (by omega)
    (le_trans (size_le_self _) (by omega)) V10
  have k712 : ∀ v, v ∉ "i" :: SN → σ12.vars v = σ7.vars v := fun v hv =>
    (k12.var hv).trans (k710.var fun h => hv (List.mem_cons_of_mem _ h))
  have a12 : σ12.arrs = σ4.arrs := by rw [k12.2.1, k710.2.1, a7]
  -- the clause sets
  have D : CData F (σ4.arrs "vr") (σ4.arrs "sg") (σ4.arrs "cl") L (2 * L + 4) S B :=
    ⟨post, by rw [lvr, hkd]; exact hsz, by rw [lsg, hkd]; exact hsz, by rw [lcl, hkd]; exact hsz,
     by rw [hkd]; exact hsz, by rw [hV]; omega, by rw [hV]; omega, by omega, by omega, by omega,
     by rw [hV]; exact le_trans (size_le_self _) hS2⟩
  obtain ⟨σ13, r13, o13, i13⟩ := clauseLoop_run (B := B) F _ _ _ L (2 * L + 4) S σ12 D
    (by rw [k712 _ (by simp [SN]), C7]) (by rw [k712 _ (by simp [SN]), k7, hkd])
    (by rw [k712 _ (by simp [SN]), n7, hV]) (by rw [a12]) (by rw [a12]) (by rw [a12])
    (by rw [a12, hmark4])
  -- together
  refine ⟨σ13, ?_, ?_⟩
  · have hrun := r4.seq ((rV.seq (rn.seq rm)).seq ((r8.seq (r9.seq r10)).seq (r12.seq r13)))
    rw [← hL] at hrun
    refine hrun.mono ?_
    rw [hL]
    unfold Kmain
    rw [hS]
    have h1 : (Kpair S + 4) * Vv ≤ (Kpair S + 4) * (L + 2) := Nat.mul_le_mul_left _ hVL
    have h2 : (Kclause S L + 4) * F.length ≤ (Kclause S L + 4) * (L + 1) :=
      Nat.mul_le_mul_left _ hFl
    simp only [Expr.size]
    omega
  · rw [o13, o12, o10', red_eq', hF, out, hV]
    simp only [List.append_assoc]
end Lax496464Proofs.HittingSet.Main
