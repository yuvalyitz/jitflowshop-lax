import Lax496464Proofs.Ram.BitsNat
import Lax808846Proofs.Reasoning
import Lax808846Proofs.Spec

/-!
# Writing One Self-Delimited Number to the Output

`printNat` writes `bitsNat v` — `v.size` ones, a zero, then `v.size` binary digits, least
significant first — to the output tape, reading `v` off `"vv"` and touching no other input.
This is the mirror of `Ram/DecodeNat.lean`'s `readNat`, needed to re-encode the reduction's
numeric output back into bits.
-/

namespace Lax496464Proofs.Ram.PrintNat

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.BitsNat

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-! ## Computing the digit count -/

def sizeBody : Com :=
  .seq (bump "cnt") (.assign "tt" (.bin .shiftr (V "tt") (.lit 1)))

def sizeLoop : Com := .while (.lt (.lit 0) (V "tt")) sizeBody

def computeSize : Com := .seq (.assign "tt" (V "vv")) (.seq (.assign "cnt" (.lit 0)) sizeLoop)

/-! ## Writing the ones, the separator and the digits -/

def onesOutBody : Com := .seq (.write (.lit 1)) (bump "jj")
def onesOutLoop : Com := .seq (.assign "jj" (.lit 0)) (.while (.lt (V "jj") (V "cnt")) onesOutBody)

def digitsOutBody : Com :=
  .seq (.assign "xx" (.bin .shiftr (V "vv") (V "jj")))
    (.seq (.write (.bin .sub (V "xx") (.bin .mul (.lit 2) (.bin .shiftr (V "xx") (.lit 1)))))
      (bump "jj"))
def digitsOutLoop : Com :=
  .seq (.assign "jj" (.lit 0)) (.while (.lt (V "jj") (V "cnt")) digitsOutBody)

/-- Write `bitsNat v`, reading `v` off `"vv"`. -/
def printNat : Com :=
  .seq computeSize (.seq onesOutLoop (.seq (.write (.lit 0)) digitsOutLoop))

variable {B v : ℕ}

/-! ## The digit count -/

/-- `"tt"` never exceeds `v` (it starts there and only shrinks), and together with `"cnt"`
its size always adds up to `v.size`. -/
def SizeInv (v : ℕ) (σ : Env) : Prop :=
  σ.vars "vv" = v ∧ σ.vars "tt" ≤ v ∧ (σ.vars "tt").size + σ.vars "cnt" = v.size

theorem sizeLoop_body_spec (hB : 1 < B) (hvB : v < B) :
    Spec B (fun σ => SizeInv v σ ∧ (Cond.lt (.lit 0) (V "tt")).evalB B σ = some true) sizeBody
      (fun σ σ' => SizeInv v σ' ∧ (σ'.vars "tt").size < (σ.vars "tt").size) 8 := by
  rintro σ ⟨⟨hvv, hle, hsz⟩, hcond⟩
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hcond
  obtain ⟨m, k, ⟨rfl, -⟩, ⟨rfl, hkB⟩, hr⟩ := hcond
  have htt : 0 < σ.vars "tt" := by simpa using hr.symm
  have httB : σ.vars "tt" < B := by omega
  have hsv : v.size ≤ v := size_le_self v
  have hpos : 0 < (σ.vars "tt").size := by rw [Nat.size_pos]; omega
  have hcc1B : σ.vars "cnt" + 1 < B := by omega
  have hccB : σ.vars "cnt" < B := by omega
  have hr1 : Run B (bump "cnt") σ (σ.setVar "cnt" (σ.vars "cnt" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hccB) (evalB_lit (by omega))
      (by rw [Bop.apply_add]; exact hcc1B))
  set σ1 : Env := σ.setVar "cnt" (σ.vars "cnt" + 1) with hσ1
  clear_value σ1
  have hvv1 : σ1.vars "vv" = v := by rw [hσ1]; simp [Env.setVar]; exact hvv
  have htt1 : σ1.vars "tt" = σ.vars "tt" := by rw [hσ1]; simp [Env.setVar]
  have hcnt1 : σ1.vars "cnt" = σ.vars "cnt" + 1 := by rw [hσ1]; simp [Env.setVar]
  have httB1 : σ1.vars "tt" < B := by rw [htt1]; exact httB
  have h1B : (1 : ℕ) < B := hB
  have hr2 : Run B (.assign "tt" (.bin .shiftr (V "tt") (.lit 1))) σ1
      (σ1.setVar "tt" (Bop.shiftr.apply (σ1.vars "tt") 1)) 4 :=
    Run.assign (evalB_bin (evalB_var httB1) (evalB_lit h1B) (by
      simp only [Bop.apply_shiftr]; rw [htt1]; omega))
  refine ⟨_, hr1.seq hr2, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [Env.setVar]; rw [hvv1]
  · simp [Env.setVar, Bop.apply_shiftr]; rw [htt1]; omega
  · simp [Env.setVar, Bop.apply_shiftr, htt1]
    have hne : σ.vars "tt" ≠ 0 := by omega
    have hstep := size_succ_of_ne_zero hne
    rw [hcnt1]
    omega
  · simp [Env.setVar, Bop.apply_shiftr, htt1]
    have hne : σ.vars "tt" ≠ 0 := by omega
    have hstep := size_succ_of_ne_zero hne
    have hpos : 0 < (σ.vars "tt").size := by
      rw [Nat.size_pos]; omega
    omega

theorem sizeLoop_spec (hB : 1 < B) (hvB : v < B) :
    Spec B (SizeInv v) sizeLoop (fun _ σ' => SizeInv v σ' ∧ σ'.vars "tt" = 0)
      (12 * v.size + 4) := by
  have hsize : (Cond.lt (Expr.lit 0) (V "tt")).size = 3 := by simp
  refine (Spec.while_count (b := .lt (.lit 0) (V "tt")) (c := sizeBody)
    (SizeInv v) (fun σ => (σ.vars "tt").size) 8 ?_ (sizeLoop_body_spec hB hvB)
    (fun _ h => h) ?_).post ?_
  · rintro σ ⟨hvv, hle, hsz⟩
    have h0B : (0 : ℕ) < B := by omega
    have httB : σ.vars "tt" < B := by omega
    exact ⟨_, evalB_condLt (evalB_lit h0B) (evalB_var httB)⟩
  · rintro σ ⟨hvv, hle, hsz⟩; simp only [hsize]; omega
  · rintro σ σ' hσ ⟨hI, hfalse⟩
    refine ⟨hI, ?_⟩
    simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hfalse
    obtain ⟨m, k, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := hfalse
    have : ¬ (0 < σ'.vars "tt") := by simpa using hr.symm
    omega

theorem computeSize_spec (hB : 1 < B) (hvB : v < B) :
    Spec B (fun σ => σ.vars "vv" = v) computeSize
      (fun _σ σ' => σ'.vars "vv" = v ∧ σ'.vars "cnt" = v.size ∧ σ'.vars "tt" = 0)
      (12 * v.size + 10) := by
  rintro σ hvv
  have h1 : Run B (.assign "tt" (V "vv")) σ (σ.setVar "tt" (σ.vars "vv")) 2 :=
    Run.assign (evalB_var (by omega))
  set σ1 : Env := σ.setVar "tt" (σ.vars "vv") with hσ1
  clear_value σ1
  have hvv1 : σ1.vars "vv" = v := by rw [hσ1]; simp [Env.setVar]; exact hvv
  have htt1 : σ1.vars "tt" = v := by rw [hσ1]; simp [Env.setVar]; exact hvv
  have h2 : Run B (.assign "cnt" (.lit 0)) σ1 (σ1.setVar "cnt" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  set σ2 : Env := σ1.setVar "cnt" 0 with hσ2
  clear_value σ2
  have hvv2 : σ2.vars "vv" = v := by rw [hσ2]; simp [Env.setVar]; exact hvv1
  have htt2 : σ2.vars "tt" = v := by rw [hσ2]; simp [Env.setVar]; exact htt1
  have hcnt2 : σ2.vars "cnt" = 0 := by rw [hσ2]; simp [Env.setVar]
  have hI2 : SizeInv v σ2 := ⟨hvv2, by rw [htt2], by rw [htt2, hcnt2]; omega⟩
  obtain ⟨σ3, hr3, hI3, htt3⟩ := (sizeLoop_spec hB hvB).run hI2
  refine ⟨σ3, (h1.seq (h2.seq hr3)).mono (by omega), ⟨hI3.1, ?_, htt3⟩⟩
  obtain ⟨-, -, hsz3⟩ := hI3
  rw [htt3] at hsz3
  simp at hsz3
  omega

/-! ## Writing the ones -/

def OnesOutInv (N v : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "jj" ≤ N ∧ σ.vars "cnt" = N ∧ σ.vars "vv" = v ∧
    σ.out = out0 ++ List.replicate (σ.vars "jj") 1

theorem onesOutBody_spec (N : ℕ) (hNB : N < B) (out0 : List ℕ) :
    Spec B (fun σ => OnesOutInv N v out0 σ ∧ σ.vars "jj" < N) onesOutBody
      (fun σ σ' => OnesOutInv N v out0 σ' ∧ σ'.vars "jj" = σ.vars "jj" + 1) 6 := by
  rintro σ ⟨⟨hle, hcnt, hvv, hout⟩, hjlt⟩
  have hjjB : σ.vars "jj" < B := by omega
  have hr1 : Run B (.write (.lit 1)) σ { σ with out := σ.out ++ [1] } 2 :=
    Run.write (evalB_lit (by omega))
  set σ1 : Env := { σ with out := σ.out ++ [1] } with hσ1
  clear_value σ1
  have hjj1 : σ1.vars "jj" = σ.vars "jj" := by rw [hσ1]
  have hcnt1 : σ1.vars "cnt" = σ.vars "cnt" := by rw [hσ1]
  have hvv1 : σ1.vars "vv" = σ.vars "vv" := by rw [hσ1]
  have hout1 : σ1.out = σ.out ++ [1] := by rw [hσ1]
  have hjjB1 : σ1.vars "jj" < B := by rw [hjj1]; exact hjjB
  have hr2 : Run B (bump "jj") σ1 (σ1.setVar "jj" (σ1.vars "jj" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hjjB1) (evalB_lit (by omega))
      (by rw [Bop.apply_add]; omega))
  refine ⟨_, hr1.seq hr2, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [Env.setVar]; rw [hjj1]; omega
  · simp [Env.setVar]; rw [hcnt1]; exact hcnt
  · simp [Env.setVar]; rw [hvv1]; exact hvv
  · simp [Env.setVar, hout1, hout, hjj1]
    rw [List.replicate_succ']
  · simp [Env.setVar]; rw [hjj1]

theorem onesOutLoop_spec (N : ℕ) (hNB : N < B) (out0 : List ℕ) :
    Spec B (fun σ => OnesOutInv N v out0 (σ.setVar "jj" 0)) onesOutLoop
      (fun _ σ' => OnesOutInv N v out0 σ' ∧ σ'.vars "jj" = N) ((6 + 4) * N + 6) :=
  Spec.forRangeZero "jj" "cnt" (OnesOutInv N v out0) N 6 hNB
    (fun _ h => h.1) (fun _ h => h.2.1) (onesOutBody_spec N hNB out0)

/-! ## Writing the digits -/

def DigitsOutInv (N v : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "jj" ≤ N ∧ σ.vars "cnt" = N ∧ σ.vars "vv" = v ∧
    σ.out = out0 ++ (List.range (σ.vars "jj")).map (digit v)

theorem digitsOutBody_spec (N : ℕ) (hB : 2 < B) (hNB : N < B) (hvB : v < B) (out0 : List ℕ) :
    Spec B (fun σ => DigitsOutInv N v out0 σ ∧ σ.vars "jj" < N) digitsOutBody
      (fun σ σ' => DigitsOutInv N v out0 σ' ∧ σ'.vars "jj" = σ.vars "jj" + 1) 16 := by
  rintro σ ⟨⟨hle, hcnt, hvv, hout⟩, hjlt⟩
  have hjjB : σ.vars "jj" < B := by omega
  have hvvB : σ.vars "vv" < B := by omega
  have hxval : Bop.shiftr.apply (σ.vars "vv") (σ.vars "jj") = σ.vars "vv" / 2 ^ σ.vars "jj" := rfl
  have hxB : σ.vars "vv" / 2 ^ σ.vars "jj" < B := by
    have := Nat.div_le_self (σ.vars "vv") (2 ^ σ.vars "jj")
    omega
  have hr1 : Run B (.assign "xx" (.bin .shiftr (V "vv") (V "jj"))) σ
      (σ.setVar "xx" (σ.vars "vv" / 2 ^ σ.vars "jj")) 4 :=
    Run.assign (evalB_bin (evalB_var hvvB) (evalB_var hjjB) (by rw [hxval]; exact hxB))
  set σ1 : Env := σ.setVar "xx" (σ.vars "vv" / 2 ^ σ.vars "jj") with hσ1
  clear_value σ1
  have hxx1 : σ1.vars "xx" = σ.vars "vv" / 2 ^ σ.vars "jj" := by rw [hσ1]; simp [Env.setVar]
  have hjj1 : σ1.vars "jj" = σ.vars "jj" := by rw [hσ1]; simp [Env.setVar]
  have hcnt1 : σ1.vars "cnt" = σ.vars "cnt" := by rw [hσ1]; simp [Env.setVar]
  have hvv1 : σ1.vars "vv" = v := by rw [hσ1]; simp [Env.setVar]; exact hvv
  have hxxB : σ1.vars "xx" < B := by rw [hxx1]; exact hxB
  have hval : σ1.vars "xx" - 2 * (σ1.vars "xx" / 2) = digit v (σ.vars "jj") := by
    have hxxeq : σ1.vars "xx" = v / 2 ^ σ.vars "jj" := by rw [hxx1, hvv]
    rw [hxxeq]; unfold digit; omega
  have hvalB : σ1.vars "xx" - 2 * (σ1.vars "xx" / 2) < B := by omega
  have hr2 : Run B (.write (.bin .sub (V "xx") (.bin .mul (.lit 2) (.bin .shiftr (V "xx") (.lit 1)))))
      σ1 { σ1 with out := σ1.out ++ [σ1.vars "xx" - 2 * (σ1.vars "xx" / 2)] } 8 :=
    Run.write (evalB_bin (evalB_var hxxB)
      (evalB_bin (evalB_lit (by omega))
        (evalB_bin (evalB_var hxxB) (evalB_lit (by omega))
          (by simp only [Bop.apply_shiftr]; omega))
        (by simp only [Bop.apply_mul]; omega))
      (by simp only [Bop.apply_sub]; exact hvalB))
  set σ2 : Env := { σ1 with out := σ1.out ++ [σ1.vars "xx" - 2 * (σ1.vars "xx" / 2)] }
    with hσ2
  clear_value σ2
  have hjj2 : σ2.vars "jj" = σ.vars "jj" := by rw [hσ2]; simp; exact hjj1
  have hcnt2 : σ2.vars "cnt" = σ.vars "cnt" := by rw [hσ2]; simp; exact hcnt1
  have hvv2 : σ2.vars "vv" = v := by rw [hσ2]; simp; exact hvv1
  have hout2 : σ2.out = σ1.out ++ [digit v (σ.vars "jj")] := by rw [hσ2]; simp; rw [hval]
  have hjjB2 : σ2.vars "jj" < B := by rw [hjj2]; exact hjjB
  have hr3 : Run B (bump "jj") σ2 (σ2.setVar "jj" (σ2.vars "jj" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var hjjB2) (evalB_lit (by omega))
      (by rw [Bop.apply_add]; omega))
  refine ⟨_, hr1.seq (hr2.seq hr3), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [Env.setVar]; rw [hjj2]; omega
  · simp [Env.setVar]; rw [hcnt2]; exact hcnt
  · simp [Env.setVar]; rw [hvv2]
  · simp [Env.setVar]
    rw [hjj2, hout2, hσ1]
    show σ.out ++ [digit v (σ.vars "jj")] = out0 ++ (List.range (σ.vars "jj" + 1)).map (digit v)
    rw [hout, List.range_succ, List.map_append]
    simp
  · simp [Env.setVar]; rw [hjj2]

theorem digitsOutLoop_spec (N : ℕ) (hB : 2 < B) (hNB : N < B) (hvB : v < B) (out0 : List ℕ) :
    Spec B (fun σ => DigitsOutInv N v out0 (σ.setVar "jj" 0)) digitsOutLoop
      (fun _ σ' => DigitsOutInv N v out0 σ' ∧ σ'.vars "jj" = N) ((16 + 4) * N + 6) :=
  Spec.forRangeZero "jj" "cnt" (DigitsOutInv N v out0) N 16 hNB
    (fun _ h => h.1) (fun _ h => h.2.1) (digitsOutBody_spec N hB hNB hvB out0)

/-! ## Writing the number -/

theorem printNat_spec (hB : 2 < B) (hvB : v < B) :
    Spec B (fun σ => σ.vars "vv" = v) printNat
      (fun σ σ' => σ'.out = σ.out ++ bitsNat v) (42 * v.size + 24) := by
  rintro σ hvv
  have h1B : (1 : ℕ) < B := by omega
  have hsvB : v.size < B := by have := size_le_self v; omega
  obtain ⟨σ1, hr1, hvv1, hcnt1, htt1⟩ := (computeSize_spec h1B hvB).run hvv
  have hout1 : σ1.out = σ.out := Run.out_eq hr1 (by simp [Com.NoWrite, computeSize, sizeLoop, sizeBody])
  have hI1 : OnesOutInv v.size v σ.out (σ1.setVar "jj" 0) := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simp [Env.setVar]; exact hcnt1
    · simp [Env.setVar]; exact hvv1
    · simp [Env.setVar, hout1]
  obtain ⟨σ2, hr2, hI2, hjj2⟩ := (onesOutLoop_spec v.size hsvB σ.out).run hI1
  obtain ⟨-, hcnt2, hvv2, hout2⟩ := hI2
  have hvv2B : σ2.vars "vv" < B := by omega
  have hr3 : Run B (.write (.lit 0)) σ2 { σ2 with out := σ2.out ++ [0] } 2 :=
    Run.write (evalB_lit (by omega))
  set σ3 : Env := { σ2 with out := σ2.out ++ [0] } with hσ3
  clear_value σ3
  have hcnt3 : σ3.vars "cnt" = v.size := by rw [hσ3]; exact hcnt2
  have hvv3 : σ3.vars "vv" = v := by rw [hσ3]; exact hvv2
  have hout3 : σ3.out = σ2.out ++ [0] := by rw [hσ3]
  have hI3 : DigitsOutInv v.size v (σ.out ++ List.replicate v.size 1 ++ [0]) (σ3.setVar "jj" 0) := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simp [Env.setVar]; exact hcnt3
    · simp [Env.setVar]; exact hvv3
    · simp [Env.setVar]; rw [hout3, hout2, hjj2, List.append_assoc]
  obtain ⟨σ4, hr4, hI4, hjj4⟩ :=
    (digitsOutLoop_spec v.size hB hsvB hvB (σ.out ++ List.replicate v.size 1 ++ [0])).run hI3
  obtain ⟨-, -, -, hout4⟩ := hI4
  refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq hr4))).mono (by omega), ?_⟩
  show σ4.out = σ.out ++ bitsNat v
  rw [hout4, hjj4]
  unfold bitsNat
  simp [List.append_assoc]

end Lax496464Proofs.Ram.PrintNat
