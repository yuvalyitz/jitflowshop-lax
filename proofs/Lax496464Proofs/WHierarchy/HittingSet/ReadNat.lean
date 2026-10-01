import Lax496464Proofs.WHierarchy.HittingSet.Words
import Lax808846Proofs.Tactic

/-! # Reading one self-delimited number off the input, in IMP+

`readNat` reads the code `bitsNat v` — `v.size` ones, a zero, then the `v.size` binary digits of `v`,
least significant first — off the input tape into the scalar `rn_v`. It assumes nothing about what
follows, so it is called once per number of a Hitting Set word. Its scalars are `rn_c` (the digit
count), `rn_b` (the bit just read), `rn_i` (the digit index) and `rn_v` (the value). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.ReadNat

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.Words

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- Count the leading ones; `rn_b` holds the next unread bit. -/
def onesLoop : Com := .while (.eq (V "rn_b") (.lit 1)) (.seq (bump "rn_c") (.read "rn_b"))

/-- Read one digit and add it in. -/
def digitsBody : Com :=
  .seq (.read "rn_b")
    (.seq (.assign "rn_v" (.add (V "rn_v") (.shiftl (V "rn_b") (V "rn_i")))) (bump "rn_i"))

/-- Read `rn_c` digits. -/
def digitsLoop : Com := .seq (.assign "rn_i" (.lit 0)) (.while (.lt (V "rn_i") (V "rn_c")) digitsBody)

/-- **Read one self-delimited number into `rn_v`.** -/
def readNat : Com :=
  .seq (.assign "rn_c" (.lit 0))
    (.seq (.read "rn_b") (.seq onesLoop (.seq (.assign "rn_v" (.lit 0)) digitsLoop)))

/-- The scalars `readNat` assigns. -/
def rnVars : List String := ["rn_c", "rn_b", "rn_i", "rn_v"]

/-! ## The code, cell by cell -/

/-- The digits of `v`. -/
def digits (v : ℕ) : List ℕ := (List.range v.size).map (digit v)

theorem bitsNat_eq (v : ℕ) : bitsNat v = List.replicate v.size 1 ++ 0 :: digits v := by
  simp [bitsNat, digits]

theorem getD_ones {v c : ℕ} (rest : List ℕ) (hc : c < v.size) :
    (bitsNat v ++ rest).getD c 0 = 1 := by
  rw [bitsNat_eq, List.append_assoc]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hc]

theorem getD_sep (v : ℕ) (rest : List ℕ) : (bitsNat v ++ rest).getD v.size 0 = 0 := by
  rw [bitsNat_eq, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

theorem drop_sep (v : ℕ) (rest : List ℕ) :
    (bitsNat v ++ rest).drop (v.size + 1) = digits v ++ rest := by
  rw [bitsNat_eq, List.append_assoc]
  simp [List.drop_append]

theorem length_digits (v : ℕ) : (digits v).length = v.size := by simp [digits]

/-- A partial sum of the digit expansion is at most the number. -/
theorem partial_le (v i : ℕ) (hi : i ≤ v.size) :
    ∑ k ∈ Finset.range i, digit v k * 2 ^ k ≤ v := by
  calc ∑ k ∈ Finset.range i, digit v k * 2 ^ k
      ≤ ∑ k ∈ Finset.range v.size, digit v k * 2 ^ k :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
    _ = v := sum_digit v

/-! ## Counting the ones -/

/-- The state part-way through the ones: `rn_c` of them counted, `rn_b` the next unread bit. -/
def OnesInv (v : ℕ) (rest : List ℕ) (σ : Env) : Prop :=
  σ.vars "rn_c" ≤ v.size ∧ σ.vars "rn_b" = (bitsNat v ++ rest).getD (σ.vars "rn_c") 0 ∧
    σ.inp = (bitsNat v ++ rest).drop (σ.vars "rn_c" + 1)

theorem bit_le_one {v : ℕ} {rest : List ℕ} {c : ℕ} (hc : c ≤ v.size) :
    (bitsNat v ++ rest).getD c 0 ≤ 1 := by
  rcases Nat.lt_or_ge c v.size with h | h
  · rw [getD_ones rest h]
  · rw [show c = v.size by omega, getD_sep]; omega

theorem onesBody_spec {B : ℕ} (v : ℕ) (rest : List ℕ) (hB : v.size + 2 < B) :
    Spec B (fun σ => OnesInv v rest σ ∧ (Cond.eq (V "rn_b") (.lit 1)).evalB B σ = some true)
      (.seq (bump "rn_c") (.read "rn_b"))
      (fun σ σ' => OnesInv v rest σ' ∧ v.size - σ'.vars "rn_c" < v.size - σ.vars "rn_c") 10 := by
  refine Spec.pre (P := fun σ => OnesInv v rest σ ∧ σ.vars "rn_c" < v.size) ?_ ?_
  · intro σ ⟨⟨hc, hb, hinp⟩, hlt⟩
    have hlen : σ.vars "rn_c" + 1 < (bitsNat v ++ rest).length := by simp; omega
    have hinp' : σ.inp = (bitsNat v ++ rest).getD (σ.vars "rn_c" + 1) 0 ::
        (bitsNat v ++ rest).drop (σ.vars "rn_c" + 2) := by
      rw [hinp, List.drop_eq_getElem_cons hlen, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlen]
      rfl
    have r1 := Run.assign (B := B) (σ := σ) (x := "rn_c") (e := .add (V "rn_c") (.lit 1))
      (v := σ.vars "rn_c" + 1) (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega))
        (by simp; omega))
    have r2 := Run.read (B := B) (σ := σ.setVar "rn_c" (σ.vars "rn_c" + 1)) (x := "rn_b")
      (v := (bitsNat v ++ rest).getD (σ.vars "rn_c" + 1) 0)
      (rest := (bitsNat v ++ rest).drop (σ.vars "rn_c" + 2)) (by simpa [Env.setVar] using hinp')
    refine ⟨_, (r1.seq r2).mono (by simp), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [Env.setVar]; omega
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]; omega
  · intro σ ⟨hI, hcond⟩
    refine ⟨hI, ?_⟩
    obtain ⟨hc, hb, -⟩ := hI
    rcases Nat.lt_or_ge (σ.vars "rn_c") v.size with h | h
    · exact h
    · exfalso
      have h0 : σ.vars "rn_b" = 0 := by rw [hb, show σ.vars "rn_c" = v.size by omega, getD_sep]
      rw [evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega)), h0] at hcond
      simp at hcond

theorem onesLoop_spec {B : ℕ} (v : ℕ) (rest : List ℕ) (hB : v.size + 2 < B) :
    Spec B (fun σ => OnesInv v rest σ ∧ σ.vars "rn_c" = 0) onesLoop
      (fun _ σ' => OnesInv v rest σ' ∧ σ'.vars "rn_c" = v.size) (14 * v.size + 4) := by
  refine (Spec.while_count (OnesInv v rest) (fun σ => v.size - σ.vars "rn_c") 10 ?_
    (onesBody_spec v rest hB) (fun σ h => h.1) ?_).post ?_
  · intro σ ⟨hc, hb, _⟩
    have := bit_le_one (v := v) (rest := rest) hc
    exact ⟨_, evalB_condEq (evalB_var (by rw [hb]; omega)) (evalB_lit (by omega))⟩
  · intro σ ⟨_, h0⟩
    rw [h0]; simp
  · intro σ σ' _ ⟨hI, hf⟩
    refine ⟨hI, ?_⟩
    obtain ⟨hc, hb, -⟩ := hI
    rcases Nat.lt_or_ge (σ'.vars "rn_c") v.size with h | h
    · exfalso
      have h1 : σ'.vars "rn_b" = 1 := by rw [hb, getD_ones rest h]
      rw [evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega)), h1] at hf
      simp at hf
    · omega

/-! ## Reading the digits -/

/-- The state part-way through the digits: `rn_i` of them read and summed into `rn_v`. -/
def DigitsInv (v : ℕ) (rest : List ℕ) (σ : Env) : Prop :=
  σ.vars "rn_i" ≤ v.size ∧ σ.vars "rn_c" = v.size ∧
    σ.vars "rn_v" = ∑ k ∈ Finset.range (σ.vars "rn_i"), digit v k * 2 ^ k ∧
    σ.inp = (digits v).drop (σ.vars "rn_i") ++ rest

theorem digitsBody_spec {B : ℕ} (v : ℕ) (rest : List ℕ) (hvB : v < B) (hB : v.size + 2 < B) :
    Spec B (fun σ => DigitsInv v rest σ ∧ σ.vars "rn_i" < v.size) digitsBody
      (fun σ σ' => DigitsInv v rest σ' ∧ σ'.vars "rn_i" = σ.vars "rn_i" + 1) 14 := by
  intro σ ⟨⟨hi, hc, hv, hinp⟩, hlt⟩
  set i := σ.vars "rn_i" with hi_def
  have hlen : i < (digits v).length := by rw [length_digits]; exact hlt
  have hinp' : σ.inp = digit v i :: ((digits v).drop (i + 1) ++ rest) := by
    rw [hinp, List.drop_eq_getElem_cons hlen]
    have : (digits v)[i] = digit v i := by simp [digits]
    rw [this]; rfl
  have hsum1 := partial_le v (i + 1) (by omega)
  rw [Finset.sum_range_succ] at hsum1
  have r1 := Run.read (B := B) (σ := σ) (x := "rn_b") hinp'
  set σ1 : Env := { σ.setVar "rn_b" (digit v i) with inp := (digits v).drop (i + 1) ++ rest }
    with hσ1
  have h1b : σ1.vars "rn_b" = digit v i := by simp [hσ1, Env.setVar]
  have h1i : σ1.vars "rn_i" = i := by simp [hσ1, Env.setVar, hi_def]
  have h1v : σ1.vars "rn_v" = σ.vars "rn_v" := by simp [hσ1, Env.setVar]
  have hdl := digit_le_one v i
  have e1 : (Expr.bin .shiftl (V "rn_b") (V "rn_i")).evalB B σ1 = some (digit v i * 2 ^ i) := by
    have := evalB_bin (B := B) (op := .shiftl) (σ := σ1) (evalB_var (x := "rn_b") (by omega))
      (evalB_var (x := "rn_i") (by omega)) (by rw [h1b, h1i]; simp; omega)
    rw [h1b, h1i] at this; simpa using this
  have e2 : (Expr.add (V "rn_v") (.shiftl (V "rn_b") (V "rn_i"))).evalB B σ1 =
      some (σ.vars "rn_v" + digit v i * 2 ^ i) := by
    have := evalB_bin (B := B) (op := .add) (σ := σ1) (evalB_var (x := "rn_v") (by omega)) e1
      (by rw [h1v]; simp; omega)
    rw [h1v] at this; simpa using this
  have r2 := Run.assign (B := B) (σ := σ1) (x := "rn_v") e2
  set σ2 := σ1.setVar "rn_v" (σ.vars "rn_v" + digit v i * 2 ^ i) with hσ2
  have h2i : σ2.vars "rn_i" = i := by simp [hσ2, Env.setVar, h1i]
  have r3 := Run.assign (B := B) (σ := σ2) (x := "rn_i") (e := .add (V "rn_i") (.lit 1))
    (v := i + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "rn_i") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h2i]; simp; omega)
      rw [h2i] at this; simpa using this)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [Env.setVar]; omega
  · simp [hσ2, hσ1, Env.setVar, hc]
  · simp [hσ2, hσ1, Env.setVar, hv, Finset.sum_range_succ]
  · simp [hσ2, hσ1, Env.setVar]
  · simp [Env.setVar, hi_def]

theorem digitsLoop_spec {B : ℕ} (v : ℕ) (rest : List ℕ) (hvB : v < B) (hB : v.size + 2 < B) :
    Spec B (fun σ => DigitsInv v rest (σ.setVar "rn_i" 0)) digitsLoop
      (fun _ σ' => DigitsInv v rest σ' ∧ σ'.vars "rn_i" = v.size) (18 * v.size + 6) :=
  Spec.forRangeZero "rn_i" "rn_c" (DigitsInv v rest) v.size 14 (by omega) (fun _ h => h.1)
    (fun _ h => h.2.1) (digitsBody_spec v rest hvB hB)

/-! ## Reading the number -/

theorem readNat_core {B : ℕ} (v : ℕ) (rest : List ℕ) (hvB : v < B) (hB : v.size + 2 < B) :
    Spec B (fun σ => σ.inp = bitsNat v ++ rest) readNat
      (fun _ σ' => σ'.vars "rn_v" = v ∧ σ'.inp = rest) (32 * v.size + 20) := by
  intro σ hinp
  have hlen : 0 < (bitsNat v ++ rest).length := by simp
  have hinp' : σ.inp = (bitsNat v ++ rest).getD 0 0 :: (bitsNat v ++ rest).drop 1 := by
    rw [hinp]
    rcases h : bitsNat v ++ rest with _ | ⟨a, l⟩
    · rw [h] at hlen; simp at hlen
    · rfl
  have r1 := Run.assign (B := B) (σ := σ) (x := "rn_c") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  have r2 := Run.read (B := B) (σ := σ.setVar "rn_c" 0) (x := "rn_b")
    (v := (bitsNat v ++ rest).getD 0 0) (rest := (bitsNat v ++ rest).drop 1)
    (by simpa [Env.setVar] using hinp')
  set σ2 : Env := { (σ.setVar "rn_c" 0).setVar "rn_b" ((bitsNat v ++ rest).getD 0 0) with
    inp := (bitsNat v ++ rest).drop 1 } with hσ2
  obtain ⟨σ3, r3, ⟨_, _, hinp3⟩, hc3⟩ := (onesLoop_spec (B := B) v rest hB).run (σ := σ2)
    ⟨⟨by simp [hσ2, Env.setVar], by simp [hσ2, Env.setVar], by simp [hσ2, Env.setVar]⟩,
      by simp [hσ2, Env.setVar]⟩
  have r4 := Run.assign (B := B) (σ := σ3) (x := "rn_v") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  obtain ⟨σ5, r5, ⟨_, _, hv5, hinp5⟩, hi5⟩ :=
    (digitsLoop_spec (B := B) v rest hvB hB).run (σ := σ3.setVar "rn_v" 0)
      ⟨by simp [Env.setVar], by simp [Env.setVar, hc3], by simp [Env.setVar],
        by simp [Env.setVar]; rw [hinp3, hc3, drop_sep]⟩
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp; omega), ?_, ?_⟩
  · rw [hv5, hi5, sum_digit]
  · rw [hinp5, hi5, ← length_digits, List.drop_length, List.nil_append]

/-- **The reader.** From a tape starting with the code of `v`, `readNat` leaves `v` in `rn_v` and
the tape just past the code, and changes nothing else but its own four scalars. -/
theorem readNat_spec {B : ℕ} (v : ℕ) (rest : List ℕ) (hvB : v < B) (hB : v.size + 2 < B) :
    Spec B (fun σ => σ.inp = bitsNat v ++ rest) readNat
      (fun σ σ' => σ'.vars "rn_v" = v ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧ σ'.arrs = σ.arrs ∧
        ∀ y, y ∉ rnVars → σ'.vars y = σ.vars y) (32 * v.size + 20) := by
  refine (readNat_core v rest hvB hB).frame.post ?_
  rintro σ σ' - ⟨⟨hv, hinp⟩, hvars, harrs, -, hout⟩
  refine ⟨hv, hinp, hout (by decide), ?_, ?_⟩
  · funext a
    exact harrs a (by simp [readNat, onesLoop, digitsLoop, digitsBody, Com.warrs])
  · intro y hy
    refine hvars y ?_
    simp only [rnVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [readNat, onesLoop, digitsLoop, digitsBody, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

end Lax496464Proofs.WHierarchy.HittingSet.ReadNat
