import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Main
import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Correct
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # The complement map is computable in polynomial time on graph words

The IMP+ program `readTape; body` is compiled under a layout of its scalars and the two arrays `a`
and `mat`; `ImpBridge.polyTimeOn_of_solves` turns its verified run into `PolyTimeOn`. Its values
stay below `2 ^ (2 bitSize x + 4)` and its cost is at most `1000 (|x| + 1)^2`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.PolyTime

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Machine Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Fill Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Passes
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Rows Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Main

/-- The layout: the reader's scalars, the body's, and the arrays `a` and `mat`. -/
def layout : Layout := ⟨ReadTape.readVars ++ bodyVars, ["a", "mat"], 8⟩

set_option maxHeartbeats 4000000 in
theorem cmd_ok : Com.Ok layout cmd := by
  simp [layout, cmd, ReadTape.readTape, ReadTape.readLoop, ReadTape.readBody, ReadTape.readVars,
    ReadTape.V, body, header, fill, fillRow, innerLoop, fillInner, adjCom, rowCount, emitIf,
    rowEmit, pass1, pass2, pass3, tailK, bump, bodyVars, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

/-- The array lengths of the initial environment. -/
def extOf (x : List ℕ) (a : String) : ℕ :=
  if a = "a" then x.length else if a = "mat" then nOf x * nOf x else 0

/-- The cost of the whole program. -/
def Kall (x : List ℕ) : ℕ := 16 * x.length + 7 + Kbody x

theorem cmd_run {x : List ℕ} (hd : Dom x) {B : ℕ} (hB : BOK x B) (hxB : ∀ v ∈ x, v < B)
    (hk : kOf x < B) :
    ∃ σ', Run B cmd (initEnv (extOf x) (x.length :: x)) σ' (Kall x) ∧ σ'.out = complWord x := by
  have hlen : x.length < B := by have hb : x.length + nOf x * nOf x + 4 < B := hB; omega
  have h1 := ReadTape.readTape_spec x (initEnv (extOf x) (x.length :: x)) hxB hlen rfl
    (by simp [initEnv, extOf])
  have h2 := body_spec hd hB hk
  have h := Spec.seq (R := fun _ σ'' => σ''.out = complWord x) h1 h2 ?_ ?_
  · obtain ⟨σ', hr, hq⟩ := h _ rfl
    exact ⟨σ', hr, hq⟩
  · rintro σ σ' rfl ⟨ha, hn, -, -, -, harr⟩
    refine ⟨ha, ?_, hn⟩
    rw [harr "mat" (by decide)]
    simp [initEnv, extOf]
  · rintro σ σ' σ'' rfl ⟨-, -, -, hout, -⟩ hq
    rw [hq, hout]
    simp [initEnv]

/-! ### Sizes -/

/-- The value bound. -/
def Bv (x : List ℕ) : ℕ := 2 ^ (2 * bitSize x + 4)

theorem kOf_mem {x : List ℕ} (hx : x ≠ []) : kOf x ∈ x := by
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · exact absurd rfl hx
  · simp [kOf]

theorem sq_lt_Bv (x : List ℕ) : bitSize x + bitSize x * bitSize x + 4 < Bv x := by
  unfold Bv
  have h1 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have h2 : bitSize x * bitSize x < 2 ^ bitSize x * 2 ^ bitSize x :=
    Nat.mul_lt_mul'' h1 h1
  have h3 : 2 ^ (2 * bitSize x + 4) = 16 * (2 ^ bitSize x * 2 ^ bitSize x) := by
    rw [← Nat.pow_add]; rw [show 2 * bitSize x + 4 = 4 + (bitSize x + bitSize x) by omega,
      Nat.pow_add]
  have h4 : 1 ≤ 2 ^ bitSize x := Nat.one_le_two_pow
  have h5 : 1 ≤ 2 ^ bitSize x * 2 ^ bitSize x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [h3]
  nlinarith

theorem bok_Bv {x : List ℕ} (hd : Dom x) : BOK x (Bv x) := by
  unfold BOK
  have hl := length_le_bitSize x
  have hn := hd.n_le
  have hsq : nOf x * nOf x ≤ bitSize x * bitSize x := Nat.mul_le_mul (by omega) (by omega)
  have := sq_lt_Bv x
  omega

theorem mem_lt_Bv {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v < Bv x := by
  have h := lt_two_pow_bitSize hv
  have : 2 ^ bitSize x ≤ Bv x := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem len_lt_Bv (x : List ℕ) : x.length < Bv x := by
  have hl := length_le_bitSize x
  have := sq_lt_Bv x
  omega

/-- The cost is quadratic. -/
theorem Kall_le {x : List ℕ} (hd : Dom x) : Kall x ≤ 1000 * (x.length + 1) ^ 2 := by
  have hn := hd.n_le
  unfold Kall Kbody Kfill K1 K3 Krow
  have hnn : nOf x * nOf x ≤ x.length * x.length := Nat.mul_le_mul (by omega) (by omega)
  have hln : x.length * nOf x ≤ x.length * x.length := Nat.mul_le_mul le_rfl (by omega)
  have e : (x.length + 1) ^ 2 = x.length * x.length + 2 * x.length + 1 := by ring
  rw [e]
  nlinarith

/-- Every entry of the complement word is at most `n²` or is the parameter. -/
theorem entry_le {x : List ℕ} {v : ℕ} (hv : v ∈ complWord x) :
    v ≤ nOf x * nOf x ∨ v = kOf x := by
  rw [complWord_eq] at hv
  have hN : nOf x ≤ nOf x * nOf x := Nat.le_mul_self _
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | ((⟨s, hs, rfl⟩ | ⟨s, hs, ht⟩) | rfl)
  · left; exact hN
  · left; have := psum_le_sq (x := x) le_rfl; omega
  · left; omega
  · left; exact psum_le_sq (by omega)
  · left; have := (mem_nbW.mp ht).1; omega
  · right; rfl

/-- **The complement map runs in polynomial time on graph words.** -/
theorem polyTimeOn_complWord : PolyTimeOn GraphInstances complWord := by
  refine polyTimeOn_of_solves (L := layout) (c := cmd) (B := fun y => Bv y.tail)
    (K := fun y => Kall y.tail) (c₀ := 20000) (d := 2) ?_ ?_ ?_ ?_
  · refine ⟨cmd_ok, ?_, ?_⟩
    · rintro y ⟨x, -, rfl⟩ v hv
      simp only [List.tail_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact len_lt_Bv x
      · exact mem_lt_Bv hv'
    · rintro y ⟨x, hx, rfl⟩
      simp only [List.tail_cons]
      have hd := dom_of_mem hx
      have hne : x ≠ [] := by
        intro h; have := hd.n_le; rw [h] at this; simp at this
      obtain ⟨σ', hr, hq⟩ := cmd_run hd (bok_Bv hd) (fun v hv => mem_lt_Bv hv)
        (mem_lt_Bv (kOf_mem hne))
      exact ⟨extOf x, σ', hr, hq⟩
  · intro x _
    simp only [List.tail_cons]
    have h1 : 16 ≤ Bv x := by
      unfold Bv
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (Bv x) = 24 + 2 * Bv x := by
      simp [Layout.span, layout, ReadTape.readVars, bodyVars]
    rw [hspan]
    have hb : 2 * bitSize x + 6 ≤ 20000 * (bitSize x + 1) ^ 2 := by nlinarith
    have hpow : 2 ^ (2 * bitSize x + 6) = 4 * Bv x := by
      unfold Bv; rw [show 2 * bitSize x + 6 = (2 * bitSize x + 4) + 2 by omega, Nat.pow_add]
      ring
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hb
    rw [hpow] at this
    refine max_le (by omega) (by omega)
  · intro x hx
    simp only [List.tail_cons]
    have hd := dom_of_mem hx
    have hK := Kall_le hd
    have hl := length_le_bitSize x
    have hsq : (x.length + 1) ^ 2 ≤ (bitSize x + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (bitSize x + 1) ^ 2 := by positivity
    simp only [Layout.const]
    omega
  · intro x hx v hv
    have hd := dom_of_mem hx
    have hne : x ≠ [] := by
      intro h; have := hd.n_le; rw [h] at this; simp at this
    have hk := lt_two_pow_bitSize (kOf_mem hne)
    have hmono : 2 ^ bitSize x ≤ 2 ^ (20000 * (bitSize x + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hBv : Bv x ≤ 2 ^ (20000 * (bitSize x + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hsq := bok_Bv hd
    unfold BOK at hsq
    rcases entry_le hv with h | h
    · omega
    · omega

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.PolyTime
