import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgMain
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # The incidence reduction runs in polynomial time

The IMP+ program `readTape; body` is compiled under a layout of its scalars and the one array `a`;
`ImpBridge.polyTimeOn_of_solves` turns its verified run into `PolyTimeOn`. Its values stay below
`2 ^ (bitSize x + 4)` and its cost is at most cubic in the length of the word. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.PolyTime

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A1_FptTime
open Lax496464Proofs.WHierarchy.Machine Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgHead
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgPre Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutE Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgForm Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgMain

/-- The layout: the reader's scalars, the body's, and the array `a`. -/
def layout : Layout := ⟨ReadTape.readVars ++ bodyVars, ["a"], 8⟩

set_option maxHeartbeats 8000000 in
theorem cmd_ok : Com.Ok layout cmd := by
  simp [layout, cmd, ReadTape.readTape, ReadTape.readLoop, ReadTape.readBody, ReadTape.readVars,
    ReadTape.V, body, header, blockBody, blockLoop, blocks, maxBody, maxLoop, maxPass, preRel,
    preBody, preLoop, prePass, onesLoop, twosLoop, headOut, pElemBody, pElemLoop, pBody, pLoop,
    pOut, ecBody, ecLoop, eCountC, pairBody, pairLoop, eeBody, eeLoop, eEmitC, eBody, eOut, qBody,
    qOut, argBody, argLoop, pComp, relTail, relOut, eqOut, exOut, otherOut, fBody, fLoop, fOut,
    bump, A, V, bodyVars, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

/-! ### Outputs stay below the bound -/

theorem bigStepB_out {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k)
    (hσ : ∀ v ∈ σ.out, v < B) : ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact hσ
  | assign _ => exact hσ
  | store _ _ _ => exact hσ
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read _ => exact hσ
  | write he =>
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hσ v hv
    · exact (Expr.eval_and_lt_of_evalB he).2

/-! ### The run -/

/-- The array lengths of the initial environment. -/
def extOf (x : List ℕ) (a : String) : ℕ := if a = "a" then x.length else 0

/-- The cost of the whole program. -/
def Kall (x : List ℕ) (φ : Formula) : ℕ := 16 * x.length + 7 + Kbody x φ

theorem cmd_run {x : List ℕ} {φ : Formula} (hd : Dom x φ) {B : ℕ} (hB : BOK x B) :
    ∃ σ', Run B cmd (initEnv (extOf x) (x.length :: x)) σ' (Kall x φ) ∧
      σ'.out = outWord x φ := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hxB : ∀ v ∈ x, v < B := fun v hv => by have := le_maxEntry hv; omega
  have h1 := ReadTape.readTape_spec x (initEnv (extOf x) (x.length :: x)) hxB (by omega) rfl
    (by simp [initEnv, extOf])
  have h2 := body_spec hd hB
  have h := Spec.seq (R := fun _ σ'' => σ''.out = outWord x φ) h1 h2 ?_ ?_
  · obtain ⟨σ', hr, hq⟩ := h _ rfl
    exact ⟨σ', hr, hq⟩
  · rintro σ σ' rfl ⟨ha, hn, -⟩
    exact ⟨ha, hn⟩
  · rintro σ σ' σ'' rfl ⟨-, -, -, hout, -⟩ hq
    rw [hq, hout]
    simp [initEnv]

/-! ### Sizes -/

/-- The value bound. -/
def Bv (x : List ℕ) : ℕ := 2 ^ (bitSize x + 4)

theorem maxEntry_lt_of {M : ℕ} (hM : 0 < M) : ∀ {x : List ℕ}, (∀ v ∈ x, v < M) → maxEntry x < M
  | [], _ => by simp [maxEntry]; omega
  | a :: x, h => by
    have ih := maxEntry_lt_of hM (x := x) fun v hv => h v (by simp [hv])
    have ha := h a (by simp)
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    omega

theorem maxEntry_lt (x : List ℕ) : maxEntry x < 2 ^ bitSize x :=
  maxEntry_lt_of (Nat.two_pow_pos _) fun _ hv => lt_two_pow_bitSize hv

theorem bok_Bv (x : List ℕ) : BOK x (Bv x) := by
  unfold BOK Bv
  have h1 := maxEntry_lt x
  have h2 := length_le_bitSize x
  have h3 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have h4 : 2 ^ (bitSize x + 4) = 16 * 2 ^ bitSize x := by rw [Nat.pow_add]; ring
  have h5 : 1 ≤ 2 ^ bitSize x := Nat.one_le_two_pow
  omega

theorem mem_lt_Bv {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v < Bv x := by
  have h := lt_two_pow_bitSize hv
  have : 2 ^ bitSize x ≤ Bv x := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem len_lt_Bv (x : List ℕ) : x.length < Bv x := by
  have := bok_Bv x; unfold BOK at this; omega

/-- The cost is cubic. -/
theorem Kall_le {x : List ℕ} {φ : Formula} (hd : Dom x φ) :
    Kall x φ ≤ 20000 * (x.length + 1) ^ 3 := by
  have hz := sizes hd
  have hs := hz.s_le; have hr := hz.r_le; have hq := hz.q_le
  unfold Kall Kbody Kread Krest Khead Kp Ke KeB Kemit Kee Kfl Kf Kpre
  set L := x.length with hL
  set s := sOf x
  set r := rOf φ
  set q := nrel φ
  have e1 : s * L ≤ L * L := Nat.mul_le_mul_right _ (by omega)
  have e2 : r * s ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
  have e3 : r * (s * L) ≤ L * (L * L) := Nat.mul_le_mul (by omega) e1
  have e4 : r ≤ L := by omega
  have e5 : (L + 1) ^ 3 = L * (L * L) + 3 * (L * L) + 3 * L + 1 := by ring
  rw [e5]
  nlinarith [e1, e2, e3, e4]

/-- **The incidence reduction runs in polynomial time on its instances.** -/
theorem polyTimeOn_red : PolyTimeOn (pMC Source).Domain red := by
  refine polyTimeOn_of_solves (L := layout) (c := cmd) (B := fun y => Bv y.tail)
    (K := fun y => 20000 * (y.tail.length + 1) ^ 3) (c₀ := 300000) (d := 3) ?_ ?_ ?_ ?_
  · refine ⟨cmd_ok, ?_, ?_⟩
    · rintro y ⟨x, -, rfl⟩ v hv
      simp only [List.tail_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact len_lt_Bv x
      · exact mem_lt_Bv hv'
    · rintro y ⟨x, hx, rfl⟩
      simp only [List.tail_cons]
      obtain ⟨A, φ, he, hd, -⟩ := dom_of_mem hx
      obtain ⟨σ', hr, hq⟩ := cmd_run hd (bok_Bv x)
      exact ⟨extOf x, σ', hr.mono (Kall_le hd), by rw [hq, red_eq he]⟩
  · intro x _
    simp only [List.tail_cons]
    have h1 : 16 ≤ Bv x := by
      unfold Bv
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (Bv x) = 36 + Bv x := by
      simp [Layout.span, layout, ReadTape.readVars, bodyVars]
    rw [hspan]
    have hb : bitSize x + 6 ≤ 300000 * (bitSize x + 1) ^ 3 := by
      have : 1 ≤ (bitSize x + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have hpow : 2 ^ (bitSize x + 6) = 4 * Bv x := by
      unfold Bv; rw [show bitSize x + 6 = (bitSize x + 4) + 2 by omega, Nat.pow_add]; ring
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hb
    rw [hpow] at this
    exact max_le (by omega) (by omega)
  · intro x _
    simp only [List.tail_cons]
    have hl := length_le_bitSize x
    have hsq : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h1 : 1 ≤ (bitSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    simp only [Layout.const]
    omega
  · intro x hx v hv
    obtain ⟨A, φ, he, hd, -⟩ := dom_of_mem hx
    obtain ⟨σ', hr, hq⟩ := cmd_run hd (bok_Bv x)
    rw [red_eq he, ← hq] at hv
    obtain ⟨k, -, hbs⟩ := hr
    have hlt := bigStepB_out hbs (by simp [initEnv]) v hv
    have hBv : Bv x ≤ 2 ^ (300000 * (bitSize x + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 1 ≤ (bitSize x + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        nlinarith)
    omega

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.PolyTime
