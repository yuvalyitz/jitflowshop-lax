import Lax496464Proofs.WHierarchy.HittingSet.Common
import Lax496464.WH_E1_HittingSetInW2

/-! # The parameter of Hitting Set is computable in polynomial time

The program reads the word with `Parse.readHS` and writes the solution size it found. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Param

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Parse Lax496464Proofs.WHierarchy.HittingSet.Common
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V)
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-- Read the word, write `k`. -/
def cmd : Com := .seq readHS (.write (V "hs_k"))

/-- The arrays of the reader. -/
def parseArrs : List String := ["hs_off", "hs_mem", "hs_own"]

/-- The layout. -/
def layout : Layout := ⟨parseVars, parseArrs, 8⟩

set_option maxHeartbeats 1000000 in
theorem readHS_ok (L : Layout) (hs : ∀ y ∈ parseVars, y ∈ L.scalars)
    (ha : ∀ a ∈ parseArrs, a ∈ L.arrays) (ht : 4 ≤ L.temps) : Com.Ok L readHS := by
  have h1 := hs "hs_len" (by simp [parseVars])
  have h2 := hs "hs_n" (by simp [parseVars])
  have h3 := hs "hs_m" (by simp [parseVars])
  have h4 := hs "hs_k" (by simp [parseVars])
  have h5 := hs "hs_t" (by simp [parseVars])
  have h6 := hs "hs_j" (by simp [parseVars])
  have h7 := hs "hs_sz" (by simp [parseVars])
  have h8 := hs "hs_q" (by simp [parseVars])
  have h9 := hs "rn_c" (by simp [parseVars])
  have h10 := hs "rn_b" (by simp [parseVars])
  have h11 := hs "rn_i" (by simp [parseVars])
  have h12 := hs "rn_v" (by simp [parseVars])
  have a1 := ha "hs_off" (by simp [parseArrs])
  have a2 := ha "hs_mem" (by simp [parseArrs])
  have a3 := ha "hs_own" (by simp [parseArrs])
  simp [readHS, hdrNum, setLoop, setBody, setTail, memLoop, memBody, memTail,
    ReadNat.readNat, ReadNat.onesLoop, ReadNat.digitsLoop, ReadNat.digitsBody, Com.Ok, Expr.Ok,
    Cond.Ok, condExpr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, a1, a2, a3]
  omega

theorem cmd_ok : Com.Ok layout cmd := by
  refine ⟨readHS_ok layout (fun y hy => hy) (fun a ha => ha) (by simp [layout]), ?_⟩
  simp [Com.Ok, layout, Expr.Ok, parseVars]

/-- The value bound, on the tape `y = x.length :: x`. -/
def Bp (y : List ℕ) : ℕ := 2 ^ (y.length + 5)

/-- The cost bound. -/
def Kp (y : List ℕ) : ℕ := 200 * (y.length + 1) ^ 3 + 2

/-- The array lengths the reader is started with. -/
def extOf (P : Instance) (a : String) : ℕ :=
  if a = "hs_off" then P.m + 1 else if a = "hs_mem" then total P else
    if a = "hs_own" then total P else 0

theorem fresh_init (P : Instance) (y : List ℕ) : Fresh P (initEnv (extOf P) y) := by
  refine ⟨by simp [initEnv, extOf], ?_, by simp [initEnv, extOf], by simp [initEnv, extOf]⟩
  simp [initEnv, extOf, List.getD_eq_getElem?_getD]

theorem inp_lt (P : Instance) (k : ℕ) {v : ℕ} (hv : v ∈ (word P k).length :: word P k) :
    v < 2 ^ ((word P k).length + 1) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
  · have := word_le_one hv
    have : 2 ≤ 2 ^ ((word P k).length + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem solves : Solves layout cmd (Tapes HittingSet.Domain)
    (fun y => (fun x => [HittingSet.param x]) y.tail) Bp Kp := by
  refine ⟨cmd_ok, ?_, ?_⟩
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩ v hv
    have := inp_lt P k hv
    have h2 : 2 ^ ((word P k).length + 1) ≤ Bp ((word P k).length :: word P k) := by
      unfold Bp; exact Nat.pow_le_pow_right (by norm_num) (by simp)
    omega
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩
    have hK := Kread_le P k
    obtain ⟨-, -, -, hkL, -⟩ := dims P k
    generalize hL : (word P k).length = L at hK hkL
    have hBp : Bp (L :: word P k) = 2 ^ (L + 6) := by simp [Bp, hL]
    have hfits : Fits P k (Bp (L :: word P k)) :=
      fits_of_le P k (by rw [hBp, hL]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨extOf P, ?_⟩
    obtain ⟨σ1, r1, ⟨⟨_, _, hk1⟩, _⟩, hout1, -, -⟩ :=
      (readHS_spec (B := Bp (L :: word P k)) P k L hfits).run
        (σ := initEnv (extOf P) (L :: word P k)) ⟨rfl, fresh_init P _⟩
    have hkB : k < Bp (L :: word P k) := by
      rw [hBp]; exact lt_trans hkL (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have r2 := Run.write (B := Bp (L :: word P k)) (σ := σ1) (e := V "hs_k") (v := k)
      (by rw [← hk1]; exact evalB_var (by rw [hk1]; exact hkB))
    refine ⟨_, (r1.seq r2).mono ?_, ?_⟩
    · simp only [Kp, List.length_cons, size_var, hL]
      have : (L + 1) ^ 3 ≤ (L + 1 + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    · simp only [List.tail_cons, param_word]
      rw [hout1]; rfl

/-- The constant of the polynomial bound. -/
def c₀ : ℕ := 20000

theorem pow_le_bound (s a : ℕ) (h : a ≤ 9 * (s + 1)) : 2 ^ a ≤ 2 ^ (c₀ * (s + 1) ^ 3) := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have : s + 1 ≤ (s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold c₀; omega

/-- **The parameter of `p-Hitting-Set` is computable in polynomial time.** -/
theorem isParameterized : IsParameterized HittingSet := by
  refine polyTimeOn_of_solves (c₀ := c₀) (d := 3) solves ?_ ?_ ?_
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    generalize bitSize (word P k) = s at hlen ⊢
    have hB : Bp ((word P k).length :: word P k) = 2 ^ ((word P k).length + 6) := by simp [Bp]
    rw [hB]
    generalize (word P k).length = L at hlen ⊢
    have h32 : 32 ≤ 2 ^ (L + 6) := by
      calc 32 = 2 ^ 5 := rfl
        _ ≤ 2 ^ (L + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (2 ^ (L + 6)) ≤ 2 ^ (L + 8) := by
      simp only [Layout.span, layout, parseVars, parseArrs, List.length_cons, List.length_nil]
      have : 2 ^ (L + 8) = 4 * 2 ^ (L + 6) := by ring
      omega
    have hle : 2 ^ (L + 8) ≤ 2 ^ (c₀ * (s + 1) ^ 3) := pow_le_bound s _ (by omega)
    have h68 : 2 ^ (L + 6) ≤ 2 ^ (L + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (h68.trans hle) (hspan.trans hle)
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    simp only [Kp, List.length_cons, Layout.const]
    generalize bitSize (word P k) = s at hlen ⊢
    generalize (word P k).length = L at hlen ⊢
    have h1 : (L + 1 + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * (s + 1)) ^ 3 = 8 * (s + 1) ^ 3 := by ring
    have h3 : 1 ≤ (s + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold c₀
    omega
  · rintro x ⟨P, k, rfl⟩ v hv
    simp only [List.mem_singleton] at hv
    subst hv
    rw [param_word]
    have hlen := length_le_bitSize (word P k)
    obtain ⟨-, -, -, hk, -⟩ := dims P k
    exact lt_of_lt_of_le hk (pow_le_bound _ _ (by omega))

/--
---
conclusion: Lax496464.WH_E1_HittingSetInW2.hittingSet_isParameterized
---
The parameter of a Hitting Set word is computed in polynomial time by the IMP+ program that reads
the word — the codes of `n`, `m` and `k`, then the sets — and writes `k`: at most
`20000 (|x| + 1)^3` steps, with values below `2 ^ (|x| + 7)`.
-/
theorem hittingSet_isParameterized :
    IsParameterized Lax496464.WH_C2_HittingSet.HittingSet :=
  isParameterized

example : type_of% @Lax496464.WH_E1_HittingSetInW2.hittingSet_isParameterized :=
  hittingSet_isParameterized

end Lax496464Proofs.WHierarchy.HittingSet.Param
