import Lax496464Proofs.Ram.TotalCost
import Lax496464Proofs.Ram.TotalLayout
import Lax391470Proofs.RamBridge2
import Lax391470Proofs.BitSize

/-!
# `totalProg` is polynomial-time on the word RAM

The assembly of `RamPolytime f` for `TotalReduction.f`, following `rjlmax-lax`'s `L2Final`/
`L1Final`: `Shape`, `Solves`, `prog_runs`, the fitting condition, the bit-size polynomial
bounds, and the bridge `RamBridge2.ramPolytime_of_wordlen` (used, rather than `RamBridge`'s
polynomial-value form, because `Bd y` is exponential in the tape length — but only linear in
its bit-length, which is all the word length has to cover).
-/

namespace Lax496464Proofs.Ram.TotalFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize
open Lax496464Proofs.Ram.ScanModel (wordBound wordBound_len_lt wordBound_lt)
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry)
open Lax496464Proofs.Ram.TotalProg (totalProg)
open Lax496464Proofs.Ram.TotalReduction (f)
open Lax496464Proofs.Ram.TotalRun (Bd Mbd hlM_Mbd Bd_gt_two)
open Lax496464Proofs.Ram.TotalCost (Kc totalProg_run)
open Lax496464Proofs.Ram.TotalLayout (Ltotal totalProg_ok)
open Lax496464Proofs.Ram.BitsNat (bitsNat)

/-! ### The output is zeros and ones -/

theorem bitsNat_le_one {n v : ℕ} (hv : v ∈ bitsNat n) : v ≤ 1 := by
  simp only [bitsNat, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨-, rfl⟩ | rfl) | ⟨i, -, rfl⟩
  · exact le_refl _
  · omega
  · unfold Lax496464Proofs.Ram.BitsNat.digit; omega

theorem f_le_one {y : List ℕ} {v : ℕ} (hv : v ∈ f y) : v ≤ 1 := by
  unfold f at hv
  split_ifs at hv
  · obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hv
    exact bitsNat_le_one ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    omega

/-! ### The machine program -/

/-- The physical inputs: a word preceded by its length. -/
def Shape : Set (List ℕ) := {y | y ≠ [] ∧ y.headD 0 = y.tail.length}

lemma shape_eq {y : List ℕ} (h : y ∈ Shape) : y = y.tail.length :: y.tail := by
  obtain ⟨hne, hh⟩ := h
  rcases y with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · simp only [List.headD_cons, List.tail_cons] at hh ⊢
    rw [hh]

lemma len_lt_Bd (y : List ℕ) : y.length < Bd y := by
  unfold Bd; exact wordBound_len_lt _ _

theorem solves : Solves Ltotal totalProg Shape (fun x => f x.tail) (fun x => Bd x.tail)
    (fun x => Kc (2 * x.tail.length + 4) (Bd x.tail).size) where
  ok := totalProg_ok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact len_lt_Bd x.tail
    · exact wordBound_lt (hlM_Mbd x.tail) rfl v hv'
  run := by
    intro x hx
    obtain ⟨ext, σ', hrun, hout⟩ := totalProg_run x.tail
    rw [← shape_eq hx] at hrun
    exact ⟨ext, σ', hrun, hout⟩

def prog : Program := compileProgram Ltotal totalProg

/-! ### The word bound is linear in the bit size, in bits -/

lemma maxEntry_mem_or_zero (y : List ℕ) : maxEntry y ∈ y ∨ maxEntry y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    rcases Nat.le_total a (List.foldr max 0 t) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · right; exact h'
    · rw [Nat.max_eq_left h]; exact Or.inl List.mem_cons_self

lemma maxEntry_lt (y : List ℕ) : maxEntry y < 2 ^ (bitSize y + 1) := by
  rcases maxEntry_mem_or_zero y with hm | hm
  · exact mem_lt_two_pow_bitSize_add_one hm
  · rw [hm]; exact Nat.two_pow_pos _

lemma wordBound_lt_gen (b L M : ℕ) (hL : L ≤ b) (hM : M ≤ 2 ^ (66 * b + 199)) :
    wordBound M L < 2 ^ (69 * b + 200) := by
  have hbP : b < 2 ^ b := Nat.lt_two_pow_self
  have hX : M * 2 ^ L ≤ 2 ^ (67 * b + 199) := by
    have h4 : (2 : ℕ) ^ L ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hL
    calc M * 2 ^ L ≤ 2 ^ (66 * b + 199) * 2 ^ b := Nat.mul_le_mul hM h4
      _ = 2 ^ (67 * b + 199) := by rw [← pow_add]; ring_nf
  have hcoef : L * L + L + 1 ≤ 2 ^ (2 * b) := by
    have : (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [← pow_add]; ring_nf
    rw [this]
    have h1 : L + 1 ≤ 2 ^ b := by omega
    nlinarith
  have hBd : wordBound M L = (L * L + L + 1) * (M * 2 ^ L) + L + 10 := by
    unfold wordBound; ring
  have hprod : (L * L + L + 1) * (M * 2 ^ L) ≤ 2 ^ (2 * b) * 2 ^ (67 * b + 199) :=
    Nat.mul_le_mul hcoef hX
  have h5 : (2 : ℕ) ^ (2 * b) * 2 ^ (67 * b + 199) = 2 ^ (69 * b + 199) := by
    rw [← pow_add]; ring_nf
  have h6 : (2 : ℕ) ^ (69 * b + 200) = 2 * 2 ^ (69 * b + 199) := by rw [pow_succ]; ring
  have h7 : b + 10 < 2 ^ (69 * b + 199) := by
    have : b + 10 < 2 ^ (b + 4) := by
      have : (2 : ℕ) ^ (b + 4) = 16 * 2 ^ b := by ring
      omega
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [h5] at hprod
  rw [h6]
  generalize (2 : ℕ) ^ (69 * b + 199) = T at hprod h7 ⊢
  omega

lemma Mbd_le (y : List ℕ) : Mbd y ≤ 2 ^ (66 * bitSize y + 199) := by
  have hL : y.length ≤ bitSize y := length_le_bitSize y
  have hMe := maxEntry_lt y
  have h1 : (2 : ℕ) ^ (bitSize y + 1) ≤ 2 ^ (66 * bitSize y + 198) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (66 * (y.length + 3)) ≤ 2 ^ (66 * bitSize y + 198) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ (66 * bitSize y + 199) = 2 * 2 ^ (66 * bitSize y + 198) := by
    rw [pow_succ]; ring
  unfold Mbd; omega

/-- **`Bd y` has at most `69·bitSize y + 200` bits.** -/
lemma Bd_lt (y : List ℕ) : Bd y < 2 ^ (69 * bitSize y + 200) :=
  wordBound_lt_gen (bitSize y) y.length (Mbd y) (length_le_bitSize y) (Mbd_le y)

/-- The bit-length of `Bd y`. -/
lemma Bd_size_le (y : List ℕ) : (Bd y).size ≤ 69 * bitSize y + 200 :=
  Nat.size_le.mpr (Bd_lt y)

/-! ### Fitting into a word -/

lemma fit_of (w : ℕ) (y : List ℕ) (hw : 70 * bitSize y + 240 + 1 ≤ w) :
    max (Bd y) (Ltotal.span (Bd y)) ≤ 2 ^ w := by
  have hlt := Bd_lt y
  have hpow : (2 : ℕ) ^ (70 * bitSize y + 240) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : (2 : ℕ) ^ (69 * bitSize y + 200) ≤ 2 ^ (70 * bitSize y + 236) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (70 * bitSize y + 240) = 16 * 2 ^ (70 * bitSize y + 236) := by
    rw [show 70 * bitSize y + 240 = (70 * bitSize y + 236) + 4 by ring, pow_add]; norm_num; ring_nf
  have hspan : Ltotal.span (Bd y) ≤ 100 + 10 * Bd y := by
    simp [Layout.span, Ltotal, Lax496464Proofs.Ram.TotalLayout.scalars,
      Lax496464Proofs.Ram.TotalLayout.arrays]
  have hpos : 100 ≤ 2 ^ (70 * bitSize y + 236) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 7 ≤ 70 * bitSize y + 236 by omega))
  rw [max_le_iff]
  constructor <;> omega

/-! ### Running on the RAM -/

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 70 * bitSize x + 240 + 1 ≤ w) :
    ∃ t ≤ 10 * Kc (2 * x.length + 4) (Bd x).size + 1, RunsTo w prog (x.length :: x) (f x) t := by
  have hs : Solves Ltotal totalProg {z | z = x.length :: x} (fun z => f z.tail)
      (fun z => Bd z.tail) (fun z => Kc (2 * z.tail.length + 4) (Bd z.tail).size) :=
    ⟨solves.ok, fun z hz => solves.inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => solves.run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * Kc (2 * z.tail.length + 4) (Bd z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      exact fitsWords_of_max_le (by have := Bd_gt_two x; omega) (fit_of w x hfit))
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### The running time is polynomial in the bit size -/

lemma Kc_le_gen (Z s S : ℕ) (hs : s ≤ 4 * Z) (hS : S + 1 ≤ 241 * Z) (hZ1 : 1 ≤ Z) :
    10 * Kc s S + 1 ≤ 13000000000 * Z ^ 5 := by
  have hs4 : s * s * s * s ≤ (4 * Z) * (4 * Z) * (4 * Z) * (4 * Z) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hs hs) hs) hs
  have hprod : 20000 * (s * s * s * s) * (S + 1) ≤
      20000 * ((4 * Z) * (4 * Z) * (4 * Z) * (4 * Z)) * (241 * Z) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hs4) hS
  have e1 : 20000 * ((4 * Z) * (4 * Z) * (4 * Z) * (4 * Z)) * (241 * Z) = 1233920000 * Z ^ 5 := by
    ring
  have hZ5 : Z ≤ Z ^ 5 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hKc : Kc s S = 20000 * (s * s * s * s) * (S + 1) + 3000 * s := rfl
  have hp2 := hprod.trans e1.le
  clear hprod e1 hs4
  generalize 20000 * (s * s * s * s) * (S + 1) = A at hp2 hKc
  omega

lemma Kc_le (x : List ℕ) :
    10 * Kc (2 * x.length + 4) (Bd x).size + 1 ≤ 13000000000 * (bitSize x + 1) ^ 5 :=
  Kc_le_gen (bitSize x + 1) (2 * x.length + 4) (Bd x).size
    (by have := length_le_bitSize x; omega) (by have := Bd_size_le x; omega) (by omega)

/-- **The reduction, on zeros and ones, is polynomial-time on a word RAM.** -/
theorem ramPolytime_f : RamPolytime f := by
  refine Lax391470Proofs.RamBridge2.ramPolytime_of_wordlen (d := 70) (K := 240) (prog := prog)
    (Polynomial.C 13000000000 * (Polynomial.X + Polynomial.C 1) ^ 5) (by omega) ?_ ?_
  · intro x v hv
    have h1 := f_le_one hv
    have h2 : 2 ≤ 2 ^ (70 * bitSize x + 240) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 70 * bitSize x + 240 by omega))
    omega
  · intro w x hw
    obtain ⟨t, ht, hrun⟩ := prog_runs w x hw
    refine ⟨t, ?_, hrun⟩
    have := Kc_le x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

end Lax496464Proofs.Ram.TotalFinal
