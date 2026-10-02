import Lax496464Proofs.Ram.Program
import Lax496464Proofs.Ram.Fits
import Lax496464Proofs.Ram.Reduction
import Lax496464.Corollary4
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Corollary 4: W[2]-Hardness for the Number of Machines

The reduction of Section 8 is an fpt-reduction from Hitting Set, parameterized by the
solution size, to the shop problem parameterized by the number of machines. Its
mathematical content is `Section8.construct_correct`; its passage to words is
`Ram/Reduction.lean`; its word RAM program is `Ram/Program.lean`. What is done here is the
accounting: that every value the program computes stays below a bound the concept's two
admissibility clauses provide, and that its cost is a polynomial in the length of the word.
-/

namespace Lax496464Proofs.Corollary4

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax496464.HittingSet Lax496464.Construction Lax496464.WordEncoding
open Lax496464Proofs.Ram Lax496464Proofs.Ram.Gen Lax496464Proofs.Ram.Program
open Lax496464Proofs.Ram.Fits Lax496464Proofs.Ram.Reduction

/-! ## 1. The cost as a polynomial -/

/-- The cost of the program, as a function of the six numbers it depends on. -/
def costN (n m L Lc R nj : ℕ) : ℕ :=
  (12 * (m + 1) + 6 + (12 * L + 6) + 20) +
  (Build.costBuild n m L +
  (100 + ((2 + (((400 + 4) * Lc + 6 + 4 + 4) * R + 6)) +
    (costDum n m R + costDum n m R) + (10 + (4 * ((1 + 3 + 4 + 4) * nj + 6) + 30)))))

theorem costN_le (s n m L Lc R nj : ℕ) (hs : 1 ≤ s) (hn : n ≤ s) (hm : m ≤ s) (hL : L ≤ s)
    (hLc : Lc ≤ s * s) (hR : R ≤ 3 * (s * s)) (hnj : nj ≤ 9 * (s * s * s * s)) :
    costN n m L Lc R nj ≤ 5000 * (s * s * s * s) := by
  have h1 : costN n m L Lc R nj ≤ costN s s s (s * s) (3 * (s * s)) (9 * (s * s * s * s)) := by
    unfold costN Build.costBuild Build.costI costDum costJBody
    gcongr
  refine h1.trans ?_
  unfold costN Build.costBuild Build.costI costDum costJBody
  have e1 : s ≤ s * s := Nat.le_mul_of_pos_right _ hs
  have e2 : s * s ≤ s * s * s := Nat.le_mul_of_pos_right _ hs
  have e3 : s * s * s ≤ s * s * s * s := Nat.le_mul_of_pos_right _ hs
  nlinarith [e1, e2, e3, hs]

variable {x : List ℕ} {P : Lax496464.HittingSet.Instance} {k : ℕ}

theorem progCost_eq (h : Encodes x P k) :
    progCost P k x = costN P.n P.m (offset x P.m) (memberList P).length (R P k) (numJobs P k) := by
  unfold progCost costN
  rw [h.setCount_eq, h.universeSize_eq]

/-- The cost is at most `5000 (|x| + 1)⁴`. -/
theorem progCost_le (h : Encodes x P k) : progCost P k x ≤ 5000 * ((x.length + 1) ^ 4) := by
  have hk2 := h.size_bounds.1
  have hkn := h.size_bounds.2
  have hlen := h.length_eq
  have hnx := h.universeSize_le
  set s := x.length + 1 with hs
  have hn : P.n ≤ s := by omega
  have hm : P.m ≤ s := by omega
  have hL : offset x P.m ≤ s := by omega
  have hLc : (memberList P).length ≤ s * s :=
    (length_memberList_le h).trans (Nat.mul_le_mul hn hm)
  have hR : R P k ≤ 3 * (s * s) := by
    have h1 : k * (P.n - 1) ≤ P.n * P.n := Nat.mul_le_mul hkn (by omega)
    have h2 : P.n * P.n ≤ s * s := Nat.mul_le_mul hn hn
    have h3 : 1 ≤ s * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
    unfold R; omega
  have hnj : numJobs P k ≤ 9 * (s * s * s * s) := by
    have h1 : selCount P k ≤ 3 * (s * s) * (s * s) := Nat.mul_le_mul hR hLc
    have h2 : dumCount P k ≤ 3 * (s * s) * s * s :=
      Nat.mul_le_mul (Nat.mul_le_mul hR hm) hn
    simp only [numJobs]
    nlinarith [h1, h2]
  rw [progCost_eq h]
  refine (costN_le s _ _ _ _ _ _ (by omega) hn hm hL hLc hR hnj).trans ?_
  have : s * s * s * s = s ^ 4 := by ring
  rw [this]

/-! ## 2. The bound on the values of a run -/

/-- Room for the table the program allocates: the length of the output, its largest entry,
and a constant that covers the degenerate words with no sets. -/
noncomputable def T (x : List ℕ) : ℕ := (red x).length + maxEntry (red x) + 64

theorem red_eq' (h : Encodes x P k) :
    red x = [numJobs P k, k] ++ ((List.range (numJobs P k)).map (jp P k) ++
      ((List.range (numJobs P k)).map (jq P k) ++ ((List.range (numJobs P k)).map (jd P k) ++
        (List.range (numJobs P k)).map (fun _ => 1)))) ++ [target P k] := by
  rw [red_eq h, decisionWord_construct]

theorem length_red (h : Encodes x P k) : (red x).length = 3 + 4 * numJobs P k := by
  rw [red_eq' h]; simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range]; omega

theorem Q_le_R_mul {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (k - 1) * (n + 1) ≤ (k * (n - 1) + 2) * n := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hk' : k' ≤ n' := by omega
  simp only [show k' + 2 - 1 = k' + 1 by omega,
    show n' + 2 - 1 = n' + 1 by omega]
  rcases Nat.eq_zero_or_pos n' with h0 | h0
  · subst h0; have : k' = 0 := by omega
    subst this; norm_num
  · nlinarith [Nat.mul_le_mul_right n' hk', Nat.mul_le_mul_right (n' * n') (Nat.zero_le k')]

theorem bnd_of_encodes (h : Encodes x P k) : Bnd P k (bound x (T x)) := by
  have hk2 := h.size_bounds.1
  have hkn := h.size_bounds.2
  have hlen := h.length_eq
  have hnx := h.universeSize_le
  have hlr := length_red h
  have hnj : numJobs P k < (red x).length := by omega
  have hmax : ∀ v ∈ red x, v < bound x (T x) := by
    intro v hv
    have := le_maxEntry hv
    simp only [bound, T]; omega
  have hxne : x ≠ [] := by
    intro hx; rw [hx, List.length_nil] at hlen; omega
  have hnmax : P.n ≤ maxEntry x := by
    have : universeSize x ∈ x := by
      unfold universeSize
      rw [List.getD_eq_getElem?_getD]
      have : x[0]? = some (x.head hxne) := by
        rcases x with _ | ⟨a, l⟩
        · exact absurd rfl hxne
        · rfl
      rw [this]; exact List.head_mem hxne
    rw [← h.universeSize_eq]; exact le_maxEntry this
  have hB : x.length + maxEntry x + 1 + T x = bound x (T x) := rfl
  have hBge : (red x).length + maxEntry (red x) + 64 + x.length + maxEntry x + 1 ≤ bound x (T x) := by
    simp only [bound, T]; omega
  have hdc : dumCount P k = R P k * P.m * P.n := rfl
  have hsc : selCount P k = R P k * (memberList P).length := rfl
  have hR2 : 2 ≤ R P k := by unfold R; omega
  have hnjd : numJobs P k = selCount P k + 2 * dumCount P k := rfl
  have hcap := length_memberList_le h
  -- everything that is a constant of the construction is small when there are no sets
  have hsmall : P.m = 0 → R P k < bound x (T x) ∧ Q P k < bound x (T x) := by
    intro hm0
    have hL0 : offset x P.m = 0 := by rw [hm0]; exact h.offset_zero
    have hx4 : x.length = 4 := by omega
    have hn4 : P.n ≤ 4 := by omega
    have hk4 : k ≤ 4 := by omega
    constructor
    · have : R P k ≤ 14 := by
        unfold R
        have : k * (P.n - 1) ≤ 4 * 3 := Nat.mul_le_mul hk4 (by omega)
        omega
      omega
    · have : Q P k ≤ 15 := by
        unfold Q
        have : (k - 1) * (P.n + 1) ≤ 3 * 5 := Nat.mul_le_mul (by omega) (by omega)
        omega
      omega
  have hbig : 1 ≤ P.m → R P k < bound x (T x) ∧ Q P k < bound x (T x) := by
    intro hm1
    have hn1 : 1 ≤ P.n := by omega
    have hRd : R P k ≤ dumCount P k := by
      rw [hdc]
      calc R P k = R P k * 1 * 1 := by ring
        _ ≤ R P k * P.m * P.n := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm1) hn1
    have hQd : Q P k ≤ dumCount P k := by
      have h1 := Q_le_R_mul hk2 hkn
      rw [hdc]
      calc Q P k ≤ R P k * P.n := h1
        _ = R P k * 1 * P.n := by ring
        _ ≤ R P k * P.m * P.n := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm1) le_rfl
    constructor <;> omega
  have hmem : ∀ v ∈ red x, v < bound x (T x) := hmax
  have hR_lt : R P k < bound x (T x) := by
    rcases Nat.eq_zero_or_pos P.m with hm0 | hm1
    · exact (hsmall hm0).1
    · exact (hbig hm1).1
  have hQ_lt : Q P k < bound x (T x) := by
    rcases Nat.eq_zero_or_pos P.m with hm0 | hm1
    · exact (hsmall hm0).2
    · exact (hbig hm1).2
  refine
    { one := by omega
      slack := by omega
      nj := by omega
      n_lt := by omega
      m_lt := by omega
      q_lt := hQ_lt
      r_lt := hR_lt
      lc_lt := ?_
      k2_lt := by omega
      tg_lt := ?_
      jobs := ?_ }
  · have h1 : (memberList P).length ≤ selCount P k := by
      rw [hsc]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  · apply hmem
    rw [red_eq' h]; simp
  · intro t ht
    have hp : jp P k t ∈ red x := by
      rw [red_eq' h]
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil]
      exact Or.inl (Or.inr (Or.inl ⟨t, ht, rfl⟩))
    have hq : jq P k t ∈ red x := by
      rw [red_eq' h]
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil]
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩)))
    have hd : jd P k t ∈ red x := by
      rw [red_eq' h]
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil]
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩))))
    exact ⟨hmem _ hp, hmem _ hq, hmem _ hd⟩

/-! ## 3. The program solves the problem -/

/-- The layout of the program: its scalars, its arrays, and room for three nested
temporaries. -/
def Lred : Layout :=
  ⟨["n", "m", "mp1", "L", "i", "v", "k", "j", "bs", "be", "bl", "tt", "f", "s", "Lc", "x1", "x2",
    "R", "Q", "dc", "sc", "nj", "t", "r", "u", "e", "g", "gq", "gg", "GG", "gn", "a", "b", "c"],
   ["OFF", "MEM", "MJ", "MI", "PA", "QA", "DA"], 6⟩

set_option maxHeartbeats 4000000 in
theorem prog_ok : Com.Ok Lred prog := by
  simp [prog, ReadHS.readHS, Build.build, consts, gen, header, dumps, target', Com.Ok, Expr.Ok,
    Cond.Ok, Lred, condExpr, Build.jBody, Build.jSetup, Build.iLoop, Build.iBody, Build.scanLoop,
    Build.scanBody, Build.collect, selPass, selRow, selInner, selElem, selVals, storeTriple,
    epoch, dumPass, dumRBody, dumJ, dumJBody, dumI, dumElem, valsA, valsB, CsrRead.readBlock,
    CsrRead.readBody, Emit.emitLoop, Emit.emitBody]

/-- The cost bound, as a function of the word alone: a polynomial of degree four. -/
def Kx (x : List ℕ) : ℕ := 5000 * ((x.length + 1) ^ 4)

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext (P : Lax496464.HittingSet.Instance) (k : ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "OFF" then P.m + 1 else if a = "MEM" then offset x P.m
  else if a = "MJ" ∨ a = "MI" then P.n * P.m
  else if a = "PA" ∨ a = "QA" ∨ a = "DA" then numJobs P k else 0

theorem prog_solves (D : Set (List ℕ)) (hD : ∀ x ∈ D, x ∈ Lax496464.HittingSet.Instances) :
    Solves Lred prog D red (fun x => bound x (T x)) Kx where
  ok := prog_ok
  inp := fun x _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨P, k, h⟩ := hD x hx
    have hlen := h.length_eq
    refine ⟨ext P k x, ?_⟩
    have hxB : ∀ v ∈ x, v < bound x (T x) := fun v hv => lt_bound hv
    have hLB : offset x (setCount x) + 1 < bound x (T x) := by
      rw [h.setCount_eq]; simp only [bound]; omega
    obtain ⟨σ', hrun, hout⟩ := (prog_spec h hxB (bnd_of_encodes h) hLB).run (σ := initEnv (ext P k x) x)
      ⟨rfl, rfl, by simp [initEnv, ext], by simp [initEnv, ext], by simp [initEnv, ext],
        by simp [initEnv, ext], by simp [initEnv, ext], by simp [initEnv, ext],
        by simp [initEnv, ext]⟩
    refine ⟨σ', ?_, ?_⟩
    · exact hrun.mono (progCost_le h)
    · rw [hout, red_eq h]

/-! ## 4. The corollary -/

theorem fits_mono {c c' w : ℕ} {y : List ℕ}
    (h : Lax496464.ParameterizedComplexity.Fits c w y) (hc : c' ≤ c) :
    Lax496464.ParameterizedComplexity.Fits c' w y :=
  fun v hv => (Nat.mul_le_mul_right _ hc).trans (h v hv)

/-- The constant of the fpt-reduction: large enough to serve as the layout's fitting
constant with room for the table, and as the coefficient and the exponent of the time bound. -/
def cc : ℕ := 64 * Fits.const Lred + 50001

open Lax496464.ParameterizedComplexity in
/-- Words that are Hitting Set words with room for the reduction, and whose image has room. -/
def Dom (w : ℕ) : Set (List ℕ) :=
  {x | x ∈ Lax496464.HittingSet.byK.Domain ∧ Fits cc w x ∧ Fits cc w (red x)}

theorem red_time (w : ℕ) :
    Lax808846.RamComputes.ComputesInTime w (compileProgram Lred prog) (Dom w) red
      (fun x => cc * (fun _ : ℕ => 1) (Lax496464.HittingSet.byK.param x) * (x.length + 1) ^ cc) := by
  have hsolves := prog_solves (Dom w) (fun x hx => hx.1)
  have hcc : 64 * Fits.const Lred ≤ cc := by unfold cc; omega
  refine computesInTime_of_solves_fits (L := Lred) (T := T) (K := Kx) ?_ ?_ ?_ hsolves ?_
  · intro x hx hx0
    obtain ⟨P, k, h⟩ := hx.1
    have := h.length_eq
    rw [hx0, List.length_nil] at this
    omega
  · intro x hx
    exact fits_mono hx.2.1 (by unfold cc; omega)
  · intro x hx
    obtain ⟨P, k, h⟩ := hx.1
    have hne : red x ≠ [] := by
      intro h0; have := length_red h; rw [h0, List.length_nil] at this; omega
    have hf := hx.2.2 (maxEntry (red x)) (maxEntry_mem hne)
    calc Fits.const Lred * T x
        ≤ Fits.const Lred * (64 * ((red x).length + maxEntry (red x) + 1)) := by
          apply Nat.mul_le_mul_left; unfold T; omega
      _ = (64 * Fits.const Lred) * ((red x).length + maxEntry (red x) + 1) := by ring
      _ ≤ cc * ((red x).length + maxEntry (red x) + 1) := Nat.mul_le_mul_right _ hcc
      _ ≤ 2 ^ w := hf
  · intro x hx
    obtain ⟨P, k, h⟩ := hx.1
    have hs : 1 ≤ (x.length + 1) := by omega
    have h4 : (x.length + 1) ^ 4 ≤ (x.length + 1) ^ cc :=
      Nat.pow_le_pow_right hs (by unfold cc; omega)
    have hpos : 1 ≤ (x.length + 1) ^ 4 := Nat.one_le_pow _ _ hs
    show Layout.const Lred * (5000 * ((x.length + 1) ^ 4)) + 1 ≤
      cc * 1 * (x.length + 1) ^ cc
    have hc50 : 50001 ≤ cc := by unfold cc; omega
    calc Layout.const Lred * (5000 * ((x.length + 1) ^ 4)) + 1
        = 10 * (5000 * ((x.length + 1) ^ 4)) + 1 := rfl
      _ ≤ 50001 * (x.length + 1) ^ 4 := by omega
      _ ≤ cc * (x.length + 1) ^ 4 := Nat.mul_le_mul_right _ hc50
      _ ≤ cc * (x.length + 1) ^ cc := Nat.mul_le_mul_left _ h4
      _ = cc * 1 * (x.length + 1) ^ cc := by ring

open Lax496464.ParameterizedComplexity Lax496464.Problems Lax496464.W2Hardness in
/--
---
conclusion: Lax496464.Corollary4.w2Hard_byMachines
---
The construction of Section 8, written as a word RAM program, is an fpt-reduction from
Hitting Set. Its correctness is `Section8.construct_correct` carried to words; its running time
is a polynomial of degree four in the length of the word, and the values it computes stay
below a bound that the concept's two admissibility clauses provide.
-/
theorem w2Hard_byMachines : W2Hard byMachines :=
  ⟨red, compileProgram Lred prog, cc, fun _ => 1, id,
    { maps_domain := fun _x hx => red_mem_domain hx
      correct := fun _x hx => red_correct hx
      param_le := fun _x hx => (red_param_eq hx).le
      time := red_time }⟩

end Lax496464Proofs.Corollary4
