import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.ListUtil
import Lax496464Proofs.Ram.W3Tab

/-!
# The Sweep Table's Updates, as IMP+ Loops

The width sweep's table is a flat array `TB` with the entry of mask `X` and weight `c` at index
`X * W1 + c` (`W1 = W + 1`, scalar `"W1"`); the popcounts live in an array `PC` with
`PC[X] = pcnt X` for `X < MK` (`MK`, scalar `"MK"`, the number of masks in use, a multiple of
`2 * 2^b`).  Two events change the table, each by one flat pass over the `MK * W1` cells:

* `dueLoop` (`dueLoop_table`) — the table after a due date, `dueT`.  In place, cells ascending;
  the cell `(X, c)` with bit `b` clear reads the cell `(X + 2^b, c)` *ahead* of it (still old);
  cells with bit `b` set are overwritten by `INF`.
* `startLoop` (`startLoop_table`) — the table after a start, `startT`.  In place; the cell
  `(X, c)` with bit `b` set reads the cell `(X - 2^b, c - w)` *behind* it, whose row has bit `b`
  clear and so was left unchanged by the pass (`startStep_clear`).

`growPC` (`growPC_table`) doubles the valid range of `PC`: `PC[X + MK] := PC[X] + 1`.

**What a caller may rely on when the number of masks doubles.**  The new region of `TB`
(`MK_old * W1 ≤ index < 2 * MK_old * W1`) needs *no initialisation* before the `startLoop` of the
job that takes the new slot `b` (`2^b = MK_old`): every cell of the new region lies in a row with
bit `b` set, `startT` sets *every* such cell (to `INF` or to a computed value) and `startLoop`
reads only rows with bit `b` clear — the hypothesis `hle` of `startLoop_table` is stated for
those rows only (`j / W1 / 2^b % 2 = 0`), so the garbage in the new region is never looked at.
(Before the start, the new region is not the true table; the `Rel` invariant of `W3Tab` speaks
about masks that occur, and after the start pass every entry of the new region is defined.)

Costs are explicit and linear in `MK * W1`: `dueLoop` `44 * (MK * W1) + 14`, `startLoop`
`84 * (MK * W1) + 14`, `growPC` `24 * MK + 6`.  Values stay below the word bound `B` given the
listed hypotheses (`MK * W1 < B`, `INF < B`, `INF + p + q < B`, `d + 1 < B`, `w < B`, `m < B`,
`2 * MK < B`).  Frame facts (scalars/arrays not written) are part of every `_table` statement.
-/

namespace Lax496464Proofs.Ram.W3Loops

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3Bits

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

theorem land_one (x : ℕ) : Nat.land x 1 = x % 2 := by simp

/-- The `TB` entry of index `j`, read as the entry of `(X, c)` with `j = X * W1 + c`. -/
def tabOf (W1 : ℕ) (TB : List ℕ) (X c : ℕ) : ℕ := TB.getD (X * W1 + c) 0

/-! ## The due pass -/

/-- One cell of the due pass. -/
def dueBody : Com :=
  .seq (.assign "X" (.bin .div (V "i") (V "W1")))
    (.seq (.ite (.eq (.bin .and (.bin .div (V "X") (V "b2")) (.lit 1)) (.lit 1))
        (.store "TB" (V "i") (V "cinf"))
        (.ite (.lt (.get "TB" (.bin .add (V "i") (V "sh"))) (.get "TB" (V "i")))
          (.store "TB" (V "i") (.get "TB" (.bin .add (V "i") (V "sh"))))
          .skip))
      (.assign "i" (.bin .add (V "i") (.lit 1))))

/-- The value the due pass leaves in cell `i` when the table is `TB`. -/
def dueStep (INF b2 W1 sh : ℕ) (TB : List ℕ) (i : ℕ) : ℕ :=
  if i / W1 / b2 % 2 = 1 then INF else min (TB.getD i 0) (TB.getD (i + sh) 0)

/-- If bit `b` of `X` is clear, then `X + 2^b` is still a valid mask. -/
theorem lt_of_bit_clear {X b2 MK : ℕ} (hb2 : 0 < b2) (hd : 2 * b2 ∣ MK) (hX : X < MK)
    (hbit : ¬ X / b2 % 2 = 1) : X + b2 < MK := by
  obtain ⟨r, hr⟩ := hd
  have h1 : X / b2 < 2 * r := by
    rw [Nat.div_lt_iff_lt_mul hb2]
    have : 2 * r * b2 = 2 * b2 * r := by ring
    rw [this, ← hr]; exact hX
  have h2 : (X + b2) / b2 = X / b2 + 1 := by
    rw [Nat.add_div_right _ hb2]
  have h3 : (X + b2) / b2 < 2 * r := by
    rw [h2]; omega
  rw [Nat.div_lt_iff_lt_mul hb2] at h3
  have : 2 * r * b2 = MK := by rw [hr]; ring
  omega

/-- Reading `b2` rows ahead stays inside the table. -/
theorem read_lt {i W1 b2 MK : ℕ} (hW1 : 0 < W1) (h2 : i / W1 + b2 < MK) :
    i + b2 * W1 < MK * W1 := by
  have h := Nat.div_add_mod i W1
  have hc := Nat.mod_lt i hW1
  have h3 : W1 * (i / W1 + b2 + 1) ≤ W1 * MK := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add, Nat.mul_add] at h3
  rw [Nat.mul_comm b2 W1, Nat.mul_comm MK W1]
  omega

theorem set_getD_self' (TB : List ℕ) (i : ℕ) (h : i < TB.length) :
    TB.set i (TB[i]?.getD 0) = TB := by
  simp [List.getElem?_eq_getElem h]

theorem dueBody_spec {B : ℕ} (b2 W1 MK INF sh N i : ℕ) (TB : List ℕ)
    (hb2 : 0 < b2) (hW1 : 0 < W1) (hd : 2 * b2 ∣ MK) (hsh : sh = b2 * W1) (hN : N = MK * W1)
    (hi : i < N) (hNL : N ≤ TB.length) (hNB : N < B) (hINF : INF < B)
    (hle : ∀ j, TB.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧
        σ.vars "sh" = sh ∧ σ.vars "i" = i ∧ σ.arrs "TB" = TB)
      dueBody
      (fun σ σ' => σ'.arrs "TB" = TB.set i (dueStep INF b2 W1 sh TB i) ∧ σ'.vars "i" = i + 1 ∧
        (∀ y, y ≠ "X" → y ≠ "i" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      40 := by
  have hX : i / W1 < B := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hXb : i / W1 / b2 < B := lt_of_le_of_lt (Nat.div_le_self _ _) hX
  have hland : Nat.land (i / W1 / b2) 1 < B := by
    rw [land_one]; have := Nat.mod_lt (i / W1 / b2) (by norm_num : 0 < 2)
    have : 2 ≤ B := by omega
    omega
  have hMKpos : 0 < MK := Nat.pos_of_ne_zero (by rintro rfl; simp at hN; omega)
  have hb2MK : b2 ≤ MK := le_trans (by omega) (Nat.le_of_dvd hMKpos hd)
  have hMKN : MK ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ hW1
  have hW1N : W1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hMKpos
  have hshi : ¬ (i / W1 / b2 % 2 = 1) → i + sh < N := by
    intro hbit
    have h1 : i / W1 < MK := (Nat.div_lt_iff_lt_mul hW1).mpr (by rw [hN] at hi; exact hi)
    have h2 := lt_of_bit_clear hb2 hd h1 hbit
    rw [hsh, hN]; exact read_lt hW1 h2
  have hshB : b2 * W1 < B := by
    have : b2 * W1 ≤ MK * W1 := Nat.mul_le_mul_right _ hb2MK
    omega
  have hTBB : ∀ j, TB.getD j 0 < B := fun j => lt_of_le_of_lt (hle j) hINF
  have hTBB' : ∀ j (h : j < TB.length), TB[j] < B := fun j h => by
    have := hTBB j
    rwa [List.getD_eq_getElem _ _ h] at this
  by_cases hbit : i / W1 / b2 % 2 = 1
  · run_vcg
    all_goals (have hW1B : W1 < B := by omega)
    all_goals (have hb2B : b2 < B := by omega)
    all_goals simp_all [dueStep]
    all_goals omega
  · have hsN := hshi hbit
    rw [hsh] at hsN
    have hsNB : i + b2 * W1 < B := by omega
    have hsNL : i + b2 * W1 < TB.length := by omega
    run_vcg
    all_goals (have hW1B : W1 < B := by omega)
    all_goals (have hb2B : b2 < B := by omega)
    all_goals simp_all [dueStep, min_eq_right_of_lt]
    all_goals first
      | omega
      | (rw [eq_comm]; exact set_getD_self' _ _ (by omega))

/-- The whole due pass: set the two constants, then sweep every cell in ascending order. -/
def dueLoop : Com :=
  .seq (.assign "N" (.bin .mul (V "MK") (V "W1")))
    (.seq (.assign "sh" (.bin .mul (V "b2") (V "W1")))
      (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) dueBody)))

/-- The due pass's invariant: the cells below `i` are new, the others old. -/
def DueInv (b2 W1 N INF : ℕ) (TB0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.vars "sh" = b2 * W1 ∧
  σ.vars "N" = N ∧ σ.vars "i" ≤ N ∧ (σ.arrs "TB").length = TB0.length ∧
  ∀ j, (σ.arrs "TB").getD j 0 =
    if j < σ.vars "i" then dueStep INF b2 W1 (b2 * W1) TB0 j else TB0.getD j 0

theorem dueStep_le {INF b2 W1 sh : ℕ} {TB : List ℕ} (hle : ∀ j, TB.getD j 0 ≤ INF) (i : ℕ) :
    dueStep INF b2 W1 sh TB i ≤ INF := by
  unfold dueStep
  split_ifs
  · exact le_rfl
  · exact le_trans (min_le_left _ _) (hle _)

theorem dueLoop_spec {B : ℕ} (b2 W1 MK INF : ℕ) (TB0 : List ℕ)
    (hb2 : 0 < b2) (hW1 : 0 < W1) (hMK : 0 < MK) (hd : 2 * b2 ∣ MK)
    (hNL : MK * W1 ≤ TB0.length)
    (hNB : MK * W1 < B) (hINF : INF < B) (hle : ∀ j, TB0.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "MK" = MK ∧
        σ.vars "cinf" = INF ∧ σ.arrs "TB" = TB0)
      dueLoop
      (fun _ σ' => (σ'.arrs "TB").length = TB0.length ∧
        ∀ j, (σ'.arrs "TB").getD j 0 =
          if j < MK * W1 then dueStep INF b2 W1 (b2 * W1) TB0 j else TB0.getD j 0)
      (44 * (MK * W1) + 14) := by
  have hbody : Spec B (fun σ => DueInv b2 W1 (MK * W1) INF TB0 σ ∧ σ.vars "i" < MK * W1)
      dueBody (fun σ σ' => DueInv b2 W1 (MK * W1) INF TB0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
    intro σ ⟨hI, hlt⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
    have hle' : ∀ j, (σ.arrs "TB").getD j 0 ≤ INF := by
      intro j
      rw [h8 j]
      split_ifs
      · exact dueStep_le hle j
      · exact hle j
    obtain ⟨σ', hrun, hTB, hi', hfv, hfa, hinp, hout⟩ := dueBody_spec (B := B) b2 W1 MK INF
      (b2 * W1) (MK * W1) (σ.vars "i") (σ.arrs "TB") hb2 hW1 hd rfl rfl hlt
      (by rw [h7]; exact hNL) hNB hINF hle' σ ⟨h1, h2, h3, h4, rfl, rfl⟩
    have hi0 : σ.vars "i" < (σ.arrs "TB").length := by rw [h7]; omega
    refine ⟨σ', hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hi'⟩
    · rw [hfv "b2" (by decide) (by decide)]; exact h1
    · rw [hfv "W1" (by decide) (by decide)]; exact h2
    · rw [hfv "cinf" (by decide) (by decide)]; exact h3
    · rw [hfv "sh" (by decide) (by decide)]; exact h4
    · rw [hfv "N" (by decide) (by decide)]; exact h5
    · rw [hi']; omega
    · rw [hTB, List.length_set]; exact h7
    · intro j
      rw [hTB, hi']
      by_cases hj : j = σ.vars "i"
      · subst hj
        rw [getD_set_self _ _ _ hi0, if_pos (by omega)]
        have e1 := h8 (σ.vars "i")
        have e2 := h8 (σ.vars "i" + b2 * W1)
        rw [if_neg (by omega)] at e1 e2
        unfold dueStep
        rw [e1, e2]
      · rw [getD_set_ne _ _ _ _ hj, h8 j]
        by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
  have hloop := Spec.forRangeZero (B := B) "i" "N" (DueInv b2 W1 (MK * W1) INF TB0) (MK * W1) 40
    hNB (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.1) hbody
  have hMKB : MK < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hW1) hNB
  have hW1B : W1 < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hMK) hNB
  have hb2B : b2 < B := lt_of_le_of_lt (le_trans (by omega) (Nat.le_of_dvd hMK hd)) hMKB
  have hshB : b2 * W1 < B := lt_of_le_of_lt (Nat.mul_le_mul_right _
    (le_trans (by omega) (Nat.le_of_dvd hMK hd))) hNB
  run_vcg [hloop]
  all_goals first
    | (obtain ⟨⟨_, _, _, _, _, _, hl, hg⟩, hi⟩ :=
        ‹DueInv b2 W1 (MK * W1) INF TB0 _ ∧ _ = MK * W1›
       exact ⟨hl, fun j => by rw [hg j, hi]⟩)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Env.setVar])
    | (simp_all)

/-- The pass's per-cell value is the paper's `dueT`, entry by entry. -/
theorem dueStep_eq {b b2 W1 INF : ℕ} (hb2 : b2 = 2 ^ b) (hW1 : 0 < W1) (TB0 : List ℕ)
    {X c : ℕ} (hc : c < W1) :
    dueStep INF b2 W1 (b2 * W1) TB0 (X * W1 + c) = dueT b INF (tabOf W1 TB0) X c := by
  have hdiv : (X * W1 + c) / W1 = X := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW1, Nat.div_eq_of_lt hc, zero_add]
  unfold dueStep dueT tabOf
  rw [hdiv, ← hb2]
  have : (X + b2) * W1 + c = X * W1 + c + b2 * W1 := by ring
  rw [this]

/-- **The due pass, in the table's own terms.** -/
theorem dueLoop_table {B : ℕ} (b b2 W1 MK INF : ℕ) (TB0 : List ℕ)
    (hb2 : b2 = 2 ^ b) (hW1 : 0 < W1) (hMK : 0 < MK) (hd : 2 * b2 ∣ MK)
    (hNL : MK * W1 ≤ TB0.length) (hNB : MK * W1 < B) (hINF : INF < B)
    (hle : ∀ j, TB0.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "MK" = MK ∧
        σ.vars "cinf" = INF ∧ σ.arrs "TB" = TB0)
      dueLoop
      (fun σ σ' => (σ'.arrs "TB").length = TB0.length ∧
        (∀ X < MK, ∀ c < W1,
          tabOf W1 (σ'.arrs "TB") X c = dueT b INF (tabOf W1 TB0) X c) ∧
        (∀ j, MK * W1 ≤ j → (σ'.arrs "TB").getD j 0 = TB0.getD j 0) ∧
        (∀ j, (σ'.arrs "TB").getD j 0 ≤ INF) ∧
        (∀ y, y ≠ "N" → y ≠ "sh" → y ≠ "i" → y ≠ "X" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (44 * (MK * W1) + 14) := by
  have hb2pos : 0 < b2 := by rw [hb2]; positivity
  refine ((dueLoop_spec b2 W1 MK INF TB0 hb2pos hW1 hMK hd hNL hNB hINF hle).frame).post ?_
  rintro σ σ' - ⟨⟨hlen, hget⟩, hfv, hfa, hinp, hout⟩
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX c hc
    have hj : X * W1 + c < MK * W1 := by
      have : (X + 1) * W1 ≤ MK * W1 := Nat.mul_le_mul_right _ hX
      nlinarith
    change (σ'.arrs "TB").getD (X * W1 + c) 0 = dueT b INF (tabOf W1 TB0) X c
    rw [hget, if_pos hj, dueStep_eq hb2 hW1 TB0 hc]
  · intro j hj
    rw [hget, if_neg (by omega)]
  · intro j
    rw [hget]
    split_ifs
    · exact dueStep_le hle j
    · exact hle j
  · intro y h1 h2 h3 h4
    exact hfv y (by simp [dueLoop, dueBody, Com.wvars]; tauto)
  · intro a ha
    exact hfa a (by simp [dueLoop, dueBody, Com.warrs]; exact ha)
  · exact hinp (by simp [dueLoop, dueBody, Com.reads])
  · exact hout (by simp [dueLoop, dueBody, Com.NoWrite])

/-! ## The start pass -/

/-- The cell of the entry a start pass reads for cell `i`: the same weight column shifted down by
`w` (truncated at zero), in the row with bit `b` cleared. -/
def srcIdx (b2 W1 w i : ℕ) : ℕ := (i / W1 - b2) * W1 + (i - i / W1 * W1 - w)

/-- The part of a start cell that runs when bit `b` of the row is set: read the source entry,
test the guard, write the cell. -/
def startSet : Com :=
  .seq (.assign "c" (.bin .sub (V "i") (.bin .mul (V "X") (V "W1"))))
    (.seq (.assign "ri" (.bin .add (.bin .mul (.bin .sub (V "X") (V "b2")) (V "W1"))
        (.bin .sub (V "c") (V "sw"))))
      (.seq (.assign "tv" (.get "TB" (V "ri")))
        (.ite (.lt (.get "PC" (.bin .sub (V "X") (V "b2"))) (V "m"))
          (.ite (.lt (.bin .add (.bin .add (V "tv") (V "sp")) (V "sq"))
              (.bin .add (V "sd") (.lit 1)))
            (.store "TB" (V "i") (.bin .add (V "tv") (V "sp")))
            (.store "TB" (V "i") (V "cinf")))
          (.store "TB" (V "i") (V "cinf")))))

/-- One cell of the start pass. -/
def startBody : Com :=
  .seq (.assign "X" (.bin .div (V "i") (V "W1")))
    (.seq (.ite (.eq (.bin .and (.bin .div (V "X") (V "b2")) (.lit 1)) (.lit 1)) startSet .skip)
      (.assign "i" (.bin .add (V "i") (.lit 1))))

/-- The value the start pass leaves in cell `i` when the table is `TB` and the popcounts `PC`. -/
def startStep (b2 W1 w p q d m INF : ℕ) (TB PC : List ℕ) (i : ℕ) : ℕ :=
  if i / W1 / b2 % 2 = 1 then
    (if PC.getD (i / W1 - b2) 0 < m ∧ TB.getD (srcIdx b2 W1 w i) 0 + p + q < d + 1 then
      TB.getD (srcIdx b2 W1 w i) 0 + p else INF)
  else TB.getD i 0

theorem sub_div_self (X b : ℕ) (hb : 0 < b) : (X - b) / b = X / b - 1 := by
  rcases le_or_gt b X with h | h
  · have := Nat.add_div_right (X - b) hb
    rw [Nat.sub_add_cancel h] at this
    generalize (X - b) / b = u at this ⊢
    generalize X / b = v at this ⊢
    omega
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.zero_div, Nat.div_eq_of_lt h]

theorem le_of_bit_set {X b2 : ℕ} (h : X / b2 % 2 = 1) : b2 ≤ X := by
  by_contra hlt
  push Not at hlt
  rw [Nat.div_eq_of_lt hlt] at h
  omega

theorem srcIdx_add_le {b2 W1 w i : ℕ} (hX : b2 ≤ i / W1) :
    srcIdx b2 W1 w i + b2 * W1 ≤ i := by
  unfold srcIdx
  have h1 : i / W1 * W1 ≤ i := Nat.div_mul_le_self i W1
  have h2 : (i / W1 - b2) * W1 + b2 * W1 = i / W1 * W1 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hX]
  omega

theorem srcIdx_div {b2 W1 w i : ℕ} (hW1 : 0 < W1) : srcIdx b2 W1 w i / W1 = i / W1 - b2 := by
  unfold srcIdx
  have hc : i - i / W1 * W1 - w < W1 := by
    have := Nat.mod_lt i hW1
    have h2 : i % W1 = i - i / W1 * W1 := by rw [Nat.mod_def, Nat.mul_comm]
    omega
  rw [Nat.mul_comm (i / W1 - b2) W1, Nat.mul_add_div hW1, Nat.div_eq_of_lt hc, Nat.add_zero]

theorem srcIdx_bit {b2 W1 w i : ℕ} (hb2 : 0 < b2) (hW1 : 0 < W1) (hbit : i / W1 / b2 % 2 = 1) :
    srcIdx b2 W1 w i / W1 / b2 % 2 = 0 := by
  rw [srcIdx_div hW1, sub_div_self _ _ hb2]
  omega

theorem startSet_spec {B : ℕ} (X i b2 W1 w p q d m INF S : ℕ) (TB PC : List ℕ)
    (hS : S = (X - b2) * W1 + (i - X * W1 - w))
    (hiB : i < B) (hiL : i < TB.length) (hXB : X < B) (_hXbB : X - b2 < B)
    (hXWB : X * W1 < B) (_hcB : i - X * W1 < B) (_hcwB : i - X * W1 - w < B)
    (hXbWB : (X - b2) * W1 < B) (hSB : S < B) (hSL : S < TB.length)
    (hSle : TB.getD S 0 ≤ INF) (hINF : INF < B) (hpq : INF + p + q < B) (hd1 : d + 1 < B)
    (hPCL : X - b2 < PC.length) (hPCv : PC.getD (X - b2) 0 < B) (hb2B : b2 < B) (hW1B : W1 < B)
    (hwB : w < B) (hmB : m < B) :
    Spec B (fun σ => σ.vars "X" = X ∧ σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧
        σ.vars "sw" = w ∧ σ.vars "sp" = p ∧ σ.vars "sq" = q ∧ σ.vars "sd" = d ∧
        σ.vars "m" = m ∧ σ.vars "i" = i ∧ σ.arrs "TB" = TB ∧ σ.arrs "PC" = PC)
      startSet
      (fun σ σ' => σ'.arrs "TB" = TB.set i
          (if PC.getD (X - b2) 0 < m ∧ TB.getD S 0 + p + q < d + 1 then TB.getD S 0 + p else INF) ∧
        (∀ y, y ≠ "c" → y ≠ "ri" → y ≠ "tv" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      60 := by
  have hTBB : TB.getD S 0 < B := lt_of_le_of_lt hSle hINF
  have hTBB' : ∀ (h : S < TB.length), TB[S] < B := fun h => by
    rwa [List.getD_eq_getElem _ _ h] at hTBB
  have hTS : TB.getD S 0 + p < B := by omega
  have hTS2 : TB.getD S 0 + p + q < B := by omega
  subst hS
  run_vcg
  all_goals simp_all [ite_and]
  all_goals (congr 1; split_ifs <;> first | rfl | omega)

theorem startBody_spec {B : ℕ} (b2 W1 MK w p q d m INF : ℕ) (i : ℕ) (TB PC : List ℕ)
    (hb2 : 0 < b2) (hW1 : 0 < W1) (hMK : 0 < MK) (hd : 2 * b2 ∣ MK)
    (hi : i < MK * W1) (hNL : MK * W1 ≤ TB.length) (hNB : MK * W1 < B) (hINF : INF < B)
    (hle : ∀ j, j / W1 / b2 % 2 = 0 → TB.getD j 0 ≤ INF)
    (hpq : INF + p + q < B) (hd1 : d + 1 < B) (hw : w < B) (hm : m < B) (hPCL : MK ≤ PC.length) (hPCB : ∀ j < MK, PC.getD j 0 < B) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧
        σ.vars "sw" = w ∧ σ.vars "sp" = p ∧ σ.vars "sq" = q ∧ σ.vars "sd" = d ∧
        σ.vars "m" = m ∧ σ.vars "i" = i ∧ σ.arrs "TB" = TB ∧ σ.arrs "PC" = PC)
      startBody
      (fun σ σ' => σ'.arrs "TB" = TB.set i (startStep b2 W1 w p q d m INF TB PC i) ∧
        σ'.vars "i" = i + 1 ∧
        (∀ y, y ≠ "X" → y ≠ "c" → y ≠ "ri" → y ≠ "tv" → y ≠ "i" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      80 := by
  have hb2MK : b2 ≤ MK := le_trans (by omega) (Nat.le_of_dvd hMK hd)
  have hMKN : MK ≤ MK * W1 := Nat.le_mul_of_pos_right _ hW1
  have hW1N : W1 ≤ MK * W1 := Nat.le_mul_of_pos_left _ hMK
  have hX1 : i / W1 < MK := (Nat.div_lt_iff_lt_mul hW1).mpr hi
  have hXi : i / W1 ≤ i := Nat.div_le_self _ _
  have hXWi : i / W1 * W1 ≤ i := Nat.div_mul_le_self i W1
  have hX : i / W1 < B := by omega
  have hXb : i / W1 / b2 < B := lt_of_le_of_lt (Nat.div_le_self _ _) hX
  have hland : Nat.land (i / W1 / b2) 1 < B := by
    rw [land_one]; have := Nat.mod_lt (i / W1 / b2) (by norm_num : 0 < 2)
    have : 2 ≤ B := by omega
    omega
  have hb2B : b2 < B := by omega
  have hW1B : W1 < B := by omega
  have hXWB : i / W1 * W1 < B := by omega
  have hciB : i - i / W1 * W1 < B := by omega
  have hcwB : i - i / W1 * W1 - w < B := by omega
  have hXbB : i / W1 - b2 < B := by omega
  have hXbWB : (i / W1 - b2) * W1 < B := by
    have : (i / W1 - b2) * W1 ≤ i / W1 * W1 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  have hPCidx : i / W1 - b2 < PC.length := by omega
  have hPCv : PC.getD (i / W1 - b2) 0 < B := hPCB _ (by omega)
  by_cases hbit : i / W1 / b2 % 2 = 1
  · have hXge : b2 ≤ i / W1 := le_of_bit_set hbit
    have hsrc := srcIdx_add_le (b2 := b2) (W1 := W1) (w := w) (i := i) hXge
    have hb2W : 0 < b2 * W1 := Nat.mul_pos hb2 hW1
    have hsrci : srcIdx b2 W1 w i < i := by omega
    have hsrcB : srcIdx b2 W1 w i < B := by omega
    have hsrcL : srcIdx b2 W1 w i < TB.length := by omega
    have hset := startSet_spec (B := B) (i / W1) i b2 W1 w p q d m INF (srcIdx b2 W1 w i) TB PC rfl
      (by omega) (by omega) hX (by omega) hXWB hciB hcwB hXbWB hsrcB hsrcL (hle _ (srcIdx_bit hb2 hW1 hbit)) hINF hpq hd1
      hPCidx hPCv hb2B hW1B hw hm
    run_vcg [hset]
    all_goals (try simp_all [startStep, ite_and])
    all_goals omega
  · have hset0 : Spec B (fun _ => False) startSet (fun _ _ => True) 0 := fun σ h => h.elim
    run_vcg [hset0]
    all_goals (try simp_all [startStep])
    all_goals first
      | omega
      | exact (set_getD_self' _ _ (by omega)).symm

/-- The whole start pass: set the counter bound, then sweep every cell in ascending order. -/
def startLoop : Com :=
  .seq (.assign "N" (.bin .mul (V "MK") (V "W1")))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) startBody))

/-- The start pass's invariant: the cells below `i` are new, the others old. -/
def StartInv (b2 W1 N w p q d m INF : ℕ) (TB0 PC : List ℕ) (σ : Env) : Prop :=
  σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "cinf" = INF ∧ σ.vars "sw" = w ∧
  σ.vars "sp" = p ∧ σ.vars "sq" = q ∧ σ.vars "sd" = d ∧ σ.vars "m" = m ∧
  σ.vars "N" = N ∧ σ.vars "i" ≤ N ∧ σ.arrs "PC" = PC ∧ (σ.arrs "TB").length = TB0.length ∧
  ∀ j, (σ.arrs "TB").getD j 0 =
    if j < σ.vars "i" then startStep b2 W1 w p q d m INF TB0 PC j else TB0.getD j 0

/-- A cell in a row with bit `b` clear is not changed by the pass. -/
theorem startStep_clear {b2 W1 w p q d m INF : ℕ} (TB PC : List ℕ) {j : ℕ}
    (h : j / W1 / b2 % 2 = 0) : startStep b2 W1 w p q d m INF TB PC j = TB.getD j 0 := by
  unfold startStep
  rw [if_neg (by omega)]

/-- The value the pass computes is the same whether the cells below `i` are new or old. -/
theorem startStep_cur {b2 W1 w p q d m INF : ℕ} (hb2 : 0 < b2) (hW1 : 0 < W1) (TB TB0 PC : List ℕ)
    (i : ℕ)
    (h8 : ∀ j, TB.getD j 0 = if j < i then startStep b2 W1 w p q d m INF TB0 PC j
      else TB0.getD j 0) :
    startStep b2 W1 w p q d m INF TB PC i = startStep b2 W1 w p q d m INF TB0 PC i := by
  by_cases hbit : i / W1 / b2 % 2 = 1
  · have hXge : b2 ≤ i / W1 := le_of_bit_set hbit
    have hsrc := srcIdx_add_le (b2 := b2) (W1 := W1) (w := w) (i := i) hXge
    have hb2W : 0 < b2 * W1 := Nat.mul_pos hb2 hW1
    have hsrci : srcIdx b2 W1 w i < i := by omega
    have hS : TB.getD (srcIdx b2 W1 w i) 0 = TB0.getD (srcIdx b2 W1 w i) 0 := by
      rw [h8, if_pos hsrci, startStep_clear _ _ (srcIdx_bit hb2 hW1 hbit)]
    unfold startStep
    rw [if_pos hbit, if_pos hbit, hS]
  · have h0 : i / W1 / b2 % 2 = 0 := by omega
    rw [startStep_clear _ _ h0, startStep_clear _ _ h0, h8 i, if_neg (lt_irrefl _)]

theorem startLoop_spec {B : ℕ} (b2 W1 MK w p q d m INF : ℕ) (TB0 PC : List ℕ)
    (hb2 : 0 < b2) (hW1 : 0 < W1) (hMK : 0 < MK) (hd : 2 * b2 ∣ MK)
    (hNL : MK * W1 ≤ TB0.length) (hNB : MK * W1 < B) (hINF : INF < B)
    (hle : ∀ j, j / W1 / b2 % 2 = 0 → TB0.getD j 0 ≤ INF)
    (hpq : INF + p + q < B) (hd1 : d + 1 < B) (hw : w < B) (hm : m < B)
    (hPCL : MK ≤ PC.length) (hPCB : ∀ j < MK, PC.getD j 0 < B) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "MK" = MK ∧
        σ.vars "cinf" = INF ∧ σ.vars "sw" = w ∧ σ.vars "sp" = p ∧ σ.vars "sq" = q ∧
        σ.vars "sd" = d ∧ σ.vars "m" = m ∧ σ.arrs "TB" = TB0 ∧ σ.arrs "PC" = PC)
      startLoop
      (fun _ σ' => (σ'.arrs "TB").length = TB0.length ∧
        ∀ j, (σ'.arrs "TB").getD j 0 =
          if j < MK * W1 then startStep b2 W1 w p q d m INF TB0 PC j else TB0.getD j 0)
      (84 * (MK * W1) + 14) := by
  have hbody : Spec B (fun σ => StartInv b2 W1 (MK * W1) w p q d m INF TB0 PC σ ∧
        σ.vars "i" < MK * W1)
      startBody (fun σ σ' => StartInv b2 W1 (MK * W1) w p q d m INF TB0 PC σ' ∧
        σ'.vars "i" = σ.vars "i" + 1) 80 := by
    intro σ ⟨hI, hlt⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hI
    have hle' : ∀ j, j / W1 / b2 % 2 = 0 → (σ.arrs "TB").getD j 0 ≤ INF := by
      intro j hj
      rw [h13 j]
      split_ifs
      · rw [startStep_clear _ _ hj]; exact hle j hj
      · exact hle j hj
    obtain ⟨σ', hrun, hTB, hi', hfv, hfa, hinp, hout⟩ := startBody_spec (B := B) b2 W1 MK w p q d
      m INF (σ.vars "i") (σ.arrs "TB") PC hb2 hW1 hMK hd hlt
      (by rw [h12]; exact hNL) hNB hINF hle' hpq hd1 hw hm hPCL hPCB σ
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl, rfl, h11⟩
    have hi0 : σ.vars "i" < (σ.arrs "TB").length := by rw [h12]; omega
    refine ⟨σ', hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hi'⟩
    · rw [hfv "b2" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1
    · rw [hfv "W1" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2
    · rw [hfv "cinf" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3
    · rw [hfv "sw" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
    · rw [hfv "sp" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
    · rw [hfv "sq" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
    · rw [hfv "sd" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7
    · rw [hfv "m" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
    · rw [hfv "N" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
    · rw [hi']; omega
    · rw [hfa "PC" (by decide)]; exact h11
    · rw [hTB, List.length_set]; exact h12
    · intro j
      rw [hTB, hi', startStep_cur hb2 hW1 _ TB0 PC _ h13]
      by_cases hj : j = σ.vars "i"
      · subst hj
        rw [getD_set_self _ _ _ hi0, if_pos (by omega)]
      · rw [getD_set_ne _ _ _ _ hj, h13 j]
        by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
  have hloop := Spec.forRangeZero (B := B) "i" "N" (StartInv b2 W1 (MK * W1) w p q d m INF TB0 PC)
    (MK * W1) 80 hNB (fun σ h => h.2.2.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.2.2.2.2.1) hbody
  have hMKB : MK < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hW1) hNB
  have hW1B : W1 < B := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hMK) hNB
  run_vcg [hloop]
  all_goals first
    | (obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, hl, hg⟩, hi⟩ :=
        ‹StartInv b2 W1 (MK * W1) w p q d m INF TB0 PC _ ∧ _ = MK * W1›
       exact ⟨hl, fun j => by rw [hg j, hi]⟩)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Env.setVar])
    | (simp_all)

theorem pcnt_le (X : ℕ) : pcnt X ≤ X := by
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    rcases Nat.eq_zero_or_pos X with h | h
    · subst h; simp [pcnt]
    · rw [pcnt_div_two X]
      have := ih (X / 2) (by omega)
      omega

/-- **The start pass's per-cell value is the paper's `startT`, entry by entry.** -/
theorem startStep_eq {b b2 W1 w p q d m INF : ℕ} (hb2 : b2 = 2 ^ b) (hW1 : 0 < W1)
    (TB0 PC : List ℕ) {X c : ℕ} (hc : c < W1)
    (hPC : X / b2 % 2 = 1 → PC.getD (X - b2) 0 = pcnt (X - 2 ^ b)) :
    startStep b2 W1 w p q d m INF TB0 PC (X * W1 + c)
      = startT b w p q d m INF (tabOf W1 TB0) X c := by
  have hdiv : (X * W1 + c) / W1 = X := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW1, Nat.div_eq_of_lt hc, zero_add]
  have hcc : X * W1 + c - X * W1 = c := by omega
  unfold startStep startT srcIdx
  rw [hdiv, hcc, ← hb2]
  by_cases hbit : X / b2 % 2 = 1
  · rw [if_pos hbit, if_pos hbit, hPC hbit, hb2]
    simp only [tabOf, Nat.lt_succ_iff, Nat.add_assoc]
  · rw [if_neg hbit, if_neg hbit]; rfl

theorem startLoop_table {B : ℕ} (b b2 W1 MK w p q d m INF : ℕ) (TB0 PC : List ℕ)
    (hb2 : b2 = 2 ^ b) (hW1 : 0 < W1) (hMK : 0 < MK) (hd : 2 * b2 ∣ MK)
    (hNL : MK * W1 ≤ TB0.length) (hNB : MK * W1 < B) (hINF : INF < B)
    (hle : ∀ j, j / W1 / b2 % 2 = 0 → TB0.getD j 0 ≤ INF)
    (hpq : INF + p + q < B) (hd1 : d + 1 < B) (hw : w < B) (hm : m < B)
    (hPCL : MK ≤ PC.length) (hPC : ∀ j < MK, PC.getD j 0 = pcnt j) :
    Spec B (fun σ => σ.vars "b2" = b2 ∧ σ.vars "W1" = W1 ∧ σ.vars "MK" = MK ∧
        σ.vars "cinf" = INF ∧ σ.vars "sw" = w ∧ σ.vars "sp" = p ∧ σ.vars "sq" = q ∧
        σ.vars "sd" = d ∧ σ.vars "m" = m ∧ σ.arrs "TB" = TB0 ∧ σ.arrs "PC" = PC)
      startLoop
      (fun σ σ' => (σ'.arrs "TB").length = TB0.length ∧
        (∀ X < MK, ∀ c < W1,
          tabOf W1 (σ'.arrs "TB") X c = startT b w p q d m INF (tabOf W1 TB0) X c) ∧
        (∀ j, MK * W1 ≤ j → (σ'.arrs "TB").getD j 0 = TB0.getD j 0) ∧
        (d ≤ INF → ∀ j, j < MK * W1 → (σ'.arrs "TB").getD j 0 ≤ INF) ∧
        (∀ y, y ≠ "N" → y ≠ "i" → y ≠ "X" → y ≠ "c" → y ≠ "ri" → y ≠ "tv" →
          σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TB" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (84 * (MK * W1) + 14) := by
  have hb2pos : 0 < b2 := by rw [hb2]; positivity
  have hMKB : MK < B := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hW1) hNB
  have hPCB : ∀ j < MK, PC.getD j 0 < B := fun j hj => by
    rw [hPC j hj]; have := pcnt_le j; omega
  refine ((startLoop_spec b2 W1 MK w p q d m INF TB0 PC hb2pos hW1 hMK hd hNL hNB hINF hle hpq hd1
    hw hm hPCL hPCB).frame).post ?_
  rintro σ σ' - ⟨⟨hlen, hget⟩, hfv, hfa, hinp, hout⟩
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX c hc
    have hj : X * W1 + c < MK * W1 := by
      have : (X + 1) * W1 ≤ MK * W1 := Nat.mul_le_mul_right _ hX
      nlinarith
    change (σ'.arrs "TB").getD (X * W1 + c) 0 = startT b w p q d m INF (tabOf W1 TB0) X c
    rw [hget, if_pos hj]
    refine startStep_eq hb2 hW1 TB0 PC hc (fun hbit => ?_)
    have hbm : b2 ≤ X := le_of_bit_set hbit
    exact hPC _ (by omega) |>.trans (by rw [hb2])
  · intro j hj
    rw [hget, if_neg (by omega)]
  · intro hdI j hj
    rw [hget, if_pos hj]
    unfold startStep
    split_ifs with h1 h2
    · rw [Nat.add_assoc] at h2; omega
    · exact le_rfl
    · exact hle j (by omega)
  · intro y h1 h2 h3 h4 h5 h6
    exact hfv y (by simp [startLoop, startBody, startSet, Com.wvars]; tauto)
  · intro a ha
    exact hfa a (by simp [startLoop, startBody, startSet, Com.warrs]; exact ha)
  · exact hinp (by simp [startLoop, startBody, startSet, Com.reads])
  · exact hout (by simp [startLoop, startBody, startSet, Com.NoWrite])

/-! ## Growing the popcount array -/

/-- `PC[gx + MK] := PC[gx] + 1`, then the counter moves up. -/
def growBody : Com :=
  .seq (.store "PC" (.bin .add (V "gx") (V "MK")) (.bin .add (.get "PC" (V "gx")) (.lit 1)))
    (.assign "gx" (.bin .add (V "gx") (.lit 1)))

/-- When the masks double, copy the popcounts of the old masks `X < MK` to `X + MK`, one more. -/
def growPC : Com :=
  .seq (.assign "gx" (.lit 0)) (.while (.lt (V "gx") (V "MK")) growBody)

theorem growBody_spec {B : ℕ} (MK gx : ℕ) (PC : List ℕ) (hgx : gx < MK) (hL : 2 * MK ≤ PC.length)
    (hMKB : 2 * MK < B) (hPCB : PC.getD gx 0 + 1 < B) :
    Spec B (fun σ => σ.vars "MK" = MK ∧ σ.vars "gx" = gx ∧ σ.arrs "PC" = PC) growBody
      (fun σ σ' => σ'.arrs "PC" = PC.set (gx + MK) (PC.getD gx 0 + 1) ∧ σ'.vars "gx" = gx + 1 ∧
        (∀ y, y ≠ "gx" → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "PC" → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out)
      20 := by
  have hPCB' : ∀ h : gx < PC.length, PC[gx] + 1 < B := fun h => by
    rwa [List.getD_eq_getElem _ _ h] at hPCB
  run_vcg
  all_goals simp_all
  all_goals omega

/-- The growth loop's invariant. -/
def GrowInv (MK : ℕ) (PC0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "MK" = MK ∧ σ.vars "gx" ≤ MK ∧ (σ.arrs "PC").length = PC0.length ∧
  ∀ j, (σ.arrs "PC").getD j 0 =
    if MK ≤ j ∧ j < MK + σ.vars "gx" then PC0.getD (j - MK) 0 + 1 else PC0.getD j 0

theorem growPC_spec {B : ℕ} (MK : ℕ) (PC0 : List ℕ) (hL : 2 * MK ≤ PC0.length)
    (hMKB : 2 * MK < B) (hPCB : ∀ j < MK, PC0.getD j 0 + 1 < B) :
    Spec B (fun σ => σ.vars "MK" = MK ∧ σ.arrs "PC" = PC0) growPC
      (fun σ σ' => (σ'.arrs "PC").length = PC0.length ∧
        (∀ j, j < MK → (σ'.arrs "PC").getD j 0 = PC0.getD j 0) ∧
        (∀ j, MK ≤ j → j < 2 * MK → (σ'.arrs "PC").getD j 0 = PC0.getD (j - MK) 0 + 1) ∧
        (∀ j, 2 * MK ≤ j → (σ'.arrs "PC").getD j 0 = PC0.getD j 0) ∧
        (∀ y, y ≠ "gx" → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "PC" → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (24 * MK + 6) := by
  have hbody : Spec B (fun σ => GrowInv MK PC0 σ ∧ σ.vars "gx" < MK) growBody
      (fun σ σ' => GrowInv MK PC0 σ' ∧ σ'.vars "gx" = σ.vars "gx" + 1) 20 := by
    intro σ ⟨⟨h1, h2, h3, h4⟩, hlt⟩
    have hget : (σ.arrs "PC").getD (σ.vars "gx") 0 = PC0.getD (σ.vars "gx") 0 := by
      rw [h4, if_neg (by omega)]
    obtain ⟨σ', hrun, hPC, hgx, hfv, hfa, hinp, hout⟩ := growBody_spec (B := B) MK (σ.vars "gx")
      (σ.arrs "PC") hlt (by rw [h3]; exact hL) hMKB (by rw [hget]; exact hPCB _ hlt) σ ⟨h1, rfl, rfl⟩
    refine ⟨σ', hrun, ⟨?_, ?_, ?_, ?_⟩, hgx⟩
    · rw [hfv "MK" (by decide)]; exact h1
    · rw [hgx]; omega
    · rw [hPC, List.length_set]; exact h3
    · intro j
      rw [hPC, hgx]
      by_cases hj : j = σ.vars "gx" + MK
      · subst hj
        rw [getD_set_self _ _ _ (by rw [h3]; omega), if_pos (by omega), hget]
        congr 2
        omega
      · rw [getD_set_ne _ _ _ _ hj, h4 j]
        by_cases hjl : MK ≤ j ∧ j < MK + σ.vars "gx"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
  have hloop := Spec.forRangeZero (B := B) "gx" "MK" (GrowInv MK PC0) MK 20 (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1) hbody
  refine (hloop.frame.conseq ?_ ?_ (by omega))
  · rintro σ ⟨h1, h2⟩
    exact ⟨by simpa [Env.setVar] using h1, by simp [Env.setVar], by simp [Env.setVar, h2],
      by intro j; simp [Env.setVar, h2]⟩
  · rintro σ σ' ⟨h1, h2⟩ ⟨⟨⟨_, _, hlen, hget⟩, hgx⟩, hfv, hfa, hinp, hout⟩
    refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; rw [hget j, if_neg (by omega)]
    · intro j hj1 hj2; rw [hget j, if_pos (by omega)]
    · intro j hj; rw [hget j, if_neg (by omega)]
    · intro y hy; exact hfv y (by simp [growBody, Com.wvars]; exact hy)
    · intro a ha; exact hfa a (by simp [growBody, Com.warrs]; exact ha)
    · exact hinp (by simp [growBody, Com.reads])
    · exact hout (by simp [growBody, Com.NoWrite])

/-- Setting a fresh top bit adds one to the popcount. -/
theorem pcnt_add_pow (b : ℕ) : ∀ X, X < 2 ^ b → pcnt (X + 2 ^ b) = pcnt X + 1 := by
  induction b with
  | zero =>
    intro X hX
    have : X = 0 := by omega
    subst this
    have h := pcnt_div_two 1
    have h0 := pcnt_div_two 0
    simp only [Nat.pow_zero, Nat.zero_add] at *
    omega
  | succ b ih =>
    intro X hX
    have hp : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    have h1 : (X + 2 ^ (b + 1)) / 2 = X / 2 + 2 ^ b := by omega
    have h2 : (X + 2 ^ (b + 1)) % 2 = X % 2 := by omega
    rw [pcnt_div_two (X + 2 ^ (b + 1)), pcnt_div_two X, h1, h2, ih (X / 2) (by omega)]
    omega

/-- **The popcount array, grown.** `PC` is correct on the masks below `MK = 2^b`; afterwards it is
correct on the masks below `2 * MK`, and everything at or beyond `2 * MK` is untouched. -/
theorem growPC_table {B : ℕ} (b MK : ℕ) (PC0 : List ℕ) (hMK : MK = 2 ^ b)
    (hL : 2 * MK ≤ PC0.length) (hMKB : 2 * MK < B) (hPC : ∀ j < MK, PC0.getD j 0 = pcnt j) :
    Spec B (fun σ => σ.vars "MK" = MK ∧ σ.arrs "PC" = PC0) growPC
      (fun σ σ' => (σ'.arrs "PC").length = PC0.length ∧
        (∀ j, j < 2 * MK → (σ'.arrs "PC").getD j 0 = pcnt j) ∧
        (∀ j, 2 * MK ≤ j → (σ'.arrs "PC").getD j 0 = PC0.getD j 0) ∧
        (∀ y, y ≠ "gx" → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "PC" → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (24 * MK + 6) := by
  have hPCB : ∀ j < MK, PC0.getD j 0 + 1 < B := fun j hj => by
    rw [hPC j hj]; have := pcnt_le j; omega
  refine (growPC_spec MK PC0 hL hMKB hPCB).post ?_
  rintro σ σ' - ⟨hlen, h1, h2, h3, hfv, hfa, hinp, hout⟩
  refine ⟨hlen, ?_, h3, hfv, hfa, hinp, hout⟩
  intro j hj
  by_cases hjl : j < MK
  · rw [h1 j hjl, hPC j hjl]
  · rw [h2 j (by omega) hj]
    have hj' : j - MK < 2 ^ b := by omega
    have := pcnt_add_pow b (j - MK) hj'
    rw [hPC _ (by omega), ← hMK] at *
    have hjj : j - MK + MK = j := by omega
    rw [hjj] at this
    omega

end Lax496464Proofs.Ram.W3Loops
