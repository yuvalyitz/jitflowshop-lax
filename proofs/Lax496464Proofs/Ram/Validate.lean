import Lax496464Proofs.Ram.Build

/-!
# Checking That What the Scan Read Is a Hitting Set Word

The scan reads `n`, `m`, `m + 1` offsets, a member array and `k` whatever the header claims.
`validate` checks the remaining conditions of `HittingSet.Encodes` on what was read: the offsets
start at `0` and never decrease, every member is below `n`, the members of each block are
strictly increasing, the universe is no larger than the word, and `2 ≤ k ≤ n`. It leaves
`"valid"` at `1` if all hold and clears it to `0` otherwise (`validate_spec_generic`). A program
built from IMP+'s `Com` cannot test for end of input, so it cannot detect an over-long word, but
it rejects a malformed one.
-/

namespace Lax496464Proofs.Ram.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet
open Lax496464Proofs.Ram.Build (RC)
open Classical

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- Clear `"valid"` to `0` if `p` fails. -/
def failIf (p : Cond) : Com := .ite p (.assign "valid" (.lit 0)) .skip

/-- Clear `"valid"` to `0` unless `p` holds. -/
def failUnless (p : Cond) : Com := .ite p .skip (.assign "valid" (.lit 0))

/-- Check `OFF[j] ≤ OFF[j+1]` for every `j < m`. -/
def checkOffsets : Com :=
  .seq (.assign "j" (.lit 0))
    (.while (.lt (V "j") (V "m"))
      (.seq (failIf (.lt (.get "OFF" (.bin .add (V "j") (.lit 1))) (.get "OFF" (V "j"))))
        (bump "j")))

/-- Check `MEM[t] < n` for every `t < OFF[m]`. -/
def checkMembers : Com :=
  .seq (.assign "L" (.get "OFF" (V "m")))
    (.seq (.assign "t" (.lit 0))
      (.while (.lt (V "t") (V "L"))
        (.seq (failUnless (.lt (.get "MEM" (V "t")) (V "n")))
          (bump "t"))))

/-- The turn of the scan: inside the owner's row, compare the member at `"j"` against the
previous member of the same block (held in `"p"`, skipping the comparison at a block's first
slot) and advance; past the row's end, advance the owner instead. Guarded by `"u" < "m"` so
the reads of `OFF[u]`/`OFF[u + 1]` stay in bounds regardless of whether the offsets are
actually monotone. -/
def sortedBody : Com :=
  .ite (.lt (V "u") (V "m"))
    (.ite (.lt (V "j") (.get "OFF" (.bin .add (V "u") (.lit 1))))
      (.seq
        (.ite (.eq (V "j") (.get "OFF" (V "u"))) .skip
          (failUnless (.lt (V "p") (.get "MEM" (V "j")))))
        (.seq (.assign "p" (.get "MEM" (V "j"))) (bump "j")))
      (bump "u"))
    (bump "j")

/-- Scan the whole member array once, checking every member against the previous member of
its own block. -/
def checkSorted : Com :=
  .seq (.assign "L" (.get "OFF" (V "m")))
    (.seq (.assign "j" (.lit 0))
      (.seq (.assign "u" (.lit 0)) (.while (.lt (V "j") (V "L")) sortedBody)))

/-- Check `n ≤ m + OFF[m] + 4` — the size bound `Encodes.universeSize_le` (`P.n ≤ x.length`)
comes to, once `Encodes.length_eq` (`x.length = 4 + P.m + offset x P.m`) rewrites the length.
`checkOffsets`/`checkMembers`/`checkSorted` alone accept a tape whose declared universe is far
larger than the word that names it could ever actually enumerate — a self-delimiting code can
spend very few bits on a huge `n` and few sets, so this closes the last gap between what
`validate` accepts and what an admissible `csrWord P k` can actually look like. Rereads
`OFF[m]` itself (rather than reusing whatever `"L"` happens to hold after `checkSorted`) so it
needs nothing about `checkSorted`'s own internals beyond `"OFF"`/`"m"` being left untouched. -/
def checkUniverseBound : Com :=
  .seq (.assign "L" (.get "OFF" (V "m")))
    (failIf (.lt (.bin .add (.bin .add (V "m") (V "L")) (.lit 4)) (V "n")))

/-- **The check.** `"valid"` ends at `1` exactly when `OFF`/`MEM`/`n`/`k` (as `RC` reports
them) satisfy `Encodes`'s data conditions — including its size bound — plus block-relative
member sortedness, beyond the header lengths `readHS` already guarantees by construction. -/
def validate : Com :=
  .seq (.assign "valid" (.lit 1))
    (.seq (failUnless (.eq (.get "OFF" (.lit 0)) (.lit 0)))
      (.seq checkOffsets
        (.seq checkMembers
          (.seq checkSorted
            (.seq checkUniverseBound
              (.seq (failIf (.lt (V "k") (.lit 2)))
                (failIf (.lt (V "n") (V "k")))))))))

variable (foff fmem : ℕ → ℕ)

/-- Every one of the first `j` consecutive pairs of offsets is nondecreasing. -/
def OffsetsOkG (j : ℕ) : Prop := ∀ i < j, foff i ≤ foff (i + 1)

theorem OffsetsOkG.zero : OffsetsOkG foff 0 := fun _ h => absurd h (by omega)

theorem OffsetsOkG.succ {j : ℕ} (h : OffsetsOkG foff j) (hj : foff j ≤ foff (j + 1)) :
    OffsetsOkG foff (j + 1) := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
  · exact h i hi'
  · exact hj

/-- **Transitivity of stepwise monotonicity.** Any two indices inside the pinned range are
themselves ordered, not just consecutive ones. -/
theorem OffsetsOkG.mono {j : ℕ} (h : OffsetsOkG foff j) :
    ∀ {i k}, i ≤ k → k ≤ j → foff i ≤ foff k := by
  intro i k
  induction k with
  | zero =>
    intro hik _
    have hi0 : i = 0 := by omega
    exact hi0 ▸ le_refl _
  | succ k ih =>
    intro hik hkj
    rcases Nat.lt_or_ge i (k + 1) with hi | hi
    · exact (ih (by omega) (by omega)).trans (h k (by omega))
    · have hi' : i = k + 1 := by omega
      exact hi' ▸ le_refl _

theorem checkOffsets_spec_generic {B : ℕ} (m0 v0 : ℕ) (hB : 1 < B) (hOFFb : ∀ i ≤ m0, foff i + 1 < B)
    (hm0B : m0 < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "valid" = v0 ∧
        (σ.arrs "OFF").length = m0 + 1 ∧
        (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i))
      checkOffsets
      (fun _ σ' => σ'.vars "j" = m0 ∧
        (OffsetsOkG foff m0 → σ'.vars "valid" = v0) ∧
        (¬ OffsetsOkG foff m0 → σ'.vars "valid" = 0))
      (18 * m0 + 6) := by
  unfold checkOffsets
  have hbody : Spec B
      (fun σ => (σ.vars "j" ≤ m0 ∧ σ.vars "m" = m0 ∧ (σ.arrs "OFF").length = m0 + 1 ∧
          (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
          (OffsetsOkG foff (σ.vars "j") → σ.vars "valid" = v0) ∧
          (¬ OffsetsOkG foff (σ.vars "j") → σ.vars "valid" = 0)) ∧
        σ.vars "j" < m0)
      (.seq (failIf (.lt (.get "OFF" (.bin .add (V "j") (.lit 1))) (.get "OFF" (V "j"))))
        (bump "j"))
      (fun σ σ' => ((σ'.vars "j" ≤ m0 ∧ σ'.vars "m" = m0 ∧ (σ'.arrs "OFF").length = m0 + 1 ∧
          (∀ i ≤ m0, (σ'.arrs "OFF").getD i 0 = foff i) ∧
          (OffsetsOkG foff (σ'.vars "j") → σ'.vars "valid" = v0) ∧
          (¬ OffsetsOkG foff (σ'.vars "j") → σ'.vars "valid" = 0))) ∧
        σ'.vars "j" = σ.vars "j" + 1)
      14 := by
    rintro σ ⟨⟨hjm0, hm, hlen, hoff, hgood, hbad⟩, hjlt⟩
    have hj1m : σ.vars "j" + 1 ≤ m0 := by omega
    have hjOFF : σ.vars "j" < (σ.arrs "OFF").length := by omega
    have hj1OFF : σ.vars "j" + 1 < (σ.arrs "OFF").length := by omega
    have hj0 : (σ.arrs "OFF").getD (σ.vars "j") 0 = foff (σ.vars "j") := hoff _ (by omega)
    have hj1 : (σ.arrs "OFF").getD (σ.vars "j" + 1) 0 = foff (σ.vars "j" + 1) := hoff _ hj1m
    have hb0 : foff (σ.vars "j") + 1 < B := hOFFb _ (by omega)
    have hb1 : foff (σ.vars "j" + 1) + 1 < B := hOFFb _ hj1m
    have hjB : σ.vars "j" < B := by omega
    by_cases hstep : foff (σ.vars "j" + 1) < foff (σ.vars "j")
    · -- fails at this step: offsets not monotone here
      have hnotok : ¬ OffsetsOkG foff (σ.vars "j" + 1) :=
        fun hok => absurd (hok (σ.vars "j") (by omega)) (by omega)
      run_vcg
      all_goals (simp_all)
    · -- holds at this step
      have hle : foff (σ.vars "j") ≤ foff (σ.vars "j" + 1) := by omega
      have hgoodstep : OffsetsOkG foff (σ.vars "j" + 1) → σ.vars "valid" = v0 := fun h =>
        hgood (fun i hi => h i (by omega))
      have hbadstep : ¬ OffsetsOkG foff (σ.vars "j" + 1) → σ.vars "valid" = 0 := fun h =>
        hbad (fun hcon => h (OffsetsOkG.succ foff hcon hle))
      run_vcg
      all_goals (simp_all)
      all_goals omega
  refine ((Spec.forRangeZero (B := B) "j" "m"
    (fun σ => σ.vars "j" ≤ m0 ∧ σ.vars "m" = m0 ∧ (σ.arrs "OFF").length = m0 + 1 ∧
      (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (OffsetsOkG foff (σ.vars "j") → σ.vars "valid" = v0) ∧
      (¬ OffsetsOkG foff (σ.vars "j") → σ.vars "valid" = 0))
    m0 14 hm0B (fun _ h => h.1) (fun σ h => h.2.1) hbody
    ).pre ?_).post ?_
  · intro σ ⟨hm, hval, hlen, hoff⟩
    simp only [Env.setVar]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | (simp_all; done) | (intro hn; exact absurd (OffsetsOkG.zero foff) hn)
  · intro σ σ' hσ ⟨⟨h0, h1, h2, h3, h4, h5⟩, hj⟩
    exact ⟨hj, by rw [← hj] at *; exact h4, by rw [← hj] at *; exact h5⟩

/-- Every one of the first `t` members is below `n0`. -/
def MembersOkG (n0 t : ℕ) : Prop := ∀ u < t, fmem u < n0

theorem MembersOkG.zero {n0 : ℕ} : MembersOkG fmem n0 0 := fun _ h => absurd h (by omega)

theorem checkMembers_spec_generic {B : ℕ} (L n0 v0 : ℕ) (hB : 1 < B) (hMEMb : ∀ t < L, fmem t + 1 < B)
    (hn0B : n0 < B) (hLB : L < B) :
    Spec B (fun σ => σ.vars "n" = n0 ∧ σ.vars "valid" = v0 ∧
        (σ.arrs "MEM").length = L ∧ σ.vars "m" < (σ.arrs "OFF").length ∧
        σ.vars "m" + 1 < B ∧
        (σ.arrs "OFF").getD (σ.vars "m") 0 = L ∧
        (∀ t < L, (σ.arrs "MEM").getD t 0 = fmem t))
      checkMembers
      (fun _ σ' => σ'.vars "t" = L ∧
        (MembersOkG fmem n0 L → σ'.vars "valid" = v0) ∧
        (¬ MembersOkG fmem n0 L → σ'.vars "valid" = 0))
      (18 * L + 9) := by
  unfold checkMembers
  have hbody : Spec B
      (fun σ => (σ.vars "L" = L ∧ σ.vars "t" ≤ L ∧ σ.vars "n" = n0 ∧
          (σ.arrs "MEM").length = L ∧
          (σ.arrs "OFF").getD (σ.vars "m") 0 = L ∧
          (∀ t < L, (σ.arrs "MEM").getD t 0 = fmem t) ∧
          (MembersOkG fmem n0 (σ.vars "t") → σ.vars "valid" = v0) ∧
          (¬ MembersOkG fmem n0 (σ.vars "t") → σ.vars "valid" = 0)) ∧
        σ.vars "t" < L)
      (.seq (failUnless (.lt (.get "MEM" (V "t")) (V "n"))) (bump "t"))
      (fun σ σ' => ((σ'.vars "L" = L ∧ σ'.vars "t" ≤ L ∧ σ'.vars "n" = n0 ∧
          (σ'.arrs "MEM").length = L ∧
          (σ'.arrs "OFF").getD (σ'.vars "m") 0 = L ∧
          (∀ t < L, (σ'.arrs "MEM").getD t 0 = fmem t) ∧
          (MembersOkG fmem n0 (σ'.vars "t") → σ'.vars "valid" = v0) ∧
          (¬ MembersOkG fmem n0 (σ'.vars "t") → σ'.vars "valid" = 0))) ∧
        σ'.vars "t" = σ.vars "t" + 1)
      14 := by
    rintro σ ⟨⟨hLL, htL, hn, hlen, hoffm, hmem, hgood, hbad⟩, htlt⟩
    have ht1L : σ.vars "t" + 1 ≤ L := by omega
    have htMEM : σ.vars "t" < (σ.arrs "MEM").length := by omega
    have ht0 : (σ.arrs "MEM").getD (σ.vars "t") 0 = fmem (σ.vars "t") := hmem _ (by omega)
    have hb0 : fmem (σ.vars "t") + 1 < B := hMEMb _ (by omega)
    have htB : σ.vars "t" < B := by omega
    have hgoodstep : MembersOkG fmem n0 (σ.vars "t" + 1) → σ.vars "valid" = v0 := fun h =>
      hgood (fun u hu => h u (by omega))
    by_cases hstep : fmem (σ.vars "t") < n0
    · have hbadstep : ¬ MembersOkG fmem n0 (σ.vars "t" + 1) → σ.vars "valid" = 0 := fun h =>
        hbad (fun hcon => h (fun u hu => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu' | rfl
          · exact hcon u hu'
          · exact hstep))
      run_vcg
      all_goals (simp_all)
    · have hnotok : ¬ MembersOkG fmem n0 (σ.vars "t" + 1) :=
        fun hok => absurd (hok (σ.vars "t") (by omega)) (by omega)
      run_vcg
      all_goals (simp_all)
      all_goals omega
  have hrange : Spec B (fun σ => σ.vars "L" = L ∧ σ.vars "n" = n0 ∧
      σ.vars "valid" = v0 ∧ (σ.arrs "MEM").length = L ∧
      (σ.arrs "OFF").getD (σ.vars "m") 0 = L ∧
      (∀ t < L, (σ.arrs "MEM").getD t 0 = fmem t))
      (.seq (.assign "t" (.lit 0)) (.while (.lt (V "t") (V "L"))
        (.seq (failUnless (.lt (.get "MEM" (V "t")) (V "n"))) (bump "t"))))
      (fun _ σ' => σ'.vars "t" = L ∧
        (MembersOkG fmem n0 L → σ'.vars "valid" = v0) ∧
        (¬ MembersOkG fmem n0 L → σ'.vars "valid" = 0))
      ((14 + 4) * L + 6) := by
    refine ((Spec.forRangeZero (B := B) "t" "L"
      (fun σ => σ.vars "L" = L ∧ σ.vars "t" ≤ L ∧ σ.vars "n" = n0 ∧ (σ.arrs "MEM").length = L ∧
        (σ.arrs "OFF").getD (σ.vars "m") 0 = L ∧
        (∀ t < L, (σ.arrs "MEM").getD t 0 = fmem t) ∧
        (MembersOkG fmem n0 (σ.vars "t") → σ.vars "valid" = v0) ∧
        (¬ MembersOkG fmem n0 (σ.vars "t") → σ.vars "valid" = 0))
      L 14 hLB (fun _ h => h.2.1) (fun σ h => h.1) hbody).pre ?_).post ?_
    · intro σ hσ
      obtain ⟨hLL, hn, hval, hlen, hoffm, hmem⟩ := hσ
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | (simp_all [Env.setVar]; done) | (intro hn; exact absurd (MembersOkG.zero fmem) hn)
    · intro σ σ' hσ hq
      obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, ht⟩ := hq
      exact ⟨ht, by rw [← ht] at *; exact h6, by rw [← ht] at *; exact h7⟩
  have hassign : Spec B (fun σ => σ.vars "n" = n0 ∧ σ.vars "valid" = v0 ∧
      (σ.arrs "MEM").length = L ∧ σ.vars "m" < (σ.arrs "OFF").length ∧
      σ.vars "m" + 1 < B ∧
      (σ.arrs "OFF").getD (σ.vars "m") 0 = L ∧
      (∀ t < L, (σ.arrs "MEM").getD t 0 = fmem t))
      (.assign "L" (.get "OFF" (V "m")))
      (fun σ σ' => σ'.vars "L" = (σ.arrs "OFF").getD (σ.vars "m") 0 ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "valid" = σ.vars "valid" ∧
        σ'.arrs "MEM" = σ.arrs "MEM" ∧ σ'.arrs "OFF" = σ.arrs "OFF" ∧ σ'.vars "m" = σ.vars "m")
      3 := by
    intro σ hσ
    obtain ⟨-, -, -, hmOFF, hmB', hL, -⟩ := hσ
    have hLB' : (σ.arrs "OFF").getD (σ.vars "m") 0 < B := by omega
    have hmB : σ.vars "m" < B := by omega
    have hgetElem : (σ.arrs "OFF")[σ.vars "m"] = (σ.arrs "OFF").getD (σ.vars "m") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmOFF]
    have hev : (Expr.get "OFF" (V "m")).evalB B σ = some ((σ.arrs "OFF").getD (σ.vars "m") 0) := by
      have h1 : (V "m" : Expr).evalB B σ = some (σ.vars "m") := by
        show fit B (σ.vars "m") = some (σ.vars "m")
        rw [fit_eq_some]; exact ⟨rfl, hmB⟩
      unfold Expr.evalB
      rw [h1, Option.bind_some, List.getElem?_eq_getElem hmOFF, Option.bind_some, hgetElem]
      rw [fit_eq_some]; exact ⟨rfl, hLB'⟩
    exact ⟨σ.setVar "L" ((σ.arrs "OFF").getD (σ.vars "m") 0),
      Run.assign hev, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine (Spec.seq hassign hrange ?_ ?_).mono (by omega)
  · intro σ σ' hσ hmid
    obtain ⟨hn, hval, hlen, hmOFF, hmB', hoffm, hmem⟩ := hσ
    obtain ⟨hL, hn', hval', hmemeq, hoffeq, hmeq⟩ := hmid
    refine ⟨hL.trans hoffm, hn'.trans hn, hval'.trans hval, ?_, ?_, ?_⟩
    · rw [hmemeq]; exact hlen
    · rw [hoffeq, hmeq]; exact hoffm
    · intro t ht; rw [hmemeq]; exact hmem t ht
  · intro σ σ' σ'' hσ hmid hpost
    exact hpost

/-- Turn a "sticky" conjunction (holds `v0` if `C`, `0` otherwise) into an `ite`. Every one of
`validate`'s five checks has exactly this shape, so chaining them becomes chaining `ite`s. -/
theorem eq_ite_of_imp {C : Prop} [Decidable C] {v0 v' : ℕ} (hg : C → v' = v0) (hb : ¬ C → v' = 0) :
    v' = if C then v0 else 0 := by split_ifs with h; exacts [hg h, hb h]

/-! ## Members sorted within their own block

`checkOffsets`/`checkMembers` accept any CSR-shaped array whose offsets are nondecreasing and
whose members are below `n` — strictly weaker than what an actual `csrWord P k` looks like:
`csrWord`'s own member blocks are always built from `Instance.members`, which filters
`List.finRange` in ascending order, so they are always strictly increasing (in particular,
duplicate-free). A raw array with a repeated or out-of-order member inside one block can pass
both existing checks without being any admissible instance's `csrWord`. `checkSorted`, already
wired into `validate`, closes that gap: `"valid"` clears to `0` the first time two
consecutive members of the *same* block fail to be increasing. It scans the whole member array
once, with a second pointer walking the row — the shape of
`Lax808846Proofs.Reasoning.Lib.ownerScan_spec`'s combinator (not literally reused, since this
turn also threads a sticky `"valid"` flag rather than reading a value into a scalar). The
array-index reads it performs (`OFF[u]`, `OFF[u + 1]`) are guarded by `"u" < "m"` so the
command is well-defined on *every* tape, whether or not the offsets it is checking are
actually monotone; the guard is unreachable whenever they are, by `OffsetsOkG`. -/

/-- `s` and `s + 1` fall inside the same one of the first `nb` blocks. -/
def SameBlockG (foff : ℕ → ℕ) (nb s : ℕ) : Prop :=
  ∃ jj < nb, foff jj ≤ s ∧ s + 1 < foff (jj + 1)

/-- Every adjacent pair of members, among positions with successor below `t`, that falls in
the same one of the first `nb` blocks, is strictly increasing. Indexed one past the last
*checked* pair (`s + 1 < t`, not `s < t`) so that it lines up with the scan's own pointer:
right after the pointer has moved from `s + 1` on to `s + 2`, exactly the pair `(s, s + 1)`
has just been checked. -/
def SortedOkG (foff fmem : ℕ → ℕ) (nb t : ℕ) : Prop :=
  ∀ s, s + 1 < t → SameBlockG foff nb s → fmem s < fmem (s + 1)

theorem SortedOkG.zero {nb : ℕ} : SortedOkG foff fmem nb 0 := fun _ hs _ => absurd hs (by omega)

/-- **Adjacent strictness extends to full strict monotonicity within one block.** `SortedOkG`
only asserts `fmem s < fmem (s + 1)` for adjacent positions; chaining that across every step
from `s1` up to `s2` (all still inside block `jj`, all still below `t`) gives strict
monotonicity between *any* two positions of the block, not just neighbours. -/
theorem SortedOkG.strictMono_of_sameBlock {foff fmem : ℕ → ℕ} {nb t jj s1 s2 : ℕ}
    (h : SortedOkG foff fmem nb t) (hjj : jj < nb)
    (hlo : foff jj ≤ s1) (hhi : s2 < foff (jj + 1)) (hs2t : s2 < t) (hlt : s1 < s2) :
    fmem s1 < fmem s2 := by
  induction s2 with
  | zero => omega
  | succ s2 ih =>
    rcases Nat.lt_or_ge s1 s2 with h1 | h1
    · have hprev : fmem s2 < fmem (s2 + 1) := h s2 (by omega) ⟨jj, hjj, by omega, by omega⟩
      have hmid := ih (by omega) (by omega) h1
      omega
    · have heq : s1 = s2 := by omega
      subst heq
      exact h s1 (by omega) ⟨jj, hjj, by omega, by omega⟩

/-- **A block's members are pairwise distinct.** The injectivity `decodeInstance`'s member
count needs: two positions of the same block mapping to the same value would force one to be
strictly less than the other (via `strictMono_of_sameBlock`) and also the reverse, absurd. -/
theorem SortedOkG.injOn_sameBlock {foff fmem : ℕ → ℕ} {nb t jj : ℕ}
    (h : SortedOkG foff fmem nb t) (hjj : jj < nb) (hhi : foff (jj + 1) ≤ t) :
    Set.InjOn fmem (Set.Ico (foff jj) (foff (jj + 1))) := by
  intro s1 hs1 s2 hs2 heq
  simp only [Set.mem_Ico] at hs1 hs2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := SortedOkG.strictMono_of_sameBlock h hjj hs1.1 hs2.2 (by omega) hlt
    omega
  · have := SortedOkG.strictMono_of_sameBlock h hjj hs2.1 hs1.2 (by omega) hgt
    omega

/-- **No other block can also witness the position just before a block's own start.** The
position `p - 1` (`p` a block start, `p ≥ 1`) cannot fall inside any block among the first
`nb`: a block strictly before `u` ends at or before `p`, and a block at or after `u` starts at
or after `p`. This is what makes the scan's "skip the comparison at a block's first slot"
choice exactly right, not just a convenient default. -/
theorem not_sameBlockG_pred_of_start {nb u p : ℕ} (h : OffsetsOkG foff nb) (hu : u < nb)
    (hp : foff u = p) (hp1 : 1 ≤ p) : ¬ SameBlockG foff nb (p - 1) := by
  rintro ⟨jj, hjnb, hjlo, hjhi⟩
  rcases Nat.lt_or_ge jj u with hjlt | hjge
  · have hm := OffsetsOkG.mono foff h (show jj + 1 ≤ u by omega) (show u ≤ nb by omega)
    omega
  · have hm := OffsetsOkG.mono foff h (show u ≤ jj by omega) (show jj ≤ nb by omega)
    omega

/-- The scan's own loop invariant: the array-content facts, both pointers in range, the
current member owned by `"u"`'s row, `"p"` tracking the previous member of the same block
(or the current slot being a block's own first), and the sticky `"valid"` pair. -/
def SortedInv (m0 v0 : ℕ) (foff fmem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
    (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
    (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
    σ.vars "j" ≤ foff m0 ∧ σ.vars "u" ≤ m0 ∧ foff (σ.vars "u") ≤ σ.vars "j" ∧
    (σ.vars "j" = foff (σ.vars "u") ∨ σ.vars "p" = fmem (σ.vars "j" - 1)) ∧
    (SortedOkG foff fmem m0 (σ.vars "j") → σ.vars "valid" = v0) ∧
    (¬ SortedOkG foff fmem m0 (σ.vars "j") → σ.vars "valid" = 0)

/-- **The turn.** Either it processes the current member (comparing against `"p"` unless at a
block's own first slot) and advances `"j"`, or it advances the owner `"u"` past a finished
row. The `"u" < "m"` guard is unreachable here (`hjlt` plus the invariant forces it), so the
proof never has to reason about its `else` branch's behavior. -/
theorem sortedBody_spec {B m0 v0 : ℕ} (foff fmem : ℕ → ℕ) (hB : 1 < B)
    (hOff : OffsetsOkG foff m0) (hOFFb : ∀ i ≤ m0, foff i + 1 < B) (hm0B : m0 + 1 < B)
    (hMEMb : ∀ t < foff m0, fmem t + 1 < B) :
    Spec B (fun σ => SortedInv m0 v0 foff fmem σ ∧ σ.vars "j" < foff m0) sortedBody
      (fun σ σ' => SortedInv m0 v0 foff fmem σ' ∧
        σ.vars "j" ≤ σ'.vars "j" ∧ σ.vars "u" ≤ σ'.vars "u" ∧
        (σ.vars "j" < σ'.vars "j" ∨ σ.vars "u" < σ'.vars "u") ∧
        σ'.vars "j" - σ.vars "j" ≤ 1 ∧ σ'.vars "u" - σ.vars "u" ≤ 1)
      30 := by
  intro σ ⟨hI, hjlt⟩
  unfold SortedInv at hI
  obtain ⟨hL, hm, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr, hj, hu, hlo, hprev, hgood, hbad⟩ := hI
  have huM : σ.vars "u" < m0 := by
    rcases Nat.lt_or_ge (σ.vars "u") m0 with h | h
    · exact h
    · exfalso
      have heq : σ.vars "u" = m0 := by omega
      rw [heq] at hlo
      omega
  have hevU : (V "u" : Expr).evalB B σ = some (σ.vars "u") := evalB_var (by omega)
  have hevM : (V "m" : Expr).evalB B σ = some (σ.vars "m") := evalB_var (by omega)
  have hcondUM : (Cond.lt (V "u") (V "m")).evalB B σ = some true := by
    rw [evalB_condLt hevU hevM, hm, decide_eq_true (by omega : σ.vars "u" < m0)]
  have hu1m : σ.vars "u" + 1 ≤ m0 := by omega
  have huOFFlen : σ.vars "u" < (σ.arrs "OFF").length := by rw [hOFFlen]; omega
  have hu1OFFlen : σ.vars "u" + 1 < (σ.arrs "OFF").length := by rw [hOFFlen]; omega
  have hOFFu1 : (σ.arrs "OFF").getD (σ.vars "u" + 1) 0 = foff (σ.vars "u" + 1) := hOFFcorr _ hu1m
  have hOFFu : (σ.arrs "OFF").getD (σ.vars "u") 0 = foff (σ.vars "u") := hOFFcorr _ (by omega)
  have hOFFu1B : foff (σ.vars "u" + 1) < B := by have := hOFFb (σ.vars "u" + 1) hu1m; omega
  have hOFFuB : foff (σ.vars "u") < B := by have := hOFFb (σ.vars "u") (by omega); omega
  have hgetElemU1 : (σ.arrs "OFF")[σ.vars "u" + 1] = (σ.arrs "OFF").getD (σ.vars "u" + 1) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu1OFFlen]
  have hgetElemU : (σ.arrs "OFF")[σ.vars "u"] = (σ.arrs "OFF").getD (σ.vars "u") 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem huOFFlen]
  have hevAddU : (Expr.bin .add (V "u") (.lit 1)).evalB B σ = some (σ.vars "u" + 1) := by
    simp only [evalB_bin_iff]
    exact ⟨σ.vars "u", 1, hevU, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
  have hget?U1 : (σ.arrs "OFF")[σ.vars "u" + 1]? = some (foff (σ.vars "u" + 1)) := by
    rw [List.getElem?_eq_getElem hu1OFFlen, hgetElemU1, hOFFu1]
  have hevOFFu1 : (Expr.get "OFF" (.bin .add (V "u") (.lit 1))).evalB B σ =
      some (foff (σ.vars "u" + 1)) := evalB_get hevAddU hget?U1 hOFFu1B
  have hget?U : (σ.arrs "OFF")[σ.vars "u"]? = some (foff (σ.vars "u")) := by
    rw [List.getElem?_eq_getElem huOFFlen, hgetElemU, hOFFu]
  have hevOFFu : (Expr.get "OFF" (V "u")).evalB B σ = some (foff (σ.vars "u")) :=
    evalB_get hevU hget?U hOFFuB
  have hfoffm0B : foff m0 < B := by have := hOFFb m0 le_rfl; omega
  have hevJ : (V "j" : Expr).evalB B σ = some (σ.vars "j") := evalB_var (by omega)
  by_cases hcaseA : σ.vars "j" < foff (σ.vars "u" + 1)
  · -- Row-interior: process the slot
    have hcondJ : (Cond.lt (V "j") (.get "OFF" (.bin .add (V "u") (.lit 1)))).evalB B σ =
        some true := by rw [evalB_condLt hevJ hevOFFu1, decide_eq_true hcaseA]
    have hjMEMlen : σ.vars "j" < (σ.arrs "MEM").length := by rw [hMEMlen]; exact hjlt
    have hMEMj : (σ.arrs "MEM").getD (σ.vars "j") 0 = fmem (σ.vars "j") := hMEMcorr _ hjlt
    have hfmemjB : fmem (σ.vars "j") < B := by have := hMEMb (σ.vars "j") hjlt; omega
    have hgetElemJ : (σ.arrs "MEM")[σ.vars "j"] = (σ.arrs "MEM").getD (σ.vars "j") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjMEMlen]
    have hget?J : (σ.arrs "MEM")[σ.vars "j"]? = some (fmem (σ.vars "j")) := by
      rw [List.getElem?_eq_getElem hjMEMlen, hgetElemJ, hMEMj]
    have hevMEMj : (Expr.get "MEM" (V "j")).evalB B σ = some (fmem (σ.vars "j")) :=
      evalB_get hevJ hget?J hfmemjB
    -- shared tail: p := MEM[j]; bump j — from whatever state the inner ite leaves us in
    have hevAddJ : (Expr.bin .add (V "j") (.lit 1)).evalB B
        (σ.setVar "p" (fmem (σ.vars "j"))) = some (σ.vars "j" + 1) := by
      simp only [evalB_bin_iff]
      refine ⟨σ.vars "j", 1, ?_, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
      have hjset : (σ.setVar "p" (fmem (σ.vars "j"))).vars "j" = σ.vars "j" := by
        simp [Env.setVar]
      have h := evalB_var (B := B) (σ := σ.setVar "p" (fmem (σ.vars "j"))) (x := "j")
        (show (σ.setVar "p" (fmem (σ.vars "j"))).vars "j" < B by rw [hjset]; omega)
      rwa [hjset] at h
    have hevMEMjP : (Expr.get "MEM" (V "j")).evalB B σ = some (fmem (σ.vars "j")) := hevMEMj
    have hrunTail : Run B (.seq (.assign "p" (.get "MEM" (V "j"))) (bump "j")) σ
        ((σ.setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1)) 7 :=
      ((Run.assign (x := "p") hevMEMjP).seq
        (Run.assign (x := "j") hevAddJ)).mono (by simp only [Expr.size]; omega)
    set σ' := (σ.setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1) with hσ'def
    have hσ'j : σ'.vars "j" = σ.vars "j" + 1 := by simp [hσ'def, Env.setVar]
    have hσ'u : σ'.vars "u" = σ.vars "u" := by simp [hσ'def, Env.setVar]
    have hσ'p : σ'.vars "p" = fmem (σ.vars "j") := by simp [hσ'def, Env.setVar]
    have hσ'OFF : σ'.arrs "OFF" = σ.arrs "OFF" := by simp [hσ'def, Env.setVar]
    have hσ'MEM : σ'.arrs "MEM" = σ.arrs "MEM" := by simp [hσ'def, Env.setVar]
    have hσ'L : σ'.vars "L" = σ.vars "L" := by simp [hσ'def, Env.setVar]
    have hσ'm : σ'.vars "m" = σ.vars "m" := by simp [hσ'def, Env.setVar]
    have hσ'valid : σ'.vars "valid" = σ.vars "valid" := by simp [hσ'def, Env.setVar]
    have hjle : σ.vars "j" + 1 ≤ foff m0 := by
      have := OffsetsOkG.mono foff hOff (show σ.vars "u" + 1 ≤ m0 by omega) (le_refl m0)
      omega
    by_cases hcaseA1 : σ.vars "j" = foff (σ.vars "u")
    · -- block start: no comparison, `"valid"` unchanged
      have hcondEq : (Cond.eq (V "j") (.get "OFF" (V "u"))).evalB B σ = some true := by
        rw [evalB_condEq hevJ hevOFFu, hcaseA1]; simp
      have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
          (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ σ
          (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size + 1) :=
        Run.ite_true hcondEq (Run.skip (B := B) (σ := σ))
      have hrunFull : Run B sortedBody σ σ' 30 := by
        unfold sortedBody
        exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail))).mono (by
          simp only [Cond.size, Expr.size]; omega)
      have hnotSame : σ.vars "j" = 0 ∨ ¬ SameBlockG foff m0 (σ.vars "j" - 1) := by
        rcases Nat.eq_zero_or_pos (σ.vars "j") with h0 | hpos
        · exact Or.inl h0
        · exact Or.inr (not_sameBlockG_pred_of_start foff hOff huM hcaseA1.symm (by omega))
      have hfwd : SortedOkG foff fmem m0 (σ.vars "j") → SortedOkG foff fmem m0 (σ.vars "j" + 1) := by
        intro hsorted s hs1 hsb
        rcases Nat.lt_or_ge (s + 1) (σ.vars "j") with hlt | hge
        · exact hsorted s hlt hsb
        · exfalso
          rcases hnotSame with hj0 | hns
          · omega
          · have heq : s = σ.vars "j" - 1 := by omega
            rw [heq] at hsb; exact hns hsb
      have hbwd : SortedOkG foff fmem m0 (σ.vars "j" + 1) → SortedOkG foff fmem m0 (σ.vars "j") :=
        fun h s hs1 hsb => h s (by omega) hsb
      have hSI' : SortedInv m0 v0 foff fmem σ' := by
        unfold SortedInv
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hσ'L]; exact hL
        · rw [hσ'm]; exact hm
        · rw [hσ'OFF]; exact hOFFlen
        · rw [hσ'OFF]; exact hOFFcorr
        · rw [hσ'MEM]; exact hMEMlen
        · rw [hσ'MEM]; exact hMEMcorr
        · rw [hσ'j]; exact hjle
        · rw [hσ'u]; exact hu
        · rw [hσ'u, hσ'j]; omega
        · right; rw [hσ'p, hσ'j]; congr 1
        · rw [hσ'j, hσ'valid]; intro hsg; exact hgood (hbwd hsg)
        · rw [hσ'j, hσ'valid]; intro hsb; exact hbad (fun hcon => hsb (hfwd hcon))
      exact ⟨σ', hrunFull, hSI', by rw [hσ'j]; omega, le_of_eq hσ'u.symm,
        Or.inl (by rw [hσ'j]; omega), by rw [hσ'j]; omega, by rw [hσ'u]; omega⟩
    · -- not a block start: compare against "p"
      have hSameTrue : SameBlockG foff m0 (σ.vars "j" - 1) := by
        refine ⟨σ.vars "u", huM, by omega, ?_⟩
        have heq : σ.vars "j" - 1 + 1 = σ.vars "j" := by omega
        rw [heq]; exact hcaseA
      have hprevEq : σ.vars "p" = fmem (σ.vars "j" - 1) := by
        rcases hprev with hL' | hR'
        · exact absurd hL' hcaseA1
        · exact hR'
      have hcondEqF : (Cond.eq (V "j") (.get "OFF" (V "u"))).evalB B σ = some false := by
        rw [evalB_condEq hevJ hevOFFu]; simp [hcaseA1]
      have hpB : σ.vars "p" < B := by
        rw [hprevEq]; have := hMEMb (σ.vars "j" - 1) (by omega); omega
      by_cases hcmp : σ.vars "p" < fmem (σ.vars "j")
      · -- comparison passes: `"valid"` unchanged
        have hevP : (V "p" : Expr).evalB B σ = some (σ.vars "p") := evalB_var (by omega)
        have hcondCmp : (Cond.lt (V "p") (.get "MEM" (V "j"))).evalB B σ = some true := by
          rw [evalB_condLt hevP hevMEMj, decide_eq_true hcmp]
        have hrunFail : Run B (failUnless (.lt (V "p") (.get "MEM" (V "j")))) σ σ
            (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + 1) :=
          Run.ite_true hcondCmp (Run.skip (B := B) (σ := σ))
        have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
            (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ σ
            (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size +
              (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + 1)) :=
          Run.ite_false hcondEqF hrunFail
        have hrunFull : Run B sortedBody σ σ' 30 := by
          unfold sortedBody
          exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail))).mono (by
            simp only [Cond.size, Expr.size]; omega)
        have hfwd : SortedOkG foff fmem m0 (σ.vars "j") → SortedOkG foff fmem m0 (σ.vars "j" + 1) := by
          intro hsorted s hs1 hsb
          rcases Nat.lt_or_ge (s + 1) (σ.vars "j") with hlt | hge
          · exact hsorted s hlt hsb
          · have heq1 : s = σ.vars "j" - 1 := by omega
            have heq2 : s + 1 = σ.vars "j" := by omega
            rw [← heq1] at hprevEq
            rw [heq2, ← hprevEq]
            exact hcmp
        have hbwd : SortedOkG foff fmem m0 (σ.vars "j" + 1) → SortedOkG foff fmem m0 (σ.vars "j") :=
          fun h s hs1 hsb => h s (by omega) hsb
        have hSI' : SortedInv m0 v0 foff fmem σ' := by
          unfold SortedInv
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hσ'L]; exact hL
          · rw [hσ'm]; exact hm
          · rw [hσ'OFF]; exact hOFFlen
          · rw [hσ'OFF]; exact hOFFcorr
          · rw [hσ'MEM]; exact hMEMlen
          · rw [hσ'MEM]; exact hMEMcorr
          · rw [hσ'j]; exact hjle
          · rw [hσ'u]; exact hu
          · rw [hσ'u, hσ'j]; omega
          · right; rw [hσ'p, hσ'j]; congr 1
          · rw [hσ'j, hσ'valid]; intro hsg; exact hgood (hbwd hsg)
          · rw [hσ'j, hσ'valid]; intro hsb; exact hbad (fun hcon => hsb (hfwd hcon))
        exact ⟨σ', hrunFull, hSI', by rw [hσ'j]; omega, le_of_eq hσ'u.symm,
          Or.inl (by rw [hσ'j]; omega), by rw [hσ'j]; omega, by rw [hσ'u]; omega⟩
      · -- comparison fails: `"valid"` clears to 0
        have hevP : (V "p" : Expr).evalB B σ = some (σ.vars "p") := evalB_var (by omega)
        have hcondCmp : (Cond.lt (V "p") (.get "MEM" (V "j"))).evalB B σ = some false := by
          rw [evalB_condLt hevP hevMEMj, decide_eq_false hcmp]
        have hev0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
        have hrunFail : Run B (failUnless (.lt (V "p") (.get "MEM" (V "j")))) σ
            (σ.setVar "valid" 0) (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + (1 + 1)) :=
          Run.ite_false hcondCmp (Run.assign (x := "valid") hev0)
        have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
            (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ (σ.setVar "valid" 0)
            (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size +
              (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + (1 + 1))) :=
          Run.ite_false hcondEqF hrunFail
        have hevMEMj' : (Expr.get "MEM" (V "j")).evalB B (σ.setVar "valid" 0) =
            some (fmem (σ.vars "j")) := by simpa [Env.setVar] using hevMEMj
        have hevAddJ' : (Expr.bin .add (V "j") (.lit 1)).evalB B
            ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))) = some (σ.vars "j" + 1) := by
          simp only [evalB_bin_iff]
          refine ⟨σ.vars "j", 1, ?_, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
          have hjset : ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).vars "j" =
              σ.vars "j" := by simp [Env.setVar]
          have h := evalB_var (B := B) (σ := (σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j")))
            (x := "j")
            (show ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).vars "j" < B by
              rw [hjset]; omega)
          rwa [hjset] at h
        have hrunTail' : Run B (.seq (.assign "p" (.get "MEM" (V "j"))) (bump "j"))
            (σ.setVar "valid" 0)
            (((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1))
            7 :=
          ((Run.assign (x := "p") hevMEMj').seq
            (Run.assign (x := "j") hevAddJ')).mono (by simp only [Expr.size]; omega)
        set σ'' := ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).setVar "j"
          (σ.vars "j" + 1) with hσ''def
        have hσ''j : σ''.vars "j" = σ.vars "j" + 1 := by simp [hσ''def, Env.setVar]
        have hσ''u : σ''.vars "u" = σ.vars "u" := by simp [hσ''def, Env.setVar]
        have hσ''p : σ''.vars "p" = fmem (σ.vars "j") := by simp [hσ''def, Env.setVar]
        have hσ''OFF : σ''.arrs "OFF" = σ.arrs "OFF" := by simp [hσ''def, Env.setVar]
        have hσ''MEM : σ''.arrs "MEM" = σ.arrs "MEM" := by simp [hσ''def, Env.setVar]
        have hσ''L : σ''.vars "L" = σ.vars "L" := by simp [hσ''def, Env.setVar]
        have hσ''m : σ''.vars "m" = σ.vars "m" := by simp [hσ''def, Env.setVar]
        have hσ''valid : σ''.vars "valid" = 0 := by simp [hσ''def, Env.setVar]
        have hrunFull : Run B sortedBody σ σ'' 30 := by
          unfold sortedBody
          exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail'))).mono (by
            simp only [Cond.size, Expr.size]; omega)
        have hnotSorted : ¬ SortedOkG foff fmem m0 (σ.vars "j" + 1) := by
          intro hsorted
          have hpair := hsorted (σ.vars "j" - 1) (by omega) hSameTrue
          rw [hprevEq] at hcmp
          have heq : σ.vars "j" - 1 + 1 = σ.vars "j" := by omega
          rw [heq] at hpair
          exact hcmp hpair
        have hSI'' : SortedInv m0 v0 foff fmem σ'' := by
          unfold SortedInv
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hσ''L]; exact hL
          · rw [hσ''m]; exact hm
          · rw [hσ''OFF]; exact hOFFlen
          · rw [hσ''OFF]; exact hOFFcorr
          · rw [hσ''MEM]; exact hMEMlen
          · rw [hσ''MEM]; exact hMEMcorr
          · rw [hσ''j]; exact hjle
          · rw [hσ''u]; exact hu
          · rw [hσ''u, hσ''j]; omega
          · right; rw [hσ''p, hσ''j]; congr 1
          · rw [hσ''j]; intro hsg; exact absurd hsg hnotSorted
          · intro _; exact hσ''valid
        exact ⟨σ'', hrunFull, hSI'', by rw [hσ''j]; omega, le_of_eq hσ''u.symm,
          Or.inl (by rw [hσ''j]; omega), by rw [hσ''j]; omega, by rw [hσ''u]; omega⟩
  · -- row end: advance the owner
    have hcondJF : (Cond.lt (V "j") (.get "OFF" (.bin .add (V "u") (.lit 1)))).evalB B σ =
        some false := by rw [evalB_condLt hevJ hevOFFu1, decide_eq_false hcaseA]
    have hrunBumpU := Run.assign (B := B) (σ := σ) (x := "u") hevAddU
    set σ' := σ.setVar "u" (σ.vars "u" + 1) with hσ'def
    have hσ'u : σ'.vars "u" = σ.vars "u" + 1 := by simp [hσ'def, Env.setVar]
    have hσ'j : σ'.vars "j" = σ.vars "j" := by simp [hσ'def, Env.setVar]
    have hσ'p : σ'.vars "p" = σ.vars "p" := by simp [hσ'def, Env.setVar]
    have hσ'OFF : σ'.arrs "OFF" = σ.arrs "OFF" := by simp [hσ'def, Env.setVar]
    have hσ'MEM : σ'.arrs "MEM" = σ.arrs "MEM" := by simp [hσ'def, Env.setVar]
    have hσ'L : σ'.vars "L" = σ.vars "L" := by simp [hσ'def, Env.setVar]
    have hσ'm : σ'.vars "m" = σ.vars "m" := by simp [hσ'def, Env.setVar]
    have hσ'valid : σ'.vars "valid" = σ.vars "valid" := by simp [hσ'def, Env.setVar]
    have hrunFull : Run B sortedBody σ σ' 30 := by
      unfold sortedBody
      exact (Run.ite_true hcondUM (Run.ite_false hcondJF hrunBumpU)).mono (by
        simp only [Cond.size, Expr.size]; omega)
    have hprevNew : σ'.vars "j" = foff (σ'.vars "u") ∨ σ'.vars "p" = fmem (σ'.vars "j" - 1) := by
      rw [hσ'j, hσ'u, hσ'p]
      rcases hprev with hL' | hR'
      · left
        have hstep : foff (σ.vars "u") ≤ foff (σ.vars "u" + 1) := hOff (σ.vars "u") huM
        omega
      · right; exact hR'
    have hSI' : SortedInv m0 v0 foff fmem σ' := by
      unfold SortedInv
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hprevNew, ?_, ?_⟩
      · rw [hσ'L]; exact hL
      · rw [hσ'm]; exact hm
      · rw [hσ'OFF]; exact hOFFlen
      · rw [hσ'OFF]; exact hOFFcorr
      · rw [hσ'MEM]; exact hMEMlen
      · rw [hσ'MEM]; exact hMEMcorr
      · rw [hσ'j]; exact hj
      · rw [hσ'u]; omega
      · rw [hσ'u, hσ'j]; omega
      · rw [hσ'j, hσ'valid]; exact hgood
      · rw [hσ'j, hσ'valid]; exact hbad
    exact ⟨σ', hrunFull, hSI', le_of_eq hσ'j.symm, by rw [hσ'u]; omega,
      Or.inr (by rw [hσ'u]; omega), by rw [hσ'j]; omega, by rw [hσ'u]; omega⟩

theorem checkSorted_spec_generic {B m0 v0 : ℕ} (foff fmem : ℕ → ℕ)
    (hB : 1 < B) (hOff : OffsetsOkG foff m0) (hoff0 : foff 0 = 0)
    (hOFFb : ∀ i ≤ m0, foff i + 1 < B) (hm0B : m0 + 1 < B)
    (hMEMb : ∀ t < foff m0, fmem t + 1 < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "valid" = v0 ∧
        (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
        (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      checkSorted
      (fun _ σ' => σ'.vars "j" = foff m0 ∧
        (SortedOkG foff fmem m0 (foff m0) → σ'.vars "valid" = v0) ∧
        (¬ SortedOkG foff fmem m0 (foff m0) → σ'.vars "valid" = 0))
      (34 * foff m0 + 34 * m0 + 20) := by
  unfold checkSorted
  have hassignL : Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "valid" = v0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      (.assign "L" (.get "OFF" (V "m")))
      (fun σ σ' => σ'.vars "L" = foff m0 ∧
        σ'.vars "m" = σ.vars "m" ∧ σ'.vars "valid" = σ.vars "valid" ∧
        σ'.arrs "OFF" = σ.arrs "OFF" ∧ σ'.arrs "MEM" = σ.arrs "MEM")
      3 := by
    intro σ ⟨hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr⟩
    have hmOFF : σ.vars "m" < (σ.arrs "OFF").length := by rw [hOFFlen, hm]; omega
    have hmB : σ.vars "m" < B := by have := hOFFb m0 le_rfl; omega
    have hval : (σ.arrs "OFF").getD (σ.vars "m") 0 = foff m0 := by
      rw [hOFFcorr (σ.vars "m") (by omega), hm]
    have hLB' : (σ.arrs "OFF").getD (σ.vars "m") 0 < B := by
      have := hOFFb m0 le_rfl; omega
    have hgetElem : (σ.arrs "OFF")[σ.vars "m"] = (σ.arrs "OFF").getD (σ.vars "m") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmOFF]
    have hev : (Expr.get "OFF" (V "m")).evalB B σ = some ((σ.arrs "OFF").getD (σ.vars "m") 0) := by
      have h1 : (V "m" : Expr).evalB B σ = some (σ.vars "m") := by
        show fit B (σ.vars "m") = some (σ.vars "m")
        rw [fit_eq_some]; exact ⟨rfl, hmB⟩
      unfold Expr.evalB
      rw [h1, Option.bind_some, List.getElem?_eq_getElem hmOFF, Option.bind_some, hgetElem]
      rw [fit_eq_some]; exact ⟨rfl, hLB'⟩
    refine ⟨σ.setVar "L" ((σ.arrs "OFF").getD (σ.vars "m") 0), Run.assign hev, ?_, ?_, ?_, ?_, ?_⟩
    · exact hval
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]
  have hassignJ : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = v0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      (.assign "j" (.lit 0))
      (fun σ σ' => σ'.vars "j" = 0 ∧ σ'.vars "L" = σ.vars "L" ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.vars "valid" = σ.vars "valid" ∧
        σ'.arrs "OFF" = σ.arrs "OFF" ∧ σ'.arrs "MEM" = σ.arrs "MEM")
      2 := by
    intro σ hσ
    have hev : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    refine ⟨σ.setVar "j" 0, Run.assign hev, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar]
  have hassignU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "j" = 0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = v0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      (.assign "u" (.lit 0))
      (fun _ σ' => SortedInv m0 v0 foff fmem σ')
      2 := by
    intro σ ⟨hL, hj, hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr⟩
    have hev : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    refine ⟨σ.setVar "u" 0, Run.assign hev, ?_⟩
    unfold SortedInv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar, hL]
    · simp [Env.setVar, hm]
    · simp [Env.setVar, hOFFlen]
    · simp only [Env.setVar]; exact hOFFcorr
    · simp [Env.setVar, hMEMlen]
    · simp only [Env.setVar]; exact hMEMcorr
    · simp [Env.setVar, hj]
    · simp [Env.setVar]
    · simp [Env.setVar, hj, hoff0]
    · left; simp [Env.setVar, hj, hoff0]
    · intro _; simp [Env.setVar, hvalid]
    · intro h
      simp only [Env.setVar, hj] at h
      exact absurd (SortedOkG.zero foff fmem) h
  have hloop : Spec B (SortedInv m0 v0 foff fmem)
      (.while (.lt (V "j") (V "L")) sortedBody)
      (fun _ σ' => SortedInv m0 v0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (34 * foff m0 + 34 * m0 + 4) := by
    have hnsB : foff m0 < B := by have := hOFFb m0 le_rfl; omega
    refine Lax808846Proofs.Reasoning.Lib.Csr.ownerScan_spec B (34 * foff m0 + 34 * m0 + 4) m0
      (foff m0) 30 30 "j" "L" "u" sortedBody (SortedInv m0 v0 foff fmem) hnsB
      (fun σ hI => ⟨hI.1, hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.1⟩)
      (fun σ hI hjlt => ?_) (fun σ hσ => hσ) (fun σ hσ => by omega)
    obtain ⟨σ', hrun, hI', hjmono, humono, hprog, hjd, hud⟩ :=
      (sortedBody_spec foff fmem hB hOff hOFFb hm0B hMEMb).run ⟨hI, hjlt⟩
    exact ⟨σ', 30, hrun, hI', hjmono, humono, hprog, by omega⟩
  have hloopU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "j" = 0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = v0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      (.seq (.assign "u" (.lit 0)) (.while (.lt (V "j") (V "L")) sortedBody))
      (fun _ σ' => SortedInv m0 v0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (2 + (34 * foff m0 + 34 * m0 + 4)) :=
    Spec.seq hassignU hloop (fun _ _ _ hQ => hQ) (fun _ _ _ _ _ hqloop => hqloop)
  have hloopJU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = v0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t))
      (.seq (.assign "j" (.lit 0))
        (.seq (.assign "u" (.lit 0)) (.while (.lt (V "j") (V "L")) sortedBody)))
      (fun _ σ' => SortedInv m0 v0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (2 + (2 + (34 * foff m0 + 34 * m0 + 4))) := by
    refine Spec.seq hassignJ hloopU ?_ ?_
    · intro σ σ' hσ hmid
      obtain ⟨hj', hL', hm', hvalid', hOFF', hMEM'⟩ := hmid
      obtain ⟨hL, hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr⟩ := hσ
      refine ⟨by rw [hL', hL], hj', by rw [hm', hm], by rw [hvalid', hvalid],
        by rw [hOFF']; exact hOFFlen, ?_, by rw [hMEM']; exact hMEMlen, ?_⟩
      · rw [hOFF']; exact hOFFcorr
      · rw [hMEM']; exact hMEMcorr
    · intro σ σ' σ'' hσ hmid hpost
      exact hpost
  refine (Spec.seq hassignL hloopJU ?_ ?_).mono ?_
  · intro σ σ' hσ hmid
    obtain ⟨hL, hm, hvalid, hOFF, hMEM⟩ := hmid
    obtain ⟨hm0, hv0, hOFFlen0, hOFFcorr0, hMEMlen0, hMEMcorr0⟩ := hσ
    refine ⟨by rw [hL], by rw [hm, hm0], by rw [hvalid, hv0], by rw [hOFF]; exact hOFFlen0, ?_,
      by rw [hMEM]; exact hMEMlen0, ?_⟩
    · rw [hOFF]; exact hOFFcorr0
    · rw [hMEM]; exact hMEMcorr0
  · intro σ σ' σ'' hσ hmid hpost
    obtain ⟨hI'', hj''⟩ := hpost
    unfold SortedInv at hI''
    rw [hj''] at hI''
    exact ⟨hj'', hI''.2.2.2.2.2.2.2.2.2.2.1, hI''.2.2.2.2.2.2.2.2.2.2.2⟩
  · omega

/-! ## `checkSorted` is safe regardless of whether the offsets are actually monotone

`checkSorted`'s only array reads (`OFF[u]`, `OFF[u + 1]`, `MEM[j]`) stay in bounds purely from
the outer loop's own guard `"j" < "L"` (with `"L" = OFF[m] = foff m0` unconditionally, by the
readback-correctness invariant `RC` already gives, whether or not `foff` is monotone) and the
inner guard `"u" < "m"` — neither needs `OffsetsOkG`. What *does* need `OffsetsOkG` is
`checkSorted_spec_generic`'s content characterization (which block a slot belongs to, tracked
via `"u"`, only lines up with `foff`'s own blocks when `foff` is monotone). This weaker
invariant drops that content tracking and keeps only what `validate_spec_generic` needs for the
case where an earlier check has already cleared `"valid"` to `0`: that `checkSorted` still
terminates within the same cost bound and leaves `"valid"` at `0` — `failUnless`'s only write is
`.assign "valid" (.lit 0)`, so once `"valid"` is `0` it can only ever be reassigned to `0`. The
one extra fact this needs that the OffsetsOkG-full version didn't is `"p" < B` at entry
(`"p"` is otherwise tracked implicitly via the fact that a block's own first slot is always
reached before any comparison reads it, which itself relies on `OffsetsOkG`/`foff 0 = 0`). -/

def SortedInvZero (B m0 : ℕ) (foff fmem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧ σ.vars "valid" = 0 ∧
    (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
    (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
    σ.vars "j" ≤ foff m0 ∧ σ.vars "u" ≤ m0 ∧ σ.vars "p" < B

theorem sortedBodyZero_spec {B m0 : ℕ} (foff fmem : ℕ → ℕ) (hB : 1 < B)
    (hOFFb : ∀ i ≤ m0, foff i + 1 < B) (hm0B : m0 + 1 < B)
    (hMEMb : ∀ t < foff m0, fmem t + 1 < B) :
    Spec B (fun σ => SortedInvZero B m0 foff fmem σ ∧ σ.vars "j" < foff m0) sortedBody
      (fun σ σ' => SortedInvZero B m0 foff fmem σ' ∧
        σ.vars "j" ≤ σ'.vars "j" ∧ σ.vars "u" ≤ σ'.vars "u" ∧
        (σ.vars "j" < σ'.vars "j" ∨ σ.vars "u" < σ'.vars "u") ∧
        σ'.vars "j" - σ.vars "j" ≤ 1 ∧ σ'.vars "u" - σ.vars "u" ≤ 1)
      30 := by
  intro σ ⟨hI, hjlt⟩
  unfold SortedInvZero at hI
  obtain ⟨hL, hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr, hj, hu, hpB⟩ := hI
  have hfoffm0B : foff m0 < B := by have := hOFFb m0 le_rfl; omega
  have hevU : (V "u" : Expr).evalB B σ = some (σ.vars "u") := evalB_var (by omega)
  have hevM : (V "m" : Expr).evalB B σ = some (σ.vars "m") := evalB_var (by omega)
  have hevJ : (V "j" : Expr).evalB B σ = some (σ.vars "j") := evalB_var (by omega)
  by_cases hum : σ.vars "u" < m0
  · have hcondUM : (Cond.lt (V "u") (V "m")).evalB B σ = some true := by
      rw [evalB_condLt hevU hevM, hm, decide_eq_true hum]
    have hu1m : σ.vars "u" + 1 ≤ m0 := by omega
    have huOFFlen : σ.vars "u" < (σ.arrs "OFF").length := by rw [hOFFlen]; omega
    have hu1OFFlen : σ.vars "u" + 1 < (σ.arrs "OFF").length := by rw [hOFFlen]; omega
    have hOFFu1 : (σ.arrs "OFF").getD (σ.vars "u" + 1) 0 = foff (σ.vars "u" + 1) := hOFFcorr _ hu1m
    have hOFFu : (σ.arrs "OFF").getD (σ.vars "u") 0 = foff (σ.vars "u") := hOFFcorr _ (by omega)
    have hOFFu1B : foff (σ.vars "u" + 1) < B := by have := hOFFb (σ.vars "u" + 1) hu1m; omega
    have hOFFuB : foff (σ.vars "u") < B := by have := hOFFb (σ.vars "u") (by omega); omega
    have hgetElemU1 : (σ.arrs "OFF")[σ.vars "u" + 1] = (σ.arrs "OFF").getD (σ.vars "u" + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu1OFFlen]
    have hgetElemU : (σ.arrs "OFF")[σ.vars "u"] = (σ.arrs "OFF").getD (σ.vars "u") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem huOFFlen]
    have hevAddU : (Expr.bin .add (V "u") (.lit 1)).evalB B σ = some (σ.vars "u" + 1) := by
      simp only [evalB_bin_iff]
      exact ⟨σ.vars "u", 1, hevU, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
    have hget?U1 : (σ.arrs "OFF")[σ.vars "u" + 1]? = some (foff (σ.vars "u" + 1)) := by
      rw [List.getElem?_eq_getElem hu1OFFlen, hgetElemU1, hOFFu1]
    have hevOFFu1 : (Expr.get "OFF" (.bin .add (V "u") (.lit 1))).evalB B σ =
        some (foff (σ.vars "u" + 1)) := evalB_get hevAddU hget?U1 hOFFu1B
    have hget?U : (σ.arrs "OFF")[σ.vars "u"]? = some (foff (σ.vars "u")) := by
      rw [List.getElem?_eq_getElem huOFFlen, hgetElemU, hOFFu]
    have hevOFFu : (Expr.get "OFF" (V "u")).evalB B σ = some (foff (σ.vars "u")) :=
      evalB_get hevU hget?U hOFFuB
    by_cases hcaseA : σ.vars "j" < foff (σ.vars "u" + 1)
    · have hcondJ : (Cond.lt (V "j") (.get "OFF" (.bin .add (V "u") (.lit 1)))).evalB B σ =
          some true := by rw [evalB_condLt hevJ hevOFFu1, decide_eq_true hcaseA]
      have hjMEMlen : σ.vars "j" < (σ.arrs "MEM").length := by rw [hMEMlen]; exact hjlt
      have hMEMj : (σ.arrs "MEM").getD (σ.vars "j") 0 = fmem (σ.vars "j") := hMEMcorr _ hjlt
      have hfmemjB : fmem (σ.vars "j") < B := by have := hMEMb (σ.vars "j") hjlt; omega
      have hgetElemJ : (σ.arrs "MEM")[σ.vars "j"] = (σ.arrs "MEM").getD (σ.vars "j") 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjMEMlen]
      have hget?J : (σ.arrs "MEM")[σ.vars "j"]? = some (fmem (σ.vars "j")) := by
        rw [List.getElem?_eq_getElem hjMEMlen, hgetElemJ, hMEMj]
      have hevMEMj : (Expr.get "MEM" (V "j")).evalB B σ = some (fmem (σ.vars "j")) :=
        evalB_get hevJ hget?J hfmemjB
      have hevAddJ : (Expr.bin .add (V "j") (.lit 1)).evalB B
          (σ.setVar "p" (fmem (σ.vars "j"))) = some (σ.vars "j" + 1) := by
        simp only [evalB_bin_iff]
        refine ⟨σ.vars "j", 1, ?_, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
        have hjset : (σ.setVar "p" (fmem (σ.vars "j"))).vars "j" = σ.vars "j" := by
          simp [Env.setVar]
        have h := evalB_var (B := B) (σ := σ.setVar "p" (fmem (σ.vars "j"))) (x := "j")
          (show (σ.setVar "p" (fmem (σ.vars "j"))).vars "j" < B by rw [hjset]; omega)
        rwa [hjset] at h
      have hrunTail : Run B (.seq (.assign "p" (.get "MEM" (V "j"))) (bump "j")) σ
          ((σ.setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1)) 7 :=
        ((Run.assign (x := "p") hevMEMj).seq
          (Run.assign (x := "j") hevAddJ)).mono (by simp only [Expr.size]; omega)
      set σ' := (σ.setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1) with hσ'def
      have hσ'j : σ'.vars "j" = σ.vars "j" + 1 := by simp [hσ'def, Env.setVar]
      have hσ'u : σ'.vars "u" = σ.vars "u" := by simp [hσ'def, Env.setVar]
      have hσ'p : σ'.vars "p" = fmem (σ.vars "j") := by simp [hσ'def, Env.setVar]
      have hσ'OFF : σ'.arrs "OFF" = σ.arrs "OFF" := by simp [hσ'def, Env.setVar]
      have hσ'MEM : σ'.arrs "MEM" = σ.arrs "MEM" := by simp [hσ'def, Env.setVar]
      have hσ'L : σ'.vars "L" = σ.vars "L" := by simp [hσ'def, Env.setVar]
      have hσ'm : σ'.vars "m" = σ.vars "m" := by simp [hσ'def, Env.setVar]
      have hσ'valid : σ'.vars "valid" = σ.vars "valid" := by simp [hσ'def, Env.setVar]
      have hjle : σ.vars "j" + 1 ≤ foff m0 := by omega
      have hσ'pB : σ'.vars "p" < B := by rw [hσ'p]; exact hfmemjB
      by_cases hcaseA1 : σ.vars "j" = foff (σ.vars "u")
      · have hcondEq : (Cond.eq (V "j") (.get "OFF" (V "u"))).evalB B σ = some true := by
          rw [evalB_condEq hevJ hevOFFu, hcaseA1]; simp
        have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
            (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ σ
            (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size + 1) :=
          Run.ite_true hcondEq (Run.skip (B := B) (σ := σ))
        have hrunFull : Run B sortedBody σ σ' 30 := by
          unfold sortedBody
          exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail))).mono (by
            simp only [Cond.size, Expr.size]; omega)
        refine ⟨σ', hrunFull, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          by rw [hσ'j]; omega, le_of_eq hσ'u.symm, Or.inl (by rw [hσ'j]; omega),
          by rw [hσ'j]; omega, by rw [hσ'u]; omega⟩
        · rw [hσ'L]; exact hL
        · rw [hσ'm]; exact hm
        · rw [hσ'valid]; exact hvalid
        · rw [hσ'OFF]; exact hOFFlen
        · rw [hσ'OFF]; exact hOFFcorr
        · rw [hσ'MEM]; exact hMEMlen
        · rw [hσ'MEM]; exact hMEMcorr
        · rw [hσ'j]; exact hjle
        · rw [hσ'u]; exact hu
        · exact hσ'pB
      · have hcondEqF : (Cond.eq (V "j") (.get "OFF" (V "u"))).evalB B σ = some false := by
          rw [evalB_condEq hevJ hevOFFu]; simp [hcaseA1]
        have hevP : (V "p" : Expr).evalB B σ = some (σ.vars "p") := evalB_var hpB
        by_cases hcmp : σ.vars "p" < fmem (σ.vars "j")
        · have hcondCmp : (Cond.lt (V "p") (.get "MEM" (V "j"))).evalB B σ = some true := by
            rw [evalB_condLt hevP hevMEMj, decide_eq_true hcmp]
          have hrunFail : Run B (failUnless (.lt (V "p") (.get "MEM" (V "j")))) σ σ
              (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + 1) :=
            Run.ite_true hcondCmp (Run.skip (B := B) (σ := σ))
          have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
              (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ σ
              (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size +
                (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + 1)) :=
            Run.ite_false hcondEqF hrunFail
          have hrunFull : Run B sortedBody σ σ' 30 := by
            unfold sortedBody
            exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail))).mono (by
              simp only [Cond.size, Expr.size]; omega)
          refine ⟨σ', hrunFull, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            by rw [hσ'j]; omega, le_of_eq hσ'u.symm, Or.inl (by rw [hσ'j]; omega),
            by rw [hσ'j]; omega, by rw [hσ'u]; omega⟩
          · rw [hσ'L]; exact hL
          · rw [hσ'm]; exact hm
          · rw [hσ'valid]; exact hvalid
          · rw [hσ'OFF]; exact hOFFlen
          · rw [hσ'OFF]; exact hOFFcorr
          · rw [hσ'MEM]; exact hMEMlen
          · rw [hσ'MEM]; exact hMEMcorr
          · rw [hσ'j]; exact hjle
          · rw [hσ'u]; exact hu
          · exact hσ'pB
        · have hcondCmp : (Cond.lt (V "p") (.get "MEM" (V "j"))).evalB B σ = some false := by
            rw [evalB_condLt hevP hevMEMj, decide_eq_false hcmp]
          have hev0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
          have hrunFail : Run B (failUnless (.lt (V "p") (.get "MEM" (V "j")))) σ
              (σ.setVar "valid" 0) (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + (1 + 1)) :=
            Run.ite_false hcondCmp (Run.assign (x := "valid") hev0)
          have hrunHead : Run B (.ite (Cond.eq (V "j") (.get "OFF" (V "u"))) Com.skip
              (failUnless (.lt (V "p") (.get "MEM" (V "j"))))) σ (σ.setVar "valid" 0)
              (1 + (Cond.eq (V "j") (.get "OFF" (V "u"))).size +
                (1 + (Cond.lt (V "p") (.get "MEM" (V "j"))).size + (1 + 1))) :=
            Run.ite_false hcondEqF hrunFail
          have hevMEMj' : (Expr.get "MEM" (V "j")).evalB B (σ.setVar "valid" 0) =
              some (fmem (σ.vars "j")) := by simpa [Env.setVar] using hevMEMj
          have hevAddJ' : (Expr.bin .add (V "j") (.lit 1)).evalB B
              ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))) = some (σ.vars "j" + 1) := by
            simp only [evalB_bin_iff]
            refine ⟨σ.vars "j", 1, ?_, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
            have hjset : ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).vars "j" =
                σ.vars "j" := by simp [Env.setVar]
            have h := evalB_var (B := B)
              (σ := (σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))) (x := "j")
              (show ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).vars "j" < B by
                rw [hjset]; omega)
            rwa [hjset] at h
          have hrunTail' : Run B (.seq (.assign "p" (.get "MEM" (V "j"))) (bump "j"))
              (σ.setVar "valid" 0)
              (((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).setVar "j" (σ.vars "j" + 1))
              7 :=
            ((Run.assign (x := "p") hevMEMj').seq
              (Run.assign (x := "j") hevAddJ')).mono (by simp only [Expr.size]; omega)
          set σ'' := ((σ.setVar "valid" 0).setVar "p" (fmem (σ.vars "j"))).setVar "j"
            (σ.vars "j" + 1) with hσ''def
          have hσ''j : σ''.vars "j" = σ.vars "j" + 1 := by simp [hσ''def, Env.setVar]
          have hσ''u : σ''.vars "u" = σ.vars "u" := by simp [hσ''def, Env.setVar]
          have hσ''p : σ''.vars "p" = fmem (σ.vars "j") := by simp [hσ''def, Env.setVar]
          have hσ''OFF : σ''.arrs "OFF" = σ.arrs "OFF" := by simp [hσ''def, Env.setVar]
          have hσ''MEM : σ''.arrs "MEM" = σ.arrs "MEM" := by simp [hσ''def, Env.setVar]
          have hσ''L : σ''.vars "L" = σ.vars "L" := by simp [hσ''def, Env.setVar]
          have hσ''m : σ''.vars "m" = σ.vars "m" := by simp [hσ''def, Env.setVar]
          have hσ''valid : σ''.vars "valid" = 0 := by simp [hσ''def, Env.setVar]
          have hσ''pB : σ''.vars "p" < B := by rw [hσ''p]; exact hfmemjB
          have hrunFull : Run B sortedBody σ σ'' 30 := by
            unfold sortedBody
            exact (Run.ite_true hcondUM (Run.ite_true hcondJ (hrunHead.seq hrunTail'))).mono (by
              simp only [Cond.size, Expr.size]; omega)
          refine ⟨σ'', hrunFull, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            by rw [hσ''j]; omega, le_of_eq hσ''u.symm, Or.inl (by rw [hσ''j]; omega),
            by rw [hσ''j]; omega, by rw [hσ''u]; omega⟩
          · rw [hσ''L]; exact hL
          · rw [hσ''m]; exact hm
          · exact hσ''valid
          · rw [hσ''OFF]; exact hOFFlen
          · rw [hσ''OFF]; exact hOFFcorr
          · rw [hσ''MEM]; exact hMEMlen
          · rw [hσ''MEM]; exact hMEMcorr
          · rw [hσ''j]; exact hjle
          · rw [hσ''u]; exact hu
          · exact hσ''pB
    · have hcondJF : (Cond.lt (V "j") (.get "OFF" (.bin .add (V "u") (.lit 1)))).evalB B σ =
          some false := by rw [evalB_condLt hevJ hevOFFu1, decide_eq_false hcaseA]
      have hrunBumpU := Run.assign (B := B) (σ := σ) (x := "u") hevAddU
      set σ' := σ.setVar "u" (σ.vars "u" + 1) with hσ'def
      have hσ'u : σ'.vars "u" = σ.vars "u" + 1 := by simp [hσ'def, Env.setVar]
      have hσ'j : σ'.vars "j" = σ.vars "j" := by simp [hσ'def, Env.setVar]
      have hσ'p : σ'.vars "p" = σ.vars "p" := by simp [hσ'def, Env.setVar]
      have hσ'OFF : σ'.arrs "OFF" = σ.arrs "OFF" := by simp [hσ'def, Env.setVar]
      have hσ'MEM : σ'.arrs "MEM" = σ.arrs "MEM" := by simp [hσ'def, Env.setVar]
      have hσ'L : σ'.vars "L" = σ.vars "L" := by simp [hσ'def, Env.setVar]
      have hσ'm : σ'.vars "m" = σ.vars "m" := by simp [hσ'def, Env.setVar]
      have hσ'valid : σ'.vars "valid" = σ.vars "valid" := by simp [hσ'def, Env.setVar]
      have hσ'pB : σ'.vars "p" < B := by rw [hσ'p]; exact hpB
      have hrunFull : Run B sortedBody σ σ' 30 := by
        unfold sortedBody
        exact (Run.ite_true hcondUM (Run.ite_false hcondJF hrunBumpU)).mono (by
          simp only [Cond.size, Expr.size]; omega)
      refine ⟨σ', hrunFull, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, le_of_eq hσ'j.symm,
        by rw [hσ'u]; omega, Or.inr (by rw [hσ'u]; omega), by rw [hσ'j]; omega,
        by rw [hσ'u]; omega⟩
      · rw [hσ'L]; exact hL
      · rw [hσ'm]; exact hm
      · rw [hσ'valid]; exact hvalid
      · rw [hσ'OFF]; exact hOFFlen
      · rw [hσ'OFF]; exact hOFFcorr
      · rw [hσ'MEM]; exact hMEMlen
      · rw [hσ'MEM]; exact hMEMcorr
      · rw [hσ'j]; exact hj
      · rw [hσ'u]; omega
      · exact hσ'pB
  · have hcondUMF : (Cond.lt (V "u") (V "m")).evalB B σ = some false := by
      rw [evalB_condLt hevU hevM, hm, decide_eq_false hum]
    have hev1j : (Expr.bin .add (V "j") (.lit 1)).evalB B σ = some (σ.vars "j" + 1) := by
      simp only [evalB_bin_iff]
      exact ⟨σ.vars "j", 1, hevJ, evalB_lit (by omega), by simp [Bop.apply], by omega⟩
    have hrunBumpJ := Run.assign (B := B) (σ := σ) (x := "j") hev1j
    set σ' := σ.setVar "j" (σ.vars "j" + 1) with hσ'def
    have hσ'j : σ'.vars "j" = σ.vars "j" + 1 := by simp [hσ'def, Env.setVar]
    have hσ'u : σ'.vars "u" = σ.vars "u" := by simp [hσ'def, Env.setVar]
    have hσ'p : σ'.vars "p" = σ.vars "p" := by simp [hσ'def, Env.setVar]
    have hσ'OFF : σ'.arrs "OFF" = σ.arrs "OFF" := by simp [hσ'def, Env.setVar]
    have hσ'MEM : σ'.arrs "MEM" = σ.arrs "MEM" := by simp [hσ'def, Env.setVar]
    have hσ'L : σ'.vars "L" = σ.vars "L" := by simp [hσ'def, Env.setVar]
    have hσ'm : σ'.vars "m" = σ.vars "m" := by simp [hσ'def, Env.setVar]
    have hσ'valid : σ'.vars "valid" = σ.vars "valid" := by simp [hσ'def, Env.setVar]
    have hσ'pB : σ'.vars "p" < B := by rw [hσ'p]; exact hpB
    have hrunFull : Run B sortedBody σ σ' 30 := by
      unfold sortedBody
      exact (Run.ite_false hcondUMF hrunBumpJ).mono (by simp only [Cond.size, Expr.size]; omega)
    refine ⟨σ', hrunFull, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hσ'j]; omega,
      le_of_eq hσ'u.symm, Or.inl (by rw [hσ'j]; omega), by rw [hσ'j]; omega,
      by rw [hσ'u]; omega⟩
    · rw [hσ'L]; exact hL
    · rw [hσ'm]; exact hm
    · rw [hσ'valid]; exact hvalid
    · rw [hσ'OFF]; exact hOFFlen
    · rw [hσ'OFF]; exact hOFFcorr
    · rw [hσ'MEM]; exact hMEMlen
    · rw [hσ'MEM]; exact hMEMcorr
    · rw [hσ'j]; omega
    · rw [hσ'u]; exact hu
    · exact hσ'pB

theorem checkSortedZero_spec_generic {B m0 : ℕ} (foff fmem : ℕ → ℕ)
    (hB : 1 < B) (hOFFb : ∀ i ≤ m0, foff i + 1 < B) (hm0B : m0 + 1 < B)
    (hMEMb : ∀ t < foff m0, fmem t + 1 < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "valid" = 0 ∧
        (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
        (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
        σ.vars "p" < B)
      checkSorted
      (fun _ σ' => σ'.vars "valid" = 0)
      (34 * foff m0 + 34 * m0 + 20) := by
  unfold checkSorted
  have hassignL : Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "valid" = 0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
      σ.vars "p" < B)
      (.assign "L" (.get "OFF" (V "m")))
      (fun σ σ' => σ'.vars "L" = foff m0 ∧
        σ'.vars "m" = σ.vars "m" ∧ σ'.vars "valid" = σ.vars "valid" ∧
        σ'.arrs "OFF" = σ.arrs "OFF" ∧ σ'.arrs "MEM" = σ.arrs "MEM" ∧ σ'.vars "p" = σ.vars "p")
      3 := by
    intro σ ⟨hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr, hpB⟩
    have hmOFF : σ.vars "m" < (σ.arrs "OFF").length := by rw [hOFFlen, hm]; omega
    have hmB : σ.vars "m" < B := by have := hOFFb m0 le_rfl; omega
    have hval : (σ.arrs "OFF").getD (σ.vars "m") 0 = foff m0 := by
      rw [hOFFcorr (σ.vars "m") (by omega), hm]
    have hLB' : (σ.arrs "OFF").getD (σ.vars "m") 0 < B := by
      have := hOFFb m0 le_rfl; omega
    have hgetElem : (σ.arrs "OFF")[σ.vars "m"] = (σ.arrs "OFF").getD (σ.vars "m") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmOFF]
    have hev : (Expr.get "OFF" (V "m")).evalB B σ = some ((σ.arrs "OFF").getD (σ.vars "m") 0) := by
      have h1 : (V "m" : Expr).evalB B σ = some (σ.vars "m") := by
        show fit B (σ.vars "m") = some (σ.vars "m")
        rw [fit_eq_some]; exact ⟨rfl, hmB⟩
      unfold Expr.evalB
      rw [h1, Option.bind_some, List.getElem?_eq_getElem hmOFF, Option.bind_some, hgetElem]
      rw [fit_eq_some]; exact ⟨rfl, hLB'⟩
    refine ⟨σ.setVar "L" ((σ.arrs "OFF").getD (σ.vars "m") 0), Run.assign hev, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact hval
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar]
  have hassignJ : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = 0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
      σ.vars "p" < B)
      (.assign "j" (.lit 0))
      (fun σ σ' => σ'.vars "j" = 0 ∧ σ'.vars "L" = σ.vars "L" ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.vars "valid" = σ.vars "valid" ∧
        σ'.arrs "OFF" = σ.arrs "OFF" ∧ σ'.arrs "MEM" = σ.arrs "MEM" ∧ σ'.vars "p" = σ.vars "p")
      2 := by
    intro σ hσ
    have hev : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    refine ⟨σ.setVar "j" 0, Run.assign hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar]
  have hassignU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "j" = 0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = 0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
      σ.vars "p" < B)
      (.assign "u" (.lit 0))
      (fun _ σ' => SortedInvZero B m0 foff fmem σ')
      2 := by
    intro σ ⟨hL, hj, hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr, hpB⟩
    have hev : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    refine ⟨σ.setVar "u" 0, Run.assign hev, ?_⟩
    unfold SortedInvZero
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar, hL]
    · simp [Env.setVar, hm]
    · simp [Env.setVar, hvalid]
    · simp [Env.setVar, hOFFlen]
    · simp only [Env.setVar]; exact hOFFcorr
    · simp [Env.setVar, hMEMlen]
    · simp only [Env.setVar]; exact hMEMcorr
    · simp [Env.setVar, hj]
    · simp [Env.setVar]
    · simp [Env.setVar, hpB]
  have hloop : Spec B (SortedInvZero B m0 foff fmem)
      (.while (.lt (V "j") (V "L")) sortedBody)
      (fun _ σ' => SortedInvZero B m0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (34 * foff m0 + 34 * m0 + 4) := by
    have hnsB : foff m0 < B := by have := hOFFb m0 le_rfl; omega
    refine Lax808846Proofs.Reasoning.Lib.Csr.ownerScan_spec B (34 * foff m0 + 34 * m0 + 4) m0
      (foff m0) 30 30 "j" "L" "u" sortedBody (SortedInvZero B m0 foff fmem) hnsB
      (fun σ hI => ⟨hI.1, hI.2.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.2.1⟩)
      (fun σ hI hjlt => ?_) (fun σ hσ => hσ) (fun σ hσ => by omega)
    obtain ⟨σ', hrun, hI', hjmono, humono, hprog, hjd, hud⟩ :=
      (sortedBodyZero_spec foff fmem hB hOFFb hm0B hMEMb).run ⟨hI, hjlt⟩
    exact ⟨σ', 30, hrun, hI', hjmono, humono, hprog, by omega⟩
  have hloopU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "j" = 0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = 0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
      σ.vars "p" < B)
      (.seq (.assign "u" (.lit 0)) (.while (.lt (V "j") (V "L")) sortedBody))
      (fun _ σ' => SortedInvZero B m0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (2 + (34 * foff m0 + 34 * m0 + 4)) :=
    Spec.seq hassignU hloop (fun _ _ _ hQ => hQ) (fun _ _ _ _ _ hqloop => hqloop)
  have hloopJU : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
      σ.vars "valid" = 0 ∧
      (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
      (σ.arrs "MEM").length = foff m0 ∧ (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧
      σ.vars "p" < B)
      (.seq (.assign "j" (.lit 0))
        (.seq (.assign "u" (.lit 0)) (.while (.lt (V "j") (V "L")) sortedBody)))
      (fun _ σ' => SortedInvZero B m0 foff fmem σ' ∧ σ'.vars "j" = foff m0)
      (2 + (2 + (34 * foff m0 + 34 * m0 + 4))) := by
    refine Spec.seq hassignJ hloopU ?_ ?_
    · intro σ σ' hσ hmid
      obtain ⟨hj', hL', hm', hvalid', hOFF', hMEM', hp'⟩ := hmid
      obtain ⟨hL, hm, hvalid, hOFFlen, hOFFcorr, hMEMlen, hMEMcorr, hpB⟩ := hσ
      refine ⟨by rw [hL', hL], hj', by rw [hm', hm], by rw [hvalid', hvalid],
        by rw [hOFF']; exact hOFFlen, ?_, by rw [hMEM']; exact hMEMlen, ?_, by rw [hp']; exact hpB⟩
      · rw [hOFF']; exact hOFFcorr
      · rw [hMEM']; exact hMEMcorr
    · intro σ σ' σ'' hσ hmid hpost
      exact hpost
  refine (Spec.seq hassignL hloopJU ?_ ?_).mono ?_
  · intro σ σ' hσ hmid
    obtain ⟨hL, hm, hvalid, hOFF, hMEM, hp⟩ := hmid
    obtain ⟨hm0, hv0, hOFFlen0, hOFFcorr0, hMEMlen0, hMEMcorr0, hpB0⟩ := hσ
    refine ⟨by rw [hL], by rw [hm, hm0], by rw [hvalid, hv0], by rw [hOFF]; exact hOFFlen0, ?_,
      by rw [hMEM]; exact hMEMlen0, ?_, by rw [hp]; exact hpB0⟩
    · rw [hOFF]; exact hOFFcorr0
    · rw [hMEM]; exact hMEMcorr0
  · intro σ σ' σ'' hσ hmid hpost
    obtain ⟨hI'', hj''⟩ := hpost
    unfold SortedInvZero at hI''
    exact hI''.2.2.1
  · omega

/-- **`checkUniverseBound`'s check, both directions.** `"valid"` is left at `v0` when
`n0 ≤ m0 + foff m0 + 4` and cleared to `0` otherwise — the "sticky" shape every one of
`validate`'s checks has, chained the same way as `checkOffsets_spec_generic`/
`checkMembers_spec_generic`/`checkSorted_spec_generic`. Rereads `OFF[m]` itself rather than
depending on `"L"`'s value on entry, so its precondition needs only `"OFF"`/`"m"`, not `"L"`. -/
theorem checkUniverseBound_spec_generic {B m0 n0 v0 : ℕ} (foff : ℕ → ℕ)
    (hB : 1 < B) (hn0B : n0 < B) (hsum0B : m0 + foff m0 + 4 < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "n" = n0 ∧ σ.vars "valid" = v0 ∧
        σ.vars "m" < (σ.arrs "OFF").length ∧
        (σ.arrs "OFF").getD (σ.vars "m") 0 = foff m0)
      checkUniverseBound
      (fun _ σ' => (n0 ≤ m0 + foff m0 + 4 → σ'.vars "valid" = v0) ∧
        (¬ n0 ≤ m0 + foff m0 + 4 → σ'.vars "valid" = 0))
      13 := by
  unfold checkUniverseBound
  have hassign : Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "n" = n0 ∧ σ.vars "valid" = v0 ∧
      σ.vars "m" < (σ.arrs "OFF").length ∧
      (σ.arrs "OFF").getD (σ.vars "m") 0 = foff m0)
      (.assign "L" (.get "OFF" (V "m")))
      (fun σ σ' => σ'.vars "L" = foff m0 ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "valid" = σ.vars "valid")
      3 := by
    intro σ ⟨hm, hn, hvalid, hmOFF, hval⟩
    have hmB : σ.vars "m" < B := by rw [hm]; omega
    have hLB' : (σ.arrs "OFF").getD (σ.vars "m") 0 < B := by rw [hval]; omega
    have hgetElem : (σ.arrs "OFF")[σ.vars "m"] = (σ.arrs "OFF").getD (σ.vars "m") 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmOFF]
    have hev : (Expr.get "OFF" (V "m")).evalB B σ = some ((σ.arrs "OFF").getD (σ.vars "m") 0) := by
      have h1 : (V "m" : Expr).evalB B σ = some (σ.vars "m") := by
        show fit B (σ.vars "m") = some (σ.vars "m")
        rw [fit_eq_some]; exact ⟨rfl, hmB⟩
      unfold Expr.evalB
      rw [h1, Option.bind_some, List.getElem?_eq_getElem hmOFF, Option.bind_some, hgetElem]
      rw [fit_eq_some]; exact ⟨rfl, hLB'⟩
    refine ⟨σ.setVar "L" ((σ.arrs "OFF").getD (σ.vars "m") 0), Run.assign hev, ?_, ?_, ?_, ?_⟩
    · show (σ.setVar "L" ((σ.arrs "OFF").getD (σ.vars "m") 0)).vars "L" = foff m0
      simp only [Env.setVar]; exact hval
    · simp [Env.setVar, hm]
    · simp [Env.setVar, hn]
    · simp [Env.setVar, hvalid]
  have hcheck : Spec B (fun σ => σ.vars "L" = foff m0 ∧ σ.vars "m" = m0 ∧
      σ.vars "n" = n0 ∧ σ.vars "valid" = v0)
      (failIf (.lt (.bin .add (.bin .add (V "m") (V "L")) (.lit 4)) (V "n")))
      (fun _ σ' => (n0 ≤ m0 + foff m0 + 4 → σ'.vars "valid" = v0) ∧
        (¬ n0 ≤ m0 + foff m0 + 4 → σ'.vars "valid" = 0))
      10 := by
    intro σ ⟨hL, hm, hn, hvalid⟩
    have hevm : (V "m" : Expr).evalB B σ = some m0 := by rw [← hm]; exact evalB_var (by omega)
    have hevL : (V "L" : Expr).evalB B σ = some (foff m0) := by rw [← hL]; exact evalB_var (by omega)
    have hevSum : (Expr.bin .add (V "m") (V "L")).evalB B σ = some (m0 + foff m0) :=
      evalB_bin hevm hevL (by simp only [Bop.apply_add]; omega)
    have hevSum4 : (Expr.bin .add (.bin .add (V "m") (V "L")) (.lit 4)).evalB B σ =
        some (m0 + foff m0 + 4) :=
      evalB_bin hevSum (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
    have hevn : (V "n" : Expr).evalB B σ = some n0 := by rw [← hn]; exact evalB_var (by omega)
    by_cases hc : n0 ≤ m0 + foff m0 + 4
    · have hcond : (Cond.lt (.bin .add (.bin .add (V "m") (V "L")) (.lit 4)) (V "n")).evalB B σ =
          some false := by
        rw [evalB_condLt hevSum4 hevn, decide_eq_false (by omega)]
      refine ⟨σ, ?_, ?_, ?_⟩
      · exact (Run.ite_false hcond (Run.skip (B := B) (σ := σ))).mono (by
          simp only [Cond.size, Expr.size]; omega)
      · intro _; exact hvalid
      · intro h; exact absurd hc h
    · have hcond : (Cond.lt (.bin .add (.bin .add (V "m") (V "L")) (.lit 4)) (V "n")).evalB B σ =
          some true := by
        rw [evalB_condLt hevSum4 hevn, decide_eq_true (by omega)]
      have hev0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
      refine ⟨σ.setVar "valid" 0, ?_, ?_, ?_⟩
      · exact (Run.ite_true hcond (Run.assign (x := "valid") hev0)).mono (by
          simp only [Cond.size, Expr.size]; omega)
      · intro h; exact absurd h hc
      · intro _; simp [Env.setVar]
  refine (Spec.seq hassign hcheck ?_ ?_).mono (by omega)
  · intro σ σ' hσ hmid
    exact ⟨hmid.1, by rw [hmid.2.1]; exact hσ.1, by rw [hmid.2.2.1]; exact hσ.2.1,
      by rw [hmid.2.2.2]; exact hσ.2.2.1⟩
  · intro σ σ' σ'' hσ hmid hpost; exact hpost

set_option maxHeartbeats 800000 in
/-- **`validate`, for arbitrary scan output, both directions.** `"valid"` ends at `1` exactly
when all five checks pass, and at `0` the moment any of them fails, so that the total
top-level program takes the reject branch on every input that does not decode to a genuine
`HittingSet` encoding. Proved by expressing the final value of
`"valid"` as one five-deep nested `ite` (via `eq_ite_of_imp` at each of the five checks, chained
through `checkOffsets_spec_generic`/`checkMembers_spec_generic`), then reading the iff straight
off that formula. -/
theorem validate_spec_generic {B m0 n0 k0 : ℕ} (foff fmem : ℕ → ℕ)
    (hB : 2 < B) (hOFFb : ∀ i ≤ m0, foff i + 1 < B) (hmB : m0 + 1 < B) (hnB : n0 < B)
    (hkB : k0 < B) (hMEMb : ∀ t < foff m0, fmem t + 1 < B)
    (hnmB : m0 + foff m0 + 4 < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ σ.vars "n" = n0 ∧ σ.vars "k" = k0 ∧
        (σ.arrs "OFF").length = m0 + 1 ∧ (∀ i ≤ m0, (σ.arrs "OFF").getD i 0 = foff i) ∧
        (σ.arrs "MEM").length = foff m0 ∧
        (∀ t < foff m0, (σ.arrs "MEM").getD t 0 = fmem t) ∧ σ.vars "p" < B)
      validate
      (fun _ σ' => (σ'.vars "valid" = 1 ↔
          (foff 0 = 0 ∧ OffsetsOkG foff m0 ∧ MembersOkG fmem n0 (foff m0) ∧
            SortedOkG foff fmem m0 (foff m0) ∧ n0 ≤ m0 + foff m0 + 4 ∧
            2 ≤ k0 ∧ k0 ≤ n0)) ∧
        σ'.vars "valid" ≤ 1)
      (2 + 7 + (18 * m0 + 6) + (18 * foff m0 + 9) + (34 * foff m0 + 34 * m0 + 20) +
        13 + 6 + 6) := by
  intro σ0 ⟨hm0, hn0, hk0, hOFFlen0, hOFFcorr0, hMEMlen0, hMEMcorr0, hp0⟩
  -- Step 0: valid := 1
  have hev0 : (Expr.lit 1).evalB B σ0 = some 1 := evalB_lit (by omega)
  have hrun0 := Run.assign (B := B) (σ := σ0) (x := "valid") hev0
  set σ0a := σ0.setVar "valid" 1 with hσ0adef
  have hm0a : σ0a.vars "m" = m0 := by simp [hσ0adef, Env.setVar, hm0]
  have hn0a : σ0a.vars "n" = n0 := by simp [hσ0adef, Env.setVar, hn0]
  have hk0a : σ0a.vars "k" = k0 := by simp [hσ0adef, Env.setVar, hk0]
  have hvalid0a : σ0a.vars "valid" = 1 := by simp [hσ0adef, Env.setVar]
  have hOFF0a : σ0a.arrs "OFF" = σ0.arrs "OFF" := by simp [hσ0adef, Env.setVar]
  have hMEM0a : σ0a.arrs "MEM" = σ0.arrs "MEM" := by simp [hσ0adef, Env.setVar]
  have hp0a : σ0a.vars "p" < B := by simp [hσ0adef, Env.setVar, hp0]
  -- Step 1: failUnless (OFF[0] = 0)
  have h0lt : 0 < (σ0a.arrs "OFF").length := by rw [hOFF0a, hOFFlen0]; omega
  have hgetElem0 : (σ0a.arrs "OFF")[0] = (σ0a.arrs "OFF").getD 0 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0lt]
  have hOFF00 : (σ0a.arrs "OFF").getD 0 0 = foff 0 := by rw [hOFF0a, hOFFcorr0 0 (by omega)]
  have hget0k : (σ0a.arrs "OFF")[0]? = some (foff 0) := by
    rw [List.getElem?_eq_getElem h0lt, hgetElem0, hOFF00]
  have hOffB0 : foff 0 < B := by have := hOFFb 0 (by omega); omega
  have hevIdx0 : (Expr.lit 0).evalB B σ0a = some 0 := evalB_lit (by omega)
  have hevGet0 : (Expr.get "OFF" (.lit 0)).evalB B σ0a = some (foff 0) :=
    evalB_get hevIdx0 hget0k hOffB0
  set σ1 := if foff 0 = 0 then σ0a else σ0a.setVar "valid" 0 with hσ1def
  have hrun1 : Run B (.ite (Cond.eq (.get "OFF" (.lit 0)) (.lit 0)) Com.skip
      (.assign "valid" (.lit 0))) σ0a σ1
      (1 + (Cond.eq (.get "OFF" (.lit 0)) (.lit 0)).size + 2) := by
    by_cases hc1 : foff 0 = 0
    · have hevCond1 : (Cond.eq (.get "OFF" (.lit 0)) (.lit 0)).evalB B σ0a = some true := by
        rw [evalB_condEq hevGet0 hevIdx0, hc1]; rfl
      rw [hσ1def, if_pos hc1]
      exact (Run.ite_true hevCond1 (Run.skip (B := B) (σ := σ0a))).mono (by omega)
    · have hevCond1 : (Cond.eq (.get "OFF" (.lit 0)) (.lit 0)).evalB B σ0a = some false := by
        rw [evalB_condEq hevGet0 hevIdx0]; simp [hc1]
      rw [hσ1def, if_neg hc1]
      have hev0' : (Expr.lit 0).evalB B σ0a = some 0 := evalB_lit (by omega)
      exact Run.ite_false hevCond1 (Run.assign (x := "valid") hev0')
  have hvalid1 : σ1.vars "valid" = if foff 0 = 0 then 1 else 0 := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1, if_pos hc1]; exact hvalid0a
    · rw [hσ1def, if_neg hc1, if_neg hc1]; simp [Env.setVar]
  have hm1 : σ1.vars "m" = m0 := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hm0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hm0a]
  have hn1 : σ1.vars "n" = n0 := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hn0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hn0a]
  have hk1 : σ1.vars "k" = k0 := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hk0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hk0a]
  have hOFF1 : σ1.arrs "OFF" = σ0.arrs "OFF" := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hOFF0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hOFF0a]
  have hMEM1 : σ1.arrs "MEM" = σ0.arrs "MEM" := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hMEM0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hMEM0a]
  have hp1 : σ1.vars "p" < B := by
    by_cases hc1 : foff 0 = 0
    · rw [hσ1def, if_pos hc1]; exact hp0a
    · rw [hσ1def, if_neg hc1]; simp [Env.setVar, hp0a]
  have hOFFcorr1 : ∀ i ≤ m0, (σ1.arrs "OFF").getD i 0 = foff i := by rw [hOFF1]; exact hOFFcorr0
  -- Step 2: checkOffsets
  obtain ⟨σ2, hrun2, hq2⟩ := checkOffsets_spec_generic foff m0 (if foff 0 = 0 then 1 else 0)
    (by omega) hOFFb (by omega) σ1 ⟨hm1, hvalid1, by rw [hOFF1]; exact hOFFlen0, hOFFcorr1⟩
  have hvalid2 : σ2.vars "valid" = if OffsetsOkG foff m0 then (if foff 0 = 0 then 1 else 0) else 0 :=
    eq_ite_of_imp hq2.2.1 hq2.2.2
  have hn2 : σ2.vars "n" = n0 := by
    have := hrun2.frame_var "n" (by decide); rw [this]; exact hn1
  have hk2 : σ2.vars "k" = k0 := by
    have := hrun2.frame_var "k" (by decide); rw [this]; exact hk1
  have hOFF2 : σ2.arrs "OFF" = σ0.arrs "OFF" := by
    have := hrun2.frame_arr "OFF" (by decide); rw [this]; exact hOFF1
  have hMEM2 : σ2.arrs "MEM" = σ0.arrs "MEM" := by
    have := hrun2.frame_arr "MEM" (by decide); rw [this]; exact hMEM1
  have hm2 : σ2.vars "m" = m0 := by
    have := hrun2.frame_var "m" (by decide); rw [this]; exact hm1
  have hp2 : σ2.vars "p" < B := by
    have := hrun2.frame_var "p" (by decide); rw [this]; exact hp1
  -- Step 3: checkMembers
  have hOFFm2 : (σ2.arrs "OFF").getD m0 0 = foff m0 := by rw [hOFF2]; exact hOFFcorr0 m0 le_rfl
  have hmOFFlen2 : σ2.vars "m" < (σ2.arrs "OFF").length := by
    rw [hOFF2, hOFFlen0, hm2]; omega
  have hmB2 : σ2.vars "m" + 1 < B := by rw [hm2]; exact hmB
  have hMEMlen2 : (σ2.arrs "MEM").length = foff m0 := by rw [hMEM2, hMEMlen0]
  have hOFFmget2 : (σ2.arrs "OFF").getD (σ2.vars "m") 0 = foff m0 := by rw [hm2]; exact hOFFm2
  have hMEMcorr2 : ∀ t < foff m0, (σ2.arrs "MEM").getD t 0 = fmem t := by
    rw [hMEM2]; exact hMEMcorr0
  have hLB3 : foff m0 < B := by have := hOFFb m0 le_rfl; omega
  obtain ⟨σ3, hrun3, hq3⟩ := checkMembers_spec_generic fmem (foff m0) n0
    (if OffsetsOkG foff m0 then (if foff 0 = 0 then 1 else 0) else 0) (by omega) hMEMb hnB
    hLB3 σ2 ⟨hn2, hvalid2, hMEMlen2, hmOFFlen2, hmB2, hOFFmget2, hMEMcorr2⟩
  have hvalid3 : σ3.vars "valid" = if MembersOkG fmem n0 (foff m0) then
      (if OffsetsOkG foff m0 then (if foff 0 = 0 then 1 else 0) else 0) else 0 :=
    eq_ite_of_imp hq3.2.1 hq3.2.2
  have hk3 : σ3.vars "k" = k0 := by
    have := hrun3.frame_var "k" (by decide); rw [this]; exact hk2
  have hn3 : σ3.vars "n" = n0 := by
    have := hrun3.frame_var "n" (by decide); rw [this]; exact hn2
  have hp3 : σ3.vars "p" < B := by
    have := hrun3.frame_var "p" (by decide); rw [this]; exact hp2
  have hOFF3 : σ3.arrs "OFF" = σ0.arrs "OFF" := by
    have := hrun3.frame_arr "OFF" (by decide); rw [this]; exact hOFF2
  have hMEM3 : σ3.arrs "MEM" = σ0.arrs "MEM" := by
    have := hrun3.frame_arr "MEM" (by decide); rw [this]; exact hMEM2
  have hm3 : σ3.vars "m" = m0 := by
    have := hrun3.frame_var "m" (by decide); rw [this]; exact hm2
  have hOFFlen3 : (σ3.arrs "OFF").length = m0 + 1 := by rw [hOFF3]; exact hOFFlen0
  have hOFFcorr3 : ∀ i ≤ m0, (σ3.arrs "OFF").getD i 0 = foff i := by rw [hOFF3]; exact hOFFcorr0
  have hMEMlen3 : (σ3.arrs "MEM").length = foff m0 := by rw [hMEM3]; exact hMEMlen0
  have hMEMcorr3 : ∀ t < foff m0, (σ3.arrs "MEM").getD t 0 = fmem t := by
    rw [hMEM3]; exact hMEMcorr0
  -- Step 3.5: checkSorted
  obtain ⟨σ4, hrun4, hvalid4, hn4, hk4⟩ :
      ∃ σ4, Run B checkSorted σ3 σ4 (34 * foff m0 + 34 * m0 + 20) ∧
        σ4.vars "valid" = (if (foff 0 = 0 ∧ OffsetsOkG foff m0) then
          (if SortedOkG foff fmem m0 (foff m0) then σ3.vars "valid" else 0) else 0) ∧
        σ4.vars "n" = n0 ∧ σ4.vars "k" = k0 := by
    by_cases hcase : foff 0 = 0 ∧ OffsetsOkG foff m0
    · obtain ⟨hoff0case, hOffcase⟩ := hcase
      obtain ⟨σ4', hrun4', hq4'⟩ := checkSorted_spec_generic foff fmem
        (by omega) hOffcase hoff0case hOFFb (by omega) hMEMb σ3
        ⟨hm3, rfl, hOFFlen3, hOFFcorr3, hMEMlen3, hMEMcorr3⟩
      have hvalid4' : σ4'.vars "valid" =
          if SortedOkG foff fmem m0 (foff m0) then σ3.vars "valid" else 0 :=
        eq_ite_of_imp hq4'.2.1 hq4'.2.2
      refine ⟨σ4', hrun4', ?_, ?_, ?_⟩
      · rw [if_pos ⟨hoff0case, hOffcase⟩]; exact hvalid4'
      · have := hrun4'.frame_var "n" (by decide); rw [this]; exact hn3
      · have := hrun4'.frame_var "k" (by decide); rw [this]; exact hk3
    · have hvalid3zero : σ3.vars "valid" = 0 := by
        rw [hvalid3]
        by_cases h0 : foff 0 = 0
        · have hO : ¬ OffsetsOkG foff m0 := fun hc => hcase ⟨h0, hc⟩
          rw [if_neg hO]; split_ifs <;> rfl
        · rw [if_neg h0]; split_ifs <;> rfl
      obtain ⟨σ4', hrun4', hq4'⟩ := checkSortedZero_spec_generic foff fmem
        (by omega) hOFFb (by omega) hMEMb σ3
        ⟨hm3, hvalid3zero, hOFFlen3, hOFFcorr3, hMEMlen3, hMEMcorr3, hp3⟩
      refine ⟨σ4', hrun4', ?_, ?_, ?_⟩
      · rw [if_neg hcase]; exact hq4'
      · have := hrun4'.frame_var "n" (by decide); rw [this]; exact hn3
      · have := hrun4'.frame_var "k" (by decide); rw [this]; exact hk3
  -- Step 3.75: checkUniverseBound
  have hm4 : σ4.vars "m" = m0 := by
    have := hrun4.frame_var "m" (by decide); rw [this]; exact hm3
  have hOFF4 : σ4.arrs "OFF" = σ3.arrs "OFF" := hrun4.frame_arr "OFF" (by decide)
  have hOFFcorr4 : ∀ i ≤ m0, (σ4.arrs "OFF").getD i 0 = foff i := by rw [hOFF4]; exact hOFFcorr3
  have hmOFFlen4 : σ4.vars "m" < (σ4.arrs "OFF").length := by rw [hOFF4, hOFFlen3, hm4]; omega
  obtain ⟨σ5, hrun5, hq5⟩ := checkUniverseBound_spec_generic (m0 := m0) (n0 := n0)
    (v0 := σ4.vars "valid")
    foff (by omega) hnB hnmB σ4
    ⟨hm4, hn4, rfl, hmOFFlen4, by rw [hm4]; exact hOFFcorr4 m0 le_rfl⟩
  have hvalid5 : σ5.vars "valid" = if n0 ≤ m0 + foff m0 + 4 then σ4.vars "valid" else 0 :=
    eq_ite_of_imp hq5.1 hq5.2
  have hn5 : σ5.vars "n" = n0 := by
    have := hrun5.frame_var "n" (by decide); rw [this]; exact hn4
  have hk5 : σ5.vars "k" = k0 := by
    have := hrun5.frame_var "k" (by decide); rw [this]; exact hk4
  -- Step 4: failIf (k < 2)
  have hevk5 : (V "k").evalB B σ5 = some (σ5.vars "k") := evalB_var (by omega)
  have hevlit2 : (Expr.lit 2).evalB B σ5 = some 2 := evalB_lit (by omega)
  set σ6 := if k0 < 2 then σ5.setVar "valid" 0 else σ5 with hσ6def
  have hrun6 : Run B (.ite (Cond.lt (V "k") (.lit 2)) (.assign "valid" (.lit 0)) Com.skip)
      σ5 σ6 (1 + (Cond.lt (V "k") (.lit 2)).size + 2) := by
    by_cases hc6 : k0 < 2
    · have hcond6 : (Cond.lt (V "k") (.lit 2)).evalB B σ5 = some true := by
        rw [evalB_condLt hevk5 hevlit2, hk5, decide_eq_true hc6]
      rw [hσ6def, if_pos hc6]
      have hev0' : (Expr.lit 0).evalB B σ5 = some 0 := evalB_lit (by omega)
      exact Run.ite_true hcond6 (Run.assign (x := "valid") hev0')
    · have hcond6 : (Cond.lt (V "k") (.lit 2)).evalB B σ5 = some false := by
        rw [evalB_condLt hevk5 hevlit2, hk5, decide_eq_false hc6]
      rw [hσ6def, if_neg hc6]
      exact (Run.ite_false hcond6 (Run.skip (B := B) (σ := σ5))).mono (by omega)
  have hvalid6 : σ6.vars "valid" = if 2 ≤ k0 then σ5.vars "valid" else 0 := by
    by_cases hc6 : k0 < 2
    · rw [hσ6def, if_pos hc6, if_neg (show ¬ 2 ≤ k0 by omega)]; simp [Env.setVar]
    · rw [hσ6def, if_neg hc6, if_pos (show 2 ≤ k0 by omega)]
  have hn6 : σ6.vars "n" = n0 := by
    by_cases hc6 : k0 < 2
    · rw [hσ6def, if_pos hc6]; simp [Env.setVar, hn5]
    · rw [hσ6def, if_neg hc6]; exact hn5
  have hk6 : σ6.vars "k" = k0 := by
    by_cases hc6 : k0 < 2
    · rw [hσ6def, if_pos hc6]; simp [Env.setVar, hk5]
    · rw [hσ6def, if_neg hc6]; exact hk5
  -- Step 5: failIf (n < k)
  have hevn6 : (V "n").evalB B σ6 = some (σ6.vars "n") := evalB_var (by omega)
  have hevk6 : (V "k").evalB B σ6 = some (σ6.vars "k") := evalB_var (by omega)
  set σ7 := if n0 < k0 then σ6.setVar "valid" 0 else σ6 with hσ7def
  have hrun7 : Run B (.ite (Cond.lt (V "n") (V "k")) (.assign "valid" (.lit 0)) Com.skip)
      σ6 σ7 (1 + (Cond.lt (V "n") (V "k")).size + 2) := by
    by_cases hc7 : n0 < k0
    · have hcond7 : (Cond.lt (V "n") (V "k")).evalB B σ6 = some true := by
        rw [evalB_condLt hevn6 hevk6, hn6, hk6, decide_eq_true hc7]
      rw [hσ7def, if_pos hc7]
      have hev0' : (Expr.lit 0).evalB B σ6 = some 0 := evalB_lit (by omega)
      exact Run.ite_true hcond7 (Run.assign (x := "valid") hev0')
    · have hcond7 : (Cond.lt (V "n") (V "k")).evalB B σ6 = some false := by
        rw [evalB_condLt hevn6 hevk6, hn6, hk6, decide_eq_false hc7]
      rw [hσ7def, if_neg hc7]
      exact (Run.ite_false hcond7 (Run.skip (B := B) (σ := σ6))).mono (by omega)
  have hvalid7 : σ7.vars "valid" = if k0 ≤ n0 then σ6.vars "valid" else 0 := by
    by_cases hc7 : n0 < k0
    · rw [hσ7def, if_pos hc7, if_neg (show ¬ k0 ≤ n0 by omega)]; simp [Env.setVar]
    · rw [hσ7def, if_neg hc7, if_pos (show k0 ≤ n0 by omega)]
  refine ⟨σ7, ?_, ?_⟩
  · show Run B validate σ0 σ7 _
    unfold validate
    exact (hrun0.seq (hrun1.seq (hrun2.seq (hrun3.seq
      (hrun4.seq (hrun5.seq (hrun6.seq hrun7))))))).mono (by
      simp only [Expr.size, Cond.size]; omega)
  · show (σ7.vars "valid" = 1 ↔
      (foff 0 = 0 ∧ OffsetsOkG foff m0 ∧ MembersOkG fmem n0 (foff m0) ∧
        SortedOkG foff fmem m0 (foff m0) ∧ n0 ≤ m0 + foff m0 + 4 ∧
        2 ≤ k0 ∧ k0 ≤ n0)) ∧
      σ7.vars "valid" ≤ 1
    rw [hvalid7, hvalid6, hvalid5, hvalid4, hvalid3]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h; split_ifs at h; tauto
    · rintro ⟨hc1, hc2, hc3, hc4, hc4b, hc5, hc6⟩; simp [hc1, hc2, hc3, hc4, hc4b, hc5, hc6]
    · split_ifs <;> omega

end Lax496464Proofs.Ram.Validate
