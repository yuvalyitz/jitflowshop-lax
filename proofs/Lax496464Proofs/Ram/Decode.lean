import Lax496464Proofs.Ram.Imp
import Lax496464.WordEncoding
import Mathlib.Data.List.GetD

/-!
# Reading the instance off the tape

Every algorithm of this submission begins the same way. The word
`[n, m, p₀ … p_{n−1}, q₀ …, d₀ …, w₀ …]`, possibly followed by a threshold, is
self-describing: its first entry says how many jobs there are and therefore how long the
four blocks that follow it are. `readInstance` takes the two header numbers into scalars
and the `4n` numbers of the blocks into the array `A`, one pass, and leaves whatever
follows on the tape for the caller.

The array is indexed by block: `A[j]` is `p_j`, `A[n+j]` is `q_j`, `A[2n+j]` is `d_j` and
`A[3n+j]` is `w_j`, which is what `preTime_eq` and its three companions say.
-/

namespace Lax496464Proofs.Ram.Decode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464.WordEncoding

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- One step of the reading pass: take the next number and store it. -/
def readBody : Com :=
  .seq (.read "v") (.seq (.store "A" (V "i") (V "v")) (bump "i"))

/-- The reading pass over the four blocks. -/
def readLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "len")) readBody)

/-- Read the header, then the four blocks. -/
def readInstance : Com :=
  .seq (.read "n") (.seq (.read "m")
    (.seq (.assign "len" (.bin .mul (.lit 4) (V "n"))) readLoop))

variable {B : ℕ} {x : List ℕ}

/-- The state part-way through the pass: the header is in place, the array holds the
prefix of the blocks already read, and the tape stands where the counter says. -/
def RInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = jobCount x ∧ σ.vars "m" = machineCount x ∧
    σ.vars "len" = 4 * jobCount x ∧ σ.vars "i" ≤ 4 * jobCount x ∧
    (σ.arrs "A").length = 4 * jobCount x ∧
    (∀ j < σ.vars "i", (σ.arrs "A").getD j 0 = x.getD (2 + j) 0) ∧
    σ.inp = x.drop (2 + σ.vars "i") ∧ σ.out = []

theorem readBody_spec (hlen : 2 + 4 * jobCount x ≤ x.length) (hxB : ∀ v ∈ x, v < B)
    (hnB : 4 * jobCount x + 1 < B) :
    Spec B (fun σ => RInv x σ ∧ σ.vars "i" < 4 * jobCount x) readBody
      (fun σ σ' => RInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv x σ ∧ σ.vars "i" < 4 * jobCount x ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "i" < (σ.arrs "A").length ∧ σ.vars "i" + 1 < B) ?_ ?_
  · run_vcg
    · obtain ⟨hn, hm, hl, hle, hlength, hcell, hinp, hout⟩ := ‹RInv x σ›
      have hilt := ‹σ.vars "i" < 4 * jobCount x›
      have hidx : 2 + σ.vars "i" < x.length := by omega
      have hAidx : σ.vars "i" < (σ.arrs "A").length := by rw [hlength]; exact hilt
      simp only [RInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hn
      · exact hm
      · exact hl
      · exact hilt
      · exact hlength
      · intro j hj
        rcases Nat.lt_or_ge j (σ.vars "i") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell j h
        · have hje : j = σ.vars "i" := by omega
          subst hje
          rw [hinp]
          simp [hAidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
        congr 1
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, hlt⟩
    obtain ⟨hn, hm, hl, hle, hlength, hcell, hinp, hout⟩ := hI
    have hidx : 2 + σ.vars "i" < x.length := by omega
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (x.drop (2 + σ.vars "i")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨⟨hn, hm, hl, hle, hlength, hcell, hinp, hout⟩, hlt, hne, ?_,
      by rw [hlength]; exact hlt, by omega⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ x.drop (2 + σ.vars "i") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hxB u (List.mem_of_mem_drop this)

theorem readLoop_spec (hlen : 2 + 4 * jobCount x ≤ x.length) (hxB : ∀ v ∈ x, v < B)
    (hnB : 4 * jobCount x + 1 < B) :
    Spec B (fun σ => RInv x (σ.setVar "i" 0)) readLoop
      (fun _ σ' => RInv x σ' ∧ σ'.vars "i" = 4 * jobCount x)
      (12 * (4 * jobCount x) + 6) :=
  Spec.forRangeZero "i" "len" (RInv x) (4 * jobCount x) 8 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (readBody_spec hlen hxB hnB)

/-- **The instance has been read.** The header is in `n` and `m`, the four blocks are in
`A`, and the tape stands just past them. -/
theorem readInstance_spec (hlen : 2 + 4 * jobCount x ≤ x.length) (hxB : ∀ v ∈ x, v < B)
    (hnB : 4 * jobCount x + 5 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * jobCount x)
      readInstance
      (fun _ σ' => RInv x σ' ∧ σ'.vars "i" = 4 * jobCount x)
      (12 * (4 * jobCount x) + 6 + 6) := by
  have hx0 : x ≠ [] := by intro hc; rw [hc] at hlen; simp at hlen
  have h0 : x.getD 0 0 = jobCount x := rfl
  have h1 : x.getD 1 0 = machineCount x := rfl
  have hn2 : jobCount x < B := by
    rcases Nat.eq_zero_or_pos (jobCount x) with h | h
    · omega
    · omega
  have hhead : x.head?.getD 0 = jobCount x := by
    rw [jobCount, List.getD_eq_getElem?_getD, List.head?_eq_getElem?]
  have htail : x.tail.tail = x.drop 2 := by
    rw [← List.drop_one, ← List.drop_one, List.drop_drop]
  have hxl : 2 ≤ x.length := by omega
  refine Spec.pre (P := fun σ => σ.inp = x ∧ σ.out = [] ∧
      (σ.arrs "A").length = 4 * jobCount x) ?_ (fun _ h => h)
  run_vcg [readLoop_spec (B := B) hlen hxB (by omega)]
  all_goals try assumption
  all_goals simp only [Env.setVar]
  all_goals simp_all [RInv]
  all_goals first
    | omega
    | (intro hc
       have hz : x.tail.length = 0 := by rw [hc]; rfl
       rw [List.length_tail] at hz
       omega)

/-! ## The decoded state -/

/-- What the caller of `readInstance` gets: the header in two scalars, the four blocks in
`A` addressed by job, and the tape just past the instance. -/
def Decoded (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = jobCount x ∧ σ.vars "m" = machineCount x ∧
    (σ.arrs "A").length = 4 * jobCount x ∧
    (∀ j < jobCount x, (σ.arrs "A").getD j 0 = preTime x j) ∧
    (∀ j < jobCount x, (σ.arrs "A").getD (jobCount x + j) 0 = procTime x j) ∧
    (∀ j < jobCount x, (σ.arrs "A").getD (2 * jobCount x + j) 0 = due x j) ∧
    (∀ j < jobCount x, (σ.arrs "A").getD (3 * jobCount x + j) 0 = wt x j) ∧
    σ.inp = x.drop (2 + 4 * jobCount x) ∧ σ.out = []

theorem decoded_of_rinv {σ : Env} (h : RInv x σ) (hi : σ.vars "i" = 4 * jobCount x) :
    Decoded x σ := by
  obtain ⟨hn, hm, hl, hle, hlength, hcell, hinp, hout⟩ := h
  refine ⟨hn, hm, hlength, ?_, ?_, ?_, ?_, by rw [hinp, hi], hout⟩
  · intro j hj
    rw [hcell j (by omega)]; rfl
  · intro j hj
    rw [hcell _ (by omega), procTime]
    congr 1
    omega
  · intro j hj
    rw [hcell _ (by omega), due]
    congr 1
    omega
  · intro j hj
    rw [hcell _ (by omega), wt]
    congr 1
    omega

/-- **The reader, as its callers use it.** -/
theorem readInstance_decoded (hlen : 2 + 4 * jobCount x ≤ x.length) (hxB : ∀ v ∈ x, v < B)
    (hnB : 4 * jobCount x + 5 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * jobCount x)
      readInstance (fun _ σ' => Decoded x σ') (48 * jobCount x + 12) :=
  ((readInstance_spec hlen hxB hnB).post
    (fun _ _ _ h => decoded_of_rinv h.1 h.2)).mono (by omega)

end Lax496464Proofs.Ram.Decode
