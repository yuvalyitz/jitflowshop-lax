import Lax496464Proofs.Ram.CsrWord
import Lax496464Proofs.Ram.BitsNat

/-!
# Decoding a Hitting Set Word as a Finite-State Scan of Its Bits

`HittingSet.encodeInstance` is `n`, `m`, `k`, then for each of the `m` sets its size
followed by its members, every number in the self-delimiting code of `BitsNat`/
`Lax391470Proofs.Bits`: a run of `1`s counting the number's bit-length, a `0`, then that
many bits, least significant first.

The scan below reads that code one entry at a time with a small state, exactly as
`Lax391470Proofs.CnfScan` reads a CNF encoding: `step` is a total function of the state
and the next entry, so `run := l.foldl step` is defined for *every* list of numbers,
whether or not it is anybody's encoding. This is what lets a word-RAM program built from
it be *total*, which `Lax759944.RamPolytime`'s definition demands. Soundness (a run that
finishes only finishes on a genuine encoding) is not needed and not proved here — only
*completeness*: run on the bits of a genuine `encodeInstance P k`, the scan reaches `done`
having recovered exactly `csrWord`'s pieces (`Ram/CsrWord.lean`), which is what lets the
already-proved `Ram.Build`/`Ram.Program` machinery be chained after it.
-/

namespace Lax496464Proofs.Ram.ScanModel

open Lax496464.HittingSet Lax496464Proofs.Ram.CsrWord
open Lax496464Proofs.Ram.BitsNat (digit bitsNat sum_digit natBits natBits_encodeNat)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The scan's state.

`ph = 0`: counting the leading `1`s of a number into `cc`. `ph = 1`: reading `cc` bits of
that number into `vv`, `ii` of them read so far. `ph = 2`: finished.

`tgt` says which field the number just finished belongs to: `0` = the universe size `n`,
`1` = the set count `m`, `2` = the solution size `k`, `3` = the size of set `j`, `4` = a
member of set `j`. `n`, `m`, `k` hold the header once read. `j` is the set being read, `u`
the member of it being read, `sz` its size. `off` is the running member-offset, and `offs`/
`mems` are the offsets and members read so far, in order. -/
structure St where
  ph : ℕ
  tgt : ℕ
  cc : ℕ
  ii : ℕ
  vv : ℕ
  n : ℕ
  m : ℕ
  k : ℕ
  j : ℕ
  u : ℕ
  sz : ℕ
  off : ℕ
  offs : List ℕ
  mems : List ℕ
  deriving Repr

/-- Start: about to count the leading `1`s of `n`. -/
def init : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], []⟩

/-- A number has just been fully read, with value `v`; act on it according to `tgt` and
say what comes next. -/
def afterNumber (s : St) (v : ℕ) : St :=
  match s.tgt with
  | 0 => { s with n := v, ph := 0, tgt := 1, cc := 0, ii := 0, vv := 0 }
  | 1 => { s with m := v, ph := 0, tgt := 2, cc := 0, ii := 0, vv := 0 }
  | 2 =>
    if s.m = 0 then
      { s with k := v, ph := 2, tgt := 0, cc := 0, sz := 0, offs := [0], ii := 0, vv := 0 }
    else
      { s with k := v, ph := 0, tgt := 3, cc := 0, sz := 0, j := 0, off := 0, offs := [0], ii := 0, vv := 0 }
  | 3 =>
    if v = 0 then
      let offs' := s.offs ++ [s.off]
      if s.j + 1 < s.m then
        { s with sz := 0, u := 0, offs := offs', j := s.j + 1, ph := 0, tgt := 3, cc := 0, ii := 0, vv := 0 }
      else
        { s with sz := 0, u := 0, offs := offs', ph := 2, tgt := 0, cc := 0, ii := 0, vv := 0 }
    else
      { s with sz := v, u := 0, ph := 0, tgt := 4, cc := 0, ii := 0, vv := 0 }
  | _ =>
    let mems' := s.mems ++ [v]
    let u' := s.u + 1
    if u' < s.sz then
      { s with mems := mems', u := u', ph := 0, tgt := 4, cc := 0, ii := 0, vv := 0 }
    else
      let off' := s.off + s.sz
      let offs' := s.offs ++ [off']
      if s.j + 1 < s.m then
        { s with mems := mems', u := 0, off := off', offs := offs', j := s.j + 1, ph := 0, tgt := 3, cc := 0, sz := 0, ii := 0, vv := 0 }
      else
        { s with mems := mems', u := 0, off := off', offs := offs', ph := 2, tgt := 0, cc := 0, sz := 0, ii := 0, vv := 0 }

/-- One entry of the input. A total function: every state and every entry has a next
state, whether or not the entry is a genuine bit or the state is mid-decoding a genuine
encoding. -/
def step (s : St) (b : ℕ) : St :=
  if s.ph = 0 then
    if b = 1 then { s with cc := s.cc + 1 }
    else if s.cc = 0 then afterNumber s 0
    else { s with ph := 1, ii := 0, vv := 0 }
  else if s.ph = 1 then
    let vv' := s.vv + b * 2 ^ s.ii
    let ii' := s.ii + 1
    if ii' < s.cc then { s with vv := vv', ii := ii' }
    else afterNumber s vv'
  else s

/-- The scan over a whole list of entries. -/
def run (s : St) (l : List ℕ) : St := l.foldl step s

@[simp] theorem run_nil (s : St) : run s [] = s := rfl
@[simp] theorem run_cons (s : St) (b : ℕ) (l : List ℕ) : run s (b :: l) = run (step s b) l := rfl
theorem run_append (s : St) (l l' : List ℕ) : run s (l ++ l') = run (run s l) l' := by
  simp [run, List.foldl_append]

/-- What one more `step` of `scanLoop`'s machine layer does to the model: the scan over
`l.take (i + 1)` is the scan over `l.take i` followed by one `step` on the `i`-th entry. -/
theorem run_take_succ (s0 : St) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    run s0 (l.take (i + 1)) = step (run s0 (l.take i)) (l.getD i 0) := by
  rw [List.take_add_one, run_append]
  simp [List.getElem?_eq_getElem hi]

/-! ## The scan's own internal bookkeeping stays consistent

A fact about `step`/`afterNumber` alone, true of every state reachable from `init` by any
list of entries — genuine encoding or not. This is what a `scanLoop` machine-layer proof
needs to know at every iteration: not just that `tgt`/`ph` stay in range, but that the CSR
bookkeeping (`offs`/`j`, `mems`/`off`/`u`, `sz`/`u`) is always internally consistent, so the
word-RAM program's array stores land at the position the model says they do. -/
def Struct (s : St) : Prop :=
  s.ph ≤ 2 ∧ s.tgt ≤ 4 ∧
  (s.tgt = 3 → s.u = 0) ∧
  (s.tgt = 4 → s.u < s.sz) ∧
  (s.tgt ≤ 2 → s.ph = 2 ∨ (s.mems = [] ∧ s.u = 0)) ∧
  ((s.tgt = 3 ∨ s.tgt = 4) → s.offs.length = s.j + 1) ∧
  ((s.tgt = 3 ∨ s.tgt = 4) → s.mems.length = s.off + s.u)

theorem Struct.init : Struct init := by unfold Struct ScanModel.init; decide

/-- `afterNumber` is only ever called by `step` from `ph = 0` or `ph = 1` — a `ph = 2`
("done") state is a fixed point of `step`, never reaches here — so `hph2` (available at
both of `step`'s call sites) is needed to rule out the "already done" branch of `Struct`'s
`tgt ≤ 2` clause when `tgt` is 0 on entry. -/
theorem Struct.afterNumber_step {s : St} (h : Struct s) (hph2 : s.ph ≠ 2) (v : ℕ) :
    Struct (afterNumber s v) := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := h
  by_cases h0 : s.tgt = 0
  · simp_all [Struct, ScanModel.afterNumber]
  by_cases h1 : s.tgt = 1
  · simp_all [Struct, ScanModel.afterNumber]
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp_all [Struct, ScanModel.afterNumber]
    · have hbase := htgt2' (by omega)
      rcases hbase with hdone | ⟨hmnil, hu0⟩
      · exact absurd hdone hph2
      · simp only [Struct, ScanModel.afterNumber, h2, if_neg hm]
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;> intro _
        · simp
        · simp [hmnil, hu0]
  by_cases h3 : s.tgt = 3
  · have hu0 : s.u = 0 := hu3 h3
    have hmeq : s.mems.length = s.off := by have := hmems (h3 ▸ Or.inl rfl); omega
    by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [Struct, ScanModel.afterNumber, h3, hv, if_pos hjm, if_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro _; simp [List.length_append, hoffs (h3 ▸ Or.inl rfl)]
        · intro _; simpa using hmeq
      · simp only [Struct, ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro hc; omega
        · intro hc; omega
        · intro _; exact Or.inl trivial
        · intro h'; omega
        · intro h'; omega
    · simp only [Struct, ScanModel.afterNumber, h3, if_neg hv]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · intro hc; omega
      · intro hc; omega
      · intro h'; omega
      · intro _; simpa using hmeq
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have h4eq : s.tgt = 4 := by omega
    have husz : s.u < s.sz := hu4 h4eq
    by_cases hlt : s.u + 1 < s.sz
    · simp only [Struct, ScanModel.afterNumber, if_pos hlt]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · intro hc; omega
      · intro hc; omega
      · intro h'; omega
      · intro h'; omega
      · intro _
        simp [List.length_append]
        have := hmems (Or.inr h4eq)
        omega
    · have hszeq : s.sz = s.u + 1 := by omega
      by_cases hjm : s.j + 1 < s.m
      · simp only [Struct, ScanModel.afterNumber, if_neg hlt, if_pos hjm]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro hc; omega
        · intro hc; omega
        · intro h'; omega
        · intro _
          have ho := hoffs (Or.inr h4eq)
          simp [List.length_append, ho]
        · intro _
          have hm := hmems (Or.inr h4eq)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
      · simp only [Struct, ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro hc; omega
        · intro hc; omega
        · intro _; exact Or.inl trivial
        · intro h'; omega
        · intro h'; omega

theorem Struct.step_step {s : St} (h : Struct s) (b : ℕ) : Struct (step s b) := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := h
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · exact ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩
  · have hS : Struct s := ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩
    exact hS.afterNumber_step (by omega) 0
  · refine ⟨by simp, htgt, hu3, hu4, ?_, hoffs, hmems⟩
    intro hle
    rcases htgt2' hle with hdone | ⟨hmnil, hu0⟩
    · omega
    · exact Or.inr ⟨hmnil, hu0⟩
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]
      exact ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩
    · simp only [hii, if_false]
      have hS : Struct s := ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩
      exact hS.afterNumber_step (by omega) _
  · exact ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩

theorem Struct.run_step {s : St} (h : Struct s) (l : List ℕ) : Struct (ScanModel.run s l) := by
  induction l generalizing s with
  | nil => simpa using h
  | cons b bs ih => rw [run_cons]; exact ih (h.step_step b)

/-! ## The set index never reaches the set count while it is still in use

`Struct` alone does not say how `j` (the set currently being read) relates to `m` (the
declared set count) — only that `offs.length = j + 1` while `tgt ∈ {3, 4}`. `JLtM` is the
companion fact that `j < m` throughout that same phase, which is what turns "the last set
was just finished" (`¬ (j + 1 < m)`, i.e. `j + 1 ≥ m`) into "the last set was *exactly*
`m − 1`" (`j + 1 = m`) rather than merely a lower bound — needed below to show the array
`bridgeCopy` copies out of is exactly as long as `m` demands, for *any* tape, not only a
genuine encoding's. -/
def JLtM (s : St) : Prop := (s.tgt = 3 ∨ s.tgt = 4) → s.j < s.m

theorem JLtM.init : JLtM init := by unfold JLtM ScanModel.init; decide

theorem JLtM.afterNumber_step {s : St} (h : JLtM s) (hStruct : Struct s) (v : ℕ) :
    JLtM (afterNumber s v) := by
  obtain ⟨-, htgt, -, -, -, -, -⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · simp_all [JLtM, ScanModel.afterNumber]
  by_cases h1 : s.tgt = 1
  · simp_all [JLtM, ScanModel.afterNumber]
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp_all [JLtM, ScanModel.afterNumber]
    · simp only [JLtM, ScanModel.afterNumber, h2, if_neg hm]
      intro _; omega
  by_cases h3 : s.tgt = 3
  · by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [JLtM, ScanModel.afterNumber, h3, hv, if_pos hjm, if_true]
        intro _; omega
      · simp only [JLtM, ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        intro hc; omega
    · simp only [JLtM, ScanModel.afterNumber, h3, if_neg hv]
      intro _; exact h (Or.inl h3)
  · have h4eq : s.tgt = 4 := by omega
    by_cases hlt : s.u + 1 < s.sz
    · simp only [JLtM, ScanModel.afterNumber, if_pos hlt]
      intro _; exact h (Or.inr h4eq)
    · by_cases hjm : s.j + 1 < s.m
      · simp only [JLtM, ScanModel.afterNumber, if_neg hlt, if_pos hjm]
        intro _; omega
      · simp only [JLtM, ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        intro hc; omega

theorem JLtM.step_step {s : St} (h : JLtM s) (hStruct : Struct s) (b : ℕ) : JLtM (step s b) := by
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · exact h
  · exact h.afterNumber_step hStruct 0
  · exact h
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]; exact h
    · simp only [hii, if_false]; exact h.afterNumber_step hStruct _
  · exact h

/-- **At the moment the scan reaches "done", the offsets array is exactly `m + 1` long** —
for *any* tape, genuine encoding or not: this is what lets `bridgeCopy` read `"OFFS"[0..m]`
safely no matter what the input was, which is what makes the whole reduction total. Proved
by the same case split as `Struct.afterNumber_step`, using `Struct`'s own `offs.length =
j + 1` together with `JLtM`'s `j < m` to pin `j + 1 = m` exactly (not merely `≥`) in the two
genuine "last set" transitions, and closing every other branch by contradiction against
`hdone` (which only the three "done" branches can satisfy). -/
theorem offs_length_eq_succ_m_of_done {s : St} (hStruct : Struct s) (hJ : JLtM s) (v : ℕ)
    (hdone : (afterNumber s v).ph = 2) :
    (afterNumber s v).offs.length = (afterNumber s v).m + 1 := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · simp only [ScanModel.afterNumber, h0] at hdone; omega
  by_cases h1 : s.tgt = 1
  · simp only [ScanModel.afterNumber, h1] at hdone; omega
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp only [ScanModel.afterNumber, h2, if_pos hm]; simp [hm]
    · simp only [ScanModel.afterNumber, h2, if_neg hm] at hdone; omega
  by_cases h3 : s.tgt = 3
  · by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, h3, hv, if_pos hjm, if_true] at hdone; omega
      · have hjlt : s.j < s.m := hJ (Or.inl h3)
        have hoffslen : s.offs.length = s.j + 1 := hoffs (Or.inl h3)
        simp only [ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    · simp only [ScanModel.afterNumber, h3, if_neg hv] at hdone; omega
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have h4eq : s.tgt = 4 := by omega
    by_cases hlt : s.u + 1 < s.sz
    · simp only [ScanModel.afterNumber, if_pos hlt] at hdone; omega
    · by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, if_neg hlt, if_pos hjm] at hdone; omega
      · have hjlt : s.j < s.m := hJ (Or.inr h4eq)
        have hoffslen : s.offs.length = s.j + 1 := hoffs (Or.inr h4eq)
        simp only [ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

/-- **One more `step` preserves "the invariant holds once `ph` has reached `2`".** Either
`step` is a no-op (`s.ph` was already `2`, so nothing changes and the hypothesis restates
itself), or it genuinely dispatches through `afterNumber`, in which case a fresh `ph = 2`
can only come from `offs_length_eq_succ_m_of_done` directly — the same five-way case split as
`Struct.step_step`/`JLtM.step_step`, since it is exactly their proof of *which* branch calls
`afterNumber` at all. -/
theorem step_step_offs_length {s : St} (hStruct : Struct s) (hJ : JLtM s)
    (hpre : s.ph = 2 → s.offs.length = s.m + 1) (b : ℕ) :
    (step s b).ph = 2 → (step s b).offs.length = (step s b).m + 1 := by
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · intro hc; exact absurd hc (by simp_all)
  · exact offs_length_eq_succ_m_of_done hStruct hJ 0
  · intro hc; exact absurd hc (by simp_all)
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]; intro hc; exact absurd hc (by simp_all)
    · simp only [hii, if_false]
      exact offs_length_eq_succ_m_of_done hStruct hJ _
  · exact hpre

/-- **The invariant `offs.length = m + 1` holds whenever the scan, run from `init`, reaches
`"done"` — for *every* tape, genuine encoding or not.** Proved by folding
`step_step_offs_length` over the whole list: `init.ph = 0 ≠ 2` makes the seed hypothesis
vacuous, and each further `step` either preserves an already-`ph = 2` state (carrying the
invariant forward unchanged) or is the one step that first reaches it (where
`offs_length_eq_succ_m_of_done` supplies the invariant directly). This is the fact
`bridgeCopy`'s `"OFFS"[0 .. m]` read needs to be safe on a tape whose scan *does* finish but
is not a genuine encoding — the companion fact for a tape whose scan never finishes is
`totalProg`'s own `"ph" == 2` gate (`Ram/TotalProg.lean`), which this lemma exists to justify
skipping past. -/
theorem run_offs_length_of_done (l : List ℕ) (hdone : (run init l).ph = 2) :
    (run init l).offs.length = (run init l).m + 1 := by
  suffices h : ∀ s : St, Struct s → JLtM s → (s.ph = 2 → s.offs.length = s.m + 1) →
      (run s l).ph = 2 → (run s l).offs.length = (run s l).m + 1 by
    exact h init Struct.init JLtM.init (by simp [init]) hdone
  clear hdone
  intro s hStruct hJ hpre
  induction l generalizing s with
  | nil => simpa using hpre
  | cons b bs ih =>
    rw [run_cons]
    exact ih (step s b) (hStruct.step_step b) (hJ.step_step hStruct b)
      (step_step_offs_length hStruct hJ hpre b)

/-! ## The member-offset is untouched outside a set's own read

`Struct`'s `mems = [] ∧ u = 0` half of its `tgt ≤ 2` clause says nothing about `off`, so
nothing yet connects `mems.length` to `off` once the scan is `done` at `tgt ≤ 2` — needed for
the same reason `JLtM` was: `bridgeCopy` reads `"MEMS"[0 .. off]`, and without this, a
`tgt = 2, m = 0` "done" state (the empty-hitting-set-universe case) leaves `off` and
`mems.length` both merely inherited from whatever the scan carried in, with no invariant
forcing them equal. `OffPristine` is the companion fact, proved by the same four-theorem
induction template as `JLtM`. -/
def OffPristine (s : St) : Prop := s.tgt ≤ 2 → s.ph = 2 ∨ s.off = 0

theorem OffPristine.init : OffPristine init := by unfold OffPristine ScanModel.init; decide

/-- Mirrors `Struct.afterNumber_step`'s own need for `hph2`: `afterNumber` is only ever
called by `step` from `ph = 0` or `ph = 1`, so `hph2` is what turns `OffPristine`'s
`ph = 2 ∨ off = 0` disjunction into the `off = 0` half whenever `tgt ≤ 2` on entry. -/
theorem OffPristine.afterNumber_step {s : St} (h : OffPristine s) (hStruct : Struct s)
    (hph2 : s.ph ≠ 2) (v : ℕ) : OffPristine (afterNumber s v) := by
  obtain ⟨-, htgt, -, -, -, -, -⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · have hoff : s.off = 0 := (h (by omega)).resolve_left hph2
    simp_all [OffPristine, ScanModel.afterNumber]
  by_cases h1 : s.tgt = 1
  · have hoff : s.off = 0 := (h (by omega)).resolve_left hph2
    simp_all [OffPristine, ScanModel.afterNumber]
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp only [OffPristine, ScanModel.afterNumber, h2, if_pos hm]
      intro _; exact Or.inl trivial
    · simp only [OffPristine, ScanModel.afterNumber, h2, if_neg hm]
      intro hc; omega
  by_cases h3 : s.tgt = 3
  · by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [OffPristine, ScanModel.afterNumber, h3, hv, if_pos hjm, if_true]
        intro hc; omega
      · simp only [OffPristine, ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        intro _; exact Or.inl trivial
    · simp only [OffPristine, ScanModel.afterNumber, h3, if_neg hv]
      intro hc; omega
  · have h4eq : s.tgt = 4 := by omega
    by_cases hlt : s.u + 1 < s.sz
    · simp only [OffPristine, ScanModel.afterNumber, if_pos hlt]
      intro hc; omega
    · by_cases hjm : s.j + 1 < s.m
      · simp only [OffPristine, ScanModel.afterNumber, if_neg hlt, if_pos hjm]
        intro hc; omega
      · simp only [OffPristine, ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        intro _; exact Or.inl trivial

theorem OffPristine.step_step {s : St} (h : OffPristine s) (hStruct : Struct s) (b : ℕ) :
    OffPristine (step s b) := by
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · exact h
  · exact h.afterNumber_step hStruct (by omega) 0
  · show s.tgt ≤ 2 → (1 : ℕ) = 2 ∨ s.off = 0
    intro htgt; have hd := h htgt; omega
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]; exact h
    · simp only [hii, if_false]; exact h.afterNumber_step hStruct (by omega) _
  · exact h

/-- **At the moment the scan reaches "done", the members array is exactly as long as the
running offset says it should be** — for *any* tape, genuine encoding or not: the companion
fact to `offs_length_eq_succ_m_of_done`, needed for the same reason (`bridgeCopy` reads
`"MEMS"[0 .. off]`). Only the `tgt = 2, m = 0` branch (the empty-universe "done" state) needs
`OffPristine`; the `tgt = 3` and `tgt = 4` "done" branches both follow directly from
`Struct`'s own `u = 0` / `off + u` clauses, exactly as `hmeq` does in
`Struct.afterNumber_step`'s own `tgt = 3` case. -/
theorem mems_length_eq_off_of_done {s : St} (hStruct : Struct s) (hOP : OffPristine s)
    (hph2 : s.ph ≠ 2) (v : ℕ) (hdone : (afterNumber s v).ph = 2) :
    (afterNumber s v).mems.length = (afterNumber s v).off := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · simp only [ScanModel.afterNumber, h0] at hdone; omega
  by_cases h1 : s.tgt = 1
  · simp only [ScanModel.afterNumber, h1] at hdone; omega
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp only [ScanModel.afterNumber, h2, if_pos hm]
      rcases htgt2' (by omega) with hc | ⟨hmnil, -⟩
      · exact absurd hc hph2
      · have hoff0 : s.off = 0 := (hOP (by omega)).resolve_left hph2
        simp [hmnil, hoff0]
    · simp only [ScanModel.afterNumber, h2, if_neg hm] at hdone; omega
  by_cases h3 : s.tgt = 3
  · have hu0 : s.u = 0 := hu3 h3
    have hmeq : s.mems.length = s.off := by have := hmems (h3 ▸ Or.inl rfl); omega
    by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, h3, hv, if_pos hjm, if_true] at hdone; omega
      · simp only [ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        exact hmeq
    · simp only [ScanModel.afterNumber, h3, if_neg hv] at hdone; omega
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have h4eq : s.tgt = 4 := by omega
    have husz : s.u < s.sz := hu4 h4eq
    by_cases hlt : s.u + 1 < s.sz
    · simp only [ScanModel.afterNumber, if_pos hlt] at hdone; omega
    · have hszeq : s.sz = s.u + 1 := by omega
      by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, if_neg hlt, if_pos hjm] at hdone; omega
      · simp only [ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hm := hmems (Or.inr h4eq)
        omega

theorem step_step_mems_length {s : St} (hStruct : Struct s) (hOP : OffPristine s)
    (hpre : s.ph = 2 → s.mems.length = s.off) (b : ℕ) :
    (step s b).ph = 2 → (step s b).mems.length = (step s b).off := by
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · intro hc; exact absurd hc (by simp_all)
  · exact mems_length_eq_off_of_done hStruct hOP (by omega) 0
  · intro hc; exact absurd hc (by simp_all)
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]; intro hc; exact absurd hc (by simp_all)
    · simp only [hii, if_false]
      exact mems_length_eq_off_of_done hStruct hOP (by omega) _
  · exact hpre

/-- **The invariant `mems.length = off` holds whenever the scan, run from `init`, reaches
`"done"` — for *every* tape, genuine encoding or not.** The companion fact to
`run_offs_length_of_done`, proved the same way (folding `step_step_mems_length` over the
whole list). -/
theorem run_mems_length_of_done (l : List ℕ) (hdone : (run init l).ph = 2) :
    (run init l).mems.length = (run init l).off := by
  suffices h : ∀ s : St, Struct s → OffPristine s → (s.ph = 2 → s.mems.length = s.off) →
      (run s l).ph = 2 → (run s l).mems.length = (run s l).off by
    exact h init Struct.init OffPristine.init (by simp [init]) hdone
  clear hdone
  intro s hStruct hOP hpre
  induction l generalizing s with
  | nil => simpa using hpre
  | cons b bs ih =>
    rw [run_cons]
    exact ih (step s b) (hStruct.step_step b) (hOP.step_step hStruct b)
      (step_step_mems_length hStruct hOP hpre b)

/-- **At the moment the scan reaches "done", the offsets array's own entry at index `m` is
exactly the running member-offset** — the fact `bridgeCopy_spec_generic`'s own `foff m0 = L0`
precondition demands (`foff := fun j => s.offs.getD j 0`, `m0 := s.m`, `L0 := s.off` — or,
via `mems_length_eq_off_of_done`, `L0 := s.mems.length`, since the two agree once done). Needs
all three of `Struct`, `JLtM` (to pin the append index `j + 1 = m` exactly, exactly as
`offs_length_eq_succ_m_of_done` does) and `OffPristine` (for the same `tgt = 2, m = 0`
"empty-universe" branch `mems_length_eq_off_of_done` needed it for) — the `tgt = 3`/`tgt = 4`
"done" branches just append `off`/`off + sz` as the array's own last entry, so once the index
is pinned to that entry, the equality is immediate. -/
theorem offs_last_eq_off_of_done {s : St} (hStruct : Struct s) (hJ : JLtM s) (hOP : OffPristine s)
    (hph2 : s.ph ≠ 2) (v : ℕ) (hdone : (afterNumber s v).ph = 2) :
    (afterNumber s v).offs.getD (afterNumber s v).m 0 = (afterNumber s v).off := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · simp only [ScanModel.afterNumber, h0] at hdone; omega
  by_cases h1 : s.tgt = 1
  · simp only [ScanModel.afterNumber, h1] at hdone; omega
  by_cases h2 : s.tgt = 2
  · by_cases hm : s.m = 0
    · simp only [ScanModel.afterNumber, h2, if_pos hm]
      rcases htgt2' (by omega) with hc | ⟨-, -⟩
      · exact absurd hc hph2
      · have hoff0 : s.off = 0 := (hOP (by omega)).resolve_left hph2
        simp [hm, hoff0]
    · simp only [ScanModel.afterNumber, h2, if_neg hm] at hdone; omega
  by_cases h3 : s.tgt = 3
  · by_cases hv : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, h3, hv, if_pos hjm, if_true] at hdone; omega
      · have hjlt : s.j < s.m := hJ (Or.inl h3)
        have hoffslen : s.offs.length = s.j + 1 := hoffs (Or.inl h3)
        have hidx : s.m = s.offs.length := by omega
        simp only [ScanModel.afterNumber, h3, hv, if_neg hjm, if_true]
        rw [hidx]; simp
    · simp only [ScanModel.afterNumber, h3, if_neg hv] at hdone; omega
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have h4eq : s.tgt = 4 := by omega
    by_cases hlt : s.u + 1 < s.sz
    · simp only [ScanModel.afterNumber, if_pos hlt] at hdone; omega
    · by_cases hjm : s.j + 1 < s.m
      · simp only [ScanModel.afterNumber, if_neg hlt, if_pos hjm] at hdone; omega
      · have hjlt : s.j < s.m := hJ (Or.inr h4eq)
        have hoffslen : s.offs.length = s.j + 1 := hoffs (Or.inr h4eq)
        have hidx : s.m = s.offs.length := by omega
        simp only [ScanModel.afterNumber, if_neg hlt, if_neg hjm]
        rw [hidx]; simp

theorem step_step_offs_last {s : St} (hStruct : Struct s) (hJ : JLtM s) (hOP : OffPristine s)
    (hpre : s.ph = 2 → s.offs.getD s.m 0 = s.off) (b : ℕ) :
    (step s b).ph = 2 → (step s b).offs.getD (step s b).m 0 = (step s b).off := by
  unfold ScanModel.step
  split_ifs with h1 h2 h3 h4
  · intro hc; exact absurd hc (by simp_all)
  · exact offs_last_eq_off_of_done hStruct hJ hOP (by omega) 0
  · intro hc; exact absurd hc (by simp_all)
  · by_cases hii : s.ii + 1 < s.cc
    · simp only [hii, if_true]; intro hc; exact absurd hc (by simp_all)
    · simp only [hii, if_false]
      exact offs_last_eq_off_of_done hStruct hJ hOP (by omega) _
  · exact hpre

/-- **The invariant `offs.getD m 0 = off` holds whenever the scan, run from `init`, reaches
`"done"` — for *every* tape, genuine encoding or not.** The companion fact to
`run_offs_length_of_done`/`run_mems_length_of_done`, proved the same way. -/
theorem run_offs_last_eq_off_of_done (l : List ℕ) (hdone : (run init l).ph = 2) :
    (run init l).offs.getD (run init l).m 0 = (run init l).off := by
  suffices h : ∀ s : St, Struct s → JLtM s → OffPristine s →
      (s.ph = 2 → s.offs.getD s.m 0 = s.off) →
      (run s l).ph = 2 → (run s l).offs.getD (run s l).m 0 = (run s l).off by
    exact h init Struct.init JLtM.init OffPristine.init (by simp [init]) hdone
  clear hdone
  intro s hStruct hJ hOP hpre
  induction l generalizing s with
  | nil => simpa using hpre
  | cons b bs ih =>
    rw [run_cons]
    exact ih (step s b) (hStruct.step_step b) (hJ.step_step hStruct b) (hOP.step_step hStruct b)
      (step_step_offs_last hStruct hJ hOP hpre b)

/-! ## Reading one self-delimited number -/

theorem run_ones (s0 : St) (cc0 c : ℕ) (rest : List ℕ) :
    run { s0 with ph := 0, cc := cc0 } (List.replicate c 1 ++ rest) =
      run { s0 with ph := 0, cc := cc0 + c } rest := by
  induction c generalizing cc0 with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.cons_append, run_cons]
    have hstep : step { s0 with ph := 0, cc := cc0 } 1 = { s0 with ph := 0, cc := cc0 + 1 } := by
      simp [step]
    rw [hstep, ih (cc0 + 1)]
    congr 2
    omega

/-- `afterNumber` reads no field but `tgt` from its state besides what it explicitly names,
so overwriting the scan's `ph`/`cc`/`ii`/`vv` first — the fields a mid-digit-read state
carries and every `afterNumber` branch already resets — changes nothing. -/
theorem afterNumber_congr (s0 : St) (ph0 cc0 ii0 vv0 v : ℕ) :
    afterNumber { s0 with ph := ph0, cc := cc0, ii := ii0, vv := vv0 } v = afterNumber s0 v := by
  simp only [afterNumber]

/-- Reading the `ds.length` digit bits of a number, starting at digit index `i0` with the
acc value of the first `i0` digits already accumulated, against a base state `s0`
(whose own `ph`/`cc`/`ii`/`vv` are irrelevant and not assumed). -/
theorem run_digits (s0 : St) (v : ℕ) : ∀ (i0 acc : ℕ),
    acc = ∑ i ∈ Finset.range i0, digit v i * 2 ^ i →
    ∀ (ds : List ℕ), ds ≠ [] → ∀ (cc : ℕ), cc = i0 + ds.length →
    (∀ t < ds.length, ds.getD t 0 = digit v (i0 + t)) →
    ∀ (rest : List ℕ),
      run { s0 with ph := 1, cc := cc, ii := i0, vv := acc } (ds ++ rest) =
        run (afterNumber s0 (∑ i ∈ Finset.range (i0 + ds.length), digit v i * 2 ^ i)) rest := by
  intro i0 acc hpartial ds
  induction ds generalizing i0 acc with
  | nil => intro h; exact absurd rfl h
  | cons b bs ih =>
    intro _ cc hcc hds rest
    have hb0 : (b :: bs).getD 0 0 = digit v (i0 + 0) := hds 0 (by simp)
    have hb : b = digit v i0 := by simpa using hb0
    rw [List.cons_append, run_cons]
    have hstep : step { s0 with ph := 1, cc := cc, ii := i0, vv := acc } b =
        if i0 + 1 < cc then { s0 with ph := 1, cc := cc, ii := i0 + 1, vv := acc + b * 2 ^ i0 }
        else afterNumber s0 (acc + b * 2 ^ i0) := by
      by_cases hlt : i0 + 1 < cc
      · simp [step, hlt]
      · simp [step, hlt, afterNumber_congr]
    by_cases hbs : bs = []
    · subst hbs
      have hcc' : cc = i0 + 1 := by simpa using hcc
      rw [hstep, if_neg (by omega)]
      have hval : (∑ i ∈ Finset.range (i0 + [b].length), digit v i * 2 ^ i) = acc + b * 2 ^ i0 := by
        simp only [List.length_cons, List.length_nil]
        rw [Finset.sum_range_succ, hpartial, hb]
      rw [hval]
      simp
    · have hbslen : 0 < bs.length := by
        rcases bs with _ | ⟨b', bs'⟩
        · exact absurd rfl hbs
        · simp
      have hlen : cc = (i0 + 1) + bs.length := by
        rw [hcc]; simp only [List.length_cons]; omega
      rw [hstep, if_pos (by omega)]
      have hvv' : acc + b * 2 ^ i0 = ∑ i ∈ Finset.range (i0 + 1), digit v i * 2 ^ i := by
        rw [Finset.sum_range_succ, hpartial, hb]
      have hds' : ∀ t < bs.length, bs.getD t 0 = digit v (i0 + 1 + t) := by
        intro t ht
        have hh := hds (t + 1) (by simp only [List.length_cons]; omega)
        have heq : (b :: bs).getD (t + 1) 0 = bs.getD t 0 := by simp
        rw [heq] at hh
        rw [hh]
        congr 1
        omega
      have hres := ih (i0 + 1) (acc + b * 2 ^ i0) hvv' hbs cc hlen hds' rest
      rw [hres]
      have harg : (i0 + 1) + bs.length = i0 + (b :: bs).length := by
        simp only [List.length_cons]; omega
      rw [harg]

/-- **Reading one self-delimited number, from a fresh `cc = 0`.** -/
theorem run_bitsNat (s : St) (hph : s.ph = 0) (hcc : s.cc = 0) (v : ℕ) (rest : List ℕ) :
    run s (bitsNat v ++ rest) = run (afterNumber s v) rest := by
  have hs : ({ s with ph := 0, cc := 0 } : St) = s := by
    obtain ⟨ph, tgt, cc, ii, vv, n, m, k, j, u, sz, off, offs, mems⟩ := s
    simp_all
  have hones : run s (List.replicate v.size 1) = { s with ph := 0, cc := v.size } := by
    have h := run_ones s 0 v.size ([] : List ℕ)
    rw [hs] at h
    simpa using h
  unfold bitsNat
  rw [List.append_assoc, List.append_assoc, run_append, hones]
  rcases Nat.eq_zero_or_pos v.size with hv0 | hv0
  · have hb : (List.range v.size).map (digit v) = [] := by rw [hv0]; simp
    have h0 : v = 0 := Nat.size_eq_zero.mp hv0
    rw [hb]
    simp only [List.nil_append, List.singleton_append, run_cons]
    have hstep : step { s with ph := 0, cc := v.size } 0 = afterNumber s 0 := by
      have heq : step { s with ph := 0, cc := v.size } 0
          = afterNumber { s with ph := 0, cc := v.size } 0 := by simp [step, hv0]
      rw [heq, afterNumber_congr]
    rw [hstep, h0]
  · have hstep : step { s with ph := 0, cc := v.size } 0
        = { s with ph := 1, cc := v.size, ii := 0, vv := 0 } := by
      simp [step, hv0.ne']
    simp only [List.singleton_append, run_cons, hstep]
    have hds : ∀ t < ((List.range v.size).map (digit v)).length,
        ((List.range v.size).map (digit v)).getD t 0 = digit v (0 + t) := by
      intro t ht
      simp only [List.length_map, List.length_range] at ht
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
      simp
    have hlen : ((List.range v.size).map (digit v)).length = v.size := by simp
    have hne : (List.range v.size).map (digit v) ≠ [] := by
      intro hc
      have := congrArg List.length hc
      rw [hlen] at this; simp at this; omega
    have hrun := run_digits s v 0 0 (by simp) ((List.range v.size).map (digit v)) hne v.size
      (by rw [hlen, Nat.zero_add]) hds rest
    rw [hrun]
    have hfinal : (∑ i ∈ Finset.range (0 + ((List.range v.size).map (digit v)).length),
        digit v i * 2 ^ i) = v := by
      rw [hlen, Nat.zero_add]
      exact sum_digit v
    rw [hfinal]

/-! ## Reading the members of one set -/

/-- Reading the remaining `members` of set `J` (out of `M` sets, of size `SZ`), having
already read `u_cur` of them into `mems_cur`. The last one dispatches exactly as
`afterNumber`'s `tgt = 4` case does: on to the next set, or done. -/
theorem run_members (s0 : St) (M SZ J : ℕ) (hm : s0.m = M) (hsz : s0.sz = SZ) (hj : s0.j = J) :
    ∀ (u_cur : ℕ) (mems_cur members : List ℕ), u_cur + members.length = SZ → members ≠ [] →
    ∀ (rest : List ℕ),
      run { s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, u := u_cur, mems := mems_cur }
          (members.flatMap bitsNat ++ rest) =
        run (if J + 1 < M then
              { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J + 1, u := 0, off := s0.off + SZ, offs := s0.offs ++ [s0.off + SZ], mems := mems_cur ++ members }
            else
              { s0 with ph := 2, cc := 0, tgt := 0, ii := 0, vv := 0, sz := 0, u := 0, off := s0.off + SZ, offs := s0.offs ++ [s0.off + SZ], mems := mems_cur ++ members })
          rest := by
  intro u_cur mems_cur members
  induction members generalizing u_cur mems_cur with
  | nil => intro h hne; exact absurd rfl hne
  | cons v vs ih =>
    intro hlen _ rest
    rw [List.flatMap_cons, List.append_assoc, run_bitsNat _ rfl rfl v]
    by_cases hvs : vs = []
    · subst hvs
      have hu' : u_cur + 1 = SZ := by simpa using hlen
      have hstep : afterNumber { s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, u := u_cur, mems := mems_cur } v
          = if J + 1 < M then
              { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J + 1, u := 0, off := s0.off + SZ, offs := s0.offs ++ [s0.off + SZ], mems := mems_cur ++ [v] }
            else
              { s0 with ph := 2, cc := 0, tgt := 0, ii := 0, vv := 0, sz := 0, u := 0, off := s0.off + SZ, offs := s0.offs ++ [s0.off + SZ], mems := mems_cur ++ [v] } := by
        simp only [afterNumber, hm, hsz, hj, hu', if_neg (show ¬ SZ < SZ by omega)]
      rw [hstep]
      simp
    · have hvslen : 0 < vs.length := by
        rcases vs with _ | ⟨v', vs'⟩
        · exact absurd rfl hvs
        · simp
      have hlen' : (u_cur + 1) + vs.length = SZ := by
        simp only [List.length_cons] at hlen; omega
      have hstep : afterNumber { s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, u := u_cur, mems := mems_cur } v
          = { s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, u := u_cur + 1, mems := mems_cur ++ [v] } := by
        simp only [afterNumber, hsz, if_pos (show u_cur + 1 < SZ by omega)]
      rw [hstep]
      have hres := ih (u_cur + 1) (mems_cur ++ [v]) hlen' hvs rest
      rw [hres]
      have hma : mems_cur ++ [v] ++ vs = mems_cur ++ (v :: vs) := by
        simp [List.append_assoc]
      rw [hma]

/-! ## Reading the family's `m` sets -/

/-- One set's contribution to the target state: its size dispatches to the empty-set
branch of `afterNumber`'s `tgt = 3` case, or (via `run_members`) to its `tgt = 4` case
once its members are read. -/
def setStep (M : ℕ) (s : St) (b : ℕ × List ℕ) : St :=
  if s.j + 1 < M then
    { s with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := s.j + 1, u := 0, off := s.off + b.1, offs := s.offs ++ [s.off + b.1], mems := s.mems ++ b.2 }
  else
    { s with ph := 2, cc := 0, tgt := 0, ii := 0, vv := 0, sz := 0, u := 0, off := s.off + b.1, offs := s.offs ++ [s.off + b.1], mems := s.mems ++ b.2 }

/-- Reading the remaining sets `J0, …, M - 1`, having already read `sizes.take J0` and
their members into `s0.offs`/`s0.mems`. `blocks` is that remaining tail, each set as its
size and its members — and, since a set's members really are as many as its declared
size, `b.2.length = b.1` for each. -/
theorem run_sets (s0 : St) (M : ℕ) (hm : s0.m = M) :
    ∀ (J0 : ℕ), s0.j = J0 → ∀ (blocks : List (ℕ × List ℕ)), J0 + blocks.length = M →
    blocks ≠ [] → (∀ b ∈ blocks, b.2.length = b.1) →
    ∀ (rest : List ℕ),
      run { s0 with ph := 0, cc := 0, tgt := 3 }
          ((blocks.flatMap fun b => bitsNat b.1 ++ b.2.flatMap bitsNat) ++ rest) =
        run (blocks.foldl (setStep M) { s0 with ph := 0, cc := 0, tgt := 3 }) rest := by
  intro J0 hJ0 blocks
  induction blocks generalizing J0 s0 with
  | nil => intro h hne; exact absurd rfl hne
  | cons b bs ih =>
    intro hlen _ hwf rest
    rw [List.flatMap_cons, List.foldl_cons]
    have hph0 : ({ s0 with ph := 0, cc := 0, tgt := 3 } : St).ph = 0 := rfl
    have hcc0 : ({ s0 with ph := 0, cc := 0, tgt := 3 } : St).cc = 0 := rfl
    have hb2len : b.2.length = b.1 := hwf b (by simp)
    have hbslen : ∀ b' ∈ bs, b'.2.length = b'.1 := fun b' hb' => hwf b' (by simp [hb'])
    rw [show ((bitsNat b.1 ++ b.2.flatMap bitsNat) ++ bs.flatMap (fun b => bitsNat b.1 ++ b.2.flatMap bitsNat) ++ rest)
        = bitsNat b.1 ++ (b.2.flatMap bitsNat ++ (bs.flatMap (fun b => bitsNat b.1 ++ b.2.flatMap bitsNat) ++ rest))
        by simp [List.append_assoc]]
    rw [run_bitsNat _ hph0 hcc0 b.1]
    have hbsM : J0 + 1 + bs.length = M := by
      simp only [List.length_cons] at hlen; omega
    by_cases hb0 : b.1 = 0
    · have hb2 : (b.2 : List ℕ) = [] := by
        rw [← List.length_eq_zero_iff, hb2len, hb0]
      have hstep : afterNumber { s0 with ph := 0, cc := 0, tgt := 3 } b.1
          = setStep M { s0 with ph := 0, cc := 0, tgt := 3 } b := by
        simp only [afterNumber, hJ0, hb0, hm, setStep]
        rw [hb2]
        simp
      rw [hb2, List.flatMap_nil, List.nil_append, hstep]
      have hs1eq : setStep M { s0 with ph := 0, cc := 0, tgt := 3 } b =
          if J0 + 1 < M then
            { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J0 + 1, u := 0, off := s0.off, offs := s0.offs ++ [s0.off], mems := s0.mems }
          else
            { s0 with ph := 2, cc := 0, tgt := 0, ii := 0, vv := 0, sz := 0, u := 0, off := s0.off, offs := s0.offs ++ [s0.off], mems := s0.mems } := by
        unfold setStep; simp [hJ0, hb0, hb2]
      rw [hs1eq]
      by_cases hbs : bs = []
      · subst hbs
        have hJM : ¬ J0 + 1 < M := by simp only [List.length_nil] at hbsM; omega
        rw [if_neg hJM, List.foldl_nil]
        rfl
      · have hbslen0 : 0 < bs.length := by
          rcases bs with _ | ⟨b', bs'⟩
          · exact absurd rfl hbs
          · simp
        have hJM : J0 + 1 < M := by omega
        rw [if_pos hJM]
        refine ih { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J0 + 1, u := 0, off := s0.off, offs := s0.offs ++ [s0.off], mems := s0.mems } ?_ (J0 + 1) ?_ hbsM hbs hbslen rest
        · exact hm
        · rfl
    · have hb2ne : b.2 ≠ [] := by
        rw [← List.length_pos_iff, hb2len]; omega
      have hstep : afterNumber { s0 with ph := 0, cc := 0, tgt := 3 } b.1
          = { s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, sz := b.1, u := 0 } := by
        simp [afterNumber, hb0]
      rw [hstep]
      set s1 := ({ s0 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, sz := b.1, u := 0 } : St) with hs1
      have hM : s1.m = M := by rw [hs1]; exact hm
      have hSZ : s1.sz = b.1 := by rw [hs1]
      have hJ : s1.j = J0 := by rw [hs1]; exact hJ0
      have hoff : s1.off = s0.off := by rw [hs1]
      have hoffs : s1.offs = s0.offs := by rw [hs1]
      have hmems : s1.mems = s0.mems := by rw [hs1]
      have hres := run_members s1 M b.1 J0 hM hSZ hJ 0 s0.mems b.2 (by simpa using hb2len) hb2ne
        (List.flatMap (fun b => bitsNat b.1 ++ b.2.flatMap bitsNat) bs ++ rest)
      rw [← hmems] at hres
      have hcollapse : ({ s1 with ph := 0, cc := 0, tgt := 4, ii := 0, vv := 0, u := 0, mems := s1.mems } : St) = s1 := rfl
      rw [hcollapse] at hres
      rw [hres, hoff, hoffs]
      set s2 := setStep M { s0 with ph := 0, cc := 0, tgt := 3 } b with hs2
      have hs2eq : s2 = (if J0 + 1 < M then
            { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J0 + 1, u := 0, off := s0.off + b.1, offs := s0.offs ++ [s0.off + b.1], mems := s0.mems ++ b.2 }
          else
            { s0 with ph := 2, cc := 0, tgt := 0, ii := 0, vv := 0, sz := 0, u := 0, off := s0.off + b.1, offs := s0.offs ++ [s0.off + b.1], mems := s0.mems ++ b.2 }) := by
        rw [hs2]; unfold setStep; simp [hJ0]
      rw [hs2eq]
      by_cases hbs : bs = []
      · subst hbs
        have hJM : ¬ J0 + 1 < M := by simp only [List.length_nil] at hbsM; omega
        rw [if_neg hJM, List.foldl_nil]
        rfl
      · have hbslen0 : 0 < bs.length := by
          rcases bs with _ | ⟨b', bs'⟩
          · exact absurd rfl hbs
          · simp
        have hJM : J0 + 1 < M := by omega
        rw [if_pos hJM]
        refine ih { s0 with ph := 0, cc := 0, tgt := 3, ii := 0, vv := 0, sz := 0, j := J0 + 1, u := 0, off := s0.off + b.1, offs := s0.offs ++ [s0.off + b.1], mems := s0.mems ++ b.2 } ?_ (J0 + 1) ?_ hbsM hbs hbslen rest
        · exact hm
        · rfl

/-! ## What `setStep`'s fold accumulates, in closed form -/

/-- Every partial-sum list begins with `0`, so it is its own head-and-tail. -/
theorem partialSums_eq_cons_tail (l : List ℕ) : l.partialSums = 0 :: l.partialSums.tail := by
  rcases l with _ | ⟨a, l'⟩
  · simp
  · rw [Lax496464Proofs.Ram.PartialSums.partialSums_cons]; simp

theorem foldl_setStep_fields (M : ℕ) : ∀ (s0 : St) (blocks : List (ℕ × List ℕ)),
    (blocks.foldl (setStep M) s0).n = s0.n ∧
    (blocks.foldl (setStep M) s0).m = s0.m ∧
    (blocks.foldl (setStep M) s0).k = s0.k ∧
    (blocks.foldl (setStep M) s0).mems = s0.mems ++ blocks.flatMap Prod.snd ∧
    (blocks.foldl (setStep M) s0).offs =
      s0.offs ++ ((blocks.map Prod.fst).partialSums.map (s0.off + ·)).tail := by
  intro s0 blocks
  induction blocks generalizing s0 with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons]
    have hn : (setStep M s0 b).n = s0.n := by unfold setStep; split_ifs <;> rfl
    have hm : (setStep M s0 b).m = s0.m := by unfold setStep; split_ifs <;> rfl
    have hk : (setStep M s0 b).k = s0.k := by unfold setStep; split_ifs <;> rfl
    have hoff : (setStep M s0 b).off = s0.off + b.1 := by unfold setStep; split_ifs <;> rfl
    have hoffs : (setStep M s0 b).offs = s0.offs ++ [s0.off + b.1] := by
      unfold setStep; split_ifs <;> rfl
    have hmems : (setStep M s0 b).mems = s0.mems ++ b.2 := by unfold setStep; split_ifs <;> rfl
    obtain ⟨ihn, ihm, ihk, ihmems, ihoffs⟩ := ih (setStep M s0 b)
    rw [hoff] at ihoffs
    refine ⟨by rw [ihn, hn], by rw [ihm, hm], by rw [ihk, hk], ?_, ?_⟩
    · rw [ihmems, hmems, List.append_assoc]
      simp [List.flatMap_cons]
    · rw [ihoffs, hoffs, List.append_assoc]
      congr 1
      set L := (bs.map Prod.fst).partialSums.map ((s0.off + b.1) + ·) with hLdef
      have hL : L = (s0.off + b.1) :: L.tail := by
        conv_lhs => rw [hLdef, partialSums_eq_cons_tail (bs.map Prod.fst)]
        rw [List.map_cons, Nat.add_zero, hLdef, List.map_tail]
      have hrhs_final : (((b :: bs).map Prod.fst).partialSums.map (s0.off + ·)).tail = L := by
        rw [List.map_cons, Lax496464Proofs.Ram.PartialSums.partialSums_cons, List.map_cons, Nat.add_zero, List.tail_cons,
          hLdef, List.map_map]
        apply List.map_congr_left
        intro x _
        simp only [Function.comp]
        omega
      rw [hrhs_final]
      conv_rhs => rw [hL]
      rw [List.singleton_append]

/-- Folding through every remaining set (`s0.j + blocks.length = M`, `blocks` nonempty)
always ends done. -/
theorem foldl_setStep_ph (M : ℕ) : ∀ (s0 : St) (blocks : List (ℕ × List ℕ)),
    s0.j + blocks.length = M → blocks ≠ [] → (blocks.foldl (setStep M) s0).ph = 2 := by
  intro s0 blocks
  induction blocks generalizing s0 with
  | nil => intro _ h; exact absurd rfl h
  | cons b bs ih =>
    intro hlen _
    rw [List.foldl_cons]
    by_cases hbs : bs = []
    · subst hbs
      have hj : ¬ s0.j + 1 < M := by simp only [List.length_cons, List.length_nil] at hlen; omega
      have hstep : setStep M s0 b = { s0 with ph := 2, tgt := 0, cc := 0, sz := 0, u := 0, ii := 0, vv := 0, off := s0.off + b.1, offs := s0.offs ++ [s0.off + b.1], mems := s0.mems ++ b.2 } := by
        unfold setStep; rw [if_neg hj]
      rw [hstep, List.foldl_nil]
    · have hbslen : 0 < bs.length := by
        rcases bs with _ | ⟨b', bs'⟩
        · exact absurd rfl hbs
        · simp
      have hj : s0.j + 1 < M := by simp only [List.length_cons] at hlen; omega
      have hstepj : (setStep M s0 b).j = s0.j + 1 := by unfold setStep; rw [if_pos hj]
      have hlen' : (setStep M s0 b).j + bs.length = M := by
        rw [hstepj]; simp only [List.length_cons] at hlen; omega
      exact ih (setStep M s0 b) hlen' hbs

/-! ## The scan, completed on a genuine encoding -/

/-- The blocks a genuine instance's bits present to `run_sets`: each set's size and its
members, in the order of the universe of sets. -/
def blocksOf (P : Instance) : List (ℕ × List ℕ) :=
  (List.finRange P.m).map fun j => ((P.F j).card, (P.members j).map Fin.val)

theorem blocksOf_map_fst (P : Instance) : (blocksOf P).map Prod.fst = sizes P := by
  unfold blocksOf sizes
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

theorem blocksOf_flatMap_snd (P : Instance) : (blocksOf P).flatMap Prod.snd = membersOf P := by
  unfold blocksOf membersOf
  rw [List.flatMap_map]

theorem length_blocksOf (P : Instance) : (blocksOf P).length = P.m := by
  simp [blocksOf]

theorem wf_blocksOf (P : Instance) : ∀ b ∈ blocksOf P, b.2.length = b.1 := by
  intro b hb
  simp only [blocksOf, List.mem_map] at hb
  obtain ⟨j, -, rfl⟩ := hb
  simp [length_members]

theorem natBits_append (l l' : List Bool) : natBits (l ++ l') = natBits l ++ natBits l' := by
  simp [natBits]

theorem natBits_flatMap {α : Type} (l : List α) (f : α → List Bool) :
    natBits (l.flatMap f) = l.flatMap (fun a => natBits (f a)) := by
  simp only [natBits, List.map_flatMap]

/-- **The bits of a genuine encoding, as a header of three numbers followed by the
blocks.** -/
theorem natBits_encodeInstance (P : Instance) (k : ℕ) :
    natBits (encodeInstance P k) =
      bitsNat P.n ++ bitsNat P.m ++ bitsNat k ++
        (blocksOf P).flatMap (fun b => bitsNat b.1 ++ b.2.flatMap bitsNat) := by
  unfold encodeInstance
  rw [natBits_append, natBits_append, natBits_append, natBits_encodeNat, natBits_encodeNat,
    natBits_encodeNat]
  congr 1
  rw [natBits_flatMap]
  unfold blocksOf
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  rw [natBits_append, natBits_encodeNat]
  congr 1
  simp only [bind_pure_comp]
  rw [show (Fin.val <$> P.members j) = (P.members j).map Fin.val from rfl, natBits_flatMap,
    List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  exact natBits_encodeNat i

/-- **Completeness.** Run on the bits of a genuine encoding, the scan reaches `done` having
recovered exactly `n`, `m`, `k`, and `csrWord`'s `offs`/`mems`. -/
theorem run_encodeInstance (P : Instance) (k : ℕ) :
    (run init (natBits (encodeInstance P k))).ph = 2 ∧
    (run init (natBits (encodeInstance P k))).n = P.n ∧
    (run init (natBits (encodeInstance P k))).m = P.m ∧
    (run init (natBits (encodeInstance P k))).k = k ∧
    (run init (natBits (encodeInstance P k))).offs = offsetsOf P ∧
    (run init (natBits (encodeInstance P k))).mems = membersOf P := by
  rw [natBits_encodeInstance]
  simp only [List.append_assoc]
  rw [run_bitsNat init rfl rfl]
  set s1 := afterNumber init P.n with hs1
  have hs1ph : s1.ph = 0 := by rw [hs1]; rfl
  have hs1cc : s1.cc = 0 := by rw [hs1]; rfl
  have hs1n : s1.n = P.n := by rw [hs1]; rfl
  have hs1mems : s1.mems = [] := by rw [hs1]; rfl
  rw [run_bitsNat s1 hs1ph hs1cc]
  set s2 := afterNumber s1 P.m with hs2
  have hs2ph : s2.ph = 0 := by rw [hs2]; rfl
  have hs2cc : s2.cc = 0 := by rw [hs2]; rfl
  have hs2n : s2.n = P.n := by rw [hs2]; rw [← hs1n]; rfl
  have hs2m : s2.m = P.m := by rw [hs2]; rfl
  have hs2mems : s2.mems = [] := by rw [hs2]; rw [← hs1mems]; rfl
  have hs2tgt : s2.tgt = 2 := by rw [hs2]; rfl
  rw [run_bitsNat s2 hs2ph hs2cc]
  rcases Nat.eq_zero_or_pos P.m with hP0 | hPpos
  · have hs2m0 : s2.m = 0 := by rw [hs2m, hP0]
    have hstep : afterNumber s2 k = { s2 with k := k, ph := 2, tgt := 0, cc := 0, sz := 0, offs := [0], ii := 0, vv := 0 } := by
      unfold afterNumber; rw [hs2tgt, hs2m0]; simp
    rw [hstep]
    have hfr : List.finRange P.m = [] := by
      rw [← List.length_eq_zero_iff, List.length_finRange]; exact hP0
    have hblocks0 : blocksOf P = [] := by unfold blocksOf; rw [hfr]; simp
    rw [hblocks0, List.flatMap_nil, run_nil]
    have hoffs0 : offsetsOf P = [0] := by
      unfold offsetsOf sizes; rw [hfr]; simp
    have hmems0 : membersOf P = [] := by
      unfold membersOf; rw [hfr]; simp
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
    · show s2.n = P.n; exact hs2n
    · show s2.m = P.m; exact hs2m
    · show ([0] : List ℕ) = offsetsOf P; exact hoffs0.symm
    · show s2.mems = membersOf P; rw [hs2mems, hmems0]
  · have hne : ¬ s2.m = 0 := by rw [hs2m]; omega
    have hstep : afterNumber s2 k = { s2 with k := k, ph := 0, tgt := 3, cc := 0, sz := 0, j := 0, off := 0, offs := [0], ii := 0, vv := 0 } := by
      unfold afterNumber
      simp only [hs2tgt, if_neg hne]
    rw [hstep]
    set s3 := ({ s2 with k := k, ph := 0, tgt := 3, cc := 0, sz := 0, j := 0, off := 0, offs := [0], ii := 0, vv := 0 } : St) with hs3
    have hs3m : s3.m = P.m := by rw [hs3]; exact hs2m
    have hs3j : s3.j = 0 := by rw [hs3]
    have hlen : (0 : ℕ) + (blocksOf P).length = P.m := by
      rw [length_blocksOf]; omega
    have hne : blocksOf P ≠ [] := by
      rw [← List.length_pos_iff, length_blocksOf]; exact hPpos
    have hwf : ∀ b ∈ blocksOf P, b.2.length = b.1 := wf_blocksOf P
    have hres := run_sets s3 P.m hs3m 0 hs3j (blocksOf P) hlen hne hwf ([] : List ℕ)
    rw [List.append_nil] at hres
    have hcollapse : ({ s3 with ph := 0, cc := 0, tgt := 3 } : St) = s3 := rfl
    rw [hcollapse] at hres
    rw [hres, run_nil]
    obtain ⟨hfn, hfm, hfk, hfmems, hfoffs⟩ := foldl_setStep_fields P.m s3 (blocksOf P)
    have hfph := foldl_setStep_ph P.m s3 (blocksOf P) (by rw [hs3j]; simpa using hlen) hne
    refine ⟨hfph, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfn, hs3]; exact hs2n
    · rw [hfm, hs3m]
    · rw [hfk, hs3]
    · rw [hfoffs]
      have hs3offs : s3.offs = [0] := by rw [hs3]
      have hs3off : s3.off = 0 := by rw [hs3]
      rw [hs3offs, hs3off]
      simp only [Nat.zero_add]
      rw [blocksOf_map_fst]
      unfold offsetsOf
      rw [partialSums_eq_cons_tail (sizes P)]
      simp
    · have hs3mems : s3.mems = [] := by rw [hs3]; exact hs2mems
      rw [hfmems, hs3mems, blocksOf_flatMap_snd]
      simp

/-! ## A growth-rate invariant, for picking a concrete word bound

`scanLoop_spec` (in `Ram/ScanProg.lean`) is stated for an arbitrary word bound `B`, subject to
a numeric side condition (`hAllBounds`) that every field of the model state stays under `B`
at every prefix of the tape. `Bounded` bounds those fields as a function of the step count `i`,
the tape length `L`, and the largest tape entry `M`; `wordBound` then picks a single `B`
(exponential in `L`, as is standard for word-RAM word sizes) generous enough to discharge
`hAllBounds` for any tape of length `L` with entries `≤ M`. -/

def Bounded (M L i : ℕ) (s : St) : Prop :=
  s.cc ≤ i ∧ s.ii ≤ i ∧ s.j ≤ i ∧ s.u ≤ i ∧
  s.vv ≤ s.ii * M * 2 ^ L ∧
  s.n ≤ i * M * 2 ^ L ∧ s.m ≤ i * M * 2 ^ L ∧ s.k ≤ i * M * 2 ^ L ∧ s.sz ≤ i * M * 2 ^ L ∧
  s.off ≤ i * (i * M * 2 ^ L) ∧
  s.offs.length ≤ i + 1 ∧ s.mems.length ≤ i ∧
  (∀ x ∈ s.offs, x ≤ i * (i * M * 2 ^ L)) ∧ (∀ x ∈ s.mems, x ≤ i * M * 2 ^ L)

theorem bumpML {i i' : ℕ} (h : i ≤ i') (M L : ℕ) : i * M * 2 ^ L ≤ i' * M * 2 ^ L := by
  apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact h

theorem bumpIIML {i i' : ℕ} (h : i ≤ i') (M L : ℕ) :
    i * (i * M * 2 ^ L) ≤ i' * (i' * M * 2 ^ L) :=
  Nat.mul_le_mul h (bumpML h M L)

theorem offszbump {i off sz M L : ℕ} (hoff : off ≤ i * (i * M * 2 ^ L)) (hsz : sz ≤ i * M * 2 ^ L) :
    off + sz ≤ (i + 1) * ((i + 1) * M * 2 ^ L) := by
  have h1 : off + sz ≤ i * (i * M * 2 ^ L) + i * M * 2 ^ L := by omega
  have h2 : i * (i * M * 2 ^ L) + i * M * 2 ^ L = (i + 1) * (i * M * 2 ^ L) := by ring
  have h3 : (i + 1) * (i * M * 2 ^ L) ≤ (i + 1) * ((i + 1) * M * 2 ^ L) :=
    Nat.mul_le_mul_left _ (bumpML (Nat.le_succ i) M L)
  omega

theorem Bounded.afterNumber_step {M L i : ℕ} {s : St} (h : Bounded M L i s) (v : ℕ)
    (hv : v ≤ (i + 1) * M * 2 ^ L) :
    Bounded M L (i + 1) (afterNumber s v) := by
  obtain ⟨hcc, hii, hj, hu, hvv, hn, hm, hk, hsz, hoff, hoffs, hmems, hoffse, hmemse⟩ := h
  have hii1 : i ≤ i + 1 := Nat.le_succ i
  have hoffbump : s.off ≤ (i + 1) * ((i + 1) * M * 2 ^ L) := hoff.trans (bumpIIML hii1 M L)
  by_cases h0 : s.tgt = 0
  · simp only [afterNumber, h0]
    exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, by simp, hv, hm.trans (bumpML hii1 M L),
      hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoffbump,
      by dsimp only; omega, by dsimp only; omega,
      fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
      fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
  by_cases h1 : s.tgt = 1
  · simp only [afterNumber, h1]
    exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L), hv,
      hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoffbump,
      by dsimp only; omega, by dsimp only; omega,
      fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
      fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
  by_cases h2 : s.tgt = 2
  · by_cases hm0 : s.m = 0
    · simp only [afterNumber, h2, if_pos hm0]
      exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
        hm.trans (bumpML hii1 M L), hv, by simp, hoffbump,
        by simp, by dsimp only; omega,
        by intro x hx; simp at hx; omega,
        fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
    · simp only [afterNumber, h2, if_neg hm0]
      exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
        hm.trans (bumpML hii1 M L), hv, by simp, by simp,
        by simp, by dsimp only; omega,
        by intro x hx; simp at hx; omega,
        fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
  by_cases h3 : s.tgt = 3
  · by_cases hv0 : v = 0
    · by_cases hjm : s.j + 1 < s.m
      · simp only [afterNumber, h3, if_pos hv0, if_pos hjm]
        refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
          hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L), by simp,
          hoffbump, by dsimp only; simp [List.length_append]; omega, by dsimp only; omega,
          ?_, fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact (hoffse x hx).trans (bumpIIML hii1 M L)
          · subst hx; exact hoff.trans (bumpIIML hii1 M L)
      · simp only [afterNumber, h3, if_pos hv0, if_neg hjm]
        refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
          hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L), by simp,
          hoffbump, by dsimp only; simp [List.length_append]; omega, by dsimp only; omega,
          ?_, fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact (hoffse x hx).trans (bumpIIML hii1 M L)
          · subst hx; exact hoff.trans (bumpIIML hii1 M L)
    · simp only [afterNumber, h3, if_neg hv0]
      exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
        hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L), hv, hoffbump,
        by dsimp only; omega, by dsimp only; omega,
        fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
        fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have hmemsbump : ∀ x ∈ s.mems, x ≤ (i + 1) * M * 2 ^ L :=
      fun x hx => (hmemse x hx).trans (bumpML hii1 M L)
    have hvbump : v ≤ (i + 1) * M * 2 ^ L := hv
    have hoffszbump : s.off + s.sz ≤ (i + 1) * ((i + 1) * M * 2 ^ L) := offszbump hoff hsz
    by_cases hlt : s.u + 1 < s.sz
    · simp only [afterNumber, if_pos hlt]
      refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
        hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L),
        hsz.trans (bumpML hii1 M L), hoffbump,
        by dsimp only; omega, by dsimp only; simp [List.length_append]; omega,
        fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L), ?_⟩
      dsimp only
      intro x hx
      simp [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hmemsbump x hx
      · subst hx; exact hvbump
    · by_cases hjm : s.j + 1 < s.m
      · simp only [afterNumber, if_neg hlt, if_pos hjm]
        refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
          hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L), by simp,
          hoffszbump, by dsimp only; simp [List.length_append]; omega,
          by dsimp only; simp [List.length_append]; omega, ?_, ?_⟩
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact (hoffse x hx).trans (bumpIIML hii1 M L)
          · subst hx; exact hoffszbump
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hmemsbump x hx
          · subst hx; exact hvbump
      · simp only [afterNumber, if_neg hlt, if_neg hjm]
        refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by simp, hn.trans (bumpML hii1 M L),
          hm.trans (bumpML hii1 M L), hk.trans (bumpML hii1 M L), by simp,
          hoffszbump, by dsimp only; simp [List.length_append]; omega,
          by dsimp only; simp [List.length_append]; omega, ?_, ?_⟩
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact (hoffse x hx).trans (bumpIIML hii1 M L)
          · subst hx; exact hoffszbump
        · dsimp only
          intro x hx
          simp [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hmemsbump x hx
          · subst hx; exact hvbump

theorem Bounded.step_step {M L i : ℕ} {s : St} (h : Bounded M L i s) (b : ℕ) (hb : b ≤ M)
    (hiL : i ≤ L) : Bounded M L (i + 1) (ScanModel.step s b) := by
  have h' := h
  obtain ⟨hcc, hii, hj, hu, hvv, hn, hm, hk, hsz, hoff, hoffs, hmems, hoffse, hmemse⟩ := h
  have hii1 : i ≤ i + 1 := Nat.le_succ i
  by_cases hph0 : s.ph = 0
  · by_cases hb1 : b = 1
    · rw [show ScanModel.step s b = { s with cc := s.cc + 1 } by simp [ScanModel.step, hph0, hb1]]
      exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; exact hvv, hn.trans (bumpML hii1 M L), hm.trans (bumpML hii1 M L),
        hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoff.trans (bumpIIML hii1 M L),
        by dsimp only; omega, by dsimp only; omega,
        fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
        fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
    · by_cases hcc0 : s.cc = 0
      · rw [show ScanModel.step s b = afterNumber s 0 by simp [ScanModel.step, hph0, hb1, hcc0]]
        exact h'.afterNumber_step 0 (Nat.zero_le _)
      · rw [show ScanModel.step s b = { s with ph := 1, ii := 0, vv := 0 } by
          simp [ScanModel.step, hph0, hb1, hcc0]]
        exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by simp, hn.trans (bumpML hii1 M L), hm.trans (bumpML hii1 M L),
          hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoff.trans (bumpIIML hii1 M L),
          by dsimp only; omega, by dsimp only; omega,
          fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
          fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
  · by_cases hph1 : s.ph = 1
    · have hpow : (2:ℕ) ^ s.ii ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hvv'loc : s.vv + b * 2 ^ s.ii ≤ (s.ii + 1) * M * 2 ^ L := by
        have hbb : b * 2 ^ s.ii ≤ M * 2 ^ L := Nat.mul_le_mul hb hpow
        have hstep : s.vv + b * 2 ^ s.ii ≤ s.ii * M * 2 ^ L + M * 2 ^ L := by omega
        have heq : s.ii * M * 2 ^ L + M * 2 ^ L = (s.ii + 1) * M * 2 ^ L := by ring
        omega
      have hvv' : s.vv + b * 2 ^ s.ii ≤ (i + 1) * M * 2 ^ L :=
        hvv'loc.trans (bumpML (by omega) M L)
      by_cases hcont : s.ii + 1 < s.cc
      · rw [show ScanModel.step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } by
          simp [ScanModel.step, hph1, hcont]]
        exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; exact hvv'loc, hn.trans (bumpML hii1 M L), hm.trans (bumpML hii1 M L),
          hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoff.trans (bumpIIML hii1 M L),
          by dsimp only; omega, by dsimp only; omega,
          fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
          fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩
      · rw [show ScanModel.step s b = afterNumber s (s.vv + b * 2 ^ s.ii) by
          simp [ScanModel.step, hph1, hcont]]
        exact h'.afterNumber_step (s.vv + b * 2 ^ s.ii) hvv'
    · rw [show ScanModel.step s b = s by simp [ScanModel.step, hph0, hph1]]
      exact ⟨by omega, by omega, by omega, by omega,
        hvv, hn.trans (bumpML hii1 M L), hm.trans (bumpML hii1 M L),
        hk.trans (bumpML hii1 M L), hsz.trans (bumpML hii1 M L), hoff.trans (bumpIIML hii1 M L),
        by omega, by omega,
        fun x hx => (hoffse x hx).trans (bumpIIML hii1 M L),
        fun x hx => (hmemse x hx).trans (bumpML hii1 M L)⟩

theorem Bounded.run_take {M L : ℕ} {s0 : St} (h0 : Bounded M L 0 s0) (l : List ℕ)
    (hlM : ∀ x ∈ l, x ≤ M) (hLL : l.length ≤ L) :
    ∀ i, i ≤ l.length → Bounded M L i (run s0 (l.take i)) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    have hib : i < l.length := by omega
    have hmem : l.getD i 0 ∈ l := by
      rw [List.getD_eq_getElem l 0 hib]; exact List.getElem_mem hib
    rw [run_take_succ s0 l i hib]
    exact (ih (by omega)).step_step (l.getD i 0) (hlM _ hmem) (by omega)

/-- A generous, exponential-in-`L` word bound: standard for a word-RAM word size, since what
must stay polynomial is the *bit-width* `Nat.log2 (wordBound M L)`, not the bound itself. -/
def wordBound (M L : ℕ) : ℕ := L * (L * M * 2 ^ L) + L * M * 2 ^ L + M * 2 ^ L + L + 10

/-- `Bounded`'s base case: `init`'s fields are all `0`, so every clause is trivially `≤ 0`. -/
theorem Bounded.init (M L : ℕ) : Bounded M L 0 init := by
  simp [Bounded, ScanModel.init]

theorem wordBound_len_lt (M L : ℕ) : L < wordBound M L := by simp only [wordBound]; omega

theorem wordBound_lt {M L : ℕ} {x : List ℕ} (hlM : ∀ v ∈ x, v ≤ M) (hLl : x.length = L) :
    ∀ v ∈ x, v < wordBound M L := by
  have hpow : 0 < (2:ℕ) ^ L := Nat.two_pow_pos L
  have hmM : M ≤ M * 2 ^ L := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * 2 ^ L := Nat.mul_le_mul_left M hpow
  intro v hv
  have := hlM v hv
  simp only [wordBound]; omega

/-- Every field the machine layer touches, at every prefix of the tape, stays under
`wordBound M L` — the numeric side condition `scanLoop_spec` defers as `hAllBounds`. -/
theorem Bounded.hAllBounds_of {M L : ℕ} {s0 : St} (hStruct0 : Struct s0) (hB0 : Bounded M L 0 s0)
    (l : List ℕ) (hlM : ∀ x ∈ l, x ≤ M) (hLl : l.length = L) :
    ∀ i < l.length,
      (run s0 (l.take i)).ph < wordBound M L ∧ (run s0 (l.take i)).n < wordBound M L ∧
      (run s0 (l.take i)).m < wordBound M L ∧
      (run s0 (l.take i)).cc + 1 < wordBound M L ∧
      (run s0 (l.take i)).vv + (l.getD i 0) * 2 ^ (run s0 (l.take i)).ii < wordBound M L ∧
      (run s0 (l.take i)).ii + 1 < wordBound M L ∧ (run s0 (l.take i)).cc < wordBound M L ∧
      (run s0 (l.take i)).j + 1 < wordBound M L ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).sz < wordBound M L ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).u < wordBound M L ∧
      (run s0 (l.take i)).u + 1 < wordBound M L ∧
      (run s0 (l.take i)).tgt < wordBound M L ∧ 5 < wordBound M L ∧ i + 1 < wordBound M L ∧
      (run s0 (l.take i)).j + 1 < L + 2 ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).u < wordBound M L := by
  intro i hi
  have hiL : i < L := by omega
  have hstruct : Struct (run s0 (l.take i)) := hStruct0.run_step _
  have hbdd : Bounded M L i (run s0 (l.take i)) := hB0.run_take l hlM (by omega) i (by omega)
  obtain ⟨hcc, hii, hj, hu, hvv, hn, hm, hk, hsz, hoff, hoffs, hmems, hoffse, hmemse⟩ := hbdd
  obtain ⟨hph2, htgt4, _, _, _, _, _⟩ := hstruct
  set st := run s0 (l.take i) with hst
  have hn' : st.n ≤ L * M * 2 ^ L := hn.trans (bumpML (by omega) M L)
  have hm' : st.m ≤ L * M * 2 ^ L := hm.trans (bumpML (by omega) M L)
  have hsz' : st.sz ≤ L * M * 2 ^ L := hsz.trans (bumpML (by omega) M L)
  have hoff' : st.off ≤ L * (L * M * 2 ^ L) := hoff.trans (bumpIIML (by omega) M L)
  have hpowpos : 0 < (2:ℕ) ^ L := Nat.two_pow_pos L
  have hpowii : (2:ℕ) ^ st.ii ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmM : M ≤ M * 2 ^ L := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * 2 ^ L := Nat.mul_le_mul_left M hpowpos
  have hbb : l.getD i 0 * 2 ^ st.ii ≤ M * 2 ^ L := by
    have hmem : l.getD i 0 ∈ l := by
      rw [List.getD_eq_getElem l 0 hi]; exact List.getElem_mem hi
    exact Nat.mul_le_mul (hlM _ hmem) hpowii
  have hvv' : st.vv + l.getD i 0 * 2 ^ st.ii ≤ st.ii * M * 2 ^ L + M * 2 ^ L := by omega
  have hvv'' : st.ii * M * 2 ^ L ≤ L * M * 2 ^ L := bumpML (by omega) M L
  simp only [wordBound]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end Lax496464Proofs.Ram.ScanModel
