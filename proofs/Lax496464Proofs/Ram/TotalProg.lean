import Lax496464Proofs.Ram.ScanProg
import Lax496464Proofs.Ram.RCBridge
import Lax496464Proofs.Ram.Validate
import Lax496464Proofs.Ram.Reject
import Lax496464Proofs.Ram.Program
import Lax496464Proofs.Ram.DecodeInstance
import Lax496464Proofs.Ram.PrintTail

/-!
# The total program

`Program.prog` reads a Hitting Set word through `readHS`, which trusts the header and is proved
correct only on a word that encodes an instance. The reduction of Theorem 1 must be a program
that is correct on every input, since `Lax759944.RamPolytime` quantifies over all of them.
`totalProg` is that program:

* `parseCom` (`Ram/ScanProg.lean`) reads the tape as a self-delimiting bit code and always
  terminates;
* a `"ph" == 2` gate checks that the scan reached its final phase — a short code can declare an
  enormous set count and then run out of tape;
* `bridgeCopy` (`Ram/RCBridge.lean`) copies what the scan found into exactly sized arrays;
* `validate` (`Ram/Validate.lean`) checks the conditions `Encodes` asks for beyond what the scan
  and the copy guarantee;
* the rest of `prog` (`progTail`) runs on a valid tape, and the fixed word of the empty
  instance (`Ram/Reject.lean`) is written otherwise.

The three cases are `totalProg_spec_valid` (the scan finishes and `validate` accepts),
`totalProg_spec_reject_unfinished` and `totalProg_spec_reject_invalid`.
-/

namespace Lax496464Proofs.Ram.TotalProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.ScanModel (St step run Struct init wordBound run_encodeInstance
  Bounded offs_length_eq_succ_m_of_done JLtM run_offs_length_of_done OffPristine
  run_mems_length_of_done run_offs_last_eq_off_of_done wordBound_len_lt)
open Lax496464Proofs.Ram.ScanProg (parseCom parseCom_spec Matches MatchesRest)
open Lax496464Proofs.Ram.RCBridge (bridgeCopy bridgeCopy_spec_generic)
open Lax496464Proofs.Ram.Validate (validate validate_spec_generic
  OffsetsOkG MembersOkG SortedOkG SameBlockG)
open Lax496464Proofs.Ram.Reject (rejectProg rejectProg_spec emptyInstance
  decisionWord_emptyInstance)
open Lax496464Proofs.Ram.Program (consts consts_spec header
  dumps target' finalOut_spec OB offs_of_encodes length_memberList_le)
open Lax496464Proofs.Ram.Build (build build_spec RC)
open Lax496464Proofs.Ram.Gen (gen gen_spec Ctx Bnd costDum)
open Lax496464Proofs.Ram.CsrWord (csrWord offsetsOf membersOf setCount_csrWord
  offset_csrWord_last getD_csrWord_n length_offsetsOf offset_csrWord member_csrWord
  member_csrWord_strictMono_of_sameBlock)
open Lax496464Proofs.Ram.InstanceWord (decisionWord)
open Lax496464Proofs.Ram.BitsNat (natBits)
open Lax496464Proofs.Ram.CsrWord (decodeInstance encodes_decodeInstance offset_decodeInstance
  member_decodeInstance_csrWord membersOf_length_decodeInstance csrWord_decodeInstance_eq)

abbrev V (s : String) : Expr := .var s

/-- `prog`'s own tail: everything after reading the word. -/
def progTail : Com := .seq build (.seq consts (.seq gen Lax496464Proofs.Ram.PrintTail.printTail))

variable {P : Instance} {k : ℕ}

/-- **`Program.prog_spec`, minus the reading step.** Exactly `Program.prog_spec`'s own proof,
starting one step later: from `RC x σ` (whatever produced it — `readHS`, or here, the scan's
`bridgeCopy`) plus the array setup `gen` needs, `progTail` produces the decision word. -/
theorem progTail_spec {B : ℕ} {x : List ℕ} (h : Encodes x P k) (hxB : ∀ v ∈ x, v < B)
    (hb : Bnd P k B) (hLB : offset x (setCount x) + 1 < B) :
    Spec B (fun σ => RC x σ ∧ σ.vars "k" = solutionSize x ∧ σ.out = [] ∧
        (σ.arrs "MJ").length = P.n * P.m ∧
        (σ.arrs "MI").length = P.n * P.m ∧ (σ.arrs "PA").length = numJobs P k ∧
        (σ.arrs "QA").length = numJobs P k ∧ (σ.arrs "DA").length = numJobs P k)
      progTail (fun _ σ' => σ'.out =
        (InstanceWord.decisionWord (construct P k) (target P k)).flatMap BitsNat.bitsNat)
      (Lax496464Proofs.Ram.Build.costBuild (universeSize x) (setCount x)
          (offset x (setCount x)) +
        (100 + ((2 + (((400 + 4) * (memberList P).length + 6 + 4 + 4) * R P k + 6)) +
          (costDum P.n P.m (R P k) + costDum P.n P.m (R P k)) +
          (3 * (42 * B.size + 26) + 4 * ((42 * B.size + 31 + 4) * numJobs P k + 6) + 30)))) := by
  have hone := hb.one
  have hk2 := h.size_bounds.1
  have hkn := h.size_bounds.2
  have hn : universeSize x = P.n := h.universeSize_eq
  have hm : setCount x = P.m := h.setCount_eq
  obtain ⟨hmB2, hnmB⟩ := hb.small hk2 hkn
  have hnmB' : universeSize x * setCount x + 1 < B := by rw [hn, hm]; exact hnmB
  have hnB : universeSize x < B := by rw [hn]; exact hb.n_lt
  have hLB' : offset x (setCount x) < B := by omega
  have hoffs := offs_of_encodes h
  have hbuild := (build_spec (x := x) hxB hone hoffs hLB' hnB hnmB' (by omega)).frame
  have hcons := consts_spec hb hk2 hkn
  have hgen := (gen_spec hb hk2 hkn).frame
  have hfin := Lax496464Proofs.Ram.PrintTail.printTail_spec hb hk2
  refine Spec.of_exists fun σ ⟨hRC, hk0, hout, hMJ, hMI, hPA, hQA, hDA⟩ => ?_
  -- building the membership pairs
  obtain ⟨σ2, hr2, ⟨hRC2, hCur2⟩, hfv2, hfa2, -, hfo2⟩ := hbuild.run
    ⟨hRC, by rw [hMJ, hn, hm], by rw [hMI, hn, hm]⟩
  have hout2 : σ2.out = [] := by rw [hfo2 (by decide), hout]
  -- the constants
  have hn2 : σ2.vars "n" = P.n := by rw [hRC2.1, hn]
  have hm2 : σ2.vars "m" = P.m := by rw [hRC2.2.1, hm]
  have hk2v : σ2.vars "k" = k := by
    rw [hfv2 "k" (by decide), hk0, h.solutionSize_eq]
  have hwml : Members.wmemberList x = memberList P := Members.wmemberList_eq h
  have hLc2 : σ2.vars "Lc" = (memberList P).length := by rw [hCur2.1, hwml]
  obtain ⟨σ3, hr3, hR3, hQ3, hdc3, hsc3, hnj3, hfv3, hfa3, hinp3, hout3⟩ :=
    hcons.run ⟨hn2, hm2, hk2v, hLc2⟩
  -- the context of the generation passes
  have hcap := length_memberList_le h
  have hCtx3 : Ctx P k σ3 := by
    refine ⟨?_, ?_, hQ3, hR3, ?_, hsc3, hdc3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfv3 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hn2]
    · rw [hfv3 "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hm2]
    · rw [hfv3 "Lc" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hLc2]
    · rw [hfa3]; have := hCur2.2.2.1; rw [hn, hm] at this; omega
    · rw [hfa3]; have := hCur2.2.2.2; rw [hn, hm] at this; omega
    · intro u hu; rw [hfa3]
      have := (hCur2.2.1 u (by rw [hwml]; exact hu)).1
      rw [hwml] at this; exact this
    · intro u hu; rw [hfa3]
      have := (hCur2.2.1 u (by rw [hwml]; exact hu)).2
      rw [hwml] at this; exact this
    · rw [hfa3, hfa2 "PA" (by decide)]; exact hPA
    · rw [hfa3, hfa2 "QA" (by decide)]; exact hQA
    · rw [hfa3, hfa2 "DA" (by decide)]; exact hDA
  have hDone3 : Lax496464Proofs.Ram.Gen.Done P k σ3 0 := fun s hs => absurd hs (Nat.not_lt_zero _)
  obtain ⟨σ4, hr4, ⟨hCtx4, hDone4, ht4⟩, hgfv, hgfa, -, hgfo⟩ := hgen.run ⟨hCtx3, hDone3⟩
  have hOB4 : OB P k σ4 := by
    refine ⟨hCtx4, hDone4, ?_, ?_⟩
    · rw [hgfv "nj" (by decide), hnj3]
    · rw [hgfv "k" (by decide), hfv3 "k" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hk2v]
  have hout4 : σ4.out = [] := by
    rw [hgfo (by decide), hout3, hout2]
  obtain ⟨σ5, hr5, hout5⟩ := hfin.run ⟨hOB4, hout4⟩
  refine ⟨σ5, _, (hr2.seq (hr3.seq (hr4.seq hr5))).mono ?_, le_rfl, ?_⟩
  · omega
  · rw [hout5]

/-- **The total program.** A `"ph" == 2` gate stands between `parseCom` and `bridgeCopy`,
unlike the sketch in this file's docstring: `bridgeCopy` reads `"OFFS"[0 .. m]`, and `m` is
only known to fit inside `"OFFS"`'s allocated length (`Ram/ScanModel.lean`'s
`offs_length_eq_succ_m_of_done`) *once the scan has actually reached "done"* — a self-
delimiting code can spend very few bits declaring an astronomically large `m` and then simply
run out of tape before processing anywhere near that many sets, leaving `m` huge and `"ph"`
stuck at `0`/`1`. Without this gate `bridgeCopy` would try to read far past `"OFFS"'`s bounds
on such a tape and get stuck (no valid `Run` derivation), breaking exactly the totality this
whole program exists to provide. The gate costs nothing on a tape that *does* finish (the
scan's own `"ph"` is already sitting in a variable `Matches` already exposes), and turns "ran
out of tape mid-set" tapes into an immediate, safe reject, same as any other malformed one. -/
def totalProg : Com :=
  .seq parseCom (.ite (.eq (V "ph") (.lit 2))
    (.seq bridgeCopy (.seq validate
      (.ite (.eq (V "valid") (.lit 1)) progTail rejectProg)))
    rejectProg)

open Lax496464.Construction (numJobs jp jq jd)

/-- **`totalProg` rejects a tape whose scan never finishes.** If `(run init y).ph ≠ 2`, the
`"ph" == 2` gate takes its `else` branch straight to `rejectProg`, never reaching `bridgeCopy`,
so no array-bound question about `"m"` arises. -/
theorem totalProg_spec_reject_unfinished {M B : ℕ} (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ M)
    (hBdef : B = wordBound M y.length) (hB2 : 2 < B) (hnot2 : (run init y).ph ≠ 2) {σ0 : Env}
    (hinp : σ0.inp = y.length :: y) (hout : σ0.out = [])
    (halen : (σ0.arrs "a").length = y.length)
    (hOFFSlen : (σ0.arrs "OFFS").length = y.length + 2) (hMEMSlen : (σ0.arrs "MEMS").length = B) :
    ∃ σ', Run B totalProg σ0 σ'
      (12 * y.length + 10 + 30 + (2220 * y.length + 6) + 30) ∧ σ'.out = [0, 0, 0] := by
  obtain ⟨σ1, hr1, hq1⟩ := parseCom_spec (M := M) y hlM σ0
    ⟨hinp, hout, halen, hOFFSlen, hMEMSlen.trans hBdef⟩
  rw [← hBdef] at hq1 hr1
  obtain ⟨⟨⟨hph1, -, -, -, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩, -⟩ := hq1
  have hout1 : σ1.out = [] := by rw [hr1.out_eq (by decide)]; exact hout
  have hnot2' : σ1.vars "ph" ≠ 2 := by rw [hph1]; exact hnot2
  have hphle2 : (run init y).ph ≤ 2 := (Struct.init.run_step y).1
  have hphB : σ1.vars "ph" < B := by rw [hph1]; omega
  have hevph1 : (V "ph").evalB B σ1 = some (σ1.vars "ph") := evalB_var hphB
  have hevlit2ph : (Expr.lit 2).evalB B σ1 = some 2 := evalB_lit (by omega)
  have hphcond : (Cond.eq (V "ph") (.lit 2)).evalB B σ1 = some false := by
    rw [evalB_condEq hevph1 hevlit2ph]; simp [hnot2']
  obtain ⟨σ2, hr2, hout2⟩ := rejectProg_spec (B := B) (by omega) σ1.out σ1 rfl
  rw [decisionWord_emptyInstance] at hout2
  have hout2' : σ2.out = [0, 0, 0] := by simp [hout2, hout1]
  have hrph := Run.ite_false
    (c := .seq bridgeCopy (.seq validate (.ite (.eq (V "valid") (.lit 1)) progTail rejectProg)))
    hphcond hr2
  refine ⟨σ2, ?_, hout2'⟩
  show Run B totalProg σ0 σ2 _
  unfold totalProg
  exact (hr1.seq hrph).mono (by simp only [Expr.size, Cond.size]; omega)

/-- **`totalProg` rejects a tape whose scan finishes but is not a genuine encoding.** The
other half of the malformed-tape totality argument this file's docstring flags as missing:
if `(run init y).ph = 2` (the scan *does* finish) but the four conditions `validate` checks
fail, `totalProg` reaches `bridgeCopy`/`validate` (the `"ph" == 2` gate takes its `then`
branch), `validate` sets `"valid" ≠ 1`, and the `"valid" == 1` gate falls through to
`rejectProg`. `bridgeCopy_spec_generic`'s own array-safety preconditions are exactly
`run_offs_length_of_done`/`run_mems_length_of_done`/`run_offs_last_eq_off_of_done` (`Ram/
ScanModel.lean`), and the two generic `Bounded` bounds (`offs.length ≤ y.length + 1`,
`mems.length ≤ y.length`) give the `"OFFS"`/`"MEMS"` length side of the same safety argument,
for *any* tape whose scan reaches `"done"` — genuine encoding or not. -/
theorem totalProg_spec_reject_invalid {M B : ℕ} (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ M)
    (hBdef : B = wordBound M y.length) (hB2 : 2 < B) (hdone : (run init y).ph = 2)
    (hnotvalid : ¬ ((run init y).offs.getD 0 0 = 0 ∧
        Lax496464Proofs.Ram.Validate.OffsetsOkG (fun j => (run init y).offs.getD j 0)
          (run init y).m ∧
        Lax496464Proofs.Ram.Validate.MembersOkG (fun t => (run init y).mems.getD t 0)
          (run init y).n ((run init y).offs.getD (run init y).m 0) ∧
        Lax496464Proofs.Ram.Validate.SortedOkG (fun j => (run init y).offs.getD j 0)
          (fun t => (run init y).mems.getD t 0) (run init y).m
          ((run init y).offs.getD (run init y).m 0) ∧
        (run init y).n ≤ (run init y).m + (run init y).offs.getD (run init y).m 0 + 4 ∧
        2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n))
    (hnB : (run init y).n < B) (hkB : (run init y).k < B)
    (hOffValB : ∀ j ≤ (run init y).m, (run init y).offs.getD j 0 + 1 < B)
    (hMemValB : ∀ t < (run init y).off, (run init y).mems.getD t 0 + 1 < B)
    (hnmB : (run init y).m + (run init y).off + 4 < B)
    {σ0 : Env} (hp0 : σ0.vars "p" < B)
    (hinp : σ0.inp = y.length :: y) (hout : σ0.out = [])
    (halen : (σ0.arrs "a").length = y.length)
    (hOFFSlen : (σ0.arrs "OFFS").length = y.length + 2) (hMEMSlen : (σ0.arrs "MEMS").length = B)
    (hOFFlen : (σ0.arrs "OFF").length = (run init y).m + 1)
    (hMEMlen : (σ0.arrs "MEM").length = (run init y).off) :
    ∃ σ', Run B totalProg σ0 σ'
      (12 * y.length + 10 + 30 + (2220 * y.length + 6) +
        (((1 + 4) + ((1 + 3 + 4 + 4) * ((run init y).m + 1) + 6) + (1 + 4) +
            ((1 + 3 + 4 + 4) * (run init y).off + 6)) +
          (2 + 7 + (18 * (run init y).m + 6) + (18 * (run init y).off + 9) +
              (34 * (run init y).off + 34 * (run init y).m + 20) + 13 + 6 + 6) + 20) +
        60) ∧
      σ'.out = [0, 0, 0] := by
  set foff : ℕ → ℕ := fun j => (run init y).offs.getD j 0 with hfoffdef
  set fmem : ℕ → ℕ := fun t => (run init y).mems.getD t 0 with hfmemdef
  -- Step 1: parseCom
  obtain ⟨σ1, hr1, hq1⟩ := parseCom_spec (M := M) y hlM σ0
    ⟨hinp, hout, halen, hOFFSlen, hMEMSlen.trans hBdef⟩
  rw [← hBdef] at hq1 hr1
  obtain ⟨hMatches1, hi1⟩ := hq1
  obtain ⟨hRest1, hcc1, hii1, hvv1⟩ := hMatches1
  obtain ⟨hph1, htgt1, hn1, hm1, hk1, hj1, hu1, hsz1, hoff1, hOFFSlen1, hMEMSlen1,
    hOFFScorr1, hMEMScorr1⟩ := hRest1
  have hoffslen : (run init y).offs.length = (run init y).m + 1 :=
    run_offs_length_of_done y hdone
  have hmemslen : (run init y).mems.length = (run init y).off :=
    run_mems_length_of_done y hdone
  have hfoffm : foff (run init y).m = (run init y).off :=
    run_offs_last_eq_off_of_done y hdone
  have hOFFcorr1 : ∀ j ≤ (run init y).m, (σ1.arrs "OFFS").getD j 0 = foff j := by
    intro j hj; exact hOFFScorr1 (t := j) (by omega)
  have hMEMcorr1 : ∀ t < (run init y).off, (σ1.arrs "MEMS").getD t 0 = fmem t := by
    intro t ht; exact hMEMScorr1 (t := t) (by omega)
  -- generic `Bounded` bound: the scan's own bookkeeping never outgrows the tape it read
  have hbnd := Bounded.run_take (Bounded.init M y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hbnd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hoffslenb, hmemslenb, -, -⟩ := hbnd
  have hmlt : (run init y).m ≤ y.length := by omega
  have hofflt : (run init y).off ≤ y.length := by omega
  have hylt : y.length + 2 < B := by
    rw [hBdef]; simp only [ScanModel.wordBound]; omega
  have hOFFSge1 : (σ1.arrs "OFFS").length ≥ (run init y).m + 1 := by rw [hOFFSlen1]; omega
  have hMEMSge1 : (σ1.arrs "MEMS").length ≥ (run init y).off := by
    rw [hMEMSlen1, hBdef]
    have := wordBound_len_lt M y.length
    omega
  have hOFF1 : (σ1.arrs "OFF").length = (run init y).m + 1 := by
    rw [hr1.frame_arr "OFF" (by decide)]; exact hOFFlen
  have hMEM1 : (σ1.arrs "MEM").length = (run init y).off := by
    rw [hr1.frame_arr "MEM" (by decide)]; exact hMEMlen
  have hout1 : σ1.out = [] := by rw [hr1.out_eq (by decide)]; exact hout
  have hp1 : σ1.vars "p" < B := by rw [hr1.frame_var "p" (by decide)]; exact hp0
  -- Step 2: bridgeCopy
  obtain ⟨σ2, hr2, hOFF2len, hMEM2len, hOFFcorr2, hMEMcorr2⟩ :=
    bridgeCopy_spec_generic (B := B) (m0 := (run init y).m) (L0 := (run init y).off) foff fmem
      (by omega) (by omega)
      (fun j hj => by simp only [hfoffdef]; have := hOffValB j hj; omega)
      (fun t ht => by simp only [hfmemdef]; have := hMemValB t ht; omega) σ1
      ⟨hm1, hOFFSge1, hOFF1, hMEM1, hMEMSge1, hOFFcorr1, hfoffm, hMEMcorr1⟩
  have hn2 : σ2.vars "n" = (run init y).n := by rw [hr2.frame_var "n" (by decide)]; exact hn1
  have hm2 : σ2.vars "m" = (run init y).m := by rw [hr2.frame_var "m" (by decide)]; exact hm1
  have hk2 : σ2.vars "k" = (run init y).k := by rw [hr2.frame_var "k" (by decide)]; exact hk1
  have hout2 : σ2.out = [] := by rw [hr2.out_eq (by decide)]; exact hout1
  have hp2 : σ2.vars "p" < B := by rw [hr2.frame_var "p" (by decide)]; exact hp1
  -- Step 3: validate
  obtain ⟨σ3, hr3, hvalid3, hvalid3le⟩ := validate_spec_generic (B := B) (m0 := (run init y).m)
    (n0 := (run init y).n) (k0 := (run init y).k) foff fmem hB2 hOffValB (by omega) hnB hkB
    (by rw [hfoffm]; exact hMemValB) (by rw [hfoffm]; exact hnmB) σ2
    ⟨hm2, hn2, hk2, hOFF2len, hOFFcorr2, by rw [hfoffm]; exact hMEM2len,
      (by rw [hfoffm]; exact hMEMcorr2), hp2⟩
  have hout3 : σ3.out = [] := by rw [hr3.out_eq (by decide)]; exact hout2
  have hvaliddef : σ3.vars "valid" = 1 ↔
      foff 0 = 0 ∧ Lax496464Proofs.Ram.Validate.OffsetsOkG foff (run init y).m ∧
        Lax496464Proofs.Ram.Validate.MembersOkG fmem (run init y).n (foff (run init y).m) ∧
        Lax496464Proofs.Ram.Validate.SortedOkG foff fmem (run init y).m (foff (run init y).m) ∧
        (run init y).n ≤ (run init y).m + foff (run init y).m + 4 ∧
        2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n := hvalid3
  have hvalidne1 : σ3.vars "valid" ≠ 1 := by
    intro hc
    apply hnotvalid
    have h := hvaliddef.mp hc
    simpa only [hfoffdef, hfmemdef] using h
  -- Step 4: the "valid" == 1 gate falls through to rejectProg
  have hev1 : (V "valid").evalB B σ3 = some (σ3.vars "valid") := evalB_var (by omega)
  have hev2 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit (by omega)
  have hcond : (Cond.eq (V "valid") (.lit 1)).evalB B σ3 = some false := by
    rw [evalB_condEq hev1 hev2]; simp [hvalidne1]
  obtain ⟨σ4, hr4, hout4⟩ := rejectProg_spec (B := B) (by omega) σ3.out σ3 rfl
  rw [decisionWord_emptyInstance] at hout4
  have hout4' : σ4.out = [0, 0, 0] := by simp [hout4, hout3]
  have hrValidIte := Run.ite_false (c := progTail) hcond hr4
  -- the "ph == 2" gate: takes the `then` branch, since the scan reached "done"
  have hph1' : σ1.vars "ph" = 2 := by rw [hph1]; exact hdone
  have hevph1 : (V "ph").evalB B σ1 = some (σ1.vars "ph") := evalB_var (by omega)
  have hevlit2ph : (Expr.lit 2).evalB B σ1 = some 2 := evalB_lit (by omega)
  have hphcond : (Cond.eq (V "ph") (.lit 2)).evalB B σ1 = some true := by
    rw [evalB_condEq hevph1 hevlit2ph, hph1']; rfl
  have hrph := Run.ite_true (d := rejectProg) hphcond (hr2.seq (hr3.seq hrValidIte))
  refine ⟨σ4, ?_, hout4'⟩
  show Run B totalProg σ0 σ4 _
  unfold totalProg
  exact (hr1.seq hrph).mono (by simp only [Expr.size, Cond.size]; omega)

/-! ## Any tape the scan finishes on and `validate` accepts

The instance is read off the scan's final state (`decY`), so nothing about `y` beyond what
`validate` checks is assumed; in particular a tape with trailing padding, which scans to the
same state as the canonical one, is covered. -/

/-- The instance the scan recovers from `y`'s tape (meaningful when `ValidY y`). -/
noncomputable def decY (y : List ℕ) : Instance :=
  decodeInstance (fun j => (run init y).offs.getD j 0) (fun t => (run init y).mems.getD t 0)
    (run init y).n (run init y).m

/-- The scan finished and `validate`'s seven conditions hold of what it recovered. -/
def ValidY (y : List ℕ) : Prop :=
  (run init y).ph = 2 ∧ (run init y).offs.getD 0 0 = 0 ∧
    OffsetsOkG (fun j => (run init y).offs.getD j 0) (run init y).m ∧
    MembersOkG (fun t => (run init y).mems.getD t 0) (run init y).n
      ((run init y).offs.getD (run init y).m 0) ∧
    SortedOkG (fun j => (run init y).offs.getD j 0) (fun t => (run init y).mems.getD t 0)
      (run init y).m ((run init y).offs.getD (run init y).m 0) ∧
    (run init y).n ≤ (run init y).m + (run init y).offs.getD (run init y).m 0 + 4 ∧
    2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n

theorem encodes_decY {y : List ℕ} (hv : ValidY y) :
    Encodes (csrWord (decY y) (run init y).k) (decY y) (run init y).k := by
  obtain ⟨-, hoff0, hOff, hMem, hSorted, hnm, hk2, hkn⟩ := hv
  exact encodes_decodeInstance (fun j => (run init y).offs.getD j 0)
    (fun t => (run init y).mems.getD t 0) (run init y).n (run init y).m hoff0 hOff hMem hSorted
    hk2 hkn hnm

theorem totalProg_spec_valid {M B : ℕ} (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ M)
    (hBdef : B = wordBound M y.length) (hB2 : 2 < B) (hv : ValidY y)
    (hnB : (run init y).n < B) (hkB : (run init y).k < B)
    (hOffValB : ∀ j ≤ (run init y).m, (run init y).offs.getD j 0 + 1 < B)
    (hMemValB : ∀ t < (run init y).off, (run init y).mems.getD t 0 + 1 < B)
    (hnmB : (run init y).m + (run init y).off + 4 < B)
    (hb : Bnd (decY y) (run init y).k B)
    (hxB : ∀ v ∈ csrWord (decY y) (run init y).k, v < B)
    {σ0 : Env} (hp0 : σ0.vars "p" < B)
    (hinp : σ0.inp = y.length :: y) (hout : σ0.out = [])
    (halen : (σ0.arrs "a").length = y.length)
    (hOFFSlen : (σ0.arrs "OFFS").length = y.length + 2) (hMEMSlen : (σ0.arrs "MEMS").length = B)
    (hOFFlen : (σ0.arrs "OFF").length = (run init y).m + 1)
    (hMEMlen : (σ0.arrs "MEM").length = (run init y).off)
    (hMJ : (σ0.arrs "MJ").length = (run init y).n * (run init y).m)
    (hMI : (σ0.arrs "MI").length = (run init y).n * (run init y).m)
    (hPA : (σ0.arrs "PA").length = numJobs (decY y) (run init y).k)
    (hQA : (σ0.arrs "QA").length = numJobs (decY y) (run init y).k)
    (hDA : (σ0.arrs "DA").length = numJobs (decY y) (run init y).k) :
    ∃ σ', Run B totalProg σ0 σ'
      (12 * y.length + 10 + 30 + (2220 * y.length + 6) +
        (((1 + 4) + ((1 + 3 + 4 + 4) * ((run init y).m + 1) + 6) + (1 + 4) +
            ((1 + 3 + 4 + 4) * (run init y).off + 6)) +
          (2 + 7 + (18 * (run init y).m + 6) + (18 * (run init y).off + 9) +
              (34 * (run init y).off + 34 * (run init y).m + 20) + 13 + 6 + 6) + 20) +
        (Lax496464Proofs.Ram.Build.costBuild (universeSize (csrWord (decY y) (run init y).k))
            (setCount (csrWord (decY y) (run init y).k))
            (offset (csrWord (decY y) (run init y).k)
              (setCount (csrWord (decY y) (run init y).k))) +
          (100 + ((2 + (((400 + 4) * (memberList (decY y)).length + 6 + 4 + 4) *
              R (decY y) (run init y).k + 6)) +
            (costDum (decY y).n (decY y).m (R (decY y) (run init y).k) +
              costDum (decY y).n (decY y).m (R (decY y) (run init y).k)) +
            (3 * (42 * B.size + 26) +
              4 * ((42 * B.size + 31 + 4) * numJobs (decY y) (run init y).k + 6) + 30))))) ∧
      σ'.out = (InstanceWord.decisionWord (construct (decY y) (run init y).k)
        (target (decY y) (run init y).k)).flatMap BitsNat.bitsNat := by
  have hvv := hv
  obtain ⟨hdone, hoff0, hOff, hMem, hSorted, hnm, hk2, hkn⟩ := hv
  set foff : ℕ → ℕ := fun j => (run init y).offs.getD j 0 with hfoffdef
  set fmem : ℕ → ℕ := fun t => (run init y).mems.getD t 0 with hfmemdef
  have hE : Encodes (csrWord (decY y) (run init y).k) (decY y) (run init y).k := encodes_decY hvv
  have hPn : (decY y).n = (run init y).n := rfl
  have hPm : (decY y).m = (run init y).m := rfl
  have hoffslen : (run init y).offs.length = (run init y).m + 1 :=
    run_offs_length_of_done y hdone
  have hmemslen : (run init y).mems.length = (run init y).off :=
    run_mems_length_of_done y hdone
  have hfoffm : foff (run init y).m = (run init y).off :=
    run_offs_last_eq_off_of_done y hdone
  have hoffOf : ∀ j ≤ (run init y).m,
      offset (csrWord (decY y) (run init y).k) j = foff j := fun j hj =>
    offset_decodeInstance foff fmem (run init y).n (run init y).m hoff0 hOff hMem hSorted _ hj
  have hmemOf : ∀ t < (run init y).off,
      member (csrWord (decY y) (run init y).k) t = fmem t := fun t ht =>
    member_decodeInstance_csrWord foff fmem (run init y).n (run init y).m hoff0 hOff hMem hSorted _
      (by rw [hfoffm]; exact ht)
  have hmemlen : (membersOf (decY y)).length = (run init y).off := by
    have := membersOf_length_decodeInstance foff fmem (run init y).n (run init y).m hoff0 hOff hMem hSorted
    rw [hfoffm] at this; exact this
  have hsc : setCount (csrWord (decY y) (run init y).k) = (run init y).m := setCount_csrWord
  have hol : offset (csrWord (decY y) (run init y).k)
      (setCount (csrWord (decY y) (run init y).k)) = (run init y).off := by
    rw [hsc, hoffOf _ le_rfl, hfoffm]
  -- Step 1: parseCom
  obtain ⟨σ1, hr1, hq1⟩ := parseCom_spec (M := M) y hlM σ0
    ⟨hinp, hout, halen, hOFFSlen, hMEMSlen.trans hBdef⟩
  rw [← hBdef] at hq1 hr1
  obtain ⟨hMatches1, hi1⟩ := hq1
  obtain ⟨hRest1, hcc1, hii1, hvv1⟩ := hMatches1
  obtain ⟨hph1, htgt1, hn1, hm1, hk1, hj1, hu1, hsz1, hoff1, hOFFSlen1, hMEMSlen1,
    hOFFScorr1, hMEMScorr1⟩ := hRest1
  have hOFFcorr1 : ∀ j ≤ (run init y).m, (σ1.arrs "OFFS").getD j 0 = foff j := by
    intro j hj; exact hOFFScorr1 (t := j) (by omega)
  have hMEMcorr1 : ∀ t < (run init y).off, (σ1.arrs "MEMS").getD t 0 = fmem t := by
    intro t ht; exact hMEMScorr1 (t := t) (by omega)
  have hbnd := Bounded.run_take (Bounded.init M y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hbnd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hoffslenb, hmemslenb, -, -⟩ := hbnd
  have hOFFSge1 : (σ1.arrs "OFFS").length ≥ (run init y).m + 1 := by
    rw [hOFFSlen1]; omega
  have hMEMSge1 : (σ1.arrs "MEMS").length ≥ (run init y).off := by
    rw [hMEMSlen1, hBdef]
    have := wordBound_len_lt M y.length
    omega
  have hOFF1 : (σ1.arrs "OFF").length = (run init y).m + 1 := by
    rw [hr1.frame_arr "OFF" (by decide)]; exact hOFFlen
  have hMEM1 : (σ1.arrs "MEM").length = (run init y).off := by
    rw [hr1.frame_arr "MEM" (by decide)]; exact hMEMlen
  have hMJ1 : (σ1.arrs "MJ").length = (run init y).n * (run init y).m := by
    rw [hr1.frame_arr "MJ" (by decide)]; exact hMJ
  have hMI1 : (σ1.arrs "MI").length = (run init y).n * (run init y).m := by
    rw [hr1.frame_arr "MI" (by decide)]; exact hMI
  have hPA1 : (σ1.arrs "PA").length = numJobs (decY y) (run init y).k := by
    rw [hr1.frame_arr "PA" (by decide)]; exact hPA
  have hQA1 : (σ1.arrs "QA").length = numJobs (decY y) (run init y).k := by
    rw [hr1.frame_arr "QA" (by decide)]; exact hQA
  have hDA1 : (σ1.arrs "DA").length = numJobs (decY y) (run init y).k := by
    rw [hr1.frame_arr "DA" (by decide)]; exact hDA
  have hout1 : σ1.out = [] := by rw [hr1.out_eq (by decide)]; exact hout
  have hp1 : σ1.vars "p" < B := by rw [hr1.frame_var "p" (by decide)]; exact hp0
  -- Step 2: bridgeCopy
  obtain ⟨σ2, hr2, hOFF2len, hMEM2len, hOFFcorr2, hMEMcorr2⟩ :=
    bridgeCopy_spec_generic (B := B) (m0 := (run init y).m) (L0 := (run init y).off) foff fmem
      (by omega) (by omega)
      (fun j hj => by simp only [hfoffdef]; have := hOffValB j hj; omega)
      (fun t ht => by simp only [hfmemdef]; have := hMemValB t ht; omega) σ1
      ⟨hm1, hOFFSge1, hOFF1, hMEM1, hMEMSge1, hOFFcorr1, hfoffm, hMEMcorr1⟩
  have hn2 : σ2.vars "n" = (run init y).n := by rw [hr2.frame_var "n" (by decide)]; exact hn1
  have hm2 : σ2.vars "m" = (run init y).m := by rw [hr2.frame_var "m" (by decide)]; exact hm1
  have hk2v : σ2.vars "k" = (run init y).k := by rw [hr2.frame_var "k" (by decide)]; exact hk1
  have hout2 : σ2.out = [] := by rw [hr2.out_eq (by decide)]; exact hout1
  have hp2 : σ2.vars "p" < B := by rw [hr2.frame_var "p" (by decide)]; exact hp1
  have hMJ2 : (σ2.arrs "MJ").length = (run init y).n * (run init y).m := by
    rw [hr2.frame_arr "MJ" (by decide)]; exact hMJ1
  have hMI2 : (σ2.arrs "MI").length = (run init y).n * (run init y).m := by
    rw [hr2.frame_arr "MI" (by decide)]; exact hMI1
  have hPA2 : (σ2.arrs "PA").length = numJobs (decY y) (run init y).k := by
    rw [hr2.frame_arr "PA" (by decide)]; exact hPA1
  have hQA2 : (σ2.arrs "QA").length = numJobs (decY y) (run init y).k := by
    rw [hr2.frame_arr "QA" (by decide)]; exact hQA1
  have hDA2 : (σ2.arrs "DA").length = numJobs (decY y) (run init y).k := by
    rw [hr2.frame_arr "DA" (by decide)]; exact hDA1
  have hRC2 : RC (csrWord (decY y) (run init y).k) σ2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ2.vars "n" = universeSize (csrWord (decY y) (run init y).k)
      rw [hn2]
      exact (getD_csrWord_n (P := decY y) (k := (run init y).k)).symm
    · rw [hsc]; exact hm2
    · intro j hj
      rw [hsc] at hj
      rw [hoffOf j hj]; exact hOFFcorr2 j hj
    · intro t ht
      rw [hol] at ht
      rw [hmemOf t ht]; exact hMEMcorr2 t ht
    · rw [hsc]; exact hOFF2len
    · rw [hol]; exact hMEM2len
  -- Step 3: validate
  obtain ⟨σ3, hr3, hvalid3, hvalid3le⟩ := validate_spec_generic (B := B) (m0 := (run init y).m)
    (n0 := (run init y).n) (k0 := (run init y).k) foff fmem hB2 hOffValB (by omega) hnB hkB
    (by rw [hfoffm]; exact hMemValB) (by rw [hfoffm]; exact hnmB) σ2
    ⟨hm2, hn2, hk2v, hOFF2len, hOFFcorr2, by rw [hfoffm]; exact hMEM2len,
      (by rw [hfoffm]; exact hMEMcorr2), hp2⟩
  have hvalid1 : σ3.vars "valid" = 1 := by
    rw [hvalid3]
    exact ⟨hoff0, hOff, hMem, hSorted, hnm, hk2, hkn⟩
  have hRC3 : RC (csrWord (decY y) (run init y).k) σ3 :=
    hRC2.congr (hr3.frame_var "n" (by decide)) (hr3.frame_var "m" (by decide))
      (hr3.frame_arr "OFF" (by decide)) (hr3.frame_arr "MEM" (by decide))
  have hk3 : σ3.vars "k" = (run init y).k := by
    rw [hr3.frame_var "k" (by decide)]; exact hk2v
  have hMJ3 : (σ3.arrs "MJ").length = (decY y).n * (decY y).m := by
    rw [hr3.frame_arr "MJ" (by decide)]; exact hMJ2
  have hMI3 : (σ3.arrs "MI").length = (decY y).n * (decY y).m := by
    rw [hr3.frame_arr "MI" (by decide)]; exact hMI2
  have hPA3 : (σ3.arrs "PA").length = numJobs (decY y) (run init y).k := by
    rw [hr3.frame_arr "PA" (by decide)]; exact hPA2
  have hQA3 : (σ3.arrs "QA").length = numJobs (decY y) (run init y).k := by
    rw [hr3.frame_arr "QA" (by decide)]; exact hQA2
  have hDA3 : (σ3.arrs "DA").length = numJobs (decY y) (run init y).k := by
    rw [hr3.frame_arr "DA" (by decide)]; exact hDA2
  have hout3 : σ3.out = [] := by rw [hr3.out_eq (by decide)]; exact hout2
  have hk3solset : σ3.vars "k" = solutionSize (csrWord (decY y) (run init y).k) := by
    rw [hk3, hE.solutionSize_eq]
  -- Step 4: the "valid" == 1 gate, then progTail
  have hLB : offset (csrWord (decY y) (run init y).k)
      (setCount (csrWord (decY y) (run init y).k)) + 1 < B := by
    rw [hol]
    have h1 : foff (run init y).m + 1 < B := hOffValB _ le_rfl
    rw [hfoffm] at h1
    exact h1
  have hev1 : (V "valid").evalB B σ3 = some (σ3.vars "valid") := evalB_var (by omega)
  have hev2 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit (by omega)
  have hcond : (Cond.eq (V "valid") (.lit 1)).evalB B σ3 = some true := by
    rw [evalB_condEq hev1 hev2, hvalid1]; rfl
  obtain ⟨σ4, hr4, hout4⟩ := progTail_spec hE hxB hb hLB σ3
    ⟨hRC3, hk3solset, hout3, hMJ3, hMI3, hPA3, hQA3, hDA3⟩
  have hrite := Run.ite_true (d := rejectProg) hcond hr4
  have hph1' : σ1.vars "ph" = 2 := by rw [hph1]; exact hdone
  have hevph1 : (V "ph").evalB B σ1 = some (σ1.vars "ph") := evalB_var (by omega)
  have hevlit2ph : (Expr.lit 2).evalB B σ1 = some 2 := evalB_lit (by omega)
  have hphcond : (Cond.eq (V "ph") (.lit 2)).evalB B σ1 = some true := by
    rw [evalB_condEq hevph1 hevlit2ph, hph1']; rfl
  have hrph := Run.ite_true (d := rejectProg) hphcond (hr2.seq (hr3.seq hrite))
  refine ⟨σ4, ?_, hout4⟩
  show Run B totalProg σ0 σ4 _
  unfold totalProg
  exact (hr1.seq hrph).mono (by simp only [Expr.size, Cond.size]; omega)

end Lax496464Proofs.Ram.TotalProg
