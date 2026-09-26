import Lax496464Proofs.Ram.ScanModel
import Lax391470Proofs.ReadAll

/-!
# The scan, as an IMP+ program

`Ram/ScanModel.lean`'s `step`/`run` is a total function of a small state and one input
entry at a time, proved (there) to decode a genuine `HittingSet.encodeInstance P k`
correctly. This file is the actual word-RAM program: `Lax391470Proofs.ReadAll.readAll`
reads the whole tape into an array of *known* length `L` (always safe, whatever the tape
holds), and `scanLoop` then processes that array with a bounded `for i in [0, L)` loop —
one call to `stepCom` per entry, matching `step` exactly — so the *loop*'s own termination
never depends on the tape's content, only on the trusted count `L`. This is what makes the
program total on every numeric tape, which `Lax759944.RamPolytime`'s definition demands.
-/

namespace Lax496464Proofs.Ram.ScanProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ScanModel (St)

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- What `afterNumber` does once a number has finished: dispatch on `"tgt"`, using `"vv"`
as the value, writing `"n"`/`"m"`/`"k"`/`"sz"`/`"j"`/`"off"`/`"u"`/`"ph"`/`"tgt"` and the
`"OFFS"`/`"MEMS"` arrays. Does *not* touch `"cc"`/`"ii"`/`"vv"` — `afterNumberCom` resets
those uniformly afterwards, since every branch of `afterNumber` resets them the same way. -/
def dispatchBody : Com :=
  .ite (.eq (V "tgt") (.lit 0))
    (.seq (.assign "n" (V "vv")) (.seq (.assign "tgt" (.lit 1)) (.assign "ph" (.lit 0))))
    (.ite (.eq (V "tgt") (.lit 1))
      (.seq (.assign "m" (V "vv")) (.seq (.assign "tgt" (.lit 2)) (.assign "ph" (.lit 0))))
      (.ite (.eq (V "tgt") (.lit 2))
        (.ite (.eq (V "m") (.lit 0))
          (.seq (.assign "k" (V "vv")) (.seq (.assign "ph" (.lit 2)) (.seq (.assign "tgt" (.lit 0))
            (.seq (.assign "sz" (.lit 0)) (.store "OFFS" (.lit 0) (.lit 0))))))
          (.seq (.assign "k" (V "vv")) (.seq (.assign "ph" (.lit 0)) (.seq (.assign "tgt" (.lit 3))
            (.seq (.assign "sz" (.lit 0)) (.seq (.assign "j" (.lit 0)) (.seq (.assign "off" (.lit 0))
              (.store "OFFS" (.lit 0) (.lit 0)))))))))
        (.ite (.eq (V "tgt") (.lit 3))
          (.ite (.eq (V "vv") (.lit 0))
            (.seq (.store "OFFS" (.bin .add (V "j") (.lit 1)) (V "off"))
              (.ite (.lt (.bin .add (V "j") (.lit 1)) (V "m"))
                (.seq (.assign "sz" (.lit 0)) (.seq (.assign "u" (.lit 0))
                  (.seq (.assign "j" (.bin .add (V "j") (.lit 1))) (.seq (.assign "ph" (.lit 0))
                    (.assign "tgt" (.lit 3))))))
                (.seq (.assign "sz" (.lit 0)) (.seq (.assign "u" (.lit 0))
                  (.seq (.assign "ph" (.lit 2)) (.assign "tgt" (.lit 0)))))))
            (.seq (.assign "sz" (V "vv")) (.seq (.assign "u" (.lit 0)) (.seq (.assign "ph" (.lit 0))
              (.assign "tgt" (.lit 4))))))
          (.seq (.store "MEMS" (.bin .add (V "off") (V "u")) (V "vv"))
            (.ite (.lt (.bin .add (V "u") (.lit 1)) (V "sz"))
              (.seq (.assign "u" (.bin .add (V "u") (.lit 1))) (.seq (.assign "ph" (.lit 0))
                (.assign "tgt" (.lit 4))))
              (.seq (.assign "off" (.bin .add (V "off") (V "sz")))
                (.seq (.store "OFFS" (.bin .add (V "j") (.lit 1)) (V "off"))
                  (.ite (.lt (.bin .add (V "j") (.lit 1)) (V "m"))
                    (.seq (.assign "sz" (.lit 0)) (.seq (.assign "u" (.lit 0))
                      (.seq (.assign "j" (.bin .add (V "j") (.lit 1))) (.seq (.assign "ph" (.lit 0))
                        (.assign "tgt" (.lit 3))))))
                    (.seq (.assign "sz" (.lit 0)) (.seq (.assign "u" (.lit 0))
                      (.seq (.assign "ph" (.lit 2)) (.assign "tgt" (.lit 0)))))))))))))

/-- `dispatchBody`, then the uniform `"cc"`/`"ii"`/`"vv"` reset every branch of
`afterNumber` shares. -/
def afterNumberCom : Com :=
  .seq dispatchBody (.seq (.assign "cc" (.lit 0)) (.seq (.assign "ii" (.lit 0)) (.assign "vv" (.lit 0))))

/-- `ph = 0`, the entry is a `1`: bump the leading-ones counter. -/
def stepPh0B1 : Com := .assign "cc" (.bin .add (V "cc") (.lit 1))

/-- `ph = 0`, the entry is a `0`, `cc = 0`: a bare `0` is a self-delimited zero-bit number. -/
def stepPh0Cc0 : Com := .seq (.assign "vv" (.lit 0)) afterNumberCom

/-- `ph = 0`, the entry is a `0`, `cc > 0`: the leading ones are counted, start reading bits. -/
def stepPh0CcPos : Com :=
  .seq (.assign "ph" (.lit 1)) (.seq (.assign "ii" (.lit 0)) (.assign "vv" (.lit 0)))

/-- `ph = 0`: count leading `1`s, or (on the terminating `0`) dispatch or start reading bits. -/
def stepPh0 : Com :=
  .ite (.eq (V "b") (.lit 1)) stepPh0B1 (.ite (.eq (V "cc") (.lit 0)) stepPh0Cc0 stepPh0CcPos)

/-- `ph = 1`: fold the entry into `vv` at digit `ii`, advance `ii`. -/
def stepPh1Prefix : Com :=
  .seq (.assign "vv" (.bin .add (V "vv") (.bin .shiftl (V "b") (V "ii"))))
    (.assign "ii" (.bin .add (V "ii") (.lit 1)))

/-- `ph = 1`: read one more digit, then continue reading or dispatch once `cc` digits are in. -/
def stepPh1 : Com :=
  .seq stepPh1Prefix (.ite (.lt (V "ii") (V "cc")) .skip afterNumberCom)

/-- One call of `ScanModel.step`, reading the current entry from `"b"`. -/
def stepCom : Com :=
  .ite (.eq (V "ph") (.lit 0)) stepPh0 (.ite (.eq (V "ph") (.lit 1)) stepPh1 .skip)

/-- Read the array entry into `"b"`, run one step, advance the counter. -/
def scanBody : Com :=
  .seq (.assign "b" (.get "a" (V "i"))) (.seq stepCom (bump "i"))

/-- Scan the whole array `"a"`, of length `"L"`. -/
def scanLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "L")) scanBody)

/-- The scan's scalars, at `ScanModel.init`. -/
def initVars : Com :=
  .seq (.assign "ph" (.lit 0)) (.seq (.assign "tgt" (.lit 0)) (.seq (.assign "cc" (.lit 0))
    (.seq (.assign "ii" (.lit 0)) (.seq (.assign "vv" (.lit 0)) (.seq (.assign "n" (.lit 0))
      (.seq (.assign "m" (.lit 0)) (.seq (.assign "k" (.lit 0)) (.seq (.assign "j" (.lit 0))
        (.seq (.assign "u" (.lit 0)) (.seq (.assign "sz" (.lit 0)) (.assign "off" (.lit 0))))))))))))

/-- **The whole parse**: read the tape, then scan it. -/
def parseCom : Com :=
  .seq Lax391470Proofs.ReadAll.readAll (.seq initVars scanLoop)

/-! ## The scan's state, on the machine -/

open Lax496464Proofs.Ram.ScanModel (afterNumber step run Struct)

/-- `σ` presents `s`'s fields other than `"cc"`/`"ii"`/`"vv"` — the "resting" fields, true
throughout, plus the `"OFFS"`/`"MEMS"` arrays (fixed at `OFFLEN`/`MEMLEN` throughout — chosen
once, generously, by the caller) agreeing with `s.offs`/`s.mems` everywhere those are
defined. -/
def MatchesRest (OFFLEN MEMLEN : ℕ) (s : St) (σ : Env) : Prop :=
  σ.vars "ph" = s.ph ∧ σ.vars "tgt" = s.tgt ∧
  σ.vars "n" = s.n ∧ σ.vars "m" = s.m ∧ σ.vars "k" = s.k ∧
  σ.vars "j" = s.j ∧ σ.vars "u" = s.u ∧ σ.vars "sz" = s.sz ∧ σ.vars "off" = s.off ∧
  (σ.arrs "OFFS").length = OFFLEN ∧ (σ.arrs "MEMS").length = MEMLEN ∧
  (∀ t < s.offs.length, (σ.arrs "OFFS").getD t 0 = s.offs.getD t 0) ∧
  (∀ t < s.mems.length, (σ.arrs "MEMS").getD t 0 = s.mems.getD t 0)

/-- `σ` presents the scan state `s` in full. -/
def Matches (OFFLEN MEMLEN : ℕ) (s : St) (σ : Env) : Prop :=
  MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "cc" = s.cc ∧ σ.vars "ii" = s.ii ∧ σ.vars "vv" = s.vv

/-- The shared tail every branch of `afterNumber` ends with: zero `"cc"`/`"ii"`/`"vv"`,
touching nothing else. -/
theorem resetCcIiVv_spec {B : ℕ} (hB : 0 < B) :
    Spec B (fun _ => True)
      (.seq (.assign "cc" (.lit 0)) (.seq (.assign "ii" (.lit 0)) (.assign "vv" (.lit 0))))
      (fun σ σ' => σ'.vars "cc" = 0 ∧ σ'.vars "ii" = 0 ∧ σ'.vars "vv" = 0 ∧
        (∀ y, y ≠ "cc" → y ≠ "ii" → y ≠ "vv" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs) 9 := by
  run_vcg
  all_goals (simp_all)

/-- `MatchesRest` only mentions vars other than `"cc"`/`"ii"`/`"vv"` and the arrays, so it
survives to any state agreeing with `σ` on those. -/
theorem MatchesRest.congr {OFFLEN MEMLEN : ℕ} {s : St} {σ σ' : Env}
    (h : MatchesRest OFFLEN MEMLEN s σ)
    (hv : ∀ y, y ≠ "cc" → y ≠ "ii" → y ≠ "vv" → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) : MatchesRest OFFLEN MEMLEN s σ' := by
  simp only [MatchesRest] at h ⊢
  rw [hv "ph" (by decide) (by decide) (by decide), hv "tgt" (by decide) (by decide) (by decide),
      hv "n" (by decide) (by decide) (by decide), hv "m" (by decide) (by decide) (by decide),
      hv "k" (by decide) (by decide) (by decide), hv "j" (by decide) (by decide) (by decide),
      hv "u" (by decide) (by decide) (by decide), hv "sz" (by decide) (by decide) (by decide),
      hv "off" (by decide) (by decide) (by decide), ha]
  exact h

/-- `MatchesRest.congr`, but when only a single named scalar (not `"cc"`/`"ii"`/`"vv"`) or a
single named array changed — no need for a blanket "every other var" hypothesis, which a
transfer across a `"b"`/`"i"`-touching assign genuinely cannot supply (those two *do* change,
and aren't excluded by the `cc`/`ii`/`vv` guard). -/
theorem MatchesRest.congr2 {OFFLEN MEMLEN : ℕ} {s : St} {σ σ' : Env}
    (h : MatchesRest OFFLEN MEMLEN s σ)
    (h1 : σ'.vars "ph" = σ.vars "ph") (h2 : σ'.vars "tgt" = σ.vars "tgt")
    (h3 : σ'.vars "n" = σ.vars "n") (h4 : σ'.vars "m" = σ.vars "m")
    (h5 : σ'.vars "k" = σ.vars "k") (h6 : σ'.vars "j" = σ.vars "j")
    (h7 : σ'.vars "u" = σ.vars "u") (h8 : σ'.vars "sz" = σ.vars "sz")
    (h9 : σ'.vars "off" = σ.vars "off")
    (ha1 : σ'.arrs "OFFS" = σ.arrs "OFFS") (ha2 : σ'.arrs "MEMS" = σ.arrs "MEMS") :
    MatchesRest OFFLEN MEMLEN s σ' := by
  simp only [MatchesRest] at h ⊢
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, ha1, ha2]
  exact h

/-- `Matches` survives setting any scalar other than the twelve it names — the shape needed
every time a `Spec.frame` exposes "untouched" facts for a scalar (`"b"`, `"i"`, `"L"`) that
isn't itself one of them. -/
theorem Matches.setVar_unrelated {OFFLEN MEMLEN : ℕ} {s : St} {σ : Env}
    (h : Matches OFFLEN MEMLEN s σ) (x : String)
    (hx1 : "ph" ≠ x) (hx2 : "tgt" ≠ x) (hx3 : "n" ≠ x) (hx4 : "m" ≠ x) (hx5 : "k" ≠ x)
    (hx6 : "j" ≠ x) (hx7 : "u" ≠ x) (hx8 : "sz" ≠ x) (hx9 : "off" ≠ x) (hx10 : "cc" ≠ x)
    (hx11 : "ii" ≠ x) (hx12 : "vv" ≠ x) (v : ℕ) :
    Matches OFFLEN MEMLEN s (σ.setVar x v) := by
  obtain ⟨⟨hph, htgt, hn, hm, hk, hj, hu, hsz, hoff, hOL, hML, hoffs, hmems⟩, hcc, hii, hvv⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp_all [Env.setVar]

/-- Incrementing a scalar, on its own. -/
theorem bump_spec {B : ℕ} (x : String) (v : ℕ) (hB : v + 1 < B) :
    Spec B (fun σ => σ.vars x = v) (bump x) (fun _ σ' => σ'.vars x = v + 1) 10 := by
  run_vcg
  all_goals (simp_all)

/-! ## The trivial `stepCom` leaves: those touching no array and calling no `afterNumberCom` -/

theorem stepPh0B1_spec {B OFFLEN MEMLEN : ℕ} (s : St) (hB : s.cc + 1 < B ∧ 5 < B) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ) stepPh0B1
      (fun _ σ' => Matches OFFLEN MEMLEN { s with cc := s.cc + 1 } σ') 10 := by
  run_vcg
  all_goals (simp_all [Matches, MatchesRest])
  all_goals omega

theorem stepPh0CcPos_spec {B OFFLEN MEMLEN : ℕ} (s : St) (hB : 5 < B) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ) stepPh0CcPos
      (fun _ σ' => Matches OFFLEN MEMLEN { s with ph := 1, ii := 0, vv := 0 } σ') 15 := by
  run_vcg
  all_goals (simp_all [Matches, MatchesRest])

theorem stepPh1Prefix_spec {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ)
    (hB : s.vv + b * 2 ^ s.ii < B ∧ s.ii + 1 < B ∧ b < B ∧ 5 < B) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepPh1Prefix
      (fun _ σ' => Matches OFFLEN MEMLEN { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } σ') 15 := by
  run_vcg
  all_goals (simp_all [Matches, MatchesRest])
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem dispatchBody_spec_tgt0 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 0)
    (hB : s.n < B ∧ v < B ∧ 5 < B) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) dispatchBody
      (fun σ σ' => MatchesRest OFFLEN MEMLEN (afterNumber s v) σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧
        σ'.vars "ii" = σ.vars "ii" ∧ σ'.vars "vv" = σ.vars "vv") 1000 := by
  run_vcg
  all_goals (simp_all [MatchesRest, afterNumber])
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem dispatchBody_spec_tgt1 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 1)
    (hB : s.m < B ∧ v < B ∧ 5 < B) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) dispatchBody
      (fun σ σ' => MatchesRest OFFLEN MEMLEN (afterNumber s v) σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧
        σ'.vars "ii" = σ.vars "ii" ∧ σ'.vars "vv" = σ.vars "vv") 1000 := by
  run_vcg
  all_goals (simp_all [MatchesRest, afterNumber])
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem dispatchBody_spec_tgt2 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 2)
    (hB : s.m < B ∧ v < B ∧ 5 < B) (hOFFLEN : 0 < OFFLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) dispatchBody
      (fun σ σ' => MatchesRest OFFLEN MEMLEN (afterNumber s v) σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧
        σ'.vars "ii" = σ.vars "ii" ∧ σ'.vars "vv" = σ.vars "vv") 1000 := by
  by_cases hm : s.m = 0 <;>
    (run_vcg
     all_goals (simp_all [MatchesRest, afterNumber])
     all_goals omega)

set_option maxHeartbeats 4000000 in
theorem dispatchBody_spec_tgt3 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 3)
    (hoffs : s.offs.length = s.j + 1)
    (hB : s.m < B ∧ v < B ∧ s.j + 1 < B ∧ s.off < B ∧ 5 < B) (hOFFLEN : s.j + 1 < OFFLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) dispatchBody
      (fun σ σ' => MatchesRest OFFLEN MEMLEN (afterNumber s v) σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧
        σ'.vars "ii" = σ.vars "ii" ∧ σ'.vars "vv" = σ.vars "vv") 1000 := by
  by_cases hv : v = 0
  · by_cases hjm : s.j + 1 < s.m
    · run_vcg
      all_goals (simp_all [MatchesRest, afterNumber])
      all_goals (try
        (intro t ht
         rcases Nat.lt_or_ge t s.offs.length with hlt | hge
         · have hne : s.j + 1 ≠ t := by omega
           simp_all [List.getElem?_set_ne, List.getElem_append_left]
         · have heq : t = s.offs.length := by omega
           simp_all))
      all_goals omega
    · run_vcg
      all_goals (simp_all [MatchesRest, afterNumber, if_neg hjm])
      all_goals (try
        (intro t ht
         rcases Nat.lt_or_ge t s.offs.length with hlt | hge
         · have hne : s.j + 1 ≠ t := by omega
           simp_all [List.getElem?_set_ne, List.getElem_append_left]
         · have heq : t = s.offs.length := by omega
           simp_all))
      all_goals omega
  · run_vcg
    all_goals (simp_all [MatchesRest, afterNumber])
    all_goals omega

/-- Closes a residual `∀ t ≤ n, (l.set n a)[t]?.getD 0 = (xs ++ [a])[t]`-shaped goal for a
CSR-style "append one entry, store it at the freshly-opened cell" invariant: split on whether
`t` is one of the untouched old cells or the fresh one just written. -/
macro "close_snoc_getD" xs:term : tactic =>
  `(tactic| (try
    (intro t ht
     rcases Nat.lt_or_ge t ($xs).length with hlt | hge
     · have hne : ($xs).length ≠ t := by omega
       simp_all [List.getElem?_set_self', List.getElem?_set_ne, List.getElem_append_left]
     · have heq : t = ($xs).length := by omega
       simp_all [List.getElem?_set_self', List.getElem_concat_length])))

set_option maxHeartbeats 4000000 in
theorem dispatchBody_spec_tgt4 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ)
    (hstgt : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3)
    (hoffs : s.offs.length = s.j + 1) (hmems : s.mems.length = s.off + s.u)
    (hB : s.m < B ∧ v < B ∧ s.j + 1 < B ∧ s.off + s.sz < B ∧ s.off + s.u < B ∧
      s.u + 1 < B ∧ s.tgt < B ∧ 5 < B)
    (hOFFLEN : s.j + 1 < OFFLEN) (hMEMLEN : s.off + s.u < MEMLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) dispatchBody
      (fun σ σ' => MatchesRest OFFLEN MEMLEN (afterNumber s v) σ' ∧ σ'.vars "cc" = σ.vars "cc" ∧
        σ'.vars "ii" = σ.vars "ii" ∧ σ'.vars "vv" = σ.vars "vv") 1000 := by
  by_cases hcont : s.u + 1 < s.sz
  · run_vcg
    all_goals (simp_all [MatchesRest, afterNumber])
    all_goals close_snoc_getD s.mems
    all_goals omega
  · by_cases hjm : s.j + 1 < s.m
    · run_vcg
      all_goals (simp_all [MatchesRest, afterNumber, if_neg hcont])
      all_goals (try constructor)
      all_goals close_snoc_getD s.mems
      all_goals close_snoc_getD s.offs
      all_goals omega
    · run_vcg
      all_goals (simp_all [MatchesRest, afterNumber, if_neg hcont, if_neg hjm])
      all_goals (try constructor)
      all_goals close_snoc_getD s.mems
      all_goals close_snoc_getD s.offs
      all_goals omega

/-! ## `afterNumberCom`: `dispatchBody` plus the shared `"cc"`/`"ii"`/`"vv"` reset -/

set_option maxHeartbeats 4000000 in
theorem afterNumberCom_spec_tgt0 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 0)
    (hB : s.n < B ∧ v < B ∧ 5 < B) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) afterNumberCom
      (fun _ σ'' => Matches OFFLEN MEMLEN (afterNumber s v) σ'') 1009 := by
  refine (dispatchBody_spec_tgt0 s v hstgt hB).seq (resetCcIiVv_spec (by omega))
    (fun _ _ _ _ => trivial) (fun σ σ' σ'' _ hQ hQ' => ?_)
  obtain ⟨hmr, _, _, _⟩ := hQ
  obtain ⟨hcc, hii, hvv, hv, ha⟩ := hQ'
  refine ⟨hmr.congr hv ha, ?_, ?_, ?_⟩ <;> (simp only [afterNumber]; split_ifs <;> simp_all)

set_option maxHeartbeats 4000000 in
theorem afterNumberCom_spec_tgt1 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 1)
    (hB : s.m < B ∧ v < B ∧ 5 < B) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) afterNumberCom
      (fun _ σ'' => Matches OFFLEN MEMLEN (afterNumber s v) σ'') 1009 := by
  refine (dispatchBody_spec_tgt1 s v hstgt hB).seq (resetCcIiVv_spec (by omega))
    (fun _ _ _ _ => trivial) (fun σ σ' σ'' _ hQ hQ' => ?_)
  obtain ⟨hmr, _, _, _⟩ := hQ
  obtain ⟨hcc, hii, hvv, hv, ha⟩ := hQ'
  refine ⟨hmr.congr hv ha, ?_, ?_, ?_⟩ <;> (simp only [afterNumber]; split_ifs <;> simp_all)

set_option maxHeartbeats 4000000 in
theorem afterNumberCom_spec_tgt2 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 2)
    (hB : s.m < B ∧ v < B ∧ 5 < B) (hOFFLEN : 0 < OFFLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) afterNumberCom
      (fun _ σ'' => Matches OFFLEN MEMLEN (afterNumber s v) σ'') 1009 := by
  refine (dispatchBody_spec_tgt2 s v hstgt hB hOFFLEN).seq (resetCcIiVv_spec (by omega))
    (fun _ _ _ _ => trivial) (fun σ σ' σ'' _ hQ hQ' => ?_)
  obtain ⟨hmr, _, _, _⟩ := hQ
  obtain ⟨hcc, hii, hvv, hv, ha⟩ := hQ'
  refine ⟨hmr.congr hv ha, ?_, ?_, ?_⟩ <;> (simp only [afterNumber]; split_ifs <;> simp_all)

set_option maxHeartbeats 4000000 in
theorem afterNumberCom_spec_tgt3 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ) (hstgt : s.tgt = 3)
    (hoffs : s.offs.length = s.j + 1)
    (hB : s.m < B ∧ v < B ∧ s.j + 1 < B ∧ s.off < B ∧ 5 < B) (hOFFLEN : s.j + 1 < OFFLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) afterNumberCom
      (fun _ σ'' => Matches OFFLEN MEMLEN (afterNumber s v) σ'') 1009 := by
  refine (dispatchBody_spec_tgt3 s v hstgt hoffs hB hOFFLEN).seq (resetCcIiVv_spec (by omega))
    (fun _ _ _ _ => trivial) (fun σ σ' σ'' _ hQ hQ' => ?_)
  obtain ⟨hmr, _, _, _⟩ := hQ
  obtain ⟨hcc, hii, hvv, hv, ha⟩ := hQ'
  refine ⟨hmr.congr hv ha, ?_, ?_, ?_⟩ <;> (simp only [afterNumber]; split_ifs <;> simp_all)

set_option maxHeartbeats 4000000 in
theorem afterNumberCom_spec_tgt4 {B OFFLEN MEMLEN : ℕ} (s : St) (v : ℕ)
    (hstgt : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3)
    (hoffs : s.offs.length = s.j + 1) (hmems : s.mems.length = s.off + s.u)
    (hB : s.m < B ∧ v < B ∧ s.j + 1 < B ∧ s.off + s.sz < B ∧ s.off + s.u < B ∧
      s.u + 1 < B ∧ s.tgt < B ∧ 5 < B)
    (hOFFLEN : s.j + 1 < OFFLEN) (hMEMLEN : s.off + s.u < MEMLEN) :
    Spec B (fun σ => MatchesRest OFFLEN MEMLEN s σ ∧ σ.vars "vv" = v) afterNumberCom
      (fun _ σ'' => Matches OFFLEN MEMLEN (afterNumber s v) σ'') 1009 := by
  refine (dispatchBody_spec_tgt4 s v hstgt hoffs hmems hB hOFFLEN hMEMLEN).seq
    (resetCcIiVv_spec (by omega)) (fun _ _ _ _ => trivial) (fun σ σ' σ'' _ hQ hQ' => ?_)
  obtain ⟨hmr, _, _, _⟩ := hQ
  obtain ⟨hcc, hii, hvv, hv, ha⟩ := hQ'
  refine ⟨hmr.congr hv ha, ?_, ?_, ?_⟩ <;> (simp only [afterNumber]; split_ifs <;> simp_all)

/-! ## `stepCom`: one full call of `ScanModel.step`

`run_vcg` unfolds `afterNumberCom` (hence `dispatchBody`) wherever it appears, so it cannot be
used on any Com containing it — these proofs are assembled from `Run`/`Spec` primitives by hand
instead, deciding each branch's condition from a `by_cases` on the concrete field values of `s`/
`b` (via `Lax808846Proofs.Reasoning.RunStep`'s `cond_eq_true`/`cond_eq_false`/`cond_lt_true`/
`cond_lt_false`, which build an `evalB = some true/false` fact *forwards* from a known equality or
inequality) and combining with `Run.ite_true`/`Run.ite_false`/`Run.seq`, padded to a common cost
with a single `.mono` per branch. Split into one theorem per `s.tgt` value (mirroring
`dispatchBody_spec_tgtN`/`afterNumberCom_spec_tgtN`) since `s.tgt` is unchanged by one `step` call
before it dispatches, so both of `stepCom`'s `afterNumberCom` call sites (`stepPh0Cc0`'s, and
`stepPh1`'s `ii + 1 ≥ cc` branch) use the *same* `afterNumberCom_spec_tgtN` within one theorem. -/

open Lax808846Proofs.Reasoning.RunStep

set_option maxHeartbeats 4000000 in
theorem stepCom_spec_tgt0 {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ) (hstgt : s.tgt = 0)
    (hB : s.ph < B ∧ s.n < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ 5 < B) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  intro σ hσ
  obtain ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩ := hσ
  have hphB : σ.vars "ph" < B := hmr.1 ▸ hB.1
  by_cases hph0 : s.ph = 0
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some true :=
      cond_eq_true B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph0])
    by_cases hb1 : b = 1
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq, hb1])
      have hstep : step s b = { s with cc := s.cc + 1 } := by simp [step, hph0, hb1]
      obtain ⟨σ', hr, hq⟩ := (stepPh0B1_spec s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.1, hB.2.2.2.2.2.2.2⟩) σ ⟨hmr, hcc, hii, hvv⟩
      refine ⟨σ', (Run.ite_true hv1 (Run.ite_true hv2 hr)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact hq
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq]; exact hb1)
      by_cases hcc0 : s.cc = 0
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some true :=
          cond_eq_true B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc, hcc0])
        have hstep : step s b = afterNumber s 0 := by simp [step, hph0, hb1, hcc0]
        have hassign : Run B (.assign "vv" (Expr.lit 0)) σ (σ.setVar "vv" 0) 2 :=
          Run.assign (evalB_lit (by omega))
        have hmr' : MatchesRest OFFLEN MEMLEN s (σ.setVar "vv" 0) :=
          hmr.congr (fun y _ _ hy3 => by simp [Env.setVar, hy3]) rfl
        have hvv' : (σ.setVar "vv" 0).vars "vv" = 0 := by simp [Env.setVar]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt0 s 0 hstgt ⟨hB.2.1, by omega, by omega⟩)
          (σ.setVar "vv" 0) ⟨hmr', hvv'⟩
        refine ⟨σ'', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_true hv3
          (hassign.seq hr2)))).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some false :=
          cond_eq_false B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc]; exact hcc0)
        have hstep : step s b = { s with ph := 1, ii := 0, vv := 0 } := by
          simp [step, hph0, hb1, hcc0]
        obtain ⟨σ', hr, hq⟩ := (stepPh0CcPos_spec (B := B) s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
          (by omega)) σ ⟨hmr, hcc, hii, hvv⟩
        refine ⟨σ', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_false hv3 hr))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some false :=
      cond_eq_false B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph0)
    by_cases hph1 : s.ph = 1
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph1])
      obtain ⟨σ1, hr1, hM1⟩ := (stepPh1Prefix_spec s b (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1, hbeq ▸ hB.2.2.1, by omega⟩) σ ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩
      obtain ⟨hmr1, hcc1, hii1, hvv1⟩ := hM1
      have hs1ii : (σ1).vars "ii" < B := by rw [hii1]; simp; omega
      have hs1cc : (σ1).vars "cc" < B := by rw [hcc1]; simp; omega
      by_cases hlt : s.ii + 1 < s.cc
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some true :=
          cond_lt_true B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } := by
          simp [step, hph1, hlt]
        refine ⟨σ1, (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_true hv3 Run.skip)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact ⟨hmr1, hcc1, hii1, hvv1⟩
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some false :=
          cond_lt_false B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = afterNumber s (s.vv + b * 2 ^ s.ii) := by
          simp [step, hph1, hlt]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt0
          ({ s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 }) (s.vv + b * 2 ^ s.ii) hstgt
          ⟨by simpa using hB.2.1, by omega, by omega⟩) σ1 ⟨hmr1, hvv1⟩
        refine ⟨σ'', (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_false hv3 hr2)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph1)
      have hstep : step s b = s := by simp [step, hph0, hph1]
      refine ⟨σ, (Run.ite_false hv1 (Run.ite_false hv2 Run.skip)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact ⟨hmr, hcc, hii, hvv⟩

set_option maxHeartbeats 4000000 in
theorem stepCom_spec_tgt1 {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ) (hstgt : s.tgt = 1)
    (hB : s.ph < B ∧ s.m < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ 5 < B) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  intro σ hσ
  obtain ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩ := hσ
  have hphB : σ.vars "ph" < B := hmr.1 ▸ hB.1
  by_cases hph0 : s.ph = 0
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some true :=
      cond_eq_true B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph0])
    by_cases hb1 : b = 1
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq, hb1])
      have hstep : step s b = { s with cc := s.cc + 1 } := by simp [step, hph0, hb1]
      obtain ⟨σ', hr, hq⟩ := (stepPh0B1_spec s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.1, hB.2.2.2.2.2.2.2⟩) σ ⟨hmr, hcc, hii, hvv⟩
      refine ⟨σ', (Run.ite_true hv1 (Run.ite_true hv2 hr)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact hq
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq]; exact hb1)
      by_cases hcc0 : s.cc = 0
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some true :=
          cond_eq_true B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc, hcc0])
        have hstep : step s b = afterNumber s 0 := by simp [step, hph0, hb1, hcc0]
        have hassign : Run B (.assign "vv" (Expr.lit 0)) σ (σ.setVar "vv" 0) 2 :=
          Run.assign (evalB_lit (by omega))
        have hmr' : MatchesRest OFFLEN MEMLEN s (σ.setVar "vv" 0) :=
          hmr.congr (fun y _ _ hy3 => by simp [Env.setVar, hy3]) rfl
        have hvv' : (σ.setVar "vv" 0).vars "vv" = 0 := by simp [Env.setVar]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt1 s 0 hstgt ⟨hB.2.1, by omega, by omega⟩)
          (σ.setVar "vv" 0) ⟨hmr', hvv'⟩
        refine ⟨σ'', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_true hv3
          (hassign.seq hr2)))).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some false :=
          cond_eq_false B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc]; exact hcc0)
        have hstep : step s b = { s with ph := 1, ii := 0, vv := 0 } := by
          simp [step, hph0, hb1, hcc0]
        obtain ⟨σ', hr, hq⟩ := (stepPh0CcPos_spec (B := B) s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
          (by omega)) σ ⟨hmr, hcc, hii, hvv⟩
        refine ⟨σ', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_false hv3 hr))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some false :=
      cond_eq_false B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph0)
    by_cases hph1 : s.ph = 1
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph1])
      obtain ⟨σ1, hr1, hM1⟩ := (stepPh1Prefix_spec s b (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1, hbeq ▸ hB.2.2.1, by omega⟩) σ ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩
      obtain ⟨hmr1, hcc1, hii1, hvv1⟩ := hM1
      have hs1ii : (σ1).vars "ii" < B := by rw [hii1]; simp; omega
      have hs1cc : (σ1).vars "cc" < B := by rw [hcc1]; simp; omega
      by_cases hlt : s.ii + 1 < s.cc
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some true :=
          cond_lt_true B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } := by
          simp [step, hph1, hlt]
        refine ⟨σ1, (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_true hv3 Run.skip)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact ⟨hmr1, hcc1, hii1, hvv1⟩
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some false :=
          cond_lt_false B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = afterNumber s (s.vv + b * 2 ^ s.ii) := by
          simp [step, hph1, hlt]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt1
          ({ s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 }) (s.vv + b * 2 ^ s.ii) hstgt
          ⟨by simpa using hB.2.1, by omega, by omega⟩) σ1 ⟨hmr1, hvv1⟩
        refine ⟨σ'', (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_false hv3 hr2)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph1)
      have hstep : step s b = s := by simp [step, hph0, hph1]
      refine ⟨σ, (Run.ite_false hv1 (Run.ite_false hv2 Run.skip)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact ⟨hmr, hcc, hii, hvv⟩

set_option maxHeartbeats 4000000 in
theorem stepCom_spec_tgt2 {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ) (hstgt : s.tgt = 2)
    (hB : s.ph < B ∧ s.m < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ 5 < B) (hOFFLEN : 0 < OFFLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  intro σ hσ
  obtain ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩ := hσ
  have hphB : σ.vars "ph" < B := hmr.1 ▸ hB.1
  by_cases hph0 : s.ph = 0
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some true :=
      cond_eq_true B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph0])
    by_cases hb1 : b = 1
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq, hb1])
      have hstep : step s b = { s with cc := s.cc + 1 } := by simp [step, hph0, hb1]
      obtain ⟨σ', hr, hq⟩ := (stepPh0B1_spec s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.1, hB.2.2.2.2.2.2.2⟩) σ ⟨hmr, hcc, hii, hvv⟩
      refine ⟨σ', (Run.ite_true hv1 (Run.ite_true hv2 hr)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact hq
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq]; exact hb1)
      by_cases hcc0 : s.cc = 0
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some true :=
          cond_eq_true B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc, hcc0])
        have hstep : step s b = afterNumber s 0 := by simp [step, hph0, hb1, hcc0]
        have hassign : Run B (.assign "vv" (Expr.lit 0)) σ (σ.setVar "vv" 0) 2 :=
          Run.assign (evalB_lit (by omega))
        have hmr' : MatchesRest OFFLEN MEMLEN s (σ.setVar "vv" 0) :=
          hmr.congr (fun y _ _ hy3 => by simp [Env.setVar, hy3]) rfl
        have hvv' : (σ.setVar "vv" 0).vars "vv" = 0 := by simp [Env.setVar]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt2 s 0 hstgt ⟨hB.2.1, by omega, by omega⟩ hOFFLEN)
          (σ.setVar "vv" 0) ⟨hmr', hvv'⟩
        refine ⟨σ'', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_true hv3
          (hassign.seq hr2)))).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some false :=
          cond_eq_false B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc]; exact hcc0)
        have hstep : step s b = { s with ph := 1, ii := 0, vv := 0 } := by
          simp [step, hph0, hb1, hcc0]
        obtain ⟨σ', hr, hq⟩ := (stepPh0CcPos_spec (B := B) s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
          (by omega)) σ ⟨hmr, hcc, hii, hvv⟩
        refine ⟨σ', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_false hv3 hr))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some false :=
      cond_eq_false B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph0)
    by_cases hph1 : s.ph = 1
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph1])
      obtain ⟨σ1, hr1, hM1⟩ := (stepPh1Prefix_spec s b (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1, hbeq ▸ hB.2.2.1, by omega⟩) σ ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩
      obtain ⟨hmr1, hcc1, hii1, hvv1⟩ := hM1
      have hs1ii : (σ1).vars "ii" < B := by rw [hii1]; simp; omega
      have hs1cc : (σ1).vars "cc" < B := by rw [hcc1]; simp; omega
      by_cases hlt : s.ii + 1 < s.cc
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some true :=
          cond_lt_true B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } := by
          simp [step, hph1, hlt]
        refine ⟨σ1, (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_true hv3 Run.skip)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact ⟨hmr1, hcc1, hii1, hvv1⟩
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some false :=
          cond_lt_false B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = afterNumber s (s.vv + b * 2 ^ s.ii) := by
          simp [step, hph1, hlt]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt2
          ({ s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 }) (s.vv + b * 2 ^ s.ii) hstgt
          ⟨by simpa using hB.2.1, by omega, by omega⟩ hOFFLEN) σ1 ⟨hmr1, hvv1⟩
        refine ⟨σ'', (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_false hv3 hr2)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph1)
      have hstep : step s b = s := by simp [step, hph0, hph1]
      refine ⟨σ, (Run.ite_false hv1 (Run.ite_false hv2 Run.skip)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact ⟨hmr, hcc, hii, hvv⟩

set_option maxHeartbeats 4000000 in
theorem stepCom_spec_tgt3 {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ) (hstgt : s.tgt = 3)
    (hoffs : s.offs.length = s.j + 1)
    (hB : s.ph < B ∧ s.m < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ s.j + 1 < B ∧ s.off < B ∧ 5 < B) (hOFFLEN : s.j + 1 < OFFLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  intro σ hσ
  obtain ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩ := hσ
  have hphB : σ.vars "ph" < B := hmr.1 ▸ hB.1
  by_cases hph0 : s.ph = 0
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some true :=
      cond_eq_true B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph0])
    by_cases hb1 : b = 1
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq, hb1])
      have hstep : step s b = { s with cc := s.cc + 1 } := by simp [step, hph0, hb1]
      obtain ⟨σ', hr, hq⟩ := (stepPh0B1_spec s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.1, by omega⟩) σ ⟨hmr, hcc, hii, hvv⟩
      refine ⟨σ', (Run.ite_true hv1 (Run.ite_true hv2 hr)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact hq
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq]; exact hb1)
      by_cases hcc0 : s.cc = 0
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some true :=
          cond_eq_true B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc, hcc0])
        have hstep : step s b = afterNumber s 0 := by simp [step, hph0, hb1, hcc0]
        have hassign : Run B (.assign "vv" (Expr.lit 0)) σ (σ.setVar "vv" 0) 2 :=
          Run.assign (evalB_lit (by omega))
        have hmr' : MatchesRest OFFLEN MEMLEN s (σ.setVar "vv" 0) :=
          hmr.congr (fun y _ _ hy3 => by simp [Env.setVar, hy3]) rfl
        have hvv' : (σ.setVar "vv" 0).vars "vv" = 0 := by simp [Env.setVar]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt3 s 0 hstgt hoffs ⟨hB.2.1, by omega, by omega, by omega, by omega⟩ hOFFLEN)
          (σ.setVar "vv" 0) ⟨hmr', hvv'⟩
        refine ⟨σ'', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_true hv3
          (hassign.seq hr2)))).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some false :=
          cond_eq_false B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc]; exact hcc0)
        have hstep : step s b = { s with ph := 1, ii := 0, vv := 0 } := by
          simp [step, hph0, hb1, hcc0]
        obtain ⟨σ', hr, hq⟩ := (stepPh0CcPos_spec (B := B) s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
          (by omega)) σ ⟨hmr, hcc, hii, hvv⟩
        refine ⟨σ', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_false hv3 hr))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some false :=
      cond_eq_false B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph0)
    by_cases hph1 : s.ph = 1
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph1])
      obtain ⟨σ1, hr1, hM1⟩ := (stepPh1Prefix_spec s b (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1, hbeq ▸ hB.2.2.1, by omega⟩) σ ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩
      obtain ⟨hmr1, hcc1, hii1, hvv1⟩ := hM1
      have hs1ii : (σ1).vars "ii" < B := by rw [hii1]; simp; omega
      have hs1cc : (σ1).vars "cc" < B := by rw [hcc1]; simp; omega
      by_cases hlt : s.ii + 1 < s.cc
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some true :=
          cond_lt_true B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } := by
          simp [step, hph1, hlt]
        refine ⟨σ1, (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_true hv3 Run.skip)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact ⟨hmr1, hcc1, hii1, hvv1⟩
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some false :=
          cond_lt_false B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = afterNumber s (s.vv + b * 2 ^ s.ii) := by
          simp [step, hph1, hlt]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt3
          ({ s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 }) (s.vv + b * 2 ^ s.ii) hstgt
          (by simpa using hoffs)
          ⟨by simpa using hB.2.1, by omega, by simp; omega, by simp; omega, by omega⟩
          (by simpa using hOFFLEN)) σ1 ⟨hmr1, hvv1⟩
        refine ⟨σ'', (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_false hv3 hr2)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph1)
      have hstep : step s b = s := by simp [step, hph0, hph1]
      refine ⟨σ, (Run.ite_false hv1 (Run.ite_false hv2 Run.skip)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact ⟨hmr, hcc, hii, hvv⟩

set_option maxHeartbeats 4000000 in
theorem stepCom_spec_tgt4 {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ)
    (hstgt : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3)
    (hoffs : s.offs.length = s.j + 1) (hmems : s.mems.length = s.off + s.u)
    (hB : s.ph < B ∧ s.m < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ s.j + 1 < B ∧ s.off + s.sz < B ∧ s.off + s.u < B ∧ s.u + 1 < B ∧
      s.tgt < B ∧ 5 < B) (hOFFLEN : s.j + 1 < OFFLEN) (hMEMLEN : s.off + s.u < MEMLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  intro σ hσ
  obtain ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩ := hσ
  have hphB : σ.vars "ph" < B := hmr.1 ▸ hB.1
  by_cases hph0 : s.ph = 0
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some true :=
      cond_eq_true B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph0])
    by_cases hb1 : b = 1
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq, hb1])
      have hstep : step s b = { s with cc := s.cc + 1 } := by simp [step, hph0, hb1]
      obtain ⟨σ', hr, hq⟩ := (stepPh0B1_spec s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.1, by omega⟩) σ ⟨hmr, hcc, hii, hvv⟩
      refine ⟨σ', (Run.ite_true hv1 (Run.ite_true hv2 hr)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact hq
    · have hv2 : (Cond.eq (V "b") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "b") (Expr.lit 1) (σ.vars "b") 1
          (evalB_var (hbeq ▸ hB.2.2.1)) (evalB_lit (by omega)) (by rw [hbeq]; exact hb1)
      by_cases hcc0 : s.cc = 0
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some true :=
          cond_eq_true B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc, hcc0])
        have hstep : step s b = afterNumber s 0 := by simp [step, hph0, hb1, hcc0]
        have hassign : Run B (.assign "vv" (Expr.lit 0)) σ (σ.setVar "vv" 0) 2 :=
          Run.assign (evalB_lit (by omega))
        have hmr' : MatchesRest OFFLEN MEMLEN s (σ.setVar "vv" 0) :=
          hmr.congr (fun y _ _ hy3 => by simp [Env.setVar, hy3]) rfl
        have hvv' : (σ.setVar "vv" 0).vars "vv" = 0 := by simp [Env.setVar]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt4 s 0 hstgt hoffs hmems
          ⟨hB.2.1, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
          hOFFLEN hMEMLEN)
          (σ.setVar "vv" 0) ⟨hmr', hvv'⟩
        refine ⟨σ'', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_true hv3
          (hassign.seq hr2)))).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
      · have hv3 : (Cond.eq (V "cc") (Expr.lit 0)).evalB B σ = some false :=
          cond_eq_false B σ (V "cc") (Expr.lit 0) (σ.vars "cc") 0
            (evalB_var (hcc ▸ hB.2.2.2.2.2.2.1)) (evalB_lit (by omega)) (by rw [hcc]; exact hcc0)
        have hstep : step s b = { s with ph := 1, ii := 0, vv := 0 } := by
          simp [step, hph0, hb1, hcc0]
        obtain ⟨σ', hr, hq⟩ := (stepPh0CcPos_spec (B := B) s (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
          (by omega)) σ ⟨hmr, hcc, hii, hvv⟩
        refine ⟨σ', (Run.ite_true hv1 (Run.ite_false hv2 (Run.ite_false hv3 hr))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq
  · have hv1 : (Cond.eq (V "ph") (Expr.lit 0)).evalB B σ = some false :=
      cond_eq_false B σ (V "ph") (Expr.lit 0) (σ.vars "ph") 0
        (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph0)
    by_cases hph1 : s.ph = 1
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some true :=
        cond_eq_true B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1, hph1])
      obtain ⟨σ1, hr1, hM1⟩ := (stepPh1Prefix_spec s b (OFFLEN := OFFLEN) (MEMLEN := MEMLEN)
        ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1, hbeq ▸ hB.2.2.1, by omega⟩) σ ⟨⟨hmr, hcc, hii, hvv⟩, hbeq⟩
      obtain ⟨hmr1, hcc1, hii1, hvv1⟩ := hM1
      have hs1ii : (σ1).vars "ii" < B := by rw [hii1]; simp; omega
      have hs1cc : (σ1).vars "cc" < B := by rw [hcc1]; simp; omega
      by_cases hlt : s.ii + 1 < s.cc
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some true :=
          cond_lt_true B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = { s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 } := by
          simp [step, hph1, hlt]
        refine ⟨σ1, (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_true hv3 Run.skip)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact ⟨hmr1, hcc1, hii1, hvv1⟩
      · have hv3 : (Cond.lt (V "ii") (V "cc")).evalB B σ1 = some false :=
          cond_lt_false B σ1 (V "ii") (V "cc") (σ1.vars "ii") (σ1.vars "cc")
            (evalB_var hs1ii) (evalB_var hs1cc) (by rw [hii1, hcc1]; omega)
        have hstep : step s b = afterNumber s (s.vv + b * 2 ^ s.ii) := by
          simp [step, hph1, hlt]
        obtain ⟨σ'', hr2, hq2⟩ := (afterNumberCom_spec_tgt4
          ({ s with vv := s.vv + b * 2 ^ s.ii, ii := s.ii + 1 }) (s.vv + b * 2 ^ s.ii)
          (by simpa using hstgt) (by simpa using hoffs) (by simpa using hmems)
          ⟨by simpa using hB.2.1, by omega, by simp; omega, by simp; omega, by simp; omega,
            by simp; omega, by simp; omega, by omega⟩
          (by simpa using hOFFLEN) (by simpa using hMEMLEN)) σ1 ⟨hmr1, hvv1⟩
        refine ⟨σ'', (Run.ite_false hv1 (Run.ite_true hv2
          (hr1.seq (Run.ite_false hv3 hr2)))).mono
          (by simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [hstep]; exact hq2
    · have hv2 : (Cond.eq (V "ph") (Expr.lit 1)).evalB B σ = some false :=
        cond_eq_false B σ (V "ph") (Expr.lit 1) (σ.vars "ph") 1
          (evalB_var hphB) (evalB_lit (by omega)) (by rw [hmr.1]; exact hph1)
      have hstep : step s b = s := by simp [step, hph0, hph1]
      refine ⟨σ, (Run.ite_false hv1 (Run.ite_false hv2 Run.skip)).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [hstep]; exact ⟨hmr, hcc, hii, hvv⟩

-- One call of stepCom, for any s.tgt. Dispatches to the matching stepCom_spec_tgtN
-- using Struct s's tgt <= 4 to enumerate the five cases and its conditional
-- offs/mems clauses to discharge dispatchBody_spec_tgt3/tgt4's own extra hypotheses.
set_option maxHeartbeats 4000000 in
theorem stepCom_spec {B OFFLEN MEMLEN : ℕ} (s : St) (b : ℕ) (hStruct : Struct s)
    (hB : s.ph < B ∧ s.n < B ∧ s.m < B ∧ b < B ∧ s.cc + 1 < B ∧ s.vv + b * 2 ^ s.ii < B ∧
      s.ii + 1 < B ∧ s.cc < B ∧ s.j + 1 < B ∧ s.off + s.sz < B ∧ s.off + s.u < B ∧
      s.u + 1 < B ∧ s.tgt < B ∧ 5 < B)
    (hOFFLEN : s.j + 1 < OFFLEN) (hMEMLEN : s.off + s.u < MEMLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s σ ∧ σ.vars "b" = b) stepCom
      (fun _ σ' => Matches OFFLEN MEMLEN (step s b) σ') 2200 := by
  obtain ⟨hph, htgt, hu3, hu4, htgt2', hoffs, hmems⟩ := hStruct
  by_cases h0 : s.tgt = 0
  · exact stepCom_spec_tgt0 s b h0
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  by_cases h1 : s.tgt = 1
  · exact stepCom_spec_tgt1 s b h1
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  by_cases h2 : s.tgt = 2
  · exact stepCom_spec_tgt2 s b h2
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ (by omega)
  by_cases h3 : s.tgt = 3
  · exact stepCom_spec_tgt3 s b h3 (hoffs (Or.inl h3))
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩ (by omega)
  · have h4 : s.tgt ≠ 0 ∧ s.tgt ≠ 1 ∧ s.tgt ≠ 2 ∧ s.tgt ≠ 3 := ⟨h0, h1, h2, h3⟩
    have h4eq : s.tgt = 4 := by omega
    exact stepCom_spec_tgt4 s b h4 (hoffs (Or.inr h4eq)) (hmems (Or.inr h4eq))
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩ (by omega) (by omega)

-- One iteration of scanLoop: read the i-th entry, run stepCom, advance i. Matches the model's
-- run_take_succ exactly, so this is the per-step lemma scanLoop's own invariant proof composes.
set_option maxHeartbeats 4000000 in
theorem scanBody_spec {B OFFLEN MEMLEN : ℕ} (s0 : St) (l : List ℕ) (i : ℕ)
    (hi : i < l.length) (hstruct : Struct (run s0 (l.take i)))
    (hlB : ∀ x ∈ l, x < B)
    (hB : (run s0 (l.take i)).ph < B ∧ (run s0 (l.take i)).n < B ∧ (run s0 (l.take i)).m < B ∧
      (run s0 (l.take i)).cc + 1 < B ∧
      (run s0 (l.take i)).vv + (l.getD i 0) * 2 ^ (run s0 (l.take i)).ii < B ∧
      (run s0 (l.take i)).ii + 1 < B ∧ (run s0 (l.take i)).cc < B ∧
      (run s0 (l.take i)).j + 1 < B ∧ (run s0 (l.take i)).off + (run s0 (l.take i)).sz < B ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).u < B ∧ (run s0 (l.take i)).u + 1 < B ∧
      (run s0 (l.take i)).tgt < B ∧ 5 < B ∧ i + 1 < B)
    (hOFFLEN : (run s0 (l.take i)).j + 1 < OFFLEN)
    (hMEMLEN : (run s0 (l.take i)).off + (run s0 (l.take i)).u < MEMLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN (run s0 (l.take i)) σ ∧ σ.vars "L" = l.length ∧
        σ.arrs "a" = l ∧ σ.vars "i" = i)
      scanBody
      (fun _ σ' => Matches OFFLEN MEMLEN (run s0 (l.take (i + 1))) σ' ∧ σ'.vars "L" = l.length ∧
        σ'.arrs "a" = l ∧ σ'.vars "i" = i + 1) 2216 := by
  have hbB : l.getD i 0 < B := by
    apply hlB
    rw [List.getD_eq_getElem l 0 hi]
    exact List.getElem_mem hi
  intro σ hσ
  obtain ⟨hM, hL, ha, hiv⟩ := hσ
  obtain ⟨hmr, hcc, hii, hvv⟩ := hM
  have hassign : Run B (.assign "b" (.get "a" (V "i"))) σ (σ.setVar "b" (l.getD i 0)) 3 :=
    Run.assign (evalB_get (evalB_var (by omega)) (by rw [ha, hiv]; simp [List.getElem?_eq_getElem hi])
      (by omega))
  have hmr' : MatchesRest OFFLEN MEMLEN (run s0 (l.take i)) (σ.setVar "b" (l.getD i 0)) :=
    hmr.congr2 (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
      (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
      (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
  have hM' : Matches OFFLEN MEMLEN (run s0 (l.take i)) (σ.setVar "b" (l.getD i 0)) :=
    ⟨hmr', by simp [Env.setVar, hcc], by simp [Env.setVar, hii], by simp [Env.setVar, hvv]⟩
  have hbeq : (σ.setVar "b" (l.getD i 0)).vars "b" = l.getD i 0 := by simp [Env.setVar]
  have hstepB : (run s0 (l.take i)).ph < B ∧ (run s0 (l.take i)).n < B ∧
      (run s0 (l.take i)).m < B ∧ l.getD i 0 < B ∧ (run s0 (l.take i)).cc + 1 < B ∧
      (run s0 (l.take i)).vv + (l.getD i 0) * 2 ^ (run s0 (l.take i)).ii < B ∧
      (run s0 (l.take i)).ii + 1 < B ∧ (run s0 (l.take i)).cc < B ∧
      (run s0 (l.take i)).j + 1 < B ∧ (run s0 (l.take i)).off + (run s0 (l.take i)).sz < B ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).u < B ∧ (run s0 (l.take i)).u + 1 < B ∧
      (run s0 (l.take i)).tgt < B ∧ 5 < B := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨σ', hr2, hq2⟩ := ((stepCom_spec (run s0 (l.take i)) (l.getD i 0) hstruct hstepB
    hOFFLEN hMEMLEN).frame) (σ.setVar "b" (l.getD i 0)) ⟨hM', hbeq⟩
  obtain ⟨hqM, hqv, hqa, _, _⟩ := hq2
  have hLeq : σ'.vars "L" = l.length := by
    rw [hqv "L" (by decide)]; simp [Env.setVar, hL]
  have haeq : σ'.arrs "a" = l := by
    rw [hqa "a" (by decide)]; simp [Env.setVar, ha]
  have hieq : σ'.vars "i" = i := by
    rw [hqv "i" (by decide)]; simp [Env.setVar, hiv]
  have hiB2 : i + 1 < B := by omega
  obtain ⟨σ2, hbump, hbumpeq, hbumpv, hbumpa, _, _⟩ := ((bump_spec "i" i hiB2).frame) σ' hieq
  obtain ⟨hqmr, hqcc, hqii, hqvv⟩ := hqM
  have hqmr2 : MatchesRest OFFLEN MEMLEN (step (run s0 (l.take i)) (l.getD i 0)) σ2 :=
    hqmr.congr2 (hbumpv "ph" (by decide)) (hbumpv "tgt" (by decide)) (hbumpv "n" (by decide))
      (hbumpv "m" (by decide)) (hbumpv "k" (by decide)) (hbumpv "j" (by decide))
      (hbumpv "u" (by decide)) (hbumpv "sz" (by decide)) (hbumpv "off" (by decide))
      (hbumpa "OFFS" (by decide)) (hbumpa "MEMS" (by decide))
  refine ⟨σ2, (hassign.seq (hr2.seq hbump)).mono (by omega), ?_⟩
  rw [show run s0 (l.take (i + 1)) = step (run s0 (l.take i)) (l.getD i 0) from
    ScanModel.run_take_succ s0 l i hi]
  have hqcc2 : σ2.vars "cc" = (step (run s0 (l.take i)) (l.getD i 0)).cc := by
    rw [hbumpv "cc" (by decide)]; exact hqcc
  have hqii2 : σ2.vars "ii" = (step (run s0 (l.take i)) (l.getD i 0)).ii := by
    rw [hbumpv "ii" (by decide)]; exact hqii
  have hqvv2 : σ2.vars "vv" = (step (run s0 (l.take i)) (l.getD i 0)).vv := by
    rw [hbumpv "vv" (by decide)]; exact hqvv
  have hLeq2 : σ2.vars "L" = l.length := by
    rw [hbumpv "L" (by decide)]; exact hLeq
  have haeq2 : σ2.arrs "a" = l := by
    rw [hbumpa "a" (by decide)]; exact haeq
  exact ⟨⟨hqmr2, hqcc2, hqii2, hqvv2⟩, hLeq2, haeq2, hbumpeq⟩

-- scanLoop's own loop invariant: at "i" = i, the machine matches the model scanned up to
-- l.take i, with "L"/"a" holding the tape's own length/contents throughout.
def ScanInv (OFFLEN MEMLEN : ℕ) (s0 : St) (l : List ℕ) (σ : Env) : Prop :=
  σ.vars "i" ≤ l.length ∧ σ.arrs "a" = l ∧ σ.vars "L" = l.length ∧
  Matches OFFLEN MEMLEN (run s0 (l.take (σ.vars "i"))) σ

-- **The whole scan.** Given the tape "a" = l fits in B (hlB), an initial Struct s0, and
-- (the one piece left abstract, for a later session to discharge with a concrete B/OFFLEN/
-- MEMLEN as functions of l.length) a bound, at every prefix of l, on every field stepCom_spec
-- needs to fit under B/OFFLEN/MEMLEN, scanLoop computes exactly run s0 l.
set_option maxHeartbeats 4000000 in
theorem scanLoop_spec {B OFFLEN MEMLEN : ℕ} (s0 : St) (l : List ℕ)
    (hStruct0 : Struct s0) (hlB : ∀ x ∈ l, x < B) (hNB : l.length < B)
    (hAllBounds : ∀ i < l.length,
      (run s0 (l.take i)).ph < B ∧ (run s0 (l.take i)).n < B ∧ (run s0 (l.take i)).m < B ∧
      (run s0 (l.take i)).cc + 1 < B ∧
      (run s0 (l.take i)).vv + (l.getD i 0) * 2 ^ (run s0 (l.take i)).ii < B ∧
      (run s0 (l.take i)).ii + 1 < B ∧ (run s0 (l.take i)).cc < B ∧
      (run s0 (l.take i)).j + 1 < B ∧ (run s0 (l.take i)).off + (run s0 (l.take i)).sz < B ∧
      (run s0 (l.take i)).off + (run s0 (l.take i)).u < B ∧ (run s0 (l.take i)).u + 1 < B ∧
      (run s0 (l.take i)).tgt < B ∧ 5 < B ∧ i + 1 < B ∧
      (run s0 (l.take i)).j + 1 < OFFLEN ∧ (run s0 (l.take i)).off + (run s0 (l.take i)).u < MEMLEN) :
    Spec B (fun σ => Matches OFFLEN MEMLEN s0 σ ∧ σ.arrs "a" = l ∧ σ.vars "L" = l.length)
      scanLoop
      (fun _ σ' => Matches OFFLEN MEMLEN (run s0 l) σ' ∧ σ'.vars "i" = l.length)
      (2220 * l.length + 6) := by
  have hbody : Spec B (fun σ => ScanInv OFFLEN MEMLEN s0 l σ ∧ σ.vars "i" < l.length) scanBody
      (fun σ σ' => ScanInv OFFLEN MEMLEN s0 l σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 2216 := by
    intro σ ⟨⟨hile, ha, hL, hM⟩, hilt⟩
    have hb14 : (run s0 (l.take (σ.vars "i"))).ph < B ∧ (run s0 (l.take (σ.vars "i"))).n < B ∧
        (run s0 (l.take (σ.vars "i"))).m < B ∧
        (run s0 (l.take (σ.vars "i"))).cc + 1 < B ∧
        (run s0 (l.take (σ.vars "i"))).vv + (l.getD (σ.vars "i") 0) *
          2 ^ (run s0 (l.take (σ.vars "i"))).ii < B ∧
        (run s0 (l.take (σ.vars "i"))).ii + 1 < B ∧ (run s0 (l.take (σ.vars "i"))).cc < B ∧
        (run s0 (l.take (σ.vars "i"))).j + 1 < B ∧
        (run s0 (l.take (σ.vars "i"))).off + (run s0 (l.take (σ.vars "i"))).sz < B ∧
        (run s0 (l.take (σ.vars "i"))).off + (run s0 (l.take (σ.vars "i"))).u < B ∧
        (run s0 (l.take (σ.vars "i"))).u + 1 < B ∧ (run s0 (l.take (σ.vars "i"))).tgt < B ∧
        5 < B ∧ σ.vars "i" + 1 < B := by
      have := hAllBounds (σ.vars "i") hilt
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto
    have hOM := hAllBounds (σ.vars "i") hilt
    obtain ⟨σ', hr, hM', hL', ha', hi'⟩ :=
      scanBody_spec s0 l (σ.vars "i") hilt (hStruct0.run_step _) hlB hb14
        (by tauto) (by tauto) σ ⟨hM, hL, ha, rfl⟩
    exact ⟨σ', hr, ⟨by omega, ha', hL', by rw [hi']; exact hM'⟩, hi'⟩
  intro σ ⟨hM, ha, hL⟩
  have hM0 : Matches OFFLEN MEMLEN s0 (σ.setVar "i" 0) :=
    hM.setVar_unrelated "i" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0
  have hM0' : Matches OFFLEN MEMLEN (run s0 (l.take 0)) (σ.setVar "i" 0) := by
    simpa using hM0
  obtain ⟨σ', hr, hInv, hiN⟩ :=
    (Spec.forRangeZero "i" "L" (ScanInv OFFLEN MEMLEN s0 l) l.length 2216 hNB
      (fun _ h => h.1) (fun _ h => h.2.2.1) hbody) σ
      ⟨by simp [Env.setVar], by simp [Env.setVar, ha], by simp [Env.setVar, hL], hM0'⟩
  obtain ⟨_, _, _, hM'⟩ := hInv
  refine ⟨σ', hr.mono (by omega), ?_, hiN⟩
  rw [hiN] at hM'
  simpa using hM'

/-- `scanLoop_spec` with `hAllBounds` closed: for any starting state and any tape whose
entries are all `≤ M`, `scanLoop` computes exactly `ScanModel.run s0 l`, at the concrete
generous word bound `ScanModel.wordBound M l.length` — no numeric side condition left open.
This is the last piece of Theorem 1's machine layer for the scan sub-program. -/
theorem scanLoop_spec_closed {M : ℕ} (s0 : St) (l : List ℕ)
    (hStruct0 : Struct s0) (hB0 : ScanModel.Bounded M l.length 0 s0)
    (hlM : ∀ x ∈ l, x ≤ M) :
    Spec (ScanModel.wordBound M l.length)
      (fun σ => Matches (l.length + 2) (ScanModel.wordBound M l.length) s0 σ ∧
        σ.arrs "a" = l ∧ σ.vars "L" = l.length)
      scanLoop
      (fun _ σ' => Matches (l.length + 2) (ScanModel.wordBound M l.length) (run s0 l) σ' ∧
        σ'.vars "i" = l.length)
      (2220 * l.length + 6) := by
  set L := l.length with hLdef
  have hlB : ∀ x ∈ l, x < ScanModel.wordBound M L := ScanModel.wordBound_lt hlM hLdef.symm
  have hLB : L < ScanModel.wordBound M L := ScanModel.wordBound_len_lt M L
  have hAllBounds := hB0.hAllBounds_of hStruct0 l hlM hLdef.symm
  exact scanLoop_spec (B := ScanModel.wordBound M L) (OFFLEN := L + 2)
    (MEMLEN := ScanModel.wordBound M L) s0 l hStruct0 hlB hLB hAllBounds

open Lax391470Proofs.ReadAll (readAll readAll_spec)

/-- `initVars`, proven: it resets every scalar to `ScanModel.init`'s value, leaving the
`OFF`/`MEM`/`a` arrays and the `L` scalar untouched (threaded through so a caller composing
this with `readAll` doesn't have to re-derive their preservation separately). -/
theorem initVars_spec {B OFFLEN MEMLEN : ℕ} (hB0 : 0 < B) (a0 : List ℕ) (L0 : ℕ) :
    Spec B (fun σ => (σ.arrs "OFFS").length = OFFLEN ∧ (σ.arrs "MEMS").length = MEMLEN ∧
        σ.arrs "a" = a0 ∧ σ.vars "L" = L0)
      initVars
      (fun σ σ' => Matches OFFLEN MEMLEN ScanModel.init σ' ∧
        σ'.arrs "OFFS" = σ.arrs "OFFS" ∧ σ'.arrs "MEMS" = σ.arrs "MEMS" ∧
        σ'.arrs "a" = a0 ∧ σ'.vars "L" = L0)
      30 := by
  run_vcg
  rename_i hOL hML ha hL
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [ScanModel.init, Env.setVar, hOL, hML, ha, hL]

/-- **The whole parse, proven**: given the tape's length-prefixed encoding on `inp` and
`OFF`/`MEM`/`a` arrays of the right size, `parseCom` produces a state matching
`ScanModel.run ScanModel.init x` exactly — this is Part C's parse half, closing the gap
between `Lax391470Proofs.ReadAll.readAll` (reading the raw tape) and `scanLoop_spec_closed`
(the proven scan), with no numeric side condition left open. -/
theorem parseCom_spec {M : ℕ} (x : List ℕ) (hlM : ∀ v ∈ x, v ≤ M) :
    Spec (ScanModel.wordBound M x.length)
      (fun σ => σ.inp = x.length :: x ∧ σ.out = [] ∧ (σ.arrs "a").length = x.length ∧
        (σ.arrs "OFFS").length = x.length + 2 ∧
        (σ.arrs "MEMS").length = ScanModel.wordBound M x.length)
      parseCom
      (fun _ σ' => Matches (x.length + 2) (ScanModel.wordBound M x.length)
        (run ScanModel.init x) σ' ∧ σ'.vars "i" = x.length)
      (12 * x.length + 10 + 30 + (2220 * x.length + 6)) := by
  intro σ hσ
  obtain ⟨hinp, hout, halen, hOFFlen, hMEMlen⟩ := hσ
  set B := ScanModel.wordBound M x.length with hBdef
  have hlB : ∀ v ∈ x, v < B := ScanModel.wordBound_lt hlM rfl
  have hLB1 : x.length + 1 < B := by rw [hBdef]; simp only [ScanModel.wordBound]; omega
  have hB0 : 0 < B := by rw [hBdef]; simp only [ScanModel.wordBound]; omega
  have hscan := scanLoop_spec_closed (M := M) ScanModel.init x Struct.init
    (ScanModel.Bounded.init M x.length) hlM
  obtain ⟨σ1, hr1, hq1⟩ := (readAll_spec (y := x) (B := B) hlB hLB1) σ ⟨hinp, hout, halen⟩
  have hOFFpres : σ1.arrs "OFFS" = σ.arrs "OFFS" := hr1.frame_arr "OFFS" (by decide)
  have hMEMpres : σ1.arrs "MEMS" = σ.arrs "MEMS" := hr1.frame_arr "MEMS" (by decide)
  obtain ⟨hLv1, ha1, hout1, hinp1⟩ := hq1
  obtain ⟨σ2, hr2, hq2⟩ := (initVars_spec (B := B) (OFFLEN := x.length + 2) (MEMLEN := B) hB0 x
    x.length) σ1 ⟨by rw [hOFFpres]; exact hOFFlen, by rw [hMEMpres]; exact hMEMlen, ha1, hLv1⟩
  obtain ⟨hM2, hOFF2, hMEM2, ha2, hL2⟩ := hq2
  obtain ⟨σ3, hr3, hq3⟩ := hscan σ2 ⟨hM2, ha2, hL2⟩
  exact ⟨σ3, (hr1.seq (hr2.seq hr3)).mono (by omega), hq3⟩

end Lax496464Proofs.Ram.ScanProg
