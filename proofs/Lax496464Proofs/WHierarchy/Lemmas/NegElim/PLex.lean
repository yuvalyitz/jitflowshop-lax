import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre

/-! # Writing sequences of variables and lexicographic comparisons

`wseq` writes a sequence of variables (read from the word or counted from a fresh variable),
`lexCom` the code of `ȳ <ₗ z̄` for two such sequences. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre

variable {x : List ℕ}

theorem seqE_lt {k g l : ℕ} (hb : g + l < Bv x) :
    seqE x k g l < Bv x := by
  unfold seqE
  split_ifs
  · exact getD_lt_Bv x _
  · exact hb

theorem seqL_getD {k g n l : ℕ} (hl : l < n) : (seqL x k g n).getD l 0 = seqE x k g l := by
  simp [seqL, List.getD_eq_getElem?_getD, hl]

@[simp] theorem getElem_seqL {k g n l : ℕ} (hl : l < (seqL x k g n).length) :
    (seqL x k g n)[l] = seqE x k g l := by
  simp [seqL]

/-! ### Sequences -/

/-- The invariant of `wseq`. -/
def WQ (x : List ℕ) (k g n : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "wk" = k ∧ σ.vars "wg" = g ∧ σ.vars "wn" = n ∧ σ.vars "wl" ≤ n ∧
    σ.out = out0 ++ seqL x k g (σ.vars "wl")

theorem wseq_value {k g n : ℕ} (hk1 : k ≤ 1) (hk : k = 0 → g + n ≤ x.length) (hb : g + n + 1 < Bv x)
    (out0 : List ℕ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "wk" = k ∧ σ.vars "wg" = g ∧ σ.vars "wn" = n ∧
        σ.out = out0) wseq
      (fun _ σ' => σ'.out = out0 ++ seqL x k g n) ((24 + 4) * n + 6) := by
  have hbody : Spec (Bv x) (fun σ => WQ x k g n out0 σ ∧ σ.vars "wl" < n)
      (.seq (.ite (.eq (V "wk") (L 0)) (.write (A (.add (V "wg") (V "wl"))))
        (.write (.add (V "wg") (V "wl")))) (bump "wl"))
      (fun σ σ' => WQ x k g n out0 σ' ∧ σ'.vars "wl" = σ.vars "wl" + 1) 24 := by
    refine Spec.pre (P := fun σ => (WQ x k g n out0 σ ∧ σ.vars "wl" < n) ∧
      (k = 0 → σ.vars "wg" + σ.vars "wl" < (σ.arrs "a").length) ∧
      seqE x k g (σ.vars "wl") < Bv x ∧ σ.vars "wg" + σ.vars "wl" < Bv x ∧
      σ.vars "wl" + 1 < Bv x ∧ σ.vars "wk" < Bv x) ?_ ?_
    · run_vcg
      all_goals
        simp only [WQ, Env.setVar] at *
        simp_all [seqL_succ, seqE]
      all_goals (try omega)
    · rintro σ ⟨⟨ha, h1, h2, h3, h4, h5⟩, hlt⟩
      refine ⟨⟨⟨ha, h1, h2, h3, h4, h5⟩, hlt⟩, fun hk0 => by rw [ha, h2]; have := hk hk0; omega,
        seqE_lt (by omega), by omega, by omega, ?_⟩
      rw [h1]; have := len_lt_Bv x; omega
  refine Spec.post (Spec.pre (Spec.forRangeZero "wl" "wn" (WQ x k g n out0) n 24 (by omega)
    (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.2.1) hbody) ?_) ?_
  · rintro σ ⟨ha, h1, h2, h3, h4⟩
    simp [WQ, Env.setVar, ha, h1, h2, h3, h4, seqL]
  · rintro σ σ' - ⟨⟨-, -, -, -, -, ho⟩, hl⟩
    rw [ho, hl]

theorem wseq_spec {n : ℕ} :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "wn" = n ∧ σ.vars "wk" ≤ 1 ∧
        (σ.vars "wk" = 0 → σ.vars "wg" + n ≤ x.length) ∧ σ.vars "wg" + n + 1 < Bv x) wseq
      (fun σ σ' => σ'.out = σ.out ++ seqL x (σ.vars "wk") (σ.vars "wg") n ∧ Keep ["wl"] σ σ')
      ((24 + 4) * n + 6) := by
  intro σ ⟨ha, hn, hk1, hk, hb⟩
  have h := Spec.keep (wseq_value (x := x) (k := σ.vars "wk") (g := σ.vars "wg") (n := n) hk1 hk hb
    σ.out) ["wl"]
    (by intro y hy; simpa [wseq, loop, bump, Com.wvars] using hy)
    (by simp [wseq, loop, bump, Com.warrs]) (by simp [wseq, loop, bump, Com.reads])
  exact h σ ⟨ha, rfl, rfl, hn, rfl⟩

/-! ### Lexicographic comparisons -/

theorem elems_spec :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "k1" ≤ 1 ∧ σ.vars "k2" ≤ 1 ∧
        (σ.vars "k1" = 0 → σ.vars "g1" + σ.vars "ll" < x.length) ∧
        (σ.vars "k2" = 0 → σ.vars "g2" + σ.vars "ll" < x.length) ∧
        σ.vars "g1" + σ.vars "ll" < Bv x ∧ σ.vars "g2" + σ.vars "ll" < Bv x) elems
      (fun σ σ' => (σ'.vars "e1" = seqE x (σ.vars "k1") (σ.vars "g1") (σ.vars "ll") ∧
        σ'.vars "e2" = seqE x (σ.vars "k2") (σ.vars "g2") (σ.vars "ll")) ∧
        Keep ["e1", "e2"] σ σ' ∧ σ'.out = σ.out) 20 := by
  have hl := len_lt_Bv x
  have h : Spec (Bv x) (fun σ => (σ.arrs "a" = x ∧ σ.vars "k1" ≤ 1 ∧ σ.vars "k2" ≤ 1 ∧
        (σ.vars "k1" = 0 → σ.vars "g1" + σ.vars "ll" < x.length) ∧
        (σ.vars "k2" = 0 → σ.vars "g2" + σ.vars "ll" < x.length) ∧
        σ.vars "g1" + σ.vars "ll" < Bv x ∧ σ.vars "g2" + σ.vars "ll" < Bv x) ∧
        (σ.arrs "a").getD (σ.vars "g1" + σ.vars "ll") 0 < Bv x ∧
        (σ.arrs "a").getD (σ.vars "g2" + σ.vars "ll") 0 < Bv x) elems
      (fun σ σ' => σ'.vars "e1" = seqE x (σ.vars "k1") (σ.vars "g1") (σ.vars "ll") ∧
        σ'.vars "e2" = seqE x (σ.vars "k2") (σ.vars "g2") (σ.vars "ll")) 20 := by
    unfold elems
    run_vcg
    all_goals
      (try simp only [Env.setVar] at *)
      simp_all [seqE]
    all_goals (try omega)
  have h' := Spec.keepOut h ["e1", "e2"]
    (by intro y hy; simp [elems, Com.wvars] at hy; simp; tauto)
    (by simp [elems, Com.warrs]) (by simp [elems, Com.reads]) (by simp [elems, Com.NoWrite])
  intro σ hσ
  have ha := hσ.1
  exact h' σ ⟨hσ, by rw [ha]; exact getD_lt_Bv x _, by rw [ha]; exact getD_lt_Bv x _⟩

/-- The invariant of `lexCom`'s loop. -/
def LXI (x : List ℕ) (k1 g1 k2 g2 m : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "k1" = k1 ∧ σ.vars "g1" = g1 ∧ σ.vars "k2" = k2 ∧ σ.vars "g2" = g2 ∧
    σ.vars "ln" = m ∧ σ.vars "lm" = m - 1 ∧ σ.vars "ll" ≤ m - 1 ∧
    σ.out = out0 ++ lexBodyL (seqL x k1 g1 m) (seqL x k2 g2 m) (σ.vars "ll")

/-- The bounds `lexCom` needs. -/
structure LexOK (x : List ℕ) (k1 g1 k2 g2 m : ℕ) : Prop where
  pos : 1 ≤ m
  kk1 : k1 ≤ 1
  kk2 : k2 ≤ 1
  r1 : k1 = 0 → g1 + m ≤ x.length
  r2 : k2 = 0 → g2 + m ≤ x.length
  b1 : g1 + m + 1 < Bv x
  b2 : g2 + m + 1 < Bv x

set_option maxHeartbeats 4000000 in
theorem lexCom_value {k1 g1 k2 g2 m : ℕ} (hok : LexOK x k1 g1 k2 g2 m) (out0 : List ℕ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "k1" = k1 ∧ σ.vars "g1" = g1 ∧
        σ.vars "k2" = k2 ∧ σ.vars "g2" = g2 ∧ σ.vars "ln" = m ∧ σ.out = out0) lexCom
      (fun _ σ' => σ'.out = out0 ++ (lexF (seqL x k1 g1 m) (seqL x k2 g2 m)).encode)
      ((80 + 4) * (m - 1) + 100) := by
  have hl := len_lt_Bv x
  have hm := hok.pos
  have hk1 := hok.kk1
  have hk2 := hok.kk2
  have hr1 := hok.r1
  have hr2 := hok.r2
  have hb1 := hok.b1
  have hb2 := hok.b2
  have hbody : Spec (Bv x) (fun σ => LXI x k1 g1 k2 g2 m out0 σ ∧ σ.vars "ll" < m - 1) lexBody
      (fun σ σ' => LXI x k1 g1 k2 g2 m out0 σ' ∧ σ'.vars "ll" = σ.vars "ll" + 1) 80 := by
    refine Spec.pre (P := fun σ => (LXI x k1 g1 k2 g2 m out0 σ ∧ σ.vars "ll" < m - 1) ∧
      seqE x k1 g1 (σ.vars "ll") < Bv x ∧ seqE x k2 g2 (σ.vars "ll") < Bv x ∧
      σ.vars "ll" + 1 < Bv x) ?_ ?_
    · unfold lexBody writes
      run_vcg [elems_spec (x := x)]
      all_goals
        simp only [LXI, Env.setVar] at *
      all_goals first
        | (find_hyp hK : _ ∧ Keep ["e1", "e2"] _ _ ∧ _
           obtain ⟨⟨he1, he2⟩, ⟨hkv, hka, -⟩, hout⟩ := hK
           have q1 := hkv "k1" (by decide)
           have q2 := hkv "g1" (by decide)
           have q3 := hkv "k2" (by decide)
           have q4 := hkv "g2" (by decide)
           have q5 := hkv "ln" (by decide)
           have q6 := hkv "lm" (by decide)
           have q7 := hkv "ll" (by decide)
           have q8 := congrFun hka "a"
           clear hkv hka
           have hlm : σ.vars "ll" < m := by omega
           simp_all [lexBodyL_succ, seqL_getD]
           all_goals (try omega))
        | (simp_all; try omega)
      all_goals (try omega)
    · rintro σ ⟨⟨ha, h1, h2, h3, h4, h5, h6, h7, h8⟩, hlt⟩
      exact ⟨⟨⟨ha, h1, h2, h3, h4, h5, h6, h7, h8⟩, hlt⟩,
        seqE_lt (by omega),
        seqE_lt (by omega), by omega⟩
  have hloop := Spec.forRangeZero (B := Bv x) (c := lexBody) "ll" "lm" (LXI x k1 g1 k2 g2 m out0)
    (m - 1) 80 (by omega) (fun σ h => h.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.2.2.1) hbody
  have hne : seqL x k1 g1 m ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have henc := encode_lexF (seqL x k1 g1 m) (seqL x k2 g2 m) (by simp) hne
  simp only [length_seqL] at henc
  rw [seqL_getD (by omega), seqL_getD (by omega)] at henc
  have hs1 : seqE x k1 g1 (m - 1) < Bv x := seqE_lt (by omega)
  have hs2 : seqE x k2 g2 (m - 1) < Bv x := seqE_lt (by omega)
  unfold lexCom loop writes
  run_vcg [hloop, elems_spec (x := x)]
  all_goals
    (try simp only [LXI, Env.setVar] at *)
  all_goals first
    | (find_hyp hK : _ ∧ Keep ["e1", "e2"] _ _ ∧ _
       obtain ⟨⟨he1, he2⟩, ⟨hkv, hka, -⟩, hout⟩ := hK
       simp_all
       all_goals (try omega))
    | (simp_all; try omega)
  all_goals (try omega)

theorem lexCom_spec {m : ℕ} :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "ln" = m ∧
        LexOK x (σ.vars "k1") (σ.vars "g1") (σ.vars "k2") (σ.vars "g2") m) lexCom
      (fun σ σ' => σ'.out = σ.out ++ (lexF (seqL x (σ.vars "k1") (σ.vars "g1") m)
        (seqL x (σ.vars "k2") (σ.vars "g2") m)).encode ∧ Keep ["lm", "ll", "e1", "e2"] σ σ')
      ((80 + 4) * (m - 1) + 100) := by
  intro σ ⟨ha, hm, hok⟩
  have h := Spec.keep (lexCom_value hok σ.out) ["lm", "ll", "e1", "e2"]
    (by intro y hy; simp [lexCom, lexBody, elems, loop, writes, bump, Com.wvars] at hy; simp; tauto)
    (by simp [lexCom, lexBody, elems, loop, writes, bump, Com.warrs])
    (by simp [lexCom, lexBody, elems, loop, writes, bump, Com.reads])
  exact h σ ⟨ha, rfl, rfl, rfl, rfl, hm, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex
