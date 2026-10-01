import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgSim

/-! # Phase 7d: storing the number of a found tuple

`lRow_value`: a successful search stores the number of its tuple `key c ++ pad ch`, padded to length
`k + 1` (`padLoop_spec`); every stored number is below the bound (`hs_lt`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgSim

variable {cl : List (List ℕ)} {d k B : ℕ}

theorem length_pad' (ch : List ℕ) : (pad cl k ch).length = k + 1 := by simp [pad]

theorem pad_getD {ch : List ℕ} {q : ℕ} (hq : q < k + 1) :
    (pad cl k ch).getD q 0 = if q < ch.length then ch.getD q 0 else nL cl := by
  unfold pad; rw [List.getD_eq_getElem _ _ (by simpa using hq)]; simp

theorem pad_le {ch : List ℕ} (h : ∀ e ∈ ch, e ≤ nL cl) {x : ℕ} (hx : x ∈ pad cl k ch) :
    x ≤ nL cl := by
  rcases mem_pad cl k hx with hx | rfl
  · exact h x hx
  · exact le_rfl

/-- The invariant of the loop over the entries of the padded set. -/
def PDI (cl : List (List ℕ)) (d k : ℕ) (A ch : List ℕ) (K0 : ℕ) (σ : Env) : Prop :=
  σ.arrs "ch" = A ∧ A.take ch.length = ch ∧ ch.length ≤ A.length ∧ σ.vars "w_nch" = ch.length ∧
    σ.vars "w_L" = nL cl ∧ σ.vars "w_M" = MM cl ∧ σ.vars "w_K1" = k + 1 ∧ σ.vars "w_q" ≤ k + 1 ∧
    σ.vars "w_acc" = K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take (σ.vars "w_q")) ∧
    σ.vars "w_pw2" = MM cl ^ (d + 2) * MM cl ^ σ.vars "w_q"

theorem pad_bounds (hB : BB cl d k B) (ch : List ℕ) (hch : ∀ e ∈ ch, e ≤ nL cl) {K0 q : ℕ}
    (hK0 : K0 < MM cl ^ (d + 2)) (hq : q < k + 1) :
    K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take (q + 1)) < B ∧
      (pad cl k ch).getD q 0 * (MM cl ^ (d + 2) * MM cl ^ q) < B ∧
      MM cl ^ (d + 2) * MM cl ^ q * MM cl < B ∧ MM cl ^ (d + 2) * MM cl ^ q < B ∧
      K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take q) < B := by
  have hM := MM_ge cl
  have hbig := hB.big
  have hlt : ∀ x ∈ pad cl k ch, x < MM cl := fun x hx => by
    have := pad_le (k := k) hch hx; have := nL_lt_MM cl; omega
  have h1 := num_take_lt (show 0 < MM cl by omega) hlt (q + 1)
  have h1' := num_take_lt (show 0 < MM cl by omega) hlt q
  have hl1 : ((pad cl k ch).take (q + 1)).length = q + 1 := by
    rw [List.length_take, length_pad']; omega
  have hl2 : ((pad cl k ch).take q).length = q := by
    rw [List.length_take, length_pad']; omega
  rw [hl1] at h1
  rw [hl2] at h1'
  set P := MM cl ^ (d + 2) with hP
  have hq1 : P * MM cl ^ (q + 1) = MM cl ^ (d + q + 3) := by rw [hP, ← pow_add]; ring_nf
  have hq0 : P * MM cl ^ q = MM cl ^ (d + q + 2) := by rw [hP, ← pow_add]; ring_nf
  have hp1 : MM cl ^ (d + q + 3) ≤ MM cl ^ (d + k + 4) := pow_le_big cl (by omega)
  have hp0 : MM cl ^ (d + q + 2) ≤ MM cl ^ (d + q + 3) := pow_le_big cl (by omega)
  have hp2 : P ≤ MM cl ^ (d + q + 2) := pow_le_big cl (by omega)
  have e1 : P * num (MM cl) ((pad cl k ch).take (q + 1)) < P * MM cl ^ (q + 1) :=
    Nat.mul_lt_mul_of_pos_left h1 (by positivity)
  have e1' : P * num (MM cl) ((pad cl k ch).take q) < P * MM cl ^ q :=
    Nat.mul_lt_mul_of_pos_left h1' (by positivity)
  have hgq : (pad cl k ch).getD q 0 < MM cl := by
    rw [List.getD_eq_getElem _ _ (by rw [length_pad']; exact hq)]
    exact hlt _ (List.getElem_mem _)
  have e2 : (pad cl k ch).getD q 0 * (P * MM cl ^ q) ≤ MM cl * (P * MM cl ^ q) :=
    Nat.mul_le_mul_right _ hgq.le
  have e3 : MM cl * (P * MM cl ^ q) = P * MM cl ^ (q + 1) := by ring
  have e4 : P * MM cl ^ q * MM cl = P * MM cl ^ (q + 1) := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 4000000 in
theorem padBody_spec (hB : BB cl d k B) {A ch : List ℕ} {K0 : ℕ} (hch : ∀ e ∈ ch, e ≤ nL cl)
    (hK0 : K0 < MM cl ^ (d + 2)) (hchk : ch.length ≤ k) :
    Spec B (fun σ => PDI cl d k A ch K0 σ ∧ σ.vars "w_q" < k + 1) padBody
      (fun σ σ' => PDI cl d k A ch K0 σ' ∧ σ'.vars "w_q" = σ.vars "w_q" + 1) 50 := by
  have hl := hB.hl
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => PDI cl d k A ch K0 σ ∧ σ.vars "w_q" < k + 1 ∧
      (σ.vars "w_q" < σ.vars "w_nch" → σ.vars "w_q" < (σ.arrs "ch").length ∧
        (σ.arrs "ch").getD (σ.vars "w_q") 0 < B ∧
        σ.vars "w_acc" + (σ.arrs "ch").getD (σ.vars "w_q") 0 * σ.vars "w_pw2" =
          K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take (σ.vars "w_q" + 1)) ∧
        (σ.arrs "ch").getD (σ.vars "w_q") 0 * σ.vars "w_pw2" < B) ∧
      (¬ σ.vars "w_q" < σ.vars "w_nch" →
        σ.vars "w_acc" + σ.vars "w_L" * σ.vars "w_pw2" =
          K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take (σ.vars "w_q" + 1)) ∧
        σ.vars "w_L" * σ.vars "w_pw2" < B) ∧
      K0 + MM cl ^ (d + 2) * num (MM cl) ((pad cl k ch).take (σ.vars "w_q" + 1)) < B ∧
      σ.vars "w_pw2" * σ.vars "w_M" = MM cl ^ (d + 2) * MM cl ^ (σ.vars "w_q" + 1) ∧
      σ.vars "w_pw2" * σ.vars "w_M" < B ∧ σ.vars "w_pw2" < B ∧ σ.vars "w_acc" < B ∧
      σ.vars "w_M" < B ∧ σ.vars "w_L" < B ∧ σ.vars "w_nch" < B ∧ σ.vars "w_q" + 1 < B) ?_ ?_
  · unfold padBody
    run_vcg
    all_goals (try simp only [PDI] at *)
    all_goals (try simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨ha, htake, hle, hn, hL, hM, hK1, hq, hacc, hpw⟩, hlt⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := pad_bounds hB ch hch hK0 hlt
    have hns := num_take_succ (MM cl) (l := pad cl k ch) (p := σ.vars "w_q")
      (by rw [length_pad']; exact hlt)
    have hpg := pad_getD (cl := cl) (ch := ch) hlt
    have hpl : (pad cl k ch).getD (σ.vars "w_q") 0 ≤ nL cl :=
      pad_le (k := k) hch (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (by rw [length_pad']; exact hlt))
    refine ⟨⟨ha, htake, hle, hn, hL, hM, hK1, hq, hacc, hpw⟩, hlt, fun h => ?_, fun h => ?_, b1,
      by rw [hpw, hM]; ring, by rw [hpw, hM]; exact b3, by rw [hpw]; exact b4,
      by rw [hacc]; exact b5, by rw [hM]; have := MM_ge cl; omega, by rw [hL]; omega,
      by rw [hn]; omega, by omega⟩
    · rw [hn] at h
      have hg : (σ.arrs "ch").getD (σ.vars "w_q") 0 = (pad cl k ch).getD (σ.vars "w_q") 0 := by
        rw [hpg, if_pos h, ha, ← htake]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
      refine ⟨by rw [ha]; omega, ?_, ?_, by rw [hg, hpw]; exact b2⟩
      · rw [hg]; omega
      · rw [hg, hacc, hpw, hns]; ring
    · rw [hn] at h
      have hg : nL cl = (pad cl k ch).getD (σ.vars "w_q") 0 := by rw [hpg, if_neg h]
      refine ⟨by rw [hL, hg, hacc, hpw, hns]; ring, by rw [hL, hg, hpw]; exact b2⟩

/-- The cost of the loop over the padded set. -/
def Kpad (k : ℕ) : ℕ := 54 * (k + 1) + 6

theorem padLoop_spec (hB : BB cl d k B) :
    Spec B (fun σ => σ.vars "w_nch" ≤ k ∧ σ.vars "w_nch" ≤ (σ.arrs "ch").length ∧
        (∀ e ∈ chOf σ, e ≤ nL cl) ∧ σ.vars "w_L" = nL cl ∧ σ.vars "w_M" = MM cl ∧
        σ.vars "w_K1" = k + 1 ∧ σ.vars "w_acc" = σ.vars "w_key" + 1 ∧
        σ.vars "w_pw2" = MM cl ^ (d + 2) ∧ σ.vars "w_key" + 1 < MM cl ^ (d + 2))
      (loop "w_q" "w_K1" padBody)
      (fun σ σ' => σ'.vars "w_acc" = σ.vars "w_key" + 1 + MM cl ^ (d + 2) *
          num (MM cl) (pad cl k (chOf σ)) ∧
        (∀ y, y ∉ ["w_q", "w_e", "w_acc", "w_pw2"] → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (Kpad k) := by
  rintro σ ⟨hn, hnl, hent, hL, hM, hK1, hacc, hpw, hK0⟩
  have hMB := hB.cb.small
  set ch := chOf σ with hchdef
  have hlen : ch.length = σ.vars "w_nch" := by
    rw [hchdef, chOf, List.length_take]; omega
  have hloop := Spec.forRangeZero (B := B) "w_q" "w_K1"
    (PDI cl d k (σ.arrs "ch") ch (σ.vars "w_key" + 1)) (k + 1) 50 (by omega)
    (fun σ h => h.2.2.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.2.2.1)
    (padBody_spec hB hent hK0 (by omega))
  obtain ⟨σ', hr, ⟨⟨-, -, -, -, -, -, -, -, hacc', -⟩, hq'⟩, hv, ha, hin, hout⟩ :=
    hloop.frame.run (σ := σ) ⟨by simp [Env.setVar], by rw [hlen, hchdef]; rfl,
      by omega, by simp [Env.setVar, hlen], by simp [Env.setVar, hL], by simp [Env.setVar, hM],
      by simp [Env.setVar, hK1], by simp [Env.setVar], by simp [Env.setVar, hacc],
      by simp [Env.setVar, hpw]⟩
  refine ⟨σ', hr.mono (by unfold Kpad; omega), ?_, fun y hy => hv y ?_, ?_,
    hin (by simp [padBody, Com.reads]), hout (by simp [padBody, Com.NoWrite])⟩
  · rw [hacc', hq', List.take_of_length_le (by rw [length_pad'])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [padBody, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  · funext a; exact ha a (by simp [padBody, Com.warrs])

theorem lval (c : ℕ) (ch : List ℕ) :
    nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch) =
      3 + MM cl * num (MM cl) (key cl d c ++ pad cl k ch) := by
  unfold nNum
  rw [num_append, length_key]
  ring

/-- **Every stored number is below the bound.** -/
theorem hs_lt (hB : BB cl d k B) {e : ℕ} (he : e ∈ hs cl d k) : e < B := by
  have hM := MM_ge cl
  have hbig := hB.big
  have hsq := MM_sq_lt hB
  rcases mem_hs cl d k he with h | h | h | h | h
  · simp only [varNums, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h; exact hB.var j hj
  · simp only [canonNums, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h
    have := fst_lt cl hj
    have := nL_lt_MM cl
    have : MM cl * fst cl j + MM cl ≤ MM cl * MM cl := by
      have := Nat.mul_le_mul_left (MM cl) (show fst cl j + 1 ≤ MM cl by omega); linarith
    omega
  · simp only [nNums, List.mem_map, List.mem_range] at h
    obtain ⟨c, -, rfl⟩ := h; exact nNum_lt hB c
  · simp only [lNums, List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    obtain ⟨hl, hlt⟩ := lTuple_props cl d k ht
    have h1 := num_lt (show 0 < MM cl by omega) hlt
    rw [hl] at h1
    have h2 : MM cl * num (MM cl) t + MM cl ≤ MM cl * MM cl ^ (d + k + 2) := by
      have := Nat.mul_le_mul_left (MM cl) (show num (MM cl) t + 1 ≤ MM cl ^ (d + k + 2) by omega)
      linarith
    have h3 : MM cl * MM cl ^ (d + k + 2) = MM cl ^ (d + k + 3) := by ring
    have h4 : MM cl ^ (d + k + 3) ≤ MM cl ^ (d + k + 4) := pow_le_big cl (by omega)
    omega
  · subst h; have := hB.hl; omega

/-- The facts `lRow` reads. -/
def LP (cl : List (List ℕ)) (d k c N : ℕ) (ch : List ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.vars "w_key" = nNum cl d c ∧ SRel cl d k σ (some ch) ∧ σ.vars "w_cur" = N ∧
    σ.arrs "hs_mem" = hsS cl d k N ∧ (σ.arrs "ch").length = k + 1

set_option maxHeartbeats 4000000 in
theorem lRow_value (hB : BB cl d k B) {c N : ℕ} {ch : List ℕ} (hN : N < sz cl d k)
    (hval : (hs cl d k).getD N 0 = nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch)) :
    Spec B (LP cl d k c N ch) lRow
      (fun _ σ' => σ'.arrs "hs_mem" = hsS cl d k (N + 1) ∧ σ'.vars "w_cur" = N + 1)
      (Kpad k + 30) := by
  have hMB := hB.cb.small
  have hszB := hB.cb.sz
  have hmd := hB.cb.md (d + 2) le_rfl
  have hbig := hB.big
  have hnk := nNum_lt hB c
  have hK0 : nNum cl d c + 1 < MM cl ^ (d + 2) := by
    have h1 := num_lt (show 0 < MM cl by have := MM_ge cl; omega)
      (l := key cl d c) (fun x hx => key_lt cl d hx)
    rw [length_key] at h1
    have h2 : MM cl * num (MM cl) (key cl d c) + MM cl ≤ MM cl * MM cl ^ (d + 1) := by
      have := Nat.mul_le_mul_left (MM cl) (show num (MM cl) (key cl d c) + 1 ≤ MM cl ^ (d + 1)
        by omega)
      linarith
    have h3 : MM cl * MM cl ^ (d + 1) = MM cl ^ (d + 2) := by ring
    have := MM_ge cl
    unfold nNum; omega
  have hvB : nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch) < B := by
    rw [← hval]
    have h1 : (hs cl d k).getD N 0 ∈ hs cl d k :=
      Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (by rw [length_hs]; exact hN)
    exact hs_lt hB h1
  refine Spec.pre (P := fun σ => LP cl d k c N ch σ ∧
      σ.vars "w_nch" ≤ k ∧ σ.vars "w_nch" ≤ (σ.arrs "ch").length ∧
      (∀ e ∈ chOf σ, e ≤ nL cl) ∧ chOf σ = ch ∧ σ.vars "w_L" = nL cl ∧ σ.vars "w_M" = MM cl ∧
      σ.vars "w_K1" = k + 1 ∧ σ.vars "w_md" = MM cl ^ (d + 2) ∧
      σ.vars "w_cur" < (σ.arrs "hs_mem").length ∧
      (σ.arrs "hs_mem").set N (nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch)) =
        hsS cl d k (N + 1) ∧ N + 1 < B) ?_ ?_
  · unfold lRow
    run_vcg [padLoop_spec hB]
    all_goals (try simp only [LP] at *)
    all_goals (try simp_all [Env.setVar, Env.setArr, chOf]; try omega)
  · intro σ hσ
    obtain ⟨hc, hkey, hR, hcur, hh, hchl⟩ := id hσ
    simp only [SRel] at hR
    obtain ⟨-, hch, hn, -, hlk, hent⟩ := hR
    refine ⟨hσ, by omega, by omega, by rw [hch]; exact hent, hch, hc.hL, hc.hM, hc.hK1, hc.hmd,
      by rw [hcur, hh, length_hsS]; exact hN, by rw [hh, ← hval]; exact hsS_set cl d k hN,
      by omega⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow
