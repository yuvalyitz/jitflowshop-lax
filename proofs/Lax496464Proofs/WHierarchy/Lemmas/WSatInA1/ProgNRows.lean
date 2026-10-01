import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

/-! # Phase 6: the numbers of the keys

`keyLoop_spec`: the key of a clause, digit by digit; `nRows_spec`: phase 6 stores the numbers of the
keys of all clauses. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

variable {cl : List (List ℕ)} {d k B : ℕ}

/-! ### Arithmetic -/

theorem num_take_succ (M : ℕ) {l : List ℕ} {p : ℕ} (hp : p < l.length) :
    num M (l.take (p + 1)) = num M (l.take p) + M ^ p * l.getD p 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some, num_append,
    List.length_take, min_eq_left hp.le, List.getD_eq_getElem _ _ hp]
  simp

theorem num_take_lt {M : ℕ} (hM : 0 < M) {l : List ℕ} (h : ∀ a ∈ l, a < M) (p : ℕ) :
    num M (l.take p) < M ^ (l.take p).length :=
  num_lt hM fun a ha => h a (List.mem_of_mem_take ha)

theorem key_getD {c p : ℕ} (hp : p < d + 1) : (key cl d c).getD p 0 = keyE cl c p := by
  unfold key; rw [List.getD_eq_getElem _ _ (by simpa using hp)]; simp

/-! ### One entry of a key -/

/-- The facts `keyEc` needs about the clause at `w_o`. -/
def KE (cl : List (List ℕ)) (d k c : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ c < cl.length ∧ σ.vars "w_o" = off cl c ∧
    σ.vars "w_ln" = len cl c

set_option maxHeartbeats 2000000 in
theorem keyEc_spec (hB : BB cl d k B) {c p : ℕ} (hpd : p < d + 1) :
    Spec B (fun σ => KE cl d k c σ ∧ σ.vars "w_p" = p) keyEc
      (fun σ σ' => σ' = σ.setVar "w_e" (keyE cl c p)) 20 := by
  have hl := hB.hl
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => KE cl d k c σ ∧ σ.vars "w_p" = p ∧
      (σ.vars "w_p" < σ.vars "w_ln" → σ.vars "w_o" + σ.vars "w_p" < (σ.arrs "cd").length ∧
        σ.vars "w_o" + σ.vars "w_p" < (σ.arrs "fp_f").length ∧
        σ.vars "w_o" + σ.vars "w_p" < B ∧ (σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_p") 0 < B ∧
        (σ.arrs "fp_f").getD (σ.vars "w_o" + σ.vars "w_p") 0 < B ∧
        ((σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_p") 0 % 2 = 0 → keyE cl c p = nL cl) ∧
        (¬ (σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_p") 0 % 2 = 0 →
          keyE cl c p = (σ.arrs "fp_f").getD (σ.vars "w_o" + σ.vars "w_p") 0)) ∧
      (¬ σ.vars "w_p" < σ.vars "w_ln" → keyE cl c p = nL cl) ∧ σ.vars "w_L" = nL cl ∧
      nL cl < B ∧ σ.vars "w_p" < B ∧ σ.vars "w_ln" < B) ?_ ?_
  · unfold keyEc
    run_vcg
    all_goals (try simp only [KE, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨hc, hf, hcm, ho, hln⟩, hp⟩
    have hcd := hc.2.2.1
    have hL := hc.2.2.2.2.1
    have hol := off_len_le cl hcm
    refine ⟨⟨hc, hf, hcm, ho, hln⟩, hp, fun hlt => ?_, fun hlt => ?_, hL, by omega, ?_, ?_⟩
    · rw [ho, hln, hp] at *
      have hj : off cl c + p < nL cl := by omega
      have hcode : (σ.arrs "cd").getD (off cl c + p) 0 = code cl (off cl c + p) := by
        rw [hcd]; rfl
      have hfst : (σ.arrs "fp_f").getD (off cl c + p) 0 = fst cl (off cl c + p) := by
        rw [hf]; exact WH_F1_getD hj
      refine ⟨by rw [hcd]; exact hj, by rw [hf, length_F1]; have := nL_le_sz cl d k; omega,
        by omega, by rw [hcode]; exact code_lt hB.hx hj, by rw [hfst]; have := fst_lt cl hj; omega,
        fun he => ?_, fun he => ?_⟩
      · rw [hcode] at he; simp [keyE, hlt, he]
      · rw [hcode] at he; rw [hfst]; simp [keyE, hlt, he]
    · rw [hln, hp] at hlt; simp [keyE, hlt]
    · rw [hp]; omega
    · rw [hln]; have := off_len_le cl hcm; omega

theorem keyEc_spec' (hB : BB cl d k B) {c : ℕ} :
    Spec B (fun σ => KE cl d k c σ ∧ σ.vars "w_p" < d + 1) keyEc
      (fun σ σ' => σ' = σ.setVar "w_e" (keyE cl c (σ.vars "w_p"))) 20 :=
  fun σ hσ => keyEc_spec hB hσ.2 σ ⟨hσ.1, rfl⟩

/-! ### The loop over the entries of a key -/

def KI (cl : List (List ℕ)) (d k c : ℕ) (σ : Env) : Prop :=
  KE cl d k c σ ∧ σ.vars "w_p" ≤ d + 1 ∧
    σ.vars "w_acc" = 2 + MM cl * num (MM cl) ((key cl d c).take (σ.vars "w_p")) ∧
    σ.vars "w_pw" = MM cl * MM cl ^ σ.vars "w_p"

theorem key_bounds (hB : BB cl d k B) (c : ℕ) {p : ℕ} (hp : p < d + 1) :
    2 + MM cl * num (MM cl) ((key cl d c).take (p + 1)) < B ∧
      keyE cl c p * (MM cl * MM cl ^ p) < B ∧ MM cl * MM cl ^ (p + 1) < B ∧
      MM cl * MM cl ^ p < B := by
  have hM := MM_ge cl
  have hbig := hB.big
  have h1 := num_take_lt (show 0 < MM cl by omega) (fun a ha => key_lt cl d (c := c) ha) (p + 1)
  have hlen : ((key cl d c).take (p + 1)).length = p + 1 := by
    rw [List.length_take, length_key]; omega
  rw [hlen] at h1
  have e1 : MM cl * MM cl ^ (p + 1) = MM cl ^ (p + 2) := by ring
  have e2 : MM cl * MM cl ^ p = MM cl ^ (p + 1) := by ring
  have h2 : MM cl ^ (p + 2) ≤ MM cl ^ (d + k + 4) := pow_le_big cl (by omega)
  have h3 : MM cl ^ (p + 1) ≤ MM cl ^ (p + 2) := pow_le_big cl (by omega)
  have h4 : keyE cl c p < MM cl := by have := keyE_le cl c p; have := nL_lt_MM cl; omega
  have h5 : keyE cl c p * MM cl ^ (p + 1) ≤ MM cl * MM cl ^ (p + 1) :=
    Nat.mul_le_mul_right _ h4.le
  have h6 : MM cl * num (MM cl) ((key cl d c).take (p + 1)) < MM cl * MM cl ^ (p + 1) :=
    Nat.mul_lt_mul_of_pos_left h1 (by omega)
  rw [e2]
  refine ⟨by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem keyBody_spec (hB : BB cl d k B) {c : ℕ} :
    Spec B (fun σ => KI cl d k c σ ∧ σ.vars "w_p" < d + 1) keyBody
      (fun σ σ' => KI cl d k c σ' ∧ σ'.vars "w_p" = σ.vars "w_p" + 1) 40 := by
  have hMB := hB.cb.small
  have hl := hB.hl
  refine Spec.pre (P := fun σ => KI cl d k c σ ∧ σ.vars "w_p" < d + 1 ∧
      σ.vars "w_acc" + keyE cl c (σ.vars "w_p") * σ.vars "w_pw" =
        2 + MM cl * num (MM cl) ((key cl d c).take (σ.vars "w_p" + 1)) ∧
      σ.vars "w_pw" * σ.vars "w_M" = MM cl * MM cl ^ (σ.vars "w_p" + 1) ∧
      σ.vars "w_acc" + keyE cl c (σ.vars "w_p") * σ.vars "w_pw" < B ∧
      keyE cl c (σ.vars "w_p") * σ.vars "w_pw" < B ∧ σ.vars "w_pw" * σ.vars "w_M" < B ∧
      σ.vars "w_pw" < B ∧ σ.vars "w_M" < B ∧ keyE cl c (σ.vars "w_p") < B ∧
      σ.vars "w_acc" < B ∧ σ.vars "w_p" + 1 < B) ?_ ?_
  · unfold keyBody
    run_vcg [keyEc_spec' hB]
    all_goals (try simp only [KI, KE, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨hke, hp, hacc, hpw⟩, hlt⟩
    have hM : σ.vars "w_M" = MM cl := hke.1.hM
    obtain ⟨b1, b2, b3, b4⟩ := key_bounds hB c hlt
    have hk2 : keyE cl c (σ.vars "w_p") ≤ nL cl := keyE_le cl c _
    have hn := num_take_succ (MM cl) (l := key cl d c) (p := σ.vars "w_p")
      (by rw [length_key]; exact hlt)
    rw [key_getD hlt] at hn
    have e1 : σ.vars "w_acc" + keyE cl c (σ.vars "w_p") * σ.vars "w_pw" =
        2 + MM cl * num (MM cl) ((key cl d c).take (σ.vars "w_p" + 1)) := by
      rw [hacc, hpw, hn]; ring
    have e2 : σ.vars "w_pw" * σ.vars "w_M" = MM cl * MM cl ^ (σ.vars "w_p" + 1) := by
      rw [hpw, hM]; ring
    have hacc_lt : σ.vars "w_acc" < B := by
      rw [hacc]
      have h7 : num (MM cl) ((key cl d c).take (σ.vars "w_p")) ≤
          num (MM cl) ((key cl d c).take (σ.vars "w_p" + 1)) := by rw [hn]; omega
      have h8 := Nat.mul_le_mul_left (MM cl) h7
      omega
    refine ⟨⟨hke, hp, hacc, hpw⟩, hlt, e1, e2, by rw [e1]; exact b1, by rw [hpw]; exact b2,
      by rw [e2]; exact b3, by rw [hpw]; exact b4, by rw [hM]; omega, by omega, hacc_lt,
      by omega⟩

/-- The cost of the loop over the entries of a key. -/
def Kkey (d : ℕ) : ℕ := 44 * (d + 1) + 6

theorem keyLoop_spec (hB : BB cl d k B) {c : ℕ} :
    Spec B (fun σ => KE cl d k c σ ∧ σ.vars "w_acc" = 2 ∧ σ.vars "w_pw" = MM cl)
      (loop "w_p" "w_d1" keyBody)
      (fun σ σ' => σ'.vars "w_acc" = nNum cl d c ∧
        (∀ y, y ∉ ["w_p", "w_e", "w_acc", "w_pw"] → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (Kkey d) := by
  rintro σ ⟨hke, hacc, hpw⟩
  have hMB := hB.cb.small
  have hloop := Spec.forRangeZero (B := B) "w_p" "w_d1" (KI cl d k c) (d + 1) 40 (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1.1.hd1) (keyBody_spec hB)
  have hke' : KE cl d k c (σ.setVar "w_p" 0) := by
    obtain ⟨hc, hf, hcm, ho, hln⟩ := hke
    refine ⟨hc.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hf], hcm,
      by simp [Env.setVar, ho], by simp [Env.setVar, hln]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ', hr, ⟨⟨-, -, hacc', -⟩, hp'⟩, hv, ha, hin, hout⟩ :=
    hloop.frame.run (σ := σ) ⟨hke', by simp [Env.setVar], by simp [Env.setVar, hacc],
      by simp [Env.setVar, hpw]⟩
  refine ⟨σ', hr, ?_, fun y hy => hv y ?_, ?_, hin (by simp [keyBody, keyEc, Com.reads]),
    hout (by simp [keyBody, keyEc, Com.NoWrite])⟩
  · rw [hacc', hp', nNum, List.take_of_length_le (by rw [length_key])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [keyBody, keyEc, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  · funext a; exact ha a (by simp [keyBody, keyEc, Com.warrs])

theorem keyLoop_spec' (hB : BB cl d k B) :
    Spec B (fun σ => KE cl d k (σ.vars "w_c") σ ∧ σ.vars "w_acc" = 2 ∧ σ.vars "w_pw" = MM cl)
      (loop "w_p" "w_d1" keyBody)
      (fun σ σ' => σ'.vars "w_acc" = nNum cl d (σ.vars "w_c") ∧
        (∀ y, y ∉ ["w_p", "w_e", "w_acc", "w_pw"] → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (Kkey d) :=
  fun σ hσ => keyLoop_spec hB σ hσ

theorem nNum_lt (hB : BB cl d k B) (c : ℕ) : nNum cl d c < B := by
  have := (key_bounds hB c (p := d) (by omega)).1
  rwa [List.take_of_length_le (by rw [length_key]), ← nNum] at this

/-! ### The loop over the clauses -/

def NI (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ σ.vars "w_c" ≤ cl.length ∧
    σ.arrs "hs_mem" = hsS cl d k (2 * nL cl + σ.vars "w_c")

set_option maxHeartbeats 4000000 in
theorem nBody_spec (hB : BB cl d k B) :
    Spec B (fun σ => NI cl d k σ ∧ σ.vars "w_c" < cl.length) nBody
      (fun σ σ' => NI cl d k σ' ∧ σ'.vars "w_c" = σ.vars "w_c" + 1) (Kkey d + 60) := by
  have hMB := hB.cb.small
  have hl := hB.hl
  have hszB := hB.cb.sz
  have hsz := nL_le_sz cl d k
  refine Spec.pre (P := fun σ => NI cl d k σ ∧ σ.vars "w_c" < cl.length ∧
      σ.vars "w_c" + 1 < (σ.arrs "co").length ∧
      (σ.arrs "co").getD (σ.vars "w_c") 0 = off cl (σ.vars "w_c") ∧
      (σ.arrs "co").getD (σ.vars "w_c" + 1) 0 - off cl (σ.vars "w_c") = len cl (σ.vars "w_c") ∧
      (σ.arrs "co").getD (σ.vars "w_c") 0 < B ∧ (σ.arrs "co").getD (σ.vars "w_c" + 1) 0 < B ∧
      2 * σ.vars "w_L" + σ.vars "w_c" < (σ.arrs "hs_mem").length ∧
      (σ.arrs "hs_mem").set (2 * σ.vars "w_L" + σ.vars "w_c") (nNum cl d (σ.vars "w_c")) =
        hsS cl d k (2 * nL cl + (σ.vars "w_c" + 1)) ∧
      nNum cl d (σ.vars "w_c") < B ∧ 2 * σ.vars "w_L" + σ.vars "w_c" < B ∧
      σ.vars "w_c" + 1 < B ∧ 2 * σ.vars "w_L" < B ∧ MM cl < B) ?_ ?_
  · unfold nBody
    run_vcg [keyLoop_spec' hB]
    all_goals (try simp only [NI, KE, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨hc, hf, hcm, hh⟩, hlt⟩
    have hco := hc.hco
    have hL := hc.hL
    have hol := off_len_le cl hlt
    have hsucc := off_succ cl hlt
    refine ⟨⟨hc, hf, hcm, hh⟩, hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, nNum_lt hB _, ?_, by omega, ?_,
      by omega⟩
    · rw [hco, length_coList]; omega
    · rw [hco, coList_getD (by omega)]
    · rw [hco, coList_getD (by omega)]; omega
    · rw [hco, coList_getD (by omega)]; omega
    · rw [hco, coList_getD (by omega)]; omega
    · rw [hh, length_hsS, hL]; omega
    · rw [hh, hL, ← hs_n cl d k hlt, ← Nat.add_assoc]; exact hsS_set cl d k (by omega)
    · rw [hL]; omega
    · rw [hL]; omega

/-- The cost of `nRows`. -/
def KnRows (cl : List (List ℕ)) (d : ℕ) : ℕ := (Kkey d + 64) * cl.length + 6

theorem nRows_spec (hB : BB cl d k B) :
    Spec B (fun σ => Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧
        σ.arrs "hs_mem" = hsS cl d k (2 * nL cl)) nRows
      (fun _ σ' => Ctx cl d k σ' ∧ σ'.arrs "fp_f" = F1 cl d k ∧
        σ'.arrs "hs_mem" = hsS cl d k (2 * nL cl + cl.length)) (KnRows cl d) := by
  have hl := hB.hl
  refine Spec.post (Spec.pre (Spec.forRangeZero "w_c" "w_m" (NI cl d k) cl.length (Kkey d + 60)
    (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.hm) (nBody_spec hB)) ?_) ?_
  · rintro σ ⟨hc, hf, hh⟩
    refine ⟨hc.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hf],
      by simp [Env.setVar], by simp [Env.setVar, hh]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · rintro σ σ' - ⟨⟨hc, hf, -, hh⟩, hj⟩
    exact ⟨hc, hf, by rw [hh, hj]⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
