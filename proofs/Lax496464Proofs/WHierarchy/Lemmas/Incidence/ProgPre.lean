import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok

/-! # Phase 4: the first walk over the tokens — the number of atoms and the largest arity

`preBody_tok`: one turn of the walk over a token of a positive `Σ_1`-formula; `prePass_spec`: after
the walk, `ic_q` is the number of atoms and `ic_r` the largest arity. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgPre

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-- The scalars `preBody` assigns. -/
def preVars : List String := ["ic_t", "ic_k", "ic_q", "ic_r", "ic_p"]

/-- What one turn does with the token `t`. -/
def PrePost (t : Token) (σ σ' : Env) : Prop :=
  σ'.vars "ic_p" = σ.vars "ic_p" + t.code.length ∧ σ'.vars "ic_q" = σ.vars "ic_q" + t.isRel ∧
    σ'.vars "ic_r" = if σ.vars "ic_r" < t.relLen then t.relLen else σ.vars "ic_r"

/-- The common precondition of one turn. -/
def PrePre (x : List ℕ) (B : ℕ) (t : Token) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ TokAt x (σ.vars "ic_p") t ∧ σ.vars "ic_q" < x.length ∧
    σ.vars "ic_r" ≤ x.length ∧ maxEntry x + 2 * x.length + 8 < B

theorem tok0 {p : ℕ} {t : Token} (h : TokAt x p t) : x.getD p 0 = t.code.getD 0 0 := by
  have := h.2 0 (code_length_pos t); simpa using this

set_option maxHeartbeats 2000000 in
theorem preBody_rel (i : ℕ) (ys : List ℕ) :
    Spec B (PrePre x B (.rel i ys)) preBody (fun σ σ' =>
      σ'.vars "ic_p" = σ.vars "ic_p" + (Token.rel i ys).code.length ∧
      σ'.vars "ic_q" = σ.vars "ic_q" + 1 ∧
      σ'.vars "ic_r" = if σ.vars "ic_r" < ys.length then ys.length else σ.vars "ic_r") 60 := by
  unfold preBody preRel
  refine Spec.pre (P := fun σ => PrePre x B (.rel i ys) σ ∧
      σ.vars "ic_p" + 2 < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_p") 0 = 0 ∧
      (σ.arrs "a").getD (σ.vars "ic_p" + 2) 0 = ys.length ∧
      σ.vars "ic_p" + 3 + ys.length < B ∧ σ.vars "ic_q" + 1 < B ∧ ys.length < B ∧
      σ.vars "ic_r" < B) ?_ ?_
  · run_vcg
    all_goals (simp only [PrePre, Token.code] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨ha, ht, hq, hr, hb⟩
    have hl := ht.1
    simp only [Token.code, List.length_cons] at hl
    have h0 := tok0 ht
    have h2 := ht.2 2 (by simp [Token.code])
    simp only [Token.code, List.getD_cons_zero, List.getD_cons_succ] at h0 h2
    refine ⟨⟨ha, ht, hq, hr, hb⟩, by rw [ha]; omega, by rw [ha]; exact h0, by rw [ha]; exact h2,
      by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem preBody_eq (u v : ℕ) :
    Spec B (PrePre x B (.eq u v)) preBody (fun σ σ' =>
      σ'.vars "ic_p" = σ.vars "ic_p" + (Token.eq u v).code.length ∧
      σ'.vars "ic_q" = σ.vars "ic_q" ∧ σ'.vars "ic_r" = σ.vars "ic_r") 60 := by
  unfold preBody preRel
  refine Spec.pre (P := fun σ => PrePre x B (.eq u v) σ ∧
      σ.vars "ic_p" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_p") 0 = 2 ∧ σ.vars "ic_p" + 3 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [PrePre, Token.code] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨ha, ht, hq, hr, hb⟩
    have hl := ht.1
    simp only [Token.code, List.length_cons] at hl
    have h0 := tok0 ht
    simp only [Token.code, List.getD_cons_zero] at h0
    exact ⟨⟨ha, ht, hq, hr, hb⟩, by rw [ha]; simp at hl; omega, by rw [ha]; exact h0, by
      simp at hl; omega⟩

set_option maxHeartbeats 2000000 in
theorem preBody_ex (u : ℕ) :
    Spec B (PrePre x B (.ex u)) preBody (fun σ σ' =>
      σ'.vars "ic_p" = σ.vars "ic_p" + (Token.ex u).code.length ∧
      σ'.vars "ic_q" = σ.vars "ic_q" ∧ σ'.vars "ic_r" = σ.vars "ic_r") 60 := by
  unfold preBody preRel
  refine Spec.pre (P := fun σ => PrePre x B (.ex u) σ ∧
      σ.vars "ic_p" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_p") 0 = 6 ∧ σ.vars "ic_p" + 2 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [PrePre, Token.code] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨ha, ht, hq, hr, hb⟩
    have hl := ht.1
    simp only [Token.code, List.length_cons] at hl
    have h0 := tok0 ht
    simp only [Token.code, List.getD_cons_zero] at h0
    exact ⟨⟨ha, ht, hq, hr, hb⟩, by rw [ha]; simp at hl; omega, by rw [ha]; exact h0, by
      simp at hl; omega⟩

set_option maxHeartbeats 2000000 in
/-- `∧` and `∨`: tags `4` and `5`. -/
theorem preBody_conn (t : Token) (htag : t.code = [4] ∨ t.code = [5]) :
    Spec B (PrePre x B t) preBody (fun σ σ' =>
      σ'.vars "ic_p" = σ.vars "ic_p" + t.code.length ∧
      σ'.vars "ic_q" = σ.vars "ic_q" ∧ σ'.vars "ic_r" = σ.vars "ic_r") 60 := by
  have hrel : t.isRel = 0 ∧ t.relLen = 0 := by
    cases t <;> simp_all [Token.code, Token.isRel, Token.relLen]
  unfold preBody preRel
  refine Spec.pre (P := fun σ => PrePre x B t σ ∧
      σ.vars "ic_p" < (σ.arrs "a").length ∧
      ((σ.arrs "a").getD (σ.vars "ic_p") 0 = 4 ∨ (σ.arrs "a").getD (σ.vars "ic_p") 0 = 5) ∧
      σ.vars "ic_p" + 1 < B ∧ t.code.length = 1) ?_ ?_
  · run_vcg
    all_goals (simp only [PrePre] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨ha, ht, hq, hr, hb⟩
    have hl := ht.1
    have h0 := tok0 ht
    have hlen : t.code.length = 1 := by rcases htag with h | h <;> rw [h] <;> rfl
    refine ⟨⟨ha, ht, hq, hr, hb⟩, by rw [ha]; omega, ?_, by omega, hlen⟩
    rw [ha, h0]
    rcases htag with h | h <;> rw [h] <;> simp

/-- **One turn**, for any token of a positive `Σ_1`-formula. -/
theorem preBody_tok (t : Token) (hok : Token.Ok t) :
    Spec B (PrePre x B t) preBody (PrePost t) 60 := by
  have h0 : ∀ r : ℕ, r = if r < 0 then 0 else r := fun r => (if_neg (Nat.not_lt_zero r)).symm
  cases t with
  | rel i ys => exact preBody_rel i ys
  | eq u v => exact (preBody_eq u v).post fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.trans (h0 _)⟩
  | ex u => exact (preBody_ex u).post fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.trans (h0 _)⟩
  | and => exact (preBody_conn _ (Or.inl rfl)).post fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.trans (h0 _)⟩
  | or => exact (preBody_conn _ (Or.inr rfl)).post fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.trans (h0 _)⟩
  | setVar _ => exact hok.elim
  | neg => exact hok.elim
  | all _ => exact hok.elim

theorem preBody_tok' (t : Token) (hok : Token.Ok t) :
    Spec B (PrePre x B t) preBody
      (fun σ σ' => PrePost t σ σ' ∧ Keep preVars σ σ' ∧ σ'.out = σ.out) 60 :=
  Spec.keepOut (preBody_tok t hok) _
    (by intro y hy; simp [preBody, preRel, Com.wvars] at hy; simp [preVars]; tauto)
    (by simp [preBody, preRel, Com.warrs]) (by simp [preBody, preRel, Com.reads])
    (by simp [preBody, preRel, Com.NoWrite])

/-- The invariant of the first walk. -/
def PreI (x : List ℕ) (φ : Formula) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ ∃ done rest : List Token, toks φ = done ++ rest ∧
    σ.vars "ic_p" = fsOf x + clen done ∧ σ.vars "ic_q" = nrelT done ∧ σ.vars "ic_r" = rmaxT done

theorem rmaxT_snoc (l : List Token) (t : Token) :
    rmaxT (l ++ [t]) = if rmaxT l < t.relLen then t.relLen else rmaxT l := by
  rw [rmaxT_append]; simp only [rmaxT_cons, rmaxT_nil]; split_ifs <;> omega

theorem preBody_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => PreI x φ σ ∧ (Cond.lt (V "ic_p") (V "rt_n")).evalB B σ = some true) preBody
      (fun σ σ' => PreI x φ σ' ∧ x.length - σ'.vars "ic_p" < x.length - σ.vars "ic_p") 60 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  rintro σ ⟨⟨ha, hn, done, rest, hsplit, hp, hq, hr⟩, hc⟩
  have hlt := lt_of_condLt_true hc
  rw [hn, hp] at hlt
  obtain ⟨t, rest', rfl⟩ := List.exists_cons_of_ne_nil (rest_ne_nil hd hsplit hlt)
  have hok := hd.ok t (by rw [hsplit]; simp)
  have htok := tokAt_of_split hd hsplit
  have hcl := clen_le hd (show toks φ = (done ++ [t]) ++ rest' by rw [hsplit]; simp)
  rw [clen_append, clen_singleton] at hcl
  have hq' := nrelT_le_clen done
  have hr' := rmaxT_le_clen done
  have hpos := code_length_pos t
  obtain ⟨σ', hrun, ⟨hp', hq'', hr''⟩, hk, -⟩ := preBody_tok' (B := B) t hok σ
    ⟨ha, by rw [hp]; exact htok, by rw [hq]; omega, by rw [hr]; omega, hb⟩
  refine ⟨σ', hrun, ⟨?_, ?_, done ++ [t], rest', by rw [hsplit]; simp, ?_, ?_, ?_⟩, ?_⟩
  · rw [hk.2.1]; exact ha
  · rw [hk.1 "rt_n" (by simp [preVars])]; exact hn
  · rw [hp', hp, clen_append, clen_singleton]; omega
  · rw [hq'', hq, nrelT_append]; simp
  · rw [hr'', hr, rmaxT_snoc]
  · rw [hp', hp]; omega

/-- The cost of the first walk. -/
def Kpre (x : List ℕ) : ℕ := (1 + 3 + 60) * x.length + 1 + 3

theorem preLoop_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (PreI x φ) preLoop (fun _ σ' => PreI x φ σ' ∧ σ'.vars "ic_p" = x.length) (Kpre x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  refine Spec.post (Spec.while_count (PreI x φ) (fun σ => x.length - σ.vars "ic_p") 60
    (fun σ h => by
      obtain ⟨_, hn, done, rest, hs, hp, _⟩ := h
      have := clen_le hd hs
      exact evalB_condLt_vars (by rw [hp]; omega) (by rw [hn]; omega))
    (preBody_spec hd hB) (fun _ h => h) (fun σ _ => ?_)) ?_
  · show (1 + 3 + 60) * (x.length - σ.vars "ic_p") + 1 + 3 ≤ Kpre x
    unfold Kpre
    have := Nat.mul_le_mul_left (1 + 3 + 60) (Nat.sub_le x.length (σ.vars "ic_p"))
    omega
  · rintro σ σ' - ⟨hI, hf⟩
    refine ⟨hI, ?_⟩
    have := le_of_condLt_false hf
    obtain ⟨-, hn, done, rest, hs, hp, -⟩ := hI
    have := clen_le hd hs
    omega

/-- At the end of the walk all the tokens are done. -/
theorem preI_end (hd : Dom x φ) {σ : Env} (h : PreI x φ σ) (hp : σ.vars "ic_p" = x.length) :
    σ.vars "ic_q" = nrel φ ∧ σ.vars "ic_r" = rOf φ := by
  obtain ⟨-, -, done, rest, hs, hp', hq, hr⟩ := h
  have hrest : rest = [] := by
    by_contra hne
    obtain ⟨t, rest', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := pos_split hd hs
    have h1 : clen (t :: rest') = t.code.length + clen rest' := by simp [clen]
    have := code_length_pos t
    omega
  subst hrest
  rw [List.append_nil] at hs
  exact ⟨by rw [hq, nrel, hs], by rw [hr, rOf, hs]⟩

theorem prePass_value (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "ic_b" = fsOf x)
      prePass (fun _ σ' => σ'.vars "ic_q" = nrel φ ∧ σ'.vars "ic_r" = rOf φ) (10 + Kpre x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hfs := fs_le hd
  unfold prePass
  run_vcg [preLoop_spec hd hB]
  all_goals first
    | exact preI_end hd (‹PreI x φ _ ∧ _›).1 (‹PreI x φ _ ∧ _›).2
    | (simp only [fsOf] at *; omega)
    | (refine ⟨?_, ?_, [], toks φ, rfl, ?_, ?_, ?_⟩ <;> simp_all [Env.setVar, clen])

theorem prePass_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "ic_b" = fsOf x)
      prePass (fun σ σ' => (σ'.vars "ic_q" = nrel φ ∧ σ'.vars "ic_r" = rOf φ) ∧
        Keep preVars σ σ' ∧ σ'.out = σ.out) (10 + Kpre x) :=
  Spec.keepOut (prePass_value hd hB) _
    (by intro y hy; simp [prePass, preLoop, preBody, preRel, Com.wvars] at hy
        simp [preVars]; tauto)
    (by simp [prePass, preLoop, preBody, preRel, Com.warrs])
    (by simp [prePass, preLoop, preBody, preRel, Com.reads])
    (by simp [prePass, preLoop, preBody, preRel, Com.NoWrite])

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgPre
