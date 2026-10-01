import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF

/-! # Phase 9: the second walk over the tokens writes the translated formula

`fBody_tok`: one turn of the walk writes the translation of the current token; `fOut_spec`: the
whole walk writes the translated formula. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-- The context of the translation the program carries out. -/
abbrev Cx (x : List ℕ) (φ : Formula) : TrCtx := ctxOf (dataOf x (rOf φ)) (fOf x)

/-- The common precondition of one turn. -/
def FPre (x : List ℕ) (φ : Formula) (p z : ℕ) (t : Token) (σ : Env) : Prop :=
  Ctx x φ σ ∧ σ.vars "ic_p" = p ∧ σ.vars "ic_z" = z ∧ TokAt x p t ∧ z < x.length

/-- The cost of one turn. -/
def Kf (x : List ℕ) : ℕ := (60 + 4) * x.length + 300

theorem relOut_absurd {Q : Env → Env → Prop} : Spec B (fun _ => False) relOut Q 0 :=
  fun _ h => h.elim

set_option maxHeartbeats 4000000 in
theorem fBody_rel (hd : Dom x φ) (hB : BOK x B) (p i : ℕ) (ys : List ℕ) (z : ℕ) :
    Spec B (FPre x φ p z (.rel i ys)) fBody
      (fun σ σ' => (i < sOf x ∧ ys.length = arOf x i → σ'.vars "ic_P" = i) ∧
        (¬ (i < sOf x ∧ ys.length = arOf x i) → σ'.vars "ic_P" = sOf x + rOf φ) ∧
        σ'.out = σ.out ++ argList x (sOf x) p (fOf x + z) ys.length ++
          [0, σ'.vars "ic_P", 1, fOf x + z] ∧
        σ'.vars "ic_p" = p + 3 + ys.length ∧ σ'.vars "ic_z" = z + 1 ∧ Ctx x φ σ') (Kf x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold fBody Kf
  refine Spec.pre (P := fun σ => FPre x φ p z (.rel i ys) σ ∧ p < (σ.arrs "a").length ∧
    (σ.arrs "a").getD p 0 = 0) ?_ ?_
  · run_vcg [relOut_value hd hB p i ys z]
    all_goals (simp only [FPre, Ctx] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨hc, hp, hz, ht, hzl⟩
    obtain ⟨t1, t2, -⟩ := tokAt_rel ht
    exact ⟨⟨hc, hp, hz, ht, hzl⟩, by rw [hc.1]; omega, by rw [hc.1]; exact t2⟩

set_option maxHeartbeats 4000000 in
theorem fBody_eq (hB : BOK x B) (p u v z : ℕ) :
    Spec B (FPre x φ p z (.eq u v)) fBody
      (fun σ σ' => σ'.out = σ.out ++ [2, u, v] ∧ σ'.vars "ic_p" = p + 3 ∧ σ'.vars "ic_z" = z ∧
        Ctx x φ σ') (Kf x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold fBody eqOut Kf
  refine Spec.pre (P := fun σ => FPre x φ p z (.eq u v) σ ∧ p + 2 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD p 0 = 2 ∧ (σ.arrs "a").getD (p + 1) 0 = u ∧
    (σ.arrs "a").getD (p + 2) 0 = v ∧ u < B ∧ v < B ∧ p + 3 < B) ?_ ?_
  · run_vcg [relOut_absurd (B := B) (Q := fun _ _ => False)]
    all_goals ((try simp only [FPre, Ctx] at *) <;> (try simp_all [Env.setVar]) <;> (try omega))
  · rintro σ ⟨hc, hp, hz, ht, hzl⟩
    have ha := hc.1
    obtain ⟨h1, h2⟩ := ht
    simp only [Token.code, List.length_cons, List.length_nil] at h1 h2
    have e0 := h2 0 (by omega); have e1 := h2 1 (by omega); have e2 := h2 2 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2
    refine ⟨⟨hc, hp, hz, ⟨by simp [Token.code]; omega, h2⟩, hzl⟩, by rw [ha]; omega,
      by rw [ha]; exact e0, by rw [ha]; exact e1, by rw [ha]; exact e2, ?_, ?_, by omega⟩
    · rw [← e1]; exact getD_lt hB _
    · rw [← e2]; exact getD_lt hB _

set_option maxHeartbeats 4000000 in
theorem fBody_ex (hB : BOK x B) (p u z : ℕ) :
    Spec B (FPre x φ p z (.ex u)) fBody
      (fun σ σ' => σ'.out = σ.out ++ [6, u] ∧ σ'.vars "ic_p" = p + 2 ∧ σ'.vars "ic_z" = z ∧
        Ctx x φ σ') (Kf x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold fBody exOut Kf
  refine Spec.pre (P := fun σ => FPre x φ p z (.ex u) σ ∧ p + 1 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD p 0 = 6 ∧ (σ.arrs "a").getD (p + 1) 0 = u ∧ u < B ∧ p + 2 < B) ?_ ?_
  · run_vcg [relOut_absurd (B := B) (Q := fun _ _ => False)]
    all_goals ((try simp only [FPre, Ctx] at *) <;> (try simp_all [Env.setVar]) <;> (try omega))
  · rintro σ ⟨hc, hp, hz, ht, hzl⟩
    have ha := hc.1
    obtain ⟨h1, h2⟩ := ht
    simp only [Token.code, List.length_cons, List.length_nil] at h1 h2
    have e0 := h2 0 (by omega); have e1 := h2 1 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
    refine ⟨⟨hc, hp, hz, ⟨by simp [Token.code]; omega, h2⟩, hzl⟩, by rw [ha]; omega,
      by rw [ha]; exact e0, by rw [ha]; exact e1, ?_, by omega⟩
    · rw [← e1]; exact getD_lt hB _

set_option maxHeartbeats 4000000 in
theorem fBody_conn (hB : BOK x B) (p z c : ℕ) (t : Token) (htc : t.code = [c])
    (hc4 : c = 4 ∨ c = 5) :
    Spec B (FPre x φ p z t) fBody
      (fun σ σ' => σ'.out = σ.out ++ [c] ∧ σ'.vars "ic_p" = p + 1 ∧ σ'.vars "ic_z" = z ∧
        Ctx x φ σ') (Kf x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold fBody otherOut Kf
  refine Spec.pre (P := fun σ => FPre x φ p z t σ ∧ p < (σ.arrs "a").length ∧
    (σ.arrs "a").getD p 0 = c ∧ (c = 4 ∨ c = 5) ∧ p + 1 < B) ?_ ?_
  · run_vcg [relOut_absurd (B := B) (Q := fun _ _ => False)]
    all_goals ((try simp only [FPre, Ctx] at *) <;> (try simp_all [Env.setVar]) <;> (try omega))
  · rintro σ ⟨hc, hp, hz, ht, hzl⟩
    have ha := hc.1
    have h1 := ht.1
    have e0 := ht.2 0 (by rw [htc]; simp)
    rw [htc] at h1 e0
    simp only [List.length_cons, List.length_nil, List.getD_cons_zero, Nat.add_zero] at h1 e0
    exact ⟨⟨hc, hp, hz, ht, hzl⟩, by rw [ha]; omega, by rw [ha]; exact e0, hc4, by omega⟩

/-- **One turn**, for any token of a positive `Σ_1`-formula: the token's translation is written. -/
theorem fBody_tok (hd : Dom x φ) (hB : BOK x B) (p z : ℕ) (t : Token) (hok : Token.Ok t) :
    Spec B (FPre x φ p z t) fBody
      (fun σ σ' => σ'.out = σ.out ++ (Cx x φ).emitTok z t ∧
        σ'.vars "ic_p" = p + t.code.length ∧ σ'.vars "ic_z" = z + t.isRel ∧ Ctx x φ σ')
      (Kf x) := by
  cases t with
  | rel i ys =>
    intro σ hσ
    obtain ⟨σ', hr, hP1, hP2, ho, hp, hz, hc⟩ := fBody_rel hd hB p i ys z σ hσ
    refine ⟨σ', hr, ?_, by rw [hp]; simp [Token.code]; omega, by rw [hz]; rfl, hc⟩
    obtain ⟨-, -, -, -, hys⟩ := tokAt_rel hσ.2.2.2.1
    have harg : argList x (sOf x) p (fOf x + z) ys.length =
        (List.range ys.length).flatMap fun l => [4, 0, (Cx x φ).s + l, 2, ys.getD l 0,
          (Cx x φ).F + z] := by
      unfold argList
      refine List.flatMap_congr fun l hl => ?_
      rw [hys l (List.mem_range.mp hl)]
      rfl
    have hP : σ'.vars "ic_P" = (Cx x φ).pIdx i ys.length := by
      by_cases hcnd : i < sOf x ∧ ys.length = arOf x i
      · rw [hP1 hcnd]; unfold TrCtx.pIdx; exact (if_pos hcnd).symm
      · rw [hP2 hcnd]; unfold TrCtx.pIdx; exact (if_neg hcnd).symm
    rw [ho, harg, hP]
    simp [TrCtx.emitTok, TrCtx.relCode]
    rfl
  | eq u v =>
    exact (fBody_eq hB p u v z).post fun _ _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, by rw [h2]; rfl, h3, h4⟩
  | ex u =>
    exact (fBody_ex hB p u z).post fun _ _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, by rw [h2]; rfl, h3, h4⟩
  | and =>
    exact (fBody_conn hB p z 4 .and rfl (Or.inl rfl)).post fun _ _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, by rw [h2]; rfl, h3, h4⟩
  | or =>
    exact (fBody_conn hB p z 5 .or rfl (Or.inr rfl)).post fun _ _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, by rw [h2]; rfl, h3, h4⟩
  | setVar _ => exact hok.elim
  | neg => exact hok.elim
  | all _ => exact hok.elim

/-- The invariant of the second walk. -/
def FI (x : List ℕ) (φ : Formula) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x φ σ ∧ ∃ done rest : List Token, toks φ = done ++ rest ∧
    σ.vars "ic_p" = fsOf x + clen done ∧ σ.vars "ic_z" = nrelT done ∧
    σ.out = out0 ++ (Cx x φ).emit 0 done

theorem fBody_spec (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => FI x φ out0 σ ∧ (Cond.lt (V "ic_p") (V "rt_n")).evalB B σ = some true) fBody
      (fun σ σ' => FI x φ out0 σ' ∧ x.length - σ'.vars "ic_p" < x.length - σ.vars "ic_p")
      (Kf x) := by
  rintro σ ⟨⟨hc, done, rest, hsplit, hp, hz, ho⟩, hcond⟩
  have hlt := lt_of_condLt_true hcond
  rw [hc.2.1, hp] at hlt
  obtain ⟨t, rest', rfl⟩ := List.exists_cons_of_ne_nil (rest_ne_nil hd hsplit hlt)
  have hok := hd.ok t (by rw [hsplit]; simp)
  have htok := tokAt_of_split hd hsplit
  have hcl := clen_le hd (show toks φ = (done ++ [t]) ++ rest' by rw [hsplit]; simp)
  rw [clen_append, clen_singleton] at hcl
  have hq' := nrelT_le_clen done
  have hpos := code_length_pos t
  have hfs2 : 2 ≤ fsOf x := by
    have := bo_mono x (Nat.zero_le (sOf x)); rw [bo_zero] at this; unfold fsOf; omega
  obtain ⟨σ', hrun, ho', hp', hz', hc'⟩ := fBody_tok (B := B) hd hB (fsOf x + clen done)
    (nrelT done) t hok σ ⟨hc, hp, hz, htok, by omega⟩
  refine ⟨σ', hrun, ⟨hc', done ++ [t], rest', by rw [hsplit]; simp, ?_, ?_, ?_⟩, ?_⟩
  · rw [hp', clen_append, clen_singleton]; omega
  · rw [hz', nrelT_append]; simp
  · rw [ho', ho, TrCtx.emit_append, TrCtx.emit_singleton, Nat.zero_add, List.append_assoc]
  · rw [hp', hp]; omega

/-- The cost of the second walk. -/
def Kfl (x : List ℕ) : ℕ := (1 + 3 + Kf x) * x.length + 1 + 3

theorem fLoop_spec (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (FI x φ out0) fLoop
      (fun _ σ' => FI x φ out0 σ' ∧ σ'.vars "ic_p" = x.length) (Kfl x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  refine Spec.post (Spec.while_count (FI x φ out0) (fun σ => x.length - σ.vars "ic_p") (Kf x)
    (fun σ h => by
      obtain ⟨hc, done, rest, hs, hp, _⟩ := h
      have := clen_le hd hs
      exact evalB_condLt_vars (by rw [hp]; omega) (by rw [hc.2.1]; omega))
    (fBody_spec hd hB out0) (fun _ h => h) (fun σ _ => ?_)) ?_
  · show (1 + 3 + Kf x) * (x.length - σ.vars "ic_p") + 1 + 3 ≤ Kfl x
    unfold Kfl
    have := Nat.mul_le_mul_left (1 + 3 + Kf x) (Nat.sub_le x.length (σ.vars "ic_p"))
    omega
  · rintro σ σ' - ⟨hI, hf⟩
    refine ⟨hI, ?_⟩
    have hle := le_of_condLt_false hf
    obtain ⟨hc, done, rest, hs, hp, -⟩ := hI
    have := clen_le hd hs
    rw [hc.2.1] at hle
    omega

theorem fI_end (hd : Dom x φ) {out0 : List ℕ} {σ : Env} (h : FI x φ out0 σ)
    (hp : σ.vars "ic_p" = x.length) : σ.out = out0 ++ ((Cx x φ).tr 0 φ).encode := by
  obtain ⟨-, done, rest, hs, hp', -, ho⟩ := h
  have hrest : rest = [] := by
    by_contra hne
    obtain ⟨t, rest', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := pos_split hd hs
    have h1 : clen (t :: rest') = t.code.length + clen rest' := by simp [clen]
    have := code_length_pos t
    omega
  subst hrest
  rw [List.append_nil] at hs
  rw [ho, TrCtx.encode_tr, hs]

theorem fOut_value (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x φ σ ∧ σ.out = out0) fOut
      (fun _ σ' => σ'.out = out0 ++ ((Cx x φ).tr 0 φ).encode) (10 + Kfl x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hfs := fs_le hd
  unfold fOut
  run_vcg [fLoop_spec hd hB out0]
  all_goals first
    | exact fI_end hd (‹FI x φ out0 _ ∧ _›).1 (‹FI x φ out0 _ ∧ _›).2
    | (simp only [Ctx, fsOf] at *; omega)
    | (refine ⟨?_, [], toks φ, rfl, ?_, ?_, ?_⟩ <;> simp_all [Ctx, Env.setVar, clen, TrCtx.emit])

/-- The scalars `fOut` assigns. -/
def fVars : List String := ["ic_p", "ic_z", "ic_t", "ic_i2", "ic_k", "ic_zz", "ic_l", "ic_P"]

theorem fOut_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) fOut
      (fun σ σ' => σ'.out = σ.out ++ ((Cx x φ).tr 0 φ).encode ∧ Keep fVars σ σ') (10 + Kfl x) := by
  intro σ hσ
  have h := Spec.keep (fOut_value hd hB σ.out) fVars
    (by intro y hy
        simp [fOut, fLoop, fBody, relOut, relTail, argLoop, argBody, pComp, eqOut, exOut, otherOut,
          bump, Com.wvars] at hy
        simp [fVars]; tauto)
    (by simp [fOut, fLoop, fBody, relOut, relTail, argLoop, argBody, pComp, eqOut, exOut,
          otherOut, bump, Com.warrs])
    (by simp [fOut, fLoop, fBody, relOut, relTail, argLoop, argBody, pComp, eqOut, exOut,
          otherOut, bump, Com.reads])
  exact h σ ⟨hσ, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgForm
