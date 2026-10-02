import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ

/-!
# The Loop over the Assignments, the Loop over the Variables

`decodeCom_spec`: the digits of `z` into `od`. `zLoop_spec`: the words of the clauses of every
assignment `z < n^r`. `tautLoop_spec`: the words of the clauses `Y_c ∨ ¬Y_c`, `c < n^s`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ

variable {D : Data} {x : List ℕ} {B : ℕ}

/-! ### The digits -/

set_option maxHeartbeats 1000000 in
theorem decStore_spec {n w j : ℕ} (hwB : w < B) (hnB : n < B) (hjB : j < B) :
    Spec B (fun σ => σ.vars "w_w" = w ∧ σ.vars "w_n" = n ∧ j < (σ.arrs "od").length)
      (.store "od" (.lit j) (.sub (V "w_w") (.mul (.div (V "w_w") (V "w_n")) (V "w_n"))))
      (fun σ σ' => σ'.arrs "od" = (σ.arrs "od").set j (w % n) ∧
        Frame [] ["od"] σ σ' ∧ σ'.out = σ.out) 12 := by
  have h1 : w / n ≤ w := Nat.div_le_self w n
  have h2 : w / n * n ≤ w := Nat.div_mul_le_self w n
  refine Spec.pre (P := fun σ => (σ.vars "w_w" = w ∧ σ.vars "w_n" = n ∧
      j < (σ.arrs "od").length) ∧ σ.vars "w_w" / σ.vars "w_n" ≤ σ.vars "w_w" ∧
      σ.vars "w_w" / σ.vars "w_n" * σ.vars "w_n" ≤ σ.vars "w_w") ?_ ?_
  · run_vcg
    have hw := ‹σ.vars "w_w" = w›
    have hn := ‹σ.vars "w_n" = n›
    refine ⟨by simp [Env.setArr, hw, hn, mod_eq_sub], ⟨fun y hy => rfl, fun b hb => ?_, rfl⟩, rfl⟩
    have : b ≠ "od" := fun e => hb (by simp [e])
    simp [Env.setArr, this]
  · rintro σ ⟨hw, hn, hj⟩
    exact ⟨⟨hw, hn, hj⟩, by rw [hw, hn]; exact h1, by rw [hw, hn]; exact h2⟩

set_option maxHeartbeats 1000000 in
theorem decDiv_spec {n w : ℕ} (hwB : w < B) (hnB : n < B) :
    Spec B (fun σ => σ.vars "w_w" = w ∧ σ.vars "w_n" = n)
      (.assign "w_w" (.div (V "w_w") (V "w_n")))
      (fun σ σ' => σ' = σ.setVar "w_w" (w / n)) 4 := by
  refine Spec.pre (P := fun σ => (σ.vars "w_w" = w ∧ σ.vars "w_n" = n) ∧
      σ.vars "w_w" / σ.vars "w_n" ≤ σ.vars "w_w") ?_ ?_
  · run_vcg
    rw [‹σ.vars "w_w" = w›, ‹σ.vars "w_n" = n›]
  · rintro σ ⟨hw, hn⟩
    exact ⟨⟨hw, hn⟩, Nat.div_le_self _ _⟩

theorem take_set_succ (l : List ℕ) {j : ℕ} (hj : j < l.length) (v : ℕ) :
    (l.set j v).take (j + 1) = l.take j ++ [v] := by
  rw [List.take_add_one, List.getElem?_set_self hj]
  simp [List.take_set_of_le (le_refl j)]

theorem decSteps_spec {n : ℕ} (hnB : n < B) : ∀ (c j w : ℕ), w < B → j + c < B →
    Spec B (fun σ => σ.vars "w_w" = w ∧ σ.vars "w_n" = n ∧ (σ.arrs "od").length = j + c)
      (decSteps j c)
      (fun σ σ' => σ'.arrs "od" = (σ.arrs "od").take j ++ digits n c w ∧
        Frame ["w_w"] ["od"] σ σ' ∧ σ'.out = σ.out) (20 * c + 1)
  | 0, j, w, _, _ => by
    refine (Spec.skip (B := B)).post fun σ σ' h e => ?_
    subst e
    exact ⟨by rw [List.take_of_length_le (by omega)]; simp [digits], Frame.refl _ _ _, rfl⟩
  | c + 1, j, w, hw, hj => by
    have h1 := decStore_spec (B := B) (n := n) (w := w) (j := j) hw hnB (by omega)
    have h1' : Spec B (fun σ => σ.vars "w_w" = w ∧ σ.vars "w_n" = n ∧
        (σ.arrs "od").length = j + (c + 1)) _ _ 12 :=
      h1.pre (by intro σ h; exact ⟨h.1, h.2.1, by omega⟩)
    have hd := decDiv_spec (B := B) (n := n) (w := w) hw hnB
    have h2 := decSteps_spec hnB c (j + 1) (w / n) (lt_of_le_of_lt (Nat.div_le_self w n) hw)
      (by omega)
    have hd' : Spec B (fun σ => σ.vars "w_w" = w ∧ σ.vars "w_n" = n ∧
        (σ.arrs "od").length = j + 1 + c) _ _ 4 := hd.pre (by intro σ h; exact ⟨h.1, h.2.1⟩)
    have h23' := Spec.seq' hd' h2 (by
      intro σ σ' hp hq
      subst hq
      exact ⟨by simp [Env.setVar], by simp [Env.setVar, hp.2.1], by simp [Env.setVar, hp.2.2]⟩)
    refine Spec.mono (Spec.seq h1' h23' ?_ ?_) (by omega)
    · intro σ σ' hp hq
      exact ⟨by rw [hq.2.1.1 _ (by simp)]; exact hp.1, by rw [hq.2.1.1 _ (by simp)]; exact hp.2.1,
        by rw [hq.1]; simp; omega⟩
    rintro σ σ' σ'' hp ⟨a1, f1, o1⟩ ⟨σm, rfl, ⟨a2, f2, o2⟩⟩
    refine ⟨?_, (f1.mono (by simp) (by simp)).trans ((Frame.setVar σ' (by simp) _).trans f2),
      by rw [o2]; simpa using o1⟩
    rw [a2]
    simp only [Env.setVar]
    rw [a1, take_set_succ _ (by omega)]
    simp [digits]

/-- **The digits of `z`** into `od`. -/
theorem decodeCom_spec (hB : BF D x B) {z : ℕ} (hz : z < nW D x ^ D.r) :
    Spec B (fun σ => Ctx D x σ ∧ σ.vars "w_z" = z) (decodeCom D.r)
      (fun σ σ' => σ'.arrs "od" = digits (nW D x) D.r z ∧ Frame ["w_w"] ["od"] σ σ' ∧
        σ'.out = σ.out) (20 * D.r + 4) := by
  have hzB := hB.npow_lt (e := D.r) (by omega)
  have hlen := hB.len
  have hrB : D.r < B := by have := hB.const; unfold cD at this; omega
  have hnB := hB.n
  have h1 : Spec B (fun σ => Ctx D x σ ∧ σ.vars "w_z" = z) (.assign "w_w" (V "w_z"))
      (fun σ σ' => σ' = σ.setVar "w_w" z) 2 := by
    refine (Spec.assign (f := fun _ => z) fun σ h => ?_)
    rw [← h.2]; exact evalB_var (by rw [h.2]; omega)
  have h2 := decSteps_spec (B := B) (n := nW D x) (by omega) D.r 0 z (by omega) (by omega)
  refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => by
      subst hq
      exact ⟨by simp [Env.setVar], by simp [Env.setVar, hp.1.n], by simp [hp.1.odlen]⟩) ?_)
    (by omega)
  rintro σ σ' σ'' - rfl ⟨a2, f2, o2⟩
  exact ⟨by rw [a2]; simp, (Frame.setVar σ (by simp) z).trans f2, by rw [o2]; rfl⟩

/-! ### Frames of the clauses -/

theorem wvars_codeCom : ∀ (js : List ℕ) (y : String), y ∈ (codeCom js).wvars → y = "w_c"
  | [], y, h => by simpa [codeCom, Com.wvars] using h
  | j :: js, y, h => by
    simp only [codeCom, Com.wvars, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact wvars_codeCom js y h
    · exact h

theorem warrs_codeCom : ∀ js : List ℕ, (codeCom js).warrs = []
  | [] => rfl
  | j :: js => by simp [codeCom, Com.warrs, warrs_codeCom js]

theorem wvars_clauseCom (C : List Lit) : ∀ y ∈ (clauseCom C).wvars, y ∈ zS := by
  intro y hy
  simp only [clauseCom, writeTaut0, Com.wvars, List.mem_append, List.mem_singleton,
    List.not_mem_nil, or_false, false_or] at hy
  rcases hy with rfl | hy | hy
  · simp [zS]
  · obtain ⟨c, hc, hyc⟩ := wvars_seqList _ y hy
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    simp only [nonXCom, Com.wvars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false] at hyc
    rcases hyc with h | h
    · have := (atom_frame l.atom).1 y h; simp only [zA, List.mem_cons] at this; simp [zS]; tauto
    · simp [zS, h]
  · obtain ⟨c, hc, hyc⟩ := wvars_seqList _ y hy
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    simp only [xLitCom, Com.wvars, List.mem_append, List.not_mem_nil, or_false] at hyc
    rw [wvars_codeCom _ y hyc]; simp [zS]

theorem warrs_clauseCom (C : List Lit) : (clauseCom C).warrs = [] := by
  have h1 : (seqList ((C.filter fun l => !isXLit l).map nonXCom)).warrs = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun b hb => ?_
    obtain ⟨c, hc, hbc⟩ := warrs_seqList _ b hb
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    have := (atom_frame l.atom).2.1 b
    simp [nonXCom, Com.warrs] at hbc; exact absurd (this hbc) (by simp)
  have h2 : (seqList ((C.filter isXLit).map xLitCom)).warrs = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun b hb => ?_
    obtain ⟨c, hc, hbc⟩ := warrs_seqList _ b hb
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    simp [xLitCom, Com.warrs, warrs_codeCom] at hbc
  simp [clauseCom, writeTaut0, Com.warrs, h1, h2]

theorem reads_clauseCom (C : List Lit) : ¬ (clauseCom C).reads := by
  have h1 : ¬ (seqList ((C.filter fun l => !isXLit l).map nonXCom)).reads := by
    refine reads_seqList _ fun c hc => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    simp [nonXCom, Com.reads, (atom_frame l.atom).2.2.1]
  have h2 : ¬ (seqList ((C.filter isXLit).map xLitCom)).reads := by
    refine reads_seqList _ fun c hc => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
    have : ∀ js, ¬ (codeCom js).reads := by
      intro js; induction js with
      | nil => simp [codeCom, Com.reads]
      | cons j js ih => simp [codeCom, Com.reads, ih]
    simp [xLitCom, Com.reads, this]
  simp [clauseCom, writeTaut0, Com.reads, h1, h2]

theorem wvars_clauses (Cs : List (List Lit)) :
    ∀ y ∈ (seqList (Cs.map clauseCom)).wvars, y ∈ zS := by
  intro y hy
  obtain ⟨c, hc, hyc⟩ := wvars_seqList _ y hy
  obtain ⟨C, -, rfl⟩ := List.mem_map.mp hc
  exact wvars_clauseCom C y hyc

theorem warrs_clauses (Cs : List (List Lit)) : (seqList (Cs.map clauseCom)).warrs = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun b hb => ?_
  obtain ⟨c, hc, hbc⟩ := warrs_seqList _ b hb
  obtain ⟨C, -, rfl⟩ := List.mem_map.mp hc
  simp [warrs_clauseCom] at hbc

/-! ### The loop over the assignments -/

theorem bump_spec (s : String) :
    Spec B (fun σ => σ.vars s + 1 < B) (bump s) (fun σ σ' => σ' = σ.setVar s (σ.vars s + 1)) 4 := by
  run_vcg
  all_goals rfl

/-- The clauses of the CNF are fit to be written. -/
def CnfOk (D : Data) (x : List ℕ) (B : ℕ) : Prop :=
  ∀ C ∈ D.cnf, (∀ l ∈ C, LitOk D x l) ∧ (C.filter isXLit).length < B

/-- The invariant of the loop over the assignments. -/
def ZI (D : Data) (x out0 : List ℕ) (σ : Env) : Prop :=
  Ctx D x σ ∧ σ.vars "w_PR" = nW D x ^ D.r ∧ σ.vars "w_z" ≤ nW D x ^ D.r ∧
    σ.out = out0 ++ (List.range (σ.vars "w_z")).flatMap (zWords D x)

/-- The cost of one assignment. -/
def Kz (D : Data) (x : List ℕ) : ℕ := 20 * D.r + 4 + Kcls x D.cnf + 4

theorem ctx_frame_od {σ σ' : Env} {S : List String} (h : Ctx D x σ) (hf : Frame S ["od"] σ σ')
    (hS : "w_n" ∉ S) (hod : (σ'.arrs "od").length = D.r) : Ctx D x σ' where
  a := by rw [hf.2.1 _ (by simp)]; exact h.a
  bo := by rw [hf.2.1 _ (by simp)]; exact h.bo
  U := by rw [hf.2.1 _ (by simp)]; exact h.U
  Ulen := by rw [hf.2.1 _ (by simp)]; exact h.Ulen
  odlen := hod
  n := by rw [hf.1 _ hS]; exact h.n

set_option maxHeartbeats 1000000 in
theorem zBody_spec (hB : BF D x B) (hg : Good x) (hC : CnfOk D x B) (out0 : List ℕ) :
    Spec B (fun σ => ZI D x out0 σ ∧ σ.vars "w_z" < nW D x ^ D.r) (zBody D)
      (fun σ σ' => ZI D x out0 σ' ∧ σ'.vars "w_z" = σ.vars "w_z" + 1) (Kz D x) := by
  intro σ ⟨⟨hc, hPR, hle, hout⟩, hlt⟩
  set z := σ.vars "w_z" with hz
  have hzB := hB.npow_lt (e := D.r) (by omega)
  obtain ⟨σ1, hr1, a1, f1, o1⟩ := decodeCom_spec hB hlt σ ⟨hc, rfl⟩
  have hc1 : Ctx D x σ1 := ctx_frame_od hc f1 (by simp) (by rw [a1]; simp)
  have hds : DsOk D x (digits (nW D x) D.r z) := by
    refine ⟨by simp, fun d hd => ?_⟩
    have hn : 0 < nW D x := by
      rcases Nat.eq_zero_or_pos D.r with h0 | h0
      · rw [h0] at hd; simp [digits] at hd
      · rcases Nat.eq_zero_or_pos (nW D x) with h | h
        · rw [h, zero_pow (by omega)] at hlt; omega
        · exact h
    exact digits_lt hn _ _ d hd
  obtain ⟨σ2, hr2, o2, f2⟩ := clausesCom_spec hB hg hds D.cnf hC σ1 ⟨hc1, a1⟩
  have hz2 : σ2.vars "w_z" = z := by
    rw [f2.1 _ (by simp [zS]), f1.1 _ (by simp)]
  obtain ⟨σ3, hr3, rfl⟩ := bump_spec (B := B) "w_z" σ2
    (by show σ2.vars "w_z" + 1 < B; rw [hz2]; omega)
  refine ⟨_, (hr1.seq (hr2.seq hr3)).mono (by unfold Kz; omega), ?_, by simp [Env.setVar, hz2, hz]⟩
  have hf : Frame ("w_w" :: "w_z" :: zS) ["od"] σ (σ2.setVar "w_z" (σ2.vars "w_z" + 1)) :=
    ((f1.mono (by simp) (by simp)).trans (f2.mono (by simp [zS]) (by simp))).trans
      (Frame.setVar _ (by simp) _)
  have hod3 : ((σ2.setVar "w_z" (σ2.vars "w_z" + 1)).arrs "od").length = D.r := by
    show (σ2.arrs "od").length = D.r
    rw [f2.2.1 _ (by simp), a1]; simp
  refine ⟨ctx_frame_od hc hf (by simp [zS]) hod3,
    by rw [hf.1 _ (by simp [zS])]; exact hPR, by simp [Env.setVar, hz2]; omega, ?_⟩
  simp only [Env.setVar, if_pos, hz2]
  show σ2.out = _
  rw [o2, o1, hout, List.range_succ, List.flatMap_append]
  simp [zWords]

theorem zLoop_spec (hB : BF D x B) (hg : Good x) (hC : CnfOk D x B) (out0 : List ℕ) :
    Spec B (fun σ => ZI D x out0 (σ.setVar "w_z" 0)) (zLoop D)
      (fun _ σ' => ZI D x out0 σ' ∧ σ'.vars "w_z" = nW D x ^ D.r)
      ((Kz D x + 4) * nW D x ^ D.r + 6) :=
  Spec.forRangeZero "w_z" "w_PR" (ZI D x out0) _ _ (hB.npow_lt (by omega))
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (zBody_spec hB hg hC out0)

/-! ### The loop over the variables -/

/-- The invariant of the loop over the variables. -/
def TaI (D : Data) (x out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "w_PS" = nW D x ^ D.s ∧ σ.vars "w_y" ≤ nW D x ^ D.s ∧
    σ.out = out0 ++ (List.range (σ.vars "w_y")).flatMap tautWords

set_option maxHeartbeats 1000000 in
theorem tautBody_spec (hB : BF D x B) (out0 : List ℕ) :
    Spec B (fun σ => TaI D x out0 σ ∧ σ.vars "w_y" < nW D x ^ D.s) tautBody
      (fun σ σ' => TaI D x out0 σ' ∧ σ'.vars "w_y" = σ.vars "w_y" + 1) 20 := by
  have hcnt := hB.count_lt.2
  have hlen := hB.len
  refine Spec.pre (P := fun σ => (TaI D x out0 σ ∧ σ.vars "w_y" < nW D x ^ D.s) ∧
      2 * σ.vars "w_y" + 1 < B) ?_ ?_
  · unfold tautBody
    run_vcg
    obtain ⟨h1, h2, h3⟩ := ‹TaI D x out0 σ›
    have h4 := ‹σ.vars "w_y" < nW D x ^ D.s›
    refine ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
    simp only [Env.setVar, if_pos]
    rw [h3, List.range_succ, List.flatMap_append]
    simp [tautWords]
  · rintro σ ⟨hI, hlt⟩
    exact ⟨⟨hI, hlt⟩, by omega⟩

theorem tautLoop_spec (hB : BF D x B) (out0 : List ℕ) :
    Spec B (fun σ => TaI D x out0 (σ.setVar "w_y" 0)) tautLoop
      (fun _ σ' => TaI D x out0 σ' ∧ σ'.vars "w_y" = nW D x ^ D.s)
      ((20 + 4) * nW D x ^ D.s + 6) :=
  Spec.forRangeZero "w_y" "w_PS" (TaI D x out0) _ _ (hB.npow_lt (by omega))
    (fun _ h => h.2.1) (fun _ h => h.1) (tautBody_spec hB out0)

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop
