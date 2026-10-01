import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgSetup

/-! # The elements: `U := 0, …, L-1`, then the new entries of the word in `[L, N)`

`uCom_value`: the program fills the array `U` with the list `UW` of the elements the reduction works
with — first `0, …, L-1`, then every entry of the word in `[L, N)` not yet listed, found by a
membership scan (`memScan_spec`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop

variable {D : Data} {x : List ℕ} {B : ℕ}

/-- Every entry of the array is below the bound. -/
def UB (B : ℕ) (l : List ℕ) : Prop := ∀ q, l.getD q 0 < B

theorem UB.set {B : ℕ} {l : List ℕ} (h : UB B l) {v : ℕ} (hv : v < B) (i : ℕ) : UB B (l.set i v) := by
  intro q
  rw [List.getD_eq_getElem?_getD]
  by_cases hq : q = i
  · subst hq
    rcases Nat.lt_or_ge q l.length with h' | h'
    · rw [List.getElem?_set_self h']; exact hv
    · rw [List.getElem?_eq_none (by simpa using h')]; simpa using lt_of_le_of_lt (Nat.zero_le _) hv
  · rw [List.getElem?_set_ne (Ne.symm hq), ← List.getD_eq_getElem?_getD]; exact h q

/-! ### `0, …, L-1` -/

/-- The invariant of the first loop. -/
def F1 (D : Data) (x : List ℕ) (B cap : ℕ) (σ : Env) : Prop :=
  σ.vars "w_L" = LW D.s D.r x ∧ σ.vars "w_e" ≤ LW D.s D.r x ∧ (σ.arrs "U").length = cap ∧
    UB B (σ.arrs "U") ∧ ∀ q < σ.vars "w_e", (σ.arrs "U").getD q 0 = q

set_option maxHeartbeats 1000000 in
theorem fill1Body_spec (hB : BF D x B) {cap : ℕ} (hcap : LW D.s D.r x ≤ cap) :
    Spec B (fun σ => F1 D x B cap σ ∧ σ.vars "w_e" < LW D.s D.r x) fill1Body
      (fun σ σ' => F1 D x B cap σ' ∧ σ'.vars "w_e" = σ.vars "w_e" + 1) 10 := by
  have hc := hB.ucap
  refine Spec.pre (P := fun σ => (F1 D x B cap σ ∧ σ.vars "w_e" < LW D.s D.r x) ∧
      σ.vars "w_e" < (σ.arrs "U").length ∧ σ.vars "w_e" + 1 < B) ?_ ?_
  · unfold fill1Body
    run_vcg
    obtain ⟨hL, hle, hlen, hUB, hq⟩ := ‹F1 D x B cap σ›
    have hlt := ‹σ.vars "w_e" < LW D.s D.r x›
    refine ⟨⟨by simp [Env.setVar, Env.setArr, hL], by simp [Env.setVar, Env.setArr]; omega,
      by simp [Env.setVar, Env.setArr, hlen], ?_, ?_⟩, by simp [Env.setVar, Env.setArr]⟩
    · simp only [Env.setVar, Env.setArr, if_pos]
      exact hUB.set (by omega) _
    · intro q hq'
      simp only [Env.setVar, Env.setArr, ↓reduceIte] at hq' ⊢
      rw [List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_ge q (σ.vars "w_e") with h | h
      · rw [List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]; exact hq q h
      · have : q = σ.vars "w_e" := by omega
        subst this
        rw [List.getElem?_set_self (by omega)]; rfl
  · rintro σ ⟨⟨hL, hle, hlen, hUB, hq⟩, hlt⟩
    exact ⟨⟨⟨hL, hle, hlen, hUB, hq⟩, hlt⟩, by rw [hlen]; omega, by omega⟩

theorem fill1_spec (hB : BF D x B) {cap : ℕ} (hcap : LW D.s D.r x ≤ cap) :
    Spec B (fun σ => F1 D x B cap (σ.setVar "w_e" 0)) fill1
      (fun _ σ' => F1 D x B cap σ' ∧ σ'.vars "w_e" = LW D.s D.r x) ((10 + 4) * LW D.s D.r x + 6) := by
  have hc := hB.ucap
  exact Spec.forRangeZero "w_e" "w_L" (F1 D x B cap) _ _ (by omega) (fun _ h => h.2.1)
    (fun _ h => h.1) (fill1Body_spec hB hcap)

/-! ### The membership scan -/

/-- The invariant of the scan for `e` in the first `n` entries of `U0`. -/
def MI (e n : ℕ) (U0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "w_e" = e ∧ σ.vars "w_n" = n ∧ σ.arrs "U" = U0 ∧ σ.vars "w_q" ≤ n ∧
    σ.vars "w_f" = if ∃ q < σ.vars "w_q", U0.getD q 0 = e then 1 else 0

set_option maxHeartbeats 1000000 in
theorem memBody_spec {e n : ℕ} {U0 : List ℕ} (hn : n ≤ U0.length) (hU : UB B U0) (heB : e < B)
    (hnB : n < B) :
    Spec B (fun σ => MI e n U0 σ ∧ σ.vars "w_q" < n) memBody
      (fun σ σ' => MI e n U0 σ' ∧ σ'.vars "w_q" = σ.vars "w_q" + 1) 12 := by
  refine Spec.pre (P := fun σ => (MI e n U0 σ ∧ σ.vars "w_q" < n) ∧
      σ.vars "w_q" < (σ.arrs "U").length ∧ (σ.arrs "U").getD (σ.vars "w_q") 0 < B ∧
      σ.vars "w_e" < B ∧ σ.vars "w_q" + 1 < B) ?_ ?_
  · unfold memBody
    run_vcg
    all_goals
      obtain ⟨he, hn', hUe, hle, hf⟩ := ‹MI e n U0 σ›
      have hlt := ‹σ.vars "w_q" < n›
      have hex := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom.exists_lt_succ_iff
        (fun q => U0.getD q 0 = e) (σ.vars "w_q")
    · have hc := ‹(σ.arrs "U").getD (σ.vars "w_q") 0 = σ.vars "w_e"›
      rw [hUe, he] at hc
      refine ⟨⟨by simp [Env.setVar, he], by simp [Env.setVar, hn'], by simp [Env.setVar, hUe],
        by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [if_pos (hex.mpr (Or.inr hc))]
    · have hc := ‹¬(σ.arrs "U").getD (σ.vars "w_q") 0 = σ.vars "w_e"›
      rw [hUe, he] at hc
      refine ⟨⟨by simp [Env.setVar, he], by simp [Env.setVar, hn'], by simp [Env.setVar, hUe],
        by simp [Env.setVar]; omega, ?_⟩, by simp [Env.setVar]⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      rw [hf]
      by_cases hp : ∃ q < σ.vars "w_q", U0.getD q 0 = e
      · rw [if_pos hp, if_pos (hex.mpr (Or.inl hp))]
      · rw [if_neg hp, if_neg (fun h => (hex.mp h).elim hp hc)]
  · rintro σ ⟨⟨he, hn', hUe, hle, hf⟩, hlt⟩
    exact ⟨⟨⟨he, hn', hUe, hle, hf⟩, hlt⟩, by rw [hUe]; omega, by rw [hUe]; exact hU _,
      by rw [he]; exact heB, by omega⟩

/-- **The membership scan.** -/
theorem memScan_spec {e n : ℕ} {U0 : List ℕ} (hn : n ≤ U0.length) (hU : UB B U0) (heB : e < B)
    (hnB : n < B) :
    Spec B (fun σ => σ.vars "w_e" = e ∧ σ.vars "w_n" = n ∧ σ.arrs "U" = U0) memScan
      (fun σ σ' => σ'.vars "w_f" = (if ∃ q < n, U0.getD q 0 = e then 1 else 0) ∧
        Frame ["w_f", "w_q"] [] σ σ' ∧ σ'.out = σ.out) (16 * n + 10) := by
  have hloop := Spec.forRangeZero "w_q" "w_n" (MI e n U0) n 12 hnB (fun _ h => h.2.2.2.1)
    (fun _ h => h.2.1) (memBody_spec hn hU heB hnB)
  have h1 : Spec B (fun σ => σ.vars "w_e" = e ∧ σ.vars "w_n" = n ∧ σ.arrs "U" = U0)
      (.assign "w_f" (.lit 0)) (fun σ σ' => σ' = σ.setVar "w_f" 0) 2 :=
    Spec.assign (f := fun _ => 0) fun σ _ => evalB_lit (by omega)
  have hval : Spec B (fun σ => σ.vars "w_e" = e ∧ σ.vars "w_n" = n ∧ σ.arrs "U" = U0) memScan
      (fun _ σ' => σ'.vars "w_f" = if ∃ q < n, U0.getD q 0 = e then 1 else 0) (16 * n + 10) := by
    refine Spec.mono (Spec.seq h1 hloop (fun σ σ' hp hq => by
      subst hq
      refine ⟨by simp [Env.setVar, hp.1], by simp [Env.setVar, hp.2.1], by simp [Env.setVar, hp.2.2],
        by simp [Env.setVar], ?_⟩
      simp [Env.setVar]) ?_) (by omega)
    rintro σ σ' σ'' - - ⟨⟨-, -, -, -, hf⟩, hq⟩
    rw [hf, hq]
  exact Spec.framedOut hval _ _ (by simp [memScan, memLoop, memBody, Com.wvars])
    (by simp [memScan, memLoop, memBody, Com.warrs]) (by simp [memScan, memLoop, memBody, Com.reads])
    (by simp [memScan, memLoop, memBody, Com.NoWrite])

/-! ### Appending the new entries -/

/-- The first `n` entries of `U` are the list `l`, `n` its length. -/
def UAgree (σ : Env) (l : List ℕ) : Prop :=
  σ.vars "w_n" = l.length ∧ ∀ q < l.length, (σ.arrs "U").getD q 0 = l.getD q 0

set_option maxHeartbeats 1000000 in
theorem pushTail_spec {n e : ℕ} :
    Spec B (fun σ => σ.vars "w_n" = n ∧ σ.vars "w_e" = e ∧ n < (σ.arrs "U").length ∧ n + 1 < B ∧
        e < B)
      (.seq (.store "U" (V "w_n") (V "w_e")) (bump "w_n"))
      (fun σ σ' => σ'.arrs "U" = (σ.arrs "U").set n e ∧ σ'.vars "w_n" = n + 1 ∧
        Frame ["w_n"] ["U"] σ σ' ∧ σ'.out = σ.out) 10 := by
  run_vcg
  have hn := ‹σ.vars "w_n" = n›
  have he := ‹σ.vars "w_e" = e›
  refine ⟨by simp [Env.setVar, Env.setArr, hn, he], by simp [Env.setVar, Env.setArr, hn],
    ⟨fun y hy => ?_, fun b hb => ?_, rfl⟩, rfl⟩
  · have : y ≠ "w_n" := fun h => hy (by simp [h])
    simp [Env.setVar, Env.setArr, this]
  · have : b ≠ "U" := fun h => hb (by simp [h])
    simp [Env.setVar, Env.setArr, this]

theorem uagree_iff_mem {σ : Env} {l : List ℕ} (h : UAgree σ l) (e : ℕ) :
    (∃ q < l.length, (σ.arrs "U").getD q 0 = e) ↔ e ∈ l := by
  constructor
  · rintro ⟨q, hq, he⟩
    rw [h.2 q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq] at he
    rw [← he]; exact List.getElem_mem hq
  · intro hm
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
    exact ⟨q, hq, by rw [h.2 q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl⟩

/-- The middle of the body of the second loop. -/
def midCom : Com := .ite (.lt (V "w_e") (V "w_L")) .skip (.ite (.lt (V "w_e") (V "w_N")) pushNew .skip)

set_option maxHeartbeats 2000000 in
theorem midCom_spec {L N e cap : ℕ} {acc : List ℕ} (hLN : L ≤ N) (hNB : N < B) (hcapB : cap + 1 < B)
    (hacc : acc.length < cap) :
    Spec B (fun σ => σ.vars "w_e" = e ∧ σ.vars "w_L" = L ∧ σ.vars "w_N" = N ∧ UAgree σ acc ∧
        (σ.arrs "U").length = cap ∧ UB B (σ.arrs "U") ∧ e < B) midCom
      (fun σ σ' => UAgree σ' (pushStep L N acc e) ∧ (σ'.arrs "U").length = cap ∧
        UB B (σ'.arrs "U") ∧ Frame ["w_f", "w_q", "w_n"] ["U"] σ σ' ∧ σ'.out = σ.out)
      (16 * cap + 50) := by
  intro σ ⟨he, hL, hN, hag, hlen, hUB, heB⟩
  have ev_e : (Expr.var "w_e").evalB B σ = some e := by rw [← he]; exact evalB_var (by rw [he]; exact heB)
  have ev_L : (Expr.var "w_L").evalB B σ = some L := by rw [← hL]; exact evalB_var (by rw [hL]; omega)
  have ev_N : (Expr.var "w_N").evalB B σ = some N := by rw [← hN]; exact evalB_var (by rw [hN]; exact hNB)
  by_cases h1 : e < L
  · have hps : pushStep L N acc e = acc := by unfold pushStep; rw [if_neg (by omega)]
    refine ⟨σ, (RunStep.ite_true B _ _ _ σ σ 1 (RunStep.cond_lt_true B σ _ _ _ _ ev_e ev_L h1)
      (RunStep.skip B σ)).mono (by simp), by rw [hps]; exact hag, hlen, hUB,
      Frame.refl _ _ _, rfl⟩
  · by_cases h2 : e < N
    · have hn := hag.1
      obtain ⟨σ1, hr1, e1, f1, o1⟩ := memScan_spec (B := B) (e := e) (n := acc.length)
        (U0 := σ.arrs "U") (by omega) hUB heB (by omega) σ ⟨he, hn, rfl⟩
      have hmem := uagree_iff_mem hag e
      have ev_f : (Expr.var "w_f").evalB B σ1 = some (σ1.vars "w_f") :=
        evalB_var (by rw [e1]; split_ifs <;> omega)
      have ev_0 : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
      have hU1 : σ1.arrs "U" = σ.arrs "U" := f1.2.1 _ (by simp)
      have hn1 : σ1.vars "w_n" = acc.length := by rw [f1.1 _ (by simp)]; exact hn
      have he1 : σ1.vars "w_e" = e := by rw [f1.1 _ (by simp)]; exact he
      by_cases h3 : e ∈ acc
      · have hps : pushStep L N acc e = acc := by unfold pushStep; rw [if_neg (by tauto)]
        have hf1 : σ1.vars "w_f" = 1 := by rw [e1, if_pos (hmem.mpr h3)]
        refine ⟨σ1, (RunStep.ite_false B _ _ _ σ σ1 _
          (RunStep.cond_lt_false B σ _ _ _ _ ev_e ev_L h1)
          (RunStep.ite_true B _ _ _ σ σ1 _ (RunStep.cond_lt_true B σ _ _ _ _ ev_e ev_N h2)
            ((RunStep.seq B _ _ σ σ1 σ1 _ _ hr1 (RunStep.ite_false B _ _ _ σ1 σ1 1
              (RunStep.cond_eq_false B σ1 _ _ _ _ ev_f ev_0 (by omega)) (RunStep.skip B σ1)))))).mono
          (by simp; omega), ?_, by rw [hU1]; exact hlen, by rw [hU1]; exact hUB,
          f1.mono (by simp) (by simp), o1⟩
        rw [hps]; exact ⟨hn1, fun q hq => by rw [hU1]; exact hag.2 q hq⟩
      · have hps : pushStep L N acc e = acc ++ [e] := by
          unfold pushStep; rw [if_pos ⟨by omega, h2, h3⟩]
        have hf1 : σ1.vars "w_f" = 0 := by rw [e1, if_neg (fun h => h3 (hmem.mp h))]
        obtain ⟨σ2, hr2, a2, n2, f2, o2⟩ := pushTail_spec (B := B) (n := acc.length) (e := e) σ1
          ⟨hn1, he1, by rw [hU1, hlen]; exact hacc, by omega, heB⟩
        refine ⟨σ2, (RunStep.ite_false B _ _ _ σ σ2 _
          (RunStep.cond_lt_false B σ _ _ _ _ ev_e ev_L h1)
          (RunStep.ite_true B _ _ _ σ σ2 _ (RunStep.cond_lt_true B σ _ _ _ _ ev_e ev_N h2)
            ((RunStep.seq B _ _ σ σ1 σ2 _ _ hr1 (RunStep.ite_true B _ _ _ σ1 σ2 _
              (RunStep.cond_eq_true B σ1 _ _ _ _ ev_f ev_0 hf1) hr2))))).mono
          (by simp; omega), ?_, by rw [a2, List.length_set, hU1, hlen], ?_,
          (f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp)), by rw [o2, o1]⟩
        · rw [hps]
          refine ⟨by rw [n2]; simp, fun q hq => ?_⟩
          rw [a2, hU1]
          simp only [List.length_append, List.length_singleton] at hq
          rcases Nat.lt_or_ge q acc.length with h | h
          · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
              ← List.getD_eq_getElem?_getD, hag.2 q h]
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
          · have : q = acc.length := by omega
            subst this
            rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
            simp
        · rw [a2, hU1]; exact hUB.set heB _
    · have hps : pushStep L N acc e = acc := by unfold pushStep; rw [if_neg (by omega)]
      refine ⟨σ, (RunStep.ite_false B _ _ _ σ σ _ (RunStep.cond_lt_false B σ _ _ _ _ ev_e ev_L h1)
        (RunStep.ite_false B _ _ _ σ σ 1 (RunStep.cond_lt_false B σ _ _ _ _ ev_e ev_N h2)
          (RunStep.skip B σ))).mono (by simp), by rw [hps]; exact hag, hlen, hUB,
        Frame.refl _ _ _, rfl⟩

/-! ### The second loop -/

/-- The elements collected from the first `p` entries of the word. -/
def accW (D : Data) (x : List ℕ) (p : ℕ) : List ℕ :=
  (x.take p).foldl (pushStep (LW D.s D.r x) (NW x)) (List.range (LW D.s D.r x))

theorem length_accW (D : Data) (x : List ℕ) (p : ℕ) :
    (accW D x p).length ≤ LW D.s D.r x + p := by
  have := length_foldl_push (L := LW D.s D.r x) (N := NW x) (x.take p) (List.range (LW D.s D.r x))
  have h2 : (x.take p).length ≤ p := by simp
  unfold accW; simp only [List.length_range] at this; omega

theorem accW_full (D : Data) (x : List ℕ) : accW D x x.length = U D x := by
  unfold accW U UW; rw [List.take_length]

/-- The capacity of `U`. -/
abbrev capW (D : Data) (x : List ℕ) : ℕ := LW D.s D.r x + x.length

/-- The invariant of the second loop. -/
def F2 (D : Data) (x : List ℕ) (B : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "w_L" = LW D.s D.r x ∧ σ.vars "w_N" = NW x ∧
    σ.vars "w_p" ≤ x.length ∧ (σ.arrs "U").length = capW D x ∧ UB B (σ.arrs "U") ∧
    UAgree σ (accW D x (σ.vars "w_p"))

set_option maxHeartbeats 2000000 in
theorem fill2Body_spec (hB : BF D x B) :
    Spec B (fun σ => F2 D x B σ ∧ σ.vars "w_p" < x.length) fill2Body
      (fun σ σ' => F2 D x B σ' ∧ σ'.vars "w_p" = σ.vars "w_p" + 1) (16 * capW D x + 70) := by
  intro σ ⟨⟨ha, hn, hL, hN, hle, hlen, hUB, hag⟩, hlt⟩
  set p := σ.vars "w_p" with hp
  have hc := hB.ucap
  have hLN := LW_le D.s D.r x
  have hNB : NW x < B := hB.getD_lt _
  have hacc := length_accW D x p
  have hev : (Expr.get "a" (V "w_p")).evalB B σ = some (x.getD p 0) := by
    have := RunStep.eval_get B σ "a" (V "w_p") p (RunStep.eval_var B σ "w_p" (by omega))
      (by rw [ha]; omega) (by rw [ha]; exact hB.getD_lt _)
    rwa [ha] at this
  have hr1 := RunStep.assign B σ "w_e" _ _ hev
  set σ1 := σ.setVar "w_e" (x.getD p 0) with hσ1
  have hag1 : UAgree σ1 (accW D x p) := ⟨by simp [hσ1, Env.setVar, hag.1], fun q hq => by
    simp only [hσ1, Env.setVar]; exact hag.2 q hq⟩
  obtain ⟨σ2, hr2, ag2, len2, UB2, f2, o2⟩ := midCom_spec (B := B) (L := LW D.s D.r x) (N := NW x)
    (e := x.getD p 0) (cap := capW D x) (acc := accW D x p) hLN hNB (by show LW D.s D.r x + x.length + 1 < B; omega)
    (by show _ < LW D.s D.r x + x.length; omega) σ1
    ⟨by simp [hσ1, Env.setVar], by simp [hσ1, Env.setVar, hL], by simp [hσ1, Env.setVar, hN],
      hag1, by simp [hσ1, Env.setVar, hlen], by simp only [hσ1, Env.setVar]; exact hUB,
      hB.getD_lt _⟩
  have hp2 : σ2.vars "w_p" = p := by rw [f2.1 _ (by simp)]; simp [hσ1, Env.setVar, hp]
  obtain ⟨σ3, hr3, rfl⟩ := bump_spec (B := B) "w_p" σ2 (by show σ2.vars "w_p" + 1 < B; rw [hp2]; omega)
  refine ⟨_, (hr1.seq (hr2.seq hr3)).mono (by simp; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show σ2.arrs "a" = x; rw [f2.2.1 _ (by simp)]; simp [hσ1, Env.setVar, ha]
  · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    rw [f2.1 _ (by simp)]; simp [hσ1, Env.setVar, hn]
  · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    rw [f2.1 _ (by simp)]; simp [hσ1, Env.setVar, hL]
  · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
    rw [f2.1 _ (by simp)]; simp [hσ1, Env.setVar, hN]
  · simp [Env.setVar, hp2]; omega
  · exact len2
  · exact UB2
  · have hstep : accW D x (p + 1) = pushStep (LW D.s D.r x) (NW x) (accW D x p) (x.getD p 0) := by
      unfold accW; exact foldl_push_take x _ p hlt
    have hpp : (σ2.setVar "w_p" (σ2.vars "w_p" + 1)).vars "w_p" = p + 1 := by
      simp [Env.setVar, hp2]
    rw [hpp, hstep]
    exact ⟨by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; exact ag2.1,
      fun q hq => by simp only [Env.setVar]; exact ag2.2 q hq⟩
  · simp [Env.setVar, hp2, hp]

theorem fill2_spec (hB : BF D x B) :
    Spec B (fun σ => F2 D x B (σ.setVar "w_p" 0)) fill2
      (fun _ σ' => F2 D x B σ' ∧ σ'.vars "w_p" = x.length)
      ((16 * capW D x + 70 + 4) * x.length + 6) := by
  have hc := hB.ucap
  exact Spec.forRangeZero "w_p" "rt_n" (F2 D x B) _ _ (by omega) (fun _ h => h.2.2.2.2.1)
    (fun _ h => h.2.1) (fill2Body_spec hB)

set_option maxHeartbeats 2000000 in
/-- **The elements.** -/
theorem uCom_value (hB : BF D x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "w_L" = LW D.s D.r x ∧
        σ.vars "w_N" = NW x ∧ σ.arrs "U" = List.replicate (capW D x) 0) uCom
      (fun _ σ' => (∀ q < nW D x, (σ'.arrs "U").getD q 0 = (U D x).getD q 0) ∧
        nW D x ≤ (σ'.arrs "U").length ∧ σ'.vars "w_n" = nW D x)
      ((10 + 4) * LW D.s D.r x + 6 + 3 + ((16 * capW D x + 70 + 4) * x.length + 6)) := by
  intro σ ⟨ha, hn, hL, hN, hU⟩
  have hc := hB.ucap
  have h1 := Spec.framedOut (fill1_spec hB (cap := capW D x) (by simp)) ["w_e"] ["U"]
    (by simp [fill1, fill1Body, Com.wvars]) (by simp [fill1, fill1Body, Com.warrs])
    (by simp [fill1, fill1Body, Com.reads]) (by simp [fill1, fill1Body, Com.NoWrite])
  obtain ⟨σ1, hr1, ⟨⟨hL1, -, hlen1, hUB1, hq1⟩, he1⟩, f1, -⟩ := h1 σ
    ⟨by simp [Env.setVar, hL], by simp [Env.setVar], by simp [Env.setVar, hU],
      fun q => by
        show (σ.arrs "U").getD q 0 < B
        rw [hU]; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> simp <;> omega,
      fun q hq => by simp [Env.setVar] at hq⟩
  have ev : (Expr.var "w_L").evalB B σ1 = some (LW D.s D.r x) := by
    rw [← hL1]; exact evalB_var (by rw [hL1]; omega)
  have hr2 := RunStep.assign B σ1 "w_n" (V "w_L") _ ev
  set σ2 := σ1.setVar "w_n" (LW D.s D.r x) with hσ2
  have hF2 : F2 D x B (σ2.setVar "w_p" 0) := by
    refine ⟨?_, ?_, ?_, ?_, by simp [Env.setVar], by simp [hσ2, Env.setVar, hlen1],
      by simp only [hσ2, Env.setVar]; exact hUB1, ?_, ?_⟩
    · simp [hσ2, Env.setVar]; rw [f1.2.1 _ (by simp)]; exact ha
    · simp [hσ2, Env.setVar]; rw [f1.1 _ (by simp)]; exact hn
    · simp [hσ2, Env.setVar, hL1]
    · simp [hσ2, Env.setVar]; rw [f1.1 _ (by simp)]; exact hN
    · simp [hσ2, Env.setVar, accW]
    · intro q hq
      simp only [hσ2, Env.setVar, ↓reduceIte, accW, List.take_zero,
        List.foldl_nil, List.length_range] at hq ⊢
      rw [hq1 q (by rw [he1]; exact hq)]
      simp [List.getD_eq_getElem?_getD, hq]
  obtain ⟨σ3, hr3, ⟨_, _, _, _, _, hlen3, _, ag3⟩, hp3⟩ := fill2_spec hB σ2 hF2
  rw [hp3, accW_full] at ag3
  refine ⟨σ3, (hr1.seq (hr2.seq hr3)).mono (by simp; omega), fun q hq => ag3.2 q hq, ?_, ag3.1⟩
  rw [hlen3]
  have := length_UW_le D.s D.r x
  exact this

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill
