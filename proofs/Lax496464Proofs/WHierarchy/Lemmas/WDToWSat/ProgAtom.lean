import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx

/-!
# The atoms: scanning a block, comparing positions

`relCom_spec`: `relCom i js` sets `w_f` to `1` exactly when the tuple of the elements at the
positions `js` is listed in the block of symbol `i` (`memW`); `eqCom`: the equation of two
positions. Both under the digits `ds` in `od`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx

variable {D : Data} {x : List ℕ} {B : ℕ}

/-- The element at position `j` read through the arrays. -/
theorem elem_read {σ : Env} (hc : Ctx D x σ) {ds : List ℕ} (hod : σ.arrs "od" = ds)
    (hds : DsOk D x ds) {j : ℕ} (hj : j < D.r) :
    (σ.arrs "U").getD ((σ.arrs "od").getD j 0) 0 = epsW D x ds j := by
  rw [hod, hc.U _ (hds.getD_lt hj)]; rfl

/-- The state of the scan of tuple `t` of block `i`. -/
def ScanPre (D : Data) (x ds : List ℕ) (i t : ℕ) (σ : Env) : Prop :=
  Ctx D x σ ∧ σ.arrs "od" = ds ∧ σ.vars "w_bs" = boW x i ∧ σ.vars "w_t" = t

set_option maxHeartbeats 2000000 in
theorem matchStep_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) {i t l q j : ℕ}
    (hpos : boW x i + 1 + t * l + q < x.length) (htl : t < x.length) (hj : j < D.r) (hl : l < B) :
    Spec B (ScanPre D x ds i t)
      (.ite (.eq (.get "a" (posE l q)) (elemE j)) .skip (.assign "w_mt" (.lit 0)))
      (fun σ σ' => σ'.vars "w_mt" =
          (if x.getD (boW x i + 1 + t * l + q) 0 = epsW D x ds j then σ.vars "w_mt" else 0) ∧
        Frame ["w_mt"] [] σ σ' ∧ σ'.out = σ.out) 20 := by
  have hlen := hB.len
  have hjB : j < B := by have := hB.const; unfold cD at this; omega
  have hodB := hds.getD_lt hj
  have hnB := hB.n
  refine Spec.pre (P := fun σ => ScanPre D x ds i t σ ∧
      σ.vars "w_bs" + 1 + σ.vars "w_t" * l + q < (σ.arrs "a").length ∧
      (σ.arrs "a").length < B ∧
      (σ.arrs "a").getD (σ.vars "w_bs" + 1 + σ.vars "w_t" * l + q) 0 =
        x.getD (boW x i + 1 + t * l + q) 0 ∧
      x.getD (boW x i + 1 + t * l + q) 0 < B ∧
      j < (σ.arrs "od").length ∧ (σ.arrs "od").getD j 0 < (σ.arrs "U").length ∧
      (σ.arrs "od").getD j 0 < B ∧
      (σ.arrs "U").getD ((σ.arrs "od").getD j 0) 0 = epsW D x ds j ∧
      epsW D x ds j < B ∧ σ.vars "w_t" < B) ?_ ?_
  · run_vcg
    · have hcase := ‹(σ.arrs "a").getD _ 0 = (σ.arrs "U").getD _ 0›
      rw [‹(σ.arrs "a").getD _ 0 = x.getD _ 0›, ‹(σ.arrs "U").getD _ 0 = epsW D x ds j›] at hcase
      exact ⟨by rw [if_pos hcase], Frame.refl _ _ _, rfl⟩
    · have hcase := ‹¬(σ.arrs "a").getD _ 0 = (σ.arrs "U").getD _ 0›
      rw [‹(σ.arrs "a").getD _ 0 = x.getD _ 0›, ‹(σ.arrs "U").getD _ 0 = epsW D x ds j›] at hcase
      exact ⟨by rw [if_neg hcase]; simp [Env.setVar], Frame.setVar σ (by simp) 0, rfl⟩
  · rintro σ ⟨hc, hod, hbs, ht⟩
    refine ⟨⟨hc, hod, hbs, ht⟩, by rw [hc.a, hbs, ht]; exact hpos, by rw [hc.a]; omega,
      by rw [hc.a, hbs, ht], hB.getD_lt _, by rw [hc.odlen]; exact hj,
      by rw [hod]; have := hc.Ulen; omega, by rw [hod]; omega, elem_read hc hod hds hj,
      U_getD_lt hB _, by rw [ht]; omega⟩

theorem ScanPre.frame {ds : List ℕ} {i t : ℕ} {σ σ' : Env} {S : List String}
    (h : ScanPre D x ds i t σ) (hf : Frame S [] σ σ') (hS : "w_n" ∉ S ∧ "w_bs" ∉ S ∧ "w_t" ∉ S) :
    ScanPre D x ds i t σ' :=
  ⟨h.1.frame hf hS.1 (by simp), by rw [hf.2.1 _ (by simp)]; exact h.2.1,
    by rw [hf.1 _ hS.2.1]; exact h.2.2.1, by rw [hf.1 _ hS.2.2]; exact h.2.2.2⟩

/-- The tuple `t` of the block at `bi` matches the elements at the positions `js`, from entry `q`. -/
def TupMatch (x : List ℕ) (bi t l q : ℕ) (ε : ℕ → ℕ) (js : List ℕ) : Prop :=
  ∀ q' < js.length, x.getD (bi + 1 + t * l + (q + q')) 0 = ε (js.getD q' 0)

instance (x : List ℕ) (bi t l q : ℕ) (ε : ℕ → ℕ) (js : List ℕ) :
    Decidable (TupMatch x bi t l q ε js) := by unfold TupMatch; infer_instance

theorem tupMatch_cons (x : List ℕ) (bi t l q : ℕ) (ε : ℕ → ℕ) (j : ℕ) (js : List ℕ) :
    TupMatch x bi t l q ε (j :: js) ↔
      x.getD (bi + 1 + t * l + q) 0 = ε j ∧ TupMatch x bi t l (q + 1) ε js := by
  unfold TupMatch
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), fun q' hq' => ?_⟩
    have := h (q' + 1) (by simp; omega)
    rw [show q + (q' + 1) = q + 1 + q' by omega] at this
    simpa using this
  · rintro ⟨h0, h⟩ q' hq'
    rcases q' with _ | q'
    · simpa using h0
    · have := h q' (by simpa using hq')
      rw [show q + 1 + q' = q + (q' + 1) by omega] at this
      simpa using this

theorem matchCom_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) {i t l : ℕ}
    (htl : t < x.length) (hl : l < B) : ∀ (js : List ℕ) (q : ℕ),
    (∀ q' < js.length, boW x i + 1 + t * l + (q + q') < x.length) → (∀ j ∈ js, j < D.r) →
    Spec B (ScanPre D x ds i t) (matchCom l js q)
      (fun σ σ' => σ'.vars "w_mt" =
          (if TupMatch x (boW x i) t l q (epsW D x ds) js then σ.vars "w_mt" else 0) ∧
        Frame ["w_mt"] [] σ σ' ∧ σ'.out = σ.out) (20 * js.length + 1)
  | [], q, _, _ => by
    refine (Spec.skip (P := ScanPre D x ds i t)).post fun σ σ' _ h => ?_
    subst h
    have hm : TupMatch x (boW x i) t l q (epsW D x ds) [] := fun q' hq' => absurd hq' (by simp)
    exact ⟨by rw [if_pos hm], Frame.refl _ _ _, rfl⟩
  | j :: js, q, hpos, hjs => by
    have h1 := matchStep_spec hB hds (i := i) (t := t) (l := l) (q := q) (j := j)
      (by simpa using hpos 0 (by simp)) htl (hjs j (by simp)) hl
    have h2 := matchCom_spec hB hds htl hl js (q + 1)
      (fun q' hq' => by
        have := hpos (q' + 1) (by simp; omega)
        rw [show q + (q' + 1) = q + 1 + q' by omega] at this; exact this)
      (fun j' hj' => hjs j' (by simp [hj']))
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' h hq => h.frame hq.2.1 (by simp)) ?_)
      (by simp; omega)
    rintro σ σ' σ'' - ⟨e1, f1, o1⟩ ⟨e2, f2, o2⟩
    refine ⟨?_, f1.trans f2, o2.trans o1⟩
    rw [e2, e1]
    have hc := tupMatch_cons x (boW x i) t l q (epsW D x ds) j js
    by_cases ha : x.getD (boW x i + 1 + t * l + q) 0 = epsW D x ds j
    · rw [if_pos ha]
      by_cases hb : TupMatch x (boW x i) t l (q + 1) (epsW D x ds) js
      · rw [if_pos hb, if_pos (hc.mpr ⟨ha, hb⟩)]
      · rw [if_neg hb, if_neg (fun h => hb (hc.mp h).2)]
    · rw [if_neg ha, if_neg (fun h => ha (hc.mp h).1)]; split_ifs <;> rfl

/-! ### One tuple, the scan -/

/-- The end of the body: record a match, next tuple. -/
def tupTail : Com :=
  .seq (.ite (.eq (V "w_mt") (.lit 1)) (.assign "w_f" (.lit 1)) .skip) (bump "w_t")

theorem tupBody_eq (js : List ℕ) :
    tupBody js = .seq (.assign "w_mt" (.lit 1)) (.seq (matchCom js.length js 0) tupTail) := rfl

theorem tupTail_spec {B : ℕ} :
    Spec B (fun τ => τ.vars "w_t" + 1 < B ∧ τ.vars "w_mt" < B ∧ 1 < B) tupTail
      (fun τ τ' => τ'.vars "w_f" = (if τ.vars "w_mt" = 1 then 1 else τ.vars "w_f") ∧
        τ'.vars "w_t" = τ.vars "w_t" + 1 ∧ Frame ["w_f", "w_t"] [] τ τ' ∧ τ'.out = τ.out) 12 := by
  unfold tupTail
  run_vcg
  · have h := ‹σ.vars "w_mt" = 1›
    refine ⟨by simp [Env.setVar, h], by simp [Env.setVar], ?_, rfl⟩
    exact (Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _)
  · have h := ‹¬σ.vars "w_mt" = 1›
    refine ⟨by simp [Env.setVar, h], by simp [Env.setVar], ?_, rfl⟩
    exact Frame.setVar σ (by simp) _

/-- The invariant of the scan of block `i` for the elements at the positions `js`. -/
def TI (D : Data) (x ds : List ℕ) (i : ℕ) (js : List ℕ) (σ : Env) : Prop :=
  Ctx D x σ ∧ σ.arrs "od" = ds ∧ σ.vars "w_bs" = boW x i ∧
    σ.vars "w_cnt" = x.getD (boW x i) 0 ∧ σ.vars "w_t" ≤ x.getD (boW x i) 0 ∧
    σ.vars "w_f" = if ∃ t < σ.vars "w_t", TupMatch x (boW x i) t js.length 0 (epsW D x ds) js
      then 1 else 0

instance (x : List ℕ) (bi n l : ℕ) (ε : ℕ → ℕ) (js : List ℕ) :
    Decidable (∃ t < n, TupMatch x bi t l 0 ε js) := by infer_instance

theorem exists_lt_succ_iff (P : ℕ → Prop) (n : ℕ) : (∃ t < n + 1, P t) ↔ (∃ t < n, P t) ∨ P n := by
  constructor
  · rintro ⟨t, ht, hp⟩
    rcases Nat.lt_or_ge t n with h | h
    · exact Or.inl ⟨t, h, hp⟩
    · right; rwa [show t = n by omega] at hp
  · rintro (⟨t, ht, hp⟩ | hp)
    · exact ⟨t, by omega, hp⟩
    · exact ⟨n, by omega, hp⟩

set_option maxHeartbeats 1000000 in
theorem tupBody_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) {i : ℕ}
    (hi : i < spW x) {js : List ℕ} (hjl : js.length = x.getD (1 + i) 0) (hjs : ∀ j ∈ js, j < D.r) :
    Spec B (fun σ => TI D x ds i js σ ∧ σ.vars "w_t" < x.getD (boW x i) 0) (tupBody js)
      (fun σ σ' => TI D x ds i js σ' ∧ σ'.vars "w_t" = σ.vars "w_t" + 1)
      (20 * js.length + 15) := by
  intro σ ⟨hI, hlt⟩
  obtain ⟨hc, hod, hbs, hcnt, hle, hf⟩ := hI
  set t := σ.vars "w_t" with ht
  have hcntx := hg.cnt i hi
  have hlen := hB.len
  have hlB : js.length < B := by rw [hjl]; exact hB.getD_lt _
  have hm := matchCom_spec hB hds (i := i) (t := t) (l := js.length) (by omega) hlB js 0
    (fun q' hq' => by
      have := pos_lt hg hi hlt (q := q') (by rw [← hjl]; exact hq')
      rw [hjl]; omega) hjs
  have hA : Spec B (fun τ => τ = σ) (.assign "w_mt" (.lit 1))
      (fun τ τ' => τ' = τ.setVar "w_mt" 1) (1 + (Expr.lit 1).size) :=
    Spec.assign (f := fun _ => 1) fun τ _ => evalB_lit (by omega)
  have hS1 : ScanPre D x ds i t (σ.setVar "w_mt" 1) :=
    ScanPre.frame ⟨hc, hod, hbs, rfl⟩ (Frame.setVar σ (S := ["w_mt"]) (by simp) 1) (by simp)
  obtain ⟨σ1, hr1, h1⟩ := hA σ rfl
  subst h1
  obtain ⟨σ2, hr2, e2, f2, o2⟩ := hm _ hS1
  have hmt2 : σ2.vars "w_mt" =
      if TupMatch x (boW x i) t js.length 0 (epsW D x ds) js then 1 else 0 := by
    rw [e2]; simp [Env.setVar]
  have ht2 : σ2.vars "w_t" = t := by rw [f2.1 _ (by simp)]; simp [Env.setVar, ht]
  obtain ⟨σ3, hr3, e3, t3, f3, o3⟩ := tupTail_spec (B := B) σ2
    ⟨by rw [ht2]; omega, by rw [hmt2]; split_ifs <;> omega, by omega⟩
  refine ⟨σ3, ?_, ?_, ?_⟩
  · rw [tupBody_eq]
    exact (hr1.seq (hr2.seq hr3)).mono (by simp only [Expr.size]; omega)
  · have hfr : Frame ["w_mt", "w_f", "w_t"] [] σ σ3 :=
      ((Frame.setVar σ (by simp) 1).trans (f2.mono (by simp) (by simp))).trans
        (f3.mono (by simp) (by simp))
    have hf2 : σ2.vars "w_f" = σ.vars "w_f" := by rw [f2.1 _ (by simp)]; simp [Env.setVar]
    refine ⟨hc.frame hfr (by simp) (by simp), by rw [hfr.2.1 _ (by simp)]; exact hod,
      by rw [hfr.1 _ (by simp)]; exact hbs, by rw [hfr.1 _ (by simp)]; exact hcnt,
      by rw [t3, ht2]; omega, ?_⟩
    rw [e3, t3, ht2, hmt2, hf2, hf]
    have hex := exists_lt_succ_iff (fun t' => TupMatch x (boW x i) t' js.length 0 (epsW D x ds) js) t
    by_cases hmat : TupMatch x (boW x i) t js.length 0 (epsW D x ds) js
    · rw [if_pos hmat, if_pos (hex.mpr (Or.inr hmat))]; rfl
    · rw [if_neg hmat]
      rw [if_neg (show ¬ (0 : ℕ) = 1 by omega)]
      by_cases hprev : ∃ t' < t, TupMatch x (boW x i) t' js.length 0 (epsW D x ds) js
      · rw [if_pos hprev, if_pos (hex.mpr (Or.inl hprev))]
      · rw [if_neg hprev, if_neg (fun h => (hex.mp h).elim hprev hmat)]
  · rw [t3, ht2]

theorem tupLoop_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) {i : ℕ}
    (hi : i < spW x) {js : List ℕ} (hjl : js.length = x.getD (1 + i) 0) (hjs : ∀ j ∈ js, j < D.r) :
    Spec B (fun σ => TI D x ds i js (σ.setVar "w_t" 0)) (tupLoop js)
      (fun _ σ' => TI D x ds i js σ' ∧ σ'.vars "w_t" = x.getD (boW x i) 0)
      ((20 * js.length + 15 + 4) * x.getD (boW x i) 0 + 6) := by
  have hcntx := hg.cnt i hi
  have hlen := hB.len
  exact Spec.forRangeZero "w_t" "w_cnt" (TI D x ds i js) _ _ (by omega)
    (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.2.1) (tupBody_spec hB hg hds hi hjl hjs)

/-- Membership through the scan. -/
theorem memW_iff_tup (x : List ℕ) (i : ℕ) (ε : ℕ → ℕ) (js : List ℕ) :
    memW x i (js.map ε) ↔
      ∃ t < x.getD (boW x i) 0, TupMatch x (boW x i) t js.length 0 ε js := by
  unfold memW TupMatch
  simp only [List.length_map, Nat.zero_add]
  refine exists_congr fun t => and_congr_right fun _ => forall₂_congr fun q hq => ?_
  have : (js.map ε).getD q 0 = ε (js.getD q 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rw [this]

/-- The cost of a relation atom. -/
def Krel (x : List ℕ) (js : List ℕ) : ℕ := (20 * js.length + 19) * x.length + 30

set_option maxHeartbeats 1000000 in
/-- **A relation atom.** -/
theorem relCom_value (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) {i : ℕ}
    (hi : i < spW x) {js : List ℕ} (hjl : js.length = x.getD (1 + i) 0) (hjs : ∀ j ∈ js, j < D.r) :
    Spec B (fun σ => Ctx D x σ ∧ σ.arrs "od" = ds) (relCom i js)
      (fun _ σ' => σ'.vars "w_f" = if memW x i (js.map (epsW D x ds)) then 1 else 0)
      (Krel x js) := by
  intro σ ⟨hc, hod⟩
  have hcntx := hg.cnt i hi
  have hlen := hB.len
  have hbo := boW_mono x (show i ≤ spW x by omega)
  have hbl := hg.blocks
  have hiB : i < B := by have := hg.head; omega
  have hbog : (σ.arrs "bo").getD i 0 = boW x i := by
    rw [hc.bo, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  have hbolen : i < (σ.arrs "bo").length := by rw [hc.bo]; simpa using hi
  have e1 : (Expr.get "bo" (.lit i)).evalB B σ = some (boW x i) := by
    have := RunStep.eval_get B σ "bo" (.lit i) i (RunStep.eval_lit B i σ hiB) hbolen
      (by rw [hbog]; omega)
    rwa [hbog] at this
  have hr1 := RunStep.assign B σ "w_bs" _ _ e1
  set σ1 := σ.setVar "w_bs" (boW x i) with hσ1
  have e2 : (Expr.get "a" (V "w_bs")).evalB B σ1 = some (x.getD (boW x i) 0) := by
    have ha1 : σ1.arrs "a" = x := by rw [hσ1]; simp [hc.a]
    have := RunStep.eval_get B σ1 "a" (V "w_bs") (boW x i)
      (RunStep.eval_var B σ1 "w_bs" (by simp [hσ1]; omega)) (by rw [ha1]; omega)
      (by rw [ha1]; exact hB.getD_lt _)
    simp only [hσ1, Env.setVar] at this ⊢
    simpa [hc.a] using this
  have hr2 := RunStep.assign B σ1 "w_cnt" _ _ e2
  set σ2 := σ1.setVar "w_cnt" (x.getD (boW x i) 0) with hσ2
  have hr3 := RunStep.assign B σ2 "w_f" (.lit 0) 0 (RunStep.eval_lit B 0 σ2 (by omega))
  set σ3 := σ2.setVar "w_f" 0 with hσ3
  have hfr : Frame ["w_bs", "w_cnt", "w_f", "w_t"] [] σ (σ3.setVar "w_t" 0) :=
    (((Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _)).trans
      (Frame.setVar _ (by simp) _)).trans (Frame.setVar _ (by simp) _)
  have hTI : TI D x ds i js (σ3.setVar "w_t" 0) := by
    refine ⟨hc.frame hfr (by simp) (by simp), by rw [hfr.2.1 _ (by simp)]; exact hod,
      by simp [hσ3, hσ2, hσ1, Env.setVar], by simp [hσ3, hσ2, hσ1, Env.setVar],
      by simp [Env.setVar], ?_⟩
    rw [if_neg (by simp [Env.setVar])]
    simp [hσ3, Env.setVar]
  obtain ⟨σ4, hr4, hI4, ht4⟩ := tupLoop_spec hB hg hds hi hjl hjs σ3 hTI
  refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq hr4))).mono ?_, ?_⟩
  · have h1 : x.getD (boW x i) 0 ≤ x.length := by omega
    have h2 : (20 * js.length + 15 + 4) * x.getD (boW x i) 0 ≤ (20 * js.length + 19) * x.length :=
      Nat.mul_le_mul_left _ h1
    simp only [Expr.size, Krel]; omega
  · show σ4.vars "w_f" = _
    rw [hI4.2.2.2.2.2, ht4]
    exact if_congr (memW_iff_tup x i _ js).symm rfl rfl

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom
