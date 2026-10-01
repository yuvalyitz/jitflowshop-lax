import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax

/-! # The translation is correct

For data `D` that list the tuples of a structure `A` (`Compat A D`), a positive `Σ_1`-formula `φ`
holds in `A` exactly when its translation `phiOf D F φ` — the translation with the fresh variables
bound in front — holds in the incidence structure (`models_iff`).

* **Forward** (`fwd`): each true atom `R_i ys` gets for its fresh variable the new element of the
  tuple `ys`; the fresh variables of false atoms keep their values.
* **Backward** (`bwd`): an assignment satisfying the translation, with the new elements sent to `0`,
  satisfies the formula: `E_l y z` forces `y` to be an entry of the tuple of `z`, hence an old
  element, and a positive formula keeps its equations when the same map is applied to both sides. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax

/-- The data list the tuples of `A`. -/
structure Compat (A : Structure) (D : IncData) : Prop where
  s_eq : D.s = A.arities.length
  N_eq : D.N = A.size
  ar_eq : ∀ i < D.s, D.ar i = A.arities.getD i 0
  list : ∀ i < D.s, (D.listOf i).Nodup ∧ (D.listOf i).toFinset = A.rel i

variable {A : Structure} {D : IncData}

theorem Compat.valid (hc : Compat A D) : D.Valid := by
  intro i hi j hj l hl
  have hm : (List.range (D.ar i)).map (D.ent i j) ∈ A.rel i := by
    rw [← (hc.list i hi).2, List.mem_toFinset]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have := (A.wf i _ hm).2.2 (D.ent i j l) (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
  rw [hc.N_eq]; exact this

theorem Compat.T_eq_zero (hc : Compat A D) (hN : D.N = 0) : D.T = 0 := by
  have hcnt : ∀ i < D.s, D.cnt i = 0 := by
    intro i hi
    have hnil : D.listOf i = [] := by
      rcases h : D.listOf i with _ | ⟨t, ts⟩
      · rfl
      · exfalso
        have hm : t ∈ A.rel i := by rw [← (hc.list i hi).2, h]; simp
        have hlen := (A.wf i t hm).2.1
        have hi' : i < A.arities.length := by rw [← hc.s_eq]; exact hi
        have hmem : A.arities.getD i 0 ∈ A.arities := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem hi'
        have := A.arity_pos _ hmem
        obtain ⟨a, as, rfl⟩ := List.exists_cons_of_length_pos (show 0 < t.length by omega)
        have := (A.wf i _ hm).2.2 a (by simp)
        rw [← hc.N_eq, hN] at this; omega
    have := congrArg List.length hnil
    simpa [IncData.listOf] using this
  unfold IncData.T IncData.po
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact hcnt i (List.mem_range.mp hi)

/-- New elements go to `0`. -/
def normA (N : ℕ) (ρ : Assignment) : Assignment := fun v => if ρ v < N then ρ v else 0

theorem normA_lt {N : ℕ} (hN : 0 < N) (ρ : Assignment) (v : ℕ) : normA N ρ v < N := by
  unfold normA; split_ifs with h
  · exact h
  · exact hN

/-! ### Forward -/

/-- **Forward**: a satisfying assignment into the old universe extends, on the fresh variables,
to one satisfying the translation. -/
theorem fwd (hc : Compat A D) (F : ℕ) : ∀ (ψ : Formula) (c : ℕ) (ρ : Assignment),
    ψ.IsQF → ψ.IsPositive → ψ.Fits A.arities 0 → RelLe D.r ψ → VarsLt F ψ →
    (∀ v ∈ ψ.freeVars, ρ v < A.size) →
    (∀ v, F + c ≤ v → v < F + c + nrel ψ → ρ v < D.size) →
    Sat A ∅ ψ ρ →
    ∃ ρ' : Assignment, (∀ v, (v < F + c ∨ F + c + nrel ψ ≤ v) → ρ' v = ρ v) ∧
      (∀ v, F + c ≤ v → v < F + c + nrel ψ → ρ' v < D.size) ∧
      Sat D.toStructure ∅ ((ctxOf D F).tr c ψ) ρ'
  | .rel i ys, c, ρ, _, _, hf, hr, hF, _, _, hs => by
    obtain ⟨hi, hl⟩ := hf
    have hr' : ys.length ≤ D.r := hr
    have hi' : i < D.s := by rw [hc.s_eq]; exact hi
    have hl' : ys.length = D.ar i := by rw [hc.ar_eq i hi']; exact hl
    have hmem : ys.map ρ ∈ D.listOf i := by
      rw [← List.mem_toFinset, (hc.list i hi').2]; exact hs
    obtain ⟨j, hj, hjt⟩ := List.mem_map.mp hmem
    have hj' : j < D.cnt i := List.mem_range.mp hj
    have hlt := D.po_add_lt_T hi' hj'
    refine ⟨ρ.update (F + c) (D.N + D.po i + j), fun v hv => ?_, fun v h1 h2 => ?_, ?_⟩
    · rw [update_ne]; simp only [nrel_rel] at hv; omega
    · simp only [nrel_rel] at h2
      rw [show v = F + c by omega, update_same]; unfold IncData.size; omega
    · have hp : (ctxOf D F).pIdx i ys.length = i := by
        unfold TrCtx.pIdx; exact if_pos ⟨hi', hl'⟩
      simp only [TrCtx.tr, TrCtx.relTr, hp, sat_relAux]
      have hz : (ctxOf D F).F + c = F + c := rfl
      rw [hz, update_same]
      refine ⟨fun m hm => ?_, (D.mem_rel_P hc.valid hi').mpr ⟨j, hj', rfl⟩⟩
      have hym : ys.getD m 0 < F := hF _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; exact List.getElem_mem hm)
      rw [update_ne _ _ (by omega)]
      have hcs : (ctxOf D F).s + (0 + m) = D.s + m := by simp [ctxOf]
      rw [hcs, D.mem_rel_E hc.valid]
      refine ⟨by omega, i, hi', by omega, j, hj', ?_⟩
      have e1 : (ys.map ρ).getD m 0 = ρ (ys.getD m 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; rfl
      have e2 : ((List.range (D.ar i)).map (D.ent i j)).getD m 0 = D.ent i j m := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
      rw [← e1, ← hjt, e2]
  | .setVar ys, _, _, _, _, _, _, _, _, _, hs => by simp [Sat] at hs
  | .eq x y, c, ρ, _, _, _, _, _, _, _, hs => ⟨ρ, fun _ _ => rfl, fun v h1 h2 => by
      simp at h2; omega, hs⟩
  | .neg _, _, _, _, hp, _, _, _, _, _, _ => hp.elim
  | .and φ ψ, c, ρ, hq, hp, hf, hr, hF, hfv, hz, hs => by
    have hv : ∀ v ∈ φ.freeVars, ρ v < A.size := fun v h => hfv v (by simp [Formula.freeVars, h])
    obtain ⟨ρ1, h1a, h1b, h1c⟩ := fwd hc F φ c ρ hq.1 hp.1 hf.1 hr.1 hF.1 hv
      (fun v h1 h2 => hz v h1 (by simp; omega)) hs.1
    have hlt2 : ∀ v ∈ ψ.freeVars, v < F := fun v h => lt_of_mem_freeVars hF.2 h
    obtain ⟨ρ2, h2a, h2b, h2c⟩ := fwd hc F ψ (c + nrel φ) ρ1 hq.2 hp.2 hf.2 hr.2 hF.2
      (fun v h => by
        rw [h1a v (Or.inl (by have := hlt2 v h; omega))]
        exact hfv v (by simp [Formula.freeVars, h]))
      (fun v h1 h2 => by
        rw [h1a v (Or.inr (by omega))]; exact hz v (by omega) (by simp; omega))
      ((sat_congr A ∅ ψ fun v h => (h1a v (Or.inl (by have := hlt2 v h; omega))).symm).mp hs.2)
    refine ⟨ρ2, fun v h => ?_, fun v h1 h2 => ?_, ?_, h2c⟩
    · simp only [nrel_and] at h
      rw [h2a v (by omega), h1a v (by omega)]
    · simp only [nrel_and] at h2
      by_cases h3 : v < F + c + nrel φ
      · rw [h2a v (by omega)]; exact h1b v h1 h3
      · exact h2b v (by omega) (by omega)
    · refine (sat_congr _ ∅ _ fun v h => ?_).mp h1c
      rw [mem_freeVars_tr (ctxOf D F) φ c hF.1 v] at h
      have hF' : (ctxOf D F).F = F := rfl
      rw [hF'] at h
      rcases h with h | h
      · exact (h2a v (Or.inl (by have := lt_of_mem_freeVars hF.1 h; omega))).symm
      · exact (h2a v (Or.inl (by omega))).symm
  | .or φ ψ, c, ρ, hq, hp, hf, hr, hF, hfv, hz, hs => by
    rcases hs with hs | hs
    · obtain ⟨ρ1, h1a, h1b, h1c⟩ := fwd hc F φ c ρ hq.1 hp.1 hf.1 hr.1 hF.1
        (fun v h => hfv v (by simp [Formula.freeVars, h]))
        (fun v h1 h2 => hz v h1 (by simp; omega)) hs
      refine ⟨ρ1, fun v h => h1a v (by simp at h; omega), fun v h1 h2 => ?_, Or.inl h1c⟩
      by_cases h3 : v < F + c + nrel φ
      · exact h1b v h1 h3
      · rw [h1a v (by omega)]; exact hz v h1 h2
    · obtain ⟨ρ2, h2a, h2b, h2c⟩ := fwd hc F ψ (c + nrel φ) ρ hq.2 hp.2 hf.2 hr.2 hF.2
        (fun v h => hfv v (by simp [Formula.freeVars, h]))
        (fun v h1 h2 => hz v (by omega) (by simp; omega)) hs
      refine ⟨ρ2, fun v h => h2a v (by simp at h; omega), fun v h1 h2 => ?_, Or.inr h2c⟩
      by_cases h3 : v < F + c + nrel φ
      · rw [h2a v (by omega)]; exact hz v h1 h2
      · exact h2b v (by omega) (by simp at h2; omega)
  | .ex _ _, _, _, hq, _, _, _, _, _, _, _ => hq.elim
  | .all _ _, _, _, hq, _, _, _, _, _, _, _ => hq.elim

/-! ### Backward -/

/-- **Backward**: an assignment satisfying the translation, with the new elements sent to `0`,
satisfies the formula. -/
theorem bwd (hc : Compat A D) (F : ℕ) : ∀ (ψ : Formula) (c : ℕ) (ρ : Assignment),
    ψ.IsQF → ψ.IsPositive → ψ.Fits A.arities 0 →
    Sat D.toStructure ∅ ((ctxOf D F).tr c ψ) ρ → Sat A ∅ ψ (normA D.N ρ)
  | .rel i ys, c, ρ, _, _, hf, hs => by
    obtain ⟨hi, hl⟩ := hf
    have hi' : i < D.s := by rw [hc.s_eq]; exact hi
    have hl' : ys.length = D.ar i := by rw [hc.ar_eq i hi']; exact hl
    have hp : (ctxOf D F).pIdx i ys.length = i := by
      unfold TrCtx.pIdx; exact if_pos ⟨hi', hl'⟩
    simp only [TrCtx.tr, TrCtx.relTr, hp, sat_relAux] at hs
    obtain ⟨hE, hP⟩ := hs
    obtain ⟨j, hj, hz⟩ := (D.mem_rel_P hc.valid hi').mp hP
    simp only [List.cons.injEq, and_true] at hz
    have hent : ∀ m < ys.length, ρ (ys.getD m 0) = D.ent i j m := by
      intro m hm
      have h := hE m hm
      have hcs : (ctxOf D F).s + (0 + m) = D.s + m := by simp [ctxOf]
      rw [hcs, D.mem_rel_E hc.valid] at h
      obtain ⟨-, i', hi'', hm', j', hj', ht⟩ := h
      simp only [List.cons.injEq, and_true] at ht
      obtain ⟨h1, h2⟩ := ht
      rw [hz] at h2
      obtain ⟨rfl, rfl⟩ := D.po_inj hj' hj (by omega)
      exact h1
    have hmap : ys.map (normA D.N ρ) = (List.range (D.ar i)).map (D.ent i j) := by
      apply List.ext_getElem
      · simp [hl']
      · intro m h1 h2
        simp only [List.getElem_map, List.getElem_range]
        have hm : m < ys.length := by simpa using h1
        have he := hent m hm
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some] at he
        have hlt := hc.valid i hi' j hj m (by omega)
        unfold normA
        rw [he, if_pos hlt]
    show ys.map (normA D.N ρ) ∈ A.rel i
    rw [hmap, ← (hc.list i hi').2, List.mem_toFinset]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  | .setVar ys, _, _, _, _, _, hs => by simp [TrCtx.tr, Sat] at hs
  | .eq x y, _, ρ, _, _, _, hs => by
    simp only [TrCtx.tr, Sat] at hs ⊢
    unfold normA; rw [hs]
  | .neg _, _, _, _, hp, _, _ => hp.elim
  | .and φ ψ, c, ρ, hq, hp, hf, hs =>
    ⟨bwd hc F φ c ρ hq.1 hp.1 hf.1 hs.1, bwd hc F ψ _ ρ hq.2 hp.2 hf.2 hs.2⟩
  | .or φ ψ, c, ρ, hq, hp, hf, hs => by
    rcases hs with hs | hs
    · exact Or.inl (bwd hc F φ c ρ hq.1 hp.1 hf.1 hs)
    · exact Or.inr (bwd hc F ψ _ ρ hq.2 hp.2 hf.2 hs)
  | .ex _ _, _, _, hq, _, _, _ => hq.elim
  | .all _ _, _, _, hq, _, _, _ => hq.elim

/-! ### Model checking -/

/-- The fresh variables. -/
def zsOf (F q : ℕ) : List ℕ := (List.range q).map (F + ·)

theorem mem_zsOf {F q v : ℕ} : v ∈ zsOf F q ↔ F ≤ v ∧ v < F + q := by
  simp only [zsOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨v - F, by omega, by omega⟩

/-- **The translated formula**: the fresh variables bound in front of the translation. -/
def phiOf (D : IncData) (F : ℕ) (φ : Formula) : Formula :=
  Formula.exBlock (zsOf F (nrel φ)) ((ctxOf D F).tr 0 φ)

theorem phiOf_exBlock (D : IncData) (F : ℕ) (xs : List ℕ) (ψ : Formula) :
    phiOf D F (Formula.exBlock xs ψ) =
      Formula.exBlock (zsOf F (nrel ψ) ++ xs) ((ctxOf D F).tr 0 ψ) := by
  rw [phiOf, nrel_exBlock, tr_exBlock, exBlock_append]

/-- **The reduction is correct**: `φ` holds in `A` exactly when its translation holds in the
incidence structure. -/
theorem models_iff (hc : Compat A D) {F : ℕ} {φ : Formula} (hF : VarsLt F φ) (hr : RelLe D.r φ)
    (hσ : IsSigma 1 φ) (hpos : φ.IsPositive) (hns : φ.NoSetVar) :
    Models A φ ↔ Models D.toStructure (phiOf D F φ) := by
  obtain ⟨xs, ψ, rfl, hqf⟩ := hσ
  have hqf' : ψ.IsQF := hqf
  rw [isPositive_exBlock] at hpos
  rw [noSetVar_exBlock] at hns
  rw [relLe_exBlock] at hr
  obtain ⟨hxs, hFψ⟩ := (varsLt_exBlock ψ xs).mp hF
  rw [phiOf_exBlock]
  set q := nrel ψ with hq
  set ψ' := (ctxOf D F).tr 0 ψ with hψ'
  have hfits : ψ'.Fits D.arities 0 ↔ ψ.Fits A.arities 0 :=
    fits_tr F hc.s_eq hc.ar_eq ψ 0 hr
  have hmemfv : ∀ v, v ∈ ψ'.freeVars ↔ v ∈ ψ.freeVars ∨ (F ≤ v ∧ v < F + q) := by
    intro v
    rw [hψ', mem_freeVars_tr (ctxOf D F) ψ 0 hFψ v]
    simp [ctxOf, hq]
  have hfvlt : ∀ v ∈ ψ.freeVars, v < F := fun v h => lt_of_mem_freeVars hFψ h
  -- the free variables of the two sides agree
  have hfvI : ∀ v, v ∈ (Formula.exBlock (zsOf F q ++ xs) ψ').freeVars ↔
      v ∈ (Formula.exBlock xs ψ).freeVars := by
    intro v
    simp only [freeVars_exBlock, Finset.mem_sdiff, List.mem_toFinset, List.mem_append, mem_zsOf,
      hmemfv]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · exact absurd (Or.inl h1) h2
    · rintro ⟨h1, h2⟩
      have := hfvlt v h1
      refine ⟨Or.inl h1, ?_⟩
      rintro (h | h)
      · omega
      · exact h2 h
  constructor
  · -- forward
    rintro ⟨hf, -, ρ, hρ, hs⟩
    rw [fits_exBlock] at hf
    rw [sat_exBlock] at hs
    obtain ⟨ρ1, h1a, h1b, h1c⟩ := hs
    have hψlt : ∀ v ∈ ψ.freeVars, ρ1 v < A.size := by
      intro v hv
      by_cases hx : v ∈ xs
      · exact h1b v hx
      · rw [h1a v hx]
        exact hρ v (by rw [freeVars_exBlock]; simp [hv, hx])
    obtain ⟨v0, hv0⟩ := exists_freeVar ψ hqf' hns hf
    have hN : 0 < D.N := by rw [hc.N_eq]; have := hψlt v0 hv0; omega
    have hsz : 0 < D.size := by unfold IncData.size; omega
    set ρ2 : Assignment := fun v => if F ≤ v ∧ v < F + q then 0 else ρ1 v with hρ2
    have h2 : ∀ v, v < F → ρ2 v = ρ1 v := fun v hv => by
      simp only [hρ2]; rw [if_neg (by omega)]
    obtain ⟨ρ3, h3a, h3b, h3c⟩ := fwd hc F ψ 0 ρ2 hqf' hpos hf hr hFψ
      (fun v hv => by rw [h2 v (hfvlt v hv)]; exact hψlt v hv)
      (fun v h1 h2' => by simp only [hρ2]; rw [if_pos (by omega)]; exact hsz)
      ((sat_congr A ∅ ψ fun v hv => (h2 v (hfvlt v hv)).symm).mp h1c)
    refine ⟨(fits_exBlock _ _ _ _).mpr (hfits.mpr hf),
      (noSetVar_exBlock _ _).mpr (noSetVar_tr _ ψ 0 hns), ρ, fun v hv => ?_, ?_⟩
    · have := hρ v ((hfvI v).mp hv)
      simp only [IncData.toStructure_size]; unfold IncData.size; rw [← hc.N_eq] at this; omega
    · rw [sat_exBlock]
      refine ⟨ρ3, fun v hv => ?_, fun v hv => ?_, h3c⟩
      · simp only [List.mem_append, mem_zsOf, not_or] at hv
        rw [h3a v (by omega)]
        simp only [hρ2]; rw [if_neg hv.1]
        exact h1a v hv.2
      · rcases List.mem_append.mp hv with hv | hv
        · rw [mem_zsOf] at hv; exact h3b v (by omega) (by omega)
        · have := hxs v hv
          rw [h3a v (by omega), h2 v this]
          have := h1b v hv
          simp only [IncData.toStructure_size]; unfold IncData.size; rw [← hc.N_eq] at this; omega
  · -- backward
    rintro ⟨hf, -, ρ, hρ, hs⟩
    rw [fits_exBlock] at hf
    have hf' : ψ.Fits A.arities 0 := hfits.mp hf
    rw [sat_exBlock] at hs
    obtain ⟨ρ1, h1a, h1b, h1c⟩ := hs
    have hsat := bwd hc F ψ 0 ρ1 hqf' hpos hf' h1c
    obtain ⟨v0, hv0⟩ := exists_freeVar ψ hqf' hns hf'
    have hsz : 0 < D.size := by
      by_cases hv : v0 ∈ zsOf F q ++ xs
      · have := h1b v0 hv
        rw [IncData.toStructure_size] at this; omega
      · have hfree : v0 ∈ (Formula.exBlock (zsOf F q ++ xs) ψ').freeVars := by
          rw [freeVars_exBlock, Finset.mem_sdiff, List.mem_toFinset, hmemfv]
          exact ⟨Or.inl hv0, hv⟩
        have := hρ v0 hfree
        rw [IncData.toStructure_size] at this; omega
    have hN : 0 < D.N := by
      by_contra h
      have hT := hc.T_eq_zero (by omega)
      unfold IncData.size at hsz; omega
    have hN' : 0 < A.size := by rw [← hc.N_eq]; exact hN
    refine ⟨(fits_exBlock _ _ _ _).mpr hf', (noSetVar_exBlock _ _).mpr hns, normA D.N ρ1,
      fun v _ => by rw [← hc.N_eq]; exact normA_lt hN ρ1 v, ?_⟩
    rw [sat_exBlock]
    exact ⟨normA D.N ρ1, fun _ _ => rfl, fun v _ => by rw [← hc.N_eq]; exact normA_lt hN ρ1 v,
      hsat⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem
