import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem

/-! # Negation elimination: `A ⊨ φ` iff `A' ⊨ φ'`

`sem` is the correctness of the translation of a quantifier-free formula, by induction; `models_iff`
lifts it to `Σ_1`-formulas `∃x̄ ψ` and their translations `∃(fresh) ∃x̄ tr ψ`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Correct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem

theorem fv_left {p : Bool} {φ : Formula} {c : ℕ} (hφ : ∀ v ∈ φ.freeVars, v < c) :
    ∀ v ∈ (tr p φ c).freeVars, v < c + cnt p φ := fun v hv => by
  rcases mem_freeVars_tr p φ c hv with h | h
  · have := hφ v h; omega
  · omega

theorem fv_right {p : Bool} {ψ : Formula} {c : ℕ} (hψ : ∀ v ∈ ψ.freeVars, v < c) (n : ℕ) :
    ∀ v ∈ (tr p ψ (c + n)).freeVars, v < c ∨ c + n ≤ v := fun v hv => by
  rcases mem_freeVars_tr p ψ (c + n) hv with h | h
  · exact Or.inl (hψ v h)
  · exact Or.inr h.1

variable {A : Structure} {D : NData}

/-- **The translation is correct** on quantifier-free formulas. -/
theorem sem (hc : Compat A D) (hN : 0 < A.size) : ∀ (p : Bool) (φ : Formula) (c : ℕ)
    (ρ : Assignment), φ.IsQF → φ.NoSetVar → φ.Fits A.arities 0 → (∀ v ∈ φ.freeVars, v < c) →
      (∀ v ∈ φ.freeVars, ρ v < A.size) →
      (Ext (NData.toStructure hc.valid) (tr p φ c) c (cnt p φ) ρ ↔ (Sat A ∅ φ ρ ↔ p = true))
  | true, .rel i ys, c, ρ, _, _, hf, _, _ => by
    have hi : i < D.s := by rw [hc.s]; exact hf.1
    show Ext _ (.rel (rI i) ys) c 0 ρ ↔ _
    rw [ext_zero]
    show ys.map ρ ∈ (NData.toStructure hc.valid).rel (rI i) ↔ (ys.map ρ ∈ A.rel i ↔ true = true)
    rw [NData.mem_rel_r hc.valid hi, hc.mem_L hi]; simp
  | false, .rel i ys, c, ρ, _, _, hf, hvc, hρ => by
    have hi : i < D.s := by rw [hc.s]; exact hf.1
    have hl : ys.length = D.ar i := by rw [hc.ar i hi]; exact hf.2
    show Ext _ (negRel i ys c) c (2 * ys.length) ρ ↔ (ys.map ρ ∈ A.rel i ↔ false = true)
    rw [ext_negRel hc hi hl (fun v hv => hvc v (by simpa [Formula.freeVars] using hv))
      (fun v hv => by rw [hc.N]; exact hρ v (by simpa [Formula.freeVars] using hv)), hc.mem_L hi]
    simp
  | _, .setVar _, _, _, _, hns, _, _, _ => hns.elim
  | true, .eq x y, c, ρ, _, _, _, _, _ => by
    show Ext _ (.eq x y) c 0 ρ ↔ _
    rw [ext_zero]; simp [Sat]
  | false, .eq x y, c, ρ, _, _, _, _, hρ => by
    show Ext _ (.or (.rel 0 [x, y]) (.rel 0 [y, x])) c 0 ρ ↔ _
    rw [ext_zero]
    have hx := hρ x (by simp [Formula.freeVars])
    have hy := hρ y (by simp [Formula.freeVars])
    rw [← hc.N] at hx hy
    simp only [Sat, NData.mem_rel_lt, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    constructor
    · rintro (⟨a, b, ⟨rfl, rfl⟩, h, -⟩ | ⟨a, b, ⟨rfl, rfl⟩, h, -⟩) <;> simp <;> omega
    · intro h
      simp only [Bool.false_eq_true, iff_false] at h
      rcases Nat.lt_or_gt_of_ne h with h | h
      · exact Or.inl ⟨_, _, ⟨rfl, rfl⟩, h, hy⟩
      · exact Or.inr ⟨_, _, ⟨rfl, rfl⟩, h, hx⟩
  | p, .neg φ, c, ρ, hq, hns, hf, hvc, hρ => by
    cases p
    · show Ext _ (tr true φ c) c (cnt true φ) ρ ↔ (¬ Sat A ∅ φ ρ ↔ false = true)
      rw [sem hc hN true φ c ρ hq hns hf hvc hρ]; simp
    · show Ext _ (tr false φ c) c (cnt false φ) ρ ↔ (¬ Sat A ∅ φ ρ ↔ true = true)
      rw [sem hc hN false φ c ρ hq hns hf hvc hρ]; simp
  | true, .and φ ψ, c, ρ, hq, hns, hf, hvc, hρ => by
    have h1 : ∀ v ∈ φ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have h2 : ∀ v ∈ ψ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have r1 : ∀ v ∈ φ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    have r2 : ∀ v ∈ ψ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    show Ext _ (.and (tr true φ c) (tr true ψ (c + cnt true φ))) c (cnt true φ + cnt true ψ) ρ ↔
      (Sat A ∅ φ ρ ∧ Sat A ∅ ψ ρ ↔ true = true)
    rw [ext_and (fv_left h1) (fv_right h2 _), sem hc hN true φ c ρ hq.1 hns.1 hf.1 h1 r1,
      sem hc hN true ψ _ ρ hq.2 hns.2 hf.2 (fun v hv => by have := h2 v hv; omega) r2]
    simp
  | false, .and φ ψ, c, ρ, hq, hns, hf, hvc, hρ => by
    have h1 : ∀ v ∈ φ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have h2 : ∀ v ∈ ψ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have r1 : ∀ v ∈ φ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    have r2 : ∀ v ∈ ψ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    show Ext _ (.or (tr false φ c) (tr false ψ (c + cnt false φ))) c (cnt false φ + cnt false ψ) ρ ↔
      (Sat A ∅ φ ρ ∧ Sat A ∅ ψ ρ ↔ false = true)
    rw [ext_or (show 0 < D.N by rw [hc.N]; exact hN) (fv_left h1) (fv_right h2 _),
      sem hc hN false φ c ρ hq.1 hns.1 hf.1 h1 r1,
      sem hc hN false ψ _ ρ hq.2 hns.2 hf.2 (fun v hv => by have := h2 v hv; omega) r2]
    simp only [Bool.false_eq_true, iff_false]
    tauto
  | true, .or φ ψ, c, ρ, hq, hns, hf, hvc, hρ => by
    have h1 : ∀ v ∈ φ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have h2 : ∀ v ∈ ψ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have r1 : ∀ v ∈ φ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    have r2 : ∀ v ∈ ψ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    show Ext _ (.or (tr true φ c) (tr true ψ (c + cnt true φ))) c (cnt true φ + cnt true ψ) ρ ↔
      (Sat A ∅ φ ρ ∨ Sat A ∅ ψ ρ ↔ true = true)
    rw [ext_or (show 0 < D.N by rw [hc.N]; exact hN) (fv_left h1) (fv_right h2 _),
      sem hc hN true φ c ρ hq.1 hns.1 hf.1 h1 r1,
      sem hc hN true ψ _ ρ hq.2 hns.2 hf.2 (fun v hv => by have := h2 v hv; omega) r2]
    simp
  | false, .or φ ψ, c, ρ, hq, hns, hf, hvc, hρ => by
    have h1 : ∀ v ∈ φ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have h2 : ∀ v ∈ ψ.freeVars, v < c := fun v hv => hvc v (by simp [Formula.freeVars, hv])
    have r1 : ∀ v ∈ φ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    have r2 : ∀ v ∈ ψ.freeVars, ρ v < A.size := fun v hv => hρ v (by simp [Formula.freeVars, hv])
    show Ext _ (.and (tr false φ c) (tr false ψ (c + cnt false φ))) c (cnt false φ + cnt false ψ) ρ ↔
      (Sat A ∅ φ ρ ∨ Sat A ∅ ψ ρ ↔ false = true)
    rw [ext_and (fv_left h1) (fv_right h2 _), sem hc hN false φ c ρ hq.1 hns.1 hf.1 h1 r1,
      sem hc hN false ψ _ ρ hq.2 hns.2 hf.2 (fun v hv => by have := h2 v hv; omega) r2]
    simp only [Bool.false_eq_true, iff_false]
    tauto
  | _, .ex _ _, _, _, hq, _, _, _, _ => hq.elim
  | _, .all _ _, _, _, hq, _, _, _, _ => hq.elim

/-! ### From quantifier-free formulas to `Σ_1` -/

theorem mem_encode_of_freeVars : ∀ (φ : Formula) {v : ℕ}, v ∈ φ.freeVars → v ∈ φ.encode
  | .rel _ _, v, h => by simp [Formula.freeVars, Formula.encode] at h ⊢; simp [h]
  | .setVar _, v, h => by simp [Formula.freeVars, Formula.encode] at h ⊢; simp [h]
  | .eq _ _, v, h => by simp [Formula.freeVars, Formula.encode] at h ⊢; tauto
  | .neg φ, v, h => by
    simp only [Formula.freeVars] at h
    simp [Formula.encode, mem_encode_of_freeVars φ h]
  | .and φ ψ, v, h => by
    simp only [Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · simp [Formula.encode, mem_encode_of_freeVars φ h]
    · simp [Formula.encode, mem_encode_of_freeVars ψ h]
  | .or φ ψ, v, h => by
    simp only [Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · simp [Formula.encode, mem_encode_of_freeVars φ h]
    · simp [Formula.encode, mem_encode_of_freeVars ψ h]
  | .ex _ φ, v, h => by
    simp only [Formula.freeVars, Finset.mem_erase] at h
    simp [Formula.encode, mem_encode_of_freeVars φ h.2]
  | .all _ φ, v, h => by
    simp only [Formula.freeVars, Finset.mem_erase] at h
    simp [Formula.encode, mem_encode_of_freeVars φ h.2]

/-- A quantifier-free formula that fits a vocabulary of positive arities has a variable. -/
theorem exists_freeVar {as : List ℕ} (has : ∀ i < as.length, 1 ≤ as.getD i 0) :
    ∀ φ : Formula, φ.IsQF → φ.NoSetVar → φ.Fits as 0 → ∃ v, v ∈ φ.freeVars
  | .rel i ys, _, _, hf => by
    have := has i hf.1
    have h2 : ys.length = as.getD i 0 := hf.2
    have hne : ys ≠ [] := by rintro rfl; rw [List.length_nil] at h2; omega
    obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨y, by simp [Formula.freeVars]⟩
  | .setVar _, _, h, _ => h.elim
  | .eq x _, _, _, _ => ⟨x, by simp [Formula.freeVars]⟩
  | .neg φ, hq, hn, hf => by
    obtain ⟨v, hv⟩ := exists_freeVar has φ hq hn hf; exact ⟨v, hv⟩
  | .and φ _, hq, hn, hf => by
    obtain ⟨v, hv⟩ := exists_freeVar has φ hq.1 hn.1 hf.1
    exact ⟨v, by simp [Formula.freeVars, hv]⟩
  | .or φ _, hq, hn, hf => by
    obtain ⟨v, hv⟩ := exists_freeVar has φ hq.1 hn.1 hf.1
    exact ⟨v, by simp [Formula.freeVars, hv]⟩
  | .ex _ _, hq, _, _ => hq.elim
  | .all _ _, hq, _, _ => hq.elim

/-- In an empty universe no `Σ_1`-formula is modelled. -/
theorem not_models_of_size_zero {B : Structure} (hB : B.size = 0) {ψ : Formula} (hq : ψ.IsQF) :
    ∀ xs : List ℕ, ¬ Models B (Formula.exBlock xs ψ)
  | [], ⟨hf, hn, ρ, hρ, _⟩ => by
    obtain ⟨v, hv⟩ := exists_freeVar (Structure.arity_pos' B) ψ hq hn hf
    have := hρ v hv; omega
  | x :: xs, ⟨_, _, ρ, _, hs⟩ => by
    obtain ⟨a, ha, -⟩ := hs; omega

theorem exBlock_append (θ : Formula) (l₁ l₂ : List ℕ) :
    Formula.exBlock (l₁ ++ l₂) θ = Formula.exBlock l₁ (Formula.exBlock l₂ θ) := by
  simp [Formula.exBlock, List.foldr_append]

/-- **Negation elimination is correct**: `A ⊨ φ` iff the expanded structure satisfies `φ'`. -/
theorem models_iff (hc : Compat A D) {b K : ℕ} {φ : Formula} (hφ : IsSigma 1 φ)
    (hns : φ.NoSetVar) (hb : ∀ v ∈ φ.encode, v < b) (hK : cnt true φ ≤ K) :
    Models A φ ↔ Models (NData.toStructure hc.valid) (phiOf b K φ) := by
  obtain ⟨xs, ψ, rfl, hq⟩ : ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ ψ.IsQF := hφ
  set A' := NData.toStructure hc.valid with hA'
  have hsz : A'.size = A.size := hc.N
  set n := cnt true ψ with hn
  rw [cnt_exBlock] at hK
  have hphi : phiOf b K (Formula.exBlock xs ψ) =
      Formula.exBlock (List.range' b K) (Formula.exBlock xs (tr true ψ b)) := by
    rw [phiOf, tr_exBlock]
  rw [hphi]
  rw [encode_exBlock] at hb
  have hbx : ∀ v ∈ xs, v < b := fun v hv => hb v (by simp; exact Or.inl ⟨v, hv, by simp⟩)
  have hbψ : ∀ v ∈ ψ.freeVars, v < b := fun v hv =>
    hb v (List.mem_append_right _ (mem_encode_of_freeVars ψ hv))
  have hnsψ : ψ.NoSetVar := (noSetVar_exBlock ψ xs).mp hns
  have hfits : (Formula.exBlock xs ψ).Fits A.arities 0 ↔
      (Formula.exBlock (List.range' b K) (Formula.exBlock xs (tr true ψ b))).Fits A'.arities 0 := by
    rw [fits_exBlock, fits_exBlock, fits_exBlock]
    exact (fits_tr_iff hc.extAr true ψ b).symm
  have hns' : (Formula.exBlock (List.range' b K) (Formula.exBlock xs (tr true ψ b))).NoSetVar := by
    rw [noSetVar_exBlock, noSetVar_exBlock]; exact tr_noSetVar true ψ b hnsψ
  have hfv : ∀ v, v ∈ (Formula.exBlock (List.range' b K) (Formula.exBlock xs (tr true ψ b))).freeVars
      ↔ v ∈ (Formula.exBlock xs ψ).freeVars := by
    intro v
    simp only [freeVars_exBlock, Finset.mem_sdiff, List.mem_toFinset, mem_range'_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases mem_freeVars_tr true ψ b h1 with h | h
      · exact ⟨h, h2⟩
      · exact absurd ⟨h.1, by omega⟩ h3
    · rintro ⟨h1, h2⟩
      have := hbψ v h1
      exact ⟨⟨freeVars_sub_tr true ψ b h1, h2⟩, by omega⟩
  have hfvθ : ∀ v ∈ (tr true ψ b).freeVars, v < b + n := fun v hv => by
    rcases mem_freeVars_tr true ψ b hv with h | h
    · have := hbψ v h; omega
    · exact h.2
  by_cases hA0 : A.size = 0
  · refine iff_of_false (not_models_of_size_zero hA0 hq xs) ?_
    rw [← exBlock_append]
    exact not_models_of_size_zero (by rw [hsz, hA0]) (tr_isQF true ψ b hq) _
  have hN : 0 < A.size := Nat.pos_of_ne_zero hA0
  unfold Models
  constructor
  · rintro ⟨hf, -, ρ, hρ, hs⟩
    have hfψ : ψ.Fits A.arities 0 := (fits_exBlock _ _ ψ xs).mp hf
    refine ⟨hfits.mp hf, hns', ?_⟩
    rw [sat_exBlock] at hs
    obtain ⟨ρ₂, h1, h2, hs2⟩ := hs
    have hr2 : ∀ v ∈ ψ.freeVars, ρ₂ v < A.size := by
      intro v hv
      by_cases hvx : v ∈ xs
      · exact h2 v hvx
      · rw [h1 v hvx]
        exact hρ v (by rw [freeVars_exBlock]; simp [hv, hvx])
    obtain ⟨ρ₃, ha3, hu3, hs3⟩ :=
      (sem hc hN true ψ b ρ₂ hq hnsψ hfψ hbψ hr2).mpr (iff_of_true hs2 rfl)
    set ρ₄ : Assignment := fun v => if b + n ≤ v ∧ v < b + K then 0 else ρ₃ v with hρ₄
    have hs4 : Sat A' ∅ (tr true ψ b) ρ₄ := (sat_congr A' ∅ _ fun v hv => by
      have := hfvθ v hv
      rw [hρ₄]; (try simp only); rw [if_neg (by omega)]).mpr hs3
    refine ⟨ρ, fun v hv => by rw [hsz]; exact hρ v ((hfv v).mp hv), ?_⟩
    rw [sat_exBlock]
    refine ⟨fun v => if b ≤ v ∧ v < b + K then ρ₄ v else ρ v, fun v hv => ?_, fun v hv => ?_, ?_⟩
    · rw [mem_range'_iff] at hv; (try simp only); rw [if_neg hv]
    · rw [mem_range'_iff] at hv; (try simp only); rw [if_pos hv, hρ₄]; (try simp only)
      split_ifs with h
      · rw [hsz]; exact hN
      · exact hu3 v hv.1 (by omega)
    · rw [sat_exBlock]
      refine ⟨ρ₄, fun v hv => ?_, fun v hv => ?_, hs4⟩
      · split_ifs with h
        · rfl
        · rw [hρ₄]; (try simp only); rw [if_neg (by omega), ha3 v (by omega), h1 v hv]
      · have := hbx v hv
        rw [hρ₄]; (try simp only); rw [if_neg (by omega), ha3 v (Or.inl this), hsz]; exact h2 v hv
  · rintro ⟨hf', -, ρ, hρ, hs⟩
    have hf : (Formula.exBlock xs ψ).Fits A.arities 0 := hfits.mpr hf'
    have hfψ : ψ.Fits A.arities 0 := (fits_exBlock _ _ ψ xs).mp hf
    refine ⟨hf, hns, ?_⟩
    rw [sat_exBlock] at hs
    obtain ⟨ρ₁, h1, h2, hs1⟩ := hs
    rw [sat_exBlock] at hs1
    obtain ⟨ρ₂, h3, h4, hs2⟩ := hs1
    set ρ₂' : Assignment := fun v => if b ≤ v ∧ v < b + K then ρ v else ρ₂ v with hρ₂'
    have hext : Ext A' (tr true ψ b) b n ρ₂' := by
      refine ⟨fun v => if b ≤ v ∧ v < b + n then ρ₂ v else ρ₂' v, fun v hv => ?_,
        fun v hv1 hv2 => ?_, (sat_congr A' ∅ _ fun v hv => ?_).mp hs2⟩
      · (try simp only); rw [if_neg (by omega)]
      · (try simp only); rw [if_pos ⟨hv1, hv2⟩]
        have hvx : v ∉ xs := fun h => by have := hbx v h; omega
        rw [h3 v hvx]; exact h2 v (by rw [mem_range'_iff]; omega)
      · have := hfvθ v hv
        split_ifs with h
        · rfl
        · rw [hρ₂']; (try simp only); rw [if_neg (by omega)]
    have hr2 : ∀ v ∈ ψ.freeVars, ρ₂' v < A.size := by
      intro v hv
      have hvb := hbψ v hv
      rw [hρ₂']; (try simp only); rw [if_neg (by omega)]
      by_cases hvx : v ∈ xs
      · rw [← hsz]; exact h4 v hvx
      · rw [h3 v hvx, h1 v (by rw [mem_range'_iff]; omega)]
        rw [← hsz]; exact hρ v ((hfv v).mpr (by rw [freeVars_exBlock]; simp [hv, hvx]))
    have hsat := ((sem hc hN true ψ b ρ₂' hq hnsψ hfψ hbψ hr2).mp hext).mpr rfl
    refine ⟨ρ, fun v hv => by rw [← hsz]; exact hρ v ((hfv v).mpr hv), ?_⟩
    rw [sat_exBlock]
    refine ⟨ρ₂', fun v hv => ?_, fun v hv => ?_, hsat⟩
    · rw [hρ₂']; (try simp only)
      split_ifs with h
      · rfl
      · rw [h3 v hv, h1 v (by rw [mem_range'_iff]; omega)]
    · have := hbx v hv
      rw [hρ₂']; (try simp only); rw [if_neg (by omega), ← hsz]; exact h4 v hv

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Correct
