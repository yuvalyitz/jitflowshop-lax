import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Correct

/-! # Negation elimination: compressing the universe

The universe `{0, …, N-1}` of a structure is part of its word only as the number `N`, so a
construction that lists all pairs of elements (as the order `<` of the expansion does) is not
polynomial in the length of the word. Before expanding, the universe is therefore compressed: the
elements of a set `U` containing every entry of every tuple are renamed by their rank in `U`
(`rk U`), and the other elements are cut down to at most `n` of them (any universe size `M` with
`min N (|U| + n) ≤ M ≤ N` will do). A `Σ_1`-formula of size at most `n` uses at most `n` elements,
and elements outside every tuple are interchangeable, so the compressed structure satisfies the same
`Σ_1`-formulas of size at most `n` (`models_compress_iff`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Lemmas.NegElim.Correct

/-! ### Ranks -/

/-- The rank of `e` in `U`: the number of elements of `U` below `e`. -/
def rk (U : Finset ℕ) (e : ℕ) : ℕ := (U.filter (· < e)).card

theorem rk_lt_rk {U : Finset ℕ} {e e' : ℕ} (he : e ∈ U) (hlt : e < e') : rk U e < rk U e' := by
  unfold rk
  refine Finset.card_lt_card ⟨fun a ha => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩
  · have := h (Finset.mem_filter.mpr ⟨he, hlt⟩); simp at this

theorem rk_injOn (U : Finset ℕ) : Set.InjOn (rk U) U := by
  intro e he e' he' h
  rcases lt_trichotomy e e' with hl | hl | hl
  · exact absurd h (ne_of_lt (rk_lt_rk he hl))
  · exact hl
  · exact absurd h (ne_of_gt (rk_lt_rk he' hl))

theorem rk_lt_card {U : Finset ℕ} {e : ℕ} (he : e ∈ U) : rk U e < U.card := by
  unfold rk
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h he; simp at this

theorem rk_surj {U : Finset ℕ} {j : ℕ} (hj : j < U.card) : ∃ e ∈ U, rk U e = j := by
  obtain ⟨e, he, h⟩ := Finset.surj_on_of_inj_on_of_card_le (s := U) (t := Finset.range U.card)
    (fun e _ => rk U e) (fun e he => Finset.mem_range.mpr (rk_lt_card he))
    (fun a b ha hb h => rk_injOn U ha hb h) (by simp) j (Finset.mem_range.mpr hj)
  exact ⟨e, he, h.symm⟩

theorem map_rk_inj {U : Finset ℕ} {u t : List ℕ} (hu : ∀ a ∈ u, a ∈ U) (ht : ∀ a ∈ t, a ∈ U)
    (h : u.map (rk U) = t.map (rk U)) : u = t := by
  have hlen : u.length = t.length := by rw [← List.length_map (f := rk U), h, List.length_map]
  apply List.ext_getElem hlen
  intro k h1 h2
  have := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at this
  exact rk_injOn U (hu _ (List.getElem_mem h1)) (ht _ (List.getElem_mem h2)) this

/-! ### The compressed structure -/

variable (A : Structure) (U : Finset ℕ) (n : ℕ)

/-- `U` holds every entry of every tuple and lies in the universe. -/
structure Cover : Prop where
  ent : ∀ i, ∀ t ∈ A.rel i, ∀ a ∈ t, a ∈ U
  lt : ∀ a ∈ U, a < A.size

variable {A U}

theorem Cover.card_le (hU : Cover A U) : U.card ≤ A.size := by
  have : U ⊆ Finset.range A.size := fun a ha => Finset.mem_range.mpr (hU.lt a ha)
  simpa using Finset.card_le_card this

/-- **The compressed structure**: tuples renamed by rank, universe `{0, …, M - 1}` for some
`M ≥ |U|`. -/
def compress (hU : Cover A U) (M : ℕ) (hM : U.card ≤ M) : Structure where
  arities := A.arities
  size := M
  rel i := (A.rel i).image (List.map (rk U))
  arity_pos := A.arity_pos
  wf i t ht := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, h2, -⟩ := A.wf i u hu
    refine ⟨h1, by rw [List.length_map, h2], fun a ha => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    have := rk_lt_card (hU.ent i u hu e he)
    omega

/-! ### Satisfaction under a renaming -/

/-- **A quantifier-free formula is preserved by a renaming** that is injective on the values used
and respects the relations on them. -/
theorem sat_map {B C : Structure} (h : ℕ → ℕ) (S : ℕ → Prop) (hinj : ∀ a b, S a → S b → h a = h b → a = b)
    (hrel : ∀ i (t : List ℕ), (∀ a ∈ t, S a) → (t ∈ B.rel i ↔ t.map h ∈ C.rel i)) :
    ∀ (ψ : Formula) (ρ : Assignment), ψ.IsQF → (∀ v ∈ ψ.freeVars, S (ρ v)) →
      (Sat B ∅ ψ ρ ↔ Sat C ∅ ψ (h ∘ ρ))
  | .rel i ys, ρ, _, hS => by
    simp only [Sat]
    rw [← List.map_map]
    exact hrel i _ (fun a ha => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact hS v (by simp [Formula.freeVars, hv]))
  | .setVar _, _, _, _ => by simp [Sat]
  | .eq x y, ρ, _, hS => by
    simp only [Sat, Function.comp]
    exact ⟨fun h' => by rw [h'], hinj _ _ (hS x (by simp [Formula.freeVars]))
      (hS y (by simp [Formula.freeVars]))⟩
  | .neg φ, ρ, hq, hS => by
    simp only [Sat]
    rw [sat_map h S hinj hrel φ ρ hq (fun v hv => hS v (by simpa [Formula.freeVars] using hv))]
  | .and φ ψ, ρ, hq, hS => by
    simp only [Sat]
    rw [sat_map h S hinj hrel φ ρ hq.1 (fun v hv => hS v (by simp [Formula.freeVars, hv])),
      sat_map h S hinj hrel ψ ρ hq.2 (fun v hv => hS v (by simp [Formula.freeVars, hv]))]
  | .or φ ψ, ρ, hq, hS => by
    simp only [Sat]
    rw [sat_map h S hinj hrel φ ρ hq.1 (fun v hv => hS v (by simp [Formula.freeVars, hv])),
      sat_map h S hinj hrel ψ ρ hq.2 (fun v hv => hS v (by simp [Formula.freeVars, hv]))]
  | .ex _ _, _, hq, _ => hq.elim
  | .all _ _, _, hq, _ => hq.elim

theorem card_freeVars_le : ∀ φ : Formula, φ.freeVars.card ≤ φ.size
  | .rel _ xs => by
    simp only [Formula.freeVars, Formula.size]
    have := List.toFinset_card_le xs; omega
  | .setVar xs => by
    simp only [Formula.freeVars, Formula.size]
    have := List.toFinset_card_le xs; omega
  | .eq x y => by
    simp only [Formula.freeVars, Formula.size]
    have := Finset.card_insert_le x {y}; simp at this; omega
  | .neg φ => by have := card_freeVars_le φ; simp [Formula.freeVars, Formula.size]; omega
  | .and φ ψ => by
    have := card_freeVars_le φ; have := card_freeVars_le ψ
    have := Finset.card_union_le φ.freeVars ψ.freeVars
    simp only [Formula.freeVars, Formula.size]; omega
  | .or φ ψ => by
    have := card_freeVars_le φ; have := card_freeVars_le ψ
    have := Finset.card_union_le φ.freeVars ψ.freeVars
    simp only [Formula.freeVars, Formula.size]; omega
  | .ex x φ => by
    have := card_freeVars_le φ; have := Finset.card_erase_le (s := φ.freeVars) (a := x)
    simp only [Formula.freeVars, Formula.size]; omega
  | .all x φ => by
    have := card_freeVars_le φ; have := Finset.card_erase_le (s := φ.freeVars) (a := x)
    simp only [Formula.freeVars, Formula.size]; omega

/-! ### The two renamings -/

/-- The elements of the universe outside `U`, in increasing order. -/
def others (N : ℕ) (U : Finset ℕ) : List ℕ := (List.range N).filter fun a => a ∉ U

theorem nodup_others (N : ℕ) (U : Finset ℕ) : (others N U).Nodup := List.nodup_range.filter _

theorem mem_others {N : ℕ} {U : Finset ℕ} {a : ℕ} : a ∈ others N U ↔ a < N ∧ a ∉ U := by
  simp [others]

theorem length_others (hU : Cover A U) : (others A.size U).length = A.size - U.card := by
  rw [← List.toFinset_card_of_nodup (nodup_others _ _)]
  have : (others A.size U).toFinset = Finset.range A.size \ U := by
    ext a; simp [mem_others]
  rw [this, Finset.card_sdiff_of_subset (fun a ha => Finset.mem_range.mpr (hU.lt a ha)),
    Finset.card_range]

open Classical in
/-- The renaming back: rank `j < |U|` to the element of `U` of that rank, the others to the
elements outside `U`. -/
noncomputable def back (N : ℕ) (U : Finset ℕ) (j : ℕ) : ℕ :=
  if h : ∃ e ∈ U, rk U e = j then Classical.choose h else (others N U).getD (j - U.card) 0

theorem back_rk {N : ℕ} {e : ℕ} (he : e ∈ U) : back N U (rk U e) = e := by
  have h : ∃ e' ∈ U, rk U e' = rk U e := ⟨e, he, rfl⟩
  unfold back
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  exact rk_injOn U h1 he h2

theorem back_of_ge {N j : ℕ} (hj : U.card ≤ j) : back N U j = (others N U).getD (j - U.card) 0 := by
  unfold back
  rw [dif_neg]
  rintro ⟨e, he, rfl⟩
  have := rk_lt_card he; omega

theorem back_ge_mem (hU : Cover A U) {j : ℕ} (hj : U.card ≤ j) (hjN : j < A.size) :
    back A.size U j ∈ others A.size U := by
  rw [back_of_ge hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [length_others hU]; omega)]
  exact List.getElem_mem _

/-- **From the compressed structure back.** -/
theorem models_of_compress (hU : Cover A U) {M : ℕ} (hM : U.card ≤ M) (hMN : M ≤ A.size)
    {φ : Formula} (hφ : IsSigma 1 φ) (h : Models (compress hU M hM) φ) : Models A φ := by
  obtain ⟨xs, ψ, rfl, hq⟩ : ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ ψ.IsQF := hφ
  obtain ⟨hf, hns, ρ₁, hρ₁, hs⟩ := h
  rw [sat_exBlock] at hs
  obtain ⟨ρ₁', h1, h2, hs'⟩ := hs
  have hMsz : (compress hU M hM).size = M := rfl
  -- the values used are below `M`
  have hV : ∀ v ∈ ψ.freeVars, ρ₁' v < M := by
    intro v hv
    by_cases hvx : v ∈ xs
    · exact h2 v hvx
    · rw [h1 v hvx]; exact hρ₁ v (by rw [freeVars_exBlock]; simp [hv, hvx])
  set π := back A.size U with hπ
  have hπN : ∀ j, j < M → π j < A.size := by
    intro j hj
    by_cases hjc : j < U.card
    · obtain ⟨e, he, rfl⟩ := rk_surj hjc
      rw [hπ, back_rk he]; exact hU.lt e he
    · exact (mem_others.mp (back_ge_mem hU (by omega) (by omega))).1
  have hinj : ∀ a b, a < M → b < M → π a = π b → a = b := by
    intro a b ha hb hab
    rcases Nat.lt_or_ge a U.card with ha' | ha' <;> rcases Nat.lt_or_ge b U.card with hb' | hb'
    · obtain ⟨e, he, rfl⟩ := rk_surj ha'
      obtain ⟨e', he', rfl⟩ := rk_surj hb'
      rw [hπ, back_rk he, back_rk he'] at hab; rw [hab]
    · obtain ⟨e, he, rfl⟩ := rk_surj ha'
      have := (mem_others.mp (back_ge_mem hU hb' (by omega))).2
      rw [hπ, back_rk he] at hab; rw [hab] at he; exact absurd he this
    · obtain ⟨e, he, rfl⟩ := rk_surj hb'
      have := (mem_others.mp (back_ge_mem hU ha' (by omega))).2
      rw [hπ, back_rk he] at hab; rw [← hab] at he; exact absurd he this
    · rw [hπ, back_of_ge ha', back_of_ge hb'] at hab
      have hl := length_others hU
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hab
      simp only [Option.getD_some] at hab
      have := (List.Nodup.getElem_inj_iff (nodup_others A.size U)).mp hab
      omega
  have hrel : ∀ i (t : List ℕ), (∀ a ∈ t, a < M) →
      (t ∈ (compress hU M hM).rel i ↔ t.map π ∈ A.rel i) := by
    intro i t ht
    constructor
    · intro h
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
      rw [List.map_map]
      rwa [List.map_congr_left (fun e he => by
        show π (rk U e) = e; rw [hπ, back_rk (hU.ent i u hu e he)]), List.map_id']
    · intro h
      refine Finset.mem_image.mpr ⟨_, h, ?_⟩
      rw [List.map_map]
      conv_rhs => rw [← List.map_id t]
      refine List.map_congr_left fun j hj => ?_
      have hjU : π j ∈ U := hU.ent i _ h _ (List.mem_map_of_mem hj)
      have hjc : j < U.card := by
        by_contra hc
        exact (mem_others.mp (back_ge_mem hU (by omega) (by have := ht j hj; omega))).2 hjU
      obtain ⟨e, he, rfl⟩ := rk_surj hjc
      show rk U (π (rk U e)) = rk U e
      rw [hπ, back_rk he]
  have hsat := (sat_map π (· < M) hinj hrel ψ ρ₁' hq hV).mp hs'
  refine ⟨hf, hns, π ∘ ρ₁', fun v hv => ?_, ?_⟩
  · rw [freeVars_exBlock] at hv
    simp only [Finset.mem_sdiff] at hv
    exact hπN _ (hV v hv.1)
  · rw [sat_exBlock]
    refine ⟨π ∘ ρ₁', fun _ _ => rfl, fun v hv => hπN _ (by rw [← hMsz]; exact h2 v hv), hsat⟩

/-- **Into the compressed structure**, for formulas of size at most `n`. -/
theorem models_compress (hU : Cover A U) {M : ℕ} (hM : U.card ≤ M)
    (hMn : min A.size (U.card + n) ≤ M) {φ : Formula} (hφ : IsSigma 1 φ) (hn : φ.size ≤ n)
    (h : Models A φ) : Models (compress hU M hM) φ := by
  obtain ⟨xs, ψ, rfl, hq⟩ : ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ ψ.IsQF := hφ
  obtain ⟨hf, hns, ρ, hρ, hs⟩ := h
  rw [sat_exBlock] at hs
  obtain ⟨ρ', h1, h2, hs'⟩ := hs
  set V := ψ.freeVars ∪ xs.toFinset with hVdef
  set S := V.image ρ' with hSdef
  have hVN : ∀ v ∈ V, ρ' v < A.size := by
    intro v hv
    rw [hVdef, Finset.mem_union, List.mem_toFinset] at hv
    by_cases hvx : v ∈ xs
    · exact h2 v hvx
    · rw [h1 v hvx]
      exact hρ v (by rw [freeVars_exBlock]; simp [hv.resolve_right hvx, hvx])
  have hSN : ∀ a ∈ S, a < A.size := by
    intro a ha; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha; exact hVN v hv
  have hScard : S.card ≤ n := by
    have e1 : S.card ≤ V.card := Finset.card_image_le
    have e2 : V.card ≤ ψ.freeVars.card + xs.toFinset.card := Finset.card_union_le _ _
    have e3 := List.toFinset_card_le xs
    have e4 := card_freeVars_le ψ
    rw [size_exBlock] at hn
    omega
  set T := (S \ U).toList with hT
  have hTlen : T.length ≤ min (A.size - U.card) n := by
    rw [hT, Finset.length_toList]
    refine le_min ?_ ?_
    · have hsub : S \ U ⊆ Finset.range A.size \ U := by
        intro a ha
        simp only [Finset.mem_sdiff, Finset.mem_range] at ha ⊢
        exact ⟨hSN a ha.1, ha.2⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_sdiff_of_subset (fun a ha => Finset.mem_range.mpr (hU.lt a ha)),
        Finset.card_range] at this
    · exact le_trans (Finset.card_le_card Finset.sdiff_subset) hScard
  have hcard := hU.card_le
  classical
  set h : ℕ → ℕ := fun a => if a ∈ U then rk U a else U.card + T.idxOf a with hh
  have hmemT : ∀ a ∈ S, a ∉ U → a ∈ T := by
    intro a ha haU; rw [hT, Finset.mem_toList, Finset.mem_sdiff]; exact ⟨ha, haU⟩
  have hlt : ∀ a ∈ S, h a < M := by
    intro a ha
    rw [hh]; simp only
    split_ifs with haU
    · have := rk_lt_card haU; omega
    · have := List.idxOf_lt_length_of_mem (hmemT a ha haU); omega
  have hinj : ∀ a b, a ∈ S → b ∈ S → h a = h b → a = b := by
    intro a b ha hb hab
    rw [hh] at hab; simp only at hab
    split_ifs at hab with haU hbU hbU
    · exact rk_injOn U haU hbU hab
    · have := rk_lt_card haU; omega
    · have := rk_lt_card hbU; omega
    · exact (List.idxOf_inj (hmemT a ha haU)).mp (by omega)
  have hrel : ∀ i (t : List ℕ), (∀ a ∈ t, a ∈ S) →
      (t ∈ A.rel i ↔ t.map h ∈ (compress hU M hM).rel i) := by
    intro i t ht
    constructor
    · intro htA
      refine Finset.mem_image.mpr ⟨t, htA, List.map_congr_left fun a ha => ?_⟩
      rw [hh]; simp only; rw [if_pos (hU.ent i t htA a ha)]
    · intro htC
      obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp htC
      have htU : ∀ a ∈ t, a ∈ U := by
        intro a ha
        by_contra haU
        have : h a ∈ t.map h := List.mem_map_of_mem ha
        rw [← hut] at this
        obtain ⟨e, he, hea⟩ := List.mem_map.mp this
        have := rk_lt_card (hU.ent i u hu e he)
        rw [hh] at hea; simp only at hea; rw [if_neg haU] at hea
        omega
      have : t.map h = t.map (rk U) := List.map_congr_left fun a ha => by
        rw [hh]; simp only; rw [if_pos (htU a ha)]
      rw [this] at hut
      have hlen : u.length = t.length := by rw [← List.length_map (f := rk U), hut, List.length_map]
      have : u = t := by
        apply List.ext_getElem hlen
        intro k h1 h2
        have := congrArg (fun l => l[k]?) hut
        simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
          List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at this
        exact rk_injOn U (hU.ent i u hu _ (List.getElem_mem h1)) (htU _ (List.getElem_mem h2)) this
      rwa [← this]
  have hS : ∀ v ∈ ψ.freeVars, ρ' v ∈ S := fun v hv =>
    Finset.mem_image_of_mem ρ' (Finset.mem_union_left _ hv)
  have hsat := (sat_map h (· ∈ S) hinj hrel ψ ρ' hq hS).mp hs'
  refine ⟨hf, hns, h ∘ ρ', fun v hv => ?_, ?_⟩
  · rw [freeVars_exBlock] at hv
    simp only [Finset.mem_sdiff] at hv
    exact hlt _ (hS v hv.1)
  · rw [sat_exBlock]
    refine ⟨h ∘ ρ', fun _ _ => rfl, fun v hv => hlt _ ?_, hsat⟩
    exact Finset.mem_image_of_mem ρ' (Finset.mem_union_right _ (List.mem_toFinset.mpr hv))

/-- **Compression keeps the `Σ_1`-formulas of size at most `n`.** -/
theorem models_compress_iff (hU : Cover A U) {M : ℕ} (hM : U.card ≤ M) (hMN : M ≤ A.size)
    (hMn : min A.size (U.card + n) ≤ M) {φ : Formula} (hφ : IsSigma 1 φ) (hn : φ.size ≤ n) :
    Models A φ ↔ Models (compress hU M hM) φ :=
  ⟨models_compress n hU hM hMn hφ hn, models_of_compress hU hM hMN hφ⟩

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress
