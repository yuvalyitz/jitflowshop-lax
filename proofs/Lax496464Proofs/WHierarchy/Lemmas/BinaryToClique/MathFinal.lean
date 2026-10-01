import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Tokenize
import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Remap
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Common
import Lax496464Proofs.WHierarchy.ComputableBounds
import Lax496464.WH_D05_BinaryToClique

/-!
# Σ₁[2] model checking to Clique: construction, correctness, parameter

On an instance `(A, ∃x̄ ψ)` of `p-MC(Σ₁[2])`: when `ψ` does not fit the vocabulary of `A`, the graph
has no vertex (and `k ≥ 2`); otherwise the graph of `Core` on the candidate values `elL x` has a
`k`-clique iff some assignment of candidate values satisfies `ψ` (`Core.clique_iff`), iff some
assignment of universe elements does (`Remap.exists_remap`), iff `A ⊨ ∃x̄ ψ`. The new parameter is
`k = 2 · (number of atoms) ≤ 2 |φ|`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.MathFinal

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax271696.VertexCover
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.FormulaData
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.StructWord Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Tokenize
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC

/-- The problem. -/
noncomputable abbrev Src : Lax888481.ParameterizedComplexity.Problem :=
  pMC {φ | IsSigma 1 φ ∧ φ.ArityAtMost 2}

/-! ### Syntax -/

theorem arityAtMost_exBlock (u : ℕ) (ψ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs ψ).ArityAtMost u ↔ ψ.ArityAtMost u
  | [] => Iff.rfl
  | _ :: xs => arityAtMost_exBlock u ψ xs

theorem fits_iff_atoms (ars : List ℕ) (s : ℕ) :
    ∀ ψ : Formula, ψ.IsQF → ψ.NoSetVar → (ψ.Fits ars s ↔ ∀ α ∈ atoms ψ, α.Fits ars s)
  | .rel i xs, _, _ => by simp [atoms]
  | .eq a b, _, _ => by simp [atoms, Formula.Fits]
  | .setVar _, _, hn => absurd hn id
  | .neg φ, hq, hn => fits_iff_atoms ars s φ hq hn
  | .and φ ψ, hq, hn => by
    simp only [Formula.Fits, atoms, List.mem_append, fits_iff_atoms ars s φ hq.1 hn.1,
      fits_iff_atoms ars s ψ hq.2 hn.2]
    constructor
    · rintro ⟨h1, h2⟩ α (h | h)
      · exact h1 α h
      · exact h2 α h
    · intro h; exact ⟨fun α hα => h α (Or.inl hα), fun α hα => h α (Or.inr hα)⟩
  | .or φ ψ, hq, hn => by
    simp only [Formula.Fits, atoms, List.mem_append, fits_iff_atoms ars s φ hq.1 hn.1,
      fits_iff_atoms ars s ψ hq.2 hn.2]
    constructor
    · rintro ⟨h1, h2⟩ α (h | h)
      · exact h1 α h
      · exact h2 α h
    · intro h; exact ⟨fun α hα => h α (Or.inl hα), fun α hα => h α (Or.inr hα)⟩
  | .ex _ _, hq, _ => absurd hq id
  | .all _ _, hq, _ => absurd hq id

theorem nA_le_size : ∀ ψ : Formula, nA ψ ≤ ψ.size
  | .rel _ _ => by simp [nA, Formula.size]
  | .eq _ _ => by simp [nA, Formula.size]
  | .setVar _ => by simp [nA]
  | .neg φ => by have := nA_le_size φ; simp [nA, Formula.size]; omega
  | .and φ ψ => by
    have := nA_le_size φ; have := nA_le_size ψ; simp [nA, Formula.size]; omega
  | .or φ ψ => by
    have := nA_le_size φ; have := nA_le_size ψ; simp [nA, Formula.size]; omega
  | .ex _ _ => by simp [nA]
  | .all _ _ => by simp [nA]

theorem mem_atoms : ∀ (ψ : Formula) {α : Formula}, α ∈ atoms ψ →
    (∃ i ys, α = .rel i ys) ∨ (∃ a b, α = .eq a b)
  | .rel i ys, α, h => by simp [atoms] at h; exact Or.inl ⟨i, ys, h⟩
  | .eq a b, α, h => by simp [atoms] at h; exact Or.inr ⟨a, b, h⟩
  | .setVar _, _, h => by simp [atoms] at h
  | .neg φ, _, h => mem_atoms φ h
  | .and φ ψ, _, h => by
    simp only [atoms, List.mem_append] at h
    rcases h with h | h
    · exact mem_atoms φ h
    · exact mem_atoms ψ h
  | .or φ ψ, _, h => by
    simp only [atoms, List.mem_append] at h
    rcases h with h | h
    · exact mem_atoms φ h
    · exact mem_atoms ψ h
  | .ex _ _, _, h => by simp [atoms] at h
  | .all _ _, _, h => by simp [atoms] at h

theorem atoms_mem_of_lt {ψ : Formula} {m : ℕ} (hm : m < nA ψ) : (atoms ψ).getD m dflt ∈ atoms ψ :=
  getD_mem (by rw [length_atoms]; exact hm)

theorem getD_map_of_lt {α : Type} {l : List α} {f : α → ℕ} {m : ℕ} {d : α} (h : m < l.length) :
    (l.map f).getD m 0 = f (l.getD m d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

/-! ### Models of a Σ₁ formula -/

/-- `A ⊨ ∃x̄ ψ(ȳ)` as a statement about `ψ`, when `ψ` has a free variable. -/
theorem models_exBlock_iff (A : Structure) (xs : List ℕ) (ψ : Formula)
    (hne : ψ.freeVars.Nonempty) :
    Models A (Formula.exBlock xs ψ) ↔ ψ.Fits A.arities 0 ∧ ψ.NoSetVar ∧
      ∃ ρ : ℕ → ℕ, (∀ v ∈ ψ.freeVars, ρ v < A.size) ∧ Sat A ∅ ψ ρ := by
  unfold Models
  rw [Lax496464Proofs.WHierarchy.Logic.SatFacts.fits_exBlock, Lax496464Proofs.WHierarchy.Logic.SatFacts.noSetVar_exBlock,
    Lax496464Proofs.WHierarchy.Logic.SatFacts.freeVars_exBlock]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨ρ, hρ, hs⟩
    rw [Lax496464Proofs.WHierarchy.Logic.SatFacts.sat_exBlock] at hs
    obtain ⟨ρ', h1, h2, h3⟩ := hs
    refine ⟨ρ', fun v hv => ?_, h3⟩
    by_cases hvx : v ∈ xs
    · exact h2 v hvx
    · rw [h1 v hvx]; exact hρ v (by simp [hv, hvx])
  · rintro ⟨ρ, hρ, hs⟩
    obtain ⟨v0, hv0⟩ := hne
    have hN : 0 < A.size := by have := hρ v0 hv0; omega
    refine ⟨ρ, fun v hv => hρ v (Finset.mem_sdiff.1 hv).1, ?_⟩
    rw [Lax496464Proofs.WHierarchy.Logic.SatFacts.sat_exBlock]
    refine ⟨fun v => if v ∈ xs ∧ v ∉ ψ.freeVars then 0 else ρ v, fun v hv => by simp [hv],
      fun v hv => ?_, ?_⟩
    · by_cases hf : v ∈ ψ.freeVars
      · simp only [hv, hf, not_true_eq_false, and_false, if_false]; exact hρ v hf
      · simp only [hv, hf, not_false_eq_true, and_self, if_true]; exact hN
    · refine (Lax496464Proofs.WHierarchy.Logic.SatFacts.sat_congr A ∅ ψ fun v hv => ?_).2 hs
      simp [hv]

/-! ### The domain -/

theorem domain_cases {x : List ℕ} (hx : x ∈ Src.Domain) :
    ∃ (y : List ℕ) (A : Structure) (xs : List ℕ) (ψ : Formula), Encodes y A ∧
      x = y ++ (Formula.exBlock xs ψ).encode ∧ ψ.IsQF ∧ ψ.NoSetVar ∧ ψ.ArityAtMost 2 ∧
      EncodesMC x A (Formula.exBlock xs ψ) := by
  obtain ⟨A, φ, ⟨y, hy, rfl⟩, ⟨⟨xs, ψ, rfl, hq⟩, har⟩, hn⟩ := hx
  exact ⟨y, A, xs, ψ, hy, rfl, hq, (Lax496464Proofs.WHierarchy.Logic.SatFacts.noSetVar_exBlock ψ xs).1 hn,
    (arityAtMost_exBlock 2 ψ xs).1 har, ⟨y, hy, rfl⟩⟩

/-! ### The graph encodes -/

theorem reduce_encodes (x : List ℕ) :
    EncodesParamInstance (reduce x) (NGX x) (graph (paramsX x) (NGX x)) (kX x) :=
  ⟨_, rfl, CsrWord.encodesGraph fun _ _ => Iff.rfl⟩

theorem clique_reduce_iff (x : List ℕ) :
    Clique.Yes (reduce x) ↔
      ∃ s : Finset (Fin (NGX x)), (graph (paramsX x) (NGX x)).IsNClique (kX x) s :=
  Common.clique_yes_iff (reduce_encodes x)

theorem reduce_mem_domain (x : List ℕ) : reduce x ∈ Clique.Domain :=
  ⟨_, _, _, reduce_encodes x⟩

/-! ### The data of the word, on an instance -/

section Instance

variable {x y : List ℕ} {A : Structure} {xs : List ℕ} {ψ : Formula}

/-- The standing hypotheses. -/
structure Inst (x y : List ℕ) (A : Structure) (xs : List ℕ) (ψ : Formula) : Prop where
  hy : Encodes y A
  hx : x = y ++ (Formula.exBlock xs ψ).encode
  hq : ψ.IsQF
  hn : ψ.NoSetVar
  ha : ψ.ArityAtMost 2

theorem Inst.tok_eq (h : Inst x y A xs ψ) :
    tok x = TS.mk x.length (toks ψ 0) (vsOf ψ) ((atoms ψ).map (abA x)) ((atoms ψ).map (arA x))
      (if fitsB x ψ then 1 else 0) := Tokenize.tok_eq h.hy h.hx h.hq h.hn h.ha

theorem Inst.qX_eq (h : Inst x y A xs ψ) : qX x = nA ψ := by
  unfold qX; rw [h.tok_eq]; simp [length_atoms]

theorem Inst.kX_eq (h : Inst x y A xs ψ) : kX x = 2 * nA ψ := by unfold kX; rw [h.qX_eq]

theorem Inst.vs_eq (h : Inst x y A xs ψ) : (tok x).vs = vsOf ψ := by rw [h.tok_eq]

theorem Inst.fl_eq (h : Inst x y A xs ψ) : (tok x).fl = if fitsB x ψ then 1 else 0 := by rw [h.tok_eq]

theorem Inst.okv_eq (h : Inst x y A xs ψ) (c : ℕ) : okv x c = valN ψ c 0 := by
  unfold okv evalNd; rw [h.tok_eq]
  simp only
  rw [show toks ψ 0 = toks ψ 0 ++ [] from (List.append_nil _).symm, List.foldr_append,
    List.foldr_nil, foldr_toks c ψ h.hq h.hn 0 []]
  rfl

theorem Inst.ar_eq (h : Inst x y A xs ψ) {m : ℕ} (hm : m < nA ψ) :
    (tok x).ar.getD m 0 = arA x ((atoms ψ).getD m dflt) := by
  rw [h.tok_eq]; exact getD_map_of_lt (by rw [length_atoms]; exact hm)

theorem Inst.ab_eq (h : Inst x y A xs ψ) {m : ℕ} (hm : m < nA ψ) :
    (tok x).ab.getD m 0 = abA x ((atoms ψ).getD m dflt) := by
  rw [h.tok_eq]; exact getD_map_of_lt (by rw [length_atoms]; exact hm)

theorem Inst.sw (h : Inst x y A xs ψ) :
    ∃ blocks, SW x y (Formula.exBlock xs ψ).encode A blocks := by
  obtain ⟨b, hb⟩ := SW.of_encodes (rest := (Formula.exBlock xs ψ).encode) h.hy
  rw [← h.hx] at hb
  exact ⟨b, hb⟩

theorem Inst.fitA_iff (h : Inst x y A xs ψ) {α : Formula} (hα : α ∈ atoms ψ) :
    fitA x α = true ↔ α.Fits A.arities 0 := by
  obtain ⟨blocks, hsw⟩ := h.sw
  rcases mem_atoms ψ hα with ⟨i, ys, rfl⟩ | ⟨a, b, rfl⟩
  · simp only [fitA, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Formula.Fits, hsw.sX_eq]
    constructor
    · rintro ⟨hi, hl⟩; exact ⟨hi, by rw [hl, hsw.rd_arity hi]⟩
    · rintro ⟨hi, hl⟩; exact ⟨hi, by rw [hl, hsw.rd_arity hi]⟩
  · simp [fitA, Formula.Fits]

theorem Inst.fitsB_iff (h : Inst x y A xs ψ) : fitsB x ψ = true ↔ ψ.Fits A.arities 0 := by
  rw [fits_iff_atoms _ _ ψ h.hq h.hn, fitsB, List.all_eq_true]
  exact forall₂_congr fun α hα => h.fitA_iff hα

theorem Inst.good (h : Inst x y A xs ψ) (hf : ψ.Fits A.arities 0) : ∀ α ∈ atoms ψ, GoodAtom α :=
  goodAtom_of_fits A.arities A.arity_pos ψ h.hq h.hn hf h.ha

open Classical in
/-- **The atom test on the word is the atom.** -/
theorem Inst.atm (h : Inst x y A xs ψ) (hf : ψ.Fits A.arities 0) {m : ℕ} (hm : m < nA ψ)
    (ρ : ℕ → ℕ) :
    atomT x m (ρ ((vsOf ψ).getD (2 * m) 0)) (ρ ((vsOf ψ).getD (2 * m + 1) 0)) =
      if Sat A ∅ ((atoms ψ).getD m dflt) ρ then 1 else 0 := by
  obtain ⟨blocks, hsw⟩ := h.sw
  have hmem := atoms_mem_of_lt hm
  have hg : GoodAtom ((atoms ψ).getD m dflt) := h.good hf _ hmem
  have hfa : ((atoms ψ).getD m dflt).Fits A.arities 0 :=
    (fits_iff_atoms _ _ ψ h.hq h.hn).1 hf _ hmem
  obtain ⟨h1, h2⟩ := vsOf_getD ψ hm
  rw [h1, h2]
  unfold atomT
  rw [h.ar_eq hm, h.ab_eq hm]
  generalize (atoms ψ).getD m dflt = α at hg hfa ⊢
  cases α with
  | rel i ys =>
    obtain ⟨hi, hl⟩ := hfa
    obtain ⟨hg1, hg2⟩ := hg
    simp only [arA, abA, hsw.sX_eq, if_pos hi, hsw.rd_arity hi]
    rw [if_neg (by omega)]
    have ha12 : A.arities.getD i 0 = 1 ∨ A.arities.getD i 0 = 2 := by omega
    have key := hsw.memX_iff hi ha12 (ρ (apair (.rel i ys)).1) (ρ (apair (.rel i ys)).2)
    have htup : (if A.arities.getD i 0 = 1 then [ρ (apair (.rel i ys)).1]
        else [ρ (apair (.rel i ys)).1, ρ (apair (.rel i ys)).2]) = ys.map ρ := by
      rw [← hl]
      match ys, hg1, hg2 with
      | [a], _, _ => simp [apair]
      | [a, b], _, _ => simp [apair]
    rw [htup] at key
    have hsat : Sat A ∅ (.rel i ys) ρ ↔ ys.map ρ ∈ A.rel i := Iff.rfl
    by_cases hm' : memX x (hp x i) (A.arities.getD i 0) (ρ (apair (.rel i ys)).1)
        (ρ (apair (.rel i ys)).2) = true
    · rw [if_pos hm', if_pos (hsat.2 (key.1 hm'))]
    · rw [if_neg hm', if_neg (fun hs => hm' (key.2 (hsat.1 hs)))]
  | eq a b =>
    simp only [arA, abA, if_true]
    have hsat : Sat A ∅ (.eq a b) ρ ↔ ρ a = ρ b := Iff.rfl
    by_cases he : ρ a = ρ b
    · have hs := hsat.2 he
      simp only [apair]; simp [he, hs]
    · have hs : ¬ Sat A ∅ (.eq a b) ρ := fun hs => he (hsat.1 hs)
      simp only [apair]; simp [he, hs]
  | setVar _ => exact absurd hg id
  | neg _ => exact absurd hg id
  | and _ _ => exact absurd hg id
  | or _ _ => exact absurd hg id
  | ex _ _ => exact absurd hg id
  | all _ _ => exact absurd hg id

open Classical in
/-- **The hypotheses of the clique theorem hold.** -/
theorem Inst.hyp (h : Inst x y A xs ψ) (hf : ψ.Fits A.arities 0) :
    Hyp (paramsX x) (qX x) (Sat A ∅ ψ) (fun m => Sat A ∅ ((atoms ψ).getD m dflt)) ↑ψ.freeVars where
  k_eq := rfl
  q_pos := by rw [h.qX_eq]; exact nA_pos ψ h.hq h.hn
  atm_eq m hm ρ := by
    rw [h.qX_eq] at hm
    show atomT x m (ρ ((tok x).vs.getD (2 * m) 0)) (ρ ((tok x).vs.getD (2 * m + 1) 0)) = _
    rw [h.vs_eq]; exact h.atm hf hm ρ
  ok_iff c _ ρ hpat := by
    show okv x c = 1 ↔ _
    rw [h.okv_eq, valN]
    have he := sat_iff_evalPat A ∅ ρ ψ h.hq h.hn (fun m => bitv c m == 1) 0 fun m hm => by
      rw [Nat.zero_add, beq_iff_eq]; exact hpat m (by rw [h.qX_eq]; exact hm)
    by_cases hv : evalPat ψ (fun m => bitv c m == 1) 0 = true
    · rw [if_pos hv]; exact ⟨fun _ => he.1 hv, fun _ => rfl⟩
    · rw [if_neg hv]; exact ⟨fun h0 => absurd h0 (by decide), fun hs => absurd (he.2 hs) hv⟩
  vs_mem r hr := by
    show (tok x).vs.getD r 0 ∈ (↑ψ.freeVars : Set ℕ)
    rw [h.vs_eq, Finset.mem_coe]
    have hr' : r < 2 * nA ψ := by have : (paramsX x).k = kX x := rfl; rw [this, h.kX_eq] at hr; exact hr
    exact vsOf_mem_freeVars ψ h.hq h.hn (h.good hf) hr'
  mem_vs v hv := by
    obtain ⟨r, hr, hrv⟩ := freeVars_mem_vsOf ψ h.hq h.hn (h.good hf) (Finset.mem_coe.1 hv)
    refine ⟨r, ?_, ?_⟩
    · show r < kX x; rw [h.kX_eq]; exact hr
    · show (tok x).vs.getD r 0 = v; rw [h.vs_eq]; exact hrv

theorem mem_elL_lt {x : List ℕ} {v : ℕ} (hv : v ∈ elL x) : v < NsX x := by
  unfold elL at hv
  rcases List.mem_append.1 hv with h | h
  · simpa using (List.mem_filter.1 h).2
  · have := List.mem_range.1 h
    unfold limX at this
    split_ifs at this <;> omega

/-- **Correctness.** -/
theorem Inst.models_iff (h : Inst x y A xs ψ) :
    Models A (Formula.exBlock xs ψ) ↔ Clique.Yes (reduce x) := by
  rw [clique_reduce_iff]
  by_cases hf : ψ.Fits A.arities 0
  · obtain ⟨blocks, hsw⟩ := h.sw
    have hq1 := nA_pos ψ h.hq h.hn
    have hne : ψ.freeVars.Nonempty :=
      ⟨_, vsOf_mem_freeVars ψ h.hq h.hn (h.good hf) (r := 0) (by omega)⟩
    rw [models_exBlock_iff A xs ψ hne]
    have hfl : (tok x).fl = 1 := by rw [h.fl_eq, if_pos ((h.fitsB_iff).2 hf)]
    have hneX : (paramsX x).ne = (elL x).length := by
      show neX x = _; unfold neX; rw [if_pos hfl]
    have hcore := clique_iff (h.hyp hf)
    change (_ ↔ ∃ s : Finset (Fin (2 ^ qX x * ((paramsX x).ne * (paramsX x).k))),
      (graph (paramsX x) _).IsNClique (paramsX x).k s)
    rw [hcore]
    simp only [hf, h.hn, true_and]
    have hidx : ∀ v, (∃ e < (paramsX x).ne, (paramsX x).E e = v) ↔ v ∈ elL x := by
      intro v
      rw [hneX]
      constructor
      · rintro ⟨e, he, rfl⟩
        show (elL x).getD e 0 ∈ elL x
        exact getD_mem he
      · intro hv
        obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hv
        exact ⟨e, he, by show (elL x).getD e 0 = _; rw [List.getD_eq_getElem _ _ he]⟩
    have hN := hsw.NsX_eq
    constructor
    · rintro ⟨ρ, hρ, hs⟩
      obtain ⟨ρ', hρ', hs'⟩ := Remap.exists_remap A ψ h.hq (x.length + kX x) {v | v ∈ elL x}
        x.toFinset (fun i t ht a ha => List.mem_toFinset.2 (hsw.mem_of_tuple ht ha))
        (fun a ha haN => by
          show a ∈ elL x
          unfold elL
          refine List.mem_append.2 (Or.inl (List.mem_filter.2 ⟨List.mem_toFinset.1 ha, ?_⟩))
          rw [hN]; simpa using haN)
        (fun a haN haM => by
          show a ∈ elL x
          unfold elL
          refine List.mem_append.2 (Or.inr (List.mem_range.2 ?_))
          unfold limX; rw [hN]; split_ifs <;> omega)
        (by
          have h1 := List.toFinset_card_le x
          have h2 : ψ.freeVars.card ≤ (vsOf ψ).toFinset.card := by
            apply Finset.card_le_card
            intro v hv
            obtain ⟨r, _, hrv⟩ := freeVars_mem_vsOf ψ h.hq h.hn (h.good hf) hv
            rw [← hrv]
            exact List.mem_toFinset.2 (getD_mem (by rw [length_vsOf]; omega))
          have h3 := List.toFinset_card_le (vsOf ψ)
          rw [length_vsOf] at h3
          rw [h.kX_eq]; omega)
        hρ hs
      exact ⟨ρ', fun v hv => (hidx _).2 (hρ' v hv), hs'⟩
    · rintro ⟨ρ, hρ, hs⟩
      refine ⟨ρ, fun v hv => ?_, hs⟩
      rw [← hN]
      exact mem_elL_lt ((hidx _).1 (hρ v hv))
  · have hL : ¬ Models A (Formula.exBlock xs ψ) := fun hm =>
      hf ((Lax496464Proofs.WHierarchy.Logic.SatFacts.fits_exBlock _ _ ψ xs).1 hm.1)
    simp only [hL, false_iff]
    rintro ⟨s, hs⟩
    have hfl : (tok x).fl = 0 := by
      rw [h.fl_eq, if_neg (fun hb => hf ((h.fitsB_iff).1 hb))]
    have hNG : NGX x = 0 := by
      unfold NGX neX; rw [if_neg (by rw [hfl]; decide)]; simp
    have hcard := hs.card_eq
    have hle : s.card ≤ NGX x := by simpa using Finset.card_le_univ s
    have hk := h.kX_eq
    have hq1 := nA_pos ψ h.hq h.hn
    omega

end Instance

/-! ### The reduction -/

theorem reduce_isReduction : IsReduction Src Clique reduce where
  maps_domain x _ := reduce_mem_domain x
  correct x hx := by
    obtain ⟨y, A, xs, ψ, hy, hxe, hq, hn, ha, hmc⟩ := domain_cases hx
    rw [Lax496464Proofs.WHierarchy.Logic.Words.pMC_yes_iff _ hmc]
    exact (Inst.models_iff ⟨hy, hxe, hq, hn, ha⟩)

theorem reduce_param_le {x : List ℕ} (hx : x ∈ Src.Domain) :
    Clique.param (reduce x) ≤ 2 * Src.param x := by
  obtain ⟨y, A, xs, ψ, hy, hxe, hq, hn, ha, hmc⟩ := domain_cases hx
  have hI : Inst x y A xs ψ := ⟨hy, hxe, hq, hn, ha⟩
  show (reduce x).getLast?.getD 0 ≤ 2 * mcParam x
  rw [Lax496464Proofs.WHierarchy.Logic.Words.mcParam_eq hmc, Lax496464Proofs.WHierarchy.Logic.SatFacts.size_exBlock]
  have h1 : (reduce x).getLast?.getD 0 = kX x := by simp [reduce]
  rw [h1, hI.kX_eq]
  have := nA_le_size ψ
  omega

theorem reduce_paramBounded : ParamBounded Src Clique reduce :=
  ⟨fun m => 2 * m, Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const 2)
    Computable.id, fun _ hx => reduce_param_le hx⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.MathFinal
