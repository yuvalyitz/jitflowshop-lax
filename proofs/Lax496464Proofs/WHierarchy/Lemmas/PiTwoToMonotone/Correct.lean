import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Pi2

/-! # The formula is `W`-satisfiable iff a witness of weight `k` exists

`witness_iff_weightSat`: for a word of `(A, k)` that fits, `alphaW` has a satisfying assignment of
weight `W` exactly when `A ⊨ φ(S)` for some `S` of `k` tuples. The chain:

1. `Pi2.witness_iff`: a witness among the elements of `U` with the `∀∃` condition over `U`;
2. `allEx_iff_digits`: the assignments of positions into `U` are the digit pairs `(za, zb)`;
3. `exists_S_iff`: sets of `k` tuples over `U` are increasing lists of `k` codes below `n^s`;
4. `Cnf.weightSat_iff`, with `good` sound for consistent blocks (`Eval.ev_sound`,
   `Blocks.dec_sound`) and complete for the canonical block deciding the `X`-atoms
   (`Blocks.dec_complete`, `Eval.ev_complete`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Correct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Pi2 Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Perm

/-! ### Codes of tuples over a list without repetition -/

section Code
variable {Ul : List ℕ}

theorem getD_idxOf' {a : ℕ} (h : a ∈ Ul) : Ul.getD (Ul.idxOf a) 0 = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h)]
  simp

theorem idxOf_getD (hnd : Ul.Nodup) {d : ℕ} (h : d < Ul.length) : Ul.idxOf (Ul.getD d 0) = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnd d h

theorem getD_mem' {d : ℕ} (h : d < Ul.length) : Ul.getD d 0 ∈ Ul := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- The code of a tuple of elements of `Ul`. -/
def enc (Ul t : List ℕ) : ℕ := codeOf Ul.length (t.map Ul.idxOf)

/-- The tuple of a code. -/
def tupOf (Ul : List ℕ) (s c : ℕ) : List ℕ := (digits Ul.length s c).map fun d => Ul.getD d 0

theorem enc_lt {t : List ℕ} (ht : ∀ a ∈ t, a ∈ Ul) : enc Ul t < Ul.length ^ t.length := by
  have := codeOf_lt (n := Ul.length) (t.map Ul.idxOf) fun d hd => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact List.idxOf_lt_length_iff.mpr (ht a ha)
  unfold enc; simpa using this

theorem map_idxOf_getD {t : List ℕ} (ht : ∀ a ∈ t, a ∈ Ul) :
    (t.map Ul.idxOf).map (fun d => Ul.getD d 0) = t := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id t]
  exact List.map_congr_left fun a ha => getD_idxOf' (ht a ha)

theorem map_getD_idxOf (hnd : Ul.Nodup) {ds : List ℕ} (hd : ∀ d ∈ ds, d < Ul.length) :
    (ds.map fun d => Ul.getD d 0).map Ul.idxOf = ds := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ds]
  exact List.map_congr_left fun d h => idxOf_getD hnd (hd d h)

theorem digits_lt' {s c : ℕ} (hc : c < Ul.length ^ s) : ∀ d ∈ digits Ul.length s c, d < Ul.length := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [digits]
  · have : 0 < Ul.length := by
      rcases Nat.eq_zero_or_pos Ul.length with h | h
      · rw [h, zero_pow (by omega)] at hc; omega
      · exact h
    exact digits_lt this s c

theorem tupOf_mem {s c : ℕ} (hc : c < Ul.length ^ s) : ∀ a ∈ tupOf Ul s c, a ∈ Ul := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  exact getD_mem' (digits_lt' hc d hd)

theorem length_tupOf (s c : ℕ) : (tupOf Ul s c).length = s := by simp [tupOf]

theorem tupOf_enc {t : List ℕ} (ht : ∀ a ∈ t, a ∈ Ul) :
    tupOf Ul t.length (enc Ul t) = t := by
  unfold tupOf enc
  have hd : ∀ d ∈ t.map Ul.idxOf, d < Ul.length := fun d hd => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact List.idxOf_lt_length_iff.mpr (ht a ha)
  have := digits_codeOf (t.map Ul.idxOf) hd
  rw [List.length_map] at this
  rw [this, map_idxOf_getD ht]

theorem tupOf_inj (hnd : Ul.Nodup) {s c c' : ℕ} (hc : c < Ul.length ^ s)
    (hc' : c' < Ul.length ^ s) (h : tupOf Ul s c = tupOf Ul s c') : c = c' := by
  have h1 := congrArg (List.map Ul.idxOf) h
  unfold tupOf at h1
  rw [map_getD_idxOf hnd (digits_lt' hc), map_getD_idxOf hnd (digits_lt' hc')] at h1
  exact digits_inj hc hc' h1

theorem enc_inj {t t' : List ℕ} (ht : ∀ a ∈ t, a ∈ Ul) (ht' : ∀ a ∈ t', a ∈ Ul)
    (hl : t.length = t'.length) (h : enc Ul t = enc Ul t') : t = t' := by
  rw [← tupOf_enc ht, ← tupOf_enc ht', h, hl]

end Code

theorem getD_digits_lt {n r z j : ℕ} (hz : z < n ^ r) (hj : j < r) : (digits n r z).getD j 0 < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_pow (by omega)] at hz; omega
    · exact h
  have hmem : (digits n r z).getD j 0 ∈ digits n r z := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
    exact List.getElem_mem _
  exact digits_lt hn _ _ _ hmem

/-! ### The digits of the positions -/

section Ds
variable {Dt : Data} {x : List ℕ}

theorem dsOf_ex {za zb j : ℕ} (hj : j < Dt.q) :
    (dsOf Dt x za zb).getD j 0 = (digits (nU Dt x) Dt.q zb).getD j 0 := by
  unfold dsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj),
    ← List.getD_eq_getElem?_getD]

theorem dsOf_un {za zb j : ℕ} (hj : Dt.q ≤ j) :
    (dsOf Dt x za zb).getD j 0 = (digits (nU Dt x) Dt.p za).getD (j - Dt.q) 0 := by
  unfold dsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hj),
    ← List.getD_eq_getElem?_getD, length_digits]

theorem dsOf_lt {za zb j : ℕ} (hza : za < nU Dt x ^ Dt.p) (hzb : zb < nU Dt x ^ Dt.q)
    (hj : j < Dt.r) : (dsOf Dt x za zb).getD j 0 < nU Dt x := by
  by_cases h : j < Dt.q
  · rw [dsOf_ex h]; exact getD_digits_lt hzb h
  · rw [dsOf_un (by omega)]; exact getD_digits_lt hza (by unfold Data.r at hj; omega)

end Ds

/-! ### Free variables of the renamed formula -/

theorem exists_atom_of_free : ∀ (ψ : Formula), ψ.IsQF → ∀ v ∈ ψ.freeVars,
    ∃ a ∈ atoms ψ, v ∈ a.freeVars
  | .rel i xs, _, v, hv => ⟨_, by simp [atoms], hv⟩
  | .setVar xs, _, v, hv => ⟨_, by simp [atoms], hv⟩
  | .eq a b, _, v, hv => ⟨_, by simp [atoms], hv⟩
  | .neg φ, hq, v, hv => by
    obtain ⟨a, ha, h⟩ := exists_atom_of_free φ hq v (by simpa [Formula.freeVars] using hv)
    exact ⟨a, by simpa [atoms] using ha, h⟩
  | .and φ ψ, hq, v, hv => by
    simp only [Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨a, ha, h⟩ := exists_atom_of_free φ hq.1 v hv; exact ⟨a, by simp [atoms, ha], h⟩
    · obtain ⟨a, ha, h⟩ := exists_atom_of_free ψ hq.2 v hv; exact ⟨a, by simp [atoms, ha], h⟩
  | .or φ ψ, hq, v, hv => by
    simp only [Formula.freeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨a, ha, h⟩ := exists_atom_of_free φ hq.1 v hv; exact ⟨a, by simp [atoms, ha], h⟩
    · obtain ⟨a, ha, h⟩ := exists_atom_of_free ψ hq.2 v hv; exact ⟨a, by simp [atoms, ha], h⟩
  | .ex _ _, hq, _, _ => absurd hq (by simp [Formula.IsQF])
  | .all _ _, hq, _, _ => absurd hq (by simp [Formula.IsQF])

section Main
variable {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
  (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys)
include hq hv

theorem free_lt {j : ℕ} (hj : j ∈ (dataOf xs ys ψ s).ψ.freeVars) : j < (dataOf xs ys ψ s).r := by
  obtain ⟨a, ha, h⟩ := exists_atom_of_free _ (isQF_rename _ ψ hq) j hj
  exact pos_lt hq hv a ha j h

omit hq hv in
/-- **Assignments into `U` are digit pairs.** -/
theorem allEx_iff_digits (Dt : Data) (hfree : ∀ j ∈ Dt.ψ.freeVars, j < Dt.r)
    (x : List ℕ) (A : Structure) (S : Set (List ℕ)) :
    AllEx Dt A S (· ∈ (U Dt x).toFinset) ↔
      ∀ za < nU Dt x ^ Dt.p, ∃ zb < nU Dt x ^ Dt.q,
          Sat A S Dt.ψ (elemOf Dt x (dsOf Dt x za zb)) := by
  set Ul := U Dt x with hUl
  have hcongr : ∀ {ε ε' : ℕ → ℕ}, (∀ j < Dt.r, ε j = ε' j) →
      (Sat A S Dt.ψ ε ↔ Sat A S Dt.ψ ε') := fun h =>
    sat_congr A S Dt.ψ fun j hj => h j (hfree j hj)
  constructor
  · intro h za hza
    obtain ⟨ε', h1, h2, h3⟩ := h (elemOf Dt x (dsOf Dt x za 0)) fun j hj1 hj2 => by
      show _ ∈ Ul.toFinset
      rw [List.mem_toFinset]
      unfold elemOf
      rw [dsOf_un hj1]
      exact getD_mem' (getD_digits_lt hza (by unfold Data.r at hj2; omega))
    set dl := (List.range Dt.q).map fun j => Ul.idxOf (ε' j) with hdl
    have hdlt : ∀ d ∈ dl, d < Ul.length := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
      exact List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp (h2 j (List.mem_range.mp hj)))
    have hlen : dl.length = Dt.q := by simp [hdl]
    have hzb := codeOf_lt dl hdlt
    rw [hlen] at hzb
    refine ⟨codeOf Ul.length dl, hzb, (hcongr fun j hj => ?_).mp h3⟩
    by_cases hjq : j < Dt.q
    · unfold elemOf
      rw [dsOf_ex hjq]
      have hdig := digits_codeOf dl hdlt
      rw [hlen] at hdig
      rw [hdig]
      have : dl.getD j 0 = Ul.idxOf (ε' j) := by
        simp [hdl, List.getD_eq_getElem?_getD, List.getElem?_range hjq]
      rw [this]
      exact (getD_idxOf' (List.mem_toFinset.mp (h2 j hjq))).symm
    · rw [h1 j (by omega) hj]
      unfold elemOf
      rw [dsOf_un (by omega), dsOf_un (by omega)]
  · intro h ε hε
    set dl := (List.range Dt.p).map fun i => Ul.idxOf (ε (Dt.q + i)) with hdl
    have hdlt : ∀ d ∈ dl, d < Ul.length := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      exact List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp
        (hε _ (by omega) (by unfold Data.r; have := List.mem_range.mp hi; omega)))
    have hlen : dl.length = Dt.p := by simp [hdl]
    have hza := codeOf_lt dl hdlt
    rw [hlen] at hza
    obtain ⟨zb, hzb, hsat⟩ := h _ hza
    refine ⟨elemOf Dt x (dsOf Dt x (codeOf Ul.length dl) zb), fun j hj1 hj2 => ?_,
      fun j hj => ?_, hsat⟩
    · unfold elemOf
      rw [dsOf_un hj1]
      have hdig := digits_codeOf dl hdlt
      rw [hlen] at hdig
      rw [hdig]
      have hi : j - Dt.q < Dt.p := by unfold Data.r at hj2; omega
      have : dl.getD (j - Dt.q) 0 = Ul.idxOf (ε j) := by
        simp [hdl, List.getD_eq_getElem?_getD, List.getElem?_range hi]
        congr 2; omega
      rw [this]
      exact getD_idxOf' (List.mem_toFinset.mp (hε j hj1 hj2))
    · show _ ∈ Ul.toFinset
      rw [List.mem_toFinset]
      unfold elemOf
      rw [dsOf_ex hj]
      exact getD_mem' (getD_digits_lt hzb hj)

/-- The set of tuples of a list of codes. -/
def Sdec (Ul : List ℕ) (s : ℕ) (t : List ℕ) : Finset (List ℕ) := (t.map (tupOf Ul s)).toFinset

omit hq hv in
/-- **Sets of `k` tuples over `U` are increasing lists of `k` codes.** -/
theorem exists_S_iff (Ul : List ℕ) (hnd : Ul.Nodup) (k : ℕ) (P : Set (List ℕ) → Prop) :
    (∃ S : Finset (List ℕ), S.card = k ∧ (∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a ∈ Ul) ∧ P ↑S) ↔
      ∃ t, Valid k (Ul.length ^ s) t ∧ P ↑(Sdec Ul s t) := by
  constructor
  · rintro ⟨S, hcard, htup, hP⟩
    set T := S.image (enc Ul) with hT
    have hTlt : ∀ c ∈ T, c < Ul.length ^ s := by
      intro c hc
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hc
      have := enc_lt (htup τ hτ).2; rwa [(htup τ hτ).1] at this
    have hTc : T.card = k := by
      rw [hT, Finset.card_image_of_injOn fun τ hτ τ' hτ' h =>
        enc_inj (htup τ hτ).2 (htup τ' hτ').2 (by rw [(htup τ hτ).1, (htup τ' hτ').1]) h]
      exact hcard
    have hv := valid_sort T hTlt
    rw [hTc] at hv
    refine ⟨_, hv, ?_⟩
    have hSd : Sdec Ul s (T.sort (· ≤ ·)) = S := by
      ext τ
      simp only [Sdec, List.mem_toFinset, List.mem_map, mem_sort_iff, hT, Finset.mem_image]
      constructor
      · rintro ⟨c, ⟨τ', hτ', rfl⟩, rfl⟩
        have := tupOf_enc (htup τ' hτ').2
        rw [(htup τ' hτ').1] at this
        rw [this]; exact hτ'
      · intro hτ
        refine ⟨enc Ul τ, ⟨τ, hτ, rfl⟩, ?_⟩
        have := tupOf_enc (htup τ hτ).2
        rwa [(htup τ hτ).1] at this
    rw [hSd]; exact hP
  · rintro ⟨t, ht, hP⟩
    refine ⟨Sdec Ul s t, ?_, fun τ hτ => ?_, hP⟩
    · unfold Sdec
      rw [List.toFinset_card_of_nodup, List.length_map, ht.len]
      refine List.Nodup.map_on (fun c hc c' hc' h => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := ht.mem_iff.mp hc
        obtain ⟨i', hi', rfl⟩ := ht.mem_iff.mp hc'
        exact tupOf_inj hnd (ht.lt i hi) (ht.lt i' hi') h
      · refine List.nodup_iff_injective_get.mpr fun a b hab => ?_
        have ha : (a : ℕ) < k := lt_of_lt_of_eq a.2 ht.len
        have hb : (b : ℕ) < k := lt_of_lt_of_eq b.2 ht.len
        have e1 : t.get a = g t a := by
          simp [g, List.getD_eq_getElem?_getD]
        have e2 : t.get b = g t b := by
          simp [g, List.getD_eq_getElem?_getD]
        rw [e1, e2] at hab
        exact Fin.ext (ht.inj ha hb hab)
    · simp only [Sdec, List.mem_toFinset, List.mem_map] at hτ
      obtain ⟨c, hc, rfl⟩ := hτ
      obtain ⟨i, hi, rfl⟩ := ht.mem_iff.mp hc
      exact ⟨length_tupOf _ _, tupOf_mem (ht.lt i hi)⟩

omit hq hv in
/-- The code of the tuple of an `X`-atom is in `t` iff the tuple is in `Sdec t`. -/
theorem code_mem_iff {Dt : Data} {x : List ℕ} {t : List ℕ} {za zb : ℕ} {kk : ℕ}
    (ht : Valid kk (nU Dt x ^ Dt.s) t)
    (hza : za < nU Dt x ^ Dt.p) (hzb : zb < nU Dt x ^ Dt.q)
    {js : List ℕ} (hjs : js.length = Dt.s) (hjr : ∀ j ∈ js, j < Dt.r) :
    codeW Dt x (dsOf Dt x za zb) js ∈ t ↔
      js.map (elemOf Dt x (dsOf Dt x za zb)) ∈ Sdec (U Dt x) Dt.s t := by
  set Ul := U Dt x with hUl
  set ds := dsOf Dt x za zb with hds
  have hnd : Ul.Nodup := UW_nodup _ _ _
  have hdl : ∀ d ∈ js.map (fun j => ds.getD j 0), d < Ul.length := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact dsOf_lt hza hzb (hjr j hj)
  have hclt : codeW Dt x ds js < Ul.length ^ Dt.s := by
    have := codeOf_lt _ hdl
    rwa [List.length_map, hjs] at this
  have htup : tupOf Ul Dt.s (codeW Dt x ds js) = js.map (elemOf Dt x ds) := by
    unfold tupOf codeW
    have := digits_codeOf _ hdl
    rw [List.length_map, hjs] at this
    rw [this, List.map_map]; rfl
  rw [← htup]
  simp only [Sdec, List.mem_toFinset, List.mem_map]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨c, hc, he⟩
    obtain ⟨i, hi, rfl⟩ := ht.mem_iff.mp hc
    rwa [← tupOf_inj hnd (ht.lt i hi) hclt he]

/-- **The formula is `W`-satisfiable iff a witness of weight `k` exists.** -/
theorem witness_iff_weightSat {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)}
    (he : Enc x A k bl) (hfit : fitW (dataOf xs ys ψ s) x) :
    Witness A (Formula.allBlock xs (Formula.exBlock ys ψ)) s k ↔
      Lax496464.WH_C3_WeightedSat.WeightSat (alphaW (dataOf xs ys ψ s) x)
        (par (dataOf xs ys ψ s) x).W := by
  set Dt := dataOf xs ys ψ s with hDt
  have hnd : (U Dt x).Nodup := UW_nodup _ _ _
  have hfits : ψ.Fits A.arities s := (fitW_iff he xs ys ψ s).mp hfit
  have hDs : Dt.s = s := rfl
  have hk : kW x = k := he.kW_eq
  -- the room in `U`
  have hR : Room A (U Dt x).toFinset x.toFinset (LW Dt.s Dt.r x) :=
    ⟨fun u hu => by rw [← he.NW_eq]; exact lt_of_mem_UW (List.mem_toFinset.mp hu),
      fun e he' => List.mem_toFinset.mpr (mem_UW_of_lt he'),
      fun e ha => List.mem_toFinset.mpr (he.mem_of_active ha),
      fun e hx hlt => List.mem_toFinset.mpr (mem_UW_of_mem (List.mem_toFinset.mp hx)
        (by rw [he.NW_eq]; exact hlt))⟩
  have hLW : LW Dt.s Dt.r x = min A.size (x.length + s * k + Dt.r) := by
    unfold LW; rw [he.NW_eq, he.kW_eq, hDs]
  have hroom : (∀ e < A.size, e ∈ (U Dt x).toFinset) ∨
      x.toFinset.card + s * k + Dt.r ≤ LW Dt.s Dt.r x := by
    rcases le_total A.size (x.length + s * k + Dt.r) with h | h
    · left
      intro e he'
      have : e < LW Dt.s Dt.r x := by rw [hLW, min_eq_left h]; exact he'
      exact List.mem_toFinset.mpr (mem_UW_of_lt this)
    · right
      rw [hLW, min_eq_right h]
      have := List.toFinset_card_le x
      omega
  rw [witness_iff hq hv hR hroom, ← hDt]
  simp only [allEx_iff_digits Dt (fun j hj => free_lt hq hv hj) x A]
  simp only [List.mem_toFinset]
  rw [and_iff_right hfits]
  rw [exists_S_iff (U Dt x) hnd k (fun S => ∀ za < nU Dt x ^ Dt.p, ∃ zb < nU Dt x ^ Dt.q,
    Sat A S Dt.ψ (elemOf Dt x (dsOf Dt x za zb)))]
  -- the formula
  have hD1 : 1 ≤ (par Dt x).D := by simp [par, hDt, dataOf]
  have hψ : Dt.ψ.IsQF := isQF_rename _ ψ hq
  have hatoms := atom_facts (xs := xs) (ys := ys) hfits
  -- the oracle is right about the relation atoms and the equations
  have hrel : ∀ za < nU Dt x ^ Dt.p, ∀ zb < nU Dt x ^ Dt.q, ∀ b v,
      RelOk (oracle Dt x (dsOf Dt x za zb) b v) A (elemOf Dt x (dsOf Dt x za zb)) Dt.ψ := by
    intro za hza zb hzb b v
    refine ⟨fun i js hm => ?_, fun a c hm => ?_⟩
    · have hf := hatoms _ hm
      simp only [Formula.Fits] at hf
      simp only [oracle, decide_eq_true_eq]
      exact he.memW_iff hf.1 (by rw [List.length_map]; exact hf.2)
    · have ha := pos_lt hq hv _ hm a (by simp [Formula.freeVars])
      have hc := pos_lt hq hv _ hm c (by simp [Formula.freeVars])
      simp only [oracle, decide_eq_true_eq]
  -- facts about the `X`-atoms
  have hxat : ∀ js ∈ xatoms Dt.ψ, js.length = s ∧ ∀ j ∈ js, j < Dt.r := by
    intro js hjs
    have hm := mem_atoms_of_xatoms _ js hjs
    exact ⟨hatoms _ hm, fun j hj => pos_lt hq hv _ hm j (by simp [Formula.freeVars, hj])⟩
  rw [show alphaW Dt x = (par Dt x).alpha (good Dt x) from rfl, weightSat_iff (par Dt x) (good Dt x)
    (fun za zb t => Sat A ↑(Sdec (U Dt x) s t) Dt.ψ (elemOf Dt x (dsOf Dt x za zb))) hD1 ?_ ?_]
  · simp only [par, hk]
    exact Iff.rfl
  · -- soundness
    intro t ht za hza b _ v _ zb hzb hcons hg
    simp only [par] at ht hza hzb hcons
    have hg' : ev (oracle Dt x (dsOf Dt x za zb) b v) Dt.ψ = (true, false) := by
      simpa [good] using hg
    have := ev_sound (oracle Dt x (dsOf Dt x za zb) b v) A ↑(Sdec (U Dt x) s t)
      (elemOf Dt x (dsOf Dt x za zb)) Dt.ψ hψ (hrel za hza zb hzb b v) (fun js hjs bb hd => ?_)
      (by rw [hg'])
    · rw [hg'] at this; exact this.mp rfl
    · obtain ⟨hl, hjr⟩ := hxat js hjs
      have hsd := dec_sound ht (length_digits _ _ _) hcons
        (codeW Dt x (dsOf Dt x za zb) js)
      simp only [oracle] at hd
      have hiff := code_mem_iff (hk ▸ ht) hza hzb hl hjr
      cases bb
      · simp only [Bool.false_eq_true, false_iff, Finset.mem_coe]
        exact fun h => hsd.2 hd (hiff.mpr h)
      · simp only [true_iff, Finset.mem_coe]
        exact hiff.mp (hsd.1 hd)
  · -- completeness
    intro t ht za hza zb hzb htr
    simp only [par] at ht hza hzb ⊢
    set us := (xatoms Dt.ψ).map (codeW Dt x (dsOf Dt x za zb)) with hus
    have hlen : 2 * us.length ≤ Dt.D := by
      simp only [hus, List.length_map, hDt, dataOf, xatoms_rename]; omega
    obtain ⟨b, hb, hdec⟩ := dec_complete (N := nU Dt x ^ s) ht us hlen
    refine ⟨b, hb, ?_⟩
    have hxd : ∀ js ∈ xatoms Dt.ψ, (oracle Dt x (dsOf Dt x za zb) b
        (canon (kW x) (nU Dt x ^ s) Dt.D t b)).xdec js =
          some (decide (codeW Dt x (dsOf Dt x za zb) js ∈ t)) := by
      intro js hjs
      exact hdec _ (List.mem_map_of_mem hjs)
    have hflag := ev_complete (oracle Dt x (dsOf Dt x za zb) b
      (canon (kW x) (nU Dt x ^ s) Dt.D t b)) Dt.ψ fun js hjs => by rw [hxd js hjs]; simp
    have hval := ev_sound (oracle Dt x (dsOf Dt x za zb) b
      (canon (kW x) (nU Dt x ^ s) Dt.D t b)) A ↑(Sdec (U Dt x) s t)
      (elemOf Dt x (dsOf Dt x za zb)) Dt.ψ hψ (hrel za hza zb hzb _ _) (fun js hjs bb hd => by
        rw [hxd js hjs] at hd
        obtain ⟨hl, hjr⟩ := hxat js hjs
        have hiff := code_mem_iff (hk ▸ ht) hza hzb hl hjr
        cases hd
        simp only [Finset.mem_coe]
        exact ⟨fun h => hiff.mp (of_decide_eq_true h), fun h => decide_eq_true (hiff.mpr h)⟩) hflag
    have hv1 : (ev (oracle Dt x (dsOf Dt x za zb) b
        (canon (kW x) (nU Dt x ^ s) Dt.D t b)) Dt.ψ).1 = true := hval.mpr htr
    have hev : ev (oracle Dt x (dsOf Dt x za zb) b (canon (kW x) (nU Dt x ^ Dt.s) Dt.D t b))
        Dt.ψ = (true, false) := Prod.ext hv1 hflag
    simp only [good]
    rw [hev]
    rfl

end Main

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Correct
