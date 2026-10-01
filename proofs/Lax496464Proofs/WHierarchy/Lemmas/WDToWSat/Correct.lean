import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics

/-! # The formula is `k`-satisfiable iff a witness of weight `k` exists

`weightSat_iff`: for a word of `(A, k)` that fits, `alphaW` is `k`-satisfiable exactly when there is a
witness among the elements of `U` (`Semantics.UWit`). Tuples of elements of `U` of length `s` and the
codes below `n^s` correspond through `enc` / `dec`, a propositional assignment of weight `k` is a
set of `k` codes, and the clauses written for `z` hold exactly when the CNF holds for the assignment
of elements given by the digits of `z`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Correct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics

/-! ### Tuples over a list without repetition, and their codes -/

section Code
variable {Ul : List ℕ} (hnd : Ul.Nodup)

theorem getD_idxOf' {a : ℕ} (h : a ∈ Ul) : Ul.getD (Ul.idxOf a) 0 = a := getD_idxOf h

include hnd in
theorem idxOf_getD {d : ℕ} (h : d < Ul.length) : Ul.idxOf (Ul.getD d 0) = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnd d h

theorem getD_mem {d : ℕ} (h : d < Ul.length) : Ul.getD d 0 ∈ Ul := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- The code of a tuple of elements of `Ul`. -/
def enc (Ul t : List ℕ) : ℕ := codeOf Ul.length (t.map Ul.idxOf)

/-- The tuple of a code. -/
def dec (Ul : List ℕ) (s c : ℕ) : List ℕ := (digits Ul.length s c).map fun d => Ul.getD d 0

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

include hnd in
theorem map_getD_idxOf {ds : List ℕ} (hd : ∀ d ∈ ds, d < Ul.length) :
    (ds.map fun d => Ul.getD d 0).map Ul.idxOf = ds := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ds]
  exact List.map_congr_left fun d h => idxOf_getD hnd (hd d h)

theorem enc_inj {t t' : List ℕ} (ht : ∀ a ∈ t, a ∈ Ul) (ht' : ∀ a ∈ t', a ∈ Ul)
    (hl : t.length = t'.length) (h : enc Ul t = enc Ul t') : t = t' := by
  have := codeOf_inj (n := Ul.length) (ds := t.map Ul.idxOf) (es := t'.map Ul.idxOf)
    (fun d hd => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd; exact List.idxOf_lt_length_iff.mpr (ht a ha))
    (fun d hd => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd; exact List.idxOf_lt_length_iff.mpr (ht' a ha))
    (by simpa using hl) h
  rw [← map_idxOf_getD ht, ← map_idxOf_getD ht', this]

theorem digits_lt' {s c : ℕ} (hc : c < Ul.length ^ s) : ∀ d ∈ digits Ul.length s c, d < Ul.length := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [digits]
  · have : 0 < Ul.length := by
      rcases Nat.eq_zero_or_pos Ul.length with h | h
      · rw [h, zero_pow (by omega)] at hc; omega
      · exact h
    exact digits_lt this s c

theorem dec_mem {s c : ℕ} (hc : c < Ul.length ^ s) : ∀ a ∈ dec Ul s c, a ∈ Ul := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  exact getD_mem (digits_lt' hc d hd)

theorem length_dec (s c : ℕ) : (dec Ul s c).length = s := by simp [dec]

include hnd in
theorem enc_dec {s c : ℕ} (hc : c < Ul.length ^ s) : enc Ul (dec Ul s c) = c := by
  unfold enc dec
  rw [map_getD_idxOf hnd (digits_lt' hc), codeOf_digits _ _ _ hc]

end Code

/-! ### Facts about the literals -/

section Lits
variable {xs : List ℕ} {ψ : Formula} {s : ℕ} {x : List ℕ} {A : Structure} {k : ℕ}
  {bl : List (List ℕ)}

/-- The literals of the CNF fit the vocabulary. -/
theorem lit_facts (hq : ψ.IsQF) (he : Enc x A k bl) (hfit : fitW (dataOf xs ψ s) x) :
    ∀ C ∈ (dataOf xs ψ s).cnf, ∀ l ∈ C,
      (∀ i js, l.atom = .rel i js → i < A.arities.length ∧ js.length = A.arities.getD i 0) ∧
      (∀ js, l.atom = .setVar js → js.length = s) := by
  intro C hC l hl
  obtain ⟨a, ha, hla⟩ := mem_cnf xs.dedup ψ true hq C hC l hl
  have hfa : a.Fits A.arities s := (fits_iff_atoms _ _ ψ).mp
    ((fits_allBlock _ _ ψ xs).mp ((fitW_iff he xs ψ s).mp hfit)) a ha
  rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, w, rfl⟩
  · refine ⟨fun i' js h => ?_, fun js h => ?_⟩
    · rw [hla] at h; simp only [renameAtom, Atom.rel.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hfa.1, by rw [List.length_map]; exact hfa.2⟩
    · rw [hla] at h; simp [renameAtom] at h
  · refine ⟨fun i' js h => ?_, fun js h => ?_⟩
    · rw [hla] at h; simp [renameAtom] at h
    · rw [hla] at h; simp only [renameAtom, Atom.setVar.injEq] at h
      subst h
      rw [List.length_map]; exact hfa
  · refine ⟨fun i' js h => ?_, fun js h => ?_⟩
    · rw [hla] at h; simp [renameAtom] at h
    · rw [hla] at h; simp [renameAtom] at h

/-- **A literal without `X` is evaluated correctly on the word.** -/
theorem nonXVal_iff (he : Enc x A k bl) (S : Set (List ℕ)) (ε : ℕ → ℕ) (l : Lit)
    (hX : isXLit l = false)
    (hrel : ∀ i js, l.atom = .rel i js → i < A.arities.length ∧ js.length = A.arities.getD i 0) :
    nonXVal x ε l = true ↔ l.holds A S ε := by
  obtain ⟨pos, atom⟩ := l
  cases atom with
  | rel i js =>
    obtain ⟨hi, hl⟩ := hrel i js rfl
    have hm := he.memW_iff hi (tup := js.map ε) (by rw [List.length_map]; exact hl)
    cases pos <;> simp [nonXVal, Lit.holds, Atom.holds, hm]
  | eq a b => cases pos <;> simp [nonXVal, Lit.holds, Atom.holds]
  | setVar js => simp [isXLit] at hX

end Lits

/-! ### The clauses -/

theorem eval_iff (F : Lax429075.CNF.Formula) (ρ : Lax429075.CNF.Assignment) :
    Lax429075.CNF.eval F ρ = true ↔ ∀ C ∈ F, ∃ l ∈ C, Lax429075.CNF.Literal.eval l ρ = true := by
  simp [Lax429075.CNF.eval, List.all_eq_true, List.any_eq_true]

open Lax429075.CNF in
theorem lit_eval (c : ℕ) (b : Bool) (S' : Finset ℕ) :
    Literal.eval ⟨c, b⟩ (fun i => decide (i ∈ S')) = true ↔ (if b then c ∈ S' else c ∉ S') := by
  cases b <;> simp [Literal.eval]

section Main
variable {xs : List ℕ} {ψ : Formula} {s : ℕ} {x : List ℕ} {A : Structure} {k : ℕ}
  {bl : List (List ℕ)}

/-- The positions of a clause are below `r`, so their digits are below `n`. -/
theorem digit_lt {D : Data} {z : ℕ} (hz : z < nW D x ^ D.r) {j : ℕ} (hj : j < D.r) :
    (digits (nW D x) D.r z).getD j 0 < nW D x := by
  have hn : 0 < nW D x := by
    rcases Nat.eq_zero_or_pos (nW D x) with h | h
    · rw [h, zero_pow (by omega)] at hz; omega
    · exact h
  have hmem : (digits (nW D x) D.r z).getD j 0 ∈ digits (nW D x) D.r z := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
    exact List.getElem_mem _
  exact digits_lt hn _ _ _ hmem

/-- **The clause written for `z` and `C` holds iff `C` holds** for the elements of the digits of
`z`, under the set of tuples whose codes are true. -/
theorem clauseOut_iff (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) (he : Enc x A k bl)
    (hfit : fitW (dataOf xs ψ s) x) (S : Finset (List ℕ))
    (hS : ∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a ∈ U (dataOf xs ψ s) x)
    {z : ℕ} (hz : z < nW (dataOf xs ψ s) x ^ (dataOf xs ψ s).r)
    {C : List Lit} (hC : C ∈ (dataOf xs ψ s).cnf) :
    (∃ l ∈ clauseOut (dataOf xs ψ s) x (digits (nW (dataOf xs ψ s) x) (dataOf xs ψ s).r z) C,
      Lax429075.CNF.Literal.eval l
        (fun i => decide (i ∈ S.image (enc (U (dataOf xs ψ s) x)))) = true) ↔
      ∃ l ∈ C, l.holds A ↑S (epsW (dataOf xs ψ s) x
        (digits (nW (dataOf xs ψ s) x) (dataOf xs ψ s).r z)) := by
  set D := dataOf xs ψ s with hD
  set ds := digits (nW D x) D.r z with hds
  set ε := epsW D x ds with hε
  have hfacts := lit_facts hq he hfit C hC
  have hidx := idxs_lt (s := s) hq hv C hC
  have hnd : (U D x).Nodup := UW_nodup _ _ _
  -- the X-literals
  have hX : ∀ l ∈ C, isXLit l = true →
      (Lax429075.CNF.Literal.eval ⟨codeW D x ds l, l.pos⟩
        (fun i => decide (i ∈ S.image (enc (U D x)))) = true ↔ l.holds A ↑S ε) := by
    intro l hl hXl
    obtain ⟨pos, atom⟩ := l
    cases atom with
    | rel i js => simp [isXLit] at hXl
    | eq a b => simp [isXLit] at hXl
    | setVar js =>
      have hjs : js.length = s := (hfacts _ hl).2 js rfl
      have hjd : ∀ d ∈ js.map (fun j => ds.getD j 0), d < nW D x := by
        intro d hd
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
        exact digit_lt hz (hidx _ hl j (by simpa [Atom.idxs] using hj))
      have htup : js.map ε = (js.map fun j => ds.getD j 0).map fun d => (U D x).getD d 0 := by
        rw [List.map_map]; rfl
      have hmemU : ∀ a ∈ js.map ε, a ∈ U D x := by
        rw [htup]; intro a ha
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
        exact getD_mem (hjd d hd)
      have hkey : codeW D x ds ⟨pos, .setVar js⟩ ∈ S.image (enc (U D x)) ↔ js.map ε ∈ S := by
        have hcw : codeW D x ds ⟨pos, .setVar js⟩ = enc (U D x) (js.map ε) := by
          unfold codeW enc
          rw [htup, map_getD_idxOf hnd hjd]; rfl
        rw [hcw, Finset.mem_image]
        constructor
        · rintro ⟨t, ht, he'⟩
          rwa [← enc_inj (hS t ht).2 hmemU (by rw [(hS t ht).1, List.length_map, hjs]) he']
        · intro h; exact ⟨_, h, rfl⟩
      rw [lit_eval, hkey]
      cases pos <;> simp [Lit.holds, Atom.holds]
  unfold clauseOut
  split_ifs with hsat
  · -- a literal without `X` holds: both sides hold
    constructor
    · intro _
      unfold satNonX at hsat
      obtain ⟨l, hl, hl'⟩ := List.any_eq_true.mp hsat
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hl'
      exact ⟨l, hl, (nonXVal_iff he ↑S ε l hl'.1 (hfacts l hl).1).mp hl'.2⟩
    · intro _
      by_cases h0 : 0 ∈ S.image (enc (U D x))
      · exact ⟨⟨0, true⟩, by simp, by rw [lit_eval]; simpa using h0⟩
      · exact ⟨⟨0, false⟩, by simp, by rw [lit_eval]; simpa using h0⟩
  · have hno : ∀ l ∈ C, isXLit l = false → ¬ l.holds A ↑S ε := by
      intro l hl hXl hh
      apply hsat
      unfold satNonX
      exact List.any_eq_true.mpr ⟨l, hl, by
        rw [hXl, Bool.not_false, Bool.true_and]
        exact (nonXVal_iff he ↑S ε l hXl (hfacts l hl).1).mpr hh⟩
    constructor
    · rintro ⟨l', hl', hev⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
      obtain ⟨hlC, hXl⟩ := List.mem_filter.mp hl
      exact ⟨l, hlC, (hX l hlC hXl).mp hev⟩
    · rintro ⟨l, hl, hh⟩
      cases hXl : isXLit l
      · exact absurd hh (hno l hl hXl)
      · exact ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hl, hXl⟩), (hX l hl hXl).mpr hh⟩

/-- **The assignment-clauses hold iff the CNF holds for all assignments into `U`.** -/
theorem forall_z_iff (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) (S : Set (List ℕ)) :
    (∀ z < nW (dataOf xs ψ s) x ^ (dataOf xs ψ s).r, CnfHolds A S (epsW (dataOf xs ψ s) x
        (digits (nW (dataOf xs ψ s) x) (dataOf xs ψ s).r z)) (dataOf xs ψ s).cnf) ↔
      ∀ ε : ℕ → ℕ, (∀ j < (dataOf xs ψ s).r, ε j ∈ U (dataOf xs ψ s) x) →
        CnfHolds A S ε (dataOf xs ψ s).cnf := by
  set D := dataOf xs ψ s with hD
  have hidx := idxs_lt (s := s) hq hv
  have hnd : (U D x).Nodup := UW_nodup _ _ _
  constructor
  · intro h ε hε
    set ds := (List.range D.r).map fun j => (U D x).idxOf (ε j) with hds
    have hdl : ∀ d ∈ ds, d < nW D x := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
      exact List.idxOf_lt_length_iff.mpr (hε j (List.mem_range.mp hj))
    have hlen : ds.length = D.r := by simp [ds]
    have hz := codeOf_lt ds hdl
    rw [hlen] at hz
    have h1 := h _ hz
    rw [← hlen, digits_codeOf ds hdl] at h1
    refine (cnfHolds_congr fun C hC l hl j hj => ?_).mp h1
    have hj' := hidx C hC l hl j hj
    have hj'' : j < D.r := hj'
    have hdj : ds.getD j 0 = (U D x).idxOf (ε j) := by
      simp [ds, List.getD_eq_getElem?_getD, List.getElem?_range hj'']
    show (U D x).getD (ds.getD j 0) 0 = ε j
    rw [hdj]; exact getD_idxOf' (hε j hj')
  · intro h z hz
    exact h _ fun j hj => getD_mem (digit_lt hz hj)

/-- `Y₀` is a variable whenever a clause of an assignment is written. -/
theorem pos_pow_s (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) (he : Enc x A k bl)
    (hfit : fitW (dataOf xs ψ s) x) (hr : 0 < nW (dataOf xs ψ s) x ^ (dataOf xs ψ s).r) :
    0 < nW (dataOf xs ψ s) x ^ s := by
  rcases Nat.eq_zero_or_pos (nW (dataOf xs ψ s) x) with hn | hn
  · rw [hn] at hr ⊢
    have hr0 : (dataOf xs ψ s).r = 0 := by
      by_contra h; rw [zero_pow h] at hr; omega
    rcases Nat.eq_zero_or_pos s with hs | hs
    · rw [hs]; simp
    · exfalso
      have hxs : xs = [] := by
        simpa [dataOf, List.length_eq_zero_iff, List.dedup_eq_nil] using hr0
      have hfree : ψ.freeVars = ∅ := by
        ext v; simp only [Finset.notMem_empty, iff_false]; intro h; simpa [hxs] using hv v h
      refine not_fits_of_noVars A.arities A.arity_pos hs ψ hq hfree ?_
      exact (fits_allBlock _ _ ψ xs).mp ((fitW_iff he xs ψ s).mp hfit)
  · exact pow_pos hn _

/-- **The variables of the formula are the codes below `n^s`.** -/
theorem mem_vars_iff (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) (he : Enc x A k bl)
    (hfit : fitW (dataOf xs ψ s) x) (c : ℕ) :
    c ∈ Lax496464.WH_C3_WeightedSat.vars (alphaW (dataOf xs ψ s) x) ↔
      c < nW (dataOf xs ψ s) x ^ s := by
  set D := dataOf xs ψ s with hD
  have hDs : D.s = s := rfl
  unfold Lax496464.WH_C3_WeightedSat.vars alphaW
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨C', hC', l, hl, rfl⟩
    rcases hC' with ⟨z, hz, hzC⟩ | ⟨c', hc', rfl⟩
    · have hz' := List.mem_range.mp hz
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hzC
      unfold clauseOut at hl
      split_ifs at hl
      · have := pos_pow_s hq hv he hfit (lt_of_le_of_lt (Nat.zero_le _) hz')
        simp at hl; rcases hl with rfl | rfl <;> exact this
      · obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
        obtain ⟨hl0C, hXl⟩ := List.mem_filter.mp hl0
        obtain ⟨pos, atom⟩ := l0
        cases atom with
        | rel i js => simp [isXLit] at hXl
        | eq a b => simp [isXLit] at hXl
        | setVar js =>
          have hjs : js.length = s := (lit_facts hq he hfit C hC _ hl0C).2 js rfl
          have hidx := idxs_lt (s := s) hq hv C hC _ hl0C
          show codeOf _ _ < _
          have := codeOf_lt (n := nW D x) (js.map fun j => (digits (nW D x) D.r z).getD j 0)
            fun d hd => by
              obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
              exact digit_lt hz' (hidx j (by simpa [Atom.idxs] using hj))
          simpa [hjs, Atom.idxs] using this
    · simp only [taut, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simpa [hDs] using hc'
  · intro hc
    exact ⟨taut c, Or.inr ⟨c, List.mem_range.mpr (by rwa [hDs]), rfl⟩, ⟨c, true⟩, by simp [taut], rfl⟩

/-- **The formula is `k`-satisfiable iff there is a witness among the elements of `U`.** -/
theorem weightSat_iff (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) (he : Enc x A k bl)
    (hfit : fitW (dataOf xs ψ s) x) :
    Lax496464.WH_C3_WeightedSat.WeightSat (alphaW (dataOf xs ψ s) x) k ↔ UWit A (dataOf xs ψ s) x k := by
  set D := dataOf xs ψ s with hD
  have hDs : D.s = s := rfl
  have hnd : (U D x).Nodup := UW_nodup _ _ _
  -- the formula holds under the codes of `S` iff the CNF holds for all assignments into `U`
  have heval : ∀ S : Finset (List ℕ), (∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a ∈ U D x) →
      (Lax429075.CNF.eval (alphaW D x) (fun i => decide (i ∈ S.image (enc (U D x)))) = true ↔
        ∀ ε : ℕ → ℕ, (∀ j < D.r, ε j ∈ U D x) → CnfHolds A ↑S ε D.cnf) := by
    intro S hS
    rw [← forall_z_iff hq hv, eval_iff]
    unfold alphaW
    simp only [zClauses, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · intro h z hz C hC
      exact (clauseOut_iff hq hv he hfit S hS hz hC).mp (h _ (Or.inl ⟨z, hz, C, hC, rfl⟩))
    · rintro h C' (⟨z, hz, C, hC, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact (clauseOut_iff hq hv he hfit S hS hz hC).mpr (h z hz C hC)
      · by_cases h0 : c ∈ S.image (enc (U D x))
        · exact ⟨⟨c, true⟩, by simp [taut], by rw [lit_eval]; simpa using h0⟩
        · exact ⟨⟨c, false⟩, by simp [taut], by rw [lit_eval]; simpa using h0⟩
  constructor
  · rintro ⟨S', hsub, hcard, hev⟩
    have hlt : ∀ c ∈ S', c < nW D x ^ s := fun c hc =>
      (mem_vars_iff hq hv he hfit c).mp (hsub hc)
    set S := S'.image (dec (U D x) s) with hS
    have hback : S.image (enc (U D x)) = S' := by
      ext c; simp only [hS, Finset.mem_image]
      constructor
      · rintro ⟨t, ⟨c', hc', rfl⟩, rfl⟩; rw [enc_dec hnd (hlt c' hc')]; exact hc'
      · intro hc; exact ⟨_, ⟨c, hc, rfl⟩, enc_dec hnd (hlt c hc)⟩
    have htup : ∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a ∈ U D x := by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨length_dec s c, dec_mem (hlt c hc)⟩
    refine ⟨S, ?_, htup, ?_⟩
    · rw [hS, Finset.card_image_of_injOn fun c hc c' hc' h => by
        rw [← enc_dec hnd (hlt c hc), ← enc_dec hnd (hlt c' hc')]; exact congrArg _ h]
      exact hcard
    · rw [← heval S htup, hback]; exact hev
  · rintro ⟨S, hcard, htup, hall⟩
    refine ⟨S.image (enc (U D x)), fun c hc => ?_, ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
      rw [mem_vars_iff hq hv he hfit]
      have := enc_lt (htup t ht).2
      rwa [(htup t ht).1] at this
    · rw [Finset.card_image_of_injOn fun t ht t' ht' h =>
        enc_inj (htup t ht).2 (htup t' ht').2 (by rw [(htup t ht).1, (htup t' ht').1]) h]
      exact hcard
    · exact (heval S htup).mpr hall

end Main

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Correct
