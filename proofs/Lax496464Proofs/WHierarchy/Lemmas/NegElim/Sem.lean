import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! # Negation elimination: the translation is correct

`Ext A' θ c n ρ` says that `θ` holds in `A'` under `ρ` changed on the fresh variables
`c, …, c+n-1` to some elements of the universe. The translation `tr p φ c` satisfies
`Ext (tr p φ c) c (cnt p φ) ρ ↔ (φ holds under ρ ↔ p)` for quantifier-free `φ` whose variables are
below `c` and take values in the universe (`sem`). The heart of it is `ext_negRel`: a tuple is not
in `R` exactly when it is below the first tuple, strictly between two consecutive ones, or above the
last one. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct

/-- The data list the tuples of `A`. -/
structure Compat (A : Structure) (D : NData) : Prop where
  s : D.s = A.arities.length
  N : D.N = A.size
  ar : ∀ i < D.s, D.ar i = A.arities.getD i 0
  L : ∀ i < D.s, (D.L i).Nodup ∧ (D.L i).toFinset = A.rel i

theorem Structure.arity_pos' (A : Structure) : ∀ i < A.arities.length, 1 ≤ A.arities.getD i 0 :=
  fun i hi => A.arity_pos _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)

variable {A : Structure} {D : NData}

theorem Compat.valid (hc : Compat A D) : D.Valid where
  pos i hi := by rw [hc.ar i hi]; exact Structure.arity_pos' A i (by rw [← hc.s]; exact hi)
  nodup i hi := (hc.L i hi).1
  tup i hi t ht := by
    have ht' : t ∈ A.rel i := by rw [← (hc.L i hi).2]; exact List.mem_toFinset.mpr ht
    obtain ⟨-, h1, h2⟩ := A.wf i t ht'
    exact ⟨by rw [hc.ar i hi, h1], fun a ha => by rw [hc.N]; exact h2 a ha⟩

theorem Compat.mem_L (hc : Compat A D) {i : ℕ} (hi : i < D.s) {t : List ℕ} :
    t ∈ D.L i ↔ t ∈ A.rel i := by
  rw [← (hc.L i hi).2, List.mem_toFinset]

theorem Compat.extAr (hc : Compat A D) : ExtAr A.arities D.arities :=
  NData.extAr hc.s.symm fun i hi => (hc.ar i hi).symm

/-! ### The lexicographic order -/

theorem map_lt_cons {ρ : Assignment} {y z : ℕ} {ys zs : List ℕ} :
    (y :: ys).map ρ < (z :: zs).map ρ ↔ ρ y < ρ z ∨ ρ y = ρ z ∧ ys.map ρ < zs.map ρ := by
  simp only [List.map_cons]; exact List.cons_lt_cons_iff

/-- **The formula `lexF` expresses the lexicographic order** on tuples in the universe. -/
theorem sat_lexF (hv : D.Valid) (S : Set (List ℕ)) (ρ : Assignment) : ∀ {ys zs : List ℕ},
    ys.length = zs.length → ys ≠ [] → (∀ v ∈ ys, ρ v < D.N) → (∀ v ∈ zs, ρ v < D.N) →
      (Sat (NData.toStructure hv) S (lexF ys zs) ρ ↔ ys.map ρ < zs.map ρ)
  | [], _, _, hne, _, _ => (hne rfl).elim
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | y :: ys, z :: zs, hl, _, hy, hz => by
    have hyz : ρ z < D.N := hz z (by simp)
    unfold lexF
    split_ifs with hys
    · subst hys
      have : zs = [] := by simpa using hl.symm
      subst this
      simp only [Sat, NData.mem_rel_lt, List.map_cons, List.map_nil]
      rw [List.cons_lt_cons_iff]
      simp only [List.cons.injEq, and_true, List.not_lt_nil, and_false, or_false]
      constructor
      · rintro ⟨a, b, ⟨rfl, rfl⟩, h, -⟩; exact h
      · intro h; exact ⟨_, _, ⟨rfl, rfl⟩, h, hyz⟩
    · rw [map_lt_cons]
      simp only [Sat, NData.mem_rel_lt, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [sat_lexF hv S ρ (by simpa using hl) hys (fun v hv => hy v (by simp [hv]))
        (fun v hv => hz v (by simp [hv]))]
      constructor
      · rintro (⟨a, b, ⟨rfl, rfl⟩, h, -⟩ | h)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ⟨_, _, ⟨rfl, rfl⟩, h, hyz⟩
        · exact Or.inr h

/-! ### Fresh variables -/

/-- `θ` holds under `ρ` changed on `c, …, c+n-1` to elements of the universe. -/
def Ext (A' : Structure) (θ : Formula) (c n : ℕ) (ρ : Assignment) : Prop :=
  ∃ ρ' : Assignment, (∀ v, (v < c ∨ c + n ≤ v) → ρ' v = ρ v) ∧
    (∀ v, c ≤ v → v < c + n → ρ' v < A'.size) ∧ Sat A' ∅ θ ρ'

theorem ext_zero {A' : Structure} {θ : Formula} {c : ℕ} {ρ : Assignment} :
    Ext A' θ c 0 ρ ↔ Sat A' ∅ θ ρ := by
  constructor
  · rintro ⟨ρ', h1, -, h3⟩
    rwa [show ρ' = ρ from funext fun v => h1 v (by omega)] at h3
  · intro h; exact ⟨ρ, fun _ _ => rfl, fun v h1 h2 => by omega, h⟩

section Glue

variable {A' : Structure} {θ₁ θ₂ : Formula} {c n₁ n₂ : ℕ} {ρ : Assignment}

/-- Restricting a witness to the first block of fresh variables. -/
theorem ext_left (h1 : ∀ v ∈ θ₁.freeVars, v < c + n₁) {ρ' : Assignment}
    (ha : ∀ v, (v < c ∨ c + (n₁ + n₂) ≤ v) → ρ' v = ρ v)
    (hu : ∀ v, c ≤ v → v < c + (n₁ + n₂) → ρ' v < A'.size) (hs : Sat A' ∅ θ₁ ρ') :
    Ext A' θ₁ c n₁ ρ := by
  refine ⟨fun v => if c ≤ v ∧ v < c + n₁ then ρ' v else ρ v, fun v hv => ?_, fun v h1 h2 => ?_,
    (sat_congr A' ∅ θ₁ fun v hv => ?_).mp hs⟩
  · (try simp only); rw [if_neg (by omega)]
  · (try simp only); rw [if_pos ⟨h1, h2⟩]; exact hu v h1 (by omega)
  · have := h1 v hv
    try simp only
    by_cases hcv : c ≤ v
    · rw [if_pos ⟨hcv, this⟩]
    · rw [if_neg (by omega)]; exact ha v (by omega)

/-- Restricting a witness to the second block of fresh variables. -/
theorem ext_right (h2 : ∀ v ∈ θ₂.freeVars, v < c ∨ c + n₁ ≤ v) {ρ' : Assignment}
    (ha : ∀ v, (v < c ∨ c + (n₁ + n₂) ≤ v) → ρ' v = ρ v)
    (hu : ∀ v, c ≤ v → v < c + (n₁ + n₂) → ρ' v < A'.size) (hs : Sat A' ∅ θ₂ ρ') :
    Ext A' θ₂ (c + n₁) n₂ ρ := by
  refine ⟨fun v => if c + n₁ ≤ v ∧ v < c + n₁ + n₂ then ρ' v else ρ v, fun v hv => ?_,
    fun v h1 h2 => ?_, (sat_congr A' ∅ θ₂ fun v hv => ?_).mp hs⟩
  · (try simp only); rw [if_neg (by omega)]
  · (try simp only); rw [if_pos ⟨h1, h2⟩]; exact hu v (by omega) (by omega)
  · rcases h2 v hv with h | h
    · rw [if_neg (by omega)]; exact ha v (Or.inl h)
    · try simp only
      by_cases hv' : v < c + n₁ + n₂
      · rw [if_pos ⟨h, hv'⟩]
      · rw [if_neg (by omega)]; exact ha v (Or.inr (by omega))

/-- **Conjunction**: witnesses for the two blocks combine. -/
theorem ext_and (h1 : ∀ v ∈ θ₁.freeVars, v < c + n₁) (h2 : ∀ v ∈ θ₂.freeVars, v < c ∨ c + n₁ ≤ v) :
    Ext A' (.and θ₁ θ₂) c (n₁ + n₂) ρ ↔ Ext A' θ₁ c n₁ ρ ∧ Ext A' θ₂ (c + n₁) n₂ ρ := by
  constructor
  · rintro ⟨ρ', ha, hu, hs1, hs2⟩
    exact ⟨ext_left h1 ha hu hs1, ext_right h2 ha hu hs2⟩
  · rintro ⟨⟨ρ₁, ha1, hu1, hs1⟩, ⟨ρ₂, ha2, hu2, hs2⟩⟩
    refine ⟨fun v => if v < c + n₁ then ρ₁ v else ρ₂ v, fun v hv => ?_, fun v hv1 hv2 => ?_,
      (sat_congr A' ∅ θ₁ fun v hv => ?_).mpr hs1, (sat_congr A' ∅ θ₂ fun v hv => ?_).mpr hs2⟩
    · try simp only
      split_ifs with h
      · exact ha1 v (by omega)
      · exact ha2 v (by omega)
    · try simp only
      split_ifs with h
      · exact hu1 v hv1 h
      · exact hu2 v (by omega) (by omega)
    · rw [if_pos (h1 v hv)]
    · try simp only
      rcases h2 v hv with h | h
      · rw [if_pos (by omega), ha1 v (Or.inl h), ha2 v (Or.inl (by omega))]
      · rw [if_neg (by omega)]

/-- **Disjunction**: a witness for one block extends to both, in a nonempty universe. -/
theorem ext_or (hN : 0 < A'.size) (h1 : ∀ v ∈ θ₁.freeVars, v < c + n₁)
    (h2 : ∀ v ∈ θ₂.freeVars, v < c ∨ c + n₁ ≤ v) :
    Ext A' (.or θ₁ θ₂) c (n₁ + n₂) ρ ↔ Ext A' θ₁ c n₁ ρ ∨ Ext A' θ₂ (c + n₁) n₂ ρ := by
  constructor
  · rintro ⟨ρ', ha, hu, hs1 | hs2⟩
    · exact Or.inl (ext_left h1 ha hu hs1)
    · exact Or.inr (ext_right h2 ha hu hs2)
  · rintro (⟨ρ₁, ha1, hu1, hs1⟩ | ⟨ρ₂, ha2, hu2, hs2⟩)
    · refine ⟨fun v => if v < c + n₁ then ρ₁ v else if v < c + (n₁ + n₂) then 0 else ρ v,
        fun v hv => ?_, fun v hv1 hv2 => ?_, Or.inl ((sat_congr A' ∅ θ₁ fun v hv => ?_).mpr hs1)⟩
      · try simp only
        split_ifs with h h'
        · exact ha1 v (by omega)
        · omega
        · rfl
      · try simp only
        split_ifs with h
        · exact hu1 v hv1 h
        · exact hN
      · rw [if_pos (h1 v hv)]
    · refine ⟨fun v => if c ≤ v ∧ v < c + n₁ then 0 else ρ₂ v,
        fun v hv => ?_, fun v hv1 hv2 => ?_, Or.inr ((sat_congr A' ∅ θ₂ fun v hv => ?_).mpr hs2)⟩
      · try simp only
        rw [if_neg (by omega)]; exact ha2 v (by omega)
      · try simp only
        split_ifs with h
        · exact hN
        · exact hu2 v (by omega) (by omega)
      · try simp only
        rcases h2 v hv with h | h
        · rw [if_neg (by omega)]
        · rw [if_neg (by omega)]

end Glue

/-! ### Negative atoms -/

theorem getD_of_lt (l : List ℕ) (k : ℕ) (h : k < l.length) : l.getD k 0 = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- The assignment sending the fresh variables `c, …` to the entries of `u`, then of `v`. -/
def asg (ρ : Assignment) (c : ℕ) (u v : List ℕ) : Assignment := fun w =>
  if c ≤ w ∧ w < c + u.length then u.getD (w - c) 0
  else if c + u.length ≤ w ∧ w < c + 2 * u.length then v.getD (w - c - u.length) 0 else ρ w

theorem asg_of_lt {ρ : Assignment} {c : ℕ} {u v : List ℕ} {w : ℕ} (h : w < c) :
    asg ρ c u v w = ρ w := by
  unfold asg; rw [if_neg (by omega), if_neg (by omega)]

theorem asg_of_ge {ρ : Assignment} {c : ℕ} {u v : List ℕ} {w : ℕ} (h : c + 2 * u.length ≤ w) :
    asg ρ c u v w = ρ w := by
  unfold asg; rw [if_neg (by omega), if_neg (by omega)]

theorem map_asg_left (ρ : Assignment) (c : ℕ) (u v : List ℕ) :
    (List.range' c u.length).map (asg ρ c u v) = u := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range']
  unfold asg
  simp only [List.length_map, List.length_range'] at h1
  rw [if_pos (by omega), show c + 1 * k - c = k by omega, getD_of_lt _ _ h2]

theorem map_asg_right (ρ : Assignment) (c : ℕ) (u v : List ℕ) (hv : v.length = u.length) :
    (List.range' (c + u.length) u.length).map (asg ρ c u v) = v := by
  apply List.ext_getElem (by simp [hv])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range']
  unfold asg
  simp only [List.length_map, List.length_range'] at h1
  rw [if_neg (by omega), if_pos (by omega), show c + u.length + 1 * k - c - u.length = k by omega,
    getD_of_lt _ _ h2]

theorem asg_lt {ρ : Assignment} {c : ℕ} {u v : List ℕ} {N : ℕ} (hv : v.length = u.length)
    (hu : ∀ a ∈ u, a < N) (hv' : ∀ a ∈ v, a < N) {w : ℕ} (h1 : c ≤ w) (h2 : w < c + 2 * u.length) :
    asg ρ c u v w < N := by
  unfold asg
  split_ifs with h h'
  · rw [getD_of_lt _ _ (by omega)]; exact hu _ (List.getElem_mem _)
  · rw [getD_of_lt _ _ (by omega)]; exact hv' _ (List.getElem_mem _)
  · omega

variable (hc : Compat A D)

include hc in
/-- **A tuple is not in `R_i` exactly when it is below the first tuple, strictly between two
consecutive ones, or above the last one** — the positive formula `negRel` says so. -/
theorem ext_negRel {i : ℕ} {ys : List ℕ} {c : ℕ} {ρ : Assignment} (hi : i < D.s)
    (hl : ys.length = D.ar i) (hyc : ∀ v ∈ ys, v < c) (hyN : ∀ v ∈ ys, ρ v < D.N) :
    Ext (NData.toStructure hc.valid) (negRel i ys c) c (2 * ys.length) ρ ↔
      ys.map ρ ∉ D.L i := by
  have hv := hc.valid
  have hr : 1 ≤ ys.length := by rw [hl]; exact hv.pos i hi
  have hys : ys ≠ [] := by intro h; subst h; simp at hr
  have htup := hv.tup i hi
  unfold negRel
  rw [if_neg hys]
  set r := ys.length with hr_def
  set t := ys.map ρ with ht_def
  -- an assignment agreeing with `ρ` below `c` gives the same tuple
  have hagree : ∀ ρ' : Assignment, (∀ v, v < c → ρ' v = ρ v) → ys.map ρ' = t := fun ρ' h =>
    List.map_congr_left fun v hv => h v (hyc v hv)
  have hlen : ∀ u ∈ D.L i, u.length = r := fun u hu => by rw [(htup u hu).1, hl]
  constructor
  · rintro ⟨ρ', ha, hu, hs⟩ ht
    have hyt := hagree ρ' fun v hv => ha v (Or.inl hv)
    have hyN' : ∀ v ∈ ys, ρ' v < D.N := fun v hv => by rw [ha v (Or.inl (hyc v hv))]; exact hyN v hv
    have huN : ∀ v ∈ List.range' c r, ρ' v < D.N := fun v hv => by
      rw [mem_range'_iff] at hv; exact hu v hv.1 (by omega)
    have hvN : ∀ v ∈ List.range' (c + r) r, ρ' v < D.N := fun v hv => by
      rw [mem_range'_iff] at hv; exact hu v (by omega) (by omega)
    have hne1 : List.range' c r ≠ [] := by simp; omega
    have hne2 : List.range' (c + r) r ≠ [] := by simp; omega
    simp only [Sat] at hs
    rcases hs with hz | ⟨hf, hlex⟩ | ⟨hs', hl1, hl2⟩ | ⟨hl', hlex⟩
    · obtain ⟨hL, -⟩ := (NData.mem_rel_z hv hi).mp hz
      rw [hL] at ht; simp at ht
    · obtain ⟨-, he⟩ := (NData.mem_rel_f hv hi).mp hf
      rw [sat_lexF hv ∅ ρ' (by simp [hr_def]) hys hyN' huN, hyt, he] at hlex
      exact absurd (lt_of_lt_of_le hlex (minL_le ht)) (lt_irrefl _)
    · obtain ⟨u, hu, v, hsv, he⟩ := (NData.mem_rel_s hv hi).mp hs'
      rw [List.map_append] at he
      obtain ⟨rfl, rfl⟩ := List.append_inj he (by rw [hlen u hu]; simp)
      rw [sat_lexF hv ∅ ρ' (by simp [hr_def]) hne1 huN hyN', hyt] at hl1
      rw [sat_lexF hv ∅ ρ' (by simp [hr_def]) hys hyN' hvN, hyt] at hl2
      have := (succOf_some hsv).2.2 t ht hl1
      exact absurd (lt_of_lt_of_le hl2 this) (lt_irrefl _)
    · obtain ⟨-, he⟩ := (NData.mem_rel_l hv hi).mp hl'
      rw [sat_lexF hv ∅ ρ' (by simp [hr_def]) hne2 hvN hyN', hyt, he] at hlex
      exact absurd (lt_of_lt_of_le hlex (le_maxL ht)) (lt_irrefl _)
  · intro hnot
    -- a witness from two tuples `u`, `v` of `R_i`
    have wit : ∀ θ : Formula, ∀ u ∈ D.L i, ∀ v ∈ D.L i,
        Sat (NData.toStructure hv) ∅ θ (asg ρ c u v) → Ext (NData.toStructure hv) θ c (2 * r) ρ := by
      intro θ u hu v hvL hs
      refine ⟨asg ρ c u v, fun w hw => ?_, fun w h1 h2 => ?_, hs⟩
      · rcases hw with hw | hw
        · exact asg_of_lt hw
        · exact asg_of_ge (by rw [hlen u hu]; omega)
      · exact asg_lt (by rw [hlen v hvL, hlen u hu]) (htup u hu).2 (htup v hvL).2 h1
          (by rw [hlen u hu]; omega)
    have hya : ∀ u v : List ℕ, ys.map (asg ρ c u v) = t := fun u v =>
      hagree _ fun w hw => asg_of_lt hw
    have hyNa : ∀ u v : List ℕ, ∀ w ∈ ys, asg ρ c u v w < D.N := fun u v w hw => by
      rw [asg_of_lt (hyc w hw)]; exact hyN w hw
    have hml : ∀ u ∈ D.L i, ∀ v, (List.range' c r).map (asg ρ c u v) = u := fun u hu v => by
      have := map_asg_left ρ c u v; rwa [hlen u hu] at this
    have hmr : ∀ u ∈ D.L i, ∀ v ∈ D.L i, (List.range' (c + r) r).map (asg ρ c u v) = v :=
      fun u hu v hvL => by
        have := map_asg_right ρ c u v (by rw [hlen v hvL, hlen u hu]); rwa [hlen u hu] at this
    have huNa : ∀ u ∈ D.L i, ∀ v ∈ D.L i, ∀ w ∈ List.range' c r, asg ρ c u v w < D.N :=
      fun u hu v hvL w hw => by
        rw [mem_range'_iff] at hw
        exact asg_lt (by rw [hlen v hvL, hlen u hu]) (htup u hu).2 (htup v hvL).2 hw.1
          (by rw [hlen u hu]; omega)
    have hvNa : ∀ u ∈ D.L i, ∀ v ∈ D.L i, ∀ w ∈ List.range' (c + r) r, asg ρ c u v w < D.N :=
      fun u hu v hvL w hw => by
        rw [mem_range'_iff] at hw
        exact asg_lt (by rw [hlen v hvL, hlen u hu]) (htup u hu).2 (htup v hvL).2 (by omega)
          (by rw [hlen u hu]; omega)
    have hne1 : List.range' c r ≠ [] := by simp; omega
    have hne2 : List.range' (c + r) r ≠ [] := by simp; omega
    by_cases hL : D.L i = []
    · -- no tuples: `Z_i y_0`
      obtain ⟨y, ys', hyy⟩ := List.exists_cons_of_ne_nil hys
      have hN : 0 < D.N := lt_of_le_of_lt (Nat.zero_le _) (hyN y (by rw [hyy]; simp))
      refine ⟨fun w => if c ≤ w ∧ w < c + 2 * r then 0 else ρ w, fun w hw => ?_,
        fun w h1 h2 => ?_, ?_⟩
      · show (if c ≤ w ∧ w < c + 2 * r then 0 else ρ w) = ρ w
        rw [if_neg (by omega)]
      · show (if c ≤ w ∧ w < c + 2 * r then 0 else ρ w) < D.N
        rw [if_pos ⟨h1, h2⟩]; exact hN
      · left
        have hyc' := hyc y (by rw [hyy]; simp)
        refine (NData.mem_rel_z hv hi).mpr ⟨hL, ρ y, hyN y (by rw [hyy]; simp), ?_⟩
        rw [hyy]
        simp only [List.headD_cons, List.map_cons, List.map_nil]
        rw [if_neg (by omega)]
    · rcases lt_trichotomy t (minL (D.L i)) with h | h | h
      · -- below the first tuple
        have hm := minL_mem hL
        refine wit _ _ hm _ hm (Or.inr (Or.inl ⟨?_, ?_⟩))
        · exact (NData.mem_rel_f hv hi).mpr ⟨hL, hml _ hm _⟩
        · rw [sat_lexF hv ∅ _ (by simp [hr_def]) hys (hyNa _ _) (huNa _ hm _ hm), hya, hml _ hm]
          exact h
      · exact absurd (h ▸ minL_mem hL) hnot
      · rcases lt_trichotomy t (maxL (D.L i)) with h' | h' | h'
        · -- between two consecutive tuples
          set P := (D.L i).filter (fun w => decide (w < t)) with hP
          have hPne : P ≠ [] := by
            intro h0
            have : minL (D.L i) ∈ P := List.mem_filter.mpr ⟨minL_mem hL, by simpa using h⟩
            rw [h0] at this; simp at this
          set u := maxL P with hu_def
          have huP := maxL_mem hPne
          rw [← hu_def] at huP
          obtain ⟨huL, hut⟩ := List.mem_filter.mp huP
          simp only [decide_eq_true_eq] at hut
          rcases hsu : succOf (D.L i) u with _ | v
          · exact absurd (lt_trans hut h') (succOf_none.mp hsu _ (maxL_mem hL))
          · obtain ⟨hvL, huv, hmin⟩ := succOf_some hsu
            have htv : t < v := by
              rcases lt_trichotomy v t with h1 | h1 | h1
              · have : v ≤ u := le_maxL (List.mem_filter.mpr ⟨hvL, by simpa using h1⟩)
                exact absurd (lt_of_lt_of_le huv this) (lt_irrefl _)
              · exact absurd (h1 ▸ hvL) hnot
              · exact h1
            refine wit _ _ huL _ hvL (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))
            · show (List.range' c r ++ List.range' (c + r) r).map (asg ρ c u v) ∈ _
              rw [List.map_append, hml _ huL, hmr _ huL _ hvL]
              exact (NData.mem_rel_s hv hi).mpr ⟨u, huL, v, hsu, rfl⟩
            · rw [sat_lexF hv ∅ _ (by simp [hr_def]) hne1 (huNa _ huL _ hvL) (hyNa _ _), hya, hml _ huL]
              exact hut
            · rw [sat_lexF hv ∅ _ (by simp [hr_def]) hys (hyNa _ _) (hvNa _ huL _ hvL), hya,
                hmr _ huL _ hvL]
              exact htv
        · exact absurd (h' ▸ maxL_mem hL) hnot
        · -- above the last tuple
          have hm := maxL_mem hL
          refine wit _ _ hm _ hm (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
          · exact (NData.mem_rel_l hv hi).mpr ⟨hL, hmr _ hm _ hm⟩
          · rw [sat_lexF hv ∅ _ (by simp [hr_def]) hne2 (hvNa _ hm _ hm) (hyNa _ _), hya, hmr _ hm _ hm]
            exact h'

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Sem
