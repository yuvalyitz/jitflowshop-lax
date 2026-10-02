import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord

/-! # Phases 1–5: reading and compressing the structure

`header` reads `s` and `N`; `entPass` copies the entries into `E`; `foPass` marks first occurrences
in `fo`; `rkPass` writes the ranks into `R`; `Mcom` sets `M`. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord

variable {x : List ℕ} {φ : Formula} {B : ℕ}

theorem set_append_replicate (l : List ℕ) (k v : ℕ) (hk : 1 ≤ k) :
    (l ++ List.replicate k 0).set l.length v = (l ++ [v]) ++ List.replicate (k - 1) 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ, List.set_append_right _ _ (le_refl _), Nat.sub_self]
  simp

theorem set_append_replicate' (l : List ℕ) (k v i : ℕ) (hk : 1 ≤ k) (hi : i = l.length) :
    (l ++ List.replicate k 0).set i v = (l ++ [v]) ++ List.replicate (k - 1) 0 := by
  subst hi; exact set_append_replicate l k v hk

theorem getD_lt_Bv (x : List ℕ) (i : ℕ) : x.getD i 0 < Bv x := by
  have := getD_le_maxEntry x i; unfold Bv; omega

theorem len_lt_Bv (x : List ℕ) : x.length + 8 < Bv x := by
  have := len_sq_le x; unfold Bv; nlinarith

theorem len64_lt_Bv (x : List ℕ) : 64 * x.length + 64 < Bv x := by
  have := len_sq_le x; unfold Bv; nlinarith

/-! ### Header -/

theorem header_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x) header
      (fun σ σ' => (σ'.vars "s" = sOf x ∧ σ'.vars "N" = nOf x) ∧
        Keep ["s", "N"] σ σ' ∧ σ'.out = σ.out) 20 := by
  have hh := hd.hdr
  have hl := len_lt_Bv x
  have h : Spec (Bv x) (fun σ => σ.arrs "a" = x) header
      (fun _ σ' => σ'.vars "s" = sOf x ∧ σ'.vars "N" = nOf x) 20 := by
    unfold header
    refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ 0 < (σ.arrs "a").length ∧
      (σ.arrs "a").getD 0 0 = sOf x ∧ 1 + sOf x < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (1 + sOf x) 0 = nOf x ∧ sOf x < Bv x ∧ nOf x < Bv x ∧
      1 + sOf x < Bv x) ?_ ?_
    · run_vcg
      all_goals (simp_all; try omega)
    · intro σ ha
      have h1 := getD_lt_Bv x 0
      have h2 := getD_lt_Bv x (1 + sOf x)
      refine ⟨ha, by rw [ha]; omega, by rw [ha]; rfl, by rw [ha]; omega, by rw [ha]; rfl, h1, h2,
        by omega⟩
  exact Spec.keepOut h _ (by intro y hy; simpa [header, Com.wvars] using hy)
    (by simp [header, Com.warrs]) (by simp [header, Com.reads]) (by simp [header, Com.NoWrite])

/-! ### The entries -/

/-- The invariant of the inner copy loop, in block `i`. -/
def EIn (x : List ℕ) (i : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "s" = sOf x ∧ σ.vars "i" = i ∧ σ.vars "p" = bo x i ∧
    σ.vars "cr" = cntOf x i * arOf x i ∧ σ.vars "k" ≤ cntOf x i * arOf x i ∧
    σ.vars "T" = oo x i + σ.vars "k" ∧
    σ.arrs "E" = (entsUpTo x i ++ tupR x (bo x i + 1) (σ.vars "k")) ++
      List.replicate (x.length - oo x i - σ.vars "k") 0

set_option maxHeartbeats 4000000 in
theorem entIn_spec (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    Spec (Bv x) (fun σ => EIn x i σ ∧ σ.vars "k" < cntOf x i * arOf x i) entIn
      (fun σ σ' => EIn x i σ' ∧ σ'.vars "k" = σ.vars "k" + 1) 40 := by
  have hl := len_lt_Bv x
  have hb := hd.blk_le hi
  have hfs := hd.fs_le
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  refine Spec.pre (P := fun σ => (EIn x i σ ∧ σ.vars "k" < cntOf x i * arOf x i) ∧
    σ.vars "p" + 1 + σ.vars "k" < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (σ.vars "p" + 1 + σ.vars "k") 0 < Bv x ∧
    σ.vars "p" + 1 + σ.vars "k" < Bv x ∧ σ.vars "T" < (σ.arrs "E").length ∧
    σ.vars "T" + 1 < Bv x ∧ σ.vars "k" + 1 < Bv x) ?_ ?_
  · unfold entIn
    run_vcg
    all_goals
      obtain ⟨ha, hs, hi', hp, hcr, hk, hT, hE⟩ := ‹EIn x i σ›
      have hk' : σ.vars "k" < cntOf x i * arOf x i := ‹_›
      have hlen : (entsUpTo x i ++ tupR x (bo x i + 1) (σ.vars "k")).length = σ.vars "T" := by
        rw [hT]; simp [oo]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Env.setVar, Env.setArr] <;>
        (try simp only [ite_true, ite_false, String.reduceEq])
      all_goals first
        | exact ha
        | exact hs
        | exact hi'
        | exact hp
        | exact hcr
        | omega
        | (rw [hE, ← hlen, set_append_replicate _ _ _ (by omega), ha, hp, tupR_succ]
           congr 1
           (try simp only [List.append_assoc]) <;> (try congr 1) <;> omega)
  · rintro σ ⟨⟨ha, hs, hi', hp, hcr, hk, hT, hE⟩, hk'⟩
    have hEl : (σ.arrs "E").length = x.length := by
      rw [hE]; simp [oo]; unfold oo at ho; omega
    refine ⟨⟨⟨ha, hs, hi', hp, hcr, hk, hT, hE⟩, hk'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hp]; omega
    · rw [ha]; exact getD_lt_Bv x _
    · rw [hp]; omega
    · rw [hEl, hT]; omega
    · rw [hT]; omega
    · omega

/-- The invariant of the walk over the blocks. -/
def EO (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "s" = sOf x ∧ σ.vars "i" ≤ sOf x ∧ σ.vars "p" = bo x (σ.vars "i") ∧
    σ.vars "T" = oo x (σ.vars "i") ∧
    σ.arrs "E" = entsUpTo x (σ.vars "i") ++ List.replicate (x.length - oo x (σ.vars "i")) 0

set_option maxHeartbeats 4000000 in
theorem entBody_at (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    Spec (Bv x) (fun τ => EO x τ ∧ τ.vars "i" = i ∧ (τ.arrs "a" = x ∧ τ.vars "p" = bo x i)) entBody
      (fun σ σ' => EO x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (44 * x.length + 60) := by
  have hl := len_lt_Bv x
  have hb := hd.blk_le hi
  have hfs := hd.fs_le
  have hh := hd.hdr
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  have hcr : cntOf x i * arOf x i ≤ x.length := by omega
  have hc1 : x.getD (bo x i) 0 = cntOf x i := rfl
  have hr1 : x.getD (1 + i) 0 = arOf x i := rfl
  have hloop := Spec.forRangeZero (B := Bv x) (c := entIn) "k" "cr" (EIn x i) (cntOf x i * arOf x i)
    40 (by omega) (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.1) (entIn_spec hd hi)
  refine Spec.pre (P := fun τ => (EO x τ ∧ τ.vars "i" = i) ∧ τ.vars "p" < (τ.arrs "a").length ∧
    (τ.arrs "a").getD (τ.vars "p") 0 = cntOf x i ∧ 1 + τ.vars "i" < (τ.arrs "a").length ∧
    (τ.arrs "a").getD (1 + τ.vars "i") 0 = arOf x i ∧ cntOf x i < Bv x ∧ arOf x i < Bv x ∧
    cntOf x i * arOf x i < Bv x ∧ τ.vars "p" + 1 + cntOf x i * arOf x i < Bv x ∧
    τ.vars "p" + 1 < Bv x ∧ 1 + τ.vars "i" < Bv x ∧ τ.vars "i" + 1 < Bv x) ?_ ?_
  · unfold entBody loop
    run_vcg [hloop]
    all_goals
      simp only [EO, EIn, Env.setVar] at *
      simp_all [entsUpTo_succ, oo_succ, bo_succ, Nat.sub_sub, tupR]
    all_goals (try omega)
    all_goals done
  · rintro τ ⟨hEO, hi', ha, hp⟩
    refine ⟨⟨hEO, hi'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [ha, hp]; omega)
      | (rw [ha, hp]; rfl)
      | (rw [ha, hi']; omega)
      | (rw [ha, hi']; rfl)
      | (rw [← hc1]; exact getD_lt_Bv x _)
      | (rw [← hr1]; exact getD_lt_Bv x _)
      | omega
      | (rw [hp]; omega)
      | (rw [hi']; omega)

theorem entBody_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => EO x σ ∧ σ.vars "i" < sOf x) entBody
      (fun σ σ' => EO x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (44 * x.length + 60) := by
  intro σ ⟨hEO, hi⟩
  obtain ⟨i, hidef⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hidef] at hi
  exact entBody_at hd hi σ ⟨hEO, hidef, by
    obtain ⟨ha, -, -, hp, -, -⟩ := hEO; rw [hidef] at hp; exact ⟨ha, hp⟩⟩

/-- The number of entries. -/
abbrev nT (x : List ℕ) : ℕ := (entries x).length

theorem nT_eq (x : List ℕ) : nT x = oo x (sOf x) := by rw [nT, entries_eq]; rfl

theorem nT_le (hd : Dom x φ) : nT x + 2 ≤ x.length := by
  have := hd.oo_le (le_refl (sOf x)); rw [nT_eq]; omega

@[simp] theorem entsUpTo_zero (x : List ℕ) : entsUpTo x 0 = [] := by unfold entsUpTo; try rfl
@[simp] theorem bo_zero' (x : List ℕ) : bo x 0 = 2 + sOf x := by unfold bo; try rfl


/-- The array `E` after `entPass`. -/
def Ew (x : List ℕ) : List ℕ := entries x ++ List.replicate (x.length - nT x) 0

theorem entPass_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "s" = sOf x ∧
        σ.arrs "E" = List.replicate x.length 0) entPass
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "s" = sOf x ∧ σ'.vars "p" = bo x (sOf x) ∧
        σ'.vars "T" = nT x ∧ σ'.arrs "E" = Ew x)
      (10 + ((44 * x.length + 60 + 4) * sOf x + 6)) := by
  have hl := len_lt_Bv x
  have hh := hd.hdr
  have hloop := Spec.forRangeZero (B := Bv x) (c := entBody) "i" "s" (EO x) (sOf x)
    (44 * x.length + 60) (by omega) (fun σ h => h.2.2.1) (fun σ h => h.2.1) (entBody_spec hd)
  unfold entPass
  run_vcg [hloop]
  all_goals
    simp only [EO, Ew, Env.setVar] at *
    simp_all [entries_eq, oo, nT]
  all_goals (try omega)

/-! ### First occurrences -/

/-- The array `fo` after `q` turns of `foPass`. -/
def foArr (x : List ℕ) (q : ℕ) : List ℕ :=
  (List.range q).map (foL (entries x)) ++ List.replicate (x.length - q) 0

/-- The invariant of the inner scan of `foPass`. -/
def FIn (x : List ℕ) (q : ℕ) (σ : Env) : Prop :=
  σ.arrs "E" = Ew x ∧ σ.arrs "fo" = foArr x q ∧ σ.vars "q" = q ∧ σ.vars "T" = nT x ∧
    σ.vars "q2" ≤ q ∧
    σ.vars "f" = if (entries x).getD q 0 ∈ (entries x).take (σ.vars "q2") then 0 else 1

theorem Ew_getD {x : List ℕ} {q : ℕ} (hq : q < nT x) : (Ew x).getD q 0 = (entries x).getD q 0 := by
  unfold Ew
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hq, ← List.getD_eq_getElem?_getD]

theorem length_Ew (hd : Dom x φ) : (Ew x).length = x.length := by
  have := nT_le hd
  simp only [Ew, List.length_append, List.length_replicate]
  unfold nT at *; omega

theorem take_succ_getD {l : List ℕ} {q : ℕ} (hq : q < l.length) :
    l.take (q + 1) = l.take q ++ [l.getD q 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hq, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hq]; rfl

set_option maxHeartbeats 4000000 in
theorem foIn_spec (hd : Dom x φ) {q : ℕ} (hq : q < nT x) :
    Spec (Bv x) (fun σ => FIn x q σ ∧ σ.vars "q2" < q) foIn
      (fun σ σ' => FIn x q σ' ∧ σ'.vars "q2" = σ.vars "q2" + 1) 30 := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  have hEl := length_Ew hd
  refine Spec.pre (P := fun σ => (FIn x q σ ∧ σ.vars "q2" < q) ∧
    σ.vars "q2" < (σ.arrs "E").length ∧ σ.vars "q" < (σ.arrs "E").length ∧
    (σ.arrs "E").getD (σ.vars "q2") 0 < Bv x ∧ (σ.arrs "E").getD (σ.vars "q") 0 < Bv x ∧
    (σ.arrs "E").getD (σ.vars "q2") 0 = (entries x).getD (σ.vars "q2") 0 ∧
    (σ.arrs "E").getD (σ.vars "q") 0 = (entries x).getD q 0 ∧
    (entries x).take (σ.vars "q2" + 1) =
      (entries x).take (σ.vars "q2") ++ [(entries x).getD (σ.vars "q2") 0] ∧
    σ.vars "q2" + 1 < Bv x) ?_ ?_
  · unfold foIn
    run_vcg
    all_goals
      simp only [FIn, Env.setVar] at *
      simp_all
    all_goals (try omega)
    all_goals (try (split_ifs <;> simp_all))
  · rintro σ ⟨⟨hE, hfo, hq', hT', hq2, hf⟩, hlt⟩
    have hgt : ∀ i, (Ew x).getD i 0 < Bv x := fun i => by
      rw [List.getD_eq_getElem?_getD]
      rcases h : (Ew x)[i]? with _ | v
      · simp; omega
      · have hv := List.mem_of_getElem? h
        simp only [Ew, List.mem_append, List.mem_replicate] at hv
        simp only [Option.getD_some]
        rcases hv with hv | ⟨-, rfl⟩
        · rw [entries_eq] at hv
          simp only [entsUpTo, List.mem_flatMap, tupR, List.mem_map] at hv
          obtain ⟨-, -, l, -, rfl⟩ := hv
          exact getD_lt_Bv x _
        · omega
    have h1 : σ.vars "q2" < (σ.arrs "E").length := by rw [hE, hEl]; omega
    have h2 : σ.vars "q" < (σ.arrs "E").length := by rw [hE, hEl, hq']; omega
    have h3 : (σ.arrs "E").getD (σ.vars "q2") 0 = (entries x).getD (σ.vars "q2") 0 := by
      rw [hE]; exact Ew_getD (by omega)
    have h4 : (σ.arrs "E").getD (σ.vars "q") 0 = (entries x).getD q 0 := by
      rw [hE, hq']; exact Ew_getD hq
    have h5 := take_succ_getD (l := entries x) (q := σ.vars "q2") (by unfold nT at hq; omega)
    refine ⟨⟨⟨hE, hfo, hq', hT', hq2, hf⟩, hlt⟩, h1, h2, by rw [hE]; exact hgt _, by rw [hE]; exact hgt _,
      h3, h4, h5, by omega⟩

theorem Ew_lt (x : List ℕ) (i : ℕ) : (Ew x).getD i 0 < Bv x := by
  have hl := len_lt_Bv x
  rw [List.getD_eq_getElem?_getD]
  rcases h : (Ew x)[i]? with _ | v
  · simp; omega
  · have hv := List.mem_of_getElem? h
    simp only [Ew, List.mem_append, List.mem_replicate] at hv
    simp only [Option.getD_some]
    rcases hv with hv | ⟨-, rfl⟩
    · rw [entries_eq] at hv
      simp only [entsUpTo, List.mem_flatMap, tupR, List.mem_map] at hv
      obtain ⟨-, -, l, -, rfl⟩ := hv
      exact getD_lt_Bv x _
    · omega

/-- The invariant of `foPass`. -/
def FO (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "E" = Ew x ∧ σ.arrs "fo" = foArr x (σ.vars "q") ∧ σ.vars "T" = nT x ∧
    σ.vars "q" ≤ nT x

theorem foArr_succ (hd : Dom x φ) {q : ℕ} (hq : q < nT x) :
    (foArr x q).set q (foL (entries x) q) = foArr x (q + 1) := by
  have := nT_le hd
  unfold foArr
  rw [set_append_replicate' _ _ _ _ (by omega) (by simp)]
  simp [List.range_succ]; omega

set_option maxHeartbeats 4000000 in
theorem foBody_at (hd : Dom x φ) {q : ℕ} (hq : q < nT x) :
    Spec (Bv x) (fun σ => FO x σ ∧ σ.vars "q" = q) foBody
      (fun σ σ' => FO x σ' ∧ σ'.vars "q" = σ.vars "q" + 1) (34 * q + 30) := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  have hloop := Spec.forRangeZero (B := Bv x) (c := foIn) "q2" "q" (FIn x q) q 30 (by omega)
    (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.1) (foIn_spec hd hq)
  have hfl : (foArr x q).length = x.length := by simp [foArr]; omega
  have hsucc := foArr_succ hd hq
  refine Spec.pre (P := fun σ => (FO x σ ∧ σ.vars "q" = q) ∧ σ.vars "q" + 1 < Bv x) ?_ ?_
  · unfold foBody loop
    run_vcg [hloop]
    all_goals
      simp only [FO, FIn, Env.setVar, Env.setArr] at *
      simp_all [foL]
    all_goals (try omega)
    all_goals (try (split_ifs <;> omega))
  · rintro σ ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩

theorem foBody_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => FO x σ ∧ σ.vars "q" < nT x) foBody
      (fun σ σ' => FO x σ' ∧ σ'.vars "q" = σ.vars "q" + 1) (34 * x.length + 30) := by
  intro σ ⟨hFO, hq⟩
  obtain ⟨q, hqd⟩ : ∃ q, σ.vars "q" = q := ⟨_, rfl⟩
  rw [hqd] at hq
  obtain ⟨σ', hr, hq'⟩ := foBody_at hd hq σ ⟨hFO, hqd⟩
  have := nT_le hd
  exact ⟨σ', hr.mono (by omega), hq'⟩

theorem foPass_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "E" = Ew x ∧ σ.vars "T" = nT x ∧
        σ.arrs "fo" = List.replicate x.length 0) foPass
      (fun _ σ' => σ'.arrs "E" = Ew x ∧ σ'.vars "T" = nT x ∧ σ'.arrs "fo" = foArr x (nT x))
      ((34 * x.length + 30 + 4) * nT x + 6) := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  refine Spec.post (Spec.pre (Spec.forRangeZero "q" "T" (FO x) (nT x) (34 * x.length + 30)
    (by omega) (fun σ h => h.2.2.2) (fun σ h => h.2.2.1) (foBody_spec hd)) ?_) ?_
  · rintro σ ⟨hE, hT', hfo⟩
    simp [FO, Env.setVar, hE, hT', hfo, foArr]
  · rintro σ σ' - ⟨⟨hE, hfo, hT', -⟩, hq⟩
    exact ⟨hE, hT', by rw [hfo, hq]⟩

/-! ### Ranks -/

/-- The array `R` after `t` turns of `rkPass`. -/
def rArr (x : List ℕ) (t : ℕ) : List ℕ :=
  (List.range t).map (fun t' => rkCount (entries x) ((entries x).getD t' 0) (nT x)) ++
    List.replicate (x.length - t) 0

theorem foArr_getD {q : ℕ} (hq : q < nT x) :
    (foArr x (nT x)).getD q 0 = foL (entries x) q := by
  unfold foArr
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hq)]
  simp [hq]

theorem foL_le (E : List ℕ) (q : ℕ) : foL E q ≤ 1 := by unfold foL; split_ifs <;> omega

theorem rkCount_le (E : List ℕ) (e q : ℕ) : rkCount E e q ≤ q := by
  induction q with
  | zero => simp [rkCount]
  | succ q ih => rw [rkCount_succ]; have := foL_le E q; split_ifs <;> omega

/-- The invariant of the inner count of `rkPass`. -/
def RIn (x : List ℕ) (t : ℕ) (σ : Env) : Prop :=
  σ.arrs "E" = Ew x ∧ σ.arrs "fo" = foArr x (nT x) ∧ σ.arrs "R" = rArr x t ∧ σ.vars "t" = t ∧
    σ.vars "T" = nT x ∧ σ.vars "q" ≤ nT x ∧
    σ.vars "cn" = rkCount (entries x) ((entries x).getD t 0) (σ.vars "q")

set_option maxHeartbeats 4000000 in
theorem rkIn_spec (hd : Dom x φ) {t : ℕ} (ht : t < nT x) :
    Spec (Bv x) (fun σ => RIn x t σ ∧ σ.vars "q" < nT x) rkIn
      (fun σ σ' => RIn x t σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 40 := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  have hEl := length_Ew hd
  have hfl : (foArr x (nT x)).length = x.length := by simp [foArr]; omega
  refine Spec.pre (P := fun σ => (RIn x t σ ∧ σ.vars "q" < nT x) ∧
    σ.vars "q" < (σ.arrs "E").length ∧ σ.vars "t" < (σ.arrs "E").length ∧
    σ.vars "q" < (σ.arrs "fo").length ∧
    (σ.arrs "E").getD (σ.vars "q") 0 < Bv x ∧ (σ.arrs "E").getD (σ.vars "t") 0 < Bv x ∧
    (σ.arrs "E").getD (σ.vars "q") 0 = (entries x).getD (σ.vars "q") 0 ∧
    (σ.arrs "E").getD (σ.vars "t") 0 = (entries x).getD t 0 ∧
    (σ.arrs "fo").getD (σ.vars "q") 0 = foL (entries x) (σ.vars "q") ∧
    (σ.arrs "fo").getD (σ.vars "q") 0 < Bv x ∧
    σ.vars "cn" + foL (entries x) (σ.vars "q") < Bv x ∧ σ.vars "q" + 1 < Bv x) ?_ ?_
  · unfold rkIn
    run_vcg
    all_goals
      simp only [RIn, Env.setVar] at *
      simp_all [rkCount_succ]
    all_goals (try omega)
  · rintro σ ⟨⟨hE, hfo, hR, ht', hT', hq, hc⟩, hlt⟩
    have h1 : (σ.arrs "E").getD (σ.vars "q") 0 = (entries x).getD (σ.vars "q") 0 := by
      rw [hE]; exact Ew_getD hlt
    have h2 : (σ.arrs "E").getD (σ.vars "t") 0 = (entries x).getD t 0 := by
      rw [hE, ht']; exact Ew_getD ht
    have h3 : (σ.arrs "fo").getD (σ.vars "q") 0 = foL (entries x) (σ.vars "q") := by
      rw [hfo]; exact foArr_getD hlt
    have h4 := foL_le (entries x) (σ.vars "q")
    have h5 := rkCount_le (entries x) ((entries x).getD t 0) (σ.vars "q")
    refine ⟨⟨⟨hE, hfo, hR, ht', hT', hq, hc⟩, hlt⟩, by rw [hE, hEl]; omega,
      by rw [hE, hEl, ht']; omega, by rw [hfo, hfl]; omega, by rw [hE]; exact Ew_lt x _,
      by rw [hE]; exact Ew_lt x _, h1, h2, h3, by rw [h3]; omega, by rw [hc]; omega, by omega⟩

/-- The invariant of `rkPass`. -/
def RO (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "E" = Ew x ∧ σ.arrs "fo" = foArr x (nT x) ∧ σ.arrs "R" = rArr x (σ.vars "t") ∧
    σ.vars "T" = nT x ∧ σ.vars "t" ≤ nT x

theorem rArr_succ (hd : Dom x φ) {t : ℕ} (ht : t < nT x) :
    (rArr x t).set t (rkCount (entries x) ((entries x).getD t 0) (nT x)) = rArr x (t + 1) := by
  have := nT_le hd
  unfold rArr
  rw [set_append_replicate' _ _ _ _ (by omega) (by simp)]
  simp [List.range_succ]; omega

set_option maxHeartbeats 4000000 in
theorem rkBody_at (hd : Dom x φ) {t : ℕ} (ht : t < nT x) :
    Spec (Bv x) (fun σ => RO x σ ∧ σ.vars "t" = t) rkBody
      (fun σ σ' => RO x σ' ∧ σ'.vars "t" = σ.vars "t" + 1) (44 * x.length + 30) := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  have hloop := Spec.forRangeZero (B := Bv x) (c := rkIn) "q" "T" (RIn x t) (nT x) 40 (by omega)
    (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.1) (rkIn_spec hd ht)
  have hrl : (rArr x t).length = x.length := by simp [rArr]; omega
  have hsucc := rArr_succ hd ht
  have hcle := rkCount_le (entries x) ((entries x).getD t 0) (nT x)
  refine Spec.pre (P := fun σ => (RO x σ ∧ σ.vars "t" = t) ∧ σ.vars "t" + 1 < Bv x) ?_ ?_
  · refine Spec.mono (K := 1 + 1 + ((40 + 4) * nT x + 6 + (1 + 1 + 1 + 5))) ?_ (by omega)
    unfold rkBody loop
    run_vcg [hloop]
    all_goals
      simp only [RO, RIn, Env.setVar, Env.setArr] at *
      simp_all [rkCount]
    all_goals (try omega)
  · rintro σ ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩

theorem rkBody_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => RO x σ ∧ σ.vars "t" < nT x) rkBody
      (fun σ σ' => RO x σ' ∧ σ'.vars "t" = σ.vars "t" + 1) (44 * x.length + 30) := by
  intro σ ⟨hRO, ht⟩
  obtain ⟨t, htd⟩ : ∃ t, σ.vars "t" = t := ⟨_, rfl⟩
  rw [htd] at ht
  exact rkBody_at hd ht σ ⟨hRO, htd⟩

/-- The array `R` after `rkPass`: the ranks of the entries. -/
def Rw (x : List ℕ) : List ℕ := (entries x).map (rkx x) ++ List.replicate (x.length - nT x) 0

theorem rArr_full (x : List ℕ) : rArr x (nT x) = Rw x := by
  unfold rArr Rw
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [rkCount_eq, rkx, Ux]
  simp only [List.length_map] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

theorem rkPass_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "E" = Ew x ∧ σ.arrs "fo" = foArr x (nT x) ∧ σ.vars "T" = nT x ∧
        σ.arrs "R" = List.replicate x.length 0) rkPass
      (fun _ σ' => σ'.arrs "R" = Rw x) ((44 * x.length + 30 + 4) * nT x + 6) := by
  have hl := len_lt_Bv x
  have hT := nT_le hd
  refine Spec.post (Spec.pre (Spec.forRangeZero "t" "T" (RO x) (nT x) (44 * x.length + 30)
    (by omega) (fun σ h => h.2.2.2.2) (fun σ h => h.2.2.2.1) (rkBody_spec hd)) ?_) ?_
  · rintro σ ⟨hE, hfo, hT', hR⟩
    simp [RO, Env.setVar, hE, hfo, hT', hR, rArr]
  · rintro σ σ' - ⟨⟨-, -, hR, -, -⟩, ht⟩
    rw [hR, ht, rArr_full]

/-! ### The size of the compressed universe -/

theorem Mcom_spec :
    Spec (Bv x) (fun σ => σ.vars "N" = nOf x ∧ σ.vars "T" = nT x ∧ σ.vars "rt_n" = x.length ∧
        nT x + x.length < Bv x ∧ nOf x < Bv x) Mcom
      (fun σ σ' => σ'.vars "M" = MOf x ∧ Keep ["M"] σ σ' ∧ σ'.out = σ.out) 20 := by
  have h : Spec (Bv x) (fun σ => σ.vars "N" = nOf x ∧ σ.vars "T" = nT x ∧
      σ.vars "rt_n" = x.length ∧ nT x + x.length < Bv x ∧ nOf x < Bv x) Mcom
      (fun _ σ' => σ'.vars "M" = MOf x) 20 := by
    unfold Mcom
    run_vcg
    all_goals
      simp only [Env.setVar] at *
      simp_all [MOf]
    all_goals omega
  exact Spec.keepOut h _ (by intro y hy; simpa [Mcom, Com.wvars] using hy)
    (by simp [Mcom, Com.warrs]) (by simp [Mcom, Com.reads]) (by simp [Mcom, Com.NoWrite])

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre
