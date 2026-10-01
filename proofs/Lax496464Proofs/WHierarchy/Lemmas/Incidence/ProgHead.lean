import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom

/-! # Phases 1–3: reading the header, walking the blocks, the largest entry

`header_spec`: the number of symbols and the size of the universe; `blocks_spec`: the start of the
formula and the number of tuples; `maxPass_spec`: the first fresh variable `1 + max x`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgHead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-! ### Header -/

theorem header_value (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x) header
      (fun _ σ' => σ'.vars "ic_s" = sOf x ∧ σ'.vars "ic_N" = nOf x) 20 := by
  have hh := hdr_lt hd
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold header
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ 0 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD 0 0 = sOf x ∧ 1 + sOf x < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (1 + sOf x) 0 = nOf x ∧ sOf x < B ∧ nOf x < B ∧ 1 + sOf x < B) ?_ ?_
  · run_vcg
    all_goals (simp_all; try omega)
  · intro σ ha
    have h1 := getD_lt hB 0
    have h2 := getD_lt hB (1 + sOf x)
    refine ⟨ha, by rw [ha]; omega, by rw [ha]; rfl, by rw [ha]; omega, by rw [ha]; rfl, h1, h2,
      by omega⟩

theorem header_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x) header
      (fun σ σ' => (σ'.vars "ic_s" = sOf x ∧ σ'.vars "ic_N" = nOf x) ∧
        Keep ["ic_s", "ic_N"] σ σ' ∧ σ'.out = σ.out) 20 :=
  Spec.keepOut (header_value hd hB) _ (by intro y hy; simpa [header, Com.wvars] using hy)
    (by simp [header, Com.warrs]) (by simp [header, Com.reads]) (by simp [header, Com.NoWrite])

/-! ### Blocks -/

/-- The invariant of the walk over the blocks. -/
def BI (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_i" ≤ sOf x ∧
    σ.vars "ic_b" = bo x (σ.vars "ic_i") ∧ σ.vars "ic_g" = poOf x (σ.vars "ic_i")

set_option maxHeartbeats 1000000 in
theorem blockBody_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => BI x σ ∧ σ.vars "ic_i" < sOf x) blockBody
      (fun σ σ' => BI x σ' ∧ σ'.vars "ic_i" = σ.vars "ic_i" + 1) 40 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hh := hdr_lt hd
  unfold blockBody
  refine Spec.pre (P := fun σ => BI x σ ∧ σ.vars "ic_i" < sOf x ∧
      σ.vars "ic_b" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_b") 0 = cntOf x (σ.vars "ic_i") ∧
      1 + σ.vars "ic_i" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (1 + σ.vars "ic_i") 0 = arOf x (σ.vars "ic_i") ∧
      cntOf x (σ.vars "ic_i") < B ∧ arOf x (σ.vars "ic_i") < B ∧
      poOf x (σ.vars "ic_i") + cntOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b" + 1 < B ∧ cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b" + 1 + cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      1 + σ.vars "ic_i" < B ∧ σ.vars "ic_i" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [BI] at *; simp_all [Env.setVar, bo_succ, poOf_succ]; try omega)
  · rintro σ ⟨⟨ha, hs, hi, hbo, hg⟩, hlt⟩
    have h1 := bo_lt hd (i := σ.vars "ic_i") (by omega)
    have h2 := bo_succ_le hd (i := σ.vars "ic_i") (by omega)
    have h3 := po_le_bo hd 0 (σ.vars "ic_i" + 1) (by omega)
    rw [po_dataOf, poOf_succ] at h3
    rw [bo_succ] at h2
    have hc := getD_lt hB (bo x (σ.vars "ic_i"))
    have har := getD_lt hB (1 + σ.vars "ic_i")
    refine ⟨⟨ha, hs, hi, hbo, hg⟩, hlt, ?_, ?_, ?_, ?_, hc, har, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hbo]; exact h1
    · rw [ha, hbo]; rfl
    · rw [ha]; omega
    · rw [ha]; rfl
    · have h4 := bo_succ_le hd (i := σ.vars "ic_i") (by omega); omega
    · rw [hbo]; omega
    · omega
    · rw [hbo]; omega
    · omega
    · omega

theorem blockLoop_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => BI x (σ.setVar "ic_i" 0)) blockLoop
      (fun _ σ' => BI x σ' ∧ σ'.vars "ic_i" = sOf x) ((40 + 4) * sOf x + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hh := hdr_lt hd
  exact Spec.forRangeZero "ic_i" "ic_s" (BI x) (sOf x) 40 (by omega) (fun σ h => h.2.2.1)
    (fun σ h => h.2.1) (blockBody_spec hd hB)

theorem blocks_value (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x) blocks
      (fun _ σ' => σ'.vars "ic_b" = bo x (sOf x) ∧ σ'.vars "ic_g" = tOf x)
      (10 + (40 + 4) * sOf x + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hh := hdr_lt hd
  unfold blocks
  run_vcg [blockLoop_spec hd hB]
  all_goals (simp only [BI, tOf] at *; simp_all [Env.setVar, bo_zero]; try omega)
  all_goals (simp [poOf])

/-- The scalars `blocks` assigns. -/
def blockVars : List String := ["ic_b", "ic_g", "ic_i", "ic_c"]

theorem blocks_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x) blocks
      (fun σ σ' => (σ'.vars "ic_b" = bo x (sOf x) ∧ σ'.vars "ic_g" = tOf x) ∧
        Keep blockVars σ σ' ∧ σ'.out = σ.out) (10 + (40 + 4) * sOf x + 6) :=
  Spec.keepOut (blocks_value hd hB) _
    (by intro y hy; simp [blocks, blockLoop, blockBody, bump, Com.wvars] at hy
        simp [blockVars]; tauto)
    (by simp [blocks, blockLoop, blockBody, bump, Com.warrs])
    (by simp [blocks, blockLoop, blockBody, bump, Com.reads])
    (by simp [blocks, blockLoop, blockBody, bump, Com.NoWrite])

/-! ### The largest entry -/

theorem maxEntry_take_succ (x : List ℕ) {p : ℕ} (hp : p < x.length) :
    maxEntry (x.take (p + 1)) =
      if maxEntry (x.take p) < x.getD p 0 then x.getD p 0 else maxEntry (x.take p) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hp]
  have : ∀ l : List ℕ, ∀ a : ℕ, maxEntry (l ++ [a]) = max (maxEntry l) a := by
    intro l a
    induction l with
    | nil => simp [maxEntry]
    | cons b l ih =>
      simp only [List.cons_append, maxEntry, List.foldr_cons] at ih ⊢
      rw [ih]; omega
  simp only [Option.toList_some]
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  split_ifs <;> omega

/-- The invariant of the scan for the largest entry. -/
def MI (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "ic_p" ≤ x.length ∧
    σ.vars "ic_m" = maxEntry (x.take (σ.vars "ic_p"))

theorem maxEntry_take_le (x : List ℕ) (p : ℕ) : maxEntry (x.take p) ≤ maxEntry x := by
  induction x generalizing p with
  | nil => simp
  | cons a x ih =>
    cases p with
    | zero => simp [maxEntry]
    | succ p =>
      simp only [List.take_succ_cons, maxEntry, List.foldr_cons] at ih ⊢
      have := ih p; omega

set_option maxHeartbeats 1000000 in
theorem maxBody_spec (hB : BOK x B) :
    Spec B (fun σ => MI x σ ∧ σ.vars "ic_p" < x.length) maxBody
      (fun σ σ' => MI x σ' ∧ σ'.vars "ic_p" = σ.vars "ic_p" + 1) 30 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold maxBody
  refine Spec.pre (P := fun σ => MI x σ ∧ σ.vars "ic_p" < x.length ∧
      σ.vars "ic_p" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (σ.vars "ic_p") 0 < B ∧
      σ.vars "ic_m" < B ∧ σ.vars "ic_p" + 1 < B ∧
      maxEntry (x.take (σ.vars "ic_p" + 1)) =
        if σ.vars "ic_m" < (σ.arrs "a").getD (σ.vars "ic_p") 0 then
          (σ.arrs "a").getD (σ.vars "ic_p") 0 else σ.vars "ic_m") ?_ ?_
  · run_vcg
    all_goals (simp only [MI] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨ha, hn, hp, hm⟩, hlt⟩
    have := maxEntry_take_le x (σ.vars "ic_p")
    refine ⟨⟨ha, hn, hp, hm⟩, hlt, by rw [ha]; exact hlt, by rw [ha]; exact getD_lt hB _,
      by omega, by omega, ?_⟩
    rw [ha, hm]; exact maxEntry_take_succ x hlt

theorem maxLoop_spec (hB : BOK x B) :
    Spec B (fun σ => MI x (σ.setVar "ic_p" 0)) maxLoop
      (fun _ σ' => MI x σ' ∧ σ'.vars "ic_p" = x.length) ((30 + 4) * x.length + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  exact Spec.forRangeZero "ic_p" "rt_n" (MI x) x.length 30 (by omega) (fun σ h => h.2.2.1)
    (fun σ h => h.2.1) (maxBody_spec hB)

theorem maxPass_value (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) maxPass
      (fun _ σ' => σ'.vars "ic_F" = fOf x) (10 + (30 + 4) * x.length + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  unfold maxPass
  run_vcg [maxLoop_spec hB]
  all_goals (simp only [MI, fOf] at *; simp_all [Env.setVar]; try omega)
  all_goals (simp [maxEntry])

/-- The scalars `maxPass` assigns. -/
def maxVars : List String := ["ic_m", "ic_p", "ic_F"]

theorem maxPass_spec (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) maxPass
      (fun σ σ' => σ'.vars "ic_F" = fOf x ∧ Keep maxVars σ σ' ∧ σ'.out = σ.out)
      (10 + (30 + 4) * x.length + 6) :=
  Spec.keepOut (maxPass_value hB) _
    (by intro y hy; simp [maxPass, maxLoop, maxBody, bump, Com.wvars] at hy
        simp [maxVars]; tauto)
    (by simp [maxPass, maxLoop, maxBody, bump, Com.warrs])
    (by simp [maxPass, maxLoop, maxBody, bump, Com.reads])
    (by simp [maxPass, maxLoop, maxBody, bump, Com.NoWrite])

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgHead
