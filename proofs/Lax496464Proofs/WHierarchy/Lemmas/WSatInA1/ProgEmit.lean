import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow

/-! # Phase 9: writing the blocks of the relations

`emitCom` with tag `w_tg` and arity `w_ar` writes the block of the tuples with that tag: their number,
then their entries, one tuple per stored value at its first occurrence. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The tuples of tag `g` are stored at the positions satisfying `sel`. -/
def sel (cl : List (List ℕ)) (d k g t : ℕ) : Bool :=
  decide ((hs cl d k).getD t 0 % MM cl = g ∧ (fe cl d k).getD t 0 = t)

/-- The positions below `t` holding a tuple of tag `g`. -/
def selL (cl : List (List ℕ)) (d k g t : ℕ) : List ℕ := (List.range t).filter (sel cl d k g)

theorem selL_succ (g t : ℕ) :
    selL cl d k g (t + 1) = selL cl d k g t ++ (if sel cl d k g t then [t] else []) := by
  unfold selL; rw [List.range_succ, List.filter_append]; simp [List.filter]
  split <;> simp_all

theorem emitList_eq (g a : ℕ) : emitList cl d k g a =
    (selL cl d k g (sz cl d k)).map fun t => digitsOf (MM cl) a ((hs cl d k).getD t 0 / MM cl) := by
  rfl

theorem fe_lt {t : ℕ} (ht : t < sz cl d k) : (fe cl d k).getD t 0 < sz cl d k := by
  rw [fe_getD cl d k ht]
  have := List.idxOf_lt_length_of_mem (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem
    (l := hs cl d k) (p := t) (by rw [length_hs]; exact ht))
  rwa [length_hs] at this

theorem length_fe : (fe cl d k).length = sz cl d k := by
  simp [fe, Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts, length_hs]

/-! ### Counting -/

/-- The context of the emission. -/
def EC (cl : List (List ℕ)) (d k g : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "hs_mem" = hs cl d k ∧ σ.arrs "fp_f" = fe cl d k ∧ σ.vars "w_tg" = g

def CNI (cl : List (List ℕ)) (d k g : ℕ) (σ : Env) : Prop :=
  EC cl d k g σ ∧ σ.vars "w_t" ≤ sz cl d k ∧ σ.vars "w_cn" = (selL cl d k g (σ.vars "w_t")).length

set_option maxHeartbeats 4000000 in
theorem cntBody_spec (hB : BB cl d k B) {g : ℕ} (hg : g < B) :
    Spec B (fun σ => CNI cl d k g σ ∧ σ.vars "w_t" < sz cl d k)
      (.seq (tagIte (bump "w_cn")) (bump "w_t"))
      (fun σ σ' => CNI cl d k g σ' ∧ σ'.vars "w_t" = σ.vars "w_t" + 1) 40 := by
  have hszB := hB.cb.sz
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => CNI cl d k g σ ∧ σ.vars "w_t" < sz cl d k ∧
      σ.vars "w_t" < (σ.arrs "hs_mem").length ∧ σ.vars "w_t" < (σ.arrs "fp_f").length ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 < B ∧ (σ.arrs "fp_f").getD (σ.vars "w_t") 0 < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 / σ.vars "w_M" < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 / σ.vars "w_M" * σ.vars "w_M" < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 - (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 /
        σ.vars "w_M" * σ.vars "w_M" = (hs cl d k).getD (σ.vars "w_t") 0 % MM cl ∧
      (σ.arrs "fp_f").getD (σ.vars "w_t") 0 = (fe cl d k).getD (σ.vars "w_t") 0 ∧
      σ.vars "w_M" < B ∧ σ.vars "w_cn" + 1 < B ∧ σ.vars "w_t" + 1 < B ∧
      (selL cl d k g (σ.vars "w_t" + 1)).length = (selL cl d k g (σ.vars "w_t")).length +
        (if sel cl d k g (σ.vars "w_t") then 1 else 0)) ?_ ?_
  · unfold tagIte
    run_vcg
    all_goals (try simp only [CNI, EC, sel, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨hE, ht, hcn⟩, hlt⟩
    have hh := hE.2.1
    have hf := hE.2.2.1
    have hM := hE.1.hM
    have hv := hs_lt hB (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (l := hs cl d k)
      (p := σ.vars "w_t") (by rw [length_hs]; exact hlt))
    have hfe := fe_lt (cl := cl) (d := d) (k := k) hlt
    have hq : (hs cl d k).getD (σ.vars "w_t") 0 / MM cl ≤ (hs cl d k).getD (σ.vars "w_t") 0 :=
      Nat.div_le_self _ _
    have hq2 : (hs cl d k).getD (σ.vars "w_t") 0 / MM cl * MM cl ≤
        (hs cl d k).getD (σ.vars "w_t") 0 := Nat.div_mul_le_self _ _
    have hcnl : (selL cl d k g (σ.vars "w_t")).length ≤ σ.vars "w_t" := by
      unfold selL; exact (List.length_filter_le _ _).trans (by simp)
    refine ⟨⟨hE, ht, hcn⟩, hlt, by rw [hh, length_hs]; exact hlt, by rw [hf, length_fe]; exact hlt,
      by rw [hh]; exact hv, by rw [hf]; omega, by rw [hh, hM]; omega, by rw [hh, hM]; omega,
      by rw [hh, hM, mod_eq_sub], by rw [hf], by rw [hM]; have := MM_ge cl; omega,
      by rw [hcn]; omega, by omega, ?_⟩
    rw [selL_succ]; split <;> simp

theorem cntLoop_spec (hB : BB cl d k B) {g : ℕ} (hg : g < B) :
    Spec B (fun σ => CNI cl d k g (σ.setVar "w_t" 0))
      (loop "w_t" "hs_t" (.seq (tagIte (bump "w_cn")) (bump "w_t")))
      (fun _ σ' => CNI cl d k g σ' ∧ σ'.vars "w_t" = sz cl d k) (44 * sz cl d k + 6) := by
  have hszB := hB.cb.sz
  exact Spec.forRangeZero "w_t" "hs_t" (CNI cl d k g) (sz cl d k) 40 (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1.1.ht) (cntBody_spec hB hg)

/-! ### The digits of one number -/

def DI (M a v : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "w_M" = M ∧ σ.vars "w_ar" = a ∧ σ.vars "w_p" ≤ a ∧ σ.vars "w_e" = v / M ^ σ.vars "w_p" ∧
    σ.out = out0 ++ (List.range (σ.vars "w_p")).map fun p => v / M ^ p % M

theorem digBody_spec {M a v : ℕ} {out0 : List ℕ} (hvB : v < B) (haB : a + 1 < B) (hMB : M < B) :
    Spec B (fun σ => DI M a v out0 σ ∧ σ.vars "w_p" < a) digBody
      (fun σ σ' => DI M a v out0 σ' ∧ σ'.vars "w_p" = σ.vars "w_p" + 1) 30 := by
  refine Spec.pre (P := fun σ => DI M a v out0 σ ∧ σ.vars "w_p" < a ∧ σ.vars "w_e" < B ∧
      σ.vars "w_e" / σ.vars "w_M" < B ∧ σ.vars "w_e" / σ.vars "w_M" * σ.vars "w_M" < B ∧
      σ.vars "w_e" - σ.vars "w_e" / σ.vars "w_M" * σ.vars "w_M" = v / M ^ σ.vars "w_p" % M ∧
      σ.vars "w_e" / σ.vars "w_M" = v / M ^ (σ.vars "w_p" + 1) ∧ σ.vars "w_M" < B ∧
      σ.vars "w_p" + 1 < B) ?_ ?_
  · unfold digBody
    run_vcg
    all_goals (try simp only [DI] at *)
    all_goals (try simp_all [Env.setVar, List.range_succ]; try omega)
  · rintro σ ⟨⟨hM, ha, hp, he, ho⟩, hlt⟩
    have h1 : v / M ^ σ.vars "w_p" ≤ v := Nat.div_le_self _ _
    have h2 : v / M ^ σ.vars "w_p" / M ≤ v / M ^ σ.vars "w_p" := Nat.div_le_self _ _
    have h3 : v / M ^ σ.vars "w_p" / M * M ≤ v / M ^ σ.vars "w_p" := Nat.div_mul_le_self _ _
    refine ⟨⟨hM, ha, hp, he, ho⟩, hlt, by rw [he]; omega, by rw [he, hM]; omega,
      by rw [he, hM]; omega, by rw [he, hM, mod_eq_sub], ?_, by rw [hM]; exact hMB, by omega⟩
    rw [he, hM, Nat.div_div_eq_div_mul, pow_succ]

/-- The cost of the digits of one number. -/
def Kdig (d k : ℕ) : ℕ := 34 * (d + k + 2) + 20

theorem digits_spec (hB : BB cl d k B) {a : ℕ} (ha : a ≤ d + k + 2) :
    Spec B (fun σ => σ.arrs "hs_mem" = hs cl d k ∧ σ.vars "w_M" = MM cl ∧ σ.vars "w_ar" = a ∧
        σ.vars "w_t" < sz cl d k) digits
      (fun σ σ' => σ'.out = σ.out ++ digitsOf (MM cl) a ((hs cl d k).getD (σ.vars "w_t") 0 / MM cl) ∧
        (∀ y, y ≠ "w_e" → y ≠ "w_p" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp) (Kdig d k) := by
  rintro σ ⟨hh, hM, har, ht⟩
  have hMB := hB.cb.small
  set v := (hs cl d k).getD (σ.vars "w_t") 0 / MM cl with hvdef
  have hv0 := hs_lt hB (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (l := hs cl d k)
      (p := σ.vars "w_t") (by rw [length_hs]; exact ht))
  have hvB : v < B := lt_of_le_of_lt (Nat.div_le_self _ _) hv0
  have hszB := hB.cb.sz
  have he : (Expr.div (.get "hs_mem" (V "w_t")) (V "w_M")).evalB B σ = some v := by
    rw [hvdef, ← hh, ← hM]
    refine evalB_bin (evalB_get (evalB_var (by omega)) ?_ (by rw [hh]; exact hv0))
      (evalB_var (by rw [hM]; omega)) (by simp; rw [hh, hM]; exact hvB)
    rw [List.getElem?_eq_getElem (by rw [hh, length_hs]; exact ht)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hh, length_hs]; exact ht :
      σ.vars "w_t" < (σ.arrs "hs_mem").length)]
  have r1 : Run B (.assign "w_e" (.div (.get "hs_mem" (V "w_t")) (V "w_M"))) σ
      (σ.setVar "w_e" v) 5 := Run.assign he
  have hloop := Spec.forRangeZero (B := B) "w_p" "w_ar" (DI (MM cl) a v σ.out) a 30 (by omega)
    (fun σ h => h.2.2.1) (fun σ h => h.2.1) (digBody_spec hvB (by omega) (by omega))
  obtain ⟨σ', r2, ⟨⟨-, -, -, -, ho⟩, hp⟩, hv, ha', hi, -⟩ :=
    hloop.frame.run (σ := σ.setVar "w_e" v) ⟨by simp [Env.setVar, hM], by simp [Env.setVar, har],
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', (r1.seq r2).mono (by unfold Kdig; nlinarith), ?_, fun y h1 h2 => ?_, ?_, ?_⟩
  · rw [ho, hp]; rfl
  · rw [hv y (by simp [digBody, Com.wvars, h1, h2])]; simp [Env.setVar, h1]
  · funext b; rw [ha' b (by simp [digBody, Com.warrs])]; rfl
  · rw [hi (by simp [digBody, Com.reads])]; rfl

/-! ### Writing the tuples -/

/-- The entries of the tuples of tag `g` stored below `t`. -/
def outL (cl : List (List ℕ)) (d k g a t : ℕ) : List ℕ :=
  (selL cl d k g t).flatMap fun t => digitsOf (MM cl) a ((hs cl d k).getD t 0 / MM cl)

def EO (cl : List (List ℕ)) (d k g a : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  EC cl d k g σ ∧ σ.vars "w_ar" = a ∧ σ.vars "w_t" ≤ sz cl d k ∧
    σ.out = out0 ++ outL cl d k g a (σ.vars "w_t")

theorem outL_succ (g a t : ℕ) : outL cl d k g a (t + 1) = outL cl d k g a t ++
    (if sel cl d k g t then digitsOf (MM cl) a ((hs cl d k).getD t 0 / MM cl) else []) := by
  unfold outL; rw [selL_succ, List.flatMap_append]; split <;> simp

set_option maxHeartbeats 4000000 in
theorem outBody_spec (hB : BB cl d k B) {g a : ℕ} (hg : g < B) (ha : a ≤ d + k + 2)
    {out0 : List ℕ} :
    Spec B (fun σ => EO cl d k g a out0 σ ∧ σ.vars "w_t" < sz cl d k)
      (.seq (tagIte digits) (bump "w_t"))
      (fun σ σ' => EO cl d k g a out0 σ' ∧ σ'.vars "w_t" = σ.vars "w_t" + 1) (Kdig d k + 40) := by
  have hszB := hB.cb.sz
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => EO cl d k g a out0 σ ∧ σ.vars "w_t" < sz cl d k ∧
      σ.vars "w_t" < (σ.arrs "hs_mem").length ∧ σ.vars "w_t" < (σ.arrs "fp_f").length ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 < B ∧ (σ.arrs "fp_f").getD (σ.vars "w_t") 0 < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 / σ.vars "w_M" < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 / σ.vars "w_M" * σ.vars "w_M" < B ∧
      (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 - (σ.arrs "hs_mem").getD (σ.vars "w_t") 0 /
        σ.vars "w_M" * σ.vars "w_M" = (hs cl d k).getD (σ.vars "w_t") 0 % MM cl ∧
      (σ.arrs "fp_f").getD (σ.vars "w_t") 0 = (fe cl d k).getD (σ.vars "w_t") 0 ∧
      σ.vars "w_M" < B ∧ σ.vars "w_t" + 1 < B ∧ σ.vars "w_M" = MM cl ∧
      σ.arrs "hs_mem" = hs cl d k) ?_ ?_
  · unfold tagIte
    run_vcg [digits_spec hB ha]
    all_goals (try simp only [EO, EC, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar, outL_succ, sel]; try omega)
  · rintro σ ⟨⟨hE, har, ht, ho⟩, hlt⟩
    have hh := hE.2.1
    have hf := hE.2.2.1
    have hM := hE.1.hM
    have hv := hs_lt hB (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (l := hs cl d k)
      (p := σ.vars "w_t") (by rw [length_hs]; exact hlt))
    have hfe := fe_lt (cl := cl) (d := d) (k := k) hlt
    have hq : (hs cl d k).getD (σ.vars "w_t") 0 / MM cl ≤ (hs cl d k).getD (σ.vars "w_t") 0 :=
      Nat.div_le_self _ _
    have hq2 : (hs cl d k).getD (σ.vars "w_t") 0 / MM cl * MM cl ≤
        (hs cl d k).getD (σ.vars "w_t") 0 := Nat.div_mul_le_self _ _
    refine ⟨⟨hE, har, ht, ho⟩, hlt, by rw [hh, length_hs]; exact hlt, by rw [hf, length_fe]; exact hlt,
      by rw [hh]; exact hv, by rw [hf]; omega, by rw [hh, hM]; omega, by rw [hh, hM]; omega,
      by rw [hh, hM, mod_eq_sub], by rw [hf], by rw [hM]; have := MM_ge cl; omega,
      by omega, hM, hh⟩

theorem outLoop_spec (hB : BB cl d k B) {g a : ℕ} (hg : g < B) (ha : a ≤ d + k + 2)
    {out0 : List ℕ} :
    Spec B (fun σ => EO cl d k g a out0 (σ.setVar "w_t" 0))
      (loop "w_t" "hs_t" (.seq (tagIte digits) (bump "w_t")))
      (fun _ σ' => EO cl d k g a out0 σ' ∧ σ'.vars "w_t" = sz cl d k)
      ((Kdig d k + 44) * sz cl d k + 6) := by
  have hszB := hB.cb.sz
  exact Spec.forRangeZero "w_t" "hs_t" (EO cl d k g a out0) (sz cl d k) (Kdig d k + 40) (by omega)
    (fun σ h => h.2.2.1) (fun σ h => h.1.1.ht) (outBody_spec hB hg ha)

/-- The cost of the block of one relation. -/
def Kemit (cl : List (List ℕ)) (d k : ℕ) : ℕ :=
  2 + ((44 * sz cl d k + 6) + (2 + ((Kdig d k + 44) * sz cl d k + 6)))

theorem emitList_block (g a : ℕ) :
    Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf (emitList cl d k g a) =
      (selL cl d k g (sz cl d k)).length :: outL cl d k g a (sz cl d k) := by
  simp [Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf, emitList_eq, outL, List.flatMap]

set_option maxHeartbeats 2000000 in
theorem emitCom_spec (hB : BB cl d k B) {g a : ℕ} (hg : g < B) (ha : a ≤ d + k + 2) :
    Spec B (fun σ => EC cl d k g σ ∧ σ.vars "w_ar" = a) emitCom
      (fun σ σ' => σ'.out = σ.out ++
          Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf (emitList cl d k g a) ∧
        (∀ y, y ∉ ["w_cn", "w_t", "w_e", "w_p"] → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp) (Kemit cl d k) := by
  rintro σ ⟨⟨hC, hh, hf, htg⟩, har⟩
  have hszB := hB.cb.sz
  have hlen : (selL cl d k g (sz cl d k)).length ≤ sz cl d k := by
    unfold selL; exact (List.length_filter_le _ _).trans (by simp)
  have r1 : Run B (.assign "w_cn" (.lit 0)) σ (σ.setVar "w_cn" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hCNI : CNI cl d k g ((σ.setVar "w_cn" 0).setVar "w_t" 0) := by
    refine ⟨⟨hC.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hh],
      by simp [Env.setVar, hf], by simp [Env.setVar, htg]⟩, by simp [Env.setVar],
      by simp [Env.setVar, selL]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ2, r2, ⟨⟨hE2, -, hcn2⟩, ht2⟩, hv2, ha2, hi2, ho2⟩ :=
    (cntLoop_spec hB hg).frame.run (σ := σ.setVar "w_cn" 0) hCNI
  have hwo : ∀ y, y ≠ "w_cn" → y ≠ "w_t" → σ2.vars y = σ.vars y := by
    intro y h1 h2
    rw [hv2 y (by simp [tagIte, Com.wvars, h1, h2])]; simp [Env.setVar, h1]
  have hout2 : σ2.out = σ.out := by
    rw [ho2 (by simp [tagIte, Com.NoWrite])]; rfl
  rw [ht2] at hcn2
  have r3 : Run B (.write (V "w_cn")) σ2
      { σ2 with out := σ2.out ++ [(selL cl d k g (sz cl d k)).length] } 2 := by
    rw [← hcn2]; exact Run.write (evalB_var (by rw [hcn2]; omega))
  set σ3 := { σ2 with out := σ2.out ++ [(selL cl d k g (sz cl d k)).length] } with hσ3
  have hEO : EO cl d k g a (σ.out ++ [(selL cl d k g (sz cl d k)).length]) (σ3.setVar "w_t" 0) := by
    obtain ⟨hC2, hh2, hf2, htg2⟩ := hE2
    refine ⟨⟨hC2.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hσ3, hh2],
      by simp [Env.setVar, hσ3, hf2], by simp [Env.setVar, hσ3, htg2]⟩,
      by simp [Env.setVar, hσ3, hwo "w_ar" (by decide) (by decide), har], by simp [Env.setVar],
      by simp [Env.setVar, hσ3, outL, selL, hout2]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar, hσ3]
    rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ4, r4, ⟨⟨-, -, -, ho4⟩, ht4⟩, hv4, ha4, hi4, -⟩ :=
    (outLoop_spec hB hg ha).frame.run (σ := σ3) hEO
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold Kemit; omega), ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [ho4, ht4, emitList_block]; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hv4 y (by simp [tagIte, digits, digBody, Com.wvars, hy.2.1, hy.2.2.1, hy.2.2.2])]
    rw [hσ3]; exact hwo y hy.1 hy.2.1
  · funext b
    rw [ha4 b (by simp [tagIte, digits, digBody, Com.warrs]), hσ3]
    rw [ha2 b (by simp [tagIte, Com.warrs])]; rfl
  · rw [hi4 (by simp [tagIte, digits, digBody, Com.reads])]
    rw [hσ3]
    rw [hi2 (by simp [tagIte, Com.reads])]; rfl

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit
