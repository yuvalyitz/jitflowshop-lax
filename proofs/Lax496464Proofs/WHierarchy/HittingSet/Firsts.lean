import Lax496464Proofs.WHierarchy.HittingSet.Compress
import Lax496464Proofs.WHierarchy.HittingSet.ReadNat

/-! # First occurrences, in IMP+

For every position `p` of the member array `hs_mem`, `firstsLoop` stores into `fp_f[p]` the first
position holding the same entry (`Compress.fst`), by a scan over the positions before `p`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Firsts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.Compress
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V bump)

/-- Keep the least position so far holding the entry of `fp_p`. -/
def scanBody : Com :=
  .seq (.ite (.eq (.get "hs_mem" (V "fp_q")) (.get "hs_mem" (V "fp_p")))
      (.ite (.lt (V "fp_q") (V "fp_r")) (.assign "fp_r" (V "fp_q")) .skip) .skip)
    (bump "fp_q")

/-- Scan the positions before `fp_p`. -/
def scanLoop : Com := .seq (.assign "fp_q" (.lit 0)) (.while (.lt (V "fp_q") (V "fp_p")) scanBody)

/-- The first occurrence of the entry at `fp_p`. -/
def firstBody : Com :=
  .seq (.assign "fp_r" (V "fp_p"))
    (.seq scanLoop (.seq (.store "fp_f" (V "fp_p") (V "fp_r")) (bump "fp_p")))

/-- **All first occurrences.** -/
def firstsLoop : Com :=
  .seq (.assign "fp_p" (.lit 0)) (.while (.lt (V "fp_p") (V "hs_t")) firstBody)

/-- The scan invariant: `r` is `p` if the entry of `p` does not occur before `q`, and its first
occurrence otherwise. -/
def RInv (l : List ℕ) (p q r : ℕ) : Prop :=
  r ≤ p ∧ (r < p → r < q ∧ l.getD r 0 = l.getD p 0) ∧
    ∀ q' < q, q' < r → l.getD q' 0 ≠ l.getD p 0

theorem rInv_zero (l : List ℕ) (p : ℕ) : RInv l p 0 p :=
  ⟨le_rfl, fun h => absurd h (lt_irrefl _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem rInv_step (l : List ℕ) {p q r : ℕ} (hq : q < p) (h : RInv l p q r) :
    RInv l p (q + 1) (if l.getD q 0 = l.getD p 0 ∧ q < r then q else r) := by
  obtain ⟨h1, h2, h3⟩ := h
  split_ifs with hc
  · refine ⟨by omega, fun _ => ⟨by omega, hc.1⟩, fun q' hq' hq'r => h3 q' (by omega) (by omega)⟩
  · refine ⟨h1, fun hr => ⟨by have := (h2 hr).1; omega, (h2 hr).2⟩, fun q' hq' hq'r => ?_⟩
    rcases Nat.lt_or_ge q' q with hlt | hge
    · exact h3 q' hlt hq'r
    · have : q' = q := by omega
      subst this
      intro he; exact hc ⟨he, hq'r⟩

theorem rInv_final (l : List ℕ) {p r : ℕ} (hp : p < l.length) (h : RInv l p p r) :
    r = l.idxOf (l.getD p 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge r p with hr | hr
  · exact (idxOf_eq_of_least l _ r (by omega) (h2 hr).2 fun q hq => h3 q (by omega) hq).symm
  · have : r = p := by omega
    subst this
    exact (idxOf_eq_of_least l _ r hp rfl fun q hq => h3 q hq hq).symm

/-- The state part-way through the scan for position `p`. -/
def SInv (l : List ℕ) (p : ℕ) (σ : Env) : Prop :=
  σ.arrs "hs_mem" = l ∧ σ.vars "fp_p" = p ∧ σ.vars "fp_q" ≤ p ∧
    RInv l p (σ.vars "fp_q") (σ.vars "fp_r")

theorem scanBody_spec {B : ℕ} (l : List ℕ) {p : ℕ} (hp : p < l.length) (hlB : ∀ v ∈ l, v < B)
    (hLB : l.length < B) :
    Spec B (fun σ => SInv l p σ ∧ σ.vars "fp_q" < p) scanBody
      (fun σ σ' => SInv l p σ' ∧ σ'.vars "fp_q" = σ.vars "fp_q" + 1) 30 := by
  refine Spec.pre (P := fun σ => SInv l p σ ∧ σ.vars "fp_q" < p ∧
    σ.vars "fp_q" < (σ.arrs "hs_mem").length ∧ σ.vars "fp_p" < (σ.arrs "hs_mem").length ∧
    (σ.arrs "hs_mem").getD (σ.vars "fp_q") 0 < B ∧ (σ.arrs "hs_mem").getD (σ.vars "fp_p") 0 < B ∧
    σ.vars "fp_r" < B ∧ σ.vars "fp_p" < B ∧ 1 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨hm, hpp, hq, hR⟩ := ‹SInv l p σ›
      have hlt : σ.vars "fp_q" < p := ‹_›
      have hst := rInv_step l hlt hR
    · have hc1 := ‹(σ.arrs "hs_mem").getD (σ.vars "fp_q") 0 =
        (σ.arrs "hs_mem").getD (σ.vars "fp_p") 0›
      rw [hm, hpp] at hc1
      rw [if_pos ⟨hc1, ‹σ.vars "fp_q" < σ.vars "fp_r"›⟩] at hst
      exact ⟨⟨by simp [Env.setVar, hm], by simp [Env.setVar, hpp], by simp [Env.setVar]; omega,
        by simpa [Env.setVar] using hst⟩, by simp [Env.setVar]⟩
    · have hc1 := ‹(σ.arrs "hs_mem").getD (σ.vars "fp_q") 0 =
        (σ.arrs "hs_mem").getD (σ.vars "fp_p") 0›
      rw [hm, hpp] at hc1
      rw [if_neg (fun h => ‹¬σ.vars "fp_q" < σ.vars "fp_r"› h.2)] at hst
      exact ⟨⟨by simp [Env.setVar, hm], by simp [Env.setVar, hpp], by simp [Env.setVar]; omega,
        by simpa [Env.setVar] using hst⟩, by simp [Env.setVar]⟩
    · have hc1 := ‹¬(σ.arrs "hs_mem").getD (σ.vars "fp_q") 0 =
        (σ.arrs "hs_mem").getD (σ.vars "fp_p") 0›
      rw [hm, hpp] at hc1
      rw [if_neg (fun h => hc1 h.1)] at hst
      exact ⟨⟨by simp [Env.setVar, hm], by simp [Env.setVar, hpp], by simp [Env.setVar]; omega,
        by simpa [Env.setVar] using hst⟩, by simp [Env.setVar]⟩
  · rintro σ ⟨⟨hm, hpp, hq, hR⟩, hlt⟩
    have hr : σ.vars "fp_r" ≤ p := hR.1
    have hmem : ∀ i < l.length, l.getD i 0 < B := fun i hi =>
      hlB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
    refine ⟨⟨hm, hpp, hq, hR⟩, hlt, by rw [hm]; omega, by rw [hm, hpp]; omega,
      by rw [hm]; exact hmem _ (by omega), by rw [hm, hpp]; exact hmem _ (by omega),
      by omega, by omega, by omega⟩

theorem scanLoop_spec {B : ℕ} (l : List ℕ) {p : ℕ} (hp : p < l.length) (hlB : ∀ v ∈ l, v < B)
    (hLB : l.length < B) :
    Spec B (fun σ => SInv l p (σ.setVar "fp_q" 0)) scanLoop
      (fun _ σ' => SInv l p σ' ∧ σ'.vars "fp_q" = p) (34 * p + 6) :=
  Spec.forRangeZero "fp_q" "fp_p" (SInv l p) p 30 (by omega) (fun _ h => h.2.2.1)
    (fun _ h => h.2.1) (scanBody_spec l hp hlB hLB)

/-- The first occurrences of a list, position by position. -/
def firsts (l : List ℕ) : List ℕ := (List.range l.length).map fun p => l.idxOf (l.getD p 0)

/-- The state part-way through the first occurrences. -/
def FInv (l : List ℕ) (σ : Env) : Prop :=
  σ.arrs "hs_mem" = l ∧ σ.vars "hs_t" = l.length ∧ σ.vars "fp_p" ≤ l.length ∧
    (σ.arrs "fp_f").length = l.length ∧
    ∀ p' < σ.vars "fp_p", (σ.arrs "fp_f").getD p' 0 = l.idxOf (l.getD p' 0)

theorem getD_set_self' (l : List ℕ) {i : ℕ} (v : ℕ) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_other' (l : List ℕ) {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem firstBody_spec {B : ℕ} (l : List ℕ) (hlB : ∀ v ∈ l, v < B) (hLB : l.length + 1 < B) :
    Spec B (fun σ => FInv l σ ∧ σ.vars "fp_p" < l.length) firstBody
      (fun σ σ' => FInv l σ' ∧ σ'.vars "fp_p" = σ.vars "fp_p" + 1) (34 * l.length + 20) := by
  intro σ ⟨⟨hm, ht, hpl, hfl, hf⟩, hlt⟩
  set p := σ.vars "fp_p" with hp_def
  have r1 := Run.assign (B := B) (σ := σ) (x := "fp_r") (e := V "fp_p") (v := p)
    (evalB_var (by omega))
  set σ1 := σ.setVar "fp_r" p with hσ1
  obtain ⟨σ2, r2, ⟨⟨hm2, hp2, -, hR2⟩, hq2⟩, hv2, ha2, -, -⟩ :=
    (scanLoop_spec (B := B) l hlt hlB (by omega)).frame.run (σ := σ1)
      ⟨by simp [hσ1, Env.setVar, hm], by simp [hσ1, Env.setVar, hp_def], by simp [Env.setVar],
        by simpa [hσ1, Env.setVar] using rInv_zero l p⟩
  have hr2 : σ2.vars "fp_r" = l.idxOf (l.getD p 0) := by
    rw [hq2] at hR2; exact rInv_final l hlt hR2
  have hrl : σ2.vars "fp_r" ≤ p := by rw [hq2] at hR2; exact hR2.1
  have ht2 : σ2.vars "hs_t" = l.length := by
    rw [hv2 _ (by simp [scanLoop, scanBody, Com.wvars])]; simp [hσ1, Env.setVar, ht]
  have hf2 : σ2.arrs "fp_f" = σ.arrs "fp_f" := by
    rw [ha2 _ (by simp [scanLoop, scanBody, Com.warrs])]; rfl
  have r3 := Run.store (B := B) (σ := σ2) (a := "fp_f") (i := V "fp_p") (e := V "fp_r")
    (evalB_var (by rw [hp2]; omega)) (evalB_var (by omega)) (by rw [hf2, hfl, hp2]; exact hlt)
  rw [hp2, hr2] at r3
  set σ3 := σ2.setArr "fp_f" p (l.idxOf (l.getD p 0)) with hσ3
  have h3p : σ3.vars "fp_p" = p := by simp [hσ3, Env.setArr, hp2]
  have r4 := Run.assign (B := B) (σ := σ3) (x := "fp_p") (e := .add (V "fp_p") (.lit 1))
    (v := p + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ3) (evalB_var (x := "fp_p") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h3p]; simp; omega)
      rw [h3p] at this; simpa using this)
  have e1 : (σ3.setVar "fp_p" (p + 1)).vars "fp_p" = p + 1 := by simp [Env.setVar]
  have e2 : (σ3.setVar "fp_p" (p + 1)).arrs "fp_f" =
      (σ.arrs "fp_f").set p (l.idxOf (l.getD p 0)) := by simp [hσ3, Env.setVar, Env.setArr, hf2]
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by simp; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hσ3, Env.setVar, Env.setArr, hm2]
  · simp [hσ3, Env.setVar, Env.setArr, ht2]
  · rw [e1]; omega
  · rw [e2, List.length_set, hfl]
  · intro p' hp'
    rw [e1] at hp'
    rw [e2]
    rcases Nat.lt_or_ge p' p with h | h
    · rw [getD_set_other' _ _ (by omega)]; exact hf p' h
    · have : p' = p := by omega
      rw [this, getD_set_self' _ _ (by rw [hfl]; exact hlt)]
  · rw [e1, hp_def]

theorem firstsLoop_spec {B : ℕ} (l : List ℕ) (hlB : ∀ v ∈ l, v < B) (hLB : l.length + 1 < B) :
    Spec B (fun σ => FInv l (σ.setVar "fp_p" 0)) firstsLoop
      (fun _ σ' => FInv l σ' ∧ σ'.vars "fp_p" = l.length)
      ((34 * l.length + 24) * l.length + 6) :=
  Spec.forRangeZero "fp_p" "hs_t" (FInv l) l.length (34 * l.length + 20) (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (firstBody_spec l hlB hLB)

theorem firsts_eq_of_FInv {l : List ℕ} {σ : Env} (h : FInv l σ) (hp : σ.vars "fp_p" = l.length) :
    σ.arrs "fp_f" = firsts l := by
  obtain ⟨-, -, -, hfl, hf⟩ := h
  refine List.ext_getElem (by simp [firsts, hfl]) fun i h1 h2 => ?_
  have := hf i (by rw [hp]; omega)
  rw [List.getD_eq_getElem _ _ h1] at this
  rw [this]
  simp [firsts]

/-! ## The compressed dimensions and the first occurrences -/

/-- `fp_kk := min k m`, `fp_NN := T + fp_kk`. -/
def prepHead : Com :=
  .seq (.assign "fp_kk" (V "hs_k"))
    (.seq (.ite (.lt (V "hs_m") (V "fp_kk")) (.assign "fp_kk" (V "hs_m")) .skip)
      (.assign "fp_NN" (.add (V "hs_t") (V "fp_kk"))))

/-- The compressed dimensions, then the first occurrences. -/
def prep : Com := .seq prepHead firstsLoop

theorem prepHead_spec {B : ℕ} (k m T : ℕ) (hB : T + k + m < B) :
    Spec B (fun σ => σ.vars "hs_k" = k ∧ σ.vars "hs_m" = m ∧ σ.vars "hs_t" = T) prepHead
      (fun σ σ' => σ'.vars "fp_kk" = min k m ∧ σ'.vars "fp_NN" = T + min k m ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "fp_kk" → y ≠ "fp_NN" → σ'.vars y = σ.vars y) 20 := by
  run_vcg
  all_goals (simp only [Env.setVar] at *; simp at *)
  all_goals exact ⟨by omega, by omega, fun y h1 h2 => by simp [h1, h2]⟩

/-- The scalars `prep` assigns. -/
def prepVars : List String := ["fp_kk", "fp_NN", "fp_p", "fp_q", "fp_r"]

/-- **The compressed dimensions and the first occurrences.** -/
theorem prep_spec {B : ℕ} (l : List ℕ) (k m : ℕ) (hlB : ∀ v ∈ l, v < B)
    (hB : l.length + k + m + 1 < B) :
    Spec B (fun σ => σ.vars "hs_k" = k ∧ σ.vars "hs_m" = m ∧ σ.vars "hs_t" = l.length ∧
        σ.arrs "hs_mem" = l ∧ (σ.arrs "fp_f").length = l.length) prep
      (fun σ σ' => σ'.vars "fp_kk" = min k m ∧ σ'.vars "fp_NN" = l.length + min k m ∧
        σ'.arrs "fp_f" = firsts l ∧ (∀ a, a ≠ "fp_f" → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ y, y ∉ prepVars → σ'.vars y = σ.vars y)
      (20 + ((34 * l.length + 24) * l.length + 6)) := by
  intro σ ⟨hk, hm, ht, hmem, hfl⟩
  obtain ⟨σ1, r1, hkk, hNN, ha1, hi1, ho1, hv1⟩ :=
    (prepHead_spec (B := B) k m l.length (by omega)).run ⟨hk, hm, ht⟩
  obtain ⟨σ2, r2, ⟨hF, hp2⟩, hv2, ha2, hi2, ho2⟩ :=
    (firstsLoop_spec (B := B) l hlB (by omega)).frame.run (σ := σ1)
      ⟨by simp [Env.setVar, ha1, hmem], by simp [Env.setVar]; rw [hv1 _ (by decide) (by decide), ht],
        by simp [Env.setVar], by simp [Env.setVar, ha1, hfl], by simp [Env.setVar]⟩
  refine ⟨σ2, r1.seq r2, ?_, ?_, firsts_eq_of_FInv hF hp2, ?_, ?_, ?_, ?_⟩
  · rw [hv2 _ (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.wvars]), hkk]
  · rw [hv2 _ (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.wvars]), hNN]
  · intro a ha
    rw [ha2 a (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.warrs, ha]), ha1]
  · rw [hi2 (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.reads]), hi1]
  · rw [ho2 (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.NoWrite]), ho1]
  · intro y hy
    simp only [prepVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hv2 y (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.wvars, hy.2.2.1,
      hy.2.2.2.1, hy.2.2.2.2]), hv1 y hy.1 hy.2.1]

end Lax496464Proofs.WHierarchy.HittingSet.Firsts
