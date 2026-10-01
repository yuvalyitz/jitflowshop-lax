import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure

/-!
# The adjacency test

`adjTest` scans the block of `u` for `v` and sets `g_f` to `1` if it finds it.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure

/-- The number of targets of a graph word. -/
def E (x : List ℕ) : ℕ := offset x (nV x)

/-- The facts about the word the programs need. -/
structure Good (x : List ℕ) : Prop where
  len : x.length = 4 + nV x + E x
  mono : ∀ u < nV x, offset x u ≤ offset x (u + 1)
  le_last : ∀ u ≤ nV x, offset x u ≤ E x

/-- The facts about the values the programs need. -/
structure Fits (x : List ℕ) (B : ℕ) : Prop where
  entries : ∀ v ∈ x, v < B
  len : (x.length + 2) * (x.length + 2) + 8 < B

theorem Fits.getD_lt {x : List ℕ} {B : ℕ} (h : Fits x B) (i : ℕ) : x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : x[i]? with _ | v
  · have := h.len; simp; omega
  · exact h.entries v (List.mem_of_getElem? hx)

theorem Fits.len_lt {x : List ℕ} {B : ℕ} (h : Fits x B) : x.length + 8 < B := by
  have := h.len; nlinarith

/-- The context every pass runs in. -/
def Ctx (x : List ℕ) (σ : Env) : Prop := σ.arrs "a" = x ∧ σ.vars "g_n" = nV x

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

theorem Keep.trans {S : List String} {σ σ' σ'' : Env} (h1 : Keep S σ σ') (h2 : Keep S σ' σ'') :
    Keep S σ σ'' :=
  ⟨fun y hy => (h2.1 y hy).trans (h1.1 y hy), h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- Framing, with the output unchanged too. -/
theorem Spec.keepOut {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) (hnw : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ' ∧ σ'.out = σ.out) K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ =>
    ⟨hq, ⟨fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩, ho hnw⟩

/-! ### The scan -/

/-- The scan up to `t`. -/
def scanUpTo (x : List ℕ) (u v t : ℕ) : Bool :=
  (List.range t).any fun s => target x (offset x u + s) == v

theorem scanUpTo_succ (x : List ℕ) (u v t : ℕ) :
    scanUpTo x u v (t + 1) = (scanUpTo x u v t || target x (offset x u + t) == v) := by
  unfold scanUpTo
  rw [List.range_succ, List.any_append]
  simp

theorem scanUpTo_full (x : List ℕ) (u v : ℕ) :
    scanUpTo x u v (offset x (u + 1) - offset x u) = adjW x u v := rfl

/-- The invariant of the scan. -/
def AdjI (x : List ℕ) (u v : ℕ) (σ : Env) : Prop :=
  Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" = v ∧ σ.vars "g_lo" = offset x u ∧
    σ.vars "g_d" = offset x (u + 1) - offset x u ∧ σ.vars "g_t" ≤ σ.vars "g_d" ∧
    σ.vars "g_f" = if scanUpTo x u v (σ.vars "g_t") then 1 else 0

theorem target_eq_getD (x : List ℕ) (lo t : ℕ) :
    x.getD (3 + nV x + lo + t) 0 = target x (lo + t) := by
  unfold target vertexCount nV; rw [Nat.add_assoc]

set_option maxHeartbeats 1000000 in
theorem adjBody_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u v : ℕ}
    (hu : u < nV x) (hv : v < nV x) :
    Spec B (fun σ => AdjI x u v σ ∧ σ.vars "g_t" < offset x (u + 1) - offset x u) adjBody
      (fun σ σ' => AdjI x u v σ' ∧ σ'.vars "g_t" = σ.vars "g_t" + 1) 20 := by
  have hlen := hx.len
  have hmono := hx.mono u hu
  have hlast := hx.le_last (u + 1) (by omega)
  have hBl := hB.len_lt
  refine Spec.pre (P := fun σ => (AdjI x u v σ ∧ σ.vars "g_t" < offset x (u + 1) - offset x u) ∧
    3 + σ.vars "g_n" + σ.vars "g_lo" + σ.vars "g_t" < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (3 + σ.vars "g_n" + σ.vars "g_lo" + σ.vars "g_t") 0 < B ∧
    σ.vars "g_v" < B ∧ σ.vars "g_t" + 1 < B ∧ 3 + σ.vars "g_n" + σ.vars "g_lo" + σ.vars "g_t" < B)
    ?_ ?_
  · unfold adjBody adjStep
    run_vcg
    all_goals
      rename_i hI hlt h1 h2 h3 h4 h5 hc
      obtain ⟨⟨ha, hn⟩, hu', hv', hlo, hd, ht, hf⟩ := hI
      rw [ha, hn, hlo, hv', target_eq_getD] at hc
      simp only [AdjI, Ctx, Env.setVar]
      simp [ha, hn, hu', hv', hlo, hd, scanUpTo_succ, hc, hf]
      omega
  · rintro σ ⟨⟨⟨ha, hn⟩, hu', hv', hlo, hd, ht, hf⟩, hlt⟩
    refine ⟨⟨⟨⟨ha, hn⟩, hu', hv', hlo, hd, ht, hf⟩, hlt⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hn, hlo]; omega
    · rw [ha]; exact hB.getD_lt _
    · rw [hv']; omega
    · omega
    · rw [hn, hlo]; omega

theorem adjLoop_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u v : ℕ}
    (hu : u < nV x) (hv : v < nV x) :
    Spec B (fun σ => AdjI x u v (σ.setVar "g_t" 0)) adjLoop
      (fun _ σ' => AdjI x u v σ' ∧ σ'.vars "g_t" = offset x (u + 1) - offset x u)
      ((20 + 4) * (offset x (u + 1) - offset x u) + 6) := by
  have hlen := hx.len
  have hlast := hx.le_last (u + 1) (by omega)
  have hBl := hB.len_lt
  exact Spec.forRangeZero "g_t" "g_d" (AdjI x u v) _ 20 (by omega)
    (fun σ h => by have := h.2.2.2.2.2.1; rw [h.2.2.2.2.1] at this; exact this)
    (fun σ h => h.2.2.2.2.1) (adjBody_spec hx hB hu hv)

/-- The cost of the adjacency test. -/
def Kadj (x : List ℕ) : ℕ := 24 * E x + 40

set_option maxHeartbeats 1000000 in
theorem adjPrep_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u v : ℕ}
    (hu : u < nV x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" = v) adjPrep
      (fun _ σ' => AdjI x u v (σ'.setVar "g_t" 0)) 20 := by
  have hlen := hx.len
  have hmono := hx.mono u hu
  have hBl := hB.len_lt
  refine Spec.pre (P := fun σ => (Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" = v) ∧
    3 + σ.vars "g_u" < (σ.arrs "a").length ∧ 3 + σ.vars "g_u" < B ∧
    (σ.arrs "a").getD (2 + σ.vars "g_u") 0 < B ∧ (σ.arrs "a").getD (3 + σ.vars "g_u") 0 < B ∧
    (σ.arrs "a").getD (3 + σ.vars "g_u") 0 - (σ.arrs "a").getD (2 + σ.vars "g_u") 0 < B) ?_ ?_
  · unfold adjPrep
    run_vcg
    all_goals (try (simp only [Env.setVar] at *; simp_all; done))
    all_goals
      have ha : σ.arrs "a" = x := (‹Ctx x σ›).1
      have hn : σ.vars "g_n" = nV x := (‹Ctx x σ›).2
      have hu' : σ.vars "g_u" = u := ‹_›
      have hv' : σ.vars "g_v" = v := ‹_›
      have e2 : x[2 + u]?.getD 0 = offset x u := by simp [offset]
      have e3 : x[3 + u]?.getD 0 = offset x (u + 1) := by
        simp [offset, show 2 + (u + 1) = 3 + u by omega]
      simp only [AdjI, Ctx, Env.setVar]
      simp [ha, hn, hu', hv', e2, e3, scanUpTo]
  · rintro σ ⟨⟨ha, hn⟩, hu', hv'⟩
    refine ⟨⟨⟨ha, hn⟩, hu', hv'⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hu']; omega
    · rw [hu']; omega
    · rw [ha]; exact hB.getD_lt _
    · rw [ha]; exact hB.getD_lt _
    · rw [ha]; exact lt_of_le_of_lt (Nat.sub_le _ _) (hB.getD_lt _)

theorem adjTest_value {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) {u v : ℕ}
    (hu : u < nV x) (hv : v < nV x) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" = u ∧ σ.vars "g_v" = v) adjTest
      (fun _ σ' => σ'.vars "g_f" = if adjW x u v then 1 else 0) (Kadj x) := by
  have hlast := hx.le_last (u + 1) (by omega)
  have hle : (20 + 4) * (offset x (u + 1) - offset x u) + 6 ≤ 24 * E x + 6 := by
    have : offset x (u + 1) - offset x u ≤ E x := by omega
    omega
  refine Spec.mono (Spec.seq (adjPrep_spec hx hB hu) (adjLoop_spec hx hB hu hv)
    (fun _ _ _ h => h) ?_) (by unfold Kadj; omega)
  rintro σ σ1 σ2 - - ⟨⟨-, -, -, -, -, -, hf⟩, ht⟩
  rw [hf, ht, scanUpTo_full]

theorem adjTest_spec {x : List ℕ} (hx : Good x) {B : ℕ} (hB : Fits x B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "g_u" < nV x ∧ σ.vars "g_v" < nV x) adjTest
      (fun σ σ' => σ'.vars "g_f" = (if adjW x (σ.vars "g_u") (σ.vars "g_v") then 1 else 0) ∧
        Keep adjVars σ σ' ∧ σ'.out = σ.out) (Kadj x) := by
  intro σ hσ
  have h := Spec.keepOut (adjTest_value hx hB hσ.2.1 hσ.2.2) adjVars ?_ ?_ ?_ ?_
  · exact h σ ⟨hσ.1, rfl, rfl⟩
  · intro y hy
    simp only [adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.wvars, adjVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    tauto
  · simp [adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.warrs]
  · simp [adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.reads]
  · simp [adjTest, adjPrep, adjLoop, adjBody, adjStep, bump, Com.NoWrite]

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
