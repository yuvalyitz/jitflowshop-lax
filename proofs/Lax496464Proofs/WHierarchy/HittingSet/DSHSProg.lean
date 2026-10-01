import Lax496464Proofs.WHierarchy.HittingSet.EmitSets
import Lax496464Proofs.WHierarchy.HittingSet.DSHSMath
import Lax496464Proofs.WHierarchy.Machine.ReadTape
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # Dominating Set to Hitting Set: the program

`dhProg` reads the graph word into the array `a`, copies the offsets into `es_off` and the targets
into `es_val`, writes the codes of `n`, `n` and `k`, and then the closed neighbourhoods with
`EmitSets.setsLoop`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSHSProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitSets Lax496464Proofs.WHierarchy.HittingSet.DSHSMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitNat (V bump emitNat)
open Lax496464Proofs.WHierarchy.Machine.ReadTape (readTape readTape_spec readVars)

def dhSetup : Com :=
  .seq (.assign "dh_n" (.get "a" (.lit 0)))
  (.seq (.assign "dh_M" (.get "a" (.lit 1)))
  (.seq (.assign "dh_k" (.get "a" (.sub (V "rt_n") (.lit 1))))
  (.seq (.assign "es_U" (V "dh_n"))
  (.seq (.assign "es_m" (V "dh_n"))
  (.seq (.assign "es_self" (.lit 1))
  (.seq (.assign "dh_n1" (.add (V "dh_n") (.lit 1)))
        (.assign "dh_T" (.add (V "dh_M") (V "dh_M")))))))))

def offBody : Com :=
  .seq (.store "es_off" (V "dh_i") (.get "a" (.add (.lit 2) (V "dh_i")))) (bump "dh_i")
def offCopy : Com := .seq (.assign "dh_i" (.lit 0)) (.while (.lt (V "dh_i") (V "dh_n1")) offBody)

def valBody : Com :=
  .seq (.store "es_val" (V "dh_i") (.get "a" (.add (.add (.lit 3) (V "dh_n")) (V "dh_i"))))
    (bump "dh_i")
def valCopy : Com := .seq (.assign "dh_i" (.lit 0)) (.while (.lt (V "dh_i") (V "dh_T")) valBody)

def header : Com :=
  .seq (.seq (.assign "en_v" (V "dh_n")) emitNat) (.seq (.seq (.assign "en_v" (V "dh_n")) emitNat)
    (.seq (.assign "en_v" (V "dh_k")) emitNat))

/-- **The program of the reduction.** -/
def dhProg : Com :=
  .seq readTape (.seq dhSetup (.seq offCopy (.seq valCopy (.seq header setsLoop))))

/-! ## The setup -/

theorem dhSetup_spec {B : ℕ} (x : List ℕ) (hl : 3 ≤ x.length) (hxB : ∀ v ∈ x, v < B)
    (hLB : x.length < B)
    (hB : 2 * x.getD 0 0 + 2 * x.getD 1 0 + 4 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) dhSetup
      (fun σ σ' => σ'.vars "dh_n" = x.getD 0 0 ∧ σ'.vars "dh_M" = x.getD 1 0 ∧
        σ'.vars "dh_k" = x.getD (x.length - 1) 0 ∧ σ'.vars "es_U" = x.getD 0 0 ∧
        σ'.vars "es_m" = x.getD 0 0 ∧ σ'.vars "es_self" = 1 ∧
        σ'.vars "dh_n1" = x.getD 0 0 + 1 ∧ σ'.vars "dh_T" = x.getD 1 0 + x.getD 1 0 ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 40 := by
  have hget : ∀ i < x.length, x.getD i 0 < B := fun i hi =>
    hxB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have h0 := hget 0 (by omega)
  have h1 := hget 1 (by omega)
  have hk := hget (x.length - 1) (by omega)
  refine Spec.pre (P := fun σ => (σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) ∧
    0 < (σ.arrs "a").length ∧ 1 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD 0 0 < B ∧ (σ.arrs "a").getD 1 0 < B ∧ σ.vars "rt_n" < B ∧ 1 < B ∧
    σ.vars "rt_n" - 1 < (σ.arrs "a").length ∧ (σ.arrs "a").getD (σ.vars "rt_n" - 1) 0 < B ∧
    (σ.arrs "a").getD 0 0 + 1 < B ∧
    (σ.arrs "a").getD 1 0 + (σ.arrs "a").getD 1 0 < B) ?_ ?_
  · run_vcg
    all_goals
      have ha : σ.arrs "a" = x := ‹_›
      have hr : σ.vars "rt_n" = x.length := ‹_›
    all_goals simp only [Env.setVar, ha, hr] at *
    all_goals simp
    all_goals
      have h0' : x[0]?.getD 0 < B := by simpa [List.getD_eq_getElem?_getD] using h0
      have h1' : x[1]?.getD 0 < B := by simpa [List.getD_eq_getElem?_getD] using h1
      have hk' : x[x.length - 1]?.getD 0 < B := by simpa [List.getD_eq_getElem?_getD] using hk
      have hB' : 2 * x[0]?.getD 0 + 2 * x[1]?.getD 0 + 4 < B := by
        simpa [List.getD_eq_getElem?_getD] using hB
      omega
  · rintro σ ⟨ha, hr⟩
    refine ⟨⟨ha, hr⟩, by rw [ha]; omega, by rw [ha]; omega, by rw [ha]; exact h0,
      by rw [ha]; exact h1, by rw [hr]; exact hLB,
      by omega, by rw [ha, hr]; omega, by rw [ha, hr]; exact hk, by rw [ha]; omega,
      by rw [ha]; omega⟩

/-! ## Copying the offsets and the targets -/

theorem getD_set_self (l : List ℕ) {i : ℕ} (v : ℕ) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_other (l : List ℕ) {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem list_eq_map {l : List ℕ} {N : ℕ} {f : ℕ → ℕ} (hl : l.length = N)
    (h : ∀ p < N, l.getD p 0 = f p) : l = (List.range N).map f := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have := h i (by omega)
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [this]

/-- The copy invariant: positions below the counter of `dst` hold `x[base + p]`. -/
def CopyI (dst cnt bnd : String) (x : List ℕ) (base N : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars bnd = N ∧ σ.vars cnt ≤ N ∧ (σ.arrs dst).length = N ∧
    ∀ p < σ.vars cnt, (σ.arrs dst).getD p 0 = x.getD (base + p) 0

theorem offBody_spec {B : ℕ} (x : List ℕ) (N : ℕ) (hl : 2 + N ≤ x.length)
    (hxB : ∀ v ∈ x, v < B) (hB : N + 3 < B) :
    Spec B (fun σ => CopyI "es_off" "dh_i" "dh_n1" x 2 N σ ∧ σ.vars "dh_i" < N) offBody
      (fun σ σ' => CopyI "es_off" "dh_i" "dh_n1" x 2 N σ' ∧ σ'.vars "dh_i" = σ.vars "dh_i" + 1)
      12 := by
  refine Spec.pre (P := fun σ => (CopyI "es_off" "dh_i" "dh_n1" x 2 N σ ∧ σ.vars "dh_i" < N) ∧
    σ.vars "dh_i" + 2 < B ∧ σ.vars "dh_i" < (σ.arrs "es_off").length ∧
    2 + σ.vars "dh_i" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (2 + σ.vars "dh_i") 0 < B ∧
    1 < B) ?_ ?_
  · run_vcg
    obtain ⟨h1, h2, h3, h4, h5⟩ := ‹CopyI "es_off" "dh_i" "dh_n1" x 2 N σ›
    have hlt : σ.vars "dh_i" < N := ‹_›
    have e1 : ∀ p, p < σ.vars "dh_i" + 1 → ((σ.arrs "es_off").set (σ.vars "dh_i")
        ((σ.arrs "a").getD (2 + σ.vars "dh_i") 0)).getD p 0 = x.getD (2 + p) 0 := by
      intro p hp
      rcases Nat.lt_or_ge p (σ.vars "dh_i") with h | h
      · rw [getD_set_other _ _ (by omega)]; exact h5 p h
      · rw [show p = σ.vars "dh_i" by omega, getD_set_self _ _ (by omega), h1]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [Env.setVar, Env.setArr, h1]
    · simp [Env.setVar, Env.setArr, h2]
    · simp [Env.setVar, Env.setArr]; omega
    · simp [Env.setVar, Env.setArr, h4]
    · intro p hp
      simp only [Env.setVar, Env.setArr, ↓reduceIte] at hp ⊢
      exact e1 p hp
    · simp [Env.setVar, Env.setArr]
  · rintro σ ⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩
    refine ⟨⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩, by omega, by omega, by rw [h1]; omega, ?_, by omega⟩
    rw [h1, List.getD_eq_getElem _ _ (by omega)]
    exact hxB _ (List.getElem_mem _)

theorem offCopy_spec {B : ℕ} (x : List ℕ) (N : ℕ) (hl : 2 + N ≤ x.length)
    (hxB : ∀ v ∈ x, v < B) (hB : N + 3 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "dh_n1" = N ∧ (σ.arrs "es_off").length = N) offCopy
      (fun σ σ' => σ'.arrs "es_off" = (List.range N).map (fun p => x.getD (2 + p) 0) ∧
        (∀ b, b ≠ "es_off" → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "dh_i" → σ'.vars y = σ.vars y) (16 * N + 6) := by
  intro σ ⟨h1, h2, h3⟩
  obtain ⟨σ', r, ⟨⟨-, -, -, hl', hc⟩, hi⟩, hv, ha, hin, ho⟩ :=
    (Spec.forRangeZero (B := B) "dh_i" "dh_n1" (CopyI "es_off" "dh_i" "dh_n1" x 2 N) N 12
      (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (offBody_spec x N hl hxB hB)).frame.run (σ := σ)
      ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, h3], by simp [Env.setVar]⟩
  refine ⟨σ', r, list_eq_map hl' fun p hp => hc p (by omega), fun b hb => ha b ?_,
    hin (by simp [offBody, Com.reads]), ho (by simp [offBody, Com.NoWrite]),
    fun y hy => hv y (by simp [offBody, Com.wvars, hy])⟩
  simp [offBody, Com.warrs, hb]

theorem valBody_spec {B : ℕ} (x : List ℕ) (n N : ℕ) (hl : 3 + n + N ≤ x.length)
    (hxB : ∀ v ∈ x, v < B) (hB : n + N + 4 < B) :
    Spec B (fun σ => (CopyI "es_val" "dh_i" "dh_T" x (3 + n) N σ ∧ σ.vars "dh_n" = n) ∧
        σ.vars "dh_i" < N) valBody
      (fun σ σ' => (CopyI "es_val" "dh_i" "dh_T" x (3 + n) N σ' ∧ σ'.vars "dh_n" = n) ∧
        σ'.vars "dh_i" = σ.vars "dh_i" + 1) 16 := by
  refine Spec.pre (P := fun σ => ((CopyI "es_val" "dh_i" "dh_T" x (3 + n) N σ ∧
      σ.vars "dh_n" = n) ∧ σ.vars "dh_i" < N) ∧
    σ.vars "dh_i" + 3 + σ.vars "dh_n" < B ∧ σ.vars "dh_i" < (σ.arrs "es_val").length ∧
    3 + σ.vars "dh_n" + σ.vars "dh_i" < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (3 + σ.vars "dh_n" + σ.vars "dh_i") 0 < B ∧ 3 < B) ?_ ?_
  · run_vcg
    obtain ⟨h1, h2, h3, h4, h5⟩ := ‹CopyI "es_val" "dh_i" "dh_T" x (3 + n) N σ›
    have hn : σ.vars "dh_n" = n := ‹_›
    have hlt : σ.vars "dh_i" < N := ‹_›
    have e1 : ∀ p, p < σ.vars "dh_i" + 1 → ((σ.arrs "es_val").set (σ.vars "dh_i")
        ((σ.arrs "a").getD (3 + σ.vars "dh_n" + σ.vars "dh_i") 0)).getD p 0 =
          x.getD (3 + n + p) 0 := by
      intro p hp
      rcases Nat.lt_or_ge p (σ.vars "dh_i") with h | h
      · rw [getD_set_other _ _ (by omega)]; exact h5 p h
      · rw [show p = σ.vars "dh_i" by omega, getD_set_self _ _ (by omega), h1, hn]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · simp [Env.setVar, Env.setArr, h1]
    · simp [Env.setVar, Env.setArr, h2]
    · simp [Env.setVar, Env.setArr]; omega
    · simp [Env.setVar, Env.setArr, h4]
    · intro p hp
      simp only [Env.setVar, Env.setArr, ↓reduceIte] at hp ⊢
      exact e1 p hp
    · simp [Env.setVar, Env.setArr, hn]
    · simp [Env.setVar, Env.setArr]
  · rintro σ ⟨⟨⟨h1, h2, h3, h4, h5⟩, hn⟩, hlt⟩
    refine ⟨⟨⟨⟨h1, h2, h3, h4, h5⟩, hn⟩, hlt⟩, by omega, by omega, by rw [h1, hn]; omega, ?_,
      by omega⟩
    rw [h1, hn, List.getD_eq_getElem _ _ (by omega)]
    exact hxB _ (List.getElem_mem _)

theorem valCopy_spec {B : ℕ} (x : List ℕ) (n N : ℕ) (hl : 3 + n + N ≤ x.length)
    (hxB : ∀ v ∈ x, v < B) (hB : n + N + 4 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "dh_T" = N ∧ σ.vars "dh_n" = n ∧
        (σ.arrs "es_val").length = N) valCopy
      (fun σ σ' => σ'.arrs "es_val" = (List.range N).map (fun p => x.getD (3 + n + p) 0) ∧
        (∀ b, b ≠ "es_val" → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "dh_i" → σ'.vars y = σ.vars y) (20 * N + 6) := by
  intro σ ⟨h1, h2, h3, h4⟩
  obtain ⟨σ', r, ⟨⟨⟨-, -, -, hl', hc⟩, -⟩, hi⟩, hv, ha, hin, ho⟩ :=
    (Spec.forRangeZero (B := B) "dh_i" "dh_T"
      (fun σ => CopyI "es_val" "dh_i" "dh_T" x (3 + n) N σ ∧ σ.vars "dh_n" = n) N 16
      (by omega) (fun _ h => h.1.2.2.1) (fun _ h => h.1.2.1)
      (valBody_spec x n N hl hxB hB)).frame.run (σ := σ)
      ⟨⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2], by simp [Env.setVar],
        by simp [Env.setVar, h4], by simp [Env.setVar]⟩, by simp [Env.setVar, h3]⟩
  refine ⟨σ', r, list_eq_map hl' fun p hp => hc p (by omega), fun b hb => ha b ?_,
    hin (by simp [valBody, Com.reads]), ho (by simp [valBody, Com.NoWrite]),
    fun y hy => hv y (by simp [valBody, Com.wvars, hy])⟩
  simp [valBody, Com.warrs, hb]

/-! ## The header -/

theorem emitVar {B : ℕ} (src : String) (v S : ℕ) (hv : v + 4 < B) (hS : v.size ≤ S) :
    Spec B (fun σ => σ.vars src = v) (.seq (.assign "en_v" (V src)) emitNat)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat v ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → σ'.vars y = σ.vars y)
      (48 * S + 42) := by
  intro σ hσ
  have r1 := Run.assign (B := B) (σ := σ) (x := "en_v") (e := V src) (v := v)
    (by rw [← hσ]; exact evalB_var (by rw [hσ]; omega))
  obtain ⟨σ2, r2, ho, ha, hi, hv2⟩ := (EmitSets.emitNat_frame (B := B) S).run
    (σ := σ.setVar "en_v" v) ⟨by simp [Env.setVar]; omega, by simp [Env.setVar]; exact hS⟩
  refine ⟨σ2, (r1.seq r2).mono (by simp; omega), by rw [ho]; simp [Env.setVar], by rw [ha]; rfl,
    by rw [hi]; rfl, fun y h1 h2 h3 h4 => ?_⟩
  rw [hv2 y h2 h3 h4]; simp [Env.setVar, h1]

theorem header_spec {B : ℕ} (n k S : ℕ) (hn : n + 4 < B) (hk : k + 4 < B) (hnS : n.size ≤ S)
    (hkS : k.size ≤ S) :
    Spec B (fun σ => σ.vars "dh_n" = n ∧ σ.vars "dh_k" = k) header
      (fun σ σ' => σ'.out = σ.out ++ (bitsNat n ++ bitsNat n ++ bitsNat k) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧
        ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → σ'.vars y = σ.vars y)
      (3 * (48 * S + 42)) := by
  intro σ ⟨h1, h2⟩
  obtain ⟨σ1, r1, o1, a1, i1, v1⟩ := (emitVar (B := B) "dh_n" n S hn hnS).run h1
  obtain ⟨σ2, r2, o2, a2, i2, v2⟩ := (emitVar (B := B) "dh_n" n S hn hnS).run (σ := σ1)
    (by rw [v1 _ (by decide) (by decide) (by decide) (by decide), h1])
  obtain ⟨σ3, r3, o3, a3, i3, v3⟩ := (emitVar (B := B) "dh_k" k S hk hkS).run (σ := σ2)
    (by rw [v2 _ (by decide) (by decide) (by decide) (by decide),
      v1 _ (by decide) (by decide) (by decide) (by decide), h2])
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), by rw [o3, o2, o1]; simp, by rw [a3, a2, a1],
    by rw [i3, i2, i1], fun y h1 h2 h3 h4 => ?_⟩
  rw [v3 y h1 h2 h3 h4, v2 y h1 h2 h3 h4, v1 y h1 h2 h3 h4]

end Lax496464Proofs.WHierarchy.HittingSet.DSHSProg
