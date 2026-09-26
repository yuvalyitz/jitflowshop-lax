import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.SegTree

/-!
# The maximum tree on the machine

Two operations on the array `a` of a maximum tree (`Ram/SegTree.lean`) over `N = 2^h` leaves:

* `tset a` — write the value in `"tv"` into leaf `"tp"`, then repair the `h` ancestors;
* `tfind a` — walk from the root to a leaf holding the root's value.

The scalars `"tN" = 2^h`, `"th" = h` are read, never written; `"ti"`, `"tc"`, `"t1"`, `"t2"`
are scratch. Each operation costs `O(h)`.
-/

namespace Lax496464Proofs.Ram.SegProg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax496464Proofs.Ram.SegTree

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- `ti := ti / 2`. -/
def halve : Com := .assign "ti" (.bin .div (V "ti") (.lit 2))

/-- Recompute cell `ti` of the tree `a` from its children, then move to the parent. -/
def recomp (a : String) : Com :=
  .seq (.assign "t1" (.get a (.bin .mul (.lit 2) (V "ti"))))
    (.seq (.assign "t2" (.get a (.bin .add (.bin .mul (.lit 2) (V "ti")) (.lit 1))))
      (.seq (.ite (.lt (V "t1") (V "t2")) (.assign "t1" (V "t2")) .skip)
        (.seq (.store a (V "ti") (V "t1")) halve)))

theorem one_le_anc {h ℓ t : ℕ} (h1 : 2 ^ h ≤ ℓ) (ht : t ≤ h) : 1 ≤ anc ℓ t := by
  unfold anc
  exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by
    calc 1 * 2 ^ t = 2 ^ t := one_mul _
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) ht
      _ ≤ ℓ := h1)

theorem recomp_spec {B : ℕ} (a : String) (h ℓ t : ℕ) (hB : 2 * 2 ^ h + 2 < B)
    (hℓ : ℓ < 2 * 2 ^ h) (ht : 1 ≤ t) (hi1 : 1 ≤ anc ℓ t) :
    Spec B (fun σ => σ.vars "ti" = anc ℓ t ∧ ConsExc (σ.arrs a) h ℓ t ∧
        (∀ v ∈ σ.arrs a, v < B))
      (recomp a)
      (fun σ σ' => σ'.vars "ti" = anc ℓ (t + 1) ∧ ConsExc (σ'.arrs a) h ℓ (t + 1) ∧
        (∀ v ∈ σ'.arrs a, v < B) ∧ (∀ k, 2 ^ h ≤ k → (σ'.arrs a).getD k 0 = (σ.arrs a).getD k 0) ∧
        (∀ y, y ≠ "ti" → y ≠ "t1" → y ≠ "t2" → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 60 := by
  have hi2 : anc ℓ t < 2 ^ h := by
    have h1 : anc ℓ t ≤ anc ℓ 1 := anc_anti ht
    have h2 : anc ℓ 1 = ℓ / 2 := by rw [anc_succ, anc_zero]
    omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hti, hC, hAB⟩ := hσ
  have hlen : (σ.arrs a).length = 2 * 2 ^ h := hC.1
  have hin1 : 2 * anc ℓ t < (σ.arrs a).length := by rw [hlen]; omega
  have hin2 : 2 * anc ℓ t + 1 < (σ.arrs a).length := by rw [hlen]; omega
  have hbd : ∀ k, k < (σ.arrs a).length → (σ.arrs a).getD k 0 < B := fun k hk =>
    hAB _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  run_vcg
  all_goals simp [hti]
  all_goals first
    | exact hbd _ hin1
    | exact hbd _ hin2
    | skip
  · rename_i hc
    simp [hti] at hc
    have hstep := hC.step ht hℓ hi1
    simp only [List.getD_eq_getElem?_getD] at hstep
    rw [max_eq_right hc.le] at hstep
    refine ⟨(anc_succ ℓ t).symm, hstep, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
      · exact hAB v hv'
      · simpa using hbd _ hin2
    · intro k hk
      simp only [← List.getD_eq_getElem?_getD]
      exact getD_set_ne (by omega)
    · intro y h1 h2 h3; simp [h1, h2, h3]
    · intro b hb1 hb2; exact absurd hb2 hb1
  · rename_i hc
    simp [hti] at hc
    have hstep := hC.step ht hℓ hi1
    simp only [List.getD_eq_getElem?_getD] at hstep
    rw [max_eq_left hc] at hstep
    refine ⟨(anc_succ ℓ t).symm, hstep, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
      · exact hAB v hv'
      · simpa using hbd _ hin1
    · intro k hk
      simp only [← List.getD_eq_getElem?_getD]
      exact getD_set_ne (by omega)
    · intro y h1 h2 h3; simp [h1, h2, h3]
    · intro b hb1 hb2; exact absurd hb2 hb1

/-- The `h` repairs: `tc := 0; while tc < th do (recomp; tc++)`. -/
def upLoop (a : String) : Com :=
  .seq (.assign "tc" (.lit 0)) (.while (.lt (V "tc") (V "th")) (.seq (recomp a) (bump "tc")))

/-- The invariant of the repair pass, for the leaf `ℓ` of the tree `a`, whose leaves are those
of `T1` throughout. -/
def UpInv (a : String) (h ℓ : ℕ) (T1 : List ℕ) (B : ℕ) (σ : Env) : Prop :=
  σ.vars "tc" ≤ h ∧ σ.vars "th" = h ∧ σ.vars "ti" = anc ℓ (σ.vars "tc" + 1) ∧
    ConsExc (σ.arrs a) h ℓ (σ.vars "tc" + 1) ∧ (∀ v ∈ σ.arrs a, v < B) ∧
    (∀ k, 2 ^ h ≤ k → (σ.arrs a).getD k 0 = T1.getD k 0)

theorem upBody_spec {B : ℕ} (a : String) (h ℓ : ℕ) (T1 : List ℕ) (hB : 2 * 2 ^ h + 2 < B)
    (h1 : 2 ^ h ≤ ℓ) (hℓ : ℓ < 2 * 2 ^ h) :
    Spec B (fun σ => UpInv a h ℓ T1 B σ ∧ σ.vars "tc" < h) (.seq (recomp a) (bump "tc"))
      (fun σ σ' => UpInv a h ℓ T1 B σ' ∧ σ'.vars "tc" = σ.vars "tc" + 1) 64 := by
  refine Spec.of_exists fun σ ⟨⟨hle, hth, hti, hC, hAB, hleaf⟩, hlt⟩ => ?_
  have hhB : h < B := by have := Nat.lt_two_pow_self (n := h); omega
  have ht : 1 ≤ σ.vars "tc" + 1 := by omega
  have hi1 : 1 ≤ anc ℓ (σ.vars "tc" + 1) := one_le_anc h1 (by omega)
  obtain ⟨σ1, hr1, hti1, hC1, hAB1, hleaf1, hv1, ha1, -, -⟩ :=
    (recomp_spec a h ℓ (σ.vars "tc" + 1) hB hℓ ht hi1).run ⟨hti, hC, hAB⟩
  have htc1 : σ1.vars "tc" = σ.vars "tc" := hv1 "tc" (by decide) (by decide) (by decide)
  have hth1 : σ1.vars "th" = h := by rw [hv1 "th" (by decide) (by decide) (by decide)]; exact hth
  have hBt : σ1.vars "tc" + 1 < B := by rw [htc1]; omega
  have hev : (bump "tc" : Com) = .assign "tc" (.bin .add (V "tc") (.lit 1)) := rfl
  have hr2 : Run B (bump "tc") σ1 (σ1.setVar "tc" (σ1.vars "tc" + 1)) 4 :=
    Run.assign (evalB_bin (evalB_var (by rw [htc1]; omega)) (evalB_lit (by omega))
      (by rw [Bop.apply_add]; exact hBt))
  refine ⟨_, 64, (hr1.seq hr2).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, if_true]; omega
  · simpa using hth1
  · simp only [vars_setVar, if_true, if_neg (by decide : ("ti" : String) ≠ "tc")]
    rw [htc1, hti1]
  · simp only [vars_setVar, if_true, arrs_setVar]; rw [htc1]; exact hC1
  · simpa using hAB1
  · intro k hk; simp only [arrs_setVar]; rw [hleaf1 k hk]; exact hleaf k hk
  · simp only [vars_setVar, if_true]; rw [htc1]

theorem upLoop_spec {B : ℕ} (a : String) (h ℓ : ℕ) (T1 : List ℕ) (hB : 2 * 2 ^ h + 2 < B)
    (h1 : 2 ^ h ≤ ℓ) (hℓ : ℓ < 2 * 2 ^ h) :
    Spec B (fun σ => UpInv a h ℓ T1 B (σ.setVar "tc" 0)) (upLoop a)
      (fun _ σ' => UpInv a h ℓ T1 B σ' ∧ σ'.vars "tc" = h) ((64 + 4) * h + 6) := by
  have hhB : h < B := by have := Nat.lt_two_pow_self (n := h); omega
  exact Spec.forRangeZero "tc" "th" (UpInv a h ℓ T1 B) h 64 hhB (fun σ hI => hI.1)
    (fun σ hI => hI.2.1) (upBody_spec a h ℓ T1 hB h1 hℓ)

/-- Write the value in `"tv"` into leaf `"tp"` of the tree `a`, then repair its ancestors. -/
def tset (a : String) : Com :=
  .seq (.assign "ti" (.bin .add (V "tN") (V "tp")))
    (.seq (.store a (V "ti") (V "tv")) (.seq halve (upLoop a)))

theorem tset_spec {B : ℕ} (a : String) (h pos v : ℕ) (hB : 2 * 2 ^ h + 2 < B) (hvB : v < B)
    (hpos : pos < 2 ^ h) :
    Spec B (fun σ => σ.vars "tN" = 2 ^ h ∧ σ.vars "th" = h ∧ σ.vars "tp" = pos ∧
        σ.vars "tv" = v ∧ Cons (σ.arrs a) h ∧ (∀ x ∈ σ.arrs a, x < B)) (tset a)
      (fun σ σ' => Cons (σ'.arrs a) h ∧ (σ'.arrs a).getD (2 ^ h + pos) 0 = v ∧
        (∀ k, 2 ^ h ≤ k → k ≠ 2 ^ h + pos → (σ'.arrs a).getD k 0 = (σ.arrs a).getD k 0) ∧
        (∀ x ∈ σ'.arrs a, x < B)) (68 * h + 40) := by
  have hhB : h < B := by have := Nat.lt_two_pow_self (n := h); omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hN, hth, hp, hv, hC, hAB⟩ := hσ
  set ℓ := 2 ^ h + pos with hℓdef
  have h1 : 2 ^ h ≤ ℓ := by omega
  have hℓ : ℓ < 2 * 2 ^ h := by omega
  have hlen : (σ.arrs a).length = 2 * 2 ^ h := hC.1
  -- ti := tN + tp
  have hvN : (V "tN").evalB B σ = some (2 ^ h) := hN ▸ evalB_var (by rw [hN]; omega)
  have hvP : (V "tp").evalB B σ = some pos := hp ▸ evalB_var (by rw [hp]; omega)
  have hr1 : Run B (.assign "ti" (.bin .add (V "tN") (V "tp"))) σ (σ.setVar "ti" ℓ) 4 :=
    Run.assign (v := ℓ) (evalB_bin hvN hvP (by rw [Bop.apply_add]; omega))
  set σ1 := σ.setVar "ti" ℓ with hσ1
  have hti1 : σ1.vars "ti" = ℓ := by simp [hσ1]
  have hv1 : σ1.vars "tv" = v := by simp [hσ1, hv]
  -- a[ti] := tv
  have hvI : (V "ti").evalB B σ1 = some ℓ := hti1 ▸ evalB_var (by rw [hti1]; omega)
  have hvV : (V "tv").evalB B σ1 = some v := hv1 ▸ evalB_var (by rw [hv1]; exact hvB)
  have hr2 : Run B (.store a (V "ti") (V "tv")) σ1 (σ1.setArr a ℓ v) 3 :=
    Run.store (idx := ℓ) (v := v) hvI hvV (by simp only [hσ1, arrs_setVar]; rw [hlen]; omega)
  set σ2 := σ1.setArr a ℓ v with hσ2
  have hti2 : σ2.vars "ti" = ℓ := by simp [hσ2, hti1]
  -- ti := ti / 2
  have hvI2 : (V "ti").evalB B σ2 = some ℓ := hti2 ▸ evalB_var (by rw [hti2]; omega)
  have hr3 : Run B halve σ2 (σ2.setVar "ti" (ℓ / 2)) 4 :=
    Run.assign (v := ℓ / 2) (evalB_bin hvI2 (evalB_lit (by omega)) (by rw [Bop.apply_div]; omega))
  set σ3 := σ2.setVar "ti" (ℓ / 2) with hσ3
  have hT : σ3.arrs a = (σ.arrs a).set ℓ v := by simp [hσ3, hσ2, hσ1]
  have h3ti : σ3.vars "ti" = ℓ / 2 := by simp [hσ3]
  have h3th : σ3.vars "th" = h := by simp [hσ3, hσ2, hσ1, hth]
  have hbase : ConsExc (σ3.arrs a) h ℓ 1 := by rw [hT]; exact ConsExc.base hC h1 hℓ
  have hUp : UpInv a h ℓ ((σ.arrs a).set ℓ v) B (σ3.setVar "tc" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [h3th]
    · simp [h3ti, anc_succ, anc_zero]
    · simpa using hbase
    · intro x hx
      simp only [arrs_setVar] at hx
      rw [hT] at hx
      rcases List.mem_or_eq_of_mem_set hx with hx' | rfl
      · exact hAB x hx'
      · exact hvB
    · intro k _
      simp [hT]
  obtain ⟨σ4, hr4, hI4, htc4⟩ := (upLoop_spec a h ℓ ((σ.arrs a).set ℓ v) hB h1 hℓ).run hUp
  obtain ⟨-, -, -, hC4, hAB4, hleaf4⟩ := hI4
  rw [htc4] at hC4
  have hCons : Cons (σ4.arrs a) h := ConsExc.final hℓ hC4
  refine ⟨σ4, _, (hr1.seq (hr2.seq (hr3.seq hr4))).mono (by omega), le_rfl, hCons, ?_, ?_, hAB4⟩
  · rw [hleaf4 ℓ h1, getD_set_self (by rw [hlen]; omega)]
  · intro k hk hne
    rw [hleaf4 k hk, getD_set_ne (Ne.symm hne)]

/-! ## Finding a leaf holding the root's value -/

/-- One step down: to the right child if it holds the value of the current cell, else the left. -/
def descend (a : String) : Com :=
  .seq (.ite (.eq (.get a (.bin .add (.bin .mul (.lit 2) (V "ti")) (.lit 1))) (.get a (V "ti")))
      (.assign "ti" (.bin .add (.bin .mul (.lit 2) (V "ti")) (.lit 1)))
      (.assign "ti" (.bin .mul (.lit 2) (V "ti"))))
    (bump "tc")

/-- The `h` steps down: `tc := 0; while tc < th do (descend; tc++)`. -/
def downLoop (a : String) : Com :=
  .seq (.assign "tc" (.lit 0)) (.while (.lt (V "tc") (V "th")) (descend a))

/-- The invariant of the descent: level `tc`, and a cell there holding the root's value. -/
def DownInv (a : String) (h : ℕ) (T : List ℕ) (σ : Env) : Prop :=
  σ.vars "tc" ≤ h ∧ σ.vars "th" = h ∧ σ.arrs a = T ∧ 2 ^ σ.vars "tc" ≤ σ.vars "ti" ∧
    σ.vars "ti" < 2 ^ (σ.vars "tc" + 1) ∧ T.getD (σ.vars "ti") 0 = T.getD 1 0

theorem descend_spec {B : ℕ} (a : String) (h : ℕ) (T : List ℕ) (hc : Cons T h)
    (hB : 2 * 2 ^ h + 2 < B) (hTB : ∀ x ∈ T, x < B) :
    Spec B (fun σ => DownInv a h T σ ∧ σ.vars "tc" < h) (descend a)
      (fun σ σ' => DownInv a h T σ' ∧ σ'.vars "tc" = σ.vars "tc" + 1) 40 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hle, hth, hT, hlo, hhi, hroot⟩, hlt⟩ := hσ
  have hpow : 2 ^ (σ.vars "tc" + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hlt
  have hpos : 1 ≤ 2 ^ σ.vars "tc" := Nat.one_le_two_pow
  have hi1 : 1 ≤ σ.vars "ti" := by omega
  have hi2 : σ.vars "ti" < 2 ^ h := by omega
  have hlen : T.length = 2 * 2 ^ h := hc.1
  have hpp : 2 ^ (σ.vars "tc" + 1) = 2 * 2 ^ σ.vars "tc" := by ring
  have hbd : ∀ k, k < T.length → T.getD k 0 < B := fun k hk =>
    hTB _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  have hhB : h < B := by have := Nat.lt_two_pow_self (n := h); omega
  obtain ⟨hd1, hd2⟩ := hc.descend hi1 hi2
  have hin1 : 2 * σ.vars "ti" + 1 < T.length := by omega
  have hin0 : 2 * σ.vars "ti" < T.length := by omega
  have hi0 : σ.vars "ti" < T.length := by omega
  run_vcg
  simp only [List.getD_eq_getElem?_getD] at hroot hbd hd1 hd2
  all_goals simp [hT]
  all_goals first
    | exact hin1
    | exact hin0
    | exact hi0
    | exact hbd _ hin1
    | exact hbd _ hin0
    | exact hbd _ hi0
    | skip
  · rename_i hc
    rw [hT] at hc
    simp only [List.getD_eq_getElem?_getD] at hc
    have hpp2 : 2 ^ (σ.vars "tc" + 1 + 1) = 2 * 2 ^ (σ.vars "tc" + 1) := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp [hth]
    · simp [hT]
    · simp; omega
    · simp; omega
    · simp [hc]; exact hroot
  · rename_i hc
    rw [hT] at hc
    simp only [List.getD_eq_getElem?_getD] at hc
    have hpp2 : 2 ^ (σ.vars "tc" + 1 + 1) = 2 * 2 ^ (σ.vars "tc" + 1) := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp [hth]
    · simp [hT]
    · simp; omega
    · simp; omega
    · simp only [List.getD_eq_getElem?_getD] at hd2 hroot
      simp; rw [hd2 hc]; exact hroot

theorem downLoop_spec {B : ℕ} (a : String) (h : ℕ) (T : List ℕ) (hc : Cons T h)
    (hB : 2 * 2 ^ h + 2 < B) (hTB : ∀ x ∈ T, x < B) :
    Spec B (fun σ => DownInv a h T (σ.setVar "tc" 0)) (downLoop a)
      (fun _ σ' => DownInv a h T σ' ∧ σ'.vars "tc" = h) ((40 + 4) * h + 6) := by
  have hhB : h < B := by have := Nat.lt_two_pow_self (n := h); omega
  exact Spec.forRangeZero "tc" "th" (DownInv a h T) h 40 hhB (fun σ hI => hI.1)
    (fun σ hI => hI.2.1) (descend_spec a h T hc hB hTB)

/-- Walk from the root to a leaf holding the root's value; the leaf's cell is left in `"ti"`. -/
def tfind (a : String) : Com := .seq (.assign "ti" (.lit 1)) (downLoop a)

theorem tfind_spec {B : ℕ} (a : String) (h : ℕ) (T : List ℕ) (hc : Cons T h)
    (hB : 2 * 2 ^ h + 2 < B) (hTB : ∀ x ∈ T, x < B) :
    Spec B (fun σ => σ.vars "th" = h ∧ σ.arrs a = T) (tfind a)
      (fun _ σ' => 2 ^ h ≤ σ'.vars "ti" ∧ σ'.vars "ti" < 2 * 2 ^ h ∧
        T.getD (σ'.vars "ti") 0 = T.getD 1 0 ∧ σ'.arrs a = T) (44 * h + 12) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hth, hT⟩ := hσ
  have hr1 : Run B (.assign "ti" (.lit 1)) σ (σ.setVar "ti" 1) 2 :=
    Run.assign (evalB_lit (by omega))
  have hI : DownInv a h T ((σ.setVar "ti" 1).setVar "tc" 0) := by
    refine ⟨by simp, by simp [hth], by simp [hT], by simp, by simp, by simp⟩
  obtain ⟨σ2, hr2, hI2, htc⟩ := (downLoop_spec a h T hc hB hTB).run hI
  obtain ⟨-, -, hT2, hlo, hhi, hroot⟩ := hI2
  rw [htc] at hlo hhi
  refine ⟨σ2, _, (hr1.seq hr2).mono (by omega), le_rfl, hlo, ?_, hroot, hT2⟩
  calc σ2.vars "ti" < 2 ^ (h + 1) := hhi
    _ = 2 * 2 ^ h := by ring

end Lax496464Proofs.Ram.SegProg
