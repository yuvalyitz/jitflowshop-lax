import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead

/-!
# Reading the Input Tape

`readStruct` copies a valid word from the input tape into array `a`, using the runs of ones to find
its end, within `24 * |x| + 60` steps.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
open Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj Lax496464Proofs.WHierarchy.MccNP.Ram.BodyHead

theorem set_take_replicate (x : List ℕ) (i : ℕ) (h : i < x.length) :
    (x.take i ++ List.replicate (x.length - i) 0).set i (x.getD i 0) =
      x.take (i + 1) ++ List.replicate (x.length - (i + 1)) 0 := by
  have hlen : (x.take i).length = i := by simp; omega
  have hrep : x.length - i = (x.length - (i + 1)) + 1 := by omega
  have htake : x.take (i + 1) = x.take i ++ [x.getD i 0] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD]
    simp [List.getElem?_eq_getElem h]
  rw [hrep, List.replicate_succ, List.set_append_right _ _ (by omega), hlen, htake]
  simp

theorem getD_le_one {x : List ℕ} (hx : Valid x) (k : ℕ) : x.getD k 0 ≤ 1 := by
  by_cases h : k < x.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact entries_le_one hx _ (List.getElem_mem _)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-- The read invariant: `x` has been copied up to `i`, the input has been consumed accordingly. -/
def CI (x : List ℕ) (i : ℕ) (σ : Env) : Prop :=
  i ≤ x.length ∧ σ.arrs "a" = x.take i ++ List.replicate (x.length - i) 0 ∧ σ.inp = x.drop i

/-- The invariant inside a run of ones. -/
def OJ (x : List ℕ) (i r : ℕ) (σ : Env) : Prop :=
  i ≤ σ.vars "b_i" ∧ σ.vars "b_i" ≤ i + r ∧
    σ.arrs "a" = x.take (σ.vars "b_i") ++ List.replicate (x.length - σ.vars "b_i") 0 ∧
    σ.inp = x.drop (σ.vars "b_i" + 1) ∧ σ.vars "b_v" = x.getD (σ.vars "b_i") 0

theorem drop_cons_getD {x : List ℕ} {k : ℕ} (h : k < x.length) :
    x.drop k = x.getD k 0 :: x.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

set_option maxHeartbeats 1000000 in
theorem onesBody {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) {i r : ℕ}
    (hlt : i + r < x.length) (_hones : ∀ j < r, x.getD (i + j) 0 = 1) (hstop : x.getD (i + r) 0 = 0) :
    Spec B (fun σ => OJ x i r σ ∧ σ.vars "b_v" = 1)
      (.seq (.store "a" (V "b_i") (.lit 1)) (.seq (bump "b_i") (.read "b_v")))
      (fun σ σ' => OJ x i r σ' ∧ i + r - σ'.vars "b_i" < i + r - σ.vars "b_i") 20 := by
  refine Spec.pre (P := fun σ => OJ x i r σ ∧ σ.vars "b_v" = 1 ∧ σ.vars "b_i" < i + r ∧
      σ.vars "b_i" < (σ.arrs "a").length ∧ σ.inp ≠ [] ∧ x.getD (σ.vars "b_i" + 1) 0 ≤ 1) ?_ ?_
  · run_vcg
    obtain ⟨h1, h2, harr, hinp, hv'⟩ := ‹OJ x i r σ›
    have hv : σ.vars "b_v" = 1 := ‹σ.vars "b_v" = 1›
    have hlti : σ.vars "b_i" < i + r := ‹σ.vars "b_i" < i + r›
    have hxi : x.getD (σ.vars "b_i") 0 = 1 := hv' ▸ hv
    have hlx : σ.vars "b_i" + 1 < x.length := by omega
    have hdrop := drop_cons_getD hlx
    have hset := set_take_replicate x (σ.vars "b_i") (by omega)
    rw [hxi] at hset
    simp [OJ, Env.setVar, Env.setArr, harr, hinp, hdrop, hset]
    omega
  · rintro σ ⟨hJ, hv⟩
    obtain ⟨h1, h2, harr, hinp, hv'⟩ := hJ
    have hxi : x.getD (σ.vars "b_i") 0 = 1 := hv' ▸ hv
    have hlti : σ.vars "b_i" < i + r := by
      by_contra hcon
      have : σ.vars "b_i" = i + r := by omega
      rw [this] at hxi; omega
    refine ⟨⟨h1, h2, harr, hinp, hv'⟩, hv, hlti, ?_, ?_, getD_le_one hx _⟩
    · rw [harr]; simp; omega
    · rw [hinp]; simp; omega

theorem take_rep_shift (x : List ℕ) (k : ℕ) (h : k < x.length) (hz : x.getD k 0 = 0) :
    x.take k ++ List.replicate (x.length - k) 0 =
      x.take (k + 1) ++ List.replicate (x.length - (k + 1)) 0 := by
  have hrep : x.length - k = (x.length - (k + 1)) + 1 := by omega
  have htake : x.take (k + 1) = x.take k ++ [x.getD k 0] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD]
    simp [List.getElem?_eq_getElem h]
  rw [hrep, List.replicate_succ, htake, hz]
  simp

theorem cond_ones {B : ℕ} {σ : Env} (h1B : 1 < B) (hv : σ.vars "b_v" < B) :
    (Cond.eq (V "b_v") (.lit 1)).evalB B σ = some (σ.vars "b_v" == 1) :=
  evalB_condEq (evalB_var hv) (evalB_lit h1B)

theorem onesRead_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) {i r : ℕ}
    (hlt : i + r < x.length) (hones : ∀ j < r, x.getD (i + j) 0 = 1) (hstop : x.getD (i + r) 0 = 0) :
    Spec B (fun σ => CI x i σ ∧ σ.vars "b_i" = i) onesRead
      (fun _ σ' => CI x (i + r + 1) σ' ∧ σ'.vars "b_i" = i + r ∧ σ'.vars "b_v" = 0)
      (24 * r + 5) := by
  unfold onesRead
  have h0 : Spec B (fun σ => CI x i σ ∧ σ.vars "b_i" = i) (.read "b_v")
      (fun σ σ' => σ' = { σ.setVar "b_v" (x.getD i 0) with inp := x.drop (i + 1) }) 1 :=
    Spec.read (v := fun _ => x.getD i 0) (rest := fun _ => x.drop (i + 1))
      fun σ h => by rw [h.1.2.2, drop_cons_getD (by omega)]
  have hloop := Spec.while_count (B := B)
    (P := fun σ => OJ x i r σ)
    (b := Cond.eq (V "b_v") (.lit 1))
    (c := .seq (.store "a" (V "b_i") (.lit 1)) (.seq (bump "b_i") (.read "b_v")))
    (K := 24 * r + 4) (OJ x i r) (fun σ => i + r - σ.vars "b_i") 20
    (fun σ hJ => ⟨_, cond_ones (by omega) (by
      rw [hJ.2.2.2.2]; have := getD_le_one hx (σ.vars "b_i"); omega)⟩)
    (by
      intro σ ⟨hJ, hc⟩
      rw [cond_ones (by omega) (by rw [hJ.2.2.2.2]; have := getD_le_one hx (σ.vars "b_i"); omega)] at hc
      have hc' : σ.vars "b_v" = 1 := by simpa using hc
      exact onesBody hx hB hlt hones hstop σ ⟨hJ, hc'⟩)
    (fun σ h => h)
    (fun σ h => by
      obtain ⟨h1, h2, -⟩ := h
      simp; omega)
  refine Spec.mono (Spec.seq h0 hloop ?_ ?_) (by omega)
  · rintro σ σ1 ⟨⟨hle, harr, hinp⟩, hbi⟩ rfl
    have hlx : i < x.length := by omega
    simp only [OJ, Env.setVar]
    simp [harr, hbi]
    try omega
  · rintro σ σ1 σ2 - - ⟨⟨h1, h2, harr, hinp, hv⟩, hf⟩
    rw [cond_ones (by omega) (by rw [hv]; have := getD_le_one hx (σ2.vars "b_i"); omega)] at hf
    have hf' : ¬ σ2.vars "b_v" = 1 := by simpa using hf
    have hbi : σ2.vars "b_i" = i + r := by
      by_contra hne
      have hlt' : σ2.vars "b_i" < i + r := by omega
      apply hf'
      rw [hv]
      have := hones (σ2.vars "b_i" - i) (by omega)
      rwa [show i + (σ2.vars "b_i" - i) = σ2.vars "b_i" by omega] at this
    refine ⟨⟨by omega, ?_, ?_⟩, hbi, ?_⟩
    · rw [harr, hbi, take_rep_shift x (i + r) hlt hstop]
    · rw [hinp, hbi]
    · rw [hv, hbi]; exact hstop

/-- The invariant of the matrix loop. -/
def MI (x : List ℕ) (e : ℕ) (σ : Env) : Prop :=
  CI x (σ.vars "b_i") σ ∧ σ.vars "b_e" = e ∧ σ.vars "b_i" ≤ e

set_option maxHeartbeats 1000000 in
theorem matBody {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) {e : ℕ}
    (he : e < x.length) :
    Spec B (fun σ => MI x e σ ∧ σ.vars "b_i" < e)
      (.seq (.read "b_v") (.seq (.store "a" (V "b_i") (V "b_v")) (bump "b_i")))
      (fun σ σ' => MI x e σ' ∧ σ'.vars "b_i" = σ.vars "b_i" + 1) 20 := by
  refine Spec.pre (P := fun σ => MI x e σ ∧ σ.vars "b_i" < e ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "b_i" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    · obtain ⟨⟨h1, harr, hinp⟩, hbe, hle⟩ := ‹MI x e σ›
      have hlt : σ.vars "b_i" < e := ‹σ.vars "b_i" < e›
      have hxL : σ.vars "b_i" < x.length := by omega
      have hdrop := drop_cons_getD hxL
      have hset := set_take_replicate x (σ.vars "b_i") hxL
      have key : (σ.arrs "a").set (σ.vars "b_i") (σ.inp.headD 0) =
          x.take (σ.vars "b_i" + 1) ++ List.replicate (x.length - (σ.vars "b_i" + 1)) 0 := by
        rw [harr, hinp, hdrop]
        simp only [List.headD_cons]
        rw [← hset, ← harr]
      have n1 : ¬ ("b_i" = "b_v") := by decide
      have n2 : ¬ ("b_e" = "b_i") := by decide
      have n3 : ¬ ("b_e" = "b_v") := by decide
      simp only [MI, CI, Env.setVar, Env.setArr, ↓reduceIte, n1, n2, n3, key]
      simp only [hinp, List.tail_drop]
      exact ⟨⟨⟨by omega, trivial, trivial⟩, hbe, by omega⟩, trivial⟩
    · simpa [Env.setVar] using ‹σ.inp.headD 0 < B›
  · rintro σ ⟨⟨⟨h1, harr, hinp⟩, hbe, hle⟩, hlt⟩
    refine ⟨⟨⟨h1, harr, hinp⟩, hbe, hle⟩, hlt, ?_, ?_, ?_⟩
    · rw [hinp]; simp; omega
    · rw [hinp, drop_cons_getD (by omega)]
      have := getD_le_one hx (σ.vars "b_i")
      simp only [List.headD_cons]; omega
    · rw [harr]; simp; omega

theorem matLoop_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) {e i0 : ℕ}
    (he : e < x.length) (hi0 : i0 ≤ e) :
    Spec B (fun σ => CI x i0 σ ∧ σ.vars "b_i" = i0 ∧ σ.vars "b_e" = e) matLoop
      (fun _ σ' => CI x e σ' ∧ σ'.vars "b_i" = e) (24 * (e - i0) + 4) := by
  unfold matLoop
  have hloop := Spec.forRange (B := B)
    (P := fun σ => MI x e σ ∧ σ.vars "b_i" = i0)
    (c := .seq (.read "b_v") (.seq (.store "a" (V "b_i") (V "b_v")) (bump "b_i")))
    "b_i" "b_e" (MI x e) e 20 (24 * (e - i0) + 4)
    (fun σ h => by have := h.1.1; have := h.2.2; omega)
    (fun σ h => by have := h.2.1; omega) (fun σ h => h.2.1) (fun σ h => h.2.2)
    (matBody hx hB he) (fun σ h => h.1) (fun σ h => by rw [h.2]; try omega)
  refine Spec.pre (Spec.post hloop (fun σ σ' _ h => ⟨by have := h.1.1; rwa [h.2] at this, h.2⟩)) ?_
  rintro σ ⟨hci, hbi, hbe⟩
  refine ⟨⟨?_, hbe, by omega⟩, hbi⟩
  rw [hbi]; exact hci

set_option maxHeartbeats 2000000 in
theorem readStruct_value {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.arrs "a" = List.replicate x.length 0) readStruct
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.inp = [])
      (24 * x.length + 60) := by
  have hlen := hx.2.1
  have hsq := sq_bound hx
  have h1 := onesRead_value hx hB (i := 0) (r := order x) (by omega)
    (fun j hj => by simpa using getD_lt_order hj) (by simpa using hx.1)
  have h2 := onesRead_value hx hB (i := order x + 1 + order x * order x) (r := kOf x) (by omega)
    (fun j hj => getD_lt_kOf hj) hx.2.2.1
  have hm := matLoop_value hx hB (e := order x + 1 + order x * order x) (i0 := order x + 1)
    (by omega) (by omega)
  unfold readStruct
  run_vcg [h1, hm, h2]
  all_goals (simp only [CI] at *; simp_all [Env.setVar]; try omega)

/-- **The reader**, with its frame. -/
theorem readStruct_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + 2 < B) :
    Spec B (fun σ => σ.inp = x ∧ σ.arrs "a" = List.replicate x.length 0) readStruct
      (fun σ σ' => σ'.arrs "a" = x ∧ σ'.inp = [] ∧ σ'.out = σ.out ∧
        (∀ y, y ∉ readVars → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "a" → σ'.arrs a = σ.arrs a))
      (24 * x.length + 60) := by
  refine Spec.post (readStruct_value hx hB).frame ?_
  rintro σ σ' - ⟨⟨ha, hi⟩, hv, harr, -, ho⟩
  refine ⟨ha, hi, ho (by simp [readStruct, onesRead, matLoop, bump, Com.NoWrite]), ?_, ?_⟩
  · intro y hy
    apply hv
    simp only [readStruct, onesRead, matLoop, bump, Com.wvars, readVars] at hy ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
    tauto
  · intro a ha'
    apply harr
    simp [readStruct, onesRead, matLoop, bump, Com.warrs, ha']

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRead
