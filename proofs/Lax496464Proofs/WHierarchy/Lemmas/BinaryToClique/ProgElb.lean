import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop

/-!
# Σ₁[2] model checking to Clique: the candidate values

`elb` sets `zk = kX x`, fills `el` with `elL x` and sets `zne = neX x`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgElb

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2

/-- The size of the array `el`. -/
def elN (x : List ℕ) : ℕ := 4 * x.length + 1

theorem qX_le (x : List ℕ) : qX x ≤ x.length := by
  have := tok_shape x; unfold qX; have := this.1.1; omega

theorem limX_le (x : List ℕ) : limX x ≤ x.length + kX x := by
  unfold limX; split_ifs <;> omega

theorem limX_le_N (x : List ℕ) : limX x ≤ NsX x := by
  unfold limX; split_ifs <;> omega

theorem length_elL (x : List ℕ) : (elL x).length ≤ 4 * x.length := by
  unfold elL
  have h1 := List.length_filter_le (fun v => decide (v < NsX x)) x
  have h2 := limX_le x
  have h3 := qX_le x
  simp only [List.length_append, List.length_range]
  unfold kX at h2; omega

/-- The candidates below `zei`. -/
def fl1 (x : List ℕ) (i : ℕ) : List ℕ := (x.take i).filter (fun v => decide (v < NsX x))

theorem fl1_succ (x : List ℕ) {i : ℕ} (hi : i < x.length) :
    fl1 x (i + 1) = fl1 x i ++ (if x.getD i 0 < NsX x then [x.getD i 0] else []) := by
  unfold fl1
  rw [List.take_add_one, List.filter_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  by_cases h : x[i] < NsX x <;> simp [h]

theorem length_fl1 (x : List ℕ) (i : ℕ) : (fl1 x i).length ≤ i := by
  unfold fl1
  exact (List.length_filter_le _ _).trans (by simp)

/-- The invariant of the first loop. -/
def E1 (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zN" = NsX x ∧ σ.vars "zei" ≤ x.length ∧
    σ.vars "zne" = (fl1 x (σ.vars "zei")).length ∧ σ.arrs "el" = pad (fl1 x (σ.vars "zei")) (elN x) ∧
    σ.vars "zlim" = limX x ∧ σ.vars "zk" = kX x ∧ σ.vars "zfl" = (tok x).fl

set_option maxHeartbeats 2000000 in
theorem elBody1_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => E1 x σ ∧ σ.vars "zei" < x.length) elBody1
      (fun σ σ' => E1 x σ' ∧ σ'.vars "zei" = σ.vars "zei" + 1) 30 := by
  have hL : 5 * x.length + 2 < B := by have := hB.2; nlinarith
  have hent := hB.1
  unfold elBody1
  refine Spec.pre (P := fun σ => E1 x σ ∧ σ.vars "zei" < x.length ∧ 5 * x.length + 2 < B ∧
    x.getD (σ.vars "zei") 0 < B ∧ NsX x < B ∧
    (fl1 x (σ.vars "zei")).length < (σ.arrs "el").length ∧
    fl1 x (σ.vars "zei" + 1) = fl1 x (σ.vars "zei") ++
      (if x.getD (σ.vars "zei") 0 < NsX x then [x.getD (σ.vars "zei") 0] else []) ∧
    (fl1 x (σ.vars "zei")).length ≤ σ.vars "zei" ∧ (fl1 x (σ.vars "zei")).length < elN x) ?_ ?_
  · run_vcg
    all_goals (simp only [E1] at *; simp_all [Env.setVar, Env.setArr]; try omega)
    all_goals first
      | exact pad_set (by assumption) _
      | (rw [if_neg (by simp_all)]; simp)
  · rintro σ ⟨⟨ha, hn, hN, hle, hne, hel, hlim, hk, hfl⟩, hlt⟩
    have h1 := length_fl1 x (σ.vars "zei")
    refine ⟨⟨ha, hn, hN, hle, hne, hel, hlim, hk, hfl⟩, hlt, by omega, rd_lt hent (by omega) _,
      by unfold NsX; exact rd_lt hent (by omega) _, ?_, fl1_succ x hlt, h1, by unfold elN; omega⟩
    rw [hel, length_pad (by unfold elN; omega)]; unfold elN; omega

theorem elLoop1_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => E1 x (σ.setVar "zei" 0)) elLoop1
      (fun _ σ' => E1 x σ' ∧ σ'.vars "zei" = x.length) ((30 + 4) * x.length + 6) := by
  have hL := HB.len hB
  exact Spec.forRangeZero "zei" "rt_n" (E1 x) x.length 30 (by omega) (fun _ h => h.2.2.2.1)
    (fun _ h => h.2.1) (elBody1_spec hB)

theorem fl1_all (x : List ℕ) : fl1 x x.length = x.filter (fun v => decide (v < NsX x)) := by
  unfold fl1; rw [List.take_length]

/-- The invariant of the second loop. -/
def E2 (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "zlim" = limX x ∧ σ.vars "zej" ≤ limX x ∧
    σ.vars "zne" = (fl1 x x.length).length + σ.vars "zej" ∧
    σ.arrs "el" = pad (fl1 x x.length ++ List.range (σ.vars "zej")) (elN x) ∧
    σ.vars "zk" = kX x ∧ σ.vars "zfl" = (tok x).fl

set_option maxHeartbeats 2000000 in
theorem elBody2_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => E2 x σ ∧ σ.vars "zej" < limX x) elBody2
      (fun σ σ' => E2 x σ' ∧ σ'.vars "zej" = σ.vars "zej" + 1) 30 := by
  have hL : 5 * x.length + 2 < B := by have := hB.2; nlinarith
  have hq := qX_le x
  have hlim := limX_le x
  have hf := length_fl1 x x.length
  unfold elBody2
  refine Spec.pre (P := fun σ => E2 x σ ∧ σ.vars "zej" < limX x ∧ 5 * x.length + 2 < B ∧
    (fl1 x x.length).length + σ.vars "zej" < elN x ∧ limX x ≤ 3 * x.length ∧
    (fl1 x x.length).length ≤ x.length ∧
    (pad (fl1 x x.length ++ List.range (σ.vars "zej")) (elN x)).set
      ((fl1 x x.length).length + σ.vars "zej") (σ.vars "zej") =
      pad (fl1 x x.length ++ List.range (σ.vars "zej" + 1)) (elN x) ∧
    (pad (fl1 x x.length ++ List.range (σ.vars "zej")) (elN x)).length = elN x) ?_ ?_
  · run_vcg
    all_goals (simp only [E2] at *; simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt⟩
    have hlq : limX x ≤ 3 * x.length := by unfold kX at hlim; omega
    refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, hlt, hL, by unfold elN; omega, hlq, hf, ?_, ?_⟩
    · rw [pad_set' (by simp) (by simp; unfold elN; omega)]
      simp [List.range_succ]
    · rw [length_pad (by simp; unfold elN; omega)]

theorem elLoop2_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => E2 x (σ.setVar "zej" 0)) elLoop2
      (fun _ σ' => E2 x σ' ∧ σ'.vars "zej" = limX x) ((30 + 4) * limX x + 6) := by
  have hL : 5 * x.length + 2 < B := by have := hB.2; nlinarith
  have hq := qX_le x
  have hlim := limX_le x
  exact Spec.forRangeZero "zej" "zlim" (E2 x) (limX x) 30 (by unfold kX at hlim; omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (elBody2_spec hB)

theorem fl_step (x : List ℕ) {st : TS} (h : st.fl ≤ 1) : (tokStep x st).fl ≤ 1 := by
  unfold tokStep
  split_ifs
  · exact h
  · simp only [relStep]; split_ifs <;> omega
  · exact h
  · exact h
  · exact h

theorem fl_iter (x : List ℕ) : ∀ n, ((tokStep x)^[n] (tokInit x)).fl ≤ 1
  | 0 => by simp [tokInit]
  | n + 1 => by rw [Function.iterate_succ_apply']; exact fl_step x (fl_iter x n)

theorem tok_fl_le (x : List ℕ) : (tok x).fl ≤ 1 := fl_iter x x.length

theorem elL_eq (x : List ℕ) : elL x = fl1 x x.length ++ List.range (limX x) := by
  rw [fl1_all]; rfl

set_option maxHeartbeats 2000000 in
/-- **The candidates.** -/
theorem elb_value {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zq" = qX x ∧
        σ.vars "zN" = NsX x ∧ σ.vars "zfl" = (tok x).fl ∧
        σ.arrs "el" = List.replicate (elN x) 0) elb
      (fun _ σ' => σ'.vars "zk" = kX x ∧ σ'.vars "zne" = neX x ∧
        σ'.arrs "el" = pad (elL x) (elN x)) ((30 + 4) * x.length + (30 + 4) * limX x + 40) := by
  have hL : 5 * x.length + 2 < B := by have := hB.2; nlinarith
  have hq := qX_le x
  have hent := hB.1
  have hNB : NsX x < B := by unfold NsX; exact rd_lt hent (by omega) _
  have hflB : (tok x).fl < B := by have := tok_fl_le x; omega
  have hlim' : limX x = if NsX x < x.length + (qX x + qX x) then NsX x
      else x.length + (qX x + qX x) := by unfold limX kX; rw [two_mul]
  unfold elb
  run_vcg [elLoop1_spec hB, elLoop2_spec hB]
  all_goals (simp only [E1, E2] at *; simp_all [Env.setVar, fl1, pad_nil, neX,
    elL_eq, kX])
  all_goals (try omega)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgElb
