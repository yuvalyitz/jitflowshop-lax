import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs

/-! # p-Clique to Multicoloured Clique: the adjacency test

`adjCom` sets `b_f` to `1` exactly when `adjW x b_s b_t`: the division step, then (for different
colours) a scan of the block of the vertex of `b_s` for the vertex of `b_t`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- The context every pass runs in. -/
def Ctx (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "b_n" = nV x ∧ σ.vars "b_tb" = 3 + nV x ∧ σ.vars "b_N" = NOf x

lemma sub_div_mul (a n : ℕ) : a - a / n * n = a % n := by
  rw [Nat.mod_def, Nat.mul_comm]

theorem adjPrep_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "b_s" < B ∧ σ.vars "b_t" < B ∧ σ.vars "b_n" < B) adjPrep
      (fun σ σ' => σ'.vars "b_cs" = σ.vars "b_s" / σ.vars "b_n" ∧
        σ'.vars "b_us" = σ.vars "b_s" % σ.vars "b_n" ∧
        σ'.vars "b_ct" = σ.vars "b_t" / σ.vars "b_n" ∧
        σ'.vars "b_ut" = σ.vars "b_t" % σ.vars "b_n") 100 := by
  unfold adjPrep
  refine Spec.pre (P := fun σ => σ.vars "b_s" < B ∧ σ.vars "b_t" < B ∧ σ.vars "b_n" < B ∧
    σ.vars "b_s" / σ.vars "b_n" ≤ σ.vars "b_s" ∧ σ.vars "b_t" / σ.vars "b_n" ≤ σ.vars "b_t" ∧
    σ.vars "b_s" / σ.vars "b_n" * σ.vars "b_n" ≤ σ.vars "b_s" ∧
    σ.vars "b_t" / σ.vars "b_n" * σ.vars "b_n" ≤ σ.vars "b_t") ?_ ?_
  · run_vcg
    all_goals simp [Env.setVar, sub_div_mul]
  · intro σ ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, Nat.div_le_self _ _, Nat.div_le_self _ _, Nat.div_mul_le_self _ _,
      Nat.div_mul_le_self _ _⟩

/-! ### The scan of a block -/

/-- Some entry among the `j` entries from `st` on is `v`. -/
def anyB (x : List ℕ) (st v j : ℕ) : Bool := (List.range j).any fun i => x.getD (st + i) 0 == v

theorem anyB_zero (x : List ℕ) (st v : ℕ) : anyB x st v 0 = false := by simp [anyB]

theorem anyB_succ (x : List ℕ) (st v j : ℕ) :
    anyB x st v (j + 1) = (anyB x st v j || x.getD (st + j) 0 == v) := by
  simp [anyB, List.range_succ, List.any_append]

theorem adjX_eq (x : List ℕ) (u v : ℕ) :
    adjX x u v = anyB x (3 + nV x + offX x u) v (offX x (u + 1) - offX x u) := rfl

/-- The invariant of the scan. -/
def SI (x : List ℕ) (st v dg : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "b_st" = st ∧ σ.vars "b_ut" = v ∧ σ.vars "b_dg" = dg ∧
    σ.vars "b_j" ≤ dg ∧ σ.vars "b_f" = if anyB x st v (σ.vars "b_j") then 1 else 0

theorem getD_lt {x : List ℕ} {B i : ℕ} (hB : ∀ v ∈ x, v < B) (h0 : 0 < B) : x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact hB _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]; exact h0

set_option maxHeartbeats 1000000 in
theorem scanBody_spec {x : List ℕ} {st v dg B : ℕ} (hB : ∀ w ∈ x, w < B)
    (hst : st + dg < x.length) (hxB : x.length + 1 < B) (hv : v < B) :
    Spec B (fun σ => SI x st v dg σ ∧ σ.vars "b_j" < dg) scanBody
      (fun σ σ' => SI x st v dg σ' ∧ σ'.vars "b_j" = σ.vars "b_j" + 1) 20 := by
  unfold scanBody
  refine Spec.pre (P := fun σ => SI x st v dg σ ∧ σ.vars "b_j" < dg ∧
    x.getD (st + σ.vars "b_j") 0 < B ∧
    anyB x st v (σ.vars "b_j" + 1) = (anyB x st v (σ.vars "b_j") ||
      x.getD (st + σ.vars "b_j") 0 == v)) ?_ ?_
  · run_vcg
    all_goals (simp only [SI] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨hI, hlt⟩
    exact ⟨hI, hlt, getD_lt hB (by omega), anyB_succ x st v _⟩

theorem scanLoop_spec {x : List ℕ} {st v dg B : ℕ} (hB : ∀ w ∈ x, w < B)
    (hst : st + dg < x.length) (hxB : x.length + 1 < B) (hv : v < B) :
    Spec B (fun σ => SI x st v dg (σ.setVar "b_j" 0)) scanLoop
      (fun _ σ' => SI x st v dg σ' ∧ σ'.vars "b_j" = dg) (24 * dg + 6) :=
  Spec.forRangeZero "b_j" "b_dg" (SI x st v dg) dg 20 (by omega) (fun _ h => h.2.2.2.2.1)
    (fun _ h => h.2.2.2.1) (scanBody_spec hB hst hxB hv)

theorem scanLoop_spec' {x : List ℕ} {B : ℕ} (hB : ∀ w ∈ x, w < B) (hxB : x.length + 1 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "b_f" = 0 ∧
        σ.vars "b_st" + σ.vars "b_dg" < x.length ∧ σ.vars "b_ut" < B) scanLoop
      (fun σ σ' => σ'.vars "b_f" =
        if anyB x (σ.vars "b_st") (σ.vars "b_ut") (σ.vars "b_dg") then 1 else 0)
      (24 * x.length + 6) := by
  intro σ ⟨ha, hf, hst, hv⟩
  obtain ⟨σ', hr, hI, hj⟩ := scanLoop_spec (st := σ.vars "b_st") (v := σ.vars "b_ut")
    (dg := σ.vars "b_dg") hB hst hxB hv σ
    ⟨by simp [Env.setVar, ha], by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar, hf, anyB_zero]⟩
  refine ⟨σ', hr.mono (by omega), ?_⟩
  show σ'.vars "b_f" = _
  rw [hI.2.2.2.2.2, hj]

theorem offX_two (x : List ℕ) (u : ℕ) : x.getD (u + 2) 0 = offX x u := by
  unfold offX; rw [Nat.add_comm]

theorem offX_three (x : List ℕ) (u : ℕ) : x.getD (u + 3) 0 = offX x (u + 1) := by
  unfold offX; congr 1; omega

set_option maxHeartbeats 2000000 in
theorem scan_spec {x : List ℕ} {B : ℕ} (hgood : Good x) (hB : ∀ w ∈ x, w < B)
    (hxB : x.length + 1 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_us" < nV x ∧ σ.vars "b_ut" < B ∧ σ.vars "b_f" = 0) scan
      (fun σ σ' => σ'.vars "b_f" =
        if adjX x (σ.vars "b_us") (σ.vars "b_ut") then 1 else 0) (24 * x.length + 40) := by
  unfold scan
  refine Spec.pre (P := fun σ => Ctx x σ ∧ σ.vars "b_us" < nV x ∧ σ.vars "b_ut" < B ∧
    σ.vars "b_f" = 0 ∧ σ.vars "b_us" + 3 < x.length ∧
    x.getD (σ.vars "b_us" + 2) 0 = offX x (σ.vars "b_us") ∧
    x.getD (σ.vars "b_us" + 3) 0 = offX x (σ.vars "b_us" + 1) ∧
    offX x (σ.vars "b_us") ≤ offX x (σ.vars "b_us" + 1) ∧
    3 + nV x + offX x (σ.vars "b_us" + 1) < x.length ∧
    offX x (σ.vars "b_us") < B ∧ offX x (σ.vars "b_us" + 1) < B) ?_ ?_
  · run_vcg [scanLoop_spec' hB hxB]
    all_goals (simp only [Ctx, adjX_eq] at *; simp_all [Env.setVar]; try omega)
    all_goals (split_ifs <;> simp_all)
  · rintro σ ⟨hc, hu, hv, hf⟩
    have hg := hgood.2 _ hu
    refine ⟨hc, hu, hv, hf, by have := hgood.1; omega, offX_two x _, offX_three x _, hg.1, hg.2,
      ?_, ?_⟩
    · unfold offX; exact getD_lt hB (by omega)
    · unfold offX; exact getD_lt hB (by omega)

set_option maxHeartbeats 2000000 in
theorem adjTest_spec {x : List ℕ} {B : ℕ} (hgood : Good x) (hB : ∀ w ∈ x, w < B)
    (hxB : x.length + 1 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_us" < nV x ∧ σ.vars "b_ut" < B ∧ σ.vars "b_cs" < B ∧
        σ.vars "b_ct" < B) adjTest
      (fun σ σ' => σ'.vars "b_f" =
        if (decide (σ.vars "b_cs" ≠ σ.vars "b_ct") && adjX x (σ.vars "b_us") (σ.vars "b_ut"))
        then 1 else 0) (24 * x.length + 60) := by
  unfold adjTest
  run_vcg [scan_spec hgood hB hxB]
  all_goals (simp only [Ctx] at *; simp_all [Env.setVar]; try omega)

theorem nV_pos_of_lt {x : List ℕ} {s : ℕ} (h : s < NOf x) : 0 < nV x := by
  unfold NOf at h
  rcases Nat.eq_zero_or_pos (nV x) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

theorem adjCom_spec {x : List ℕ} {B : ℕ} (hgood : Good x) (hB : ∀ w ∈ x, w < B)
    (hxB : x.length + NOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < NOf x ∧ σ.vars "b_t" < NOf x) adjCom
      (fun σ σ' => σ'.vars "b_f" = if adjW x (σ.vars "b_s") (σ.vars "b_t") then 1 else 0)
      (100 + (24 * x.length + 60)) := by
  have hn3 := hgood.1
  have h1 : Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < NOf x ∧ σ.vars "b_t" < NOf x) adjPrep
      (fun σ σ' => (σ'.vars "b_cs" = σ.vars "b_s" / σ.vars "b_n" ∧
        σ'.vars "b_us" = σ.vars "b_s" % σ.vars "b_n" ∧
        σ'.vars "b_ct" = σ.vars "b_t" / σ.vars "b_n" ∧
        σ'.vars "b_ut" = σ.vars "b_t" % σ.vars "b_n") ∧
        (∀ y, y ∉ adjPrep.wvars → σ'.vars y = σ.vars y) ∧
        (∀ a, a ∉ adjPrep.warrs → σ'.arrs a = σ.arrs a)) 100 := by
    refine Spec.post (Spec.pre (adjPrep_spec (B := B)).frame ?_)
      (fun σ σ' _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    rintro σ ⟨⟨_, hn, _, _⟩, hs, ht⟩
    refine ⟨by omega, by omega, by omega⟩
  refine Spec.seq h1 (adjTest_spec hgood hB (by omega)) ?_ ?_
  · rintro σ σ1 ⟨⟨ha, hn, htb, hN⟩, hs, ht⟩ ⟨⟨hcs, hus, hct, hut⟩, hvars, harrs⟩
    have e_n : σ1.vars "b_n" = σ.vars "b_n" := hvars _ (by simp [adjPrep, Com.wvars])
    have e_tb : σ1.vars "b_tb" = σ.vars "b_tb" := hvars _ (by simp [adjPrep, Com.wvars])
    have e_N : σ1.vars "b_N" = σ.vars "b_N" := hvars _ (by simp [adjPrep, Com.wvars])
    have e_a : σ1.arrs "a" = σ.arrs "a" := harrs _ (by simp [adjPrep, Com.warrs])
    have hnpos : 0 < nV x := nV_pos_of_lt hs
    have hsd : σ.vars "b_s" / σ.vars "b_n" ≤ σ.vars "b_s" := Nat.div_le_self _ _
    have htd : σ.vars "b_t" / σ.vars "b_n" ≤ σ.vars "b_t" := Nat.div_le_self _ _
    have hsm : σ.vars "b_s" % σ.vars "b_n" < σ.vars "b_n" := by rw [hn]; exact Nat.mod_lt _ hnpos
    have htm : σ.vars "b_t" % σ.vars "b_n" < σ.vars "b_n" := by rw [hn]; exact Nat.mod_lt _ hnpos
    refine ⟨⟨by rw [e_a, ha], by rw [e_n, hn], by rw [e_tb, htb], by rw [e_N, hN]⟩, ?_, ?_, ?_, ?_⟩
    · rw [hus, ← hn]; exact hsm
    · rw [hut]; omega
    · rw [hcs]; omega
    · rw [hct]; omega
  · rintro σ σ1 σ2 ⟨⟨ha, hn, htb, hN⟩, hs, ht⟩ ⟨⟨hcs, hus, hct, hut⟩, -, -⟩ hf
    rw [hf, hcs, hct, hus, hut, hn]
    rfl

/-- The scalars assigned by `adjCom`. -/
def adjVars : List String :=
  ["b_cs", "b_us", "b_ct", "b_ut", "b_f", "b_o1", "b_o2", "b_st", "b_dg", "b_j"]

/-- The cost of the adjacency test. -/
def Kadj (x : List ℕ) : ℕ := 100 + (24 * x.length + 60)

theorem adjCom_spec' {x : List ℕ} {B : ℕ} (hgood : Good x) (hB : ∀ w ∈ x, w < B)
    (hxB : x.length + NOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < NOf x ∧ σ.vars "b_t" < NOf x) adjCom
      (fun σ σ' => σ'.vars "b_f" = (if adjW x (σ.vars "b_s") (σ.vars "b_t") then 1 else 0) ∧
        Keep adjVars σ σ' ∧ σ'.out = σ.out) (Kadj x) := by
  refine Spec.post (Spec.frame (adjCom_spec hgood hB hxB))
    fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ => ⟨hq, ?_, ?_⟩
  · refine ⟨fun y hy => hv y ?_, funext fun a => ha a ?_, hi ?_⟩
    · simp only [adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.wvars,
        adjVars] at hy ⊢
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto
    · simp [adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.warrs]
    · simp [adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.reads]
  · exact ho (by simp [adjCom, adjPrep, adjTest, scan, scanLoop, scanBody, bump, Com.NoWrite])

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj
