import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath

/-!
# The Adjacency Test of the Program

`adjCom` decides whether two vertices of the multicoloured graph are adjacent, reading one entry
of the matrix held in array `a`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath

/-- The context every pass runs in. -/
def Ctx (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "b_n" = order x ∧ σ.vars "b_base" = order x + 1 ∧
    σ.vars "b_N" = nOf x

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

lemma mul_add_lt (u v n : ℕ) (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hu
  nlinarith

theorem adjTest_spec {B : ℕ} (L : ℕ) (hB : L + 2 < B) :
    Spec B (fun σ => σ.vars "b_us" < σ.vars "b_n" ∧ σ.vars "b_ut" < σ.vars "b_n" ∧
        σ.vars "b_n" * σ.vars "b_n" + σ.vars "b_n" + 1 ≤ L ∧ σ.vars "b_base" = σ.vars "b_n" + 1 ∧
        σ.vars "b_cs" < B ∧ σ.vars "b_ct" < B ∧
        (σ.arrs "a").getD (σ.vars "b_base" + σ.vars "b_us" * σ.vars "b_n" + σ.vars "b_ut") 0 ≤ 1 ∧
        (σ.arrs "a").length = L) adjTest
      (fun σ σ' => σ'.vars "b_f" =
        if σ.vars "b_cs" ≠ σ.vars "b_ct" ∧ σ.vars "b_us" ≠ σ.vars "b_ut" ∧
          (σ.arrs "a").getD (σ.vars "b_base" + σ.vars "b_us" * σ.vars "b_n" + σ.vars "b_ut") 0 = 0
        then 1 else 0) 100 := by
  unfold adjTest
  refine Spec.pre (P := fun σ => σ.vars "b_us" < σ.vars "b_n" ∧ σ.vars "b_ut" < σ.vars "b_n" ∧
        σ.vars "b_n" * σ.vars "b_n" + σ.vars "b_n" + 1 ≤ L ∧ σ.vars "b_base" = σ.vars "b_n" + 1 ∧
        σ.vars "b_cs" < B ∧ σ.vars "b_ct" < B ∧
        (σ.arrs "a").getD (σ.vars "b_base" + σ.vars "b_us" * σ.vars "b_n" + σ.vars "b_ut") 0 ≤ 1 ∧
        (σ.arrs "a").length = L ∧
        σ.vars "b_us" * σ.vars "b_n" + σ.vars "b_ut" < σ.vars "b_n" * σ.vars "b_n") ?_ ?_
  · run_vcg
    all_goals (simp_all [Env.setVar]; try omega)
  · intro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, mul_add_lt _ _ _ h1 h2⟩

lemma order_le_length {x : List ℕ} (hx : Valid x) : order x ≤ x.length := by
  have := hx.2.1; omega

lemma sq_bound {x : List ℕ} (hx : Valid x) : order x * order x + order x + 1 ≤ x.length := by
  have := hx.2.1; omega

theorem adjCom_spec {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < nOf x ∧ σ.vars "b_t" < nOf x) adjCom
      (fun σ σ' => σ'.vars "b_f" = if adjW x (σ.vars "b_s") (σ.vars "b_t") then 1 else 0) 200 := by
  have hlen := order_le_length hx
  have hsq := sq_bound hx
  have h1 : Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < nOf x ∧ σ.vars "b_t" < nOf x) adjPrep
      (fun σ σ' => (σ'.vars "b_cs" = σ.vars "b_s" / σ.vars "b_n" ∧
        σ'.vars "b_us" = σ.vars "b_s" % σ.vars "b_n" ∧
        σ'.vars "b_ct" = σ.vars "b_t" / σ.vars "b_n" ∧
        σ'.vars "b_ut" = σ.vars "b_t" % σ.vars "b_n") ∧
        (∀ y, y ∉ adjPrep.wvars → σ'.vars y = σ.vars y) ∧
        (∀ a, a ∉ adjPrep.warrs → σ'.arrs a = σ.arrs a)) 100 := by
    refine Spec.post (Spec.pre (adjPrep_spec (B := B)).frame ?_) (fun σ σ' _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    rintro σ ⟨⟨_, hn, _, _⟩, hs, ht⟩
    refine ⟨by omega, by omega, by omega⟩
  refine Spec.seq h1 (adjTest_spec x.length (by omega)) ?_ ?_
  · rintro σ σ1 ⟨⟨ha, hn, hbase, hN⟩, hs, ht⟩ ⟨⟨hcs, hus, hct, hut⟩, hvars, harrs⟩
    have hva : ∀ y, y ∉ adjPrep.wvars → σ1.vars y = σ.vars y := hvars
    have e_n : σ1.vars "b_n" = σ.vars "b_n" := hva _ (by simp [adjPrep, Com.wvars])
    have e_base : σ1.vars "b_base" = σ.vars "b_base" := hva _ (by simp [adjPrep, Com.wvars])
    have e_a : σ1.arrs "a" = σ.arrs "a" := harrs _ (by simp [adjPrep, Com.warrs])
    have hnpos : 0 < order x := order_pos_of_lt hs
    have hu : σ1.vars "b_us" < σ1.vars "b_n" := by
      rw [hus, e_n, hn]; exact Nat.mod_lt _ hnpos
    have hv : σ1.vars "b_ut" < σ1.vars "b_n" := by
      rw [hut, e_n, hn]; exact Nat.mod_lt _ hnpos
    have hsdiv : σ.vars "b_s" / σ.vars "b_n" ≤ σ.vars "b_s" := Nat.div_le_self _ _
    have htdiv : σ.vars "b_t" / σ.vars "b_n" ≤ σ.vars "b_t" := Nat.div_le_self _ _
    refine ⟨hu, hv, by rw [e_n, hn]; exact hsq, by rw [e_base, e_n, hbase, hn], ?_, ?_, ?_, ?_⟩
    · rw [hcs]; omega
    · rw [hct]; omega
    · rw [e_a, ha, e_n, e_base, hn, hbase, hus, hut, hn]
      have hu' : σ.vars "b_s" % order x < order x := Nat.mod_lt _ hnpos
      have hv' : σ.vars "b_t" % order x < order x := Nat.mod_lt _ hnpos
      have := (hx.2.2.2.1 _ hu' _ hv').1
      unfold entry at this
      exact this
    · rw [e_a, ha]
  · rintro σ σ1 σ2 ⟨⟨ha, hn, hbase, hN⟩, hs, ht⟩ ⟨⟨hcs, hus, hct, hut⟩, hvars, harrs⟩ hf
    have hva : ∀ y, y ∉ adjPrep.wvars → σ1.vars y = σ.vars y := hvars
    have e_n : σ1.vars "b_n" = σ.vars "b_n" := hva _ (by simp [adjPrep, Com.wvars])
    have e_base : σ1.vars "b_base" = σ.vars "b_base" := hva _ (by simp [adjPrep, Com.wvars])
    have e_a : σ1.arrs "a" = σ.arrs "a" := harrs _ (by simp [adjPrep, Com.warrs])
    rw [hf]
    simp only [adjW, decide_eq_true_eq]
    rw [hcs, hct, hus, hut, e_a, e_base, e_n, ha, hn, hbase]

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

/-- The scalars assigned by `adjCom`. -/
def adjVars : List String := ["b_cs", "b_us", "b_ct", "b_ut", "b_f"]

theorem adjCom_spec' {x : List ℕ} (hx : Valid x) {B : ℕ} (hB : x.length + nOf x + 2 < B) :
    Spec B (fun σ => Ctx x σ ∧ σ.vars "b_s" < nOf x ∧ σ.vars "b_t" < nOf x) adjCom
      (fun σ σ' => σ'.vars "b_f" = (if adjW x (σ.vars "b_s") (σ.vars "b_t") then 1 else 0) ∧
        Keep adjVars σ σ' ∧ σ'.out = σ.out) 200 := by
  refine Spec.post (Spec.frame (adjCom_spec hx hB)) fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ => ⟨hq, ?_, ?_⟩
  · refine ⟨fun y hy => hv y ?_, funext fun a => ha a ?_, hi ?_⟩
    · simp only [adjCom, adjPrep, adjTest, Com.wvars, adjVars] at hy ⊢
      simpa using hy
    · simp [adjCom, adjPrep, adjTest, Com.warrs]
    · simp [adjCom, adjPrep, adjTest, Com.reads]
  · exact ho (by simp [adjCom, adjPrep, adjTest, Com.NoWrite])

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyAdj
