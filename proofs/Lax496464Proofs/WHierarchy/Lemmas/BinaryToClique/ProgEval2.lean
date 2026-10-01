import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval1

/-! # Σ₁[2] model checking to Clique: one node, and the evaluation of all nodes

`evStepC_spec`: the program's operation on the stack for one node is `evStep`; `evLoop_spec`: the
loop over all nodes leaves the value of the formula under the valuation on top of the stack. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval1
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-! ### The nodes -/

theorem nd_bound_step (x : List ℕ) {st : TS} {n : ℕ} (hs : Shape st) (hl : st.nd.length ≤ n)
    (h : ∀ e ∈ st.nd, e.1 ≤ Mmax x + 2 ∧ e.2 ≤ n) :
    ∀ e ∈ (tokStep x st).nd, e.1 ≤ Mmax x + 2 ∧ e.2 ≤ n + 1 := by
  have hab := hs.1
  intro e he
  unfold tokStep at he
  split_ifs at he
  · have := h e he; omega
  · simp only [relStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · have := h e he; omega
    · simp; omega
  · simp only [eqStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · have := h e he; omega
    · simp; omega
  · simp only [otherStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · have := h e he; omega
    · simp; exact getD_le_Mmax x _ |>.trans (by omega)
  · have := h e he; omega

theorem nd_bound_iter (x : List ℕ) : ∀ n, ∀ e ∈ ((tokStep x)^[n] (tokInit x)).nd,
    e.1 ≤ Mmax x + 2 ∧ e.2 ≤ n
  | 0 => by simp [tokInit]
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact nd_bound_step x (shape_iter x n).1 (shape_iter x n).2 (nd_bound_iter x n)

theorem tok_nd_bound (x : List ℕ) : ∀ e ∈ (tok x).nd, e.1 ≤ Mmax x + 2 ∧ e.2 ≤ x.length :=
  nd_bound_iter x x.length

/-- The stack after the last `k` nodes. -/
def sfx (x : List ℕ) (c k : ℕ) : List ℕ :=
  ((tok x).nd.drop ((tok x).nd.length - k)).foldr (evStep c) []

theorem sfx_zero (x : List ℕ) (c : ℕ) : sfx x c 0 = [] := by simp [sfx]

theorem sfx_succ (x : List ℕ) (c : ℕ) {k : ℕ} (hk : k < (tok x).nd.length) :
    sfx x c (k + 1) = evStep c ((tok x).nd[(tok x).nd.length - (k + 1)]'(by omega)) (sfx x c k) := by
  unfold sfx
  rw [List.drop_eq_getElem_cons (by omega), List.foldr_cons]
  congr 3; omega

theorem length_sfx (x : List ℕ) (c : ℕ) : ∀ k, k ≤ (tok x).nd.length → (sfx x c k).length ≤ k
  | 0, _ => by simp [sfx_zero]
  | k + 1, hk => by
    rw [sfx_succ x c (by omega)]
    have := length_sfx x c k (by omega)
    have := length_evStep c ((tok x).nd[(tok x).nd.length - (k + 1)]'(by omega)) (sfx x c k)
    omega

theorem bits_sfx (x : List ℕ) (c : ℕ) : ∀ k, k ≤ (tok x).nd.length → Bits (sfx x c k)
  | 0, _ => by simp [sfx_zero, Bits]
  | k + 1, hk => by
    rw [sfx_succ x c (by omega)]
    exact evStep_bits _ _ (bits_sfx x c k (by omega))

theorem sfx_all (x : List ℕ) (c : ℕ) : sfx x c (tok x).nd.length = evalNd c (tok x).nd := by
  simp [sfx, evalNd]

/-! ### One node -/

set_option maxHeartbeats 2000000 in
theorem opC_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ l.length < S ∧ S < B ∧ 5 < B ∧ σ.vars "zc" < B ∧
        σ.vars "zm" < B ∧ σ.vars "zc" / 2 ^ σ.vars "zm" < B ∧ σ.vars "zg" < B)
      opC (fun σ σ' => SI S (evStep (σ.vars "zc") (σ.vars "zg", σ.vars "zm") l) σ') 80 := by
  unfold opC
  run_vcg [pushBit_spec (B := B) (S := S) l, pushBit_spec (B := B) (S := S) l,
    negC_spec (B := B) (S := S) l, andC_spec (B := B) (S := S) l, orC_spec (B := B) (S := S) l]
  all_goals first
    | omega
    | exact ⟨‹SI S l σ›, by (repeat' constructor) <;> first | assumption | omega⟩
    | simp_all [evStep]

/-! ### The loop over the nodes -/

theorem SI_setVar {S : ℕ} {l : List ℕ} {σ : Env} (h : SI S l σ) (y : String) (hy : y ≠ "zsp")
    (v : ℕ) : SI S l (σ.setVar y v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simp [Ne.symm hy, h1], h2, h3, h4⟩

/-- The invariant of the loop over the nodes, for the valuation `c`. -/
def EVI (x : List ℕ) (c : ℕ) (σ : Env) : Prop :=
  σ.vars "zc" = c ∧ σ.vars "zT" = (tok x).nd.length ∧
    σ.arrs "nt" = pad ((tok x).nd.map Prod.fst) (x.length + 1) ∧
    σ.arrs "na" = pad ((tok x).nd.map Prod.snd) (x.length + 1) ∧
    σ.vars "zet" ≤ (tok x).nd.length ∧ SI (x.length + 1) (sfx x c (σ.vars "zet")) σ

theorem evRead_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zT" < B ∧ σ.vars "zet" + 1 < B ∧
        σ.vars "zT" - (σ.vars "zet" + 1) < (σ.arrs "nt").length ∧
        σ.vars "zT" - (σ.vars "zet" + 1) < (σ.arrs "na").length ∧
        (σ.arrs "nt").getD (σ.vars "zT" - (σ.vars "zet" + 1)) 0 < B ∧
        (σ.arrs "na").getD (σ.vars "zT" - (σ.vars "zet" + 1)) 0 < B)
      (.seq (.assign "zj" (.sub (V "zT") (.add (V "zet") (.lit 1))))
        (.seq (.assign "zg" (.get "nt" (V "zj"))) (.assign "zm" (.get "na" (V "zj")))))
      (fun σ σ' => σ' = ((σ.setVar "zj" (σ.vars "zT" - (σ.vars "zet" + 1))).setVar "zg"
        ((σ.arrs "nt").getD (σ.vars "zT" - (σ.vars "zet" + 1)) 0)).setVar "zm"
        ((σ.arrs "na").getD (σ.vars "zT" - (σ.vars "zet" + 1)) 0)) 20 := by
  run_vcg
  all_goals first
    | omega
    | simp_all

set_option maxHeartbeats 2000000 in
theorem evStepC_spec {x : List ℕ} {B c : ℕ} (hc : c < B) (hL : 2 * x.length + 6 < B)
    (hM : Mmax x + 3 < B) :
    Spec B (fun σ => EVI x c σ ∧ σ.vars "zet" < (tok x).nd.length) evStepC
      (fun σ σ' => EVI x c σ' ∧ σ'.vars "zet" = σ.vars "zet" + 1) 120 := by
  intro σ ⟨⟨hzc, hT, hnt, hna, hle, hSI⟩, hlt⟩
  have hTL := (tok_shape x).2
  have hbd := tok_nd_bound x
  set k := σ.vars "zet" with hk
  set T := (tok x).nd.length with hTdef
  have hj : T - (k + 1) < T := by omega
  have hntj : (σ.arrs "nt").getD (T - (k + 1)) 0 = ((tok x).nd[T - (k + 1)]'hj).1 := by
    rw [hnt, getD_pad, List.getD_eq_getElem _ _ (by simp; omega)]; simp
  have hnaj : (σ.arrs "na").getD (T - (k + 1)) 0 = ((tok x).nd[T - (k + 1)]'hj).2 := by
    rw [hna, getD_pad, List.getD_eq_getElem _ _ (by simp; omega)]; simp
  have he := hbd _ (List.getElem_mem hj)
  have lnt : (σ.arrs "nt").length = x.length + 1 := by rw [hnt, length_pad (by simp; omega)]
  have lna : (σ.arrs "na").length = x.length + 1 := by rw [hna, length_pad (by simp; omega)]
  obtain ⟨σ3, r3, e3⟩ := evRead_spec (B := B) σ ⟨by rw [hT]; omega, by omega,
    by rw [hT, lnt]; omega, by rw [hT, lna]; omega, by rw [hT, hntj]; omega,
    by rw [hT, hnaj]; omega⟩
  rw [hT, hntj, hnaj] at e3
  have hls := length_sfx x c k hle
  have h3SI : SI (x.length + 1) (sfx x c k) σ3 := by
    rw [e3]
    exact SI_setVar (SI_setVar (SI_setVar hSI _ (by decide) _) _ (by decide) _) _ (by decide) _
  have hc3 : σ3.vars "zc" = c := by rw [e3]; simp [hzc]
  have hg3 : σ3.vars "zg" = ((tok x).nd[T - (k + 1)]'hj).1 := by rw [e3]; simp
  have hm3 : σ3.vars "zm" = ((tok x).nd[T - (k + 1)]'hj).2 := by rw [e3]; simp
  obtain ⟨σ4, r4, h4⟩ := opC_spec (B := B) (S := x.length + 1) (sfx x c k) σ3
    ⟨h3SI, by omega, by omega, by omega, by rw [hc3]; exact hc, by rw [hm3]; omega,
      by rw [hc3]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hc, by rw [hg3]; omega⟩
  rw [hc3, hg3, hm3, ← sfx_succ x c (by omega)] at h4
  have f4 : ∀ y, y ∉ opC.wvars → σ4.vars y = σ3.vars y := fun y hy => r4.frame_var y hy
  have fa4 : ∀ a, a ∉ opC.warrs → σ4.arrs a = σ3.arrs a := fun a ha => r4.frame_arr a ha
  have het4 : σ4.vars "zet" = k := by
    rw [f4 "zet" (by decide), e3]; simp [hk]
  have hv : (Expr.add (V "zet") (.lit 1)).evalB B σ4 = some (k + 1) := by
    have := evalB_bin (op := .add) (evalB_var (x := "zet") (σ := σ4) (B := B) (by omega))
      (evalB_lit (n := 1) (σ := σ4) (B := B) (by omega)) (by simp; omega)
    rw [het4] at this; exact this
  have r5 : Run B (bump "zet") σ4 (σ4.setVar "zet" (k + 1)) 4 := by
    have := Run.assign (x := "zet") hv
    simpa using this
  refine ⟨_, (r3.seq (r4.seq r5)).mono (by norm_num), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hk]⟩
  · simp; rw [f4 "zc" (by decide), hc3]
  · simp; rw [f4 "zT" (by decide), e3]; simp [hT, hTdef]
  · simp; rw [fa4 "nt" (by decide), e3]; simp [hnt]
  · simp; rw [fa4 "na" (by decide), e3]; simp [hna]
  · simp; omega
  · simp only [vars_setVar, ↓reduceIte]
    exact SI_setVar h4 _ (by decide) _

theorem evLoop_spec {x : List ℕ} {B c : ℕ} (hc : c < B) (hL : 2 * x.length + 6 < B)
    (hM : Mmax x + 3 < B) :
    Spec B (fun σ => EVI x c (σ.setVar "zet" 0)) evLoop
      (fun _ σ' => EVI x c σ' ∧ σ'.vars "zet" = (tok x).nd.length)
      ((120 + 4) * (tok x).nd.length + 6) := by
  have hTL := (tok_shape x).2
  exact Spec.forRangeZero "zet" "zT" (EVI x c) (tok x).nd.length 120 (by omega)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.1) (evStepC_spec hc hL hM)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval2
