import Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs
import Mathlib.Data.List.Lex

/-! # The lexicographic comparison `cmp` and the tuple writer `wR`

The tuples live in the array `R`: the tuple of length `r` at `g` is `tupR w g r`. `cmp` compares
two of them entry by entry; the state `(dd, lt)` after a prefix is `cmpF` of the two prefixes, and
after the whole tuples `lt` says whether the first is lexicographically below the second. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs

/-! ### Mathematics -/

/-- The tuple of length `r` starting at `g`. -/
def tupR (w : List ℕ) (g r : ℕ) : List ℕ := (List.range r).map fun l => w.getD (g + l) 0

theorem tupR_succ (w : List ℕ) (g r : ℕ) : tupR w g (r + 1) = tupR w g r ++ [w.getD (g + r) 0] := by
  simp [tupR, List.range_succ]

@[simp] theorem length_tupR (w : List ℕ) (g r : ℕ) : (tupR w g r).length = r := by simp [tupR]

/-- The state of the comparison after two prefixes: `(decided, below)`. -/
def cmpF : List ℕ → List ℕ → ℕ × ℕ
  | a :: u, b :: v => if a < b then (1, 1) else if b < a then (1, 0) else cmpF u v
  | _, _ => (0, 0)

theorem cmpF_eq : ∀ {u v : List ℕ}, u.length = v.length →
    cmpF u v = if u = v then (0, 0) else (1, if u < v then 1 else 0)
  | [], [], _ => by simp [cmpF]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: u, b :: v, h => by
    have ih := cmpF_eq (u := u) (v := v) (by simpa using h)
    simp only [cmpF]
    by_cases hab : a < b
    · simp [hab, List.cons_lt_cons_iff, show a ≠ b by omega]
    · by_cases hba : b < a
      · simp [hab, hba, List.cons_lt_cons_iff, show a ≠ b by omega, show ¬ a = b by omega]
      · have : a = b := by omega
        subst this
        simp [ih, List.cons_lt_cons_iff]

theorem cmpF_snoc : ∀ {u v : List ℕ} (a b : ℕ), u.length = v.length →
    cmpF (u ++ [a]) (v ++ [b]) =
      if (cmpF u v).1 = 0 then (if a < b then (1, 1) else if b < a then (1, 0) else (0, 0))
      else cmpF u v
  | [], [], a, b, _ => by simp [cmpF]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: u, d :: v, a, b, h => by
    have ih := cmpF_snoc (u := u) (v := v) a b (by simpa using h)
    simp only [List.cons_append, cmpF]
    by_cases hcd : c < d
    · simp [hcd]
    · by_cases hdc : d < c
      · simp [hcd, hdc]
      · simp only [hcd, hdc, if_false]; exact ih

theorem cmpF_le (u v : List ℕ) : (cmpF u v).1 ≤ 1 ∧ (cmpF u v).2 ≤ 1 := by
  induction u generalizing v with
  | nil => simp [cmpF]
  | cons a u ih =>
    cases v with
    | nil => simp [cmpF]
    | cons b v => simp only [cmpF]; split_ifs <;> simp [ih v]

/-- **After whole tuples** the comparison says whether the first is below the second. -/
theorem cmpF_snd {u v : List ℕ} (h : u.length = v.length) :
    (cmpF u v).2 = if u < v then 1 else 0 := by
  rw [cmpF_eq h]
  split_ifs with h1 h2 <;> first | rfl | (subst h1; simp at h2)

/-- Decided. -/
def cmpD (u v : List ℕ) : ℕ := (cmpF u v).1
/-- Below. -/
def cmpT (u v : List ℕ) : ℕ := (cmpF u v).2

theorem cmpT_le_cmpD (u v : List ℕ) : cmpT u v ≤ cmpD u v ∧ cmpD u v ≤ 1 := by
  unfold cmpT cmpD
  induction u generalizing v with
  | nil => simp [cmpF]
  | cons a u ih =>
    cases v with
    | nil => simp [cmpF]
    | cons b v => simp only [cmpF]; split_ifs <;> simp [ih v]

theorem cmpD_snoc {u v : List ℕ} (a b : ℕ) (h : u.length = v.length) :
    cmpD (u ++ [a]) (v ++ [b]) = if cmpD u v = 0 then (if a < b then 1 else if b < a then 1 else 0)
      else cmpD u v := by
  unfold cmpD; rw [cmpF_snoc a b h]; split_ifs <;> rfl

theorem cmpT_snoc {u v : List ℕ} (a b : ℕ) (h : u.length = v.length) :
    cmpT (u ++ [a]) (v ++ [b]) = if cmpD u v = 0 then (if a < b then 1 else 0) else cmpT u v := by
  unfold cmpD cmpT; rw [cmpF_snoc a b h]; split_ifs <;> first | rfl | omega

/-! ### `cmp` -/

variable {B : ℕ}

/-- The values `cmp` needs below the bound. -/
structure CmpOK (B : ℕ) (w : List ℕ) (g1 g2 r : ℕ) : Prop where
  len1 : g1 + r ≤ w.length
  len2 : g2 + r ≤ w.length
  ent : ∀ v ∈ w, v < B
  b1 : g1 + r + 1 < B
  b2 : g2 + r + 1 < B
  two : 2 < B

/-- The invariant of the comparison loop. -/
def CI (w : List ℕ) (g1 g2 r : ℕ) (σ : Env) : Prop :=
  σ.arrs "R" = w ∧ σ.vars "x1" = g1 ∧ σ.vars "x2" = g2 ∧ σ.vars "r" = r ∧ σ.vars "l1" ≤ r ∧
    σ.vars "dd" = cmpD (tupR w g1 (σ.vars "l1")) (tupR w g2 (σ.vars "l1")) ∧
    σ.vars "lt" = cmpT (tupR w g1 (σ.vars "l1")) (tupR w g2 (σ.vars "l1"))

theorem getD_lt {w : List ℕ} (h : ∀ v ∈ w, v < B) (hB : 0 < B) (i : ℕ) : w.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hw : w[i]? with _ | v
  · simpa using hB
  · exact h v (List.mem_of_getElem? hw)

set_option maxHeartbeats 4000000 in
theorem cmpBody_spec {w : List ℕ} {g1 g2 r : ℕ} (hok : CmpOK B w g1 g2 r) :
    Spec B (fun σ => CI w g1 g2 r σ ∧ σ.vars "l1" < r) (.seq cmpStep (bump "l1"))
      (fun σ σ' => CI w g1 g2 r σ' ∧ σ'.vars "l1" = σ.vars "l1" + 1) 60 := by
  have hB1 : 2 < B := hok.two
  refine Spec.pre (P := fun σ => (CI w g1 g2 r σ ∧ σ.vars "l1" < r) ∧
    σ.vars "x1" + σ.vars "l1" < (σ.arrs "R").length ∧ σ.vars "x2" + σ.vars "l1" < (σ.arrs "R").length ∧
    (σ.arrs "R").getD (σ.vars "x1" + σ.vars "l1") 0 < B ∧
    (σ.arrs "R").getD (σ.vars "x2" + σ.vars "l1") 0 < B ∧
    σ.vars "x1" + σ.vars "l1" < B ∧ σ.vars "x2" + σ.vars "l1" < B ∧ σ.vars "l1" + 1 < B ∧
    σ.vars "dd" < B ∧ σ.vars "lt" < B) ?_ ?_
  · unfold cmpStep
    run_vcg
    all_goals
      have hCI := ‹CI w g1 g2 r σ›
      obtain ⟨hR, h1, h2, -, -, -, -⟩ := id hCI
      have hu : (tupR w g1 (σ.vars "l1")).length = (tupR w g2 (σ.vars "l1")).length := by simp
      have hTD := cmpT_le_cmpD (tupR w g1 (σ.vars "l1")) (tupR w g2 (σ.vars "l1"))
      simp only [hR, h1, h2] at *
      obtain ⟨hR, h1, h2, hr, hl, hd, ht⟩ := hCI
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Env.setVar] <;>
        (try simp only [ite_true, ite_false, String.reduceEq]) <;>
        (try rw [tupR_succ, tupR_succ, cmpD_snoc _ _ hu]) <;>
        (try rw [tupR_succ, tupR_succ, cmpT_snoc _ _ hu]) <;>
        (try simp_all) <;> (try split_ifs) <;> omega
  · rintro σ ⟨⟨hR, h1, h2, hr, hl, hd, ht⟩, hlt⟩
    have hle := cmpF_le (tupR w g1 (σ.vars "l1")) (tupR w g2 (σ.vars "l1"))
    rw [← cmpD, ← cmpT] at hle
    have := hok.len1; have := hok.len2; have := hok.b1; have := hok.b2
    refine ⟨⟨⟨hR, h1, h2, hr, hl, hd, ht⟩, hlt⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR, h1]; omega
    · rw [hR, h2]; omega
    · rw [hR]; exact getD_lt hok.ent (by omega) _
    · rw [hR]; exact getD_lt hok.ent (by omega) _
    · omega
    · omega
    · omega
    · omega
    · omega

/-- **The comparison.** -/
theorem cmp_spec {w : List ℕ} {g1 g2 r : ℕ} (hok : CmpOK B w g1 g2 r) :
    Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "x1" = g1 ∧ σ.vars "x2" = g2 ∧ σ.vars "r" = r) cmpC
      (fun σ σ' => σ'.vars "lt" = (if tupR w g1 r < tupR w g2 r then 1 else 0) ∧
        Keep ["dd", "lt", "l1"] σ σ') (64 * r + 20) := by
  have hloop := Spec.forRangeZero (B := B) (c := .seq cmpStep (bump "l1")) "l1" "r"
    (CI w g1 g2 r) r 60 (by have := hok.b1; omega) (fun σ h => h.2.2.2.2.1)
    (fun σ h => h.2.2.2.1) (cmpBody_spec hok)
  have h : Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "x1" = g1 ∧ σ.vars "x2" = g2 ∧
      σ.vars "r" = r ∧ 1 < B) cmpC
      (fun _ σ' => σ'.vars "lt" = (if tupR w g1 r < tupR w g2 r then 1 else 0)) (64 * r + 20) := by
    unfold cmpC loop
    run_vcg [hloop]
    all_goals first
      | (obtain ⟨⟨-, -, -, -, -, -, ht⟩, hl⟩ := ‹CI w g1 g2 r _ ∧ _›
         rw [ht, hl, cmpT, cmpF_snd (by simp)])
      | (simp only [CI, Env.setVar] at *; simp_all [tupR, cmpF, cmpD, cmpT])
      | omega
  intro σ hσ
  have h' := Spec.keep h ["dd", "lt", "l1"]
    (by intro y hy; simp [cmpC, loop, cmpStep, bump, Com.wvars] at hy; simp; tauto)
    (by simp [cmpC, loop, cmpStep, bump, Com.warrs]) (by simp [cmpC, loop, cmpStep, bump, Com.reads])
  exact h' σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2, by have := hok.b1; omega⟩

/-- **The comparison**, with the positions read off the state. -/
theorem cmp_spec' {w : List ℕ} {r : ℕ} :
    Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "r" = r ∧ CmpOK B w (σ.vars "x1") (σ.vars "x2") r)
      cmpC
      (fun σ σ' => σ'.vars "lt" =
          (if tupR w (σ.vars "x1") r < tupR w (σ.vars "x2") r then 1 else 0) ∧
        Keep ["dd", "lt", "l1"] σ σ') (64 * r + 20) := by
  intro σ ⟨hR, hr, hok⟩
  exact cmp_spec hok σ ⟨hR, rfl, rfl, hr⟩

/-! ### `wR` -/

/-- The invariant of the tuple writer. -/
def WI (w : List ℕ) (g n : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "R" = w ∧ σ.vars "g" = g ∧ σ.vars "nn" = n ∧ σ.vars "l2" ≤ n ∧
    σ.out = out0 ++ tupR w g (σ.vars "l2")

set_option maxHeartbeats 1000000 in
/-- **Writing `R[g … g + n - 1]`.** -/
theorem wR_spec {w : List ℕ} {g n : ℕ} (hlen : g + n ≤ w.length) (hent : ∀ v ∈ w, v < B)
    (hb : g + n + 1 < B) :
    Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "g" = g ∧ σ.vars "nn" = n) wR
      (fun σ σ' => σ'.out = σ.out ++ tupR w g n ∧ Keep ["l2"] σ σ') (24 * n + 6) := by
  have hbody : ∀ out0 : List ℕ, Spec B (fun σ => WI w g n out0 σ ∧ σ.vars "l2" < n)
      (.seq (.write (.get "R" (.add (V "g") (V "l2")))) (bump "l2"))
      (fun σ σ' => WI w g n out0 σ' ∧ σ'.vars "l2" = σ.vars "l2" + 1) 20 := by
    intro out0
    refine Spec.pre (P := fun σ => (WI w g n out0 σ ∧ σ.vars "l2" < n) ∧
      σ.vars "g" + σ.vars "l2" < (σ.arrs "R").length ∧
      (σ.arrs "R").getD (σ.vars "g" + σ.vars "l2") 0 < B ∧
      σ.vars "g" + σ.vars "l2" < B ∧ σ.vars "l2" + 1 < B) ?_ ?_
    · run_vcg
      all_goals
        obtain ⟨hR, h1, h2, hl, ho⟩ := ‹WI w g n out0 σ›
        simp only [WI, Env.setVar] at *
        simp_all [tupR_succ]
      all_goals omega
    · rintro σ ⟨⟨hR, h1, h2, hl, ho⟩, hlt⟩
      refine ⟨⟨⟨hR, h1, h2, hl, ho⟩, hlt⟩, by rw [hR, h1]; omega, ?_, by omega, by omega⟩
      rw [hR]; exact getD_lt hent (by omega) _
  have h : ∀ out0 : List ℕ, Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "g" = g ∧
      σ.vars "nn" = n ∧ σ.out = out0) wR
      (fun _ σ' => σ'.out = out0 ++ tupR w g n) (24 * n + 6) := by
    intro out0
    refine Spec.post (Spec.pre (Spec.forRangeZero "l2" "nn" (WI w g n out0) n 20 (by omega)
      (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1) (hbody out0)) ?_) ?_
    · rintro σ ⟨hR, h1, h2, ho⟩
      simp [WI, Env.setVar, hR, h1, h2, ho, tupR]
    · rintro σ σ' - ⟨⟨-, -, -, -, ho⟩, hl⟩
      rw [ho, hl]
  intro σ hσ
  have h' := Spec.keep (h σ.out) ["l2"]
    (by intro y hy; simpa [wR, loop, bump, Com.wvars] using hy)
    (by simp [wR, loop, bump, Com.warrs]) (by simp [wR, loop, bump, Com.reads])
  exact h' σ ⟨hσ.1, hσ.2.1, hσ.2.2, rfl⟩

/-- **Writing a tuple**, with the start read off the state. -/
theorem wR_spec' {w : List ℕ} {n : ℕ} (hent : ∀ v ∈ w, v < B) :
    Spec B (fun σ => σ.arrs "R" = w ∧ σ.vars "nn" = n ∧ σ.vars "g" + n ≤ w.length ∧
        σ.vars "g" + n + 1 < B) wR
      (fun σ σ' => σ'.out = σ.out ++ tupR w (σ.vars "g") n ∧ Keep ["l2"] σ σ') (24 * n + 6) := by
  intro σ ⟨hR, hn, h1, h2⟩
  exact wR_spec h1 hent h2 σ ⟨hR, rfl, hn⟩

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
