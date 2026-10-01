import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop

/-!
# Generic pieces of the program: digits, powers, counted loops

`decG_spec`: the `c` lowest digits of `w` into positions `j, …, j+c-1` of an array.
`powG_spec`: a power. `loopC_out`: a counted loop whose iteration `i` writes `g i` and keeps a
context.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Frame Frame.refl Frame.trans Frame.mono Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs

variable {B : ℕ}

/-! ### Digits -/

theorem set_take_drop (l : List ℕ) {j c : ℕ} (hj : j + (c + 1) ≤ l.length) (v : ℕ) (ds : List ℕ) :
    (l.set j v).take (j + 1) ++ ds ++ (l.set j v).drop (j + 1 + c) =
      l.take j ++ (v :: ds) ++ l.drop (j + (c + 1)) := by
  have h1 : (l.set j v).take (j + 1) = l.take j ++ [v] := by
    rw [List.take_add_one, List.getElem?_set_self (by omega)]
    simp [List.take_set_of_le (le_refl j)]
  have h2 : (l.set j v).drop (j + 1 + c) = l.drop (j + (c + 1)) := by
    rw [List.drop_set_of_lt (show j < j + 1 + c by omega), show j + 1 + c = j + (c + 1) by omega]
  rw [h1, h2]; simp

set_option maxHeartbeats 1000000 in
theorem decStoreG_spec {arr w bs : String} {n w0 j : ℕ} (hwB : w0 < B) (hnB : n < B)
    (hjB : j < B) :
    Spec B (fun σ => σ.vars w = w0 ∧ σ.vars bs = n ∧ j < (σ.arrs arr).length)
      (.store arr (.lit j) (.sub (V w) (.mul (.div (V w) (V bs)) (V bs))))
      (fun σ σ' => σ'.arrs arr = (σ.arrs arr).set j (w0 % n) ∧
        Frame [] [arr] σ σ' ∧ σ'.out = σ.out) 12 := by
  have h1 : w0 / n ≤ w0 := Nat.div_le_self w0 n
  have h2 : w0 / n * n ≤ w0 := Nat.div_mul_le_self w0 n
  refine Spec.pre (P := fun σ => (σ.vars w = w0 ∧ σ.vars bs = n ∧
      j < (σ.arrs arr).length) ∧ σ.vars w / σ.vars bs ≤ σ.vars w ∧
      σ.vars w / σ.vars bs * σ.vars bs ≤ σ.vars w) ?_ ?_
  · run_vcg
    have hw := ‹σ.vars w = w0›
    have hn := ‹σ.vars bs = n›
    refine ⟨by simp [Env.setArr, hw, hn, mod_eq_sub], ⟨fun y hy => rfl, fun b hb => ?_, rfl⟩, rfl⟩
    have : b ≠ arr := fun e => hb (by simp [e])
    simp [Env.setArr, this]
  · rintro σ ⟨hw, hn, hj⟩
    exact ⟨⟨hw, hn, hj⟩, by rw [hw, hn]; exact h1, by rw [hw, hn]; exact h2⟩

set_option maxHeartbeats 1000000 in
theorem decDivG_spec {w bs : String} {n w0 : ℕ} (hwB : w0 < B) (hnB : n < B) :
    Spec B (fun σ => σ.vars w = w0 ∧ σ.vars bs = n)
      (.assign w (.div (V w) (V bs)))
      (fun σ σ' => σ' = σ.setVar w (w0 / n)) 4 := by
  refine Spec.pre (P := fun σ => (σ.vars w = w0 ∧ σ.vars bs = n) ∧
      σ.vars w / σ.vars bs ≤ σ.vars w) ?_ ?_
  · run_vcg
    rw [‹σ.vars w = w0›, ‹σ.vars bs = n›]
  · rintro σ ⟨hw, hn⟩
    exact ⟨⟨hw, hn⟩, Nat.div_le_self _ _⟩

/-- **Digits into an array.** -/
theorem decG_spec {arr w bs : String} (hwb : w ≠ bs) {n : ℕ} (hnB : n < B) {L : ℕ} :
    ∀ (c j w0 : ℕ), w0 < B → j + c ≤ L → j + c < B →
    Spec B (fun σ => σ.vars w = w0 ∧ σ.vars bs = n ∧ (σ.arrs arr).length = L)
      (decG arr w bs j c)
      (fun σ σ' => σ'.arrs arr = (σ.arrs arr).take j ++ digits n c w0 ++ (σ.arrs arr).drop (j + c) ∧
        Frame [w] [arr] σ σ' ∧ σ'.out = σ.out) (20 * c + 1)
  | 0, j, w0, _, _, _ => by
    refine (Spec.skip (B := B)).post fun σ σ' h e => ?_
    subst e
    exact ⟨by simp [digits], Frame.refl _ _ _, rfl⟩
  | c + 1, j, w0, hw, hjL, hjB => by
    have h1 := decStoreG_spec (B := B) (arr := arr) (w := w) (bs := bs) (n := n) (w0 := w0)
      (j := j) hw hnB (by omega)
    have h1' : Spec B (fun σ => σ.vars w = w0 ∧ σ.vars bs = n ∧ (σ.arrs arr).length = L) _ _ 12 :=
      h1.pre (by intro σ h; exact ⟨h.1, h.2.1, by omega⟩)
    have hd := decDivG_spec (B := B) (w := w) (bs := bs) (n := n) (w0 := w0) hw hnB
    have h2 := decG_spec (arr := arr) (L := L) hwb hnB c (j + 1) (w0 / n) (lt_of_le_of_lt (Nat.div_le_self w0 n) hw)
      (by omega) (by omega)
    have hd' : Spec B (fun σ => σ.vars w = w0 ∧ σ.vars bs = n ∧ (σ.arrs arr).length = L) _ _ 4 :=
      hd.pre (by intro σ h; exact ⟨h.1, h.2.1⟩)
    have h23' := Spec.seq' hd' h2 (by
      intro σ σ' hp hq
      subst hq
      exact ⟨by simp [Env.setVar], by simp [Env.setVar, Ne.symm hwb, hp.2.1],
        by simp [Env.setVar, hp.2.2]⟩)
    refine Spec.mono (Spec.seq h1' h23' ?_ ?_) (by omega)
    · intro σ σ' hp hq
      exact ⟨by rw [hq.2.1.1 _ (by simp)]; exact hp.1, by rw [hq.2.1.1 _ (by simp)]; exact hp.2.1,
        by rw [hq.1]; simp; omega⟩
    rintro σ σ' σ'' hp ⟨a1, f1, o1⟩ ⟨σm, rfl, ⟨a2, f2, o2⟩⟩
    refine ⟨?_, (f1.mono (by simp) (by simp)).trans ((Frame.setVar σ' (by simp) _).trans f2),
      by rw [o2]; simpa using o1⟩
    rw [a2]
    simp only [Env.setVar]
    rw [a1, set_take_drop _ (by omega)]
    simp [digits]

/-! ### Powers -/

theorem powG_spec {dst bs : String} (hdb : dst ≠ bs) {b0 : ℕ} (h1 : 1 < B) :
    ∀ e : ℕ, (b0 + 1) ^ e < B →
    Spec B (fun σ => σ.vars bs = b0) (powG dst bs e)
      (fun σ σ' => σ'.vars dst = b0 ^ e ∧ Frame [dst] [] σ σ' ∧ σ'.out = σ.out) (4 * e + 2)
  | 0, _ => by
    refine (Spec.assign (P := fun σ => σ.vars bs = b0) (x := dst) (e := .lit 1)
      (f := fun _ => 1) fun σ _ => evalB_lit h1).post fun σ σ' _ h => ?_
    subst h
    exact ⟨by simp [Env.setVar], Frame.setVar σ (by simp) _, rfl⟩
  | e + 1, he => by
    have hle : (b0 + 1) ^ e ≤ (b0 + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have ih := powG_spec (b0 := b0) hdb h1 e (by omega)
    have hb1 : b0 ^ (e + 1) ≤ (b0 + 1) ^ (e + 1) := Nat.pow_le_pow_left (by omega) _
    have hb0 : b0 ^ e ≤ (b0 + 1) ^ e := Nat.pow_le_pow_left (by omega) _
    have hbB : b0 ≤ (b0 + 1) ^ (e + 1) := by
      calc b0 ≤ b0 + 1 := by omega
        _ = (b0 + 1) ^ 1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : Spec B (fun σ => σ.vars bs = b0 ∧ σ.vars dst = b0 ^ e)
        (.assign dst (.mul (V dst) (V bs)))
        (fun σ σ' => σ' = σ.setVar dst (b0 ^ (e + 1))) 4 :=
      Spec.assign (f := fun _ => b0 ^ (e + 1)) fun σ h => by
        have := evalB_bin (op := .mul) (evalB_var (x := dst) (σ := σ) (B := B)
          (by rw [h.2]; omega)) (evalB_var (x := bs) (σ := σ) (B := B) (by rw [h.1]; omega))
          (by rw [h.1, h.2, Bop.apply_mul, ← pow_succ]; omega)
        rw [h.1, h.2, Bop.apply_mul, ← pow_succ] at this
        exact this
    refine Spec.mono (Spec.seq ih h2 (fun σ σ' hp hq =>
      ⟨by rw [hq.2.1.1 _ (by simp [Ne.symm hdb])]; exact hp, hq.1⟩) ?_) (by omega)
    rintro σ σ' σ'' - ⟨-, f1, o1⟩ rfl
    exact ⟨by simp [Env.setVar], f1.trans (Frame.setVar σ' (by simp) _), by rw [← o1]; rfl⟩

/-! ### Counted loops writing output -/

/-- **A counted loop** whose iteration `i` keeps the context `Ctx`, leaves the counter alone and
writes `g i`. -/
theorem loopC_out {x m : String} {body : Com} {N Kb : ℕ} (hNB : N + 1 < B)
    (Ctx : Env → Prop) (hset : ∀ σ v, Ctx σ → Ctx (σ.setVar x v))
    (hm : ∀ σ, Ctx σ → σ.vars m = N) (g : ℕ → List ℕ)
    (hbody : ∀ i < N, Spec B (fun σ => Ctx σ ∧ σ.vars x = i) body
      (fun σ σ' => Ctx σ' ∧ σ'.vars x = i ∧ σ'.out = σ.out ++ g i) Kb) :
    Spec B Ctx (loopC x m body)
      (fun σ σ' => Ctx σ' ∧ σ'.out = σ.out ++ (List.range N).flatMap g) ((Kb + 4 + 4) * N + 6) := by
  intro σ hσ
  let I : Env → Prop := fun τ => Ctx τ ∧ τ.vars x ≤ N ∧
    τ.out = σ.out ++ (List.range (τ.vars x)).flatMap g
  have hstep : Spec B (fun τ => I τ ∧ τ.vars x < N) (.seq body (bump x))
      (fun τ τ' => I τ' ∧ τ'.vars x = τ.vars x + 1) (Kb + 4) := by
    intro τ ⟨⟨hc, hle, ho⟩, hlt⟩
    obtain ⟨τ1, hr1, hc1, hx1, ho1⟩ := hbody (τ.vars x) hlt τ ⟨hc, rfl⟩
    have hb := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop.bump_spec (B := B) x τ1
      (show τ1.vars x + 1 < B by rw [hx1]; omega)
    obtain ⟨τ2, hr2, rfl⟩ := hb
    refine ⟨_, hr1.seq hr2, ⟨hset _ _ hc1, by simp [Env.setVar, hx1]; omega, ?_⟩, by
      simp [Env.setVar, hx1]⟩
    show τ1.out = _
    rw [ho1, ho]
    simp [Env.setVar, hx1, List.range_succ]
  have hloop := Spec.forRangeZero (B := B) (c := .seq body (bump x)) x m I N (Kb + 4) (by omega)
    (fun τ h => h.2.1) (fun τ h => hm τ h.1) hstep
  obtain ⟨σ', hr, ⟨hc', -, ho'⟩, hx'⟩ := hloop σ ⟨hset σ 0 hσ, by simp [Env.setVar],
    by simp [Env.setVar]⟩
  refine ⟨σ', hr, hc', ?_⟩
  rw [ho', hx']

/-! ### What the pieces assign -/

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
