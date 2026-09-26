import Lax496464Proofs.Ram.Q3Defs

/-!
# Q3: the table-chain lemmas (pure)

`tab_init`, `tab_step`, `tab_final`: the initial table means `R0`, a marginalisation pass followed
by a take pass turns a table meaning `R` into one meaning `Step .. R`, and the answer read-off.
-/

namespace Lax496464Proofs.Ram.Q3Tab

open Lax496464Proofs.Ram.Q3Defs

theorem getD_init {bt w1 INF : ℕ} {T : List ℕ}
    (hT : T = (List.replicate (bt * w1) INF).set 0 0) {i : ℕ} (hi : i < bt * w1) :
    T.getD i 0 = if i = 0 then 0 else INF := by
  subst hT
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = 0
  · subst h
    simp [hi]
  · have h' : ¬ (0 = i) := fun e => h e.symm
    simp [h, h', hi]

theorem tab_init {bt w1 INF : ℕ} {T : List ℕ} (hT : T = (List.replicate (bt * w1) INF).set 0 0) :
    TabSem bt w1 INF R0 T := by
  intro x hx c hc
  have hi : x * w1 + c < bt * w1 := by
    have : (x + 1) * w1 ≤ bt * w1 := Nat.mul_le_mul_right _ hx
    nlinarith
  have hw : 0 < w1 := by omega
  have hcell : cell w1 T x c = if x * w1 + c = 0 then 0 else INF := getD_init hT hi
  have hiff : x * w1 + c = 0 ↔ x = 0 ∧ c = 0 := by
    constructor
    · intro h
      have hc0 : c = 0 := by omega
      have : x * w1 = 0 := by omega
      rcases Nat.mul_eq_zero.1 this with h1 | h1
      · exact ⟨h1, hc0⟩
      · omega
    · rintro ⟨rfl, rfl⟩; simp
  by_cases h : x * w1 + c = 0
  · rw [hcell, if_pos h]
    refine ⟨by omega, fun P _ => ?_⟩
    have := hiff.1 h
    simp [R0, this]
  · rw [hcell, if_neg h]
    refine ⟨le_refl _, fun P hP => ?_⟩
    have : ¬ (x = 0 ∧ c = 0) := fun e => h (hiff.2 e)
    simp only [R0, this, iff_false, not_le]
    exact hP

theorem tab_step {bt w1 bb m qm INF pwd pwq pj qj dj wj : ℕ} {R : ℕ → ℕ → ℕ → Prop} {T S T' G : List ℕ}
    (hdj : dj < INF) (hG : ∀ x < bt, G.getD x 0 = digsum bb qm x)
    (hT : TabSem bt w1 INF R T) (hS : MargOK bt w1 pwd INF T S)
    (hT' : TakeOK bt w1 bb m INF pwq pj qj dj wj G S T') :
    TabSem bt w1 INF (Step bt bb m qm pwd pwq pj qj dj wj R) T' := by
  intro x hx c hc
  obtain ⟨hle, hiff⟩ := hT' x hx c hc
  refine ⟨hle, fun P hP => ?_⟩
  rw [hiff P]
  unfold Step
  have hb : x - pwq < bt := lt_of_le_of_lt (Nat.sub_le _ _) hx
  have hc' : c - wj < w1 := lt_of_le_of_lt (Nat.sub_le _ _) hc
  have hfirst : cell w1 S x c ≤ P ↔ ∃ y < bt, y / pwd = x ∧ R y c P := by
    rw [(hS x hx c hc).2 P]
    have hnot : ¬ INF ≤ P := by omega
    simp only [hnot, false_or]
    constructor
    · rintro ⟨y, hy, hyd, hcy⟩
      exact ⟨y, hy, hyd, ((hT y hy c hc).2 P hP).1 hcy⟩
    · rintro ⟨y, hy, hyd, hR⟩
      exact ⟨y, hy, hyd, ((hT y hy c hc).2 P hP).2 hR⟩
  have hsecond : (1 ≤ x / pwq % bb ∧ G.getD x 0 ≤ m ∧
        cell w1 S (x - pwq) (c - wj) + pj + qj ≤ dj ∧ cell w1 S (x - pwq) (c - wj) + pj ≤ P) ↔
      (1 ≤ x / pwq % bb ∧ digsum bb qm x ≤ m ∧
        ∃ y < bt, y / pwd = x - pwq ∧ ∃ P'', R y (c - wj) P'' ∧ P'' + pj + qj ≤ dj ∧
          P'' + pj ≤ P) := by
    rw [hG x hx]
    refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
    constructor
    · rintro ⟨h1, h2⟩
      set v := cell w1 S (x - pwq) (c - wj) with hv
      have hvI : v < INF := by omega
      have := ((hS (x - pwq) hb (c - wj) hc').2 v).1 (le_refl _)
      rcases this with h | ⟨y, hy, hyd, hcy⟩
      · omega
      · exact ⟨y, hy, hyd, v, ((hT y hy (c - wj) hc').2 v hvI).1 hcy, h1, h2⟩
    · rintro ⟨y, hy, hyd, P'', hR, h1, h2⟩
      have hPI : P'' < INF := by omega
      have hcy : cell w1 T y (c - wj) ≤ P'' := ((hT y hy (c - wj) hc').2 P'' hPI).2 hR
      have hv : cell w1 S (x - pwq) (c - wj) ≤ P'' :=
        ((hS (x - pwq) hb (c - wj) hc').2 P'').2 (Or.inr ⟨y, hy, hyd, hcy⟩)
      omega
  rw [hfirst, hsecond]

theorem tab_final {bt w1 INF W : ℕ} (hw : w1 = W + 1) (hINF : 0 < INF) {R : ℕ → ℕ → ℕ → Prop} {T : List ℕ}
    (hT : TabSem bt w1 INF R T) :
    (∃ x < bt, cell w1 T x W < INF) ↔ ∃ x < bt, R x W (INF - 1) := by
  have hW : W < w1 := by omega
  have hI : INF - 1 < INF := by omega
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, ((hT x hx W hW).2 (INF - 1) hI).1 (by omega)⟩
  · rintro ⟨x, hx, h⟩
    have := ((hT x hx W hW).2 (INF - 1) hI).2 h
    exact ⟨x, hx, by omega⟩

end Lax496464Proofs.Ram.Q3Tab
