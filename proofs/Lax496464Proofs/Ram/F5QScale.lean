import Lax496464Proofs.Ram.F5QFit

/-!
# Theorem 5 (Profile Sweep): the Scale Factor, the Rescaling Pass and the Threshold
-/

namespace Lax496464Proofs.Ram.F5QScale

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.F5QFit (getq_set V)

/-! ## `kCom`: `kk := max 1 (wm / (W * n))` -/

def kCom : Com :=
  .seq (.assign "u1" (.bin .mul (V "W") (V "n")))
    (.seq (.assign "u2" (.bin .div (V "wm") (V "u1")))
      (.seq (.assign "kk" (V "u2")) (.ite (.lt (V "kk") (.lit 1)) (.assign "kk" (.lit 1)) .skip)))

theorem kCom_spec {B e n wmv : ℕ} (hB : 1 < B) (heB : e < B) (hnB : n < B) (hen : e * n < B) (hwm : wmv < B) :
    Spec B (fun σ => σ.vars "W" = e ∧ σ.vars "n" = n ∧ σ.vars "wm" = wmv) kCom
      (fun _ σ' => σ'.vars "kk" = max 1 (wmv / (e * n))) 20 := by
  intro σ ⟨hW, hn, hw⟩
  have hd : wmv / (e * n) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hwm
  have hkey : ((e = 0 ∨ n = 0) ∨ wmv < e * n) → wmv / (e * n) ≤ 1 := by
    rintro ((h | h) | h)
    · subst h; simp
    · subst h; simp
    · rw [Nat.div_eq_of_lt h]; omega
  have hkey2 : ((¬e = 0 ∧ ¬n = 0) ∧ e * n ≤ wmv) → 1 ≤ wmv / (e * n) := by
    rintro ⟨⟨h1, h2⟩, h3⟩
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.pos_of_ne_zero h1) (Nat.pos_of_ne_zero h2))).mpr
      (by omega)
  unfold kCom
  run_vcg
  all_goals simp [Env.setVar, hW, hn, hw] at *
  all_goals omega

/-! ## `wCom`: `W := 2 * W * n * n` -/

def wCom : Com :=
  .assign "W" (.bin .mul (.bin .mul (.bin .mul (.lit 2) (V "W")) (V "n")) (V "n"))

theorem wCom_spec {B e n : ℕ} (_hB : 1 < B) (heB : e < B) (hnB : n < B) (h2 : 2 < B) (h1 : 2 * e < B) (h3 : 2 * e * n < B)
    (h4 : 2 * e * n * n < B) :
    Spec B (fun σ => σ.vars "W" = e ∧ σ.vars "n" = n) wCom
      (fun _ σ' => σ'.vars "W" = 2 * e * n * n ∧ σ'.vars "n" = n) 10 := by
  intro σ ⟨hW, hn⟩
  unfold wCom
  run_vcg
  all_goals simp [Env.setVar, hW, hn] at *
  all_goals omega

/-! ## `rescaleCom` -/

def rescaleBody : Com :=
  .seq (.assign "u1" (.get "WS" (V "i")))
    (.seq (.ite (.lt (.lit 0) (V "u1"))
        (.store "WS" (V "i") (.bin .add (.bin .div (.bin .sub (V "u1") (.lit 1)) (V "kk")) (.lit 1)))
        .skip)
      (.assign "i" (.bin .add (V "i") (.lit 1))))

def rescaleCom : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) rescaleBody)

/-- The rescaled weight. -/
def rescVal (kk w : ℕ) : ℕ := if 0 < w then (w - 1) / kk + 1 else 0

def rescArr (kk : ℕ) (Wl : List ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map (fun k => rescVal kk (Wl.getD k 0))

def RInv (kk : ℕ) (Wl : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "kk" = kk ∧ σ.vars "i" ≤ n ∧ (σ.arrs "WS").length = n ∧
  ∀ j, (σ.arrs "WS").getD j 0 = if j < σ.vars "i" then rescVal kk (Wl.getD j 0) else Wl.getD j 0

theorem rescVal_le {kk w : ℕ} (_hk : 1 ≤ kk) : rescVal kk w ≤ w := by
  unfold rescVal
  split_ifs with h
  · have : (w - 1) / kk ≤ w - 1 := Nat.div_le_self _ _
    omega
  · omega

theorem rescaleBody_spec {B n kk : ℕ} (Wl : List ℕ) (hB : 1 < B) (hk : 1 ≤ kk) (_hW : Wl.length = n)
    (hnB : n < B) (hkB : kk < B) (hwB : ∀ k < n, Wl.getD k 0 < B) :
    Spec B (fun σ => RInv kk Wl n σ ∧ σ.vars "i" < n) rescaleBody
      (fun σ σ' => RInv kk Wl n σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  intro σ ⟨⟨hn, hkk, hi, hWl, hWg⟩, hlt⟩
  have hiB : σ.vars "i" + 1 < B := by omega
  have hg := hWg (σ.vars "i")
  have hwB' := hwB _ hlt
  have hWlen : σ.vars "i" < (σ.arrs "WS").length := by omega
  have hrv : rescVal kk (Wl.getD (σ.vars "i") 0) ≤ Wl.getD (σ.vars "i") 0 := rescVal_le hk
  have hdiv : (Wl.getD (σ.vars "i") 0 - 1) / kk ≤ Wl.getD (σ.vars "i") 0 - 1 := Nat.div_le_self _ _
  have hWget : (σ.arrs "WS").getD (σ.vars "i") 0 = Wl.getD (σ.vars "i") 0 := by
    rw [hg, if_neg (by omega)]
  run_vcg
  all_goals simp only [RInv, Env.setVar, Env.setArr] at *
  all_goals simp [getq_set _ _ _ _ hWlen] at *
  all_goals first
    | omega
    | (rw [hkk, hg]; omega)
    | skip
  · have hpos : 0 < Wl[σ.vars "i"]?.getD 0 := by omega
    refine ⟨hn, hkk, by omega, hWl, ?_⟩
    intro j
    by_cases hj : j = σ.vars "i"
    · rw [hj, if_pos rfl, if_pos le_rfl]
      unfold rescVal
      rw [if_pos hpos, hg, hkk]
    · rw [if_neg hj, hWg j]
      by_cases hjl : j < σ.vars "i"
      · rw [if_pos hjl, if_pos (by omega)]
      · rw [if_neg hjl, if_neg (by omega)]
  · have h0 : Wl[σ.vars "i"]?.getD 0 = 0 := by omega
    refine ⟨hn, hkk, by omega, hWl, ?_⟩
    intro j
    rw [hWg j]
    by_cases hj : j = σ.vars "i"
    · rw [hj, if_neg (lt_irrefl _), if_pos le_rfl, h0]
      simp [rescVal]
    · by_cases hjl : j < σ.vars "i"
      · rw [if_pos hjl, if_pos (by omega)]
      · rw [if_neg hjl, if_neg (by omega)]

/-- **The rescaling pass.** -/
theorem rescaleCom_spec {B n kk : ℕ} (Wl : List ℕ) (hB : 1 < B) (hk : 1 ≤ kk) (hW : Wl.length = n)
    (hnB : n < B) (hkB : kk < B) (hwB : ∀ k < n, Wl.getD k 0 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "kk" = kk ∧ σ.arrs "WS" = Wl) rescaleCom
      (fun _ σ' => σ'.arrs "WS" = rescArr kk Wl n) (44 * n + 10) := by
  have hloop := Spec.forRangeZero (B := B) (c := rescaleBody) "i" "n" (RInv kk Wl n) n 40 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.1) (rescaleBody_spec Wl hB hk hW hnB hkB hwB)
  refine Spec.of_exists fun σ ⟨hn, hkk, hWs⟩ => ?_
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ) (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar, hn]
    · simp [Env.setVar, hkk]
    · simp [Env.setVar]
    · simp [Env.setVar, hWs, hW]
    · intro j; simp [Env.setVar, hWs])
  refine ⟨σ2, _, hr2.mono ?_, le_rfl, ?_⟩
  · omega
  · obtain ⟨-, -, -, hl, hg⟩ := hI
    rw [hi] at hg
    apply List.ext_getElem
    · simp [hl, rescArr]
    · intro j h1 h2
      have := hg j
      rw [List.getD_eq_getElem _ _ h1, if_pos (by simp [rescArr] at h2; omega)] at this
      rw [this]
      simp [rescArr]

end Lax496464Proofs.Ram.F5QScale
