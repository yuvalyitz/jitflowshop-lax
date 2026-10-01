import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PLayout
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds

/-!
# The value bound and the cost bound

With `T = c₀ · (|x| + 1) · (k + 1)` and `G = T^E₀` (constants fixed by the formula): every constant
of the formula (`W`, `C`, `P`, `Q`, …) is at most `G`, the largest constant `big` is at most `20·G⁴`
(`big_le`), and the cost of the program is at most `Kc · G⁵` (`Kprog_le`). The value bound is the
one of `Lemmas/WDToWSat` plus `big`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PBounds

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (BF)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill (capW)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom (Krel)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PEval Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseX
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseM Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PMain

variable (Dt : Data) (x : List ℕ)

/-! ### The scale -/

/-- The constant factor of the scale. -/
def c0 : ℕ := Dt.s + Dt.r + Dt.D + 4

/-- The scale `T`. -/
def Tb : ℕ := c0 Dt * ((x.length + 1) * (kW x + 1))

/-- The exponent. -/
def E0 : ℕ := (Dt.s + 1) * (Dt.D + 1) + Dt.p + Dt.q + 2

/-- **The unit `G`.** -/
def G : ℕ := Tb Dt x ^ E0 Dt

theorem nU_le : nU Dt x ≤ 2 * x.length + Dt.s * kW x + Dt.r :=
  Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds.nW_le (wd Dt) x

theorem capW_le : capW (wd Dt) x ≤ 2 * x.length + Dt.s * kW x + Dt.r := by
  have := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds.LW_le' (wd Dt) x
  unfold capW; simp only [wd] at this ⊢; omega

theorem lin_le_T {a : ℕ} (ha : a ≤ 2 * x.length + Dt.s * kW x + Dt.r + Dt.D + 2) : a ≤ Tb Dt x := by
  unfold Tb c0
  have h1 : 1 ≤ kW x + 1 := by omega
  have h2 : x.length + 1 ≤ (x.length + 1) * (kW x + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : kW x + 1 ≤ (x.length + 1) * (kW x + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : Dt.s * kW x ≤ Dt.s * ((x.length + 1) * (kW x + 1)) := Nat.mul_le_mul_left _ (by omega)
  have h5 : 1 ≤ (x.length + 1) * (kW x + 1) := by omega
  nlinarith

theorem T_ge : 4 ≤ Tb Dt x ∧ x.length + 1 ≤ Tb Dt x ∧ kW x + 2 ≤ Tb Dt x ∧ Dt.D ≤ Tb Dt x ∧
    nU Dt x + 2 ≤ Tb Dt x ∧ capW (wd Dt) x ≤ Tb Dt x ∧ Dt.r ≤ Tb Dt x := by
  have hn := nU_le Dt x
  have hc := capW_le Dt x
  have h4 : 4 ≤ Tb Dt x := by
    unfold Tb c0
    have : 1 ≤ (x.length + 1) * (kW x + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hk : kW x + 2 ≤ Tb Dt x := by
    unfold Tb c0
    have h3 : kW x + 1 ≤ (x.length + 1) * (kW x + 1) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  exact ⟨h4, lin_le_T Dt x (by omega), hk, lin_le_T Dt x (by omega), lin_le_T Dt x (by omega),
    lin_le_T Dt x (by omega), lin_le_T Dt x (by omega)⟩

theorem T_pow_le {e : ℕ} (he : e ≤ E0 Dt) : Tb Dt x ^ e ≤ G Dt x :=
  Nat.pow_le_pow_right (by have := (T_ge Dt x).1; omega) he

theorem G_ge_one : 1 ≤ G Dt x := Nat.one_le_pow _ _ (by have := (T_ge Dt x).1; omega)

theorem T_le_G : Tb Dt x ≤ G Dt x := by
  have := T_pow_le Dt x (e := 1) (by unfold E0; omega); simpa using this

theorem N2_le : nU Dt x ^ Dt.s + 2 ≤ Tb Dt x ^ (Dt.s + 1) := by
  have hT := T_ge Dt x
  have h1 : nU Dt x ^ Dt.s ≤ Tb Dt x ^ Dt.s := Nat.pow_le_pow_left (by omega) _
  have h2 : 1 ≤ Tb Dt x ^ Dt.s := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

theorem units_le : (par Dt x).W ≤ G Dt x ∧ (kW x + 2) ^ Dt.D ≤ G Dt x ∧ (par Dt x).C ≤ G Dt x ∧
    (nU Dt x ^ Dt.s + 2) ^ Dt.D ≤ G Dt x ∧ (par Dt x).P ≤ G Dt x ∧ (par Dt x).Q ≤ G Dt x ∧
    nU Dt x ^ Dt.s ≤ G Dt x := by
  have hT := T_ge Dt x
  have hN := N2_le Dt x
  have hkD : (kW x + 2) ^ Dt.D ≤ G Dt x :=
    (Nat.pow_le_pow_left hT.2.2.1 _).trans (T_pow_le Dt x (by unfold E0; nlinarith))
  have hND : (nU Dt x ^ Dt.s + 2) ^ Dt.D ≤ G Dt x := by
    calc (nU Dt x ^ Dt.s + 2) ^ Dt.D ≤ (Tb Dt x ^ (Dt.s + 1)) ^ Dt.D := Nat.pow_le_pow_left hN _
      _ = Tb Dt x ^ ((Dt.s + 1) * Dt.D) := by rw [← pow_mul]
      _ ≤ G Dt x := T_pow_le Dt x (by unfold E0; nlinarith)
  refine ⟨?_, hkD, ?_, hND, ?_, ?_, ?_⟩
  · show (kW x + 1) ^ Dt.D ≤ _
    exact (Nat.pow_le_pow_left (by omega) _).trans hkD
  · show (nU Dt x ^ Dt.s + 1) ^ Dt.D ≤ _
    exact (Nat.pow_le_pow_left (by omega) _).trans hND
  · exact (Nat.pow_le_pow_left (by omega) _).trans (T_pow_le Dt x (by unfold E0; omega))
  · exact (Nat.pow_le_pow_left (by omega) _).trans (T_pow_le Dt x (by unfold E0; omega))
  · have : nU Dt x ^ Dt.s ≤ Tb Dt x ^ (Dt.s + 1) := by omega
    exact this.trans (T_pow_le Dt x (by unfold E0; nlinarith))

theorem big_le : big Dt x ≤ 30 * G Dt x ^ 4 := by
  obtain ⟨hW, hkD, hC, hND, hP, hQ, hN⟩ := units_le Dt x
  have hT := T_ge Dt x
  have hTG := T_le_G Dt x
  have hG := G_ge_one Dt x
  set g := G Dt x
  have hk : kW x ≤ g := by omega
  have hD2 : Dt.D * Dt.D ≤ g * g := Nat.mul_le_mul (by omega) (by omega)
  have hr : Dt.r ≤ g := by omega
  have g2 : g ≤ g ^ 2 := by nlinarith
  have g3 : g ^ 2 ≤ g ^ 3 := by nlinarith
  have g4 : g ^ 3 ≤ g ^ 4 := by nlinarith
  have hWC : (par Dt x).W * (par Dt x).C ≤ g ^ 2 := by
    calc (par Dt x).W * (par Dt x).C ≤ g * g := Nat.mul_le_mul hW hC
      _ = g ^ 2 := by ring
  have hWCW : (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C ≤ g ^ 4 := by
    calc (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C
        = ((par Dt x).W * (par Dt x).C) * ((par Dt x).W * (par Dt x).C) := by ring
      _ ≤ g ^ 2 * g ^ 2 := Nat.mul_le_mul hWC hWC
      _ = g ^ 4 := by ring
  have hWCQ : (par Dt x).W * (par Dt x).C * (par Dt x).Q ≤ g ^ 3 := by
    calc (par Dt x).W * (par Dt x).C * (par Dt x).Q ≤ g ^ 2 * g := Nat.mul_le_mul hWC hQ
      _ = g ^ 3 := by ring
  unfold big
  nlinarith

/-! ### The cost -/

/-- The cost factor of the evaluation. -/
def cev (D : ℕ) : Formula → ℕ
  | .rel _ js => 20 * js.length + 49
  | .eq _ _ => 12
  | .setVar js => 7 * js.length + 2 + Kdec D
  | .neg φ => cev D φ + 6
  | .and φ ψ => cev D φ + cev D ψ + 6
  | .or φ ψ => cev D φ + cev D ψ + 6
  | .ex _ _ => 2
  | .all _ _ => 2

theorem Kev_le : ∀ ψ : Formula, Kev Dt x ψ ≤ cev Dt.D ψ * (x.length + 1)
  | .rel _ js => by simp only [Kev, cev, Krel]; nlinarith
  | .eq _ _ => by simp only [Kev, cev]; nlinarith
  | .setVar js => by simp only [Kev, cev]; nlinarith
  | .neg φ => by have := Kev_le φ; simp only [Kev, cev]; nlinarith
  | .and φ ψ => by have := Kev_le φ; have := Kev_le ψ; simp only [Kev, cev]; nlinarith
  | .or φ ψ => by have := Kev_le φ; have := Kev_le ψ; simp only [Kev, cev]; nlinarith
  | .ex _ _ => by simp only [Kev, cev]; nlinarith
  | .all _ _ => by simp only [Kev, cev]; nlinarith

/-- A loop step: `c + ((X + 8) · C + 6) ≤ (c + a + 14) · G^(i+1)` for `X ≤ a · G^i`, `C ≤ G`. -/
theorem step {X C a g i c : ℕ} (hX : X ≤ a * g ^ i) (hC : C ≤ g) (hg : 1 ≤ g) :
    c + ((X + 8) * C + 6) ≤ (c + a + 14) * g ^ (i + 1) := by
  have h1 : 1 ≤ g ^ i := Nat.one_le_pow _ _ hg
  have h2 : g ^ (i + 1) = g ^ i * g := pow_succ _ _
  have h3 : (X + 8) * C ≤ (a * g ^ i + 8) * g := Nat.mul_le_mul (by omega) hC
  have h4 : 1 ≤ g ^ (i + 1) := Nat.one_le_pow _ _ hg
  nlinarith

/-- The constants of the cost bound. -/
def a2 (D : ℕ) : ℕ := 20 * D + 3 + (100 * (D * D) + 20) + 2 + 12 + 1 + 76
def a6 (D : ℕ) : ℕ := 3 * (20 * D + 9) + a2 D + 3 * 14 + 14
def b1 (Dt : Data) : ℕ := 20 * Dt.q + 36 + cev Dt.D Dt.ψ
def b5 (Dt : Data) : ℕ := 2 * (20 * Dt.D + 9) + (20 * Dt.p + 12) + b1 Dt + 4 * 14

/-- **The cost constant.** -/
def Kc (Dt : Data) : ℕ :=
  1000 + 16 + 12 * (wd Dt).rels.length + 34 + 14 + 16 + 74 + 6 * Dt.s + 6 * Dt.p + 6 * Dt.q +
    8 * Dt.D + 18 + a6 Dt.D + b5 Dt

set_option maxHeartbeats 4000000 in
/-- **The cost bound.** -/
theorem Kprog_le (hg : Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath.Good x) :
    Kprog Dt x ≤ Kc Dt * G Dt x ^ 5 := by
  obtain ⟨hW, -, hC, -, hP, hQ, -⟩ := units_le Dt x
  have hT := T_ge Dt x
  have hTG := T_le_G Dt x
  have hG := G_ge_one Dt x
  set g := G Dt x with hgdef
  have hX : x.length + 1 ≤ g := by omega
  -- phase X
  have k2 : Kx2 Dt x ≤ a2 Dt.D * g := by
    unfold Kx2 Kcf a2
    have : 1 ≤ g := hG
    nlinarith
  have k3 : Kxb2 Dt x ≤ (20 * Dt.D + 3 + a2 Dt.D + 14) * g ^ (1 + 1) :=
    step (c := 20 * Dt.D + 3) (i := 1) (by simpa using k2) hC hG
  have k4 : Kxv1 Dt x ≤ (20 * Dt.D + 3 + (20 * Dt.D + 3 + a2 Dt.D + 14) + 14) * g ^ (1 + 1 + 1) :=
    step (c := 20 * Dt.D + 3) k3 hW hG
  have k5 : Kxb1 Dt x ≤ (20 * Dt.D + 3 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + a2 Dt.D + 14) + 14) + 14) *
      g ^ (1 + 1 + 1 + 1) :=
    step (c := 20 * Dt.D + 3) k4 hC hG
  have k6 : KX Dt x ≤ (0 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + a2 Dt.D + 14) + 14) +
      14) + 14) * g ^ (1 + 1 + 1 + 1 + 1) := by
    have := step (c := 0) k5 hW hG
    unfold KX; simpa using this
  have hKX : KX Dt x ≤ a6 Dt.D * g ^ 5 := by
    have : 0 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + a2 Dt.D + 14) + 14) + 14) + 14 ≤
        a6 Dt.D := by unfold a6; omega
    exact k6.trans (Nat.mul_le_mul this le_rfl)
  -- phase M
  have m1 : Kmzb Dt x ≤ b1 Dt * g := by
    have := Kev_le Dt x Dt.ψ
    have h2 : cev Dt.D Dt.ψ * (x.length + 1) ≤ cev Dt.D Dt.ψ * g := Nat.mul_le_mul_left _ hX
    unfold Kmzb b1
    nlinarith
  have m2 : Kmv Dt x ≤ (20 * Dt.D + 3 + b1 Dt + 14) * g ^ (1 + 1) :=
    step (c := 20 * Dt.D + 3) (i := 1) (by simpa using m1) hQ hG
  have m3 : Kmb Dt x ≤ (20 * Dt.D + 3 + (20 * Dt.D + 3 + b1 Dt + 14) + 14) * g ^ (1 + 1 + 1) :=
    step (c := 20 * Dt.D + 3) m2 hC hG
  have m4 : Kmza Dt x ≤ (20 * Dt.p + 5 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + b1 Dt + 14) + 14) + 14 + 1)
      * g ^ (1 + 1 + 1 + 1) := by
    have := step (c := 20 * Dt.p + 5) m3 hW hG
    have h1 : 1 ≤ g ^ (1 + 1 + 1 + 1) := Nat.one_le_pow _ _ hG
    have e : Kmza Dt x = 20 * Dt.p + 5 + ((Kmb Dt x + 8) * (par Dt x).W + 6) + 1 := by
      unfold Kmza; omega
    rw [e]; nlinarith
  have m5 : KM Dt x ≤ (0 + (20 * Dt.p + 5 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + b1 Dt + 14) + 14) + 14 +
      1) + 14) * g ^ (1 + 1 + 1 + 1 + 1) := by
    have := step (c := 0) m4 hP hG
    unfold KM; simpa using this
  have hKM : KM Dt x ≤ b5 Dt * g ^ 5 := by
    have : 0 + (20 * Dt.p + 5 + (20 * Dt.D + 3 + (20 * Dt.D + 3 + b1 Dt + 14) + 14) + 14 + 1) + 14
        ≤ b5 Dt := by unfold b5; omega
    exact m5.trans (Nat.mul_le_mul this le_rfl)
  -- the rest
  have g1 : g ≤ g ^ 5 := by
    have := Nat.pow_le_pow_right hG (show 1 ≤ 5 by omega); simpa using this
  have g2 : g ^ 2 ≤ g ^ 5 := Nat.pow_le_pow_right hG (by omega)
  have hsp : spW x ≤ g := by have := hg.head; omega
  have hcapT := hT.2.2.2.2.2.1
  have hcapE : capW (wd Dt) x = LW Dt.s Dt.r x + x.length := rfl
  have hL : LW Dt.s Dt.r x ≤ g := by omega
  have hcap : capW (wd Dt) x ≤ g := by omega
  have hcx : (16 * capW (wd Dt) x + 70 + 4) * x.length ≤ 90 * g ^ 2 := by
    have : (16 * capW (wd Dt) x + 70 + 4) * x.length ≤ (16 * g + 74) * g :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hCW : (((10 + 8) * (par Dt x).C + 6 + 2 + 8) + 8) * (par Dt x).W ≤ 42 * g ^ 2 := by
    have : (((10 + 8) * (par Dt x).C + 6 + 2 + 8) + 8) * (par Dt x).W ≤ (18 * g + 24) * g :=
      Nat.mul_le_mul (by omega) hW
    nlinarith
  have h1 : 1 ≤ g ^ 5 := Nat.one_le_pow _ _ hG
  unfold Kprog Kmain Kc
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PBounds
