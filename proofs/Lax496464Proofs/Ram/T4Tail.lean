import Lax496464Proofs.Ram.T4Setup
import Lax496464Proofs.Ram.T4Front
import Lax496464Proofs.Ram.Corollary1Init
import Lax496464Proofs.Section6

/-!
# Theorem 4's machine, part 7: everything after the sorted arrays exist
-/

namespace Lax496464Proofs.Ram.T4Tail

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Greedy Lax496464.EstOrder
open Lax496464Proofs.Ram.SegProg (V bump)
open Lax496464Proofs.Ram.T4Trees Lax496464Proofs.Ram.T4Defs Lax496464Proofs.Ram.T4Model
open Lax496464Proofs.Ram.T4Expire Lax496464Proofs.Ram.T4Step Lax496464Proofs.Ram.T4Job
open Lax496464Proofs.Ram.T4Setup
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.Corollary1Init (maxScan maxScan_spec foldr_max_lt)

/-- The scalars the greedy starts from: nothing counted, nothing running, the common
preprocessing time in `p0`. -/
def initScalars : Com :=
  .seq (.assign "sz" (.lit 0)) (.seq (.assign "run" (.lit 0))
    (.ite (.lt (.lit 0) (V "n")) (.assign "p0" (.get "PS" (.lit 0))) (.assign "p0" (.lit 0))))

theorem initScalars_spec {B : ℕ} (n0 p : ℕ) (hB : 1 < B) (hpB : p < B) (hn0B : n0 < B) :
    Spec B (fun σ => σ.vars "n" = n0 ∧ (0 < n0 → (σ.arrs "PS").getD 0 0 = p ∧
        0 < (σ.arrs "PS").length)) initScalars
      (fun σ σ' => σ'.vars "sz" = 0 ∧ σ'.vars "run" = 0 ∧ (0 < n0 → σ'.vars "p0" = p) ∧
        (n0 = 0 → σ'.vars "p0" = 0) ∧
        (∀ y, y ≠ "sz" → y ≠ "run" → y ≠ "p0" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs) 20 := by
  refine Spec.of_exists fun σ ⟨hn, hp⟩ => ?_
  run_vcg
  all_goals (simp_all)
  all_goals (try (intro h; omega))

/-- Write `1` when the count reaches the threshold, else `0`. -/
def finalOut : Com :=
  .seq (.ite (.lt (V "sz") (V "W")) (.assign "ans" (.lit 0)) (.assign "ans" (.lit 1)))
    (.write (V "ans"))

theorem finalOut_spec {B : ℕ} (sz W : ℕ) (hB : 1 < B) (hszB : sz < B) (hWB : W < B) :
    Spec B (fun σ => σ.vars "sz" = sz ∧ σ.vars "W" = W ∧ σ.out = []) finalOut
      (fun _ σ' => σ'.out = [if W ≤ sz then 1 else 0]) 20 := by
  refine Spec.of_exists fun σ ⟨hsz, hW, ho⟩ => ?_
  run_vcg
  all_goals (simp_all)

theorem le_foldr_max' (l : List ℕ) (v : ℕ) (hv : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hv
  | cons a t ih =>
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp only [List.foldr_cons]; omega
    · simp only [List.foldr_cons]; exact le_trans (ih hv') (le_max_right _ _)

/-- The value bound for the sentinel: `BIG = max d + 2`. -/
def bigOf (J : Instance) : ℕ := ((List.range J.jobs).map (dv J)).foldr max 0 + 2

theorem dv_mem {J : Instance} (i : J.Job) : J.d i ∈ (List.range J.jobs).map (dv J) :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, by simp [dv, i.isLt]⟩

theorem mem_dv {J : Instance} {v : ℕ} (hv : v ∈ (List.range J.jobs).map (dv J)) :
    ∃ i : J.Job, v = J.d i := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  have hk' := List.mem_range.mp hk
  exact ⟨⟨k, hk'⟩, by simp [dv, hk']⟩

theorem num2_of {J : Instance} {p B : ℕ} (hnB : 4 * J.jobs + 8 < B) (hpB : p < B)
    (hmB : J.machines < B) (hd2 : ∀ j : J.Job, J.d j + 2 < B)
    (hdd : ∀ a b : J.Job, J.d a + J.d b + 3 < B) (hdq : ∀ a b : J.Job, J.d a + J.q b + 2 < B) :
    Num2 J B (J.jobs - 1).size (bigOf J) p := by
  have h2 := two_pow_size_le J.jobs
  have hcap : J.jobs ≤ 2 ^ (J.jobs - 1).size := by
    have := Nat.lt_size_self (J.jobs - 1); omega
  refine ⟨⟨by omega, hcap, ?_, ?_, ?_, ?_⟩, hpB, hmB⟩
  · intro i
    have := le_foldr_max' _ _ (dv_mem i)
    unfold bigOf; omega
  · intro i
    have := foldr_max_lt (l := (List.range J.jobs).map (dv J)) (B := B) (c := J.q i + 2)
      (fun v hv => by obtain ⟨a, rfl⟩ := mem_dv hv; have := hdq a i; omega)
      (by have := hdq i i; omega)
    unfold bigOf; omega
  · intro i
    have := foldr_max_lt (l := (List.range J.jobs).map (dv J)) (B := B) (c := J.d i + 3)
      (fun v hv => by obtain ⟨a, rfl⟩ := mem_dv hv; have := hdd a i; omega)
      (by have := hdd i i; omega)
    unfold bigOf; omega
  · have := foldr_max_lt (l := (List.range J.jobs).map (dv J)) (B := B) (c := 2)
      (fun v hv => by obtain ⟨a, rfl⟩ := mem_dv hv; have := hd2 a; omega) (by omega)
    unfold bigOf; omega

theorem treeOK_zero {a : String} {h B : ℕ} {σ : Env} (hB : 0 < B)
    (hA : σ.arrs a = List.replicate (2 * 2 ^ h) 0) {f : ℕ → ℕ} (hf : ∀ ℓ, f ℓ = 0) :
    TreeOK a h f B σ := by
  refine ⟨⟨by rw [hA]; simp, fun i _ _ => ?_⟩, fun ℓ _ => ?_, fun x hx => ?_⟩
  · rw [hA]; simp
  · rw [hA, hf]; simp
  · rw [hA] at hx; simp at hx; omega

/-- **The greedy's count is the answer.** -/
theorem hasWeight_iff_card {J : Instance} {p W : ℕ} (hest : EstOrdered J)
    (hq : ∀ j : J.Job, 0 < J.q j) (hw1 : ∀ j : J.Job, J.w j = 1) (hp : ∀ j : J.Job, J.p j = p)
    (S : ℕ → Finset J.Job) (h0 : S 0 = ∅)
    (hrun : ∀ i (hi : i < J.jobs), Step J p (S i) (S (i + 1)) ⟨i, hi⟩) :
    HasWeight J W ↔ W ≤ (S J.jobs).card := by
  obtain ⟨hfeas, hmax⟩ := Lax496464Proofs.Section6.greedy_card_max J hest hp hq S h0 hrun
  have hwt : ∀ Z : Finset J.Job, weight J Z = Z.card := fun Z => by
    simp [weight, hw1]
  constructor
  · rintro ⟨Z, hZ, hW⟩
    rw [hwt] at hW
    exact hW.trans (hmax Z hZ)
  · intro h
    exact ⟨S J.jobs, hfeas, by rw [hwt]; exact h⟩

/-- Everything after the sorted arrays. -/
def tail4 : Com :=
  .seq maxScan (.seq sizeLoop (.seq initScalars (.seq mainLoop finalOut)))

/-- The cost of `tail4`. -/
def tailK (n : ℕ) : ℕ :=
  (2 + (2 + ((50 + 4) * n + 6) + 4 + 4)) + (12 * (n - 1).size + 8) + 20 +
    ((Kbody (n - 1).size + 4) * n + 6) + 20

open Classical in
/-- **The tail computes the answer.** -/
theorem tail4_spec {J : Instance} {p W B : ℕ} (hest : EstOrdered J)
    (hq : ∀ j : J.Job, 0 < J.q j) (hw1 : ∀ j : J.Job, J.w j = 1) (hp : ∀ j : J.Job, J.p j = p)
    (hp0 : J.jobs = 0 → p = 0) (hB2 : 2 < B) (hnB : 4 * J.jobs + 8 < B) (hpB : p < B)
    (hmB : J.machines < B) (hWB : W < B) (hd2 : ∀ j : J.Job, J.d j + 2 < B)
    (hdd : ∀ a b : J.Job, J.d a + J.d b + 3 < B) (hdq : ∀ a b : J.Job, J.d a + J.q b + 2 < B) :
    Spec B (fun σ => σ.arrs "PS" = (List.range J.jobs).map (pv J) ∧
        σ.arrs "QS" = (List.range J.jobs).map (qv J) ∧
        σ.arrs "DS" = (List.range J.jobs).map (dv J) ∧ σ.vars "n" = J.jobs ∧
        σ.vars "m" = J.machines ∧ σ.vars "sn" = J.jobs ∧ σ.vars "W" = W ∧ σ.out = [] ∧
        σ.arrs "TX" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 ∧
        σ.arrs "TY" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0) tail4
      (fun _ σ' => σ'.out = [if HasWeight J W then 1 else 0]) (tailK J.jobs) := by
  refine Spec.of_exists fun σ0 hσ0 => ?_
  obtain ⟨hPS, hQS, hDS, hn, hm, hsn, hW, hout, hTX, hTY⟩ := hσ0
  have hN2 := num2_of hnB hpB hmB hd2 hdd hdq
  have hB1 : 1 < B := by omega
  have hDSl : ((List.range J.jobs).map (dv J)).length = J.jobs := by simp
  have hDSB : ∀ v ∈ (List.range J.jobs).map (dv J), v + 2 < B := fun v hv => by
    obtain ⟨a, rfl⟩ := mem_dv hv; exact hd2 a
  -- the sentinel
  obtain ⟨σ1, hr1, ⟨hcinf1, hDS1, hsn1⟩, hfv1, hfa1, -, hfo1⟩ :=
    (maxScan_spec hB1 _ J.jobs hDSl hDSB (by omega)).frame.run (σ := σ0) ⟨hDS, hsn⟩
  have hn1 : σ1.vars "n" = J.jobs := by rw [hfv1 "n" (by decide)]; exact hn
  have hm1 : σ1.vars "m" = J.machines := by rw [hfv1 "m" (by decide)]; exact hm
  have hW1 : σ1.vars "W" = W := by rw [hfv1 "W" (by decide)]; exact hW
  have hout1 : σ1.out = [] := by rw [hfo1 (by decide)]; exact hout
  have hPS1 : σ1.arrs "PS" = (List.range J.jobs).map (pv J) := by
    rw [hfa1 "PS" (by decide)]; exact hPS
  have hQS1 : σ1.arrs "QS" = (List.range J.jobs).map (qv J) := by
    rw [hfa1 "QS" (by decide)]; exact hQS
  have hTX1 : σ1.arrs "TX" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hfa1 "TX" (by decide)]; exact hTX
  have hTY1 : σ1.arrs "TY" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hfa1 "TY" (by decide)]; exact hTY
  -- the height of the trees
  obtain ⟨σ2, hr2, ⟨htN2, hth2, hn2⟩, hfv2, hfa2, -, hfo2⟩ :=
    (sizeLoop_spec (B := B) (n := J.jobs) (by omega)).frame.run (σ := σ1) hn1
  have hm2 : σ2.vars "m" = J.machines := by rw [hfv2 "m" (by decide)]; exact hm1
  have hW2 : σ2.vars "W" = W := by rw [hfv2 "W" (by decide)]; exact hW1
  have hcinf2 : σ2.vars "cinf" = bigOf J := by rw [hfv2 "cinf" (by decide)]; exact hcinf1
  have hout2 : σ2.out = [] := by rw [hfo2 (by decide)]; exact hout1
  have hPS2 : σ2.arrs "PS" = (List.range J.jobs).map (pv J) := by
    rw [hfa2 "PS" (by decide)]; exact hPS1
  have hQS2 : σ2.arrs "QS" = (List.range J.jobs).map (qv J) := by
    rw [hfa2 "QS" (by decide)]; exact hQS1
  have hDS2 : σ2.arrs "DS" = (List.range J.jobs).map (dv J) := by
    rw [hfa2 "DS" (by decide)]; rw [hfa1 "DS" (by decide)]; exact hDS
  have hTX2 : σ2.arrs "TX" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hfa2 "TX" (by decide)]; exact hTX1
  have hTY2 : σ2.arrs "TY" = List.replicate (2 * 2 ^ (J.jobs - 1).size) 0 := by
    rw [hfa2 "TY" (by decide)]; exact hTY1
  -- the starting counts
  obtain ⟨σ3, hr3, hsz3, hrun3, hp3, hp3z, hfv3, harr3⟩ :=
    (initScalars_spec (B := B) J.jobs p hB1 hpB (by omega)).run (σ := σ2)
      ⟨hn2, fun hpos => by
        rw [hPS2]
        have : 0 < J.jobs := hpos
        refine ⟨?_, by simpa using hpos⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range this]
        simp [pv, this, hp]⟩
  have hp0' : σ3.vars "p0" = p := by
    by_cases hj : J.jobs = 0
    · rw [hp3z hj, hp0 hj]
    · exact hp3 (Nat.pos_of_ne_zero hj)
  have hMI : MI J p (J.jobs - 1).size (bigOf J) B 0 (σ3.setVar "jj" 0) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun _ => ∅, ∅, rfl, ?_, Inv.zero, ?_, ?_, ?_, ?_⟩
    · simp; rw [hfv3 "n" (by decide) (by decide) (by decide)]; exact hn2
    · simp; rw [hfv3 "m" (by decide) (by decide) (by decide)]; exact hm2
    · simp; rw [hfv3 "tN" (by decide) (by decide) (by decide)]; exact htN2
    · simp; rw [hfv3 "th" (by decide) (by decide) (by decide)]; exact hth2
    · simp; rw [hfv3 "cinf" (by decide) (by decide) (by decide)]; exact hcinf2
    · simp; rw [harr3]; exact hDS2
    · simp; rw [harr3]; exact hQS2
    · simp; exact hp0'
    · simp
    · intro i hi hlt; omega
    · simp [hsz3]
    · simp [hrun3]
    · unfold TreeOK; simp only [arrs_setVar]; rw [harr3]
      exact treeOK_zero (by omega) hTX2 (fun ℓ => by simp [lfX])
    · unfold TreeOK; simp only [arrs_setVar]; rw [harr3]
      exact treeOK_zero (by omega) hTY2 (fun ℓ => by simp [lfY])
  obtain ⟨σ4, K4, hr4, hMI4, hK4⟩ := mainLoop_run hest hq hN2 hMI
  obtain ⟨hS4, hp4, hjj4, S, Act, hS0, hsteps, hInv, hsz4, hrun4, hX4, hY4⟩ := hMI4
  have hout3 : σ3.out = [] := by rw [hr3.out_eq (by decide)]; exact hout2
  have hout4 : σ4.out = [] := by rw [hr4.out_eq (by decide)]; exact hout3
  have hW3 : σ3.vars "W" = W := by
    rw [hfv3 "W" (by decide) (by decide) (by decide)]; exact hW2
  have hW4 : σ4.vars "W" = W := by rw [hr4.frame_var "W" (by decide)]; exact hW3
  have hcardB : (S J.jobs).card < B := by
    have := Finset.card_le_univ (S J.jobs); simp at this; omega
  obtain ⟨σ5, hr5, hout5⟩ := (finalOut_spec (B := B) (S J.jobs).card W hB1 hcardB hWB).run
    ⟨by rw [hsz4], hW4, hout4⟩
  have hrun : ∀ i (hi : i < J.jobs), Step J p (S i) (S (i + 1)) ⟨i, hi⟩ :=
    fun i hi => hsteps i hi (by omega)
  have hiff := hasWeight_iff_card (W := W) hest hq hw1 hp S hS0 hrun
  refine ⟨σ5, _, hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5))), ?_, ?_⟩
  · unfold tailK; omega
  · rw [hout5]
    congr 1
    by_cases hw : W ≤ (S J.jobs).card
    · simp [hw, hiff.mpr hw]
    · have hnw : ¬ J.HasWeight W := fun h => hw (hiff.mp h)
      simp [hw, hnw]

end Lax496464Proofs.Ram.T4Tail
