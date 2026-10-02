import Lax496464Proofs.Ram.Cols1
import Lax496464Proofs.Ram.ListUtil
import Lax496464Proofs.Ram.ListUtil

/-!
# Corollary 1: the Initial Constants

Before the table can be filled, the machine needs a sentinel `cinf` strictly larger than
every due date the sorted array `DS` holds — the table's `+∞`. A single scan finds it: keep
the largest due date seen, then add two, room for `Dat.infd`'s strict inequality.
-/

namespace Lax496464Proofs.Ram.Corollary1Init

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.ListUtil

/-- One step: raise `cinf` to `DS[mi]+1` if that is bigger. -/
def maxBody : Com :=
  .seq (.assign "mv" (.get "DS" (V "mi")))
    (.seq (.ite (.lt (V "cinf") (V "mv")) (.assign "cinf" (V "mv")) .skip) (bump "mi"))

/-- `cinf := 1 + max (DS[0], …, DS[n-1], 0)`, over the whole array. -/
def maxScan : Com :=
  .seq (.assign "cinf" (.lit 0))
    (.seq (.seq (.assign "mi" (.lit 0)) (.while (.lt (V "mi") (V "sn")) maxBody))
      (.seq (bump "cinf") (bump "cinf")))

theorem foldr_max_lt {l : List ℕ} {B c : ℕ} (h : ∀ v ∈ l, v + c < B) (hB : c < B) :
    l.foldr max 0 + c < B := by
  induction l with
  | nil => simpa using hB
  | cons a l ih =>
    simp only [List.foldr_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    omega

/-- The invariant of the scan: `cinf` is the max of the prefix seen so far. -/
def MI (DS : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.arrs "DS" = DS ∧ σ.vars "sn" = n ∧ σ.vars "mi" ≤ n ∧
    σ.vars "cinf" = (DS.take (σ.vars "mi")).foldr max 0

theorem foldr_max_eq (l : List ℕ) (seed : ℕ) : l.foldr max seed = max seed (l.foldr max 0) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, ih]; omega

theorem maxBody_spec {B : ℕ} (hB : 1 < B) (DS : List ℕ) (n : ℕ) (hDSl : DS.length = n)
    (hDSB : ∀ v ∈ DS, v + 2 < B) (hnB : n < B) :
    Spec B (fun σ => MI DS n σ ∧ σ.vars "mi" < n) maxBody
      (fun σ σ' => MI DS n σ' ∧ σ'.vars "mi" = σ.vars "mi" + 1) 50 := by
  have hgetB : ∀ t, t < DS.length → DS.getD t 0 < B := fun t ht => by
    have := hDSB (DS.getD t 0) (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
    omega
  refine Spec.of_exists fun σ ⟨⟨hDS, hsn, hmin, hcinf⟩, hlt⟩ => ?_
  have hmiD : σ.vars "mi" < DS.length := by omega
  have hcinfB : σ.vars "cinf" < B := by
    rw [hcinf]
    have hDSB' : ∀ v ∈ DS.take (σ.vars "mi"), v < B := fun v hv => by
      have := hDSB v (List.mem_of_mem_take hv); omega
    have := foldr_max_lt (c := 0) hDSB' (by omega)
    omega
  have hmiB : σ.vars "mi" < B := by omega
  have hvi : (V "mi").evalB B σ = some (σ.vars "mi") :=
    evalB_var (B := B) (σ := σ) (x := "mi") hmiB
  have hg : (Expr.get "DS" (V "mi")).evalB B σ = some (DS.getD (σ.vars "mi") 0) := by
    have := RunStep.eval_get B σ "DS" (V "mi") (σ.vars "mi") hvi (by rw [hDS]; exact hmiD)
      (by rw [hDS]; exact hgetB _ hmiD)
    rwa [hDS] at this
  have r1 := Run.assign (B := B) (σ := σ) (x := "mv") (e := .get "DS" (V "mi"))
    (v := DS.getD (σ.vars "mi") 0) hg
  set σa : Env := σ.setVar "mv" (DS.getD (σ.vars "mi") 0) with hσa
  have hmvB : DS.getD (σ.vars "mi") 0 < B := hgetB _ hmiD
  have hva : (V "cinf").evalB B σa = some (σ.vars "cinf") := by
    have : σa.vars "cinf" = σ.vars "cinf" := by simp [hσa]
    exact this ▸ evalB_var (B := B) (σ := σa) (x := "cinf") (by rw [this]; exact hcinfB)
  have hvb : (V "mv").evalB B σa = some (DS.getD (σ.vars "mi") 0) := by
    have : σa.vars "mv" = DS.getD (σ.vars "mi") 0 := by simp [hσa]
    exact this ▸ evalB_var (B := B) (σ := σa) (x := "mv") (by rw [this]; exact hmvB)
  have hc := evalB_condLt hva hvb
  have hcsize : (Cond.lt (V "cinf") (V "mv")).size = 3 := by decide
  have htk : DS.take (σ.vars "mi" + 1) = DS.take (σ.vars "mi") ++ [DS.getD (σ.vars "mi") 0] :=
    Lax496464Proofs.Ram.Sort.take_getD_succ DS hmiD
  by_cases hlt' : σ.vars "cinf" < DS.getD (σ.vars "mi") 0
  · have hct : (Cond.lt (V "cinf") (V "mv")).evalB B σa = some true := by
      rw [hc]; simpa using hlt'
    have r2 := Run.assign (B := B) (σ := σa) (x := "cinf") (e := V "mv")
      (v := DS.getD (σ.vars "mi") 0) hvb
    set σb : Env := σa.setVar "cinf" (DS.getD (σ.vars "mi") 0) with hσb
    have hl1 : (Expr.lit 1).evalB B σb = some 1 := evalB_lit hB
    have hvi3 : (V "mi").evalB B σb = some (σ.vars "mi") := by
      have : σb.vars "mi" = σ.vars "mi" := by simp [hσb, hσa]
      exact this ▸ evalB_var (B := B) (σ := σb) (x := "mi") (by rw [this]; omega)
    have r3 := Run.assign (B := B) (σ := σb) (x := "mi") (e := .bin .add (V "mi") (.lit 1))
      (v := σ.vars "mi" + 1) (evalB_bin hvi3 hl1 (by show σ.vars "mi" + 1 < B; omega))
    have hcinf3 : (σb.setVar "mi" (σ.vars "mi" + 1)).vars "cinf" = DS.getD (σ.vars "mi") 0 := by
      simp [hσb, hσa]
    have hmi3 : (σb.setVar "mi" (σ.vars "mi" + 1)).vars "mi" = σ.vars "mi" + 1 := by simp
    have hDS3 : (σb.setVar "mi" (σ.vars "mi" + 1)).arrs "DS" = DS := by
      simp [hσb, hσa, hDS]
    have hsn3 : (σb.setVar "mi" (σ.vars "mi" + 1)).vars "sn" = n := by simp [hσb, hσa, hsn]
    refine ⟨_, 50, (r1.seq ((Run.ite_true hct r2).seq r3)).mono ?_, le_rfl, ⟨hDS3, hsn3, by omega, ?_⟩, hmi3⟩
    · simp only [Expr.size, hcsize]; omega
    · rw [hmi3, hcinf3, htk, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil, Nat.max_zero]
      rw [foldr_max_eq]
      omega
  · have hct : (Cond.lt (V "cinf") (V "mv")).evalB B σa = some false := by
      rw [hc]; simpa using hlt'
    have r2 : Run B .skip σa σa 1 := Run.skip
    have hl1 : (Expr.lit 1).evalB B σa = some 1 := evalB_lit hB
    have hvi3 : (V "mi").evalB B σa = some (σ.vars "mi") := by
      have : σa.vars "mi" = σ.vars "mi" := by simp [hσa]
      exact this ▸ evalB_var (B := B) (σ := σa) (x := "mi") (by rw [this]; omega)
    have r3 := Run.assign (B := B) (σ := σa) (x := "mi") (e := .bin .add (V "mi") (.lit 1))
      (v := σ.vars "mi" + 1) (evalB_bin hvi3 hl1 (by show σ.vars "mi" + 1 < B; omega))
    have hcinf3 : (σa.setVar "mi" (σ.vars "mi" + 1)).vars "cinf" = σ.vars "cinf" := by
      simp [hσa]
    have hmi3 : (σa.setVar "mi" (σ.vars "mi" + 1)).vars "mi" = σ.vars "mi" + 1 := by simp
    have hDS3 : (σa.setVar "mi" (σ.vars "mi" + 1)).arrs "DS" = DS := by simp [hσa, hDS]
    have hsn3 : (σa.setVar "mi" (σ.vars "mi" + 1)).vars "sn" = n := by simp [hσa, hsn]
    refine ⟨_, 50, (r1.seq ((Run.ite_false hct r2).seq r3)).mono ?_, le_rfl, ⟨hDS3, hsn3, by omega, ?_⟩, hmi3⟩
    · simp only [Expr.size, hcsize]; omega
    · rw [hmi3, hcinf3, htk, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil, Nat.max_zero]
      rw [foldr_max_eq]
      omega

/-- `cinf := 1 + max(DS[0], …, DS[n-1], 0)`, computed over the whole array. -/
theorem maxScan_spec {B : ℕ} (hB : 1 < B) (DS : List ℕ) (n : ℕ) (hDSl : DS.length = n)
    (hDSB : ∀ v ∈ DS, v + 2 < B) (hnB : n + 2 < B) :
    Spec B (fun σ => σ.arrs "DS" = DS ∧ σ.vars "sn" = n) maxScan
      (fun _ σ' => σ'.vars "cinf" = DS.foldr max 0 + 2 ∧ σ'.arrs "DS" = DS ∧ σ'.vars "sn" = n)
      (2 + (2 + ((50 + 4) * n + 6) + 4 + 4)) := by
  have hloop := Spec.forRangeZero (B := B) (c := maxBody) "mi" "sn" (MI DS n) n 50 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (maxBody_spec hB DS n hDSl hDSB (by omega))
  refine Spec.of_exists fun σ ⟨hDS, hsn⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r0 := Run.assign (B := B) (σ := σ) (x := "cinf") (e := .lit 0) (v := 0) hl0
  set σ0 : Env := σ.setVar "cinf" 0 with hσ0
  have hMI0 : MI DS n (σ0.setVar "mi" 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hσ0, hDS, hsn]
  obtain ⟨σ1, hr1, hI1, hmi1⟩ := hloop σ0 hMI0
  have hcinf1 : σ1.vars "cinf" = DS.foldr max 0 := by
    have := hI1.2.2.2; rw [hmi1, List.take_of_length_le (by omega)] at this; exact this
  have hmax0B : DS.foldr max 0 + 2 < B := foldr_max_lt hDSB (by omega)
  have hl1 : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit hB
  have hvc : (V "cinf").evalB B σ1 = some (DS.foldr max 0) :=
    hcinf1 ▸ evalB_var (B := B) (σ := σ1) (x := "cinf") (by rw [hcinf1]; omega)
  have r2 := Run.assign (B := B) (σ := σ1) (x := "cinf") (e := .bin .add (V "cinf") (.lit 1))
    (v := DS.foldr max 0 + 1) (evalB_bin hvc hl1 (by show DS.foldr max 0 + 1 < B; omega))
  set σ2 : Env := σ1.setVar "cinf" (DS.foldr max 0 + 1) with hσ2
  have hvc2 : (V "cinf").evalB B σ2 = some (DS.foldr max 0 + 1) := by
    have : σ2.vars "cinf" = DS.foldr max 0 + 1 := by simp [hσ2]
    exact this ▸ evalB_var (B := B) (σ := σ2) (x := "cinf") (by rw [this]; omega)
  have hl1' : (Expr.lit 1).evalB B σ2 = some 1 := evalB_lit hB
  have h2eval : (Expr.bin Bop.add (V "cinf") (Expr.lit 1)).evalB B σ2 = some (DS.foldr max 0 + 2) :=
    @evalB_bin B Bop.add (V "cinf") (Expr.lit 1) σ2 (DS.foldr max 0 + 1) 1 hvc2 hl1'
      (by show DS.foldr max 0 + 1 + 1 < B; omega)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "cinf") (e := .bin .add (V "cinf") (.lit 1))
    (v := DS.foldr max 0 + 2) h2eval
  refine ⟨_, _, (r0.seq (hr1.seq (r2.seq r3))).mono ?_, le_rfl, ?_, ?_, ?_⟩
  · simp only [Expr.size]; omega
  · simp [hσ2]
  · simp [hσ2, hI1.1]
  · simp [hσ2, hI1.2.1]

/-! ## The rest of the setup: `sn1`, the initial answer, and `PC := [cinf, …, cinf]` -/

open Lax496464Proofs.Ram.Cols1 (fillInf fillInf_spec)

/-- `sn1 := sn + 1`; `ans := 1` if `W = 0`, else `0`; then `PC := [cinf, …, cinf]`. -/
def initRest : Com :=
  .seq (.assign "sn1" (.bin .add (V "sn") (.lit 1)))
    (.seq (.ite (.eq (V "W") (.lit 0)) (.assign "ans" (.lit 1)) (.assign "ans" (.lit 0)))
      fillInf)

theorem initRest_spec {B : ℕ} (hB : 1 < B) (n W inf : ℕ) (hnB : n + 2 < B) (hWB : W < B)
    (hinfB : inf < B) :
    Spec B (fun σ => σ.vars "sn" = n ∧ σ.vars "W" = W ∧ σ.vars "cinf" = inf ∧
        (σ.arrs "PC").length = n + 1) initRest
      (fun _ σ' => σ'.vars "sn1" = n + 1 ∧ (σ'.vars "ans" = 1 ∨ σ'.vars "ans" = 0) ∧
        (σ'.vars "ans" = 1 ↔ W = 0) ∧ σ'.arrs "PC" = List.replicate (n + 1) inf ∧
        σ'.vars "sn" = n ∧ σ'.vars "cinf" = inf)
      (8 + (30 + ((20 + 4) * (n + 1) + 6))) := by
  have hcsize : (Cond.eq (V "W") (Expr.lit 0)).size = 3 := by decide
  refine Spec.of_exists fun σ ⟨hsn, hW, hcinf, hPCl⟩ => ?_
  have hvn : (V "sn").evalB B σ = some n := hsn ▸ evalB_var (B := B) (σ := σ) (x := "sn")
    (by rw [hsn]; omega)
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  have r1 := Run.assign (B := B) (σ := σ) (x := "sn1") (e := .bin .add (V "sn") (.lit 1))
    (v := n + 1) (evalB_bin hvn hl1 (by show n + 1 < B; omega))
  set σ1 : Env := σ.setVar "sn1" (n + 1) with hσ1
  have hvW : (V "W").evalB B σ1 = some W := by
    have : σ1.vars "W" = W := by simp [hσ1, hW]
    exact this ▸ evalB_var (B := B) (σ := σ1) (x := "W") (by rw [this]; omega)
  have hl0 : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
  have hc := evalB_condEq hvW hl0
  have hsn1 : σ1.vars "sn" = n := by simp [hσ1, hsn]
  by_cases hW0 : W = 0
  · have hct : (Cond.eq (V "W") (.lit 0)).evalB B σ1 = some true := by rw [hc]; simp [hW0]
    have hl1' : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit hB
    have r2 := Run.assign (B := B) (σ := σ1) (x := "ans") (e := .lit 1) (v := 1) hl1'
    set σ2 : Env := σ1.setVar "ans" 1 with hσ2
    have hPCl2 : (σ2.arrs "PC").length = n + 1 := by simp [hσ2, hσ1, hPCl]
    have hsn12 : σ2.vars "sn1" = n + 1 := by simp [hσ2, hσ1]
    have hcinf2 : σ2.vars "cinf" = inf := by simp [hσ2, hσ1, hcinf]
    have hans2 : σ2.vars "ans" = 1 := by simp [hσ2]
    have hsn2 : σ2.vars "sn" = n := by simp [hσ2, hσ1, hsn]
    obtain ⟨σ3, hr3, ⟨hPC3, hsn13, hcinf3⟩, hfv3, -, -, -⟩ :=
      (fillInf_spec hB inf (n + 1) (by omega) hinfB).frame.run (σ := σ2) ⟨hPCl2, hsn12, hcinf2⟩
    have hans3 : σ3.vars "ans" = 1 := by rw [hfv3 "ans" (by decide), hans2]
    have hsn3 : σ3.vars "sn" = n := by rw [hfv3 "sn" (by decide), hsn2]
    refine ⟨σ3, _, (r1.seq (Run.ite_true hct r2 |>.seq hr3)).mono ?_, le_rfl, hsn13,
      Or.inl hans3, by simp [hans3, hW0], hPC3, hsn3, hcinf3⟩
    simp only [Expr.size, hcsize]; omega
  · have hct : (Cond.eq (V "W") (.lit 0)).evalB B σ1 = some false := by
      rw [hc]; simp [hW0]
    have hl0' : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
    have r2 := Run.assign (B := B) (σ := σ1) (x := "ans") (e := .lit 0) (v := 0) hl0'
    set σ2 : Env := σ1.setVar "ans" 0 with hσ2
    have hPCl2 : (σ2.arrs "PC").length = n + 1 := by simp [hσ2, hσ1, hPCl]
    have hsn12 : σ2.vars "sn1" = n + 1 := by simp [hσ2, hσ1]
    have hcinf2 : σ2.vars "cinf" = inf := by simp [hσ2, hσ1, hcinf]
    have hans2 : σ2.vars "ans" = 0 := by simp [hσ2]
    have hsn2 : σ2.vars "sn" = n := by simp [hσ2, hσ1, hsn]
    obtain ⟨σ3, hr3, ⟨hPC3, hsn13, hcinf3⟩, hfv3, -, -, -⟩ :=
      (fillInf_spec hB inf (n + 1) (by omega) hinfB).frame.run (σ := σ2) ⟨hPCl2, hsn12, hcinf2⟩
    have hans3 : σ3.vars "ans" = 0 := by rw [hfv3 "ans" (by decide), hans2]
    have hsn3 : σ3.vars "sn" = n := by rw [hfv3 "sn" (by decide), hsn2]
    refine ⟨σ3, _, (r1.seq (Run.ite_false hct r2 |>.seq hr3)).mono ?_, le_rfl, hsn13,
      Or.inr hans3, by simp [hans3, hW0], hPC3, hsn3, hcinf3⟩
    simp only [Expr.size, hcsize]; omega

end Lax496464Proofs.Ram.Corollary1Init
