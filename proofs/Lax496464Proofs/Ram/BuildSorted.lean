import Lax496464Proofs.Ram.Nxt1
import Lax496464Proofs.Ram.EstPermute
import Lax496464Proofs.Ram.Decode
import Lax496464Proofs.Ram.Dp1

/-!
# The sorted arrays

`EstSort.estSortCom` leaves the sort's output permutation `P` in `SA`. What every downstream
program of this submission wants is not the permutation but three arrays `PS`, `QS`, `DS`,
indexed by *position*, holding the corresponding job's preprocessing time, processing time and
due date: `PS[k] = p_{P[k]}`, and so on, exactly `pv`, `qv`, `dv` of the instance permuted by
`P`. One generic loop reads a block of the decoded instance through the permutation; it is run
three times, once per block, with the offset into `A` held in a scalar.
-/

namespace Lax496464Proofs.Ram.BuildSorted

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.Decode (Decoded)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.WordEncoding
open Lax496464Proofs.Ram.EstPermute Lax496464Proofs.Ram.Dp1

/-- Copy one block of `A`, at offset `boff`, through the permutation `SA`, into `dst`. -/
def buildRow (dst : String) : Com :=
  .seq (.assign "bi" (.lit 0))
    (.while (.lt (V "bi") (V "sn"))
      (.seq (.assign "bt" (.get "SA" (V "bi")))
        (.seq (.assign "bv" (.get "A" (.bin .add (V "boff") (V "bt"))))
          (.seq (.store dst (V "bi") (V "bv")) (bump "bi")))))

theorem buildRow_spec {B : ℕ} (hB : 1 < B) (dst : String) (hdst : dst ≠ "SA" ∧ dst ≠ "A")
    (A P dst0 : List ℕ) (n boff : ℕ) (hPl : P.length = n) (hPn : ∀ k < n, P.getD k 0 < n)
    (hAlen : boff + n ≤ A.length) (hAB : ∀ v ∈ A, v < B) (hnB : n < B) (hboffnB : boff + n < B)
    (hdst0l : dst0.length = n) :
    Spec B (fun σ => σ.arrs "SA" = P ∧ σ.arrs "A" = A ∧ σ.vars "sn" = n ∧ σ.vars "boff" = boff ∧
        σ.arrs dst = dst0)
      (buildRow dst)
      (fun _ σ' => σ'.arrs dst = (List.range n).map (fun k => A.getD (boff + P.getD k 0) 0) ∧
        σ'.arrs "SA" = P ∧ σ'.arrs "A" = A ∧ σ'.vars "sn" = n ∧ σ'.vars "boff" = boff)
      ((20 + 4) * n + 6) := by
  have hgetB : ∀ t, t < A.length → A.getD t 0 < B := fun t ht =>
    hAB _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  have hboffB' : boff < B := by omega
  have hSAne : "SA" ≠ dst := Ne.symm hdst.1
  have hAne : "A" ≠ dst := Ne.symm hdst.2
  have hloop := Spec.forRangeZero (B := B) (c := .seq (.assign "bt" (.get "SA" (V "bi")))
      (.seq (.assign "bv" (.get "A" (.bin .add (V "boff") (V "bt"))))
        (.seq (.store dst (V "bi") (V "bv")) (bump "bi")))) "bi" "sn"
    (fun σ => σ.arrs "SA" = P ∧ σ.arrs "A" = A ∧ σ.vars "sn" = n ∧ σ.vars "boff" = boff ∧
      (σ.arrs dst).length = n ∧ σ.vars "bi" ≤ n ∧ (σ.arrs dst).take (σ.vars "bi") =
        ((List.range n).map (fun k => A.getD (boff + P.getD k 0) 0)).take (σ.vars "bi"))
    n 20 hnB (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.1) (by
      refine Spec.of_exists fun σ ⟨⟨hSA, hA, hsn, hboff, hdl, hle, htk⟩, hlt⟩ => ?_
      have hkn : σ.vars "bi" < n := hlt
      have hPkn : P.getD (σ.vars "bi") 0 < n := hPn _ hkn
      have hPkA : P.getD (σ.vars "bi") 0 < A.length := by omega
      have hvi : (V "bi").evalB B σ = some (σ.vars "bi") :=
        evalB_var (B := B) (σ := σ) (x := "bi") (by omega)
      have hg1 : (Expr.get "SA" (V "bi")).evalB B σ = some (P.getD (σ.vars "bi") 0) := by
        have := RunStep.eval_get B σ "SA" (V "bi") (σ.vars "bi") hvi (by rw [hSA]; omega)
          (by rw [hSA]; omega)
        rwa [hSA] at this
      have r1 := Run.assign (B := B) (σ := σ) (x := "bt") (e := .get "SA" (V "bi"))
        (v := P.getD (σ.vars "bi") 0) hg1
      set σa : Env := σ.setVar "bt" (P.getD (σ.vars "bi") 0) with hσa
      have hva : (V "boff").evalB B σa = some boff := by
        have : σa.vars "boff" = boff := by simp [hσa, hboff]
        exact this ▸ evalB_var (B := B) (σ := σa) (x := "boff") (by rw [this]; omega)
      have hvb : (V "bt").evalB B σa = some (P.getD (σ.vars "bi") 0) := by
        have : σa.vars "bt" = P.getD (σ.vars "bi") 0 := by simp [hσa]
        exact this ▸ evalB_var (B := B) (σ := σa) (x := "bt") (by rw [this]; omega)
      have hidx : (Expr.bin .add (V "boff") (V "bt")).evalB B σa
          = some (boff + P.getD (σ.vars "bi") 0) :=
        evalB_bin hva hvb (by show boff + P.getD (σ.vars "bi") 0 < B; omega)
      have hg2 : (Expr.get "A" (.bin .add (V "boff") (V "bt"))).evalB B σa
          = some (A.getD (boff + P.getD (σ.vars "bi") 0) 0) := by
        have hAa : σa.arrs "A" = A := by simp [hσa, hA]
        have := RunStep.eval_get B σa "A" (.bin .add (V "boff") (V "bt"))
          (boff + P.getD (σ.vars "bi") 0) hidx (by rw [hAa]; omega)
          (by rw [hAa]; exact hgetB _ (by omega))
        rwa [hAa] at this
      have r2 := Run.assign (B := B) (σ := σa) (x := "bv")
        (e := .get "A" (.bin .add (V "boff") (V "bt")))
        (v := A.getD (boff + P.getD (σ.vars "bi") 0) 0) hg2
      set σb : Env := σa.setVar "bv" (A.getD (boff + P.getD (σ.vars "bi") 0) 0) with hσb
      have hvi3 : (V "bi").evalB B σb = some (σ.vars "bi") := by
        have : σb.vars "bi" = σ.vars "bi" := by simp [hσb, hσa]
        exact this ▸ evalB_var (B := B) (σ := σb) (x := "bi") (by rw [this]; omega)
      have hvb3 : (V "bv").evalB B σb = some (A.getD (boff + P.getD (σ.vars "bi") 0) 0) := by
        have : σb.vars "bv" = A.getD (boff + P.getD (σ.vars "bi") 0) 0 := by simp [hσb]
        exact this ▸ evalB_var (B := B) (σ := σb) (x := "bv") (by
          rw [this]; exact hgetB _ (by omega))
      have hdlb : (σb.arrs dst).length = n := by simp [hσb, hσa, hdl]
      have hidxlt : σ.vars "bi" < (σb.arrs dst).length := by rw [hdlb]; omega
      have r3 := Run.store (B := B) (σ := σb) (a := dst) (i := V "bi") (e := V "bv")
        (idx := σ.vars "bi") (v := A.getD (boff + P.getD (σ.vars "bi") 0) 0) hvi3 hvb3 hidxlt
      set σc : Env := σb.setArr dst (σ.vars "bi") (A.getD (boff + P.getD (σ.vars "bi") 0) 0)
        with hσc
      have hl1 : (Expr.lit 1).evalB B σc = some 1 := evalB_lit hB
      have hvi4 : (V "bi").evalB B σc = some (σ.vars "bi") := by
        have : σc.vars "bi" = σ.vars "bi" := by simp [hσc, hσb, hσa]
        exact this ▸ evalB_var (B := B) (σ := σc) (x := "bi") (by rw [this]; omega)
      have r4 := Run.assign (B := B) (σ := σc) (x := "bi") (e := .bin .add (V "bi") (.lit 1))
        (v := σ.vars "bi" + 1) (evalB_bin hvi4 hl1 (by show σ.vars "bi" + 1 < B; omega))
      have hSAc : σc.arrs "SA" = P := by
        simp only [hσc, arrs_setArr, if_neg hSAne, hσb, hσa]; exact hSA
      have hAc : σc.arrs "A" = A := by
        simp only [hσc, arrs_setArr, if_neg hAne, hσb, hσa]; exact hA
      have hdstc : σc.arrs dst = (σb.arrs dst).set (σ.vars "bi")
          (A.getD (boff + P.getD (σ.vars "bi") 0) 0) := by
        simp only [hσc, arrs_setArr]; simp
      set σd : Env := σc.setVar "bi" (σ.vars "bi" + 1) with hσd
      have hSAd : σd.arrs "SA" = P := by simp [hσd, hSAc]
      have hAd : σd.arrs "A" = A := by simp [hσd, hAc]
      have hsnd : σd.vars "sn" = n := by simp [hσd, hσc, hσb, hσa, hsn]
      have hboffd : σd.vars "boff" = boff := by simp [hσd, hσc, hσb, hσa, hboff]
      have hdstd : σd.arrs dst = σc.arrs dst := by simp [hσd]
      have hbid : σd.vars "bi" = σ.vars "bi" + 1 := by simp [hσd]
      refine ⟨σd, 20, (r1.seq (r2.seq (r3.seq r4))).mono ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.size]; omega
      · exact hSAd
      · exact hAd
      · exact hsnd
      · exact hboffd
      · rw [hdstd, hdstc, List.length_set, hdlb]
      · omega
      · rw [hdstd, hdstc, hbid, Lax496464Proofs.Ram.Sort.take_set_succ (σb.arrs dst) hidxlt]
        have hσbdst : σb.arrs dst = σ.arrs dst := by simp [hσb, hσa]
        rw [hσbdst, htk, Lax496464Proofs.Ram.Sort.take_getD_succ _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, hkn]
      · exact hbid)
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨hSA, hA, hsn, hboff, hdst0⟩
    exact ⟨by simpa using hSA, by simpa using hA, by simpa using hsn, by simpa using hboff,
      by simp [hdst0, hdst0l], by simp, by simp⟩
  · rintro σ σ' - ⟨⟨hSA, hA, hsn, hboff, hdl, hle, htk⟩, hbi⟩
    rw [hbi] at htk
    refine ⟨?_, hSA, hA, hsn, hboff⟩
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp)] at htk
    exact htk

/-! ## All three blocks -/

/-- Fill `PS`, `QS`, `DS` from the decoded instance in `A` and the sort's permutation in `SA`. -/
def buildSorted : Com :=
  .seq (.assign "boff" (.lit 0)) (.seq (buildRow "PS")
    (.seq (.assign "boff" (V "sn")) (.seq (buildRow "QS")
      (.seq (.assign "boff" (.bin .mul (.lit 2) (V "sn"))) (buildRow "DS")))))

theorem buildSorted_spec {B : ℕ} (hB : 1 < B) (A P PS0 QS0 DS0 : List ℕ) (n : ℕ)
    (hPl : P.length = n) (hPn : ∀ k < n, P.getD k 0 < n) (hAlen : 3 * n + n ≤ A.length)
    (hAB : ∀ v ∈ A, v < B) (hnB : 4 * n + 3 < B) (hPS0 : PS0.length = n)
    (hQS0 : QS0.length = n) (hDS0 : DS0.length = n) :
    Spec B (fun σ => σ.arrs "SA" = P ∧ σ.arrs "A" = A ∧ σ.vars "sn" = n ∧
        σ.arrs "PS" = PS0 ∧ σ.arrs "QS" = QS0 ∧ σ.arrs "DS" = DS0) buildSorted
      (fun _ σ' => σ'.arrs "PS" = (List.range n).map (fun k => A.getD (P.getD k 0) 0) ∧
        σ'.arrs "QS" = (List.range n).map (fun k => A.getD (n + P.getD k 0) 0) ∧
        σ'.arrs "DS" = (List.range n).map (fun k => A.getD (2 * n + P.getD k 0) 0) ∧
        σ'.arrs "SA" = P ∧ σ'.arrs "A" = A ∧ σ'.vars "sn" = n)
      (4 + (((20 + 4) * n + 6) + 4 + ((20 + 4) * n + 6) + 4 + ((20 + 4) * n + 6))) := by
  have hone := hB
  refine Spec.of_exists fun σ ⟨hSA, hA, hsn, hPS0', hQS0', hDS0'⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := "boff") (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar "boff" 0 with hσ1
  obtain ⟨σ2, hr2, ⟨hPS2, hSA2, hA2, hsn2, hboff2⟩, hfv2, hfa2, -, -⟩ :=
    (buildRow_spec hB "PS" (by decide) A P PS0 n 0 hPl hPn (by omega) hAB (by omega) (by omega)
      hPS0).frame.run (σ := σ1) ⟨by simp [hσ1, hSA], by simp [hσ1, hA], by simp [hσ1, hsn],
      by simp [hσ1], by simp [hσ1, hPS0']⟩
  have hQS2 : σ2.arrs "QS" = QS0 := by rw [hfa2 "QS" (by decide), hσ1]; simpa using hQS0'
  have hDS2 : σ2.arrs "DS" = DS0 := by rw [hfa2 "DS" (by decide), hσ1]; simpa using hDS0'
  have hvn2 : (V "sn").evalB B σ2 = some n := hsn2 ▸ evalB_var (B := B) (σ := σ2) (x := "sn")
    (by rw [hsn2]; omega)
  have r3 := Run.assign (B := B) (σ := σ2) (x := "boff") (e := V "sn") (v := n) hvn2
  set σ3 : Env := σ2.setVar "boff" n with hσ3
  obtain ⟨σ4, hr4, ⟨hQS4, hSA4, hA4, hsn4, hboff4⟩, hfv4, hfa4, -, -⟩ :=
    (buildRow_spec hB "QS" (by decide) A P QS0 n n hPl hPn (by omega) hAB (by omega) (by omega)
      hQS0).frame.run (σ := σ3) ⟨by simp [hσ3, hSA2], by simp [hσ3, hA2], by simp [hσ3, hsn2],
      by simp [hσ3], by simp [hσ3, hQS2]⟩
  have hPS4 : σ4.arrs "PS" = (List.range n).map (fun k => A.getD (P.getD k 0) 0) := by
    rw [hfa4 "PS" (by decide), hσ3]; simpa using hPS2
  have hDS4 : σ4.arrs "DS" = DS0 := by rw [hfa4 "DS" (by decide), hσ3]; simpa using hDS2
  have hvn4 : (V "sn").evalB B σ4 = some n := hsn4 ▸ evalB_var (B := B) (σ := σ4) (x := "sn")
    (by rw [hsn4]; omega)
  have hl2 : (Expr.lit 2).evalB B σ4 = some 2 := evalB_lit (by omega)
  have h2n : 2 * n < B := by omega
  have hidx5 : (Expr.bin Bop.mul (Expr.lit 2) (V "sn")).evalB B σ4 = some (2 * n) :=
    evalB_bin hl2 hvn4 h2n
  have r5 := Run.assign (B := B) (σ := σ4) (x := "boff") (e := .bin .mul (.lit 2) (V "sn"))
    (v := 2 * n) hidx5
  set σ5 : Env := σ4.setVar "boff" (2 * n) with hσ5
  obtain ⟨σ6, hr6, ⟨hDS6, hSA6, hA6, hsn6, hboff6⟩, hfv6, hfa6, -, -⟩ :=
    (buildRow_spec hB "DS" (by decide) A P DS0 n (2 * n) hPl hPn (by omega) hAB (by omega)
      (by omega) hDS0).frame.run (σ := σ5) ⟨by simp [hσ5, hSA4], by simp [hσ5, hA4],
      by simp [hσ5, hsn4], by simp [hσ5], by simp [hσ5, hDS4]⟩
  have hPS6 : σ6.arrs "PS" = (List.range n).map (fun k => A.getD (P.getD k 0) 0) := by
    rw [hfa6 "PS" (by decide), hσ5]; simpa using hPS4
  have hQS6 : σ6.arrs "QS" = (List.range n).map (fun k => A.getD (n + P.getD k 0) 0) := by
    rw [hfa6 "QS" (by decide), hσ5]; simpa using hQS4
  refine ⟨σ6, _, (r1.seq (hr2.seq (r3.seq (hr4.seq (r5.seq hr6))))).mono ?_, le_rfl, hPS6, hQS6,
    hDS6, hSA6, hA6, hsn6⟩
  simp only [Expr.size]; omega

/-! ## The arrays are `pv`, `qv`, `dv` of the sorted instance -/

end Lax496464Proofs.Ram.BuildSorted
