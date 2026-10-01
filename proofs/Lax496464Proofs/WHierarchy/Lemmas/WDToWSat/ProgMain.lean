import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill

/-!
# The whole program

`mainCom_spec`: on a word that fits, the main part writes `outWords D x`. `prog_run`: from the initial
environment on the tape `x.length :: x`, the program runs to the output `R D x`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgSetup
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill

variable {D : Data} {x : List ℕ} {B : ℕ}

theorem wvars_decSteps : ∀ (c j : ℕ), ∀ y ∈ (decSteps j c).wvars, y = "w_w"
  | 0, _, y, h => by simp [decSteps] at h
  | c + 1, j, y, h => by
    simp only [decSteps, Com.wvars, List.mem_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact h
    · exact wvars_decSteps c (j + 1) y h

theorem warrs_decSteps : ∀ (c j : ℕ), ∀ b ∈ (decSteps j c).warrs, b = "od"
  | 0, _, b, h => by simp [decSteps] at h
  | c + 1, j, b, h => by
    simp only [decSteps, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.nil_append] at h
    rcases h with h | h
    · exact h
    · exact warrs_decSteps c (j + 1) b h

theorem wvars_zLoop (D : Data) : ∀ y ∈ (zLoop D).wvars, y ∈ "w_z" :: "w_w" :: zS := by
  intro y hy
  have h1 := wvars_decSteps D.r 0 y
  have h2 := wvars_clauses D.cnf y
  simp only [zLoop, zBody, decodeCom, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hy
  simp only [List.mem_cons]
  tauto

theorem warrs_zLoop (D : Data) : ∀ b ∈ (zLoop D).warrs, b ∈ ["od"] := by
  intro b hb
  have h1 := warrs_decSteps D.r 0 b
  simp only [zLoop, zBody, decodeCom, Com.warrs, List.mem_append, warrs_clauses,
    List.not_mem_nil, or_false, List.nil_append] at hb
  simp [h1 hb]

theorem reads_zLoop (D : Data) : ¬ (zLoop D).reads := by
  have hdec : ∀ j c, ¬ (decSteps j c).reads := by
    intro j c
    induction c generalizing j with
    | zero => simp [decSteps]
    | succ c ih => simp [decSteps, Com.reads, ih]
  have hcl : ¬ (seqList (D.cnf.map clauseCom)).reads := by
    refine reads_seqList _ fun c hc => ?_
    obtain ⟨C, -, rfl⟩ := List.mem_map.mp hc
    exact reads_clauseCom C
  simp [zLoop, zBody, decodeCom, Com.reads, hdec, hcl]

/-- The state before the main part. -/
structure MPre (D : Data) (x : List ℕ) (σ : Env) : Prop where
  a : σ.arrs "a" = x
  n : σ.vars "rt_n" = x.length
  sp : σ.vars "w_sp" = spW x
  N : σ.vars "w_N" = NW x
  k : σ.vars "w_k" = kW x
  bo : (σ.arrs "bo").length = spW x
  U : σ.arrs "U" = List.replicate (capW D x) 0
  od : (σ.arrs "od").length = D.r

/-- The cost of the main part. -/
def Kmain (D : Data) (x : List ℕ) : ℕ :=
  (34 * spW x + 12) + (20 + (((10 + 4) * LW D.s D.r x + 6 + 3 +
    ((16 * capW D x + 70 + 4) * x.length + 6)) + ((6 * D.r + 3) + ((6 * D.s + 3) +
    (10 + (((Kz D x + 4) * nW D x ^ D.r + 6) + (((20 + 4) * nW D x ^ D.s + 6) + 2)))))))

set_option maxHeartbeats 4000000 in
/-- **The main part** writes the formula and `k`. -/
theorem mainCom_run (hB : BF D x B) (hg : Good x) (hC : CnfOk D x B) {σ : Env} (hσ : MPre D x σ) :
    ∃ σ', Run B (mainCom D) σ σ' (Kmain D x) ∧ σ'.out = σ.out ++ outWords D x := by
  have hcnt := hB.count_lt
  have hkB : kW x < B := hB.getD_lt _
  have hrs : D.r ≤ D.r + D.s := by omega
  have hss : D.s ≤ D.r + D.s := by omega
  -- block positions
  obtain ⟨σ1, hr1, bo1, f1, o1⟩ := boCom_spec hB hg σ ⟨hσ.a, hσ.sp, hσ.bo⟩
  -- L
  obtain ⟨σ2, hr2, L2, f2, o2⟩ := LCom_spec hB (D := D) σ1
    ⟨by rw [f1.1 _ (by simp)]; exact hσ.n, by rw [f1.1 _ (by simp)]; exact hσ.k,
      by rw [f1.1 _ (by simp)]; exact hσ.N⟩
  -- U
  have hu := Spec.framedOut (uCom_value hB (D := D)) ["w_e", "w_n", "w_p", "w_f", "w_q"] ["U"]
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.wvars])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.warrs])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.reads])
    (by simp [uCom, fill1, fill1Body, fill2, fill2Body, pushNew, memScan, memLoop, memBody,
      Com.NoWrite])
  have f12 : Frame ["w_p", "w_i", "w_t", "w_L"] ["bo"] σ σ2 :=
    (f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))
  obtain ⟨σ3, hr3, ⟨U3, Ul3, n3⟩, f3, o3⟩ := hu σ2
    ⟨by rw [f12.2.1 _ (by simp)]; exact hσ.a, by rw [f12.1 _ (by simp)]; exact hσ.n, L2,
      by rw [f12.1 _ (by simp)]; exact hσ.N, by rw [f12.2.1 _ (by simp)]; exact hσ.U⟩
  -- powers
  obtain ⟨σ4, hr4, P4, f4, o4⟩ := powCom_spec hB "w_PR" (by decide) hrs σ3 n3
  obtain ⟨σ5, hr5, P5, f5, o5⟩ := powCom_spec hB "w_PS" (by decide) hss σ4
    (by show σ4.vars "w_n" = _; rw [f4.1 _ (by simp)]; exact n3)
  have hPR5 : σ5.vars "w_PR" = nW D x ^ D.r := by rw [f5.1 _ (by simp)]; exact P4
  -- the count
  have evc : (Expr.add (.mul (V "w_PR") (.lit D.cnf.length)) (V "w_PS")).evalB B σ5 =
      some (nW D x ^ D.r * D.cnf.length + nW D x ^ D.s) := by
    rw [← hPR5, ← P5]
    refine evalB_bin (evalB_bin (evalB_var ?_) (evalB_lit ?_) ?_) (evalB_var ?_) ?_
    · rw [hPR5]; exact hB.npow_lt hrs
    · have := hB.const; unfold cD at this; omega
    · simp only [Bop.apply_mul]; rw [hPR5]; have := hcnt.1; omega
    · rw [P5]; exact hB.npow_lt hss
    · simp only [Bop.apply_add]; rw [hPR5, P5]; exact hcnt.1
  have hr6 := RunStep.write B σ5 _ _ evc
  set σ6 := { σ5 with out := σ5.out ++ [nW D x ^ D.r * D.cnf.length + nW D x ^ D.s] } with hσ6
  -- the frames so far
  have f16 : Frame ["w_p", "w_i", "w_t", "w_L", "w_e", "w_n", "w_f", "w_q", "w_PR", "w_PS"]
      ["bo", "U"] σ σ6 :=
    ((((f12.mono (by simp) (by simp)).trans (f3.mono (by simp) (by simp))).trans
      (f4.mono (by simp) (by simp))).trans (f5.mono (by simp) (by simp))).trans
      (Frame.refl _ _ _)
  have hctx : Ctx D x σ6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ5.arrs "a" = x; rw [f16.2.1 _ (by simp)]; exact hσ.a
    · show σ5.arrs "bo" = _
      rw [f5.2.1 _ (by simp), f4.2.1 _ (by simp), f3.2.1 _ (by simp), f2.2.1 _ (by simp)]
      exact bo1
    · intro q hq
      show (σ5.arrs "U").getD q 0 = _
      rw [f5.2.1 _ (by simp), f4.2.1 _ (by simp)]; exact U3 q hq
    · show _ ≤ (σ5.arrs "U").length
      rw [f5.2.1 _ (by simp), f4.2.1 _ (by simp)]; exact Ul3
    · show (σ5.arrs "od").length = D.r; rw [f16.2.1 _ (by simp)]; exact hσ.od
    · show σ5.vars "w_n" = _; rw [f5.1 _ (by simp), f4.1 _ (by simp)]; exact n3
  -- the assignments
  have hz := Spec.framed (zLoop_spec hB hg hC σ6.out) _ _ (wvars_zLoop D) (warrs_zLoop D)
    (reads_zLoop D)
  obtain ⟨σ7, hr7, ⟨⟨-, -, -, hout7⟩, hz7⟩, f7⟩ := hz σ6
    ⟨ctx_frame_od hctx (Frame.setVar σ6 (S := ["w_z"]) (A := ["od"]) (by simp) 0) (by simp)
      (by simp [Env.setVar]; exact hctx.odlen),
      by simp [Env.setVar]; exact hPR5, by simp [Env.setVar], by simp [Env.setVar]⟩
  rw [hz7] at hout7
  -- the tautologies
  have ht := Spec.framed (tautLoop_spec hB (D := D) σ7.out) ["w_y"] []
    (by simp [tautLoop, tautBody, Com.wvars]) (by simp [tautLoop, tautBody, Com.warrs])
    (by simp [tautLoop, tautBody, Com.reads])
  have hPS7 : σ7.vars "w_PS" = nW D x ^ D.s := by
    rw [f7.1 _ (by simp [zS])]; show σ5.vars "w_PS" = _; exact P5
  obtain ⟨σ8, hr8, ⟨⟨-, -, hout8⟩, hy8⟩, f8⟩ := ht σ7
    ⟨by simp [Env.setVar, hPS7], by simp [Env.setVar], by simp [Env.setVar]⟩
  rw [hy8] at hout8
  -- `k`
  have hk8 : σ8.vars "w_k" = kW x := by
    rw [f8.1 _ (by simp), f7.1 _ (by simp [zS])]
    show σ5.vars "w_k" = _
    rw [f16.1 _ (by simp)]; exact hσ.k
  have hr9 := RunStep.write B σ8 (V "w_k") _ (evalB_var (by rw [hk8]; exact hkB))
  refine ⟨_, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq hr9)))))))).mono
    (by simp only [Kmain, Expr.size]; omega), ?_⟩
  show σ8.out ++ [σ8.vars "w_k"] = _
  rw [hk8, hout8, hout7]
  show σ5.out ++ _ ++ _ ++ _ ++ _ = _
  rw [o5, o4, o3, o2, o1]
  simp [outWords]

/-! ### The whole program -/

/-- The array lengths of the initial environment. -/
def extW (D : Data) (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length else if a = "bo" then spW x else if a = "U" then capW D x
  else if a = "od" then D.r else 0

/-- The cost of the program. -/
def Kprog (D : Data) (x : List ℕ) : ℕ :=
  16 * x.length + 7 + (20 + ((12 * D.rels.length + 4) + (1 + 3 + (Kmain D x + 10))))

theorem noCom_spec (hk : kW x < B) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "w_k" = kW x) noCom
      (fun σ σ' => σ'.out = σ.out ++ [1, 0, kW x]) 6 := by
  unfold noCom
  run_vcg
  simp [‹σ.vars "w_k" = kW x›]

set_option maxHeartbeats 2000000 in
/-- **The program computes the reduction.** -/
theorem prog_run (hB : BF D x B) (hg : Good x) (hC : fitW D x → CnfOk D x B) :
    ∃ σ', Run B (prog D) (initEnv (extW D x) (x.length :: x)) σ' (Kprog D x) ∧
      σ'.out = R D x := by
  have hlen := hB.len
  have hkB : kW x < B := hB.getD_lt _
  set σ0 := initEnv (extW D x) (x.length :: x) with hσ0
  obtain ⟨σ1, hr1, a1, n1, -, out1, v1, arr1⟩ :=
    Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape_spec x σ0 hB.entries (by omega) rfl
      (by simp [σ0, initEnv, extW]) σ0 rfl
  obtain ⟨σ2, hr2, sp2, N2, k2, f2, o2⟩ := headCom_spec hB hg σ1 ⟨a1, n1⟩
  obtain ⟨σ3, hr3, ft3, f3, o3⟩ := fitCom_spec hB hg (D := D) σ2
    ⟨by rw [f2.2.1 _ (by simp)]; exact a1, sp2⟩
  have ev_ft : (Expr.var "w_ft").evalB B σ3 = some (σ3.vars "w_ft") :=
    evalB_var (by rw [ft3]; split_ifs <;> omega)
  have ev_1 : (Expr.lit 1).evalB B σ3 = some 1 := evalB_lit (by omega)
  have hk3 : σ3.vars "w_k" = kW x := by rw [f3.1 _ (by simp)]; exact k2
  have hout3 : σ3.out = [] := by rw [o3, o2, out1]; simp [σ0, initEnv]
  by_cases hfit : fitW D x
  · have hft : σ3.vars "w_ft" = 1 := by rw [ft3, if_pos hfit]
    have f23 : Frame ["w_sp", "w_N", "w_k", "w_ft"] [] σ1 σ3 :=
      (f2.mono (by simp) (by simp)).trans (f3.mono (by simp) (by simp))
    have hpre : MPre D x σ3 := by
      refine ⟨by rw [f23.2.1 _ (by simp)]; exact a1, by rw [f23.1 _ (by simp)]; exact n1,
        by rw [f3.1 _ (by simp)]; exact sp2, by rw [f3.1 _ (by simp)]; exact N2, hk3, ?_, ?_, ?_⟩
      · rw [f23.2.1 _ (by simp), arr1 _ (by simp)]; simp [σ0, initEnv, extW]
      · rw [f23.2.1 _ (by simp), arr1 _ (by simp)]; simp [σ0, initEnv, extW]
      · rw [f23.2.1 _ (by simp), arr1 _ (by simp)]; simp [σ0, initEnv, extW]
    obtain ⟨σ4, hr4, o4⟩ := mainCom_run hB hg (hC hfit) hpre
    refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq (RunStep.ite_true B _ _ _ σ3 σ4 _
      (RunStep.cond_eq_true B σ3 _ _ _ _ ev_ft ev_1 hft) hr4)))).mono
      (by simp only [Kprog, Cond.size, Expr.size]; omega), ?_⟩
    rw [o4, hout3, R_eq hfit]; rfl
  · have hft : σ3.vars "w_ft" = 0 := by rw [ft3, if_neg hfit]
    obtain ⟨σ4, hr4, o4⟩ := noCom_spec (x := x) hkB (by omega) σ3 hk3
    refine ⟨σ4, (hr1.seq (hr2.seq (hr3.seq (RunStep.ite_false B _ _ _ σ3 σ4 _
      (RunStep.cond_eq_false B σ3 _ _ _ _ ev_ft ev_1 (by omega)) hr4)))).mono
      (by simp only [Kprog, Cond.size, Expr.size]; omega), ?_⟩
    rw [o4, hout3]; unfold R; rw [if_neg hfit]; rfl

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain
