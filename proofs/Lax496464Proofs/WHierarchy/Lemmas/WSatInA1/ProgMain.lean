import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRows
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgStruct
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm2

/-! # The whole body writes the reduction's output

`body_spec`: the ten phases of `body d` write the word of the structure followed by the code of the
sentence; the frame facts show that each phase keeps what the later phases read. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgEmit Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgStruct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm2
open Lax496464Proofs.WHierarchy.HittingSet.Firsts (firstsLoop firstsLoop_spec FInv firsts_eq_of_FInv
  firstBody scanLoop scanBody)

variable {cl : List (List ℕ)} {d k B : ℕ}

/-! ### What each phase writes -/

theorem warrs_parse : parse.warrs ⊆ ["co", "cd"] := by
  intro a ha; simp [parse, parseBody, copyBody, Com.warrs] at ha ⊢; tauto
theorem wvars_consts (y : String) (h : y ∈ (consts d).wvars) :
    y ∈ ["w_M", "w_pb", "w_pn", "w_pr", "w_pi", "w_dk", "hs_t", "w_md", "w_K1", "w_F", "w_nv",
      "w_d1"] := by
  simp [consts, powCom, Com.wvars] at h ⊢; tauto
theorem warrs_consts : (consts d).warrs = [] := by simp [consts, powCom, Com.warrs]
theorem warrs_varRows : varRows.warrs ⊆ ["hs_mem"] := by
  intro a ha; simp [varRows, Com.warrs] at ha ⊢; tauto
theorem warrs_firsts : firstsLoop.warrs ⊆ ["fp_f"] := by
  intro a ha; simp [firstsLoop, firstBody, scanLoop, scanBody, Com.warrs] at ha ⊢; tauto
theorem wvars_firsts (y : String) (h : y ∈ firstsLoop.wvars) : y ∈ ["fp_p", "fp_q", "fp_r"] := by
  simp [firstsLoop, firstBody, scanLoop, scanBody, Com.wvars] at h ⊢; tauto
theorem warrs_canonRows : canonRows.warrs ⊆ ["hs_mem"] := by
  intro a ha; simp [canonRows, Com.warrs] at ha ⊢; tauto
theorem warrs_nRows : nRows.warrs ⊆ ["hs_mem"] := by
  intro a ha; simp [nRows, nBody, keyBody, keyEc, Com.warrs] at ha ⊢; tauto
theorem warrs_lRows : (lRows d).warrs ⊆ ["hs_mem", "ch"] := by
  intro a ha
  simp [lRows, lBody, simBody, simHead, simTail, lRow, padBody, c2Body, c2Step, c2Grp, grpCom,
    grpHead, grpTail, hitLoop, hitLit, chLoop, pick, Com.warrs] at ha ⊢; tauto

theorem ctx_not_consts : ∀ y ∈ ["w_m", "w_L", "w_k"], y ∉ ["w_M", "w_pb", "w_pn", "w_pr", "w_pi",
    "w_dk", "hs_t", "w_md", "w_K1", "w_F", "w_nv", "w_d1"] := by decide

theorem ctx_not_firsts : ∀ y ∈ ctxVars, y ∉ ["fp_p", "fp_q", "fp_r"] := by decide

theorem not_mem_of_subset {l l' : List String} (h : l ⊆ l') {a : String} (ha : a ∉ l') : a ∉ l :=
  fun hm => ha (h hm)

/-! ### The body -/

/-- The arrays of the initial environment. -/
def Arrs0 (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  σ.arrs "co" = List.replicate (cl.length + 1) 0 ∧ σ.arrs "cd" = List.replicate (nL cl) 0 ∧
    σ.arrs "hs_mem" = List.replicate (sz cl d k) 0 ∧ σ.arrs "fp_f" = List.replicate (sz cl d k) 0 ∧
    σ.arrs "ch" = List.replicate (k + 1) 0

/-- The cost of the body. -/
def Kbody (cl : List (List ℕ)) (d k : ℕ) : ℕ :=
  Kparse cl + (Kconst d k + ((24 * nL cl + 6) + (((34 * sz cl d k + 24) * sz cl d k + 6) +
    ((34 * nL cl + 6) + (KnRows cl d + (KlRows cl d k + (((34 * sz cl d k + 24) * sz cl d k + 6) +
      (KstructOut cl d k + KformOut d k))))))))

theorem hsS_lt (hB : BB cl d k B) (n : ℕ) : ∀ v ∈ hsS cl d k n, v < B := by
  intro v hv
  simp only [hsS, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hs_lt hB (List.mem_of_mem_take hv)
  · have := List.eq_of_mem_replicate hv; have := hB.hl; omega

set_option maxHeartbeats 8000000 in
theorem body_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) :
    Spec B (fun σ => σ.arrs "a" = wordOf' cl k ∧ Arrs0 cl d k σ) (body d)
      (fun σ σ' => σ'.out = σ.out ++ (structWord cl d k ++ (phi d k).encode)) (Kbody cl d k) := by
  rintro σ0 ⟨ha, hco, hcd, hhs, hfp, hch⟩
  have hszB := hB.cb.sz
  have hl := hB.hl
  -- 1. parse
  obtain ⟨σ1, r1, hP1, hv1, ha1, -, ho1⟩ :=
    (parse_value (B := B) (k := k) hB.hx hB.hl).frame σ0 ⟨ha, hco, hcd⟩
  obtain ⟨ha1', hm1, hL1, hk1, hco1, hcd1⟩ := hP1
  have hhs1 : σ1.arrs "hs_mem" = List.replicate (sz cl d k) 0 := by
    rw [ha1 _ (not_mem_of_subset warrs_parse (by decide))]; exact hhs
  have hfp1 : σ1.arrs "fp_f" = List.replicate (sz cl d k) 0 := by
    rw [ha1 _ (not_mem_of_subset warrs_parse (by decide))]; exact hfp
  have hch1 : σ1.arrs "ch" = List.replicate (k + 1) 0 := by
    rw [ha1 _ (not_mem_of_subset warrs_parse (by decide))]; exact hch
  have ho1' : σ1.out = σ0.out := ho1 (by simp [parse, parseBody, copyBody, Com.NoWrite])
  -- 2. constants
  obtain ⟨σ2, r2, hC2, hv2, ha2, -, ho2⟩ := (consts_value (d := d) hB.cb).frame σ1 ⟨hL1, hk1, hm1⟩
  have hkeep2 : ∀ y ∈ ["w_m", "w_L", "w_k"], σ2.vars y = σ1.vars y := by
    intro y hy
    exact hv2 y (fun h => ctx_not_consts y hy (wvars_consts y h))
  have ha2' : σ2.arrs = σ1.arrs := funext fun a => ha2 a (by rw [warrs_consts]; simp)
  have hCtx2 : Ctx cl d k σ2 := by
    refine ⟨by rw [ha2']; exact ha1', by rw [ha2']; exact hco1, by rw [ha2']; exact hcd1,
      by rw [hkeep2 _ (by simp)]; exact hm1, by rw [hkeep2 _ (by simp)]; exact hL1,
      by rw [hkeep2 _ (by simp)]; exact hk1, hC2⟩
  have ho2' : σ2.out = σ0.out := by rw [ho2 (by simp [consts, powCom, Com.NoWrite]), ho1']
  -- 3. the variables
  obtain ⟨σ3, r3, ⟨hC3, hh3⟩, -, ha3, -, ho3⟩ := (varRows_spec hB).frame σ2
    ⟨hCtx2, by rw [ha2', hhs1, hsS_zero]⟩
  have hfp3 : σ3.arrs "fp_f" = List.replicate (sz cl d k) 0 := by
    rw [ha3 _ (not_mem_of_subset warrs_varRows (by decide)), ha2']; exact hfp1
  have hch3 : σ3.arrs "ch" = List.replicate (k + 1) 0 := by
    rw [ha3 _ (not_mem_of_subset warrs_varRows (by decide)), ha2']; exact hch1
  have ho3' : σ3.out = σ0.out := by rw [ho3 (by simp [varRows, Com.NoWrite]), ho2']
  -- 4. the first occurrences of the variables
  have hFI : FInv (hsS cl d k (nL cl)) (σ3.setVar "fp_p" 0) := by
    refine ⟨by simp [Env.setVar, hh3], by simp [Env.setVar, hC3.ht, length_hsS],
      by simp [Env.setVar], by simp [Env.setVar, hfp3, length_hsS], by simp [Env.setVar]⟩
  obtain ⟨σ4, r4, ⟨hF4, hp4⟩, hv4, ha4, -, ho4⟩ :=
    (firstsLoop_spec (B := B) (hsS cl d k (nL cl)) (hsS_lt hB _)
      (by rw [length_hsS]; omega)).frame σ3 hFI
  have hfp4 : σ4.arrs "fp_f" = F1 cl d k := firsts_eq_of_FInv hF4 hp4
  have hC4 : Ctx cl d k σ4 := hC3.keep
    (fun y hy => hv4 y (fun h => ctx_not_firsts y hy (wvars_firsts y h)))
    (fun a ha' => ha4 a (not_mem_of_subset warrs_firsts (by revert ha' a; decide)))
  have hh4 : σ4.arrs "hs_mem" = hsS cl d k (nL cl) := by
    rw [ha4 _ (not_mem_of_subset warrs_firsts (by decide))]; exact hh3
  have hch4 : σ4.arrs "ch" = List.replicate (k + 1) 0 := by
    rw [ha4 _ (not_mem_of_subset warrs_firsts (by decide))]; exact hch3
  have ho4' : σ4.out = σ0.out := by
    rw [ho4 (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.NoWrite]), ho3']
  -- 5. the tuples of `C`
  obtain ⟨σ5, r5, ⟨hC5, hf5, hh5⟩, -, ha5, -, ho5⟩ := (canonRows_spec hB).frame σ4 ⟨hC4, hfp4, hh4⟩
  have hch5 : σ5.arrs "ch" = List.replicate (k + 1) 0 := by
    rw [ha5 _ (not_mem_of_subset warrs_canonRows (by decide))]; exact hch4
  have ho5' : σ5.out = σ0.out := by rw [ho5 (by simp [canonRows, Com.NoWrite]), ho4']
  -- 6. the keys
  obtain ⟨σ6, r6, ⟨hC6, hf6, hh6⟩, -, ha6, -, ho6⟩ := (nRows_spec hB).frame σ5 ⟨hC5, hf5, hh5⟩
  have hch6 : σ6.arrs "ch" = List.replicate (k + 1) 0 := by
    rw [ha6 _ (not_mem_of_subset warrs_nRows (by decide))]; exact hch5
  have ho6' : σ6.out = σ0.out := by
    rw [ho6 (by simp [nRows, nBody, keyBody, keyEc, Com.NoWrite]), ho5']
  -- 7. the searches
  obtain ⟨σ7, r7, ⟨hC7, hh7⟩, -, ha7, -, ho7⟩ := (lRows_spec hB hd).frame σ6
    ⟨hC6, hf6, by rw [hch6]; simp, hh6⟩
  have hf7 : σ7.arrs "fp_f" = F1 cl d k := by
    rw [ha7 _ (not_mem_of_subset warrs_lRows (by decide))]; exact hf6
  have ho7' : σ7.out = σ0.out := by
    rw [ho7 (by simp [lRows, lBody, simBody, simHead, simTail, lRow, padBody, c2Body, c2Step,
      c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit, chLoop, pick, Com.NoWrite]), ho6']
  -- 8. the first occurrences of all numbers
  have hFI8 : FInv (hs cl d k) (σ7.setVar "fp_p" 0) := by
    refine ⟨by simp [Env.setVar, hh7], by simp [Env.setVar, hC7.ht, length_hs],
      by simp [Env.setVar], by simp [Env.setVar, hf7, length_F1, length_hs], by simp [Env.setVar]⟩
  obtain ⟨σ8, r8, ⟨hF8, hp8⟩, hv8, ha8, -, ho8⟩ :=
    (firstsLoop_spec (B := B) (hs cl d k) (fun v hv => hs_lt hB hv)
      (by rw [length_hs]; omega)).frame σ7 hFI8
  have hC8 : Ctx cl d k σ8 := hC7.keep
    (fun y hy => hv8 y (fun h => ctx_not_firsts y hy (wvars_firsts y h)))
    (fun a ha' => ha8 a (not_mem_of_subset warrs_firsts (by revert ha' a; decide)))
  have hh8 : σ8.arrs "hs_mem" = hs cl d k := by
    rw [ha8 _ (not_mem_of_subset warrs_firsts (by decide))]; exact hh7
  have hS8 : SC cl d k σ8 := ⟨hC8, hh8, firsts_eq_of_FInv hF8 hp8⟩
  have ho8' : σ8.out = σ0.out := by
    rw [ho8 (by simp [firstsLoop, firstBody, scanLoop, scanBody, Com.NoWrite]), ho7']
  -- 9. the structure
  obtain ⟨σ9, r9, ho9, hS9⟩ := structOut_spec hB σ8 hS8
  -- 10. the sentence
  have hFB : FB d k B := ⟨hB.cb.nv, by have := hB.cb.small; have := MM_ge cl; omega⟩
  obtain ⟨σ10, r10, ho10⟩ := formOut_spec hFB σ9
    ⟨hS9.1.hk, hS9.1.hK1, hS9.1.hF, hS9.1.hnv, hS9.1.hd1⟩
  rw [length_hsS] at r4
  rw [length_hs] at r8
  refine ⟨σ10, r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10)))))))),
    ?_⟩
  show σ10.out = σ0.out ++ (structWord cl d k ++ (phi d k).encode)
  rw [ho10, ho9, ho8', List.append_assoc]

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgMain
