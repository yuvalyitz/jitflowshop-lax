import Lax496464Proofs.WHierarchy.HittingSet.DSMain
import Lax496464Proofs.WHierarchy.HittingSet.DSMath
import Lax496464Proofs.WHierarchy.HittingSet.WDFinal

/-! # Hitting Set to Dominating Set: the running time, and the reduction

The program `dsProg` writes the word of the reduction (`dsOut_eq`, `dsProg_run`), compiles under its
layout and runs in polynomial time (`polyTime`); with the correctness of `DSMath` this gives
`p-Hitting-Set ≤fpt p-Dominating-Set` (`hittingSet_le_dominatingSet`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_C1_GraphProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Parse Lax496464Proofs.WHierarchy.HittingSet.Common
open Lax496464Proofs.WHierarchy.HittingSet.Compress Lax496464Proofs.WHierarchy.HittingSet.Firsts
open Lax496464Proofs.WHierarchy.HittingSet.DSGraph Lax496464Proofs.WHierarchy.HittingSet.DSMath
open Lax496464Proofs.WHierarchy.HittingSet.DSProg1 Lax496464Proofs.WHierarchy.HittingSet.DSProg2
open Lax496464Proofs.WHierarchy.HittingSet.DSMain Lax496464Proofs.WHierarchy.HittingSet.CsrBuild
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V)
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! ## The word written is the word of the graph -/

/-- The offsets the reader leaves in `hs_off`. -/
def offList (P : Instance) : List ℕ := (List.range (P.m + 1)).map (offs P)

theorem offList_getD (P : Instance) {i : ℕ} (hi : i ≤ P.m) : (offList P).getD i 0 = offs P i := by
  simp [offList, List.getD_eq_getElem?_getD, show i < P.m + 1 by omega]

theorem psum_congr {a b : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, a i = b i) : psum a n = psum b n := by
  unfold psum
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem pre_eq_psum (g : ℕ → List ℕ) (i : ℕ) : pre g i = psum (fun u => (g u).length) i := rfl

theorem psum_add (a : ℕ → ℕ) (x y : ℕ) : psum a (x + y) = psum a x + psum (fun j => a (x + j)) y := by
  unfold psum
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

theorem cntL_eq (P : Instance) (u : ℕ) : cntL (firsts (memL P)) (total P) u = cnt P u := by
  unfold cntL cnt
  congr 1
  refine List.filter_congr fun p hp => ?_
  rw [WDFinal.firsts_getD P (List.mem_range.mp hp)]

theorem eLen_eq (P : Instance) (k : ℕ) {u : ℕ} (hu : u < NN P k) :
    eLen (firsts (memL P)) (NN P k) (total P) u = (blk P k u).length := by
  rw [eLen, cntL_eq, blk, if_pos hu, length_elemBlk P k hu]

theorem sLen_eq (P : Instance) (k : ℕ) {j : ℕ} (hj : j < P.m) :
    sLen (offList P) j = (blk P k (NN P k + j)).length := by
  rw [sLen, offList_getD P (by omega), offList_getD P (by omega), blk, if_neg (by omega),
    Nat.add_sub_cancel_left, length_setBlk P hj]

theorem eBlk_eq (P : Instance) (k : ℕ) {u : ℕ} (hu : u < NN P k) :
    eBlkL (firsts (memL P)) (ownL P) (NN P k) (total P) u = blk P k u := by
  rw [blk, if_pos hu, eBlkL, elemBlk, setsOfL]
  congr 1
  have : ((List.range (total P)).filter fun p => (firsts (memL P)).getD p 0 = u) =
      (List.range (total P)).filter fun p => fst P p = u := by
    refine List.filter_congr fun p hp => ?_
    rw [WDFinal.firsts_getD P (List.mem_range.mp hp)]
  rw [this]
  rfl

theorem sBlk_eq (P : Instance) (k : ℕ) (j : ℕ) :
    sBlkL (firsts (memL P)) (ownL P) (total P) j = blk P k (NN P k + j) := by
  rw [blk, if_neg (by omega), Nat.add_sub_cancel_left, sBlkL, setBlk]
  have : ((List.range (total P)).filter fun p => (ownL P).getD p 0 = j) =
      (List.range (total P)).filter fun p => own P p = j := rfl
  rw [this]
  refine List.map_congr_left fun p hp => ?_
  simp only [List.mem_filter, List.mem_range] at hp
  exact WDFinal.firsts_getD P hp.1

theorem psum_eLen (P : Instance) (k : ℕ) {i : ℕ} (hi : i ≤ NN P k) :
    psum (eLen (firsts (memL P)) (NN P k) (total P)) i = pre (blk P k) i := by
  rw [pre_eq_psum]; exact psum_congr fun u hu => eLen_eq P k (by omega)

theorem psum_sLen (P : Instance) (k : ℕ) {j : ℕ} (hj : j ≤ P.m) :
    psum (eLen (firsts (memL P)) (NN P k) (total P)) (NN P k) + psum (sLen (offList P)) j =
      pre (blk P k) (NN P k + j) := by
  rw [psum_eLen P k le_rfl, pre_eq_psum, pre_eq_psum, psum_add]
  congr 1
  exact psum_congr fun i hi => sLen_eq P k (by omega)

/-- **The program writes the word of the reduction.** -/
theorem dsOut_eq (P : Instance) (k : ℕ) :
    dsOut P k = dsList (firsts (memL P)) (ownL P) (offList P) (NN P k) P.m (total P) (kk P k) := by
  have hoffs : (List.range (NV P k + 1)).map (pre (blk P k)) =
      0 :: ((List.range (NN P k)).map (fun u => psum (eLen (firsts (memL P)) (NN P k) (total P))
        (u + 1)) ++ (List.range P.m).map (fun j => psum (eLen (firsts (memL P)) (NN P k)
          (total P)) (NN P k) + psum (sLen (offList P)) (j + 1))) := by
    rw [List.range_succ_eq_map, List.map_cons, pre_zero, List.map_map]
    congr 1
    rw [NV, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun u hu => ?_
      simp only [Function.comp]
      rw [psum_eLen P k (by have := List.mem_range.mp hu; omega)]
    · refine List.map_congr_left fun j hj => ?_
      simp only [Function.comp]
      rw [psum_sLen P k (by have := List.mem_range.mp hj; omega)]
      rfl
  have htgt : (List.range (NV P k)).flatMap (blk P k) =
      (List.range (NN P k)).flatMap (eBlkL (firsts (memL P)) (ownL P) (NN P k) (total P)) ++
        (List.range P.m).flatMap (sBlkL (firsts (memL P)) (ownL P) (total P)) := by
    rw [NV, List.range_add, List.flatMap_append, List.flatMap_map]
    congr 1
    · exact List.flatMap_congr fun u hu => (eBlk_eq P k (List.mem_range.mp hu)).symm
    · exact List.flatMap_congr fun j _ => (sBlk_eq P k j).symm
  rw [dsOut, dsGraphWord, csrWord, hoffs, htgt, dsList, NV, MV]
  simp

/-! ## Empty sets, as the program tests them -/

theorem emp_iff (P : Instance) : Emp (offList P) P.m ↔ ¬ NoEmpty P := by
  constructor
  · rintro ⟨j, hj, he⟩ hne
    rw [offList_getD P (by omega), offList_getD P (by omega)] at he
    have := hne j hj; omega
  · intro h
    by_contra hc
    apply h
    intro j hj
    have hle := offs_mono P (show j ≤ j + 1 by omega)
    rcases Nat.lt_or_ge (offs P j) (offs P (j + 1)) with h1 | h1
    · exact h1
    · exact absurd ⟨j, hj, by rw [offList_getD P (by omega), offList_getD P (by omega)]; omega⟩ hc

theorem off_eq {P : Instance} {k : ℕ} {σ : Env} (h : Parsed P k σ) : σ.arrs "hs_off" = offList P := by
  obtain ⟨-, -, -, hol, hoff, -, -, -, -⟩ := h
  refine WDFinal.list_eq_of_getD (by rw [hol]; simp [offList]) fun i hi => ?_
  rw [hol] at hi
  rw [hoff i (by omega), offList_getD P (by omega)]

/-! ## The run -/

/-- The cost bound of the program. -/
def Kds (P : Instance) (k : ℕ) : ℕ :=
  Kread P k + (24 * P.m + 8) + 12 + Kmain (total P) P.m (NN P k)

/-- The value bound all numbers of the run stay below. -/
theorem vals (P : Instance) (k : ℕ) :
    (NN P k) * (NN P k) + NN P k + P.m + total P + 2 + 2 * MV P k ≤
      16 * ((word P k).length + 1) ^ 2 := by
  obtain ⟨h1, -, -, -, -⟩ := dims P k
  generalize (word P k).length = L at h1
  have hN : NN P k ≤ 2 * L := by unfold NN kk; omega
  have hsq : NN P k * NN P k ≤ (2 * L) * (2 * L) := Nat.mul_le_mul hN hN
  have hM : 2 * MV P k ≤ NN P k * NN P k + 2 * total P := by
    unfold MV
    have := Nat.div_mul_le_self (NN P k * (NN P k - 1)) 2
    have : NN P k * (NN P k - 1) ≤ NN P k * NN P k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  have : (2 * L) * (2 * L) + 2 * L + L + L + 2 + (2 * L) * (2 * L) + 2 * L ≤ 16 * (L + 1) ^ 2 := by
    nlinarith
  omega

theorem sq_lt_pow (L : ℕ) : 16 * (L + 1) ^ 2 < 2 ^ (2 * L + 8) := by
  have h : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  have h2 : (L + 1) ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left h 2
  have h3 : (2 ^ L) ^ 2 = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  have h4 : 2 ^ (2 * L + 8) = 256 * 2 ^ (2 * L) := by ring
  have h5 : 0 < 2 ^ (2 * L) := Nat.two_pow_pos _
  omega

theorem dsProg_run {B : ℕ} (P : Instance) (k L : ℕ)
    (hB : 2 ^ (2 * (word P k).length + 8) ≤ B) :
    ∃ σ', Run B dsProg (initEnv (WDFinal.extWD P) (L :: word P k)) σ' (Kds P k) ∧
      σ'.out = redDS (word P k) := by
  classical
  obtain ⟨hmT, hn, hm, hk, -⟩ := dims P k
  have hv := vals P k
  have hsq := sq_lt_pow (word P k).length
  have hL2 : (word P k).length < 2 ^ (word P k).length := Nat.lt_two_pow_self
  have hpow : 2 ^ ((word P k).length + 3) ≤ 2 ^ (2 * (word P k).length + 8) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB8 : 2 ^ ((word P k).length + 3) = 8 * 2 ^ (word P k).length := by ring
  have hfits : Fits P k B := fits_of_le P k (hpow.trans hB)
  obtain ⟨σ1, r1, hP1, hout1, harr1, -⟩ :=
    (readHS_spec (B := B) P k L hfits).run (σ := initEnv (WDFinal.extWD P) (L :: word P k))
      ⟨rfl, WDFinal.fresh_initWD P _⟩
  have hPar := hP1
  obtain ⟨⟨hn1, hm1, hk1⟩, ht1, -, -⟩ := hP1
  have hmem1 := WDFinal.mem_eq hPar
  have hown1 := WDFinal.own_eq hPar
  have hoff1 := off_eq hPar
  have hf1 : (σ1.arrs "fp_f").length = total P := by
    rw [harr1 _ (by decide) (by decide) (by decide)]; simp [initEnv, WDFinal.extWD]
  have hOFFB : ∀ v ∈ offList P, v < B := by
    intro v hv'
    simp only [offList, List.mem_map, List.mem_range] at hv'
    obtain ⟨i, hi, rfl⟩ := hv'
    have := offs_mono P (show i ≤ P.m by omega)
    unfold total at hmT; omega
  obtain ⟨σ2, r2, hem2, ha2, -, ho2, hv2⟩ :=
    (emCheck_spec (B := B) (offList P) P.m (by simp [offList]) hOFFB (by omega)).run (σ := σ1)
      ⟨hoff1, hm1⟩
  have hn2 : σ2.vars "hs_n" = P.n := by rw [hv2 _ (by decide) (by decide), hn1]
  have hk2 : σ2.vars "hs_k" = k := by rw [hv2 _ (by decide) (by decide), hk1]
  rw [redDS_word]
  have hc1 : (Cond.lt (V "hs_n") (V "hs_k")).evalB B σ2 = some (decide (P.n < k)) := by
    rw [evalB_condLt (evalB_var (by rw [hn2]; omega)) (evalB_var (by rw [hk2]; omega)), hn2, hk2]
  by_cases hkn : k ≤ P.n
  · have hc1' : (Cond.lt (V "hs_n") (V "hs_k")).evalB B σ2 = some false := by
      rw [hc1]; simp; omega
    have hc2 : (Cond.eq (V "ds_em") (.lit 1)).evalB B σ2 =
        some (decide (Emp (offList P) P.m)) := by
      rw [evalB_condEq (evalB_var (by rw [hem2]; split_ifs <;> omega)) (evalB_lit (by omega)),
        hem2]
      by_cases he : Emp (offList P) P.m <;> simp [he]
    by_cases hne : NoEmpty P
    · rw [if_pos ⟨hkn, hne⟩]
      have he : ¬ Emp (offList P) P.m := fun h => (emp_iff P).mp h hne
      rw [decide_eq_false he] at hc2
      have hlB : ∀ v ∈ memL P, v < B := by
        intro v hv'
        obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv'
        rw [← List.getD_eq_getElem _ 0 hp]
        have := memL_lt P (by rwa [length_memL] at hp); omega
      have hS := psum_sLen P k (le_refl P.m)
      rw [show NN P k + P.m = NV P k from rfl, pre_blk] at hS
      obtain ⟨σ3, r3, hout3⟩ :=
        (dsMain_spec (B := B) (memL P) (ownL P) (offList P) k P.m
          (by rw [length_ownL, length_memL]) (by simp [offList]) hlB
          (fun v hv' => by have := WDFinal.firsts_lt P hv'; omega)
          (fun v hv' => by
            have := WDFinal.ownL_mem_lt P hv'; rw [length_memL]
            have : total P + min k P.m + v ≤ NN P k + P.m := by unfold NN kk; omega
            omega)
          (fun v hv' => by have := WDFinal.ownL_mem_lt P hv'; omega) hOFFB
          (by rw [length_memL]; omega)
          (by rw [length_memL]; have : total P + min k P.m = NN P k := rfl; rw [this]; omega)
          (by rw [length_memL]; have : total P + min k P.m = NN P k := rfl; rw [this, hS]; omega)
          ).run (σ := σ2)
          ⟨hk2, by rw [hv2 _ (by decide) (by decide), hm1],
            by rw [hv2 _ (by decide) (by decide), ht1, length_memL],
            by rw [ha2, hmem1], by rw [ha2, hown1], by rw [ha2, hoff1],
            by rw [ha2, hf1, length_memL]⟩
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hc1' (Run.ite_false hc2 r3)))).mono ?_, ?_⟩
      · have e : Kmain (memL P).length P.m ((memL P).length + min k P.m) =
            Kmain (total P) P.m (NN P k) := by rw [length_memL]; rfl
        rw [e] at r3
        simp only [Kds, size_condLt, size_condEq, size_var, size_lit]
        omega
      · rw [hout3, ho2, hout1, dsOut_eq]
        simp only [length_memL]
        rfl
    · rw [if_neg (fun h => hne h.2)]
      have he : Emp (offList P) P.m := by
        by_contra h; exact hne (by by_contra h'; exact h ((emp_iff P).mpr h'))
      rw [decide_eq_true he] at hc2
      obtain ⟨σ3, r3, hout3⟩ := (writeNoDS_spec (B := B) (by omega)).run (σ := σ2) trivial
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hc1' (Run.ite_true hc2 r3)))).mono ?_, ?_⟩
      · simp only [Kds, Kmain, size_condLt, size_condEq, size_var, size_lit]; omega
      · rw [hout3, ho2, hout1]; rfl
  · rw [if_neg (fun h => hkn h.1)]
    have hc1' : (Cond.lt (V "hs_n") (V "hs_k")).evalB B σ2 = some true := by
      rw [hc1]; simp; omega
    obtain ⟨σ3, r3, hout3⟩ := (writeNoDS_spec (B := B) (by omega)).run (σ := σ2) trivial
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hc1' r3))).mono ?_, ?_⟩
    · simp only [Kds, Kmain, size_condLt, size_var]; omega
    · rw [hout3, ho2, hout1]; rfl

/-! ## Compilation and bounds -/

/-- The scalars of the program. -/
def dsVars : List String :=
  parseVars ++ Firsts.prepVars ++
    ["ds_em", "ds_j", "ds_u", "ds_p", "ds_c", "ds_o", "ds_v", "ds_N", "ds_M"]

def layout : Layout := ⟨dsVars, WDProg.wdArrs, 8⟩

set_option maxHeartbeats 4000000 in
theorem dsProg_ok : Com.Ok layout dsProg := by
  refine ⟨Param.readHS_ok layout (fun y hy => by simp [layout, dsVars, hy])
    (fun a ha => by
      simp only [Param.parseArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp [layout, WDProg.wdArrs]) (by simp [layout]), ?_⟩
  simp [layout, dsVars, WDProg.wdArrs, parseVars, Firsts.prepVars, emCheck, emLoop, emBody,
    writeNoDS, dsMain, prep, prepHead, firstsLoop, firstBody, scanLoop, scanBody, dsHead,
    offELoop, offEBody, cntLoop, cntBody, offSLoop, offSBody, tgtELoop, tgtEBody, vLoop, vBody,
    pLoop, pBody, tgtSLoop, tgtSBody, sLoop, sBody, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem arith_ds (L T m NN : ℕ) (hT : T ≤ L) (hm : m ≤ L) (hN : NN ≤ 2 * L) :
    (20 + ((34 * T + 24) * T + 6)) + 40 + ((24 * T + 64) * NN + 6) + (24 * m + 6) +
    ((18 * NN + 24 * T + 24) * NN + 6) + ((24 * T + 14) * m + 6) + 2 + (24 * m + 8) + 12
      ≤ 500 * (L + 1) ^ 3 := by
  have h1 : (34 * T + 24) * T ≤ (34 * L + 24) * L := Nat.mul_le_mul (by omega) hT
  have h2 : (24 * T + 64) * NN ≤ (24 * L + 64) * (2 * L) := Nat.mul_le_mul (by omega) hN
  have h3 : (18 * NN + 24 * T + 24) * NN ≤ (36 * L + 24 * L + 24) * (2 * L) :=
    Nat.mul_le_mul (by omega) hN
  have h4 : (24 * T + 14) * m ≤ (24 * L + 14) * L := Nat.mul_le_mul (by omega) hm
  have h5 : (34 * L + 24) * L + (24 * L + 64) * (2 * L) + (36 * L + 24 * L + 24) * (2 * L) +
      (24 * L + 14) * L + 48 * L + 200 ≤ 500 * (L + 1) ^ 3 := by
    ring_nf; nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 2)]
  omega

theorem Kds_le (P : Instance) (k : ℕ) : Kds P k ≤ 700 * ((word P k).length + 1) ^ 3 := by
  have hr := Kread_le P k
  obtain ⟨h1, -, -, -, -⟩ := dims P k
  have hN : NN P k ≤ 2 * (word P k).length := by unfold NN kk; omega
  have := arith_ds (word P k).length (total P) P.m (NN P k) (by omega) (by omega) hN
  unfold Kds Kmain
  omega

/-- The value bound, on the tape `y = x.length :: x`. -/
def Bds (y : List ℕ) : ℕ := 2 ^ (2 * y.length + 8)

/-- The cost bound, on the tape. -/
def Kt (y : List ℕ) : ℕ := 700 * (y.length + 1) ^ 3

theorem solves : Solves layout dsProg (Tapes HittingSet.Domain) (fun y => redDS y.tail) Bds Kt := by
  refine ⟨dsProg_ok, ?_, ?_⟩
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩ v hv
    have := Param.inp_lt P k hv
    have h2 : 2 ^ ((word P k).length + 1) ≤ Bds ((word P k).length :: word P k) := by
      unfold Bds; exact Nat.pow_le_pow_right (by norm_num) (by simp only [List.length_cons]; omega)
    omega
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩
    refine ⟨WDFinal.extWD P, ?_⟩
    obtain ⟨σ', r, hout⟩ := dsProg_run (B := Bds ((word P k).length :: word P k)) P k
      (word P k).length (by unfold Bds; exact Nat.pow_le_pow_right (by norm_num) (by simp only [List.length_cons]; omega))
    refine ⟨σ', r.mono ?_, by rw [hout]; rfl⟩
    have := Kds_le P k
    have h : ((word P k).length + 1) ^ 3 ≤ ((word P k).length + 1 + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    simp only [Kt, List.length_cons]; omega

/-- The entries of the output are below `16 (L + 1)^2`. -/
theorem out_le (P : Instance) (k : ℕ) {v : ℕ} (hv : v ∈ redDS (word P k)) :
    v ≤ 16 * ((word P k).length + 1) ^ 2 := by
  classical
  have hvals := vals P k
  rw [redDS_word] at hv
  split_ifs at hv
  · rw [dsOut, dsGraphWord, csrWord] at hv
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.mem_flatMap, List.not_mem_nil, or_false] at hv
    rcases hv with (((h | h) | ⟨i, hi, rfl⟩) | ⟨u, hu, hvu⟩) | h
    · subst h; unfold NV; omega
    · subst h; omega
    · have := pre_mono (blk P k) (show i ≤ NV P k by omega)
      rw [pre_blk] at this; omega
    · have := blk_lt P k hu hvu; unfold NV at this; omega
    · subst h; unfold kk; have := dims P k; omega
  · have : v ≤ 1 := by simp [dsNo] at hv; omega
    omega

/-! ## Polynomial time -/

/-- The constant of the polynomial bound. -/
def c₂ : ℕ := 100000

theorem pow_le_c₂ (s a : ℕ) (h : a ≤ 20 * (s + 1)) : 2 ^ a ≤ 2 ^ (c₂ * (s + 1) ^ 3) := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have : s + 1 ≤ (s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold c₂; omega

theorem polyTime : PolyTimeOn HittingSet.Domain redDS := by
  refine polyTimeOn_of_solves (c₀ := c₂) (d := 3) solves ?_ ?_ ?_
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    generalize bitSize (word P k) = s at hlen ⊢
    have hB : Bds ((word P k).length :: word P k) = 2 ^ (2 * (word P k).length + 10) := by
      simp [Bds]; ring_nf
    rw [hB]
    generalize (word P k).length = L at hlen ⊢
    have h32 : 64 ≤ 2 ^ (2 * L + 10) := by
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ (2 * L + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (2 ^ (2 * L + 10)) ≤ 2 ^ (2 * L + 13) := by
      simp only [Layout.span, layout, dsVars, WDProg.wdArrs, parseVars, Firsts.prepVars,
        List.length_cons, List.length_nil, List.length_append]
      have : 2 ^ (2 * L + 13) = 8 * 2 ^ (2 * L + 10) := by ring
      omega
    have hle : 2 ^ (2 * L + 13) ≤ 2 ^ (c₂ * (s + 1) ^ 3) := pow_le_c₂ s _ (by omega)
    have h69 : 2 ^ (2 * L + 10) ≤ 2 ^ (2 * L + 13) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (h69.trans hle) (hspan.trans hle)
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    simp only [Kt, List.length_cons, Layout.const]
    generalize bitSize (word P k) = s at hlen ⊢
    generalize (word P k).length = L at hlen ⊢
    have h1 : (L + 1 + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * (s + 1)) ^ 3 = 8 * (s + 1) ^ 3 := by ring
    have h3 : 1 ≤ (s + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold c₂
    omega
  · rintro x ⟨P, k, rfl⟩ v hv
    have hlen := length_le_bitSize (word P k)
    have h1 := out_le P k hv
    have h2 := sq_lt_pow (word P k).length
    have h3 : 2 ^ (2 * (word P k).length + 8) ≤ 2 ^ (c₂ * (bitSize (word P k) + 1) ^ 3) :=
      pow_le_c₂ _ _ (by omega)
    omega

/--
---
conclusion: Lax496464.WH_E3_DominatingSet.hittingSet_le_dominatingSet
---
**`p-Hitting-Set ≤fpt p-Dominating-Set`** (Flum–Grohe, Example 2.7). On the word of `(P, k)` with
`k ≤ n` and no empty set, the reduction writes the graph of the compressed instance — its elements
(the first occurrences of the members and `min k m` spare elements) form a clique, and each set is a
vertex joined to its elements — with parameter `min k m`; otherwise a fixed no-instance. The new
parameter is at most `k + 1`, and an IMP+ program computes the reduction within
`100000 (|x| + 1)^3` steps.
-/
theorem hittingSet_le_dominatingSet : HittingSet ≤ᶠᵖᵗ DominatingSet :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTime

example : type_of% @Lax496464.WH_E3_DominatingSet.hittingSet_le_dominatingSet :=
  hittingSet_le_dominatingSet

end Lax496464Proofs.WHierarchy.HittingSet.DSFinal
