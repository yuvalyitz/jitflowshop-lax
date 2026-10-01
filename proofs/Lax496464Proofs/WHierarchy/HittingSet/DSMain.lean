import Lax496464Proofs.WHierarchy.HittingSet.DSProg2
import Lax496464Proofs.WHierarchy.HittingSet.Firsts
import Lax496464Proofs.WHierarchy.HittingSet.Parse

/-! # Hitting Set to Dominating Set: the whole program

`dsMain` writes the graph word `[N, M, 0, offsets…, targets…]` followed by `min k m`; `dsProg` reads
the word, tests for an empty set, and writes either the graph word or the fixed no-instance
`[0, 0, 0, 1]`. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V bump)
open Lax496464Proofs.WHierarchy.HittingSet.Parse Lax496464Proofs.WHierarchy.HittingSet.Firsts
open Lax496464Proofs.WHierarchy.HittingSet.DSProg1 Lax496464Proofs.WHierarchy.HittingSet.DSProg2

/-- The header: `ds_N := NN + m`, `ds_M := NN (NN - 1) / 2 + T`, written, then the offset `0`. -/
def dsHead : Com :=
  .seq (.assign "ds_N" (.add (V "fp_NN") (V "hs_m")))
  (.seq (.assign "ds_M" (.add (.div (.mul (V "fp_NN") (.sub (V "fp_NN") (.lit 1))) (.lit 2))
    (V "hs_t")))
  (.seq (.write (V "ds_N")) (.seq (.write (V "ds_M")) (.seq (.write (.lit 0))
    (.assign "ds_o" (.lit 0))))))

/-- Everything after the reader, for an instance with `k ≤ n` and no empty set. -/
def dsMain : Com :=
  .seq prep (.seq dsHead (.seq offELoop (.seq offSLoop (.seq tgtELoop (.seq tgtSLoop
    (.write (V "fp_kk")))))))

/-- The fixed no-instance. -/
def writeNoDS : Com :=
  .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1))))

/-- **The program of the reduction.** -/
def dsProg : Com :=
  .seq readHS (.seq emCheck (.ite (.lt (V "hs_n") (V "hs_k")) writeNoDS
    (.ite (.eq (V "ds_em") (.lit 1)) writeNoDS dsMain)))

theorem writeNoDS_spec {B : ℕ} (hB : 1 < B) :
    Spec B (fun _ => True) writeNoDS (fun σ σ' => σ'.out = σ.out ++ [0, 0, 0, 1]) 8 := by
  run_vcg
  simp

theorem dsHead_spec {B : ℕ} (NN m T : ℕ) (hB : NN * NN + NN + m + T + 2 < B) :
    Spec B (fun σ => σ.vars "fp_NN" = NN ∧ σ.vars "hs_m" = m ∧ σ.vars "hs_t" = T) dsHead
      (fun σ σ' => σ'.out = σ.out ++ [NN + m, NN * (NN - 1) / 2 + T, 0] ∧
        σ'.vars "ds_o" = 0 ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        ∀ y, y ≠ "ds_N" → y ≠ "ds_M" → y ≠ "ds_o" → σ'.vars y = σ.vars y) 40 := by
  have h1 : NN * (NN - 1) ≤ NN * NN := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : NN * (NN - 1) / 2 ≤ NN * (NN - 1) := Nat.div_le_self _ _
  run_vcg
  all_goals (simp only [Env.setVar] at *; simp at *)
  all_goals
    have hN : σ.vars "fp_NN" = NN := ‹_›
    have hm : σ.vars "hs_m" = m := ‹_›
    have ht : σ.vars "hs_t" = T := ‹_›
    simp only [hN, hm, ht]
  all_goals first
    | omega
    | (simp only [true_and]; intro y hy1 hy2 hy3; simp [hy1, hy2, hy3])

/-- What `dsMain` writes. -/
def dsList (F O OFF : List ℕ) (NN m T kk : ℕ) : List ℕ :=
  [NN + m, NN * (NN - 1) / 2 + T, 0] ++ (List.range NN).map (fun u => psum (eLen F NN T) (u + 1)) ++
    (List.range m).map (fun j => psum (eLen F NN T) NN + psum (sLen OFF) (j + 1)) ++
    (List.range NN).flatMap (eBlkL F O NN T) ++ (List.range m).flatMap (sBlkL F O T) ++ [kk]

/-- The cost of `dsMain`. -/
def Kmain (T m NN : ℕ) : ℕ :=
  (20 + ((34 * T + 24) * T + 6)) + 40 + ((24 * T + 64) * NN + 6) + (24 * m + 6) +
    ((18 * NN + 24 * T + 24) * NN + 6) + ((24 * T + 14) * m + 6) + 2

theorem dsMain_spec {B : ℕ} (l O OFF : List ℕ) (k m : ℕ)
    (hO : O.length = l.length) (hOFF : OFF.length = m + 1)
    (hlB : ∀ v ∈ l, v < B) (hFB : ∀ v ∈ firsts l, v < B)
    (hOB : ∀ v ∈ O, l.length + min k m + v < B) (hOB' : ∀ v ∈ O, v < B)
    (hOFFB : ∀ v ∈ OFF, v < B) (hB1 : l.length + k + m + 1 < B)
    (hB2 : (l.length + min k m) * (l.length + min k m) + (l.length + min k m) + m + l.length + 2 < B)
    (hS : psum (eLen (firsts l) (l.length + min k m) l.length) (l.length + min k m) +
      psum (sLen OFF) m < B) :
    Spec B (fun σ => σ.vars "hs_k" = k ∧ σ.vars "hs_m" = m ∧ σ.vars "hs_t" = l.length ∧
        σ.arrs "hs_mem" = l ∧ σ.arrs "hs_own" = O ∧ σ.arrs "hs_off" = OFF ∧
        (σ.arrs "fp_f").length = l.length) dsMain
      (fun σ σ' => σ'.out = σ.out ++ dsList (firsts l) O OFF (l.length + min k m) m l.length
        (min k m)) (Kmain l.length m (l.length + min k m)) := by
  intro σ ⟨hk, hm, ht, hmem, hown, hoff, hfl⟩
  set T := l.length with hT
  set NN := T + min k m with hNN
  set F := firsts l with hF
  have hFl : F.length = T := by simp [hF, firsts, hT]
  -- the compressed dimensions and the first occurrences
  obtain ⟨σ1, r1, hkk1, hNN1, hF1, ha1, -, ho1, hv1⟩ :=
    (prep_spec (B := B) l k m hlB hB1).run (σ := σ) ⟨hk, hm, ht, hmem, hfl⟩
  have v1 : ∀ y, y ∉ prepVars → σ1.vars y = σ.vars y := hv1
  have hm1 : σ1.vars "hs_m" = m := by rw [v1 _ (by decide), hm]
  have ht1 : σ1.vars "hs_t" = T := by rw [v1 _ (by decide), ht]
  -- the header
  obtain ⟨σ2, r2, ho2, hdo2, ha2, -, hv2⟩ :=
    (dsHead_spec (B := B) NN m T (by omega)).run (σ := σ1) ⟨hNN1, hm1, ht1⟩
  have v2 : ∀ y, y ≠ "ds_N" → y ≠ "ds_M" → y ≠ "ds_o" → σ2.vars y = σ1.vars y := hv2
  -- the offsets of the elements
  obtain ⟨σ3, r3, hdo3, ho3, ha3, -, hv3⟩ :=
    (offELoop_spec (B := B) F NN T hFl (by rw [hF]; exact hFB) (by omega)
      (by omega)).run (σ := σ2)
      ⟨by rw [ha2, hF1], by rw [v2 _ (by decide) (by decide) (by decide), ht1],
        by rw [v2 _ (by decide) (by decide) (by decide), hNN1], hdo2⟩
  have v3 : ∀ y, y ≠ "ds_u" → y ≠ "ds_p" → y ≠ "ds_c" → y ≠ "ds_o" → σ3.vars y = σ2.vars y :=
    hv3
  -- the offsets of the sets
  obtain ⟨σ4, r4, ho4, ha4, -, hv4⟩ :=
    (offSLoop_spec (B := B) OFF m (psum (eLen F NN T) NN) hOFF hOFFB (by omega) hS).run (σ := σ3)
      ⟨by rw [ha3, ha2, ha1 _ (by decide), hoff],
        by rw [v3 _ (by decide) (by decide) (by decide) (by decide),
          v2 _ (by decide) (by decide) (by decide), hm1], hdo3⟩
  have v4 : ∀ y, y ≠ "ds_j" → y ≠ "ds_o" → σ4.vars y = σ3.vars y := hv4
  have e4 : ∀ y, y ∉ prepVars → y ≠ "ds_N" → y ≠ "ds_M" → y ≠ "ds_o" → y ≠ "ds_u" →
      y ≠ "ds_p" → y ≠ "ds_c" → y ≠ "ds_j" → σ4.vars y = σ.vars y := by
    intro y h1 h2 h3 h4 h5 h6 h7 h8
    rw [v4 y h8 h4, v3 y h5 h6 h7 h4, v2 y h2 h3 h4, v1 y h1]
  have hNN4 : σ4.vars "fp_NN" = NN := by
    rw [v4 _ (by decide) (by decide), v3 _ (by decide) (by decide) (by decide) (by decide),
      v2 _ (by decide) (by decide) (by decide), hNN1]
  have hkk4 : σ4.vars "fp_kk" = min k m := by
    rw [v4 _ (by decide) (by decide), v3 _ (by decide) (by decide) (by decide) (by decide),
      v2 _ (by decide) (by decide) (by decide), hkk1]
  have ha4' : σ4.arrs = σ1.arrs := by rw [ha4, ha3, ha2]
  -- the neighbour lists of the elements
  obtain ⟨σ5, r5, ho5, ha5, -, hv5⟩ :=
    (tgtELoop_spec (B := B) F O NN T hFl (by rw [hO]) (by rw [hF]; exact hFB) hOB
      (by omega)).run (σ := σ4)
      ⟨by rw [ha4', hF1], by rw [ha4', ha1 _ (by decide), hown], hNN4,
        by rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), ht]⟩
  have v5 : ∀ y, y ≠ "ds_u" → y ≠ "ds_v" → y ≠ "ds_p" → σ5.vars y = σ4.vars y := hv5
  -- the neighbour lists of the sets
  obtain ⟨σ6, r6, ho6, ha6, -, hv6⟩ :=
    (tgtSLoop_spec (B := B) F O T m hFl (by rw [hO]) (by rw [hF]; exact hFB) hOB'
      (by omega)).run (σ := σ5)
      ⟨by rw [ha5, ha4', hF1], by rw [ha5, ha4', ha1 _ (by decide), hown],
        by rw [v5 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide), ht],
        by rw [v5 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide), hm]⟩
  have hkk6 : σ6.vars "fp_kk" = min k m := by
    rw [hv6 _ (by decide) (by decide), v5 _ (by decide) (by decide) (by decide), hkk4]
  have r7 := Run.write (B := B) (σ := σ6) (e := V "fp_kk") (v := min k m)
    (by rw [← hkk6]; exact evalB_var (by rw [hkk6]; omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_, ?_⟩
  · have : (34 * l.length + 24) * l.length = (34 * T + 24) * T := rfl
    simp only [Kmain, size_var]; omega
  · show σ6.out ++ [min k m] = _
    rw [ho6, ho5, ho4, ho3, ho2, ho1]
    simp only [dsList, List.append_assoc]

end Lax496464Proofs.WHierarchy.HittingSet.DSMain
