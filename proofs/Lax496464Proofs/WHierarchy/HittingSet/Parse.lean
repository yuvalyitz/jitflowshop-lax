import Lax496464Proofs.WHierarchy.HittingSet.ReadNat
import Lax496464Proofs.WHierarchy.HittingSet.Form

/-! # Reading a Hitting Set word, in IMP+

`readHS` reads the tape `x.length :: word P k`: the length, then the codes of `n`, `m` and `k` into
the scalars `hs_n`, `hs_m`, `hs_k`, and then the sets. The members of all sets go one after the
other into the array `hs_mem`, the set each belongs to into `hs_own`, and the offset of each set
into `hs_off` (`Form.memL`, `Form.ownL`, `Form.offs`); `hs_t` ends as the total number of
members. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Parse

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat

/-- Store the member just read, and its set; advance. -/
def memTail : Com :=
  .seq (.store "hs_mem" (V "hs_t") (V "rn_v"))
    (.seq (.store "hs_own" (V "hs_t") (V "hs_j")) (.seq (bump "hs_t") (bump "hs_q")))

/-- Read one member. -/
def memBody : Com := .seq readNat memTail

/-- Read the members of one set. -/
def memLoop : Com := .seq (.assign "hs_q" (.lit 0)) (.while (.lt (V "hs_q") (V "hs_sz")) memBody)

/-- Record where the next set starts. -/
def setTail : Com := .seq (bump "hs_j") (.store "hs_off" (V "hs_j") (V "hs_t"))

/-- Read one set: its size, then its members. -/
def setBody : Com := .seq readNat (.seq (.assign "hs_sz" (V "rn_v")) (.seq memLoop setTail))

/-- Read the sets. -/
def setLoop : Com := .seq (.assign "hs_j" (.lit 0)) (.while (.lt (V "hs_j") (V "hs_m")) setBody)

/-- Read one number of the header into `dst`. -/
def hdrNum (dst : String) : Com := .seq readNat (.assign dst (V "rn_v"))

/-- **Read a Hitting Set word.** -/
def readHS : Com :=
  .seq (.read "hs_len")
  (.seq (hdrNum "hs_n") (.seq (hdrNum "hs_m") (.seq (hdrNum "hs_k")
  (.seq (.assign "hs_t" (.lit 0)) setLoop))))

/-! ## Small facts about arrays -/

theorem getD_set_self (l : List ℕ) {i : ℕ} (v : ℕ) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_other (l : List ℕ) {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-! ## The invariants -/

/-- The three header numbers are in place. -/
def Hdr (P : Instance) (k : ℕ) (σ : Env) : Prop :=
  σ.vars "hs_n" = P.n ∧ σ.vars "hs_m" = P.m ∧ σ.vars "hs_k" = k

/-- The arrays: offsets up to set `j`, members and owners up to position `t`. -/
def Arrs (P : Instance) (j t : ℕ) (σ : Env) : Prop :=
  (σ.arrs "hs_off").length = P.m + 1 ∧ (∀ i ≤ j, (σ.arrs "hs_off").getD i 0 = offs P i) ∧
  (σ.arrs "hs_mem").length = total P ∧
    (∀ p < t, (σ.arrs "hs_mem").getD p 0 = (memL P).getD p 0) ∧
  (σ.arrs "hs_own").length = total P ∧
    (∀ p < t, (σ.arrs "hs_own").getD p 0 = (ownL P).getD p 0)

/-- Part-way through the members of set `j`. -/
def MemInv (P : Instance) (k j : ℕ) (σ : Env) : Prop :=
  Hdr P k σ ∧ σ.vars "hs_j" = j ∧ σ.vars "hs_sz" = (mlist P j).length ∧
    σ.vars "hs_q" ≤ (mlist P j).length ∧ σ.vars "hs_t" = offs P j + σ.vars "hs_q" ∧
    σ.inp = ((mlist P j).drop (σ.vars "hs_q")).flatMap bitsNat ++ restSets P (j + 1) ∧
    Arrs P j (σ.vars "hs_t") σ

/-- Part-way through the sets. -/
def SetInv (P : Instance) (k : ℕ) (σ : Env) : Prop :=
  Hdr P k σ ∧ σ.vars "hs_j" ≤ P.m ∧ σ.vars "hs_t" = offs P (σ.vars "hs_j") ∧
    σ.inp = restSets P (σ.vars "hs_j") ∧ Arrs P (σ.vars "hs_j") (σ.vars "hs_t") σ

/-- The value bound the reader needs. -/
def Fits (P : Instance) (k B : ℕ) : Prop := P.n + P.m + k + total P + 2 < B

/-- The size bound the reader's cost is stated with. -/
def szB (P : Instance) (k : ℕ) : ℕ := P.n.size + P.m.size + k.size

/-- The cost of one `readNat` on this word. -/
def Rn (P : Instance) (k : ℕ) : ℕ := 32 * szB P k + 20

theorem total_le_n_of_lt (P : Instance) {j : ℕ} (hj : j < P.m) :
    offs P j + (mlist P j).length ≤ total P := by
  rw [← offs_succ]; exact offs_mono P (by omega)

theorem length_mlist_le_total (P : Instance) {j : ℕ} (hj : j < P.m) :
    (mlist P j).length ≤ total P := by
  have := total_le_n_of_lt P hj; omega

/-! ## One member -/

theorem memTail_run {B : ℕ} (σ : Env) (ht : σ.vars "hs_t" < (σ.arrs "hs_mem").length)
    (ht' : σ.vars "hs_t" < (σ.arrs "hs_own").length) (htB : σ.vars "hs_t" + 1 < B)
    (hqB : σ.vars "hs_q" + 1 < B) (hvB : σ.vars "rn_v" < B) (hjB : σ.vars "hs_j" < B) :
    Run B memTail σ
      ((((σ.setArr "hs_mem" (σ.vars "hs_t") (σ.vars "rn_v")).setArr "hs_own" (σ.vars "hs_t")
        (σ.vars "hs_j")).setVar "hs_t" (σ.vars "hs_t" + 1)).setVar "hs_q" (σ.vars "hs_q" + 1))
      14 := by
  have r1 := Run.store (B := B) (σ := σ) (a := "hs_mem") (i := V "hs_t") (e := V "rn_v")
    (evalB_var (by omega)) (evalB_var hvB) ht
  set σ1 := σ.setArr "hs_mem" (σ.vars "hs_t") (σ.vars "rn_v") with hσ1
  have h1t : σ1.vars "hs_t" = σ.vars "hs_t" := rfl
  have h1j : σ1.vars "hs_j" = σ.vars "hs_j" := rfl
  have h1q : σ1.vars "hs_q" = σ.vars "hs_q" := rfl
  have h1o : (σ1.arrs "hs_own").length = (σ.arrs "hs_own").length := by
    simp [hσ1, Env.setArr]
  have r2 := Run.store (B := B) (σ := σ1) (a := "hs_own") (i := V "hs_t") (e := V "hs_j")
    (evalB_var (by rw [h1t]; omega)) (evalB_var (by rw [h1j]; omega)) (by rw [h1o, h1t]; exact ht')
  set σ2 := σ1.setArr "hs_own" (σ1.vars "hs_t") (σ1.vars "hs_j") with hσ2
  have h2t : σ2.vars "hs_t" = σ.vars "hs_t" := rfl
  have h2q : σ2.vars "hs_q" = σ.vars "hs_q" := rfl
  have r3 := Run.assign (B := B) (σ := σ2) (x := "hs_t") (e := .add (V "hs_t") (.lit 1))
    (v := σ.vars "hs_t" + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ2) (evalB_var (x := "hs_t") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h2t]; simp; omega)
      rw [h2t] at this; simpa using this)
  set σ3 := σ2.setVar "hs_t" (σ.vars "hs_t" + 1) with hσ3
  have h3q : σ3.vars "hs_q" = σ.vars "hs_q" := by simp [hσ3, Env.setVar, h2q]
  have r4 := Run.assign (B := B) (σ := σ3) (x := "hs_q") (e := .add (V "hs_q") (.lit 1))
    (v := σ.vars "hs_q" + 1) (by
      have := evalB_bin (B := B) (op := .add) (σ := σ3) (evalB_var (x := "hs_q") (by omega))
        (evalB_lit (n := 1) (by omega)) (by rw [h3q]; simp; omega)
      rw [h3q] at this; simpa using this)
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by simp)

theorem memBody_spec {B : ℕ} (P : Instance) (k : ℕ) {j : ℕ} (hj : j < P.m) (hB : Fits P k B) :
    Spec B (fun σ => MemInv P k j σ ∧ σ.vars "hs_q" < (mlist P j).length) memBody
      (fun σ σ' => MemInv P k j σ' ∧ σ'.vars "hs_q" = σ.vars "hs_q" + 1) (Rn P k + 14) := by
  intro σ ⟨⟨hH, hj0, hsz, hq, ht, hinp, hA⟩, hlt⟩
  obtain ⟨hn, hm, hk⟩ := hH
  obtain ⟨hol, hoff, hml, hmem, hwl, hown⟩ := hA
  set q := σ.vars "hs_q" with hq_def
  set a := (mlist P j).getD q 0 with ha_def
  have hTj := total_le_n_of_lt P hj
  have ha_mem : a ∈ mlist P j := by
    rw [ha_def, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  have ha_n : a < P.n := mlist_lt P ha_mem
  have hsize : a.size ≤ P.n.size := Nat.size_le_size ha_n.le
  have hB' := hB
  unfold Fits at hB'
  have hsa : a.size ≤ a := size_le_self a
  -- the input starts with the code of the member
  have hinp' : σ.inp = bitsNat a ++ (((mlist P j).drop (q + 1)).flatMap bitsNat ++
      restSets P (j + 1)) := by
    rw [hinp, List.drop_eq_getElem_cons hlt, List.flatMap_cons, List.append_assoc]
    rw [ha_def, List.getD_eq_getElem _ _ hlt]
  obtain ⟨σ1, r1, hv1, hinp1, hout1, harr1, hvar1⟩ :=
    (readNat_spec (B := B) a (((mlist P j).drop (q + 1)).flatMap bitsNat ++ restSets P (j + 1))
      (by omega) (by omega)).run hinp'
  have v1 : ∀ y, y ∉ rnVars → σ1.vars y = σ.vars y := hvar1
  have e_t : σ1.vars "hs_t" = σ.vars "hs_t" := v1 _ (by decide)
  have e_q : σ1.vars "hs_q" = q := v1 _ (by decide)
  have e_j : σ1.vars "hs_j" = j := by rw [v1 _ (by decide), hj0]
  have hpos := pos_facts P hj hlt
  have ht_lt : σ.vars "hs_t" < total P := by rw [ht]; exact hpos.1
  have r2 := memTail_run (B := B) σ1 (by rw [e_t, harr1, hml]; exact ht_lt)
    (by rw [e_t, harr1, hwl]; exact ht_lt) (by rw [e_t]; omega) (by rw [e_q]; omega)
    (by rw [hv1]; omega) (by rw [e_j]; omega)
  have hsz' : a.size ≤ szB P k := by unfold szB; omega
  set σ' := (((σ1.setArr "hs_mem" (σ1.vars "hs_t") (σ1.vars "rn_v")).setArr "hs_own"
    (σ1.vars "hs_t") (σ1.vars "hs_j")).setVar "hs_t" (σ1.vars "hs_t" + 1)).setVar "hs_q"
    (σ1.vars "hs_q" + 1) with hσ'
  have f_var : ∀ y, y ≠ "hs_t" → y ≠ "hs_q" → σ'.vars y = σ1.vars y := by
    intro y h1 h2; simp [hσ', Env.setVar, Env.setArr, h1, h2]
  have f_t : σ'.vars "hs_t" = σ.vars "hs_t" + 1 := by simp [hσ', Env.setVar, Env.setArr, e_t]
  have f_q : σ'.vars "hs_q" = q + 1 := by simp [hσ', Env.setVar, Env.setArr, e_q]
  have f_mem : σ'.arrs "hs_mem" = (σ.arrs "hs_mem").set (σ.vars "hs_t") a := by
    simp [hσ', Env.setVar, Env.setArr, e_t, hv1, harr1]
  have f_own : σ'.arrs "hs_own" = (σ.arrs "hs_own").set (σ.vars "hs_t") j := by
    simp [hσ', Env.setVar, Env.setArr, e_t, e_j, harr1]
  have f_off : σ'.arrs "hs_off" = σ.arrs "hs_off" := by
    simp [hσ', Env.setVar, Env.setArr, harr1]
  have f_inp : σ'.inp = σ1.inp := by simp [hσ', Env.setVar, Env.setArr]
  clear_value σ'
  refine ⟨σ', (r1.seq r2).mono (by simp [Rn]; omega), ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [f_var _ (by decide) (by decide), v1 _ (by decide), hn]
    · rw [f_var _ (by decide) (by decide), v1 _ (by decide), hm]
    · rw [f_var _ (by decide) (by decide), v1 _ (by decide), hk]
    · rw [f_var _ (by decide) (by decide), e_j]
    · rw [f_var _ (by decide) (by decide), v1 _ (by decide), hsz]
    · rw [f_q]; omega
    · rw [f_t, f_q, ht]; omega
    · rw [f_q, f_inp, hinp1]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f_off, hol]
      · intro i hi; rw [f_off]; exact hoff i hi
      · rw [f_mem, List.length_set, hml]
      · intro p hp
        rw [f_t] at hp
        rw [f_mem]
        rcases Nat.lt_or_ge p (σ.vars "hs_t") with hp' | hp'
        · rw [getD_set_other _ _ (by omega)]; exact hmem p hp'
        · have hpe : p = σ.vars "hs_t" := by omega
          rw [hpe, getD_set_self _ _ (by rw [hml]; exact ht_lt), ht, hpos.2.1]
      · rw [f_own, List.length_set, hwl]
      · intro p hp
        rw [f_t] at hp
        rw [f_own]
        rcases Nat.lt_or_ge p (σ.vars "hs_t") with hp' | hp'
        · rw [getD_set_other _ _ (by omega)]; exact hown p hp'
        · have hpe : p = σ.vars "hs_t" := by omega
          rw [hpe, getD_set_self _ _ (by rw [hwl]; exact ht_lt), ht, hpos.2.2]
  · rw [f_q]

theorem memLoop_spec {B : ℕ} (P : Instance) (k : ℕ) {j : ℕ} (hj : j < P.m) (hB : Fits P k B) :
    Spec B (fun σ => MemInv P k j (σ.setVar "hs_q" 0)) memLoop
      (fun _ σ' => MemInv P k j σ' ∧ σ'.vars "hs_q" = (mlist P j).length)
      ((Rn P k + 18) * (mlist P j).length + 6) := by
  have hl := length_mlist_le_total P hj
  have hB' := hB
  unfold Fits at hB'
  exact Spec.forRangeZero "hs_q" "hs_sz" (MemInv P k j) (mlist P j).length (Rn P k + 14)
    (by omega) (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (memBody_spec P k hj hB)

/-! ## One set -/

theorem setTail_run {B : ℕ} (σ : Env) (hj : σ.vars "hs_j" + 1 < (σ.arrs "hs_off").length)
    (hjB : σ.vars "hs_j" + 1 < B) (htB : σ.vars "hs_t" < B) :
    Run B setTail σ
      ((σ.setVar "hs_j" (σ.vars "hs_j" + 1)).setArr "hs_off" (σ.vars "hs_j" + 1) (σ.vars "hs_t"))
      7 := by
  have r1 := Run.assign (B := B) (σ := σ) (x := "hs_j") (e := .add (V "hs_j") (.lit 1))
    (v := σ.vars "hs_j" + 1) (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega))
      (by simp; omega))
  set σ1 := σ.setVar "hs_j" (σ.vars "hs_j" + 1) with hσ1
  have h1j : σ1.vars "hs_j" = σ.vars "hs_j" + 1 := by simp [hσ1, Env.setVar]
  have h1t : σ1.vars "hs_t" = σ.vars "hs_t" := by simp [hσ1, Env.setVar]
  have h1o : σ1.arrs "hs_off" = σ.arrs "hs_off" := rfl
  have r2 := Run.store (B := B) (σ := σ1) (a := "hs_off") (i := V "hs_j") (e := V "hs_t")
    (evalB_var (by rw [h1j]; omega)) (evalB_var (by rw [h1t]; omega))
    (by rw [h1o, h1j]; exact hj)
  rw [h1j, h1t] at r2
  exact (r1.seq r2).mono (by simp)

/-- The cost of reading one set. -/
def Kset (P : Instance) (k : ℕ) : ℕ := Rn P k + (Rn P k + 18) * total P + 15

theorem setBody_spec {B : ℕ} (P : Instance) (k : ℕ) (hB : Fits P k B) :
    Spec B (fun σ => SetInv P k σ ∧ σ.vars "hs_j" < P.m) setBody
      (fun σ σ' => SetInv P k σ' ∧ σ'.vars "hs_j" = σ.vars "hs_j" + 1) (Kset P k) := by
  intro σ ⟨⟨hH, hjm, ht, hinp, hA⟩, hlt⟩
  obtain ⟨hn, hm, hk⟩ := hH
  obtain ⟨hol, hoff, hml, hmem, hwl, hown⟩ := hA
  set j := σ.vars "hs_j" with hj_def
  set len := (mlist P j).length with hlen_def
  have hTj := total_le_n_of_lt P hlt
  have hlenT := length_mlist_le_total P hlt
  have hlen_n : len ≤ P.n := length_mlist_le P j
  have hsize : len.size ≤ P.n.size := Nat.size_le_size hlen_n
  have hsl : len.size ≤ len := size_le_self len
  have hB' := hB
  unfold Fits at hB'
  have hsz' : len.size ≤ szB P k := by unfold szB; omega
  have hinp' : σ.inp = bitsNat len ++ ((mlist P j).flatMap bitsNat ++ restSets P (j + 1)) := by
    rw [hinp, restSets_cons P hlt, setBits, List.append_assoc]
  obtain ⟨σ1, r1, hv1, hinp1, hout1, harr1, hvar1⟩ :=
    (readNat_spec (B := B) len ((mlist P j).flatMap bitsNat ++ restSets P (j + 1))
      (by omega) (by omega)).run hinp'
  have v1 : ∀ y, y ∉ rnVars → σ1.vars y = σ.vars y := hvar1
  have r2 := Run.assign (B := B) (σ := σ1) (x := "hs_sz") (e := V "rn_v") (v := len)
    (by rw [← hv1]; exact evalB_var (by rw [hv1]; omega))
  set σ2 := σ1.setVar "hs_sz" len with hσ2
  have e2 : ∀ y, y ≠ "hs_sz" → y ∉ rnVars → σ2.vars y = σ.vars y := by
    intro y h1 h2; rw [← v1 y h2]; simp [hσ2, Env.setVar, h1]
  obtain ⟨σ3, r3, ⟨⟨hn3, hm3, hk3⟩, hj3, hsz3, _, ht3, hinp3, hA3⟩, hq3⟩ :=
    (memLoop_spec (B := B) P k hlt hB).run (σ := σ2)
      ⟨⟨by simp [Env.setVar]; rw [e2 _ (by decide) (by decide), hn],
        by simp [Env.setVar]; rw [e2 _ (by decide) (by decide), hm],
        by simp [Env.setVar]; rw [e2 _ (by decide) (by decide), hk]⟩,
      by simp [Env.setVar]; rw [e2 _ (by decide) (by decide)],
      by simp [hσ2, Env.setVar, hlen_def],
      by simp [Env.setVar],
      by simp [Env.setVar]; rw [e2 _ (by decide) (by decide), ht],
      by simp [Env.setVar]; rw [hσ2]; simp [Env.setVar, hinp1],
      by
        obtain ⟨_, _, _, _, _, _⟩ := (⟨hol, hoff, hml, hmem, hwl, hown⟩ : Arrs P j (σ.vars "hs_t") σ)
        have ha2 : (σ2.setVar "hs_q" 0).arrs = σ.arrs := by
          simp [hσ2, Env.setVar, harr1]
        have ht2 : (σ2.setVar "hs_q" 0).vars "hs_t" = σ.vars "hs_t" := by
          simp [Env.setVar]; rw [e2 _ (by decide) (by decide)]
        rw [ht2]
        simp only [Arrs, ha2]
        exact ⟨hol, hoff, hml, hmem, hwl, hown⟩⟩
  obtain ⟨hol3, hoff3, hml3, hmem3, hwl3, hown3⟩ := hA3
  have ht3' : σ3.vars "hs_t" = offs P (j + 1) := by rw [ht3, hq3, offs_succ]
  have r4 := setTail_run (B := B) σ3 (by rw [hj3, hol3]; omega) (by rw [hj3]; omega)
    (by rw [ht3']; have := offs_mono P (show j + 1 ≤ P.m by omega); unfold total at hB'; omega)
  rw [hj3] at r4
  set σ' := (σ3.setVar "hs_j" (j + 1)).setArr "hs_off" (j + 1) (σ3.vars "hs_t") with hσ'
  have f_var : ∀ y, y ≠ "hs_j" → σ'.vars y = σ3.vars y := by
    intro y h1; simp [hσ', Env.setVar, Env.setArr, h1]
  have f_j : σ'.vars "hs_j" = j + 1 := by simp [hσ', Env.setVar, Env.setArr]
  have f_off : σ'.arrs "hs_off" = (σ3.arrs "hs_off").set (j + 1) (offs P (j + 1)) := by
    simp [hσ', Env.setVar, Env.setArr, ht3']
  have f_arr : ∀ a, a ≠ "hs_off" → σ'.arrs a = σ3.arrs a := by
    intro a h; simp [hσ', Env.setVar, Env.setArr, h]
  have f_inp : σ'.inp = σ3.inp := by simp [hσ', Env.setVar, Env.setArr]
  clear_value σ'
  refine ⟨σ', (r1.seq (r2.seq (r3.seq r4))).mono ?_, ?_, f_j⟩
  · have hm1 : (Rn P k + 18) * (mlist P j).length ≤ (Rn P k + 18) * total P :=
      Nat.mul_le_mul_left _ hlenT
    have hr : 32 * len.size + 20 ≤ Rn P k := by unfold Rn; omega
    simp only [Kset, size_var]
    omega
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [f_var _ (by decide), hn3]
    · rw [f_var _ (by decide), hm3]
    · rw [f_var _ (by decide), hk3]
    · rw [f_j]; omega
    · rw [f_j, f_var _ (by decide), ht3']
    · rw [f_j, f_inp, hinp3, hq3, List.drop_length, List.flatMap_nil, List.nil_append]
    · rw [f_j, f_var _ (by decide), ht3']
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f_off, List.length_set, hol3]
      · intro i hi
        rw [f_off]
        rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
        · rw [getD_set_other _ _ (by omega)]; exact hoff3 i (by omega)
        · rw [show i = j + 1 by omega, getD_set_self _ _ (by rw [hol3]; omega)]
      · rw [f_arr _ (by decide), hml3]
      · intro p hp; rw [f_arr _ (by decide)]; exact hmem3 p (by rw [ht3']; exact hp)
      · rw [f_arr _ (by decide), hwl3]
      · intro p hp; rw [f_arr _ (by decide)]; exact hown3 p (by rw [ht3']; exact hp)

theorem setLoop_spec {B : ℕ} (P : Instance) (k : ℕ) (hB : Fits P k B) :
    Spec B (fun σ => SetInv P k (σ.setVar "hs_j" 0)) setLoop
      (fun _ σ' => SetInv P k σ' ∧ σ'.vars "hs_j" = P.m) ((Kset P k + 4) * P.m + 6) := by
  have hB' := hB
  unfold Fits at hB'
  exact Spec.forRangeZero "hs_j" "hs_m" (SetInv P k) P.m (Kset P k) (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (setBody_spec P k hB)

/-! ## The whole word -/

/-- The cost of reading a word. -/
def Kread (P : Instance) (k : ℕ) : ℕ := 3 * Rn P k + 20 + (Kset P k + 4) * P.m

/-- What the reader ends with. -/
def Parsed (P : Instance) (k : ℕ) (σ : Env) : Prop :=
  Hdr P k σ ∧ σ.vars "hs_t" = total P ∧ σ.inp = [] ∧ Arrs P P.m (total P) σ

/-- The arrays the reader is started with. -/
def Fresh (P : Instance) (σ : Env) : Prop :=
  (σ.arrs "hs_off").length = P.m + 1 ∧ (σ.arrs "hs_off").getD 0 0 = 0 ∧
    (σ.arrs "hs_mem").length = total P ∧ (σ.arrs "hs_own").length = total P

/-- One number of the header: read it and copy it into `dst`. -/
theorem hdr_step {B : ℕ} (σ : Env) (dst : String) (v : ℕ) (rest : List ℕ)
    (hinp : σ.inp = bitsNat v ++ rest) (hvB : v < B) (hsB : v.size + 2 < B) :
    ∃ σ', Run B (hdrNum dst) σ σ' (32 * v.size + 22) ∧
      σ'.vars dst = v ∧ σ'.inp = rest ∧ σ'.arrs = σ.arrs ∧
      ∀ y, y ≠ dst → y ∉ rnVars → σ'.vars y = σ.vars y := by
  obtain ⟨σ1, r1, hv1, hinp1, -, harr1, hvar1⟩ := (readNat_spec (B := B) v rest hvB hsB).run hinp
  have r2 := Run.assign (B := B) (σ := σ1) (x := dst) (e := V "rn_v") (v := v)
    (by rw [← hv1]; exact evalB_var (by rw [hv1]; exact hvB))
  refine ⟨_, (r1.seq r2).mono (by simp), by simp [Env.setVar], by simp [Env.setVar, hinp1],
    by simp [Env.setVar, harr1], ?_⟩
  intro y h1 h2
  simp only [Env.setVar, if_neg h1]
  exact hvar1 y h2

theorem readHS_core {B : ℕ} (P : Instance) (k L : ℕ) (hB : Fits P k B) :
    Spec B (fun σ => σ.inp = L :: word P k ∧ Fresh P σ) readHS (fun _ σ' => Parsed P k σ')
      (Kread P k) := by
  intro σ ⟨hinp, hol, ho0, hml, hwl⟩
  have hB' := hB
  unfold Fits at hB'
  have hsn : P.n.size ≤ P.n := size_le_self _
  have hsm : P.m.size ≤ P.m := size_le_self _
  have hsk : k.size ≤ k := size_le_self _
  have r0 := Run.read (B := B) (σ := σ) (x := "hs_len") hinp
  set σ0 : Env := { σ.setVar "hs_len" L with inp := word P k } with hσ0
  have hw : σ0.inp = bitsNat P.n ++ (bitsNat P.m ++ (bitsNat k ++ restSets P 0)) := by
    rw [hσ0, word_eq]; simp
  obtain ⟨σ2, r2, h2n, hinp2, harr2, hvar2⟩ :=
    hdr_step (B := B) σ0 "hs_n" P.n _ hw (by omega) (by omega)
  obtain ⟨σ4, r4, h4m, hinp4, harr4, hvar4⟩ :=
    hdr_step (B := B) σ2 "hs_m" P.m _ hinp2 (by omega) (by omega)
  obtain ⟨σ6, r6, h6k, hinp6, harr6, hvar6⟩ :=
    hdr_step (B := B) σ4 "hs_k" k _ hinp4 (by omega) (by omega)
  have r7 := Run.assign (B := B) (σ := σ6) (x := "hs_t") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  have ha6 : σ6.arrs = σ.arrs := by rw [harr6, harr4, harr2]; rfl
  have h6n : σ6.vars "hs_n" = P.n := by
    rw [hvar6 _ (by decide) (by decide), hvar4 _ (by decide) (by decide), h2n]
  have h6m : σ6.vars "hs_m" = P.m := by rw [hvar6 _ (by decide) (by decide), h4m]
  obtain ⟨σ8, r8, hI8, hj8⟩ := (setLoop_spec (B := B) P k hB).run
    (σ := σ6.setVar "hs_t" 0)
    ⟨⟨by simp [Env.setVar, h6n], by simp [Env.setVar, h6m], by simp [Env.setVar, h6k]⟩,
      by simp [Env.setVar], by simp [Env.setVar, offs_zero], by simp [Env.setVar, hinp6],
      by
        simp only [Arrs, Env.setVar]
        simp only [ha6]
        refine ⟨hol, ?_, hml, ?_, hwl, ?_⟩
        · intro i hi; simp at hi; rw [hi, ho0, offs_zero]
        · intro p hp; simp at hp
        · intro p hp; simp at hp⟩
  obtain ⟨hH8, -, ht8, hinp8, hA8⟩ := hI8
  refine ⟨σ8, (r0.seq (r2.seq (r4.seq (r6.seq (r7.seq r8))))).mono ?_, hH8, ?_, ?_, ?_⟩
  · have h1 : 32 * P.n.size + 22 ≤ Rn P k + 2 := by unfold Rn szB; omega
    have h2 : 32 * P.m.size + 22 ≤ Rn P k + 2 := by unfold Rn szB; omega
    have h3 : 32 * k.size + 22 ≤ Rn P k + 2 := by unfold Rn szB; omega
    simp only [Kread, size_lit]
    omega
  · rw [ht8, hj8]; rfl
  · rw [hinp8, hj8, restSets_m]
  · rw [hj8, ht8] at hA8; rw [hj8] at hA8; exact hA8

/-- The scalars `readHS` assigns. -/
def parseVars : List String :=
  ["hs_len", "hs_n", "hs_m", "hs_k", "hs_t", "hs_j", "hs_sz", "hs_q", "rn_c", "rn_b", "rn_i",
    "rn_v"]

/-- **The reader.** On the tape `L :: word P k`, with the three arrays fresh, `readHS` ends with the
header in `hs_n`, `hs_m`, `hs_k`, the total number of members in `hs_t`, the arrays filled in, the
tape consumed; it writes nothing, and changes no other scalar and no other array. -/
theorem readHS_spec {B : ℕ} (P : Instance) (k L : ℕ) (hB : Fits P k B) :
    Spec B (fun σ => σ.inp = L :: word P k ∧ Fresh P σ) readHS
      (fun σ σ' => Parsed P k σ' ∧ σ'.out = σ.out ∧
        (∀ a, a ≠ "hs_off" → a ≠ "hs_mem" → a ≠ "hs_own" → σ'.arrs a = σ.arrs a) ∧
        ∀ y, y ∉ parseVars → σ'.vars y = σ.vars y) (Kread P k) := by
  refine (readHS_core P k L hB).frame.post ?_
  rintro σ σ' - ⟨hP, hvars, harrs, -, hout⟩
  refine ⟨hP, hout (by decide), ?_, ?_⟩
  · intro a h1 h2 h3
    refine harrs a ?_
    simp [readHS, hdrNum, setLoop, setBody, setTail, memLoop, memBody, memTail, readNat, onesLoop,
      digitsLoop, digitsBody, Com.warrs, h1, h2, h3]
  · intro y hy
    refine hvars y ?_
    simp only [parseVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [readHS, hdrNum, setLoop, setBody, setTail, memLoop, memBody, memTail, readNat, onesLoop,
      digitsLoop, digitsBody, Com.wvars, hy]

end Lax496464Proofs.WHierarchy.HittingSet.Parse
