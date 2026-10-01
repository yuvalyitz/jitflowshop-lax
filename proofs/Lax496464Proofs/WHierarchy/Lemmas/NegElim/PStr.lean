import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre

/-! # Phases 6–8: writing the expanded structure

`hdOut` writes the vocabulary and the size, `ltOut` the order, `symPass` the five blocks of every
old symbol. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind Lax496464Proofs.WHierarchy.Lemmas.NegElim.PSym
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre

variable {x : List ℕ} {φ : Formula}

theorem MOf_le (hd : Dom x φ) : MOf x ≤ 2 * x.length := by
  have := nT_le hd; unfold MOf nT at *; omega

theorem sq_lt_Bv (x : List ℕ) {M : ℕ} (hM : M ≤ 2 * x.length) : M * M + M + 8 < Bv x := by
  have h1 : M * M ≤ (2 * x.length) * (2 * x.length) := Nat.mul_le_mul hM hM
  have h2 : (2 * x.length) * (2 * x.length) ≤ 4 * ((x.length + 2) * (x.length + 2)) := by nlinarith
  have h3 : 64 * (x.length + 2) * (x.length + 2) = 64 * ((x.length + 2) * (x.length + 2)) := by ring
  have h4 := len_sq_le x
  unfold Bv; omega

/-! ### The vocabulary -/

/-- The invariant of `hdOut`'s loop. -/
def HI (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "s" = sOf x ∧ σ.vars "M" = MOf x ∧ σ.vars "i" ≤ sOf x ∧
    σ.out = out0 ++ (List.range (σ.vars "i")).flatMap fun i => arBlk (arOf x i)

theorem hdOut_value (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "s" = sOf x ∧ σ.vars "M" = MOf x) hdOut
      (fun σ σ' => σ'.out = σ.out ++ ((5 * sOf x + 1) :: ((2 :: (List.range (sOf x)).flatMap
        fun i => arBlk (arOf x i)) ++ [MOf x]))) (40 * x.length + 40) := by
  have hl := len_lt_Bv x
  have hl64 := len64_lt_Bv x
  have hh := hd.hdr
  have hM := MOf_le hd
  have hbody : ∀ out0, Spec (Bv x) (fun σ => HI x out0 σ ∧ σ.vars "i" < sOf x) hdBody
      (fun σ σ' => HI x out0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
    intro out0
    refine Spec.pre (P := fun σ => (HI x out0 σ ∧ σ.vars "i" < sOf x) ∧
      1 + σ.vars "i" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (1 + σ.vars "i") 0 = arOf x (σ.vars "i") ∧
      2 * arOf x (σ.vars "i") < Bv x ∧ 1 + σ.vars "i" < Bv x) ?_ ?_
    · unfold hdBody writes
      run_vcg
      all_goals
        simp only [HI, Env.setVar] at *
        simp_all [List.range_succ, arBlk]
      all_goals (try omega)
    · rintro σ ⟨⟨ha, hs, hM', hi, ho⟩, hlt⟩
      have := getD_le_maxEntry x (1 + σ.vars "i")
      refine ⟨⟨⟨ha, hs, hM', hi, ho⟩, hlt⟩, by rw [ha]; omega, by rw [ha]; rfl, ?_, by omega⟩
      unfold arOf Bv; omega
  intro σ ⟨ha, hs, hM'⟩
  have hloop := Spec.forRangeZero (B := Bv x) (c := hdBody) "i" "s" (HI x (σ.out ++ [5 * sOf x + 1, 2]))
    (sOf x) 30 (by omega) (fun σ h => h.2.2.2.1) (fun σ h => h.2.1) (hbody _)
  have h : Spec (Bv x) (fun τ => τ.arrs "a" = x ∧ τ.vars "s" = sOf x ∧ τ.vars "M" = MOf x ∧
      τ.out = σ.out) hdOut
      (fun _ σ' => σ'.out = σ.out ++ ((5 * sOf x + 1) :: ((2 :: (List.range (sOf x)).flatMap
        fun i => arBlk (arOf x i)) ++ [MOf x]))) (40 * x.length + 40) := by
    refine Spec.mono (K := 1 + (((L 5).mul (V "s")).add (L 1)).size + (1 + (L 2).size + 1) +
      ((30 + 4) * sOf x + 6 + (1 + (V "M").size))) ?_ (by simp; omega)
    unfold hdOut writes loop
    run_vcg [hloop]
    all_goals
      simp only [HI, Env.setVar] at *
      simp_all
    all_goals (try omega)
  exact h σ ⟨ha, hs, hM', rfl⟩

/-! ### The order -/

/-- The pairs `[u, v]`, `u < v`, of row `u`, flattened, up to `v`. -/
def ltRow (u v : ℕ) : List ℕ := (List.range v).flatMap fun v' => if u < v' then [u, v'] else []

/-- The flattened pairs, up to row `u`. -/
def ltUpTo (M u : ℕ) : List ℕ := (List.range u).flatMap fun u' => ltRow u' M

/-- The inner invariant of `ltOut`. -/
def LI (M u : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "M" = M ∧ σ.vars "u" = u ∧ σ.vars "v" ≤ M ∧ σ.out = out0 ++ ltRow u (σ.vars "v")

/-- The outer invariant of `ltOut`. -/
def LO (M : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "M" = M ∧ σ.vars "u" ≤ M ∧ σ.out = out0 ++ ltUpTo M (σ.vars "u")

theorem ltUpTo_succ (M u : ℕ) : ltUpTo M (u + 1) = ltUpTo M u ++ ltRow u M := by
  simp [ltUpTo, List.range_succ]

theorem ltBody_spec {M : ℕ} (hM : M + 8 < Bv x) (out0 : List ℕ) :
    Spec (Bv x) (fun σ => LO M out0 σ ∧ σ.vars "u" < M) ltBody
      (fun σ σ' => LO M out0 σ' ∧ σ'.vars "u" = σ.vars "u" + 1) ((24 + 4) * M + 10) := by
  intro σ ⟨hLO, hu⟩
  obtain ⟨u, hud⟩ : ∃ u, σ.vars "u" = u := ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ o1, σ.out = o1 := ⟨_, rfl⟩
  have hin : Spec (Bv x) (fun τ => LI M u o1 τ ∧ τ.vars "v" < M) ltIn
      (fun τ τ' => LI M u o1 τ' ∧ τ'.vars "v" = τ.vars "v" + 1) 24 := by
    refine Spec.pre (P := fun τ => (LI M u o1 τ ∧ τ.vars "v" < M) ∧ τ.vars "u" < Bv x ∧
      τ.vars "v" + 1 < Bv x) ?_ ?_
    · unfold ltIn writes
      run_vcg
      all_goals
        simp only [LI, ltRow, Env.setVar] at *
        simp_all [List.range_succ]
      all_goals (try omega)
    · rintro τ ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, by omega, by omega⟩
  have hloop := Spec.forRangeZero (B := Bv x) (c := ltIn) "v" "M" (LI M u o1) M 24 (by omega)
    (fun τ h => h.2.2.1) (fun τ h => h.1) hin
  have hu' : u < M := by rw [← hud]; exact hu
  have h : Spec (Bv x) (fun τ => τ.vars "M" = M ∧ τ.vars "u" = u ∧ τ.out = o1) ltBody
      (fun _ τ' => τ'.vars "M" = M ∧ τ'.vars "u" = u + 1 ∧ τ'.out = o1 ++ ltRow u M)
      ((24 + 4) * M + 10) := by
    unfold ltBody loop
    run_vcg [hloop]
    all_goals
      simp only [LI, ltRow, Env.setVar] at *
      simp_all
    all_goals (try omega)
  obtain ⟨τ, hr, h1, h2, h3⟩ := h σ ⟨hLO.1, hud, ho1⟩
  obtain ⟨-, -, h6⟩ := hLO
  refine ⟨τ, hr, ⟨h1, by omega, ?_⟩, by rw [h2, hud]⟩
  rw [h3, h2, ← ho1, h6, hud, ltUpTo_succ, List.append_assoc]


theorem len_filter_lt (u : ℕ) : ∀ M, ((List.range M).filter (fun v => decide (u < v))).length = M - 1 - u
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, len_filter_lt u M]
    by_cases h : u < M <;> simp [h] <;> omega

theorem sum_row : ∀ M, 2 * ((List.range M).map (fun u => M - 1 - u)).sum = M * (M - 1)
  | 0 => by simp
  | M + 1 => by
    have ih := sum_row M
    have e : ((List.range (M + 1)).map (fun u => M + 1 - 1 - u)).sum =
        ((List.range M).map (fun u => M - 1 - u)).sum + M := by
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_sub_cancel,
        Nat.sub_self, add_zero]
      have : ∀ l : List ℕ, (∀ u ∈ l, u < M) → (l.map (fun u => M - u)).sum = (l.map (fun u => M - 1 - u)).sum + l.length := by
        intro l hl
        induction l with
        | nil => simp
        | cons a l ih2 =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have := hl a (by simp)
          rw [ih2 (fun u hu => hl u (by simp [hu]))]; omega
      rw [this _ (fun u hu => List.mem_range.mp hu), List.length_range]
    rw [e]
    rcases M with _ | M
    · simp
    · simp only [Nat.add_sub_cancel] at ih ⊢
      rw [Nat.mul_add, ih]; ring

theorem flatten_flatMap' {α β : Type} (f : α → List (List β)) :
    ∀ l : List α, (l.flatMap f).flatten = l.flatMap fun a => (f a).flatten
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, List.flatten_append, flatten_flatMap' f l]

theorem row_eq (u : ℕ) : ∀ M, (((List.range M).filter (fun v => decide (u < v))).map fun v => [u, v]).flatten =
    (List.range M).flatMap fun v => if u < v then [u, v] else []
  | 0 => rfl
  | M + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.flatten_append, row_eq u M,
      List.flatMap_append]
    by_cases h : u < M <;> simp [h]

/-- The number of pairs `u < v < M`. -/
theorem length_ltList (M : ℕ) : (ltList M).length = M * (M - 1) / 2 := by
  have h : (ltList M).length = ((List.range M).map (fun u => M - 1 - u)).sum := by
    unfold ltList
    rw [List.length_flatMap]
    congr 1
    refine List.map_congr_left fun u _ => ?_
    rw [List.length_map, len_filter_lt]
  have := sum_row M
  omega

theorem flatten_ltList (M : ℕ) : (ltList M).flatten = ltUpTo M M := by
  unfold ltList ltUpTo ltRow
  rw [flatten_flatMap']
  exact List.flatMap_congr fun u _ => row_eq u M

theorem ltOut_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.vars "M" = MOf x) ltOut
      (fun σ σ' => σ'.out = σ.out ++ ((MOf x * (MOf x - 1) / 2) :: ltUpTo (MOf x) (MOf x)))
      (((24 + 4) * MOf x + 10 + 4) * MOf x + 6 + 20) := by
  have hM := MOf_le hd
  have hsq := sq_lt_Bv x hM
  intro σ hσ
  have hloop := Spec.forRangeZero (B := Bv x) (c := ltBody) "u" "M"
    (LO (MOf x) (σ.out ++ [MOf x * (MOf x - 1) / 2])) (MOf x) ((24 + 4) * MOf x + 10) (by omega)
    (fun τ h => h.2.1) (fun τ h => h.1) (ltBody_spec (by omega) _)
  have h : Spec (Bv x) (fun τ => τ.vars "M" = MOf x ∧ τ.out = σ.out) ltOut
      (fun _ σ' => σ'.out = σ.out ++ ((MOf x * (MOf x - 1) / 2) :: ltUpTo (MOf x) (MOf x)))
      (((24 + 4) * MOf x + 10 + 4) * MOf x + 6 + 20) := by
    have hmm : MOf x * (MOf x - 1) ≤ MOf x * MOf x := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    unfold ltOut loop
    run_vcg [hloop]
    all_goals
      simp only [LO, ltUpTo, Env.setVar] at *
      simp_all
    all_goals (try omega)
  exact h σ ⟨hσ, rfl⟩

/-! ### The symbols -/

theorem Rw_getD {x : List ℕ} {k : ℕ} (hk : k < nT x) :
    (Rw x).getD k 0 = rkx x ((entries x).getD k 0) := by
  unfold Rw
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem length_Rw (hd : Dom x φ) : (Rw x).length = x.length := by
  have := nT_le hd
  simp only [Rw, List.length_append, List.length_map, List.length_replicate]
  unfold nT at *; omega

theorem Rw_lt (hd : Dom x φ) {v : ℕ} (hv : v ∈ Rw x) : v ≤ x.length := by
  have := nT_le hd
  simp only [Rw, List.mem_append, List.mem_map, List.mem_replicate] at hv
  rcases hv with ⟨e, he, rfl⟩ | ⟨-, rfl⟩
  · have h1 := Lax496464Proofs.WHierarchy.Lemmas.NegElim.Compress.rk_lt_card (U := Ux x) (e := e) (by simp [Ux, he])
    have h2 : (Ux x).card ≤ (entries x).length := List.toFinset_card_le _
    unfold rkx; unfold nT at this; omega
  · omega

theorem LR_Rw (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    LR (Rw x) (oo x i) (cntOf x i) (arOf x i) = (listOf x i).map (List.map (rkx x)) := by
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  have hs := nT_eq x
  have hmono := oo_mono x (show i + 1 ≤ sOf x by omega)
  rw [oo_succ] at hmono
  rw [listOf_eq]
  unfold LR
  rw [List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < cntOf x i := List.mem_range.mp hj
  have hjr := tup_le (o := 0) (r := arOf x i) hj'
  simp only [Function.comp, tupR, List.map_map]
  refine List.map_congr_left fun l hl => ?_
  have hl' : l < arOf x i := List.mem_range.mp hl
  simp only [Function.comp]
  have hk : j * arOf x i + l < cntOf x i * arOf x i := by omega
  rw [show oo x i + j * arOf x i + l = oo x i + (j * arOf x i + l) by ring, Rw_getD (by omega),
    entries_eq, entsUpTo_getD hi hk]
  congr 2; ring

theorem Rw_ent (hd : Dom x φ) : ∀ v ∈ Rw x, v < Bv x := fun v hv => by
  have := Rw_lt hd hv; have := len_lt_Bv x; omega

/-- What `symPass` has written after `i` symbols. -/
def symAcc (x : List ℕ) (i : ℕ) : List ℕ :=
  (List.range i).flatMap fun i' => symOut (Rw x) (oo x i') (cntOf x i') (arOf x i') (MOf x)

/-- The invariant of `symPass`. -/
def SPI (x : List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.arrs "R" = Rw x ∧ σ.vars "s" = sOf x ∧ σ.vars "M" = MOf x ∧
    σ.vars "i" ≤ sOf x ∧ σ.vars "o" = oo x (σ.vars "i") ∧ σ.vars "p" = bo x (σ.vars "i") ∧
    σ.out = out0 ++ symAcc x (σ.vars "i")

/-- A bound on the cost of one symbol. -/
def Kw (x : List ℕ) : ℕ := 700 * (x.length + 1) * (x.length + 1) + 100

theorem Ksym_le {c r M n : ℕ} (hcr : c * r ≤ n) (hc : c ≤ n) (hM : M ≤ 2 * n) :
    Ksym c r M ≤ 700 * (n + 1) * (n + 1) := by
  have h1 : c * r * c ≤ n * n := Nat.mul_le_mul hcr hc
  have h2 : c * c ≤ n * n := Nat.mul_le_mul hc hc
  unfold Ksym Kfl' KsB Ks
  nlinarith

theorem Bv_big (x : List ℕ) : 16 * maxEntry x + 64 * x.length + 64 < Bv x := by
  have := len_sq_le x; unfold Bv; nlinarith

theorem symOK (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    SymOK (Bv x) (Rw x) (oo x i) (cntOf x i) (arOf x i) := by
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  have hc : cntOf x i ≤ maxEntry x := getD_le_maxEntry x (bo x i)
  have hr : arOf x i ≤ maxEntry x := getD_le_maxEntry x (1 + i)
  have hl64 := Bv_big x
  exact ⟨by rw [length_Rw hd]; omega, Rw_ent hd, by omega⟩

theorem cr_le (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) :
    cntOf x i * arOf x i ≤ x.length ∧ cntOf x i ≤ x.length := by
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  have hr := hd.ar_pos i hi
  refine ⟨by omega, ?_⟩
  have := Nat.le_mul_of_pos_right (cntOf x i) (show 0 < arOf x i by omega)
  omega

set_option maxHeartbeats 4000000 in
theorem symBody_at (hd : Dom x φ) {i : ℕ} (hi : i < sOf x) (out0 : List ℕ) :
    Spec (Bv x) (fun σ => SPI x out0 σ ∧ σ.vars "i" = i) symBody
      (fun σ σ' => SPI x out0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (Kw x + 100) := by
  have hs := symOK hd hi
  have hM := MOf_le hd
  have hl64 := len64_lt_Bv x
  have hbig := hs.big
  have ho := hd.oo_le (i := i + 1) (by omega)
  rw [oo_succ] at ho
  have hbo := hd.blk_le hi
  have hfs := hd.fs_le
  obtain ⟨hcr, hcn⟩ := cr_le hd hi
  have hMc : MOf x + cntOf x i + 1 < Bv x := by omega
  have hK : Ksym (cntOf x i) (arOf x i) (MOf x) ≤ Kw x :=
    (Ksym_le hcr hcn hM).trans (Nat.le_add_right _ _)
  have hsym := (symW_spec hs hMc).mono hK
  have hc1 : x.getD (bo x i) 0 = cntOf x i := rfl
  have hr1 : x.getD (1 + i) 0 = arOf x i := rfl
  refine Spec.pre (P := fun σ => (SPI x out0 σ ∧ σ.vars "i" = i) ∧
    σ.vars "p" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (σ.vars "p") 0 = cntOf x i ∧
    1 + σ.vars "i" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (1 + σ.vars "i") 0 = arOf x i) ?_ ?_
  · refine Spec.mono (K := 1 + (A (V "p")).size + (1 + (A ((L 1).add (V "i"))).size + (Kw x +
      (1 + ((V "o").add ((V "c").mul (V "r"))).size + (1 + (((V "p").add (L 1)).add
      ((V "c").mul (V "r"))).size + (1 + ((V "i").add (L 1)).size)))))) ?_ (by simp; omega)
    unfold symBody
    run_vcg [hsym]
    all_goals first
      | (find_hyp hK' : _ ∧ Keep blkVars _ _
         obtain ⟨hout, hkv, hka, -⟩ := hK'
         have e1 := hkv "i" (by decide)
         have e2 := hkv "o" (by decide)
         have e3 := hkv "p" (by decide)
         have e4 := hkv "s" (by decide)
         have e5 := hkv "M" (by decide)
         have e6 := hkv "c" (by decide)
         have e7 := hkv "r" (by decide)
         have e8 := congrFun hka "a"
         have e9 := congrFun hka "R"
         clear hkv hka
         simp only [SPI, SCM, SC, symAcc, Env.setVar] at *
         simp_all [List.range_succ, bo_succ, oo_succ])
      | (simp only [SPI, SCM, SC, symAcc, Env.setVar] at *
         simp_all [List.range_succ, bo_succ, oo_succ])
    all_goals (try omega)
  · rintro σ ⟨⟨ha, hR, hs', hM', hi', ho', hp, hout⟩, hii⟩
    rw [hii] at hp
    exact ⟨⟨⟨ha, hR, hs', hM', hi', ho', by rw [hii]; exact hp, hout⟩, hii⟩, by rw [ha, hp]; omega,
      by rw [ha, hp]; exact hc1, by rw [ha, hii]; omega, by rw [ha, hii]; exact hr1⟩

theorem symBody_spec (hd : Dom x φ) (out0 : List ℕ) :
    Spec (Bv x) (fun σ => SPI x out0 σ ∧ σ.vars "i" < sOf x) symBody
      (fun σ σ' => SPI x out0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (Kw x + 100) := by
  intro σ ⟨hS, hi⟩
  obtain ⟨i, hid⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hid] at hi
  exact symBody_at hd hi out0 σ ⟨hS, hid⟩

theorem symPass_spec (hd : Dom x φ) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.arrs "R" = Rw x ∧ σ.vars "s" = sOf x ∧
        σ.vars "M" = MOf x) symPass
      (fun σ σ' => σ'.out = σ.out ++ symAcc x (sOf x)) (10 + ((Kw x + 100 + 4) * sOf x + 6)) := by
  have hl64 := len64_lt_Bv x
  have hh := hd.hdr
  intro σ hσ
  have hloop := Spec.forRangeZero (B := Bv x) (c := symBody) "i" "s" (SPI x σ.out) (sOf x)
    (Kw x + 100) (by omega) (fun τ h => h.2.2.2.2.1) (fun τ h => h.2.2.1) (symBody_spec hd _)
  have h : Spec (Bv x) (fun τ => (τ.arrs "a" = x ∧ τ.arrs "R" = Rw x ∧ τ.vars "s" = sOf x ∧
      τ.vars "M" = MOf x) ∧ τ.out = σ.out) symPass
      (fun _ σ' => σ'.out = σ.out ++ symAcc x (sOf x)) (10 + ((Kw x + 100 + 4) * sOf x + 6)) := by
    unfold symPass loop
    run_vcg [hloop]
    all_goals
      simp only [SPI, symAcc, Env.setVar] at *
      simp_all [oo]
    all_goals (try omega)
  exact h σ ⟨hσ, rfl⟩

/-! ### The word of the expanded structure -/

theorem flatten_map_flatMap {α : Type} (f : ℕ → List (List α)) (g : List α → List ℕ) :
    ∀ l : List ℕ, ((l.flatMap f).map g).flatten = l.flatMap fun i => ((f i).map g).flatten
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatten_map_flatMap f g l]

/-- **The structure part of the output.** -/
theorem word_eq {A : Structure} (h : EncodesMC x A φ) (hd : Dom x φ) :
    (dataOf x).word = ((5 * sOf x + 1) :: ((2 :: (List.range (sOf x)).flatMap
        fun i => arBlk (arOf x i)) ++ [MOf x])) ++
      ((MOf x * (MOf x - 1) / 2) :: ltUpTo (MOf x) (MOf x)) ++ symAcc x (sOf x) := by
  have hc := compat h
  have hsym : (List.range (sOf x)).flatMap (fun i => ((NData.blocks (dataOf x) i).map
      Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf).flatten) = symAcc x (sOf x) := by
    unfold symAcc
    refine List.flatMap_congr fun i hi => ?_
    have hi' : i < sOf x := List.mem_range.mp hi
    have hL : (dataOf x).L i = LR (Rw x) (oo x i) (cntOf x i) (arOf x i) := by
      rw [LR_Rw hd hi']; rfl
    have hnd : (LR (Rw x) (oo x i) (cntOf x i) (arOf x i)).Nodup := by
      rw [← hL]; exact (hc.L i hi').1
    rw [symOut_eq hnd]
    unfold NData.blocks
    rw [hL]; rfl
  have hs : (dataOf x).s = sOf x := rfl
  have hN : (dataOf x).N = MOf x := rfl
  have hlt : Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf (ltList (MOf x)) =
      (MOf x * (MOf x - 1) / 2) :: ltUpTo (MOf x) (MOf x) := by
    unfold Lax496464Proofs.WHierarchy.Logic.StructureCode.blockOf; rw [length_ltList, flatten_ltList]
  unfold NData.word Lax496464Proofs.WHierarchy.Logic.StructureCode.wordOf
  rw [NData.length_arities]
  simp only [NData.tss, List.map_cons, List.flatten_cons, flatten_map_flatMap, hs, hN, hlt, hsym]
  simp [NData.arities, dataOf]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr
