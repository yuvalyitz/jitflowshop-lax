import Lax496464Proofs.Ram.Q3Defs

/-!
# Q3: the Initialisation Commands of the Profile Sweep

Three IMP+ commands, each with a `Spec`.  Temporaries come from the pool
`"i" "u1" "u2" "u3" "u4" "u5" "u6"`.

* `powCom dst base ex` — `dst := base ^ ex`.  Mentions (reads/writes) exactly the three scalars
  `dst base ex` and the temporary `"i"`.  When `base = 1` the loop is skipped, so the cost is a
  constant; otherwise it is linear in `ex`.
* `maxCom a dst` — `dst := max (a[0], …, a[n-1], 0)`.  Reads the scalar `"n"` and the array `a`,
  writes `dst` and the temporaries `"i" "u1"`.
* `gInitCom` — fills the digit-sum table.  Reads the scalars `"bt" "bb"`, reads and writes the
  array `"G"`, writes the temporaries `"i" "u1" "u2" "u3" "u4" "u5"`.

Costs: `powCom` `10` if `b = 1` else `12 e + 12`; `maxCom` `20 n + 8`; `gInitCom` `30 bt + 6`.
`powCom_spec` has one hypothesis beyond the requested statement, `b < B` (the test `base = 1`
reads `base` even when `ex = 0`).
-/

namespace Lax496464Proofs.Ram.Q3Init

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Q3Defs

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-! ## `powCom` -/

/-- One turn of the power loop. -/
def powBody (dst base : String) : Com :=
  .seq (.assign dst (.bin .mul (V dst) (V base)))
    (.assign "i" (.bin .add (V "i") (.lit 1)))

/-- `dst := base ^ ex`; if `base = 1` the loop is skipped. -/
def powCom (dst base ex : String) : Com :=
  .seq (.assign dst (.lit 1))
    (.ite (.eq (V base) (.lit 1)) .skip
      (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V ex)) (powBody dst base))))

/-- The invariant of the power loop. -/
def PowInv (dst base ex : String) (b e : ℕ) (σ : Env) : Prop :=
  σ.vars base = b ∧ σ.vars ex = e ∧ σ.vars "i" ≤ e ∧ σ.vars dst = b ^ σ.vars "i"

theorem pow_lt_of_le {B b e k : ℕ} (hB : 1 < B) (hpow : b ^ e < B) (hk : k ≤ e) : b ^ k < B := by
  rcases Nat.eq_zero_or_pos b with h0 | hpos
  · subst h0
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simpa using hB
    · rw [zero_pow (by omega)]; omega
  · exact lt_of_le_of_lt (Nat.pow_le_pow_right hpos hk) hpow

theorem powBody_spec {B b e : ℕ} (dst base ex : String) (hd1 : dst ≠ base) (hd2 : dst ≠ ex) (hd3 : dst ≠ "i")
    (hb3 : base ≠ "i") (he3 : ex ≠ "i") (hB : 1 < B) (hpow : b ^ e < B) (hbB : b < B)
    (heB : e < B) :
    Spec B (fun σ => PowInv dst base ex b e σ ∧ σ.vars "i" < e) (powBody dst base)
      (fun σ σ' => PowInv dst base ex b e σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 8 := by
  intro σ ⟨⟨hb, he, hi, hd⟩, hlt⟩
  have hp : b ^ (σ.vars "i" + 1) < B := pow_lt_of_le hB hpow (by omega)
  have hdB : σ.vars dst < B := by rw [hd]; exact pow_lt_of_le hB hpow (by omega)
  have hbB' : σ.vars base < B := by rw [hb]; exact hbB
  have hex : σ.vars ex < B := by rw [he]; exact heB
  have hmul : σ.vars dst * σ.vars base < B := by rw [hd, hb, ← pow_succ]; exact hp
  run_vcg
  all_goals simp [PowInv, Env.setVar, hd3, Ne.symm hd3, hb3, he3, Ne.symm hd2, Ne.symm hd1,
    hb, he, hd, hlt, pow_succ]
  all_goals omega

/-- **Power**: `dst := base ^ ex`, constant time if `base = 1`, else linear in `ex`.
Hypothesis `hbB : b < B` is needed because the test `base = 1` reads `base` even when `ex = 0`. -/
theorem powCom_spec {B b e : ℕ} (dst base ex : String) (hd1 : dst ≠ base) (hd2 : dst ≠ ex)
    (hd3 : dst ≠ "i") (hb3 : base ≠ "i") (he3 : ex ≠ "i") (hB : 1 < B) (hpow : b ^ e < B)
    (hbB : b < B) (heB : e < B) :
    Spec B (fun σ => σ.vars base = b ∧ σ.vars ex = e) (powCom dst base ex)
      (fun _ σ' => σ'.vars dst = b ^ e) (if b = 1 then 10 else 12 * e + 12) := by
  have hloop := Spec.forRangeZero (B := B) (c := powBody dst base) "i" ex (PowInv dst base ex b e)
    e 8 heB (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (powBody_spec dst base ex hd1 hd2 hd3 hb3 he3 hB hpow hbB heB)
  refine Spec.of_exists fun σ ⟨hb, he⟩ => ?_
  have hl1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit hB
  have r1 := Run.assign (B := B) (σ := σ) (x := dst) (e := .lit 1) (v := 1) hl1
  set σ1 : Env := σ.setVar dst 1 with hσ1
  have hb1' : σ1.vars base = b := by simp [hσ1, Env.setVar, Ne.symm hd1, hb]
  have he1' : σ1.vars ex = e := by simp [hσ1, Env.setVar, Ne.symm hd2, he]
  have hvb : (V base).evalB B σ1 = some b := hb1' ▸ evalB_var (by rw [hb1']; exact hbB)
  have hl1' : (Expr.lit 1).evalB B σ1 = some 1 := evalB_lit hB
  have hc := evalB_condEq hvb hl1'
  have hdst1 : σ1.vars dst = 1 := by simp [hσ1]
  by_cases hb1 : b = 1
  · have hct : (Cond.eq (V base) (.lit 1)).evalB B σ1 = some true := by rw [hc]; simp [hb1]
    refine ⟨σ1, _, (r1.seq (Run.ite_true hct Run.skip)).mono ?_, le_rfl, ?_⟩
    · rw [if_pos hb1]; simp only [Expr.size, Cond.size]; omega
    · rw [hdst1, hb1]; simp
  · have hct : (Cond.eq (V base) (.lit 1)).evalB B σ1 = some false := by rw [hc]; simp [hb1]
    obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hb1', he1', hdst1, hb3, he3, hd3])
    refine ⟨σ2, _, (r1.seq (Run.ite_false hct hr2)).mono ?_, le_rfl, ?_⟩
    · rw [if_neg hb1]; simp only [Expr.size, Cond.size]; omega
    · rw [hI.2.2.2, hi]

/-! ## `maxCom` -/

/-- One turn of the max scan: `u1 := a[i]; if dst < u1 then dst := u1; i := i + 1`. -/
def maxBody (a dst : String) : Com :=
  .seq (.assign "u1" (.get a (V "i")))
    (.seq (.ite (.lt (V dst) (V "u1")) (.assign dst (V "u1")) .skip)
      (.assign "i" (.bin .add (V "i") (.lit 1))))

/-- `dst := max (a[0], …, a[n-1], 0)`, the count being the scalar `"n"`. -/
def maxCom (a dst : String) : Com :=
  .seq (.assign dst (.lit 0))
    (.seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) (maxBody a dst)))

/-- The invariant of the max scan: `dst` is the max of the prefix seen so far. -/
def MaxInv (a dst : String) (A : List ℕ) (n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs a = A ∧ σ.vars "i" ≤ n ∧
    σ.vars dst = (A.take (σ.vars "i")).foldr max 0

theorem foldr_max_seed (l : List ℕ) (seed : ℕ) : l.foldr max seed = max seed (l.foldr max 0) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, ih]; omega

theorem foldr_max_lt' {l : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ v ∈ l, v < B) :
    l.foldr max 0 < B := by
  induction l with
  | nil => simpa using hB
  | cons a l ih =>
    simp only [List.foldr_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    omega

theorem foldr_max_take_succ (A : List ℕ) (i : ℕ) (hi : i < A.length) :
    (A.take (i + 1)).foldr max 0 = max ((A.take i).foldr max 0) (A.getD i 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  simp only [Option.toList_some, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  rw [foldr_max_seed]
  omega

theorem maxBody_spec {B n : ℕ} (a dst : String) (A : List ℕ)
    (hdst : dst ≠ "i" ∧ dst ≠ "u1" ∧ dst ≠ "n") (hB : 1 < B)
    (hl : A.length = n) (hAB : ∀ v ∈ A, v < B) (hnB : n < B) :
    Spec B (fun σ => MaxInv a dst A n σ ∧ σ.vars "i" < n) (maxBody a dst)
      (fun σ σ' => MaxInv a dst A n σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 16 := by
  obtain ⟨hd1, hd2, hd3⟩ := hdst
  intro σ ⟨⟨hn, ha, hi, hd⟩, hlt⟩
  have hgetB : ∀ t, t < A.length → A.getD t 0 < B := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hAB _ (List.getElem_mem ht)
  have hiA : σ.vars "i" < A.length := by omega
  have hdB : σ.vars dst < B := by
    rw [hd]; exact foldr_max_lt' (by omega) (fun v hv => hAB v (List.mem_of_mem_take hv))
  have hgB : (σ.arrs a).getD (σ.vars "i") 0 < B := by rw [ha]; exact hgetB _ hiA
  have hiL : σ.vars "i" < (σ.arrs a).length := by rw [ha]; exact hiA
  have htake := foldr_max_take_succ A (σ.vars "i") hiA
  have hgd : (σ.arrs a).getD (σ.vars "i") 0 = A.getD (σ.vars "i") 0 := by rw [ha]
  have hgd' : A[σ.vars "i"]?.getD 0 = A.getD (σ.vars "i") 0 := rfl
  run_vcg
  all_goals simp only [MaxInv, Env.setVar] at *
  all_goals simp [hd1, hd2, hd3, Ne.symm hd1, Ne.symm hd3] at *
  all_goals first | omega | (refine ⟨hn, ha, ?_, ?_⟩ <;> omega)

/-- **Max scan**: `dst := max (A[0], …, A[n-1], 0)`, linear in `n`. -/
theorem maxCom_spec {B n : ℕ} (a dst : String) (A : List ℕ)
    (hdst : dst ≠ "i" ∧ dst ≠ "u1" ∧ dst ≠ "n") (hB : 1 < B)
    (hl : A.length = n) (hAB : ∀ v ∈ A, v < B) (hnB : n < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs a = A) (maxCom a dst)
      (fun _ σ' => σ'.vars dst = A.foldr max 0) (20 * n + 8) := by
  obtain ⟨hd1, hd2, hd3⟩ := hdst
  have hloop := Spec.forRangeZero (B := B) (c := maxBody a dst) "i" "n" (MaxInv a dst A n)
    n 16 hnB (fun _ h => h.2.2.1) (fun _ h => h.1)
    (maxBody_spec a dst A ⟨hd1, hd2, hd3⟩ hB hl hAB hnB)
  refine Spec.of_exists fun σ ⟨hn, ha⟩ => ?_
  have hl0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  have r1 := Run.assign (B := B) (σ := σ) (x := dst) (e := .lit 0) (v := 0) hl0
  set σ1 : Env := σ.setVar dst 0 with hσ1
  obtain ⟨σ2, hr2, hI, hi⟩ := hloop.run (σ := σ1) (by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hσ1, Env.setVar, hn, ha, Ne.symm hd3, hd1])
  refine ⟨σ2, _, (r1.seq hr2).mono ?_, le_rfl, ?_⟩
  · simp only [Expr.size]; omega
  · rw [hI.2.2.2, hi, List.take_of_length_le (by omega)]

/-! ## `gInitCom`: the digit-sum table -/

/-- Local recursion for the digit sum: peel the lowest digit. -/
theorem digsum_step {bb qm x : ℕ} (hbb : 2 ≤ bb) (hx0 : 0 < x) (hx : x < bb ^ qm) :
    digsum bb qm x = digsum bb qm (x / bb) + x % bb := by
  cases qm with
  | zero => simp at hx; omega
  | succ q =>
    have hpos : 0 < bb := by omega
    have hxq : x / bb < bb ^ q := by
      rw [Nat.div_lt_iff_lt_mul hpos]; rw [pow_succ] at hx; exact hx
    have htop : dig bb (x / bb) q = 0 := by
      unfold dig; rw [Nat.div_eq_of_lt hxq]; simp
    have hshift : ∀ i, dig bb (x / bb) i = dig bb x (i + 1) := by
      intro i; unfold dig
      rw [Nat.div_div_eq_div_mul, pow_succ', ]
    unfold digsum
    rw [Finset.sum_range_succ' _ q, Finset.sum_range_succ _ q, htop]
    have h0 : dig bb x 0 = x % bb := by simp [dig]
    rw [h0]
    simp only [hshift, add_zero]

/-- The value written into `G[i]`, and that it is the digit sum and at most `i`. -/
theorem gval {bb qm bt i : ℕ} (G : List ℕ) (hbb : 1 ≤ bb) (hbt : bt = bb ^ qm) (hi : i < bt)
    (hprev : ∀ y < i, G.getD y 0 = digsum bb qm y ∧ G.getD y 0 ≤ y)
    (hzero : ∀ y, i ≤ y → G.getD y 0 = 0) :
    G.getD (i / bb) 0 + (i - i / bb * bb) = digsum bb qm i ∧
      G.getD (i / bb) 0 + (i - i / bb * bb) ≤ i := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have h' : G[0]?.getD 0 = 0 := hzero 0 le_rfl
    simp [h', digsum, dig]
  · have hbb2 : 2 ≤ bb := by
      by_contra hlt
      have : bb = 1 := by omega
      subst this
      simp at hbt; omega
    have hlt : i / bb < i := Nat.div_lt_self hpos (by omega)
    obtain ⟨hg1, hg2⟩ := hprev _ hlt
    have hstep := digsum_step (bb := bb) (qm := qm) hbb2 hpos (hbt ▸ hi)
    have hdm := Nat.div_add_mod i bb
    have hmod : i - i / bb * bb = i % bb := by
      have : i / bb * bb = bb * (i / bb) := Nat.mul_comm _ _
      omega
    have hle : i / bb ≤ bb * (i / bb) := Nat.le_mul_of_pos_left _ (by omega)
    rw [hmod, hstep, hg1]
    refine ⟨rfl, ?_⟩
    omega

/-- The five scalar assignments of a table-fill turn: `u5 := G[i / bb] + (i - (i / bb) * bb)`. -/
def gCalc : Com :=
  .seq (.assign "u1" (.bin .div (V "i") (V "bb")))
    (.seq (.assign "u2" (.get "G" (V "u1")))
      (.seq (.assign "u3" (.bin .mul (V "u1") (V "bb")))
        (.seq (.assign "u4" (.bin .sub (V "i") (V "u3")))
          (.assign "u5" (.bin .add (V "u2") (V "u4"))))))

/-- The two writing commands of a table-fill turn: `G[i] := u5; i := i + 1`. -/
def gWrite : Com :=
  .seq (.store "G" (V "i") (V "u5")) (.assign "i" (.bin .add (V "i") (.lit 1)))

/-- One turn of the table fill: `G[i] := G[i / bb] + (i - (i / bb) * bb)`. -/
def gBody : Com := .seq gCalc gWrite

/-- The digit-sum table: `G[x] := digsum bb qm x` for all `x < bt` (`G` initially all zeros of
length `bt`). -/
def gInitCom : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "bt")) gBody)

/-- The invariant of the table fill: entries below `i` are final (digit sum, at most the index),
the others still zero. -/
def GInv (bt bb qm : ℕ) (σ : Env) : Prop :=
  σ.vars "bt" = bt ∧ σ.vars "bb" = bb ∧ σ.vars "i" ≤ bt ∧ (σ.arrs "G").length = bt ∧
    (∀ y < σ.vars "i", (σ.arrs "G").getD y 0 = digsum bb qm y ∧ (σ.arrs "G").getD y 0 ≤ y) ∧
    (∀ y, σ.vars "i" ≤ y → (σ.arrs "G").getD y 0 = 0)

theorem gCalc_spec {B bb i : ℕ} (G : List ℕ) (hbb : 1 ≤ bb) (hbbB : bb < B) (hiB : i < B)
    (hiL : i < G.length) (hGle : ∀ y, G.getD y 0 ≤ y) :
    Spec B (fun σ => σ.vars "i" = i ∧ σ.vars "bb" = bb ∧ σ.arrs "G" = G) gCalc
      (fun _ σ' => σ'.vars "u5" = G.getD (i / bb) 0 + (i - i / bb * bb)) 19 := by
  intro σ ⟨hi, hbbσ, hG⟩
  have hu1 : i / bb ≤ i := Nat.div_le_self _ _
  have hu3 : i / bb * bb ≤ i := Nat.div_mul_le_self _ _
  have hg1 := hGle (i / bb)
  have hu1L : i / bb < G.length := by omega
  have hpos : 0 < bb := hbb
  have hgd : (σ.arrs "G").getD (i / bb) 0 = G.getD (i / bb) 0 := by rw [hG]
  have hgd' : (σ.arrs "G")[i / bb]?.getD 0 = G.getD (i / bb) 0 := by rw [hG]; rfl
  have hGL : (σ.arrs "G").length = G.length := by rw [hG]
  have hg2 : G[i / bb]?.getD 0 ≤ i / bb := hg1
  have hu4 : i / bb ≤ i / bb * bb := Nat.le_mul_of_pos_right _ hpos
  run_vcg
  all_goals simp [Env.setVar, hi, hbbσ, hgd']
  all_goals omega

theorem getD_set_of_ne (G : List ℕ) (i v y : ℕ) (h : i ≠ y) :
    (G.set i v).getD y 0 = G.getD y 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_self (G : List ℕ) (i v : ℕ) (h : i < G.length) :
    (G.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem gWrite_spec {B i v : ℕ} (G : List ℕ) (hiL : i < G.length) (hiB : i + 1 < B) (hv : v < B) :
    Spec B (fun σ => σ.vars "i" = i ∧ σ.vars "u5" = v ∧ σ.arrs "G" = G) gWrite
      (fun _ σ' => σ'.arrs "G" = G.set i v ∧ σ'.vars "i" = i + 1) 7 := by
  intro σ ⟨hi, hu5, hG⟩
  have hiL' : i < (σ.arrs "G").length := by rw [hG]; exact hiL
  run_vcg
  all_goals simp [Env.setVar, hi, hu5, hG]

theorem gBody_spec {B bt bb qm : ℕ} (_hB : 1 < B) (hbb : 1 ≤ bb) (hbt : bt = bb ^ qm)
    (hbtB : bt < B) (hbbB : bb < B) :
    Spec B (fun σ => GInv bt bb qm σ ∧ σ.vars "i" < bt) gBody
      (fun σ σ' => GInv bt bb qm σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 26 := by
  intro σ ⟨⟨hbtσ, hbbσ, hi, hlen, hprev, hzero⟩, hlt⟩
  obtain ⟨hv1, hv2⟩ := gval (σ.arrs "G") hbb hbt hlt hprev hzero
  have hGle : ∀ y, (σ.arrs "G").getD y 0 ≤ y := by
    intro y
    by_cases hy : y < σ.vars "i"
    · exact (hprev y hy).2
    · rw [hzero y (by omega)]; exact Nat.zero_le _
  have hiL : σ.vars "i" < (σ.arrs "G").length := by omega
  obtain ⟨σ1, hr1, hu5, hfv1, hfa1, -, -⟩ :=
    (gCalc_spec (B := B) (bb := bb) (i := σ.vars "i") (σ.arrs "G") hbb hbbB (by omega) hiL hGle).frame.run
      (σ := σ) ⟨rfl, hbbσ, rfl⟩
  have hG1 : σ1.arrs "G" = σ.arrs "G" := hfa1 "G" (by decide)
  have hi1 : σ1.vars "i" = σ.vars "i" := hfv1 "i" (by decide)
  obtain ⟨σ2, hr2, ⟨hG2, hi2⟩, hfv2, hfa2, -, -⟩ :=
    (gWrite_spec (B := B) (i := σ.vars "i") (v := (σ.arrs "G").getD (σ.vars "i" / bb) 0 +
      (σ.vars "i" - σ.vars "i" / bb * bb)) (σ.arrs "G") hiL (by omega) (by omega)).frame.run
      (σ := σ1) ⟨hi1, hu5, hG1⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hi2⟩
  · rw [hfv2 "bt" (by decide), hfv1 "bt" (by decide), hbtσ]
  · rw [hfv2 "bb" (by decide), hfv1 "bb" (by decide), hbbσ]
  · omega
  · rw [hG2, List.length_set, hlen]
  · intro y hy
    rw [hi2] at hy
    rw [hG2]
    by_cases hyi : y = σ.vars "i"
    · subst hyi
      rw [getD_set_self _ _ _ hiL]
      exact ⟨hv1, hv2⟩
    · rw [getD_set_of_ne _ _ _ _ (Ne.symm hyi)]
      exact hprev y (by omega)
  · intro y hy
    rw [hi2] at hy
    rw [hG2, getD_set_of_ne _ _ _ _ (by omega)]
    exact hzero y (by omega)

/-- **The digit-sum table**: from `G = [0, …, 0]` (length `bt = bb ^ qm`) to
`G[x] = digsum bb qm x` (also `≤ x`), linear in `bt`. -/
theorem gInitCom_spec {B bt bb qm : ℕ} (hB : 1 < B) (hbb : 1 ≤ bb) (hbt : bt = bb ^ qm)
    (hbtB : bt < B) (hbbB : bb < B) :
    Spec B (fun σ => σ.vars "bt" = bt ∧ σ.vars "bb" = bb ∧ σ.arrs "G" = List.replicate bt 0)
      gInitCom
      (fun _ σ' => (σ'.arrs "G").length = bt ∧
        (∀ x < bt, (σ'.arrs "G").getD x 0 = digsum bb qm x) ∧
        (∀ x < bt, (σ'.arrs "G").getD x 0 ≤ x)) (30 * bt + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := gBody) "i" "bt" (GInv bt bb qm) bt 26 hbtB
    (fun _ h => h.2.2.1) (fun _ h => h.1) (gBody_spec hB hbb hbt hbtB hbbB)
  intro σ ⟨hbtσ, hbbσ, hG⟩
  obtain ⟨σ', hr, hI, hi⟩ := hloop.run (σ := σ) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Env.setVar] using hbtσ
    · simpa [Env.setVar] using hbbσ
    · simp [Env.setVar]
    · simp [Env.setVar, hG]
    · simp [Env.setVar]
    · intro y _
      simp only [Env.setVar, hG, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp)
  obtain ⟨-, -, -, hlen, hprev, -⟩ := hI
  rw [hi] at hprev
  exact ⟨σ', hr.mono (by omega), hlen, fun x hx => (hprev x hx).1, fun x hx => (hprev x hx).2⟩

end Lax496464Proofs.Ram.Q3Init