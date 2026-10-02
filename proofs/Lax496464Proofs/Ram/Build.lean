import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.Members
import Lax496464Proofs.Ram.ListUtil

/-!
# The Membership Pairs, Built on the Machine

`Members.lean` says what the pairs are: for each set `j`, the elements `i` of the universe
with `memB x j i`, in the order of the universe. A program has the offsets and the member
array and no way to say "sorted, without repetition", so it asks the question the definition
asks: for each set `j` and each element `i`, is there a position of the block of `j`
holding `i`? Three nested scans, `m · n · (|block| + 1)` steps in all — polynomial, which is
all the reduction owes.
-/

namespace Lax496464Proofs.Ram.Build

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464Proofs.Ram.Members Lax496464Proofs.Ram.ListUtil

/-- A scalar, as an expression. -/
abbrev V (s : String) : Expr := .var s

/-- Increment a scalar. -/
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-! ## 1. What the program has read -/

variable (x : List ℕ)

/-- The header scalars, the offsets in `OFF` and the members in `MEM`. -/
def RC (σ : Env) : Prop :=
  σ.vars "n" = universeSize x ∧ σ.vars "m" = setCount x ∧
  (∀ j ≤ setCount x, (σ.arrs "OFF").getD j 0 = offset x j) ∧
  (∀ t < offset x (setCount x), (σ.arrs "MEM").getD t 0 = member x t) ∧
  (σ.arrs "OFF").length = setCount x + 1 ∧ (σ.arrs "MEM").length = offset x (setCount x)

variable {x}

theorem RC.congr {σ σ' : Env} (h : RC x σ) (hn : σ'.vars "n" = σ.vars "n")
    (hm : σ'.vars "m" = σ.vars "m") (ho : σ'.arrs "OFF" = σ.arrs "OFF")
    (hme : σ'.arrs "MEM" = σ.arrs "MEM") : RC x σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, h1]
  · rw [hm, h2]
  · rw [ho]; exact h3
  · rw [hme]; exact h4
  · rw [ho]; exact h5
  · rw [hme]; exact h6

theorem member_lt {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 0 < B) (t : ℕ) : member x t < B := by
  unfold member
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[3 + setCount x + t]? with _ | v
  · simpa using hB
  · simp only [Option.getD_some]
    exact hxB v (List.mem_of_getElem? h)

/-! ## 2. Is there a position of the block holding `i`? -/

/-- Scan the block of set `j`, held as `bs` and `bl`, for the element `i`, leaving the answer
in `f`. -/
def scanBody : Com :=
  .seq (.assign "tt" (.bin .add (V "bs") (V "s")))
    (.seq (.ite (.eq (.get "MEM" (V "tt")) (V "i")) (.assign "f" (.lit 1)) .skip) (bump "s"))

def scanLoop : Com :=
  .seq (.assign "f" (.lit 0))
    (.seq (.assign "s" (.lit 0)) (.while (.lt (V "s") (V "bl")) scanBody))

variable (x) in
/-- The scan's invariant: after `s` positions, `f` says whether one of them held `i`. -/
def SI (j i N : ℕ) (σ : Env) : Prop :=
  RC x σ ∧ σ.vars "i" = i ∧ σ.vars "bs" = offset x j ∧ σ.vars "bl" = N ∧
  σ.vars "s" ≤ N ∧ (σ.vars "f" = 0 ∨ σ.vars "f" = 1) ∧
  (σ.vars "f" = 1 ↔ ∃ s' < σ.vars "s", member x (offset x j + s') = i)

theorem scanBody_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (j i N : ℕ)
    (hN : offset x j + N ≤ offset x (setCount x)) (hLB : offset x (setCount x) < B)
    (hiB : i < B) :
    Spec B (fun σ => SI x j i N σ ∧ σ.vars "s" < N) scanBody
      (fun σ σ' => SI x j i N σ' ∧ σ'.vars "s" = σ.vars "s" + 1) 40 := by
  refine Spec.pre (P := fun σ => SI x j i N σ ∧ σ.vars "s" < N ∧
      (σ.arrs "MEM").getD (σ.vars "bs" + σ.vars "s") 0 = member x (offset x j + σ.vars "s") ∧
      σ.vars "bs" + σ.vars "s" < (σ.arrs "MEM").length ∧
      member x (offset x j + σ.vars "s") < B ∧ σ.vars "bs" + σ.vars "s" < B ∧
      σ.vars "s" + 1 < B ∧ i < B) ?_ ?_
  · run_vcg
    all_goals (simp only [SI] at *; simp_all)
    all_goals first
      | omega
      | (obtain ⟨hRC, -, -, -, -, hf, hiff⟩ := ‹RC x _ ∧ _›
         first
           | exact ⟨RC.congr hRC (by simp) (by simp) (by simp) (by simp), _, le_rfl, rfl⟩
           | (refine ⟨RC.congr hRC (by simp) (by simp) (by simp) (by simp), ?_, ?_⟩
              · rcases hf with h | h
                · exact Or.inl h
                · exact Or.inr (hiff.mp h)
              · constructor
                · rintro ⟨s', h1, h2⟩; exact ⟨s', h1.le, h2⟩
                · rintro ⟨s', h1, h2⟩
                  rcases h1.lt_or_eq with h | rfl
                  · exact ⟨s', h, h2⟩
                  · exact absurd h2 ‹_›))
  · rintro σ ⟨hI, hlt⟩
    obtain ⟨⟨hC, hi, hbs, hbl, hle, hf, hiff⟩, -⟩ := And.intro hI hlt
    have hRC := hC
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hRC
    have hidx : offset x j + σ.vars "s" < offset x (setCount x) := by omega
    refine ⟨⟨hC, hi, hbs, hbl, hle, hf, hiff⟩, hlt, ?_, ?_, member_lt hxB (by omega) _, ?_, ?_, hiB⟩
    · rw [hbs]; exact h4 _ hidx
    · rw [hbs, h6]; exact hidx
    · rw [hbs]; omega
    · omega

theorem scanLoop_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (j i N : ℕ)
    (hN : offset x j + N ≤ offset x (setCount x)) (hLB : offset x (setCount x) < B)
    (hiB : i < B) (hNB : N < B) :
    Spec B (fun σ => RC x σ ∧ σ.vars "i" = i ∧ σ.vars "bs" = offset x j ∧ σ.vars "bl" = N)
      scanLoop
      (fun _ σ' => RC x σ' ∧ σ'.vars "i" = i ∧ σ'.vars "bs" = offset x j ∧
        σ'.vars "bl" = N ∧ (σ'.vars "f" = 0 ∨ σ'.vars "f" = 1) ∧
        (σ'.vars "f" = 1 ↔ ∃ s' < N, member x (offset x j + s') = i))
      (2 + ((40 + 4) * N + 6)) := by
  have hloop := Spec.forRangeZero (B := B) "s" "bl" (SI x j i N) N 40 hNB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.1) (scanBody_spec hxB hB j i N hN hLB hiB)
  have hassign := Spec.assign (B := B)
    (P := fun σ => RC x σ ∧ σ.vars "i" = i ∧ σ.vars "bs" = offset x j ∧ σ.vars "bl" = N)
    (x := "f") (e := .lit 0) (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))
  refine (hassign.seq hloop (fun σ σ' hσ h => ?_)
    (fun σ σ' σ'' _ _ h2 => ?_)).mono ?_
  · obtain ⟨hC, hi, hbs, hbl⟩ := hσ
    subst h
    refine ⟨hC.congr (by simp) (by simp) (by simp) (by simp), by simpa using hi,
      by simpa using hbs, by simpa using hbl, by simp, Or.inl (by simp), ?_⟩
    simp
  · obtain ⟨⟨hC, hi, hbs, hbl, hle, hf, hiff⟩, hs⟩ := h2
    rw [hs] at hiff
    exact ⟨hC, hi, hbs, hbl, hf, hiff⟩
  · simp only [Expr.size]; omega

/-! ## 3. The list being built -/

variable (x) in
/-- The pairs of the sets before `j`. -/
def prefixPairs (j : ℕ) : List (ℕ × ℕ) :=
  (List.range j).flatMap fun j' => (wmembers x j').map fun i' => (j', i')

variable (x) in
/-- The pairs of set `j` whose element is below `i`. -/
def blockPairs (j i : ℕ) : List (ℕ × ℕ) :=
  ((List.range i).filter (memB x j)).map fun i' => (j, i')

theorem prefixPairs_succ (j : ℕ) :
    prefixPairs x (j + 1) = prefixPairs x j ++ blockPairs x j (universeSize x) := by
  simp only [prefixPairs, blockPairs, wmembers, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

theorem blockPairs_succ (j i : ℕ) :
    blockPairs x j (i + 1) = blockPairs x j i ++ (if memB x j i = true then [(j, i)] else []) := by
  by_cases h : memB x j i = true <;> simp [blockPairs, List.range_succ, List.filter_append, h]

theorem wmemberList_eq_prefix : wmemberList x = prefixPairs x (setCount x) := rfl

theorem length_blockPairs_le (j i : ℕ) : (blockPairs x j i).length ≤ i := by
  simp only [blockPairs, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem length_prefixPairs_le (j : ℕ) : (prefixPairs x j).length ≤ j * universeSize x := by
  induction j with
  | zero => simp [prefixPairs]
  | succ j ih =>
    rw [prefixPairs_succ, List.length_append, Nat.succ_mul]
    have := length_blockPairs_le (x := x) j (universeSize x)
    omega

variable (x) in
/-- The state holds the list `cur`, in the first `|cur|` cells of `MJ` and `MI`, with room
for `m·n` pairs. -/
def CurInv (cur : List (ℕ × ℕ)) (σ : Env) : Prop :=
  σ.vars "Lc" = cur.length ∧
  (∀ u < cur.length, (σ.arrs "MJ").getD u 0 = (cur.getD u (0, 0)).1 ∧
    (σ.arrs "MI").getD u 0 = (cur.getD u (0, 0)).2) ∧
  universeSize x * setCount x ≤ (σ.arrs "MJ").length ∧
  universeSize x * setCount x ≤ (σ.arrs "MI").length

theorem CurInv.push {cur : List (ℕ × ℕ)} {σ : Env} (h : CurInv x cur σ)
    (hlt : cur.length < universeSize x * setCount x) (j i : ℕ) :
    CurInv x (cur ++ [(j, i)])
      (((σ.setArr "MJ" (σ.vars "Lc") j).setArr "MI" (σ.vars "Lc") i).setVar "Lc"
        (σ.vars "Lc" + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [h1], ?_, by simpa using h3, by simpa using h4⟩
  intro u hu
  simp only [List.length_append, List.length_singleton] at hu
  simp only [arrs_setVar, arrs_setArr, if_true, if_neg (show "MJ" ≠ "MI" by decide),
    if_neg (show "MI" ≠ "MJ" by decide), h1]
  rcases Nat.lt_or_ge u cur.length with h | h
  · rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega),
      List.getD_append _ _ _ _ h]
    exact h2 u h
  · obtain rfl : u = cur.length := by omega
    rw [getD_set_self _ _ _ (by omega), getD_set_self _ _ _ (by omega),
      List.getD_append_right _ _ _ _ le_rfl]
    simp

/-- Append the pair `(j, i)`. -/
def collect : Com :=
  .seq (.store "MJ" (V "Lc") (V "j"))
    (.seq (.store "MI" (V "Lc") (V "i")) (bump "Lc"))

theorem collect_spec {B : ℕ} {cur : List (ℕ × ℕ)} (hlt : cur.length < universeSize x * setCount x) :
    Spec B (fun σ => CurInv x cur σ ∧ σ.vars "j" < B ∧ σ.vars "i" < B ∧ cur.length + 1 < B)
      collect
      (fun σ σ' => σ' = (((σ.setArr "MJ" (σ.vars "Lc") (σ.vars "j")).setArr "MI"
        (σ.vars "Lc") (σ.vars "i")).setVar "Lc" (σ.vars "Lc" + 1))) 20 := by
  refine Spec.pre (P := fun σ => CurInv x cur σ ∧ σ.vars "Lc" < (σ.arrs "MJ").length ∧
      σ.vars "Lc" < (σ.arrs "MI").length ∧ σ.vars "j" < B ∧ σ.vars "i" < B ∧
      σ.vars "Lc" < B ∧ σ.vars "Lc" + 1 < B) ?_ ?_
  · run_vcg
    all_goals simp
  · rintro σ ⟨hσ, hj, hi, hc⟩
    obtain ⟨hL, -, h3, h4⟩ := id hσ
    refine ⟨hσ, by omega, by omega, hj, hi, by omega, by omega⟩

theorem CurInv.congr {cur : List (ℕ × ℕ)} {σ σ' : Env} (h : CurInv x cur σ)
    (hL : σ'.vars "Lc" = σ.vars "Lc") (hj : σ'.arrs "MJ" = σ.arrs "MJ")
    (hi : σ'.arrs "MI" = σ.arrs "MI") : CurInv x cur σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hL, h1], ?_, by rw [hj]; exact h3, by rw [hi]; exact h4⟩
  intro u hu
  rw [hj, hi]; exact h2 u hu

/-- One element of the universe against one set: scan the block, and append the pair if
found. -/
def iBody : Com :=
  .seq scanLoop (.seq (.ite (.eq (V "f") (.lit 1)) collect .skip) (bump "i"))

variable (x) in
/-- What is fixed while the elements of set `j` are visited. -/
def EI (j : ℕ) (σ : Env) : Prop :=
  RC x σ ∧ σ.vars "j" = j ∧ σ.vars "bs" = offset x j ∧
    σ.vars "bl" = offset x (j + 1) - offset x j

theorem iBody_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (j i : ℕ) (cur : List (ℕ × ℕ))
    (hj : j < setCount x) (hi : i < universeSize x)
    (hmono : offset x j ≤ offset x (j + 1)) (hle : offset x (j + 1) ≤ offset x (setCount x))
    (hcur : cur.length ≤ j * universeSize x + i)
    (hLB : offset x (setCount x) < B) (hnB : universeSize x < B)
    (hmnB : universeSize x * setCount x + 1 < B) (hjB : j < B) :
    Spec B (fun σ => EI x j σ ∧ σ.vars "i" = i ∧ CurInv x cur σ) iBody
      (fun _ σ' => EI x j σ' ∧ σ'.vars "i" = i + 1 ∧
        CurInv x (cur ++ (if memB x j i = true then [(j, i)] else [])) σ')
      (2 + ((40 + 4) * (offset x (j + 1) - offset x j) + 6) + (1 + 3 + 20) + 4 + 4) := by
  have hN : offset x j + (offset x (j + 1) - offset x j) ≤ offset x (setCount x) := by omega
  have hscan := (scanLoop_spec hxB hB j i (offset x (j + 1) - offset x j) hN hLB (by omega)
    (by omega)).frame
  refine Spec.of_exists fun σ ⟨⟨hRC, hj', hbs, hbl⟩, hi', hCur⟩ => ?_
  obtain ⟨σ1, hr1, ⟨hRC1, hi1, hbs1, hbl1, hf01, hfiff⟩, hfv, hfa, -, -⟩ :=
    hscan.run ⟨hRC, hi', hbs, hbl⟩
  have hLc1 : σ1.vars "Lc" = σ.vars "Lc" := hfv "Lc" (by decide)
  have hj1 : σ1.vars "j" = j := by rw [hfv "j" (by decide)]; exact hj'
  have hMJ1 : σ1.arrs "MJ" = σ.arrs "MJ" := hfa "MJ" (by decide)
  have hMI1 : σ1.arrs "MI" = σ.arrs "MI" := hfa "MI" (by decide)
  have hCur1 : CurInv x cur σ1 := hCur.congr hLc1 hMJ1 hMI1
  have hone := hB
  have hlit : (Expr.lit 1).evalB B σ1 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hfvar : (V "f").evalB B σ1 = some (σ1.vars "f") :=
    evalB_var (by rcases hf01 with h | h <;> rw [h] <;> omega)
  have hcond := evalB_condEq hfvar hlit
  have hlen : cur.length ≤ j * universeSize x + i := hcur
  have hlt' : cur.length < universeSize x * setCount x := by
    have h1 : j * universeSize x + i < universeSize x * setCount x := by
      calc j * universeSize x + i < j * universeSize x + universeSize x := by omega
        _ = (j + 1) * universeSize x := by ring
        _ ≤ setCount x * universeSize x := Nat.mul_le_mul_right _ hj
        _ = universeSize x * setCount x := Nat.mul_comm _ _
    omega
  have hmemB : memB x j i = true ↔ σ1.vars "f" = 1 := by
    rw [hfiff, memB_iff]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      exact ⟨t - offset x j, by omega, by rw [Nat.add_sub_cancel' h1]; exact h3⟩
    · rintro ⟨s', hs, he⟩
      exact ⟨offset x j + s', by omega, by omega, he⟩
  -- the conditional
  have key : ∃ σ2 K2, Run B (Com.ite (.eq (V "f") (.lit 1)) collect .skip) σ1 σ2 K2 ∧
      K2 ≤ 1 + 3 + 20 ∧
      CurInv x (cur ++ (if memB x j i = true then [(j, i)] else [])) σ2 ∧
      (∀ y, y ≠ "Lc" → σ2.vars y = σ1.vars y) ∧
      (∀ a, a ≠ "MJ" → a ≠ "MI" → σ2.arrs a = σ1.arrs a) := by
    by_cases hf : σ1.vars "f" = 1
    · have hmem : memB x j i = true := hmemB.mpr hf
      have hcond' : (Cond.eq (V "f") (.lit 1)).evalB B σ1 = some true := by
        rw [hcond, hf]; simp
      obtain ⟨σ2, hr2, hσ2⟩ := (collect_spec (B := B) hlt').run
        ⟨hCur1, by rw [hj1]; exact hjB, by rw [hi1]; omega, by omega⟩
      refine ⟨σ2, _, Run.ite_true hcond' hr2, ?_, ?_, ?_, ?_⟩
      · simp [Cond.size]
      · rw [if_pos hmem]
        have := hCur1.push hlt' j i
        rw [hσ2, hj1, hi1]
        exact this
      · intro y hy; rw [hσ2]; simp [hy]
      · intro a h1 h2; rw [hσ2]; simp [h1, h2]
    · have hmem : ¬ memB x j i = true := fun h => hf (hmemB.mp h)
      have hcond' : (Cond.eq (V "f") (.lit 1)).evalB B σ1 = some false := by
        rw [hcond]; simp [hf]
      refine ⟨σ1, _, Run.ite_false hcond' Run.skip, ?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
      · simp [Cond.size]
      · rw [if_neg hmem, List.append_nil]; exact hCur1
  obtain ⟨σ2, K2, hr2, hK2, hCur2, hfv2, hfa2⟩ := key
  have hvar : (V "i").evalB B σ2 = some i := by
    have : σ2.vars "i" = i := by rw [hfv2 "i" (by decide), hi1]
    rw [← this]; exact evalB_var (by omega)
  have hlit2 : (Expr.lit 1).evalB B σ2 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hr3 := Run.assign (B := B) (σ := σ2) (x := "i") (e := .bin .add (V "i") (.lit 1))
    (v := i + 1) (evalB_bin hvar hlit2 (by show i + 1 < B; omega))
  refine ⟨_, _, hr1.seq (hr2.seq hr3), ?_, ?_⟩
  · simp only [Expr.size]; omega
  · have hv : ∀ y, y ≠ "Lc" → y ≠ "i" →
        (σ2.setVar "i" (i + 1)).vars y = σ1.vars y := by
      intro y h1 h2; simp [h2, hfv2 y h1]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by simp, ?_⟩
    · exact hRC1.congr (hv "n" (by decide) (by decide)) (hv "m" (by decide) (by decide))
        (by simp [hfa2 "OFF" (by decide) (by decide)])
        (by simp [hfa2 "MEM" (by decide) (by decide)])
    · rw [hv "j" (by decide) (by decide)]; exact hj1
    · rw [hv "bs" (by decide) (by decide)]; exact hbs1
    · rw [hv "bl" (by decide) (by decide)]; exact hbl1
    · exact hCur2.congr (by simp) (by simp) (by simp)

/-- The cost of one element. -/
def costI (N : ℕ) : ℕ := 2 + ((40 + 4) * N + 6) + (1 + 3 + 20) + 4 + 4

/-- Every element of the universe against set `j`. -/
def iLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) iBody)

theorem EI.setVar {j : ℕ} {σ : Env} (h : EI x j σ) {y : String} (v : ℕ)
    (hy : y ∉ ["n", "m", "j", "bs", "bl"]) : EI x j (σ.setVar y v) := by
  obtain ⟨hRC, h1, h2, h3⟩ := h
  have hne : ∀ z ∈ ["n", "m", "j", "bs", "bl"], z ≠ y := fun z hz h => hy (h ▸ hz)
  refine ⟨hRC.congr ?_ ?_ rfl rfl, ?_, ?_, ?_⟩
  · simp [hne "n" (by simp)]
  · simp [hne "m" (by simp)]
  · simp [hne "j" (by simp), h1]
  · simp [hne "bs" (by simp), h2]
  · simp [hne "bl" (by simp), h3]

theorem iLoop_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (j : ℕ)
    (hj : j < setCount x) (hmono : offset x j ≤ offset x (j + 1))
    (hle : offset x (j + 1) ≤ offset x (setCount x))
    (hLB : offset x (setCount x) < B) (hnB : universeSize x < B)
    (hmnB : universeSize x * setCount x + 1 < B) (hjB : j < B) :
    Spec B (fun σ => EI x j σ ∧ CurInv x (prefixPairs x j) σ) iLoop
      (fun _ σ' => EI x j σ' ∧ CurInv x (prefixPairs x (j + 1)) σ')
      ((costI (offset x (j + 1) - offset x j) + 4) * universeSize x + 6) := by
  refine (Spec.forRangeZero (B := B) "i" "n"
    (fun σ => EI x j σ ∧ σ.vars "i" ≤ universeSize x ∧
      CurInv x (prefixPairs x j ++ blockPairs x j (σ.vars "i")) σ)
    (universeSize x) (costI (offset x (j + 1) - offset x j)) hnB (fun _ h => h.2.1)
    (fun _ h => h.1.1.1) ?_).conseq ?_ ?_ le_rfl
  · refine Spec.of_exists fun σ ⟨⟨hE, hle', hCur⟩, hlt⟩ => ?_
    have hcur : (prefixPairs x j ++ blockPairs x j (σ.vars "i")).length ≤
        j * universeSize x + σ.vars "i" := by
      rw [List.length_append]
      have := length_prefixPairs_le (x := x) j
      have := length_blockPairs_le (x := x) j (σ.vars "i")
      omega
    obtain ⟨σ', hrun, hE', hi', hCur'⟩ :=
      (iBody_spec hxB hB j (σ.vars "i") _ hj hlt hmono hle hcur hLB hnB hmnB hjB).run
        ⟨hE, rfl, hCur⟩
    refine ⟨σ', _, hrun, le_rfl, ⟨hE', by omega, ?_⟩, hi'⟩
    · rw [hi', blockPairs_succ, ← List.append_assoc]; exact hCur'
  · rintro σ ⟨hE, hCur⟩
    refine ⟨hE.setVar 0 (by decide), by simp, ?_⟩
    · simp only [vars_setVar, if_true, blockPairs, List.range_zero, List.filter_nil, List.map_nil,
        List.append_nil]
      exact hCur.congr (by simp) (by simp) (by simp)
  · rintro σ σ' - ⟨⟨hE, -, hCur⟩, hi⟩
    rw [hi, ← prefixPairs_succ] at hCur
    exact ⟨hE, hCur⟩

/-- Take the block of set `j`: its start and its length. -/
def jSetup : Com :=
  .seq (.assign "bs" (.get "OFF" (V "j")))
    (.seq (.assign "be" (.get "OFF" (.bin .add (V "j") (.lit 1))))
      (.assign "bl" (.bin .sub (V "be") (V "bs"))))

theorem jSetup_spec {B : ℕ} (j : ℕ) (hj : j < setCount x) (hB : 1 < B)
    (hoB : offset x (j + 1) < B) (hoB' : offset x j < B) (hjB : j + 1 < B) :
    Spec B (fun σ => RC x σ ∧ σ.vars "j" = j) jSetup
      (fun σ σ' => σ'.vars "bs" = offset x j ∧ σ'.vars "bl" = offset x (j + 1) - offset x j ∧
        (∀ y, y ≠ "bs" → y ≠ "be" → y ≠ "bl" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) 30 := by
  refine Spec.pre (P := fun σ => RC x σ ∧ σ.vars "j" = j ∧
      (∀ h : j < (σ.arrs "OFF").length, (σ.arrs "OFF")[j] = offset x j) ∧
      (∀ h : j + 1 < (σ.arrs "OFF").length, (σ.arrs "OFF")[j + 1] = offset x (j + 1)) ∧
      j < (σ.arrs "OFF").length ∧ j + 1 < (σ.arrs "OFF").length) ?_ ?_
  · run_vcg
    all_goals (simp only [RC] at *; simp_all)
    all_goals omega
  · rintro σ ⟨hC, hj'⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := id hC
    refine ⟨hC, hj', fun h => ?_, fun h => ?_, by omega, by omega⟩
    · have := h3 j (by omega); rw [List.getD_eq_getElem _ _ h] at this; exact this
    · have := h3 (j + 1) (by omega); rw [List.getD_eq_getElem _ _ h] at this; exact this

/-- One set: its block, then every element against it, then the next set. -/
def jBody : Com := .seq jSetup (.seq iLoop (bump "j"))

variable (x) in
/-- What holds between sets: the read, and the pairs of the sets so far. -/
def JI (σ : Env) : Prop :=
  RC x σ ∧ σ.vars "j" ≤ setCount x ∧ CurInv x (prefixPairs x (σ.vars "j")) σ

/-- The offsets are nondecreasing, and none exceeds the last. -/
structure Offs (x : List ℕ) : Prop where
  mono : ∀ j < setCount x, offset x j ≤ offset x (j + 1)
  le_last : ∀ j ≤ setCount x, offset x j ≤ offset x (setCount x)

theorem jBody_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (ho : Offs x)
    (hLB : offset x (setCount x) < B) (hnB : universeSize x < B)
    (hmnB : universeSize x * setCount x + 1 < B) (hmB : setCount x < B) :
    Spec B (fun σ => JI x σ ∧ σ.vars "j" < setCount x) jBody
      (fun σ σ' => JI x σ' ∧ σ'.vars "j" = σ.vars "j" + 1)
      (30 + ((costI (offset x (setCount x)) + 4) * universeSize x + 6) + 4) := by
  refine Spec.of_exists fun σ ⟨⟨hRC, hle, hCur⟩, hlt⟩ => ?_
  have hj1 := ho.mono _ hlt
  have hj2 := ho.le_last (σ.vars "j" + 1) (by omega)
  have hj3 := ho.le_last (σ.vars "j") (by omega)
  obtain ⟨σ1, hr1, hbs1, hbl1, hfv1, harr1, hinp1, hout1⟩ :=
    (jSetup_spec (B := B) (σ.vars "j") hlt hB (by omega) (by omega) (by omega)).run ⟨hRC, rfl⟩
  have hE1 : EI x (σ.vars "j") σ1 := by
    refine ⟨hRC.congr ?_ ?_ ?_ ?_, ?_, hbs1, hbl1⟩
    · exact hfv1 "n" (by decide) (by decide) (by decide)
    · exact hfv1 "m" (by decide) (by decide) (by decide)
    · rw [harr1]
    · rw [harr1]
    · exact hfv1 "j" (by decide) (by decide) (by decide)
  have hC1 : CurInv x (prefixPairs x (σ.vars "j")) σ1 :=
    hCur.congr (hfv1 "Lc" (by decide) (by decide) (by decide)) (by rw [harr1]) (by rw [harr1])
  obtain ⟨σ2, hr2, hE2, hC2⟩ :=
    (iLoop_spec hxB hB (σ.vars "j") hlt hj1 (ho.le_last _ (by omega)) hLB hnB hmnB
      (by omega)).run ⟨hE1, hC1⟩
  have hone := hB
  have hj2v : σ2.vars "j" = σ.vars "j" := hE2.2.1
  have hlit : (Expr.lit 1).evalB B σ2 = some 1 := by
    simp only [Expr.evalB]; exact fit_self hone
  have hvar : (V "j").evalB B σ2 = some (σ.vars "j") :=
    hj2v ▸ evalB_var (by rw [hj2v]; omega)
  have hr3 := Run.assign (B := B) (σ := σ2) (x := "j") (e := .bin .add (V "j") (.lit 1))
    (v := σ.vars "j" + 1) (evalB_bin hvar hlit (by show σ.vars "j" + 1 < B; omega))
  have hcost : (costI (offset x (σ.vars "j" + 1) - offset x (σ.vars "j")) + 4) * universeSize x
      ≤ (costI (offset x (setCount x)) + 4) * universeSize x := by
    apply Nat.mul_le_mul_right
    unfold costI; omega
  refine ⟨_, _, hr1.seq (hr2.seq hr3), ?_, ?_⟩
  · simp only [Expr.size]; omega
  · refine ⟨⟨?_, ?_, ?_⟩, by simp⟩
    · exact hE2.1.congr (by simp) (by simp) (by simp) (by simp)
    · simp only [vars_setVar, if_true]; omega
    · simp only [vars_setVar, if_true]
      exact hC2.congr (by simp) (by simp) (by simp)

/-- **The membership pairs**: `Lc` of them, in `MJ` and `MI`. -/
def build : Com :=
  .seq (.assign "Lc" (.lit 0))
    (.seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "m")) jBody))

/-- The cost of `build`. -/
def costBuild (n m L : ℕ) : ℕ :=
  2 + (((30 + ((costI L + 4) * n + 6) + 4) + 4) * m + 6)

theorem build_spec {B : ℕ} (hxB : ∀ v ∈ x, v < B) (hB : 1 < B) (ho : Offs x)
    (hLB : offset x (setCount x) < B) (hnB : universeSize x < B)
    (hmnB : universeSize x * setCount x + 1 < B) (hmB : setCount x < B) :
    Spec B (fun σ => RC x σ ∧ universeSize x * setCount x ≤ (σ.arrs "MJ").length ∧
        universeSize x * setCount x ≤ (σ.arrs "MI").length) build
      (fun _ σ' => RC x σ' ∧ CurInv x (wmemberList x) σ')
      (costBuild (universeSize x) (setCount x) (offset x (setCount x))) := by
  have hloop := Spec.forRangeZero (B := B) "j" "m" (JI x) (setCount x)
    (30 + ((costI (offset x (setCount x)) + 4) * universeSize x + 6) + 4) hmB
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (jBody_spec hxB hB ho hLB hnB hmnB hmB)
  have hassign := Spec.assign (B := B)
    (P := fun σ => RC x σ ∧ universeSize x * setCount x ≤ (σ.arrs "MJ").length ∧
        universeSize x * setCount x ≤ (σ.arrs "MI").length)
    (x := "Lc") (e := .lit 0) (f := fun _ => 0) (fun σ _ => evalB_lit (by omega))
  refine (hassign.seq hloop (fun σ σ' hσ h => ?_)
    (fun σ σ' σ'' _ _ h2 => ?_)).mono ?_
  · obtain ⟨hC, h1, h2⟩ := hσ
    subst h
    refine ⟨hC.congr (by simp) (by simp) (by simp) (by simp), by simp, ?_⟩
    · simp only [vars_setVar, if_true, prefixPairs, List.range_zero, List.flatMap_nil]
      exact ⟨by simp, by simp, by simpa using h1, by simpa using h2⟩
  · obtain ⟨⟨hC, hle, hCur⟩, hj⟩ := h2
    rw [hj] at hCur
    exact ⟨hC, by rw [wmemberList_eq_prefix]; exact hCur⟩
  · unfold costBuild; simp only [Expr.size]; omega

end Lax496464Proofs.Ram.Build
