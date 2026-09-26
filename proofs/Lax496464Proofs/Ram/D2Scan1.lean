import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.D2Valid
import Lax496464Proofs.Ram.Sort
import Lax496464Proofs.Ram.ListUtil

/-!
# Theorem 2's machine, part 1: the scan of one set

`scanCom` does, on the number `zc` (a code of a nonempty set, `m` digits in base `nb = n+1`) and a
starting candidate `zy`, what `D2Scan.scanF` does on the tail of its digit string, and then builds
the number of the rotated string (`D2Scan.code_formula`) in `zcode`.  It costs `O(k+1)` with `k` the
number of thresholds passed, whatever `m` is.
-/

namespace Lax496464Proofs.Ram.D2Scan1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid

theorem mod_eq_sub (a b : ℕ) : a % b = a - a / b * b := by
  have := Nat.div_add_mod a b
  rw [Nat.mul_comm] at this
  omega

/-- `zx := zt mod nb`, with `zt` already assigned. -/
abbrev digE : Expr := .bin .sub (V "zt") (.bin .mul (.bin .div (V "zt") (V "nb")) (V "nb"))

/-- One digit: read the digit number `zi` of `zc`, and either pass it (advancing the candidate if
it equals it) or stop the scan. -/
def scanBody : Com :=
  .seq (.assign "zt"
      (.bin .div (V "zc") (.get "PW" (.bin .sub (.bin .sub (V "m") (.lit 1)) (V "zi")))))
    (.seq (.assign "zx" digE)
      (.ite (.lt (V "zx") (V "n"))
        (.ite (.lt (V "zcur") (V "zx"))
          (.assign "zlim" (.lit 0))
          (.seq (.ite (.eq (V "zx") (V "zcur")) (bump "zcur") .skip) (bump "zi")))
        (.assign "zlim" (.lit 0))))

theorem scanBody_spec {B : ℕ} (hB : 1 < B) (n b m c zi cur lim P : ℕ) :
    Spec B (fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = b ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧
        σ.vars "zi" = zi ∧ σ.vars "zcur" = cur ∧ σ.vars "zlim" = lim ∧ zi < m ∧
        (σ.arrs "PW").getD (m - 1 - zi) 0 = P ∧ m - 1 - zi < (σ.arrs "PW").length ∧
        c < B ∧ b < B ∧ n < B ∧ m < B ∧ P < B ∧ cur + 1 < B ∧ zi + 1 < B) scanBody
      (fun _σ σ' =>
        σ'.vars "zcur" = (if c / P % b < n ∧ c / P % b ≤ cur then
            (if c / P % b = cur then cur + 1 else cur) else cur) ∧
        σ'.vars "zi" = (if c / P % b < n ∧ c / P % b ≤ cur then zi + 1 else zi) ∧
        σ'.vars "zlim" = (if c / P % b < n ∧ c / P % b ≤ cur then lim else 0)) 60 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hc, hnb, hn, hm, hzi, hcur, hlim, hlt, hP, hlen, hcB, hbB, hnB, hmB, hPB, hcurB, hziB⟩ := hσ
  have hmod : ∀ t : ℕ, t - t / b * b = t % b := fun t => (mod_eq_sub t b).symm
  have hcP : c / P < B := lt_of_le_of_lt (Nat.div_le_self _ _) hcB
  have hcPb : c / P / b < B := lt_of_le_of_lt (Nat.div_le_self _ _) hcP
  have hcPb' : c / P / b * b < B := lt_of_le_of_lt (Nat.div_mul_le_self _ _) hcP
  have hcPm : c / P % b < B := lt_of_le_of_lt (Nat.mod_le _ _) hcP
  run_vcg
  all_goals (simp_all)

theorem scanF_cons_pos {n x cur : ℕ} {T : List ℕ} (h : x < n ∧ x ≤ cur) :
    scanF n (x :: T) cur =
      ((scanF n T (if x = cur then cur + 1 else cur)).1,
        (scanF n T (if x = cur then cur + 1 else cur)).2 + 1) := by
  simp [scanF, h]

theorem scanF_cons_neg {n x cur : ℕ} {T : List ℕ} (h : ¬ (x < n ∧ x ≤ cur)) :
    scanF n (x :: T) cur = (cur, 0) := by
  simp [scanF, h]

/-- The whole scan. -/
def scanLoop : Com := .while (.lt (V "zi") (V "zlim")) scanBody

/-- What the scan loop keeps: `T.drop (zi-1)` is what is left to scan. -/
def SInv (n b m c y : ℕ) (T PWl : List ℕ) (σ : Env) : Prop :=
  σ.vars "zc" = c ∧ σ.vars "nb" = b ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.arrs "PW" = PWl ∧
  1 ≤ σ.vars "zi" ∧ σ.vars "zi" ≤ m ∧ σ.vars "zcur" ≤ n ∧
  (σ.vars "zlim" = m ∨ σ.vars "zlim" = 0) ∧
  scanF n T y = ((scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur")).1,
    (σ.vars "zi" - 1) + (scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur")).2) ∧
  (σ.vars "zlim" = 0 → scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur") = (σ.vars "zcur", 0))

theorem scanLoop_spec {B : ℕ} (hB : 1 < B) (n b m c y : ℕ) (T PWl : List ℕ) (hb : b = n + 1)
    (hm : 1 ≤ m) (hT : T.length = m - 1)
    (hdig : ∀ i, 1 ≤ i → i < m → c / b ^ (m - 1 - i) % b = T.getD (i - 1) 0)
    (hPWl : PWl.length = m + 1) (hPW : ∀ i ≤ m, PWl.getD i 0 = b ^ i)
    (hcB : c < B) (hbB : b < B) (_hnB : n + 1 < B) (hmB : m < B) (hPB : ∀ i ≤ m, b ^ i < B)
    (hy : y ≤ n) :
    Spec B (fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = b ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧
        σ.arrs "PW" = PWl ∧ σ.vars "zcur" = y ∧ σ.vars "zi" = 1 ∧ σ.vars "zlim" = m) scanLoop
      (fun _σ σ' => σ'.vars "zcur" = (scanF n T y).1 ∧ σ'.vars "zi" = (scanF n T y).2 + 1)
      (64 * ((scanF n T y).2 + 1) + 4) := by
  classical
  have hdef : ∀ σ, SInv n b m c y T PWl σ → ∃ v, (Cond.lt (V "zi") (V "zlim")).evalB B σ = some v := by
    intro σ hI
    obtain ⟨-, -, -, -, -, -, hzim, -, hlim, -⟩ := hI
    exact evalB_condLt_vars (by omega) (by rcases hlim with h | h <;> omega)
  have hstep : ∀ σ, SInv n b m c y T PWl σ → (Cond.lt (V "zi") (V "zlim")).evalB B σ = some true →
      ∃ σ' K, Run B scanBody σ σ' K ∧ SInv n b m c y T PWl σ' ∧ 1 + (Cond.lt (V "zi") (V "zlim")).size + K +
        (fun σ : Env => if σ.vars "zlim" = 0 then 0 else
          64 * ((scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur")).2 + 1)) σ' ≤
        (fun σ : Env => if σ.vars "zlim" = 0 then 0 else
          64 * ((scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur")).2 + 1)) σ := by
    intro σ hI hv
    obtain ⟨hc, hnb, hn, hm', hPWσ, hzi1, hzim, hcurn, hlim, hscan, hstop⟩ := hI
    have hlt := lt_of_condLt_true hv
    have hlimm : σ.vars "zlim" = m := by
      rcases hlim with h | h
      · exact h
      · rw [h] at hlt; omega
    have hzi_lt : σ.vars "zi" < m := by omega
    have hPidx : m - 1 - σ.vars "zi" ≤ m := by omega
    have hPv : (σ.arrs "PW").getD (m - 1 - σ.vars "zi") 0 = b ^ (m - 1 - σ.vars "zi") := by
      rw [hPWσ]; exact hPW _ hPidx
    have hlenPW : m - 1 - σ.vars "zi" < (σ.arrs "PW").length := by rw [hPWσ, hPWl]; omega
    obtain ⟨σ', hrun, ⟨hzcur', hzi', hzlim'⟩, hfv, hfa, -, -⟩ :=
      (scanBody_spec hB n b m c (σ.vars "zi") (σ.vars "zcur") (σ.vars "zlim")
        (b ^ (m - 1 - σ.vars "zi"))).frame.run
        ⟨hc, hnb, hn, hm', rfl, rfl, rfl, hzi_lt, hPv, hlenPW, hcB, hbB, by omega, hmB,
          hPB _ hPidx, by omega, by omega⟩
    have hc' : σ'.vars "zc" = c := by rw [hfv "zc" (by decide)]; exact hc
    have hnb' : σ'.vars "nb" = b := by rw [hfv "nb" (by decide)]; exact hnb
    have hn' : σ'.vars "n" = n := by rw [hfv "n" (by decide)]; exact hn
    have hm'' : σ'.vars "m" = m := by rw [hfv "m" (by decide)]; exact hm'
    have hPW' : σ'.arrs "PW" = PWl := by rw [hfa "PW" (by decide)]; exact hPWσ
    have hx := hdig (σ.vars "zi") hzi1 hzi_lt
    have hTlen : σ.vars "zi" - 1 < T.length := by omega
    have hdrop : T.drop (σ.vars "zi" - 1) = T.getD (σ.vars "zi" - 1) 0 :: T.drop (σ.vars "zi") := by
      rw [List.drop_eq_getElem_cons hTlen, List.getD_eq_getElem _ _ hTlen]
      congr 2; omega
    rw [hx] at hzcur' hzi' hzlim'
    rw [hdrop] at hscan hstop
    have hsz : (Cond.lt (V "zi") (V "zlim")).size = 3 := rfl
    by_cases hcase : T.getD (σ.vars "zi" - 1) 0 < n ∧ T.getD (σ.vars "zi" - 1) 0 ≤ σ.vars "zcur"
    · simp only [hcase, and_self, if_true] at hzcur' hzi' hzlim'
      have hcur'n : σ'.vars "zcur" ≤ n := by
        rw [hzcur']; split_ifs with h
        · omega
        · exact hcurn
      rw [scanF_cons_pos hcase] at hscan
      rw [← hzcur'] at hscan
      have hzi'' : σ'.vars "zi" - 1 = σ.vars "zi" := by omega
      refine ⟨σ', 60, hrun, ⟨hc', hnb', hn', hm'', hPW', by omega, by omega, hcur'n,
        Or.inl (by omega), ?_, ?_⟩, ?_⟩
      · rw [hzi'', hzcur']
        rw [← hzcur'] at *
        simp only at hscan ⊢
        rw [hscan]
        ext <;> simp; omega
      · intro h; omega
      · show 1 + 3 + 60 + (if σ'.vars "zlim" = 0 then 0 else _) ≤ (if σ.vars "zlim" = 0 then 0 else _)
        rw [hzlim', hlimm, if_neg (by omega), if_neg (by omega), hzi'']
        rw [hdrop, scanF_cons_pos hcase, ← hzcur']
        simp only
        omega
    · simp only [hcase, if_false] at hzcur' hzi' hzlim'
      rw [scanF_cons_neg hcase] at hscan hstop
      refine ⟨σ', 60, hrun, ⟨hc', hnb', hn', hm'', hPW', by omega, by omega, by omega,
        Or.inr hzlim', ?_, ?_⟩, ?_⟩
      · rw [hzi', hzcur', hdrop, scanF_cons_neg hcase]
        simp only at hscan ⊢
        exact hscan
      · intro _
        rw [hzi', hzcur', hdrop, scanF_cons_neg hcase]
      · show 1 + 3 + 60 + (if σ'.vars "zlim" = 0 then 0 else _) ≤ (if σ.vars "zlim" = 0 then 0 else _)
        rw [hzlim', if_pos rfl, hlimm, if_neg (by omega), hdrop, scanF_cons_neg hcase]
        omega
  have hloop := Spec.while_potential (B := B) (b := Cond.lt (V "zi") (V "zlim")) (c := scanBody)
    (P := fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = b ∧ σ.vars "n" = n ∧ σ.vars "m" = m ∧
        σ.arrs "PW" = PWl ∧ σ.vars "zcur" = y ∧ σ.vars "zi" = 1 ∧ σ.vars "zlim" = m)
    (K := 64 * ((scanF n T y).2 + 1) + 4) (SInv n b m c y T PWl)
    (fun σ : Env => if σ.vars "zlim" = 0 then 0 else
      64 * ((scanF n (T.drop (σ.vars "zi" - 1)) (σ.vars "zcur")).2 + 1))
    hdef hstep
    (by
      rintro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨h1, h2, h3, h4, h5, by omega, by omega, by omega, Or.inl h8, ?_, ?_⟩
      · rw [h7, h6]; simp
      · intro h; omega)
    (by
      rintro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      show (if σ.vars "zlim" = 0 then 0 else _) + 1 + (Cond.lt (V "zi") (V "zlim")).size ≤ _
      rw [if_neg (by omega), h7, h6]
      simp only [Nat.sub_self, List.drop_zero]
      show _ ≤ _
      have : (Cond.lt (V "zi") (V "zlim")).size = 3 := rfl
      omega)
  refine hloop.post ?_
  rintro σ σ' hpre ⟨hI, hfalse⟩
  obtain ⟨hc, hnb, hn, hm', hPWσ, hzi1, hzim, hcurn, hlim, hscan, hstop⟩ := hI
  have hle := le_of_condLt_false hfalse
  have hr : scanF n (T.drop (σ'.vars "zi" - 1)) (σ'.vars "zcur") = (σ'.vars "zcur", 0) := by
    rcases hlim with h | h
    · have hzi : σ'.vars "zi" = m := by omega
      rw [List.drop_eq_nil_of_le (by omega)]
      simp [scanF]
    · exact hstop h
  rw [hr] at hscan
  simp only at hscan
  have h1 := congrArg Prod.fst hscan
  have h2 := congrArg Prod.snd hscan
  simp only at h1 h2
  exact ⟨h1.symm, by omega⟩

/-- Build the number of the rotated string from `zc`, `zi` (`= k + 1`) and `zcur`. -/
def scanFin : Com :=
  .seq (.assign "zq" (.bin .sub (V "m") (V "zi")))
    (.seq (.assign "zt" (.bin .div (V "zc") (.get "PW" (V "zq"))))
      (.seq (.assign "zu" (.bin .div (V "zt") (.get "PW" (.bin .sub (V "zi") (.lit 1)))))
        (.seq (.assign "zp"
            (.bin .sub (V "zt") (.bin .mul (V "zu") (.get "PW" (.bin .sub (V "zi") (.lit 1))))))
          (.seq (.assign "zp" (.bin .add (.bin .mul (V "zp") (V "nb")) (V "zcur")))
            (.seq (.assign "zw" (.bin .sub (V "zc") (.bin .mul (V "zt") (.get "PW" (V "zq")))))
              (.assign "zcode" (.bin .add (.bin .mul (V "zp") (.get "PW" (V "zq"))) (V "zw"))))))))

/-- The number of the rotated string, as the formula of `D2Scan.code_formula`. -/
def rotCode (b m c k cur : ℕ) : ℕ :=
  ((c / b ^ (m - (k + 1)) % b ^ k) * b + cur) * b ^ (m - (k + 1)) + c % b ^ (m - (k + 1))

set_option maxHeartbeats 1000000 in
theorem scanFin_spec {B : ℕ} (hB : 1 < B) (b m c k cur : ℕ) (PWl : List ℕ) (hk : k + 1 ≤ m)
    (hPWl : PWl.length = m + 1) (hPW : ∀ i ≤ m, PWl.getD i 0 = b ^ i)
    (hb : 0 < b) (hcB : c < B) (hbB : b < B) (hmB : m < B) (hPB : ∀ i ≤ m, b ^ i < B)
    (hnewB : rotCode b m c k cur < B) (hcurB : cur < B) :
    Spec B (fun σ => σ.vars "zc" = c ∧ σ.vars "nb" = b ∧ σ.vars "m" = m ∧ σ.vars "zi" = k + 1 ∧
        σ.vars "zcur" = cur ∧ σ.arrs "PW" = PWl) scanFin
      (fun _σ σ' => σ'.vars "zcode" = rotCode b m c k cur) 100 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hc, hnb, hm, hzi, hcur, hPWσ⟩ := hσ
  have hP1 : (σ.arrs "PW").getD (m - (k + 1)) 0 = b ^ (m - (k + 1)) := by
    rw [hPWσ]; exact hPW _ (by omega)
  have hP2 : (σ.arrs "PW").getD (k + 1 - 1) 0 = b ^ k := by
    rw [hPWσ]; simpa using hPW k (by omega)
  have hl1 : m - (k + 1) < (σ.arrs "PW").length := by rw [hPWσ, hPWl]; omega
  have hl2 : k + 1 - 1 < (σ.arrs "PW").length := by rw [hPWσ, hPWl]; omega
  have hq : b ^ (m - (k + 1)) < B := hPB _ (by omega)
  have hqk : b ^ k < B := hPB _ (by omega)
  have hzt : c / b ^ (m - (k + 1)) < B := lt_of_le_of_lt (Nat.div_le_self _ _) hcB
  have hzu : c / b ^ (m - (k + 1)) / b ^ k < B := lt_of_le_of_lt (Nat.div_le_self _ _) hzt
  have hzu' : c / b ^ (m - (k + 1)) / b ^ k * b ^ k < B :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) hzt
  have hmod : ∀ t d : ℕ, t - t / d * d = t % d := fun t d => (mod_eq_sub t d).symm
  have hmod2 : c - c / b ^ (m - (k + 1)) * b ^ (m - (k + 1)) = c % b ^ (m - (k + 1)) := hmod _ _
  have hzp1 : c / b ^ (m - (k + 1)) % b ^ k < B := lt_of_le_of_lt (Nat.mod_le _ _) hzt
  have hpos : 0 < b ^ (m - (k + 1)) := pow_pos hb _
  have hrot : rotCode b m c k cur = ((c / b ^ (m - (k + 1)) % b ^ k) * b + cur) *
      b ^ (m - (k + 1)) + c % b ^ (m - (k + 1)) := rfl
  have hz1 : (c / b ^ (m - (k + 1)) % b ^ k) * b + cur < B := by
    have : (c / b ^ (m - (k + 1)) % b ^ k) * b + cur ≤ rotCode b m c k cur := by
      rw [hrot]
      have h1 : 1 ≤ b ^ (m - (k + 1)) := hpos
      nlinarith [Nat.zero_le (c % b ^ (m - (k + 1)))]
    omega
  have hz2 : (c / b ^ (m - (k + 1)) % b ^ k) * b < B := by omega
  have hz3 : c / b ^ (m - (k + 1)) * b ^ (m - (k + 1)) < B :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) hcB
  have hz4 : ((c / b ^ (m - (k + 1)) % b ^ k) * b + cur) * b ^ (m - (k + 1)) < B := by
    have : ((c / b ^ (m - (k + 1)) % b ^ k) * b + cur) * b ^ (m - (k + 1)) ≤ rotCode b m c k cur := by
      rw [hrot]; omega
    omega
  run_vcg
  all_goals (simp_all)

/-- `zcur := zy; zi := 1; zlim := m`. -/
def scanInit : Com :=
  .seq (.assign "zcur" (V "zy")) (.seq (.assign "zi" (.lit 1)) (.assign "zlim" (V "m")))

theorem scanInit_spec {B : ℕ} (hB : 1 < B) (y m : ℕ) (hyB : y < B) (hmB : m < B) :
    Spec B (fun σ => σ.vars "zy" = y ∧ σ.vars "m" = m) scanInit
      (fun _σ σ' => σ'.vars "zcur" = y ∧ σ'.vars "zi" = 1 ∧ σ'.vars "zlim" = m) 6 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hy, hm⟩ := hσ
  run_vcg
  all_goals (simp_all)

/-- The whole scan of one set: from the number `zc` and the candidate `zy`, the number `zcode`
of the set with the smallest threshold replaced. -/
def scanCom : Com := .seq scanInit (.seq scanLoop scanFin)

theorem hdig_of {n m j : ℕ} {Zs : List ℕ} (hsl : SL n m (j :: Zs)) (hm : 1 ≤ m) :
    ∀ i, 1 ≤ i → i < m →
      codeL n m (j :: Zs) / (n + 1) ^ (m - 1 - i) % (n + 1) =
        (lstOf n (m - 1) Zs).getD (i - 1) 0 := by
  intro i hi1 him
  have hZ1 : Zs.length ≤ m - 1 := (sl_tail hsl).len
  have hc : codeL n m (j :: Zs) = enc (n + 1) (j :: lstOf n (m - 1) Zs) := by
    unfold codeL; rw [lstOf_cons hm hZ1]
  have hTsl : SL n (m - 1) Zs := sl_tail hsl
  have hjn : j < n + 1 := by have := hsl.lt j (by simp); omega
  have hd := dig_enc (b := n + 1) (by omega) (L := j :: lstOf n (m - 1) Zs)
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hjn
      · exact hTsl.lstOf_lt x hx) i (by simp [hTsl.lstOf_length]; omega)
  have hlen : (j :: lstOf n (m - 1) Zs).length = m := by simp [hTsl.lstOf_length]; omega
  rw [hlen] at hd
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [List.getD_cons_succ] at hd
  rw [hc]
  simp only [Nat.add_sub_cancel]
  rw [hd]
  unfold dig
  rfl

set_option maxHeartbeats 1000000 in
theorem scanCom_spec {B : ℕ} (hB : 1 < B) (n m j y : ℕ) (Zs : List ℕ) (PWl : List ℕ)
    (hsl : SL n m (j :: Zs)) (hm : 1 ≤ m) (hy : y ≤ n)
    (hPWl : PWl.length = m + 1) (hPW : ∀ i ≤ m, PWl.getD i 0 = (n + 1) ^ i)
    (hNB : (n + 1) ^ m < B) (hmB : m < B) :
    Spec B (fun σ => σ.vars "zc" = codeL n m (j :: Zs) ∧ σ.vars "nb" = n + 1 ∧ σ.vars "n" = n ∧
        σ.vars "m" = m ∧ σ.arrs "PW" = PWl ∧ σ.vars "zy" = y) scanCom
      (fun _σ σ' => σ'.vars "zcode" = codeL n m (newL n Zs
          (scanF n (lstOf n (m - 1) Zs) y).1 (scanF n (lstOf n (m - 1) Zs) y).2))
      (64 * (Zs.length + 1) + 110) := by
  have hTsl : SL n (m - 1) Zs := sl_tail hsl
  have hjn : j < n + 1 := by have := hsl.lt j (by simp); omega
  have hokay0 : ScanOK n Zs y (scanF n (lstOf n (m - 1) Zs) y) :=
    scanF_ok n Zs (m - 1 - Zs.length) y (List.sortedLT_iff_pairwise.mp hTsl.sorted) hTsl.lt hy
  obtain ⟨cur, k, hrk⟩ : ∃ cur k, scanF n (lstOf n (m - 1) Zs) y = (cur, k) := ⟨_, _, rfl⟩
  rw [hrk] at hokay0
  simp only [hrk]
  have hokay : ScanOK n Zs y (cur, k) := hokay0
  have hk : k ≤ Zs.length := hokay.k_le
  have hZ1 : Zs.length ≤ m - 1 := hTsl.len
  have hcurn : cur ≤ n := hokay.le_n
  have hb1 : n + 1 ≤ (n + 1) ^ m := Nat.le_self_pow (by omega) _
  have hPB : ∀ i ≤ m, (n + 1) ^ i < B := fun i hi =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hi) hNB
  have hcB : codeL n m (j :: Zs) < B := lt_trans hsl.codeL_lt hNB
  have hform := code_formula (m := m) (j := j) hm hTsl hjn hokay (by omega)
  have hnewsl := newL_sl hm hTsl hokay
  have hsub : m - (k + 1) = m - 1 - k := by omega
  have hnewB : rotCode (n + 1) m (codeL n m (j :: Zs)) k cur < B := by
    have : rotCode (n + 1) m (codeL n m (j :: Zs)) k cur = codeL n m (newL n Zs cur k) := by
      rw [hform]; simp only [rotCode, hsub]
    rw [this]; exact lt_trans hnewsl.codeL_lt hNB
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hc, hnb, hn, hm', hPWσ, hyσ⟩ := hσ
  -- init
  obtain ⟨σ1, hr1, ⟨hcur1, hzi1, hlim1⟩, hfv1, hfa1, -, -⟩ :=
    (scanInit_spec hB y m (by omega) hmB).frame.run ⟨hyσ, hm'⟩
  have hc1 : σ1.vars "zc" = codeL n m (j :: Zs) := by rw [hfv1 "zc" (by decide)]; exact hc
  have hnb1 : σ1.vars "nb" = n + 1 := by rw [hfv1 "nb" (by decide)]; exact hnb
  have hn1 : σ1.vars "n" = n := by rw [hfv1 "n" (by decide)]; exact hn
  have hm1 : σ1.vars "m" = m := by rw [hfv1 "m" (by decide)]; exact hm'
  have hPW1 : σ1.arrs "PW" = PWl := by rw [hfa1 "PW" (by decide)]; exact hPWσ
  -- the loop
  obtain ⟨σ2, hr2, ⟨hcur2, hzi2⟩, hfv2, hfa2, -, -⟩ :=
    (scanLoop_spec hB n (n + 1) m (codeL n m (j :: Zs)) y (lstOf n (m - 1) Zs) PWl rfl hm
      hTsl.lstOf_length (hdig_of hsl hm) hPWl hPW hcB (by omega) (by omega) hmB hPB hy).frame.run
      ⟨hc1, hnb1, hn1, hm1, hPW1, hcur1, hzi1, hlim1⟩
  have hc2 : σ2.vars "zc" = codeL n m (j :: Zs) := by rw [hfv2 "zc" (by decide)]; exact hc1
  have hnb2 : σ2.vars "nb" = n + 1 := by rw [hfv2 "nb" (by decide)]; exact hnb1
  have hm2 : σ2.vars "m" = m := by rw [hfv2 "m" (by decide)]; exact hm1
  have hPW2 : σ2.arrs "PW" = PWl := by rw [hfa2 "PW" (by decide)]; exact hPW1
  -- the end
  rw [hrk] at hcur2 hzi2
  simp only at hcur2 hzi2
  obtain ⟨σ3, hr3, hcode3⟩ :=
    (scanFin_spec hB (n + 1) m (codeL n m (j :: Zs)) k cur PWl (by omega) hPWl hPW (by omega)
      hcB (by omega) hmB hPB hnewB (by omega)).run
      ⟨hc2, hnb2, hm2, hzi2, hcur2, hPW2⟩
  rw [hrk] at hr2
  simp only at hr2
  refine ⟨σ3, 6 + ((64 * (k + 1) + 4) + 100), hr1.seq (hr2.seq hr3), by omega, ?_⟩
  rw [hcode3, hform]
  simp only [rotCode, hsub]

end Lax496464Proofs.Ram.D2Scan1
