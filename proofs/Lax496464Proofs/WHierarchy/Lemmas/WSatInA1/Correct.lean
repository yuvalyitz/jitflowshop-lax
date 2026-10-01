import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula

/-! # Correctness: a weight-`k` satisfying set exists iff the sentence holds in the structure

Stated on the list of clause codes `cl`: `weightC cl k` says that some `k` variables of the
occurrences, set to true, satisfy every clause. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Correct

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula
open Lax496464Proofs.WHierarchy.HittingSet.Compress (getD_idxOf getD_mem)

variable (cl : List (List ℕ)) (d k : ℕ)

/-- The set `S` of variables, set to true, satisfies every clause. -/
def satC (S : Finset ℕ) : Prop :=
  ∀ c < cl.length, ∃ p < len cl c,
    (code cl (off cl c + p) % 2 = 0 ∧ code cl (off cl c + p) / 2 ∈ S) ∨
    (code cl (off cl c + p) % 2 = 1 ∧ code cl (off cl c + p) / 2 ∉ S)

/-- Some `k` variables of the occurrences, set to true, satisfy every clause. -/
def weightC : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, ∃ j < nL cl, code cl j / 2 = v) ∧ S.card = k ∧ satC cl S

/-! ### Facts about representatives -/

theorem varList_mem {j : ℕ} (hj : j < nL cl) : code cl j / 2 ∈ varList cl := mem_varList cl hj

theorem rep_lt {v : ℕ} (hv : v ∈ varList cl) : rep cl v < nL cl := by
  have := List.idxOf_lt_length_of_mem hv; rwa [length_varList] at this

theorem fst_eq_self_of {u j : ℕ} (hj : j < nL cl) (hu : u = fst cl j) : fst cl u = u := by
  subst hu; exact fst_fst cl hj

theorem getD_lt_of {B : ℕ} : ∀ (l : List ℕ) (j : ℕ) {dflt : ℕ}, (∀ e ∈ l, e < B) → dflt < B →
    l.getD j dflt < B
  | [], _, _, _, h => by simpa using h
  | a :: l, 0, _, h, _ => by simpa using h a (by simp)
  | a :: l, j + 1, _, h, hd => by
    simpa using getD_lt_of l j (fun e he => h e (by simp [he])) hd

/-! ### From a satisfying set to a model -/

theorem forward (hd : ∀ C ∈ cl, C.length ≤ d) (h : weightC cl k) :
    Models (A cl d k) (phi d k) := by
  obtain ⟨S, hSv, hSk, hsat⟩ := h
  have hlen := len_le_of_dcnf cl hd
  set sl := S.sort (· ≤ ·) with hsl
  have hsl_len : sl.length = k := by rw [hsl, Finset.length_sort, hSk]
  have hsl_nd : sl.Nodup := Finset.sort_nodup _ _
  have hsl_mem : ∀ v, v ∈ sl ↔ v ∈ S := fun v => Finset.mem_sort _
  have hSvar : ∀ v ∈ S, v ∈ varList cl := by
    intro v hv; obtain ⟨j, hj, rfl⟩ := hSv v hv; exact varList_mem cl hj
  -- the values of the `x_i` and of `w`
  set ρx : ℕ → ℕ := fun i => if i < k then rep cl (sl.getD i 0) else nL cl with hρx
  have hsl_get : ∀ i < k, sl.getD i 0 ∈ S := fun i hi =>
    (hsl_mem _).mp (getD_mem (by rw [hsl_len]; exact hi))
  set T : Finset ℕ := S.image (rep cl) with hT
  have hTcard : T.card ≤ k := hSk ▸ Finset.card_image_le
  have hρxT : ∀ i < k, ρx i ∈ T := fun i hi => by
    simp only [hρx, if_pos hi, hT, Finset.mem_image]; exact ⟨_, hsl_get i hi, rfl⟩
  have hTρx : ∀ e ∈ T, ∃ i < k, ρx i = e := by
    intro e he
    simp only [hT, Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem ((hsl_mem v).mpr hv)
    refine ⟨i, by omega, ?_⟩
    simp only [hρx, if_pos (show i < k by omega)]
    rw [List.getD_eq_getElem _ _ hi, hiv]
  have hTlt : ∀ e ∈ T, e < nL cl := by
    intro e he
    simp only [hT, Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he; exact rep_lt cl (hSvar v hv)
  -- a representative in `T` belongs to a variable in `S`
  have hrepT : ∀ j < nL cl, fst cl j ∈ T → code cl j / 2 ∈ S := by
    intro j hj hm
    simp only [hT, Finset.mem_image] at hm
    obtain ⟨v, hv, he⟩ := hm
    rw [fst_eq_rep] at he
    rw [← rep_inj cl (hSvar v hv) he]; exact hv
  -- the search succeeds for every key made of the `x_i` and `w`
  have hY : ∀ t, ∃ y : List ℕ, y.length = k + 1 ∧ (∀ e ∈ y, e ∈ T ∨ e = nL cl) ∧
      ((vt d k t).map ρx ∈ (A cl d k).rel 2 → (vt d k t).map ρx ++ y ∈ lTuples cl d k) := by
    intro t
    by_cases hg : (vt d k t).map ρx ∈ (A cl d k).rel 2
    · obtain ⟨c, hc, hkey⟩ := (rel2 cl d k).mp hg
      have hkeyT : ∀ x ∈ key cl d c, x ∈ T ∨ x = nL cl := by
        intro x hx
        rw [← hkey] at hx
        simp only [List.mem_map] at hx
        obtain ⟨i, -, rfl⟩ := hx
        by_cases hi : i < k
        · exact Or.inl (hρxT i hi)
        · right; simp [hρx, hi]
      have hhit : ∀ c2 < cl.length, key cl d c2 = key cl d c →
          ∃ i < len cl c2, code cl (off cl c2 + i) % 2 = 0 ∧ fst cl (off cl c2 + i) ∈ T := by
        intro c2 hc2 hk2
        obtain ⟨p, hp, hlit⟩ := hsat c2 hc2
        have hocc := off_lt cl hc2 hp
        rcases hlit with ⟨he, hin⟩ | ⟨ho, hnin⟩
        · refine ⟨p, hp, he, ?_⟩
          simp only [hT, Finset.mem_image]
          exact ⟨_, hin, (fst_eq_rep cl _).symm⟩
        · exfalso
          have hmem : keyE cl c2 p ∈ key cl d c2 := by
            simp only [key, List.mem_map, List.mem_range]
            exact ⟨p, by have := hlen c2; omega, rfl⟩
          rw [hk2] at hmem
          have hke : keyE cl c2 p = fst cl (off cl c2 + p) := by
            simp only [keyE, if_pos hp, if_neg (show ¬ code cl (off cl c2 + p) % 2 = 0 by omega)]
          rcases hkeyT _ hmem with hm | hm
          · rw [hke] at hm; exact hnin (hrepT _ hocc hm)
          · rw [hke] at hm; have := fst_lt cl hocc; omega
      obtain ⟨b, hb, ch, hsim, hchT⟩ := sim_complete cl d k c T hTcard hc hlen hhit
      obtain ⟨hchk, -, -⟩ := sim_sound cl d k c hsim
      refine ⟨pad cl k ch, length_pad cl k ch, fun e he => ?_, fun _ => ?_⟩
      · rcases mem_pad cl k he with he | he
        · exact Or.inl (hchT e he)
        · exact Or.inr he
      · rw [hkey]; exact (mem_lTuples cl d k).mpr ⟨c, hc, b, hb, ch, hsim, rfl⟩
    · exact ⟨List.replicate (k + 1) (nL cl), by simp, fun e he => Or.inr
        (List.eq_of_mem_replicate he), fun h => absurd h hg⟩
  choose Y hYlen hYent hYL using hY
  -- the assignment
  set ρ : Assignment := fun v => if v < k + 1 then ρx v else
    (Y ((v - (k + 1)) / (k + 1))).getD ((v - (k + 1)) % (k + 1)) (nL cl) with hρ
  have hρlow : ∀ v < k + 1, ρ v = ρx v := fun v hv => by
    simp only [hρ]; rw [if_pos hv]
  have hρy : ∀ t, ∀ j < k + 1, ρ (yv k t j) = (Y t).getD j (nL cl) := by
    intro t j hj
    have h1 : ¬ yv k t j < k + 1 := by unfold yv; omega
    have h2 : yv k t j - (k + 1) = j + (k + 1) * t := by unfold yv; ring_nf; omega
    simp only [hρ, if_neg h1, h2, Nat.add_mul_div_left _ _ (show 0 < k + 1 by omega),
      Nat.div_eq_of_lt hj, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hvt : ∀ t, (vt d k t).map ρ = (vt d k t).map ρx :=
    fun t => List.map_congr_left fun v hv => hρlow v (vt_lt d k t v hv)
  have hyt : ∀ t, (yt k t).map ρ = Y t := by
    intro t
    refine List.ext_getElem (by simp [yt, hYlen]) fun j h1 h2 => ?_
    simp only [yt, List.getElem_map, List.getElem_range]
    rw [hρy t j (by simpa [yt] using h1), List.getD_eq_getElem _ _ h2]
  have hρk : ρ k = nL cl := by rw [hρlow k (by omega)]; simp [hρx]
  -- the sentence holds
  have hsat_psi : Sat (A cl d k) ∅ (psi d k) ρ := by
    rw [sat_psi]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hρk, rel0]
    · intro i hi
      rw [hρlow i (by omega), rel1]
      obtain ⟨j, hj, hjv⟩ := hSv _ (hsl_get i hi)
      refine ⟨j, hj, ?_⟩
      simp only [hρx, if_pos hi, fst_eq_rep, hjv]
    · intro i hi j hj he
      rw [hρlow i (by omega), hρlow j (by omega)] at he
      simp only [hρx, if_pos hi, if_pos (show j < k by omega)] at he
      have := rep_inj cl (hSvar _ (hsl_get i hi)) he
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
      have := (List.Nodup.getElem_inj_iff hsl_nd).mp this
      omega
    · intro t ht hg
      rw [hvt] at hg
      refine ⟨?_, fun j hj => ?_⟩
      · rw [List.map_append, hvt, hyt, rel3]; exact hYL t hg
      · rw [hρy t j hj]
        have hmem : (Y t).getD j (nL cl) ∈ Y t := by
          rw [List.getD_eq_getElem _ _ (by rw [hYlen]; exact hj)]; exact List.getElem_mem _
        rcases hYent t _ hmem with he | he
        · obtain ⟨i, hi, hie⟩ := hTρx _ he
          exact ⟨i, by omega, by rw [hρlow i (by omega), hie]⟩
        · exact ⟨k, by omega, by rw [hρk, he]⟩
  -- the values lie in the universe
  have hbound : ∀ v, ρ v < nL cl + 1 := by
    intro v
    by_cases hv : v < k + 1
    · rw [hρlow v hv]
      simp only [hρx]
      split_ifs with hi
      · have := hTlt _ (hρxT v hi); simp only [hρx, if_pos hi] at this; omega
      · omega
    · simp only [hρ, if_neg hv]
      refine getD_lt_of _ _ (fun e he => ?_) (by omega)
      rcases hYent _ e he with he | he
      · have := hTlt _ he; omega
      · omega
  rw [models_iff_of_sentence (isSentence_phi d k) ρ]
  refine ⟨fits_phi d k, noSetVar_phi d k, ?_⟩
  unfold phi
  rw [sat_exBlock]
  exact ⟨ρ, fun _ _ => rfl, fun v _ => hbound v, hsat_psi⟩

/-! ### From a model to a satisfying set -/

theorem backward (h : Models (A cl d k) (phi d k)) : weightC cl k := by
  obtain ⟨-, -, ρ0, -, hs⟩ := h
  unfold phi at hs
  rw [sat_exBlock] at hs
  obtain ⟨ρ, -, -, hψ⟩ := hs
  rw [sat_psi] at hψ
  obtain ⟨h0, h1, hdist, hcl⟩ := hψ
  have hρk : ρ k = nL cl := by simpa [rel0] using (rel0 cl d k).mp h0
  have hx : ∀ i < k, ∃ j < nL cl, ρ i = fst cl j := fun i hi => (rel1 cl d k).mp (h1 i hi)
  have hxlt : ∀ i < k, ρ i < nL cl := by
    intro i hi; obtain ⟨j, hj, he⟩ := hx i hi; rw [he]; exact fst_lt cl hj
  have hxfst : ∀ i < k, fst cl (ρ i) = ρ i := by
    intro i hi; obtain ⟨j, hj, he⟩ := hx i hi; exact fst_eq_self_of cl hj he
  -- the set of variables
  set S : Finset ℕ := (Finset.range k).image fun i => code cl (ρ i) / 2 with hS
  have hinj : ∀ i < k, ∀ i' < k, code cl (ρ i) / 2 = code cl (ρ i') / 2 → i = i' := by
    intro i hi i' hi' he
    have := (fst_eq_iff cl (hxlt i hi) (hxlt i' hi')).mpr he
    rw [hxfst i hi, hxfst i' hi'] at this
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hdist i' hi' i hlt this.symm
    · exact hdist i hi i' hlt this
  have hcard : S.card = k := by
    rw [hS, Finset.card_image_of_injOn (fun i hi i' hi' he => hinj i (by simpa using hi) i'
      (by simpa using hi') he)]
    simp
  -- an occurrence whose variable is in `S` has its representative among the `x_i`
  have hmemS : ∀ j < nL cl, code cl j / 2 ∈ S → ∃ i < k, fst cl j = ρ i := by
    intro j hj hm
    simp only [hS, Finset.mem_image, Finset.mem_range] at hm
    obtain ⟨i, hi, he⟩ := hm
    refine ⟨i, hi, ?_⟩
    rw [← hxfst i hi]; exact (fst_eq_iff cl hj (hxlt i hi)).mpr he.symm
  refine ⟨S, fun v hv => ?_, hcard, fun c hc => ?_⟩
  · simp only [hS, Finset.mem_image, Finset.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨_, hxlt i hi, rfl⟩
  · by_contra hno
    push Not at hno
    -- the digits of the key of `c`
    have hδ : ∀ p, ∃ i < k + 1, keyE cl c p = ρ i := by
      intro p
      unfold keyE
      split_ifs with hp he
      · exact ⟨k, by omega, hρk.symm⟩
      · have ho : code cl (off cl c + p) % 2 = 1 := by omega
        have hocc := off_lt cl hc hp
        have hin : code cl (off cl c + p) / 2 ∈ S := (hno p hp).2 ho
        obtain ⟨i, hi, he'⟩ := hmemS _ hocc hin
        exact ⟨i, by omega, he'⟩
      · exact ⟨k, by omega, hρk.symm⟩
    choose δ hδlt hδe using hδ
    obtain ⟨t, ht, hdig⟩ := exists_digits (k + 1) (d + 1) δ fun p _ => hδlt p
    have hvt : (vt d k t).map ρ = key cl d c := by
      simp only [vt, key, List.map_map]
      refine List.map_congr_left fun p hp => ?_
      simp only [Function.comp, hdig p (List.mem_range.mp hp)]
      exact (hδe p).symm
    obtain ⟨h3, hin⟩ := hcl t ht (by rw [hvt]; exact (rel2 cl d k).mpr ⟨c, hc, rfl⟩)
    rw [rel3, List.map_append, hvt, mem_lTuples] at h3
    obtain ⟨c', hc', b, -, ch, hsim, heq⟩ := h3
    obtain ⟨hk1, hk2⟩ := List.append_inj heq (by simp [length_key])
    obtain ⟨hchk, -, hhit⟩ := sim_sound cl d k c' hsim
    obtain ⟨i, hi, hev, hmem⟩ := (hitB_iff cl ch c).mp (hhit c hc hk1)
    have hocc := off_lt cl hc hi
    have hpad := mem_pad_of_mem cl k (by omega) hmem
    rw [← hk2] at hpad
    simp only [yt, List.map_map, List.mem_map, List.mem_range] at hpad
    obtain ⟨j, hj, hje⟩ := hpad
    obtain ⟨i', hi', hi'e⟩ := hin j hj
    simp only [Function.comp] at hje
    rw [hi'e] at hje
    by_cases hik : i' < k
    · have : code cl (off cl c + i) / 2 ∈ S := by
        simp only [hS, Finset.mem_image, Finset.mem_range]
        refine ⟨i', hik, ?_⟩
        rw [hje, code_fst cl hocc]
      exact (hno i hi).1 hev this
    · have : i' = k := by omega
      rw [this, hρk] at hje
      have := fst_lt cl hocc; omega

/-- **Correctness.** -/
theorem weightC_iff (hd : ∀ C ∈ cl, C.length ≤ d) :
    weightC cl k ↔ Models (A cl d k) (phi d k) :=
  ⟨forward cl d k hd, backward cl d k⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Correct
