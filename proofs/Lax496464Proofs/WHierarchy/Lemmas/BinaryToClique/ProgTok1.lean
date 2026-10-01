import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr

/-!
# Σ₁[2] model checking to Clique: one step of the tokenizer, per tag

`Corr x st σ`: the machine state `σ` holds the tokenizer state `st` (arrays filled from the front).
Each kind of node — relation atom, equation, other — moves `Corr x st` to `Corr x (step st)`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-- The machine state holds the tokenizer state `st`. -/
def Corr (x : List ℕ) (st : TS) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
    σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧
    σ.vars "zp" = st.p ∧ σ.vars "zT" = st.nd.length ∧ σ.vars "zq" = st.ab.length ∧
    σ.vars "zfl" = st.fl ∧
    σ.arrs "nt" = pad (st.nd.map Prod.fst) (x.length + 1) ∧
    σ.arrs "na" = pad (st.nd.map Prod.snd) (x.length + 1) ∧
    σ.arrs "vs" = pad st.vs (2 * x.length + 2) ∧
    σ.arrs "ab" = pad st.ab (x.length + 1) ∧ σ.arrs "ar" = pad st.ar (x.length + 1)

/-- The shape facts of a tokenizer state that has room for one more node. -/
def Good (x : List ℕ) (st : TS) : Prop :=
  st.nd.length < x.length ∧ st.ab.length ≤ st.nd.length ∧ st.vs.length = 2 * st.ab.length ∧
    st.ar.length = st.ab.length

theorem rd_one_add (x : List ℕ) (i : ℕ) : rd x (1 + i) = rd x (i + 1) := by rw [Nat.add_comm]

/-! ### The variables of a relation atom -/

set_option maxHeartbeats 1000000 in
theorem relVars_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zp" + 4 < B ∧
        x.length < B ∧ σ.vars "zn" < B) relVars
      (fun σ σ' => σ' = (σ.setVar "zy1" (if σ.vars "zn" = 0 then 0 else rd x (σ.vars "zp" + 3))).setVar
        "zy2" (if σ.vars "zn" = 2 then rd x (σ.vars "zp" + 4)
          else if σ.vars "zn" = 0 then 0 else rd x (σ.vars "zp" + 3))) 40 := by
  have hent := hB.1
  have hB2 : 2 < B := by have := hB.2; nlinarith
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  unfold relVars
  run_vcg [rdV_spec hent (by omega) "zy1" "zp" 3, rdV_spec hent (by omega) "zy2" "zp" 4]
  all_goals (simp_all [Env.setVar]; try omega)

/-! ### The symbol of a relation atom -/

theorem hp_lt_of {x : List ℕ} {B : ℕ} (hB : HB x B) (i : ℕ) : hp x i < B := by
  have := hp_le x i; have := hB.2; nlinarith

theorem bsL_getD {x : List ℕ} {i : ℕ} (hi : i < sX x) :
    (pad (bsL x (sX x)) (sX x)).getD i 0 = hp x i := by
  rw [getD_pad, bsL, List.getD_eq_getElem _ _ (by simpa using hi)]; simp

set_option maxHeartbeats 2000000 in
theorem relSym_spec {x : List ℕ} {B : ℕ} (hB : HB x B) (lb lr : List ℕ) (f0 : ℕ) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
        σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧ σ.arrs "ab" = pad lb (x.length + 1) ∧
        σ.arrs "ar" = pad lr (x.length + 1) ∧ σ.vars "zq" = lb.length ∧ lr.length = lb.length ∧
        lb.length < x.length + 1 ∧ σ.vars "zfl" = f0 ∧ σ.vars "zi" < B ∧ σ.vars "zn" < B)
      relSym
      (fun σ σ' => (σ'.arrs "ab" = pad (lb ++ [if σ.vars "zi" < sX x then hp x (σ.vars "zi") else 0])
          (x.length + 1) ∧
        σ'.arrs "ar" = pad (lr ++ [if σ.vars "zi" < sX x then rd x (σ.vars "zi" + 1) else 0])
          (x.length + 1) ∧
        σ'.vars "zfl" = (if σ.vars "zi" < sX x then
          (if σ.vars "zn" = rd x (σ.vars "zi" + 1) then f0 else 0) else 0)) ∧
        KeepA ["zw", "zfl"] ["ab", "ar"] σ σ') 60 := by
  have hent := hB.1
  have hB2 : x.length + 2 < B := by have := hB.2; nlinarith
  have hsB : sX x + 2 < B := by
    have := rd_le_Mmax x 0; have := hB.2; unfold sX; nlinarith
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  have hpB : ∀ i, hp x i < B := hp_lt_of hB
  refine Spec.keepA (c := relSym) ?_ ["zw", "zfl"] ["ab", "ar"] (by simp [relSym, rdV, Com.wvars])
    (by simp [relSym, rdV, Com.warrs]) (by simp [relSym, rdV, Com.reads])
    (by simp [relSym, rdV, Com.NoWrite])
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
        σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧ σ.arrs "ab" = pad lb (x.length + 1) ∧
        σ.arrs "ar" = pad lr (x.length + 1) ∧ σ.vars "zq" = lb.length ∧ lr.length = lb.length ∧
        lb.length < x.length + 1 ∧ σ.vars "zfl" = f0 ∧ σ.vars "zi" < B ∧ σ.vars "zn" < B ∧
        (σ.vars "zi" < sX x → (σ.arrs "bs").getD (σ.vars "zi") 0 = hp x (σ.vars "zi")) ∧
        (σ.arrs "bs").length = sX x ∧ (σ.arrs "ab").length = x.length + 1 ∧
        (σ.arrs "ar").length = x.length + 1 ∧ x.length + 2 < B) ?_ ?_
  · unfold relSym
    run_vcg [rdV_spec hent (by omega) "zw" "zi" 1]
    all_goals (simp_all [Env.setVar, Env.setArr]; try omega)
    all_goals first
      | exact hrdB _
      | exact hpB _
      | (constructor <;> omega)
      | exact ⟨pad_set' (by omega) (by omega) _, pad_set' (by omega) (by omega) _⟩
      | (rw [if_neg (by omega), if_neg (by omega)]
         exact ⟨pad_set' (by omega) (by omega) _, pad_set' (by omega) (by omega) _⟩)
  · rintro σ ⟨ha, hn, hs, hbs, hab, har, hq, hlr, hlb, hfl, hi, hnB⟩
    refine ⟨ha, hn, hs, hbs, hab, har, hq, hlr, hlb, hfl, hi, hnB, fun h => ?_, ?_, ?_, ?_, hB2⟩
    · rw [hbs]; exact bsL_getD h
    · rw [hbs, length_pad (by rw [length_bsL])]
    · rw [hab, length_pad (by omega)]
    · rw [har, length_pad (by omega)]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1
