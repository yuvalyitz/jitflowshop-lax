import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1

/-! # Σ₁[2] model checking to Clique: the three kinds of tokenizer steps

The pieces shared by the tokenizer steps: pushing a node (`pushNodeLit_spec`, `pushNodeG_spec`),
pushing the variables of an atom (`pushVars_spec`), and the tail of the step for a relation atom
(`relTail_spec`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem HB.len {x : List ℕ} {B : ℕ} (hB : HB x B) : 2 * x.length + 6 < B := by
  have := hB.2; nlinarith

theorem set_nd {l : List (ℕ × ℕ)} {n : ℕ} (h : l.length < n) (g m : ℕ) :
    (pad (l.map Prod.fst) n).set l.length g = pad ((l ++ [(g, m)]).map Prod.fst) n ∧
    (pad (l.map Prod.snd) n).set l.length m = pad ((l ++ [(g, m)]).map Prod.snd) n := by
  constructor
  · rw [pad_set' (by simp) (by simpa using h)]; simp
  · rw [pad_set' (by simp) (by simpa using h)]; simp

theorem set_vs {l : List ℕ} {n q : ℕ} (hl : l.length = 2 * q) (h : l.length + 2 ≤ n) (a b : ℕ) :
    ((pad l n).set (q + q) a).set (q + q + 1) b = pad (l ++ [a, b]) n := by
  rw [pad_set' (by omega) (by omega), pad_set' (by simp; omega) (by simp; omega)]
  simp

/-- `Corr` spelled out, with the facts a step needs. -/
def CorrX (x : List ℕ) (st : TS) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
    σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧
    σ.vars "zp" = st.p ∧ σ.vars "zT" = st.nd.length ∧ σ.vars "zq" = st.ab.length ∧
    σ.vars "zfl" = st.fl ∧
    σ.arrs "nt" = pad (st.nd.map Prod.fst) (x.length + 1) ∧
    σ.arrs "na" = pad (st.nd.map Prod.snd) (x.length + 1) ∧
    σ.arrs "vs" = pad st.vs (2 * x.length + 2) ∧
    σ.arrs "ab" = pad st.ab (x.length + 1) ∧ σ.arrs "ar" = pad st.ar (x.length + 1) ∧
    st.p < x.length ∧ st.nd.length < x.length ∧ st.ab.length ≤ st.nd.length ∧
    st.vs.length = 2 * st.ab.length ∧ st.ar.length = st.ab.length ∧
    (∀ g m, (pad (st.nd.map Prod.fst) (x.length + 1)).set st.nd.length g =
        pad ((st.nd ++ [(g, m)]).map Prod.fst) (x.length + 1)) ∧
    (∀ g m, (pad (st.nd.map Prod.snd) (x.length + 1)).set st.nd.length m =
        pad ((st.nd ++ [(g, m)]).map Prod.snd) (x.length + 1)) ∧
    (∀ a b, ((pad st.vs (2 * x.length + 2)).set (st.ab.length + st.ab.length) a).set
      (st.ab.length + st.ab.length + 1) b = pad (st.vs ++ [a, b]) (2 * x.length + 2)) ∧
    (∀ v, (pad st.ab (x.length + 1)).set st.ab.length v = pad (st.ab ++ [v]) (x.length + 1)) ∧
    (∀ v, (pad st.ar (x.length + 1)).set st.ab.length v = pad (st.ar ++ [v]) (x.length + 1)) ∧
    (pad (st.nd.map Prod.fst) (x.length + 1)).length = x.length + 1 ∧
    (pad (st.nd.map Prod.snd) (x.length + 1)).length = x.length + 1 ∧
    (pad st.vs (2 * x.length + 2)).length = 2 * x.length + 2 ∧
    (pad st.ab (x.length + 1)).length = x.length + 1 ∧
    (pad st.ar (x.length + 1)).length = x.length + 1 ∧
    (pad (bsL x (sX x)) (sX x)).length = sX x ∧
    (∀ i < sX x, (pad (bsL x (sX x)) (sX x)).getD i 0 = hp x i)

theorem corrX_of {x : List ℕ} {st : TS} {σ : Env} (h : Corr x st σ) (hp : st.p < x.length)
    (hg : Good x st) : CorrX x st σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hp, g1, g2, g3, g4,
    fun g m => (set_nd (by omega) g m).1, fun g m => (set_nd (by omega) g m).2,
    fun a b => set_vs g3 (by omega) a b, fun v => pad_set (by omega) v,
    fun v => by rw [← g4]; exact pad_set (by omega) v,
    length_pad (by simp; omega), length_pad (by simp; omega), length_pad (by omega),
    length_pad (by omega), length_pad (by omega), length_pad (by simp [length_bsL]),
    fun i hi => bsL_getD hi⟩


/-! ### Small pieces, with the state they produce -/

theorem pushNodeLit_spec {B : ℕ} (k : ℕ) :
    Spec B (fun σ => σ.vars "zT" < (σ.arrs "nt").length ∧ σ.vars "zT" < (σ.arrs "na").length ∧
        σ.vars "zT" + 1 < B ∧ k < B ∧ σ.vars "zq" < B)
      (pushNode (.lit k) (V "zq"))
      (fun σ σ' => σ' = ((σ.setArr "nt" (σ.vars "zT") k).setArr "na" (σ.vars "zT")
        (σ.vars "zq")).setVar "zT" (σ.vars "zT" + 1)) 20 := by
  unfold pushNode
  run_vcg
  all_goals simp_all

theorem pushNodeG_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zT" < (σ.arrs "nt").length ∧ σ.vars "zT" < (σ.arrs "na").length ∧
        σ.vars "zT" + 1 < B ∧ σ.vars "zg" < B)
      (pushNode (V "zg") (.lit 0))
      (fun σ σ' => σ' = ((σ.setArr "nt" (σ.vars "zT") (σ.vars "zg")).setArr "na" (σ.vars "zT")
        0).setVar "zT" (σ.vars "zT" + 1)) 20 := by
  unfold pushNode
  run_vcg
  all_goals simp_all

theorem pushVars_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zq" + σ.vars "zq" + 1 < (σ.arrs "vs").length ∧
        σ.vars "zq" + σ.vars "zq" + 1 < B ∧ σ.vars "zy1" < B ∧ σ.vars "zy2" < B)
      pushVars
      (fun σ σ' => σ' = (σ.setArr "vs" (σ.vars "zq" + σ.vars "zq") (σ.vars "zy1")).setArr "vs"
        (σ.vars "zq" + σ.vars "zq" + 1) (σ.vars "zy2")) 20 := by
  unfold pushVars
  run_vcg
  all_goals simp_all

theorem relTail_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "zq" + 1 < B ∧ σ.vars "zp" + 3 + σ.vars "zn" < B ∧
        σ.vars "rt_n" < B ∧ σ.vars "zn" < B)
      (.seq (bump "zq")
        (.ite (.lt (V "zn") (V "rt_n")) (.assign "zp" (.add (.add (V "zp") (.lit 3)) (V "zn")))
          (.assign "zp" (V "rt_n"))))
      (fun σ σ' => σ' = (σ.setVar "zq" (σ.vars "zq" + 1)).setVar "zp"
        (if σ.vars "zn" < σ.vars "rt_n" then σ.vars "zp" + 3 + σ.vars "zn" else σ.vars "rt_n"))
      30 := by
  run_vcg
  all_goals first
    | (simp_all; done)
    | (rw [if_neg (by simp_all)]; simp)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2
