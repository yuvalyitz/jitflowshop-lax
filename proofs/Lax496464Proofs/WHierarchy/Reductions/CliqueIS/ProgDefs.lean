import Lax496464Proofs.WHierarchy.Machine.ReadTape
import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math

/-! # The IMP+ program of the complement map: definitions

After `readTape` (array `a` = the word `x`, `rt_n = |x|`), `body`
* reads `n` and builds the `n × n` adjacency matrix `mat` of the graph from the CSR blocks (`fill`);
* sums the degrees of the complement (`pass1`, into `ci_M`);
* writes `n`, `ci_M / 2`, `0`, the offsets (`pass2`), the targets (`pass3`) and the last entry `k`.

The complement test of `(s, t)` is `s ≠ t ∧ mat[s n + t] = 0` (`adjCom`). All scalars of `body` are
prefixed `ci_`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- `ci_n := a[0]`, `ci_tb := 3 + ci_n` (the start of the targets). -/
def header : Com :=
  .seq (.assign "ci_n" (.get "a" (.lit 0))) (.assign "ci_tb" (.add (.lit 3) (V "ci_n")))

/-- One target of the block of `ci_u`: `mat[u n + a[tb + j]] := 1`. -/
def fillInner : Com :=
  .seq (.store "mat" (.add (.mul (V "ci_u") (V "ci_n")) (.get "a" (.add (V "ci_tb") (V "ci_j"))))
    (.lit 1)) (bump "ci_j")

/-- The loop over the block of `ci_u`. -/
def innerLoop : Com := .while (.lt (V "ci_j") (V "ci_e")) fillInner

/-- One row of the matrix: the block of `ci_u`. -/
def fillRow : Com :=
  .seq (.assign "ci_j" (.get "a" (.add (.lit 2) (V "ci_u"))))
  (.seq (.assign "ci_e" (.get "a" (.add (.lit 3) (V "ci_u"))))
  (.seq innerLoop (bump "ci_u")))

/-- The adjacency matrix. -/
def fill : Com := .seq (.assign "ci_u" (.lit 0)) (.while (.lt (V "ci_u") (V "ci_n")) fillRow)

/-- `ci_f := 1` if `ci_s ≠ ci_t` and they are not adjacent, else `0`. -/
def adjCom : Com :=
  .seq (.assign "ci_f" (.lit 0))
   (.ite (.eq (V "ci_s") (V "ci_t")) .skip
    (.ite (.eq (.get "mat" (.add (.mul (V "ci_s") (V "ci_n")) (V "ci_t"))) (.lit 0))
      (.assign "ci_f" (.lit 1)) .skip))

/-- `ci_d :=` the degree of `ci_s` in the complement. -/
def rowCount : Com :=
  .seq (.assign "ci_d" (.lit 0))
   (.seq (.assign "ci_t" (.lit 0))
    (.while (.lt (V "ci_t") (V "ci_n"))
     (.seq adjCom (.seq (.assign "ci_d" (.add (V "ci_d") (V "ci_f"))) (bump "ci_t")))))

/-- Write `ci_t` if `ci_f = 1`. -/
def emitIf : Com := .ite (.eq (V "ci_f") (.lit 1)) (.write (V "ci_t")) .skip

/-- Writes the neighbours of `ci_s` in the complement, in increasing order. -/
def rowEmit : Com :=
  .seq (.assign "ci_t" (.lit 0))
   (.while (.lt (V "ci_t") (V "ci_n"))
    (.seq adjCom (.seq emitIf (bump "ci_t"))))

/-- `ci_M :=` the sum of the degrees. -/
def pass1 : Com :=
  .seq (.assign "ci_M" (.lit 0))
   (.seq (.assign "ci_s" (.lit 0))
    (.while (.lt (V "ci_s") (V "ci_n"))
     (.seq rowCount (.seq (.assign "ci_M" (.add (V "ci_M") (V "ci_d"))) (bump "ci_s")))))

/-- Writes the running offsets after each vertex. -/
def pass2 : Com :=
  .seq (.assign "ci_off" (.lit 0))
   (.seq (.assign "ci_s" (.lit 0))
    (.while (.lt (V "ci_s") (V "ci_n"))
     (.seq rowCount (.seq (.assign "ci_off" (.add (V "ci_off") (V "ci_d")))
       (.seq (.write (V "ci_off")) (bump "ci_s"))))))

/-- Writes the targets. -/
def pass3 : Com :=
  .seq (.assign "ci_s" (.lit 0))
   (.while (.lt (V "ci_s") (V "ci_n")) (.seq rowEmit (bump "ci_s")))

/-- Writes the last entry of the word, the parameter. -/
def tailK : Com := .write (.get "a" (.sub (V "rt_n") (.lit 1)))

/-- **The body**: array `a` holds the word, `rt_n` its length; the complement word is written. -/
def body : Com :=
  .seq header
  (.seq fill
  (.seq pass1
  (.seq (.write (V "ci_n"))
  (.seq (.write (.div (V "ci_M") (.lit 2)))
  (.seq (.write (.lit 0))
  (.seq pass2
  (.seq pass3 tailK)))))))

/-- **The program**: read the tape, then the body. -/
def cmd : Com := .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape body

/-- The scalars `body` may assign. -/
def bodyVars : List String :=
  ["ci_n", "ci_tb", "ci_u", "ci_j", "ci_e", "ci_s", "ci_t", "ci_f", "ci_d", "ci_M", "ci_off"]

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- What the program needs of a word: the facts of a CSR word with a parameter that it uses. -/
structure Dom (x : List ℕ) : Prop where
  len : x.length = 4 + nOf x + offAt x (nOf x)
  mono : ∀ i < nOf x, offAt x i ≤ offAt x (i + 1)
  tgt_lt : ∀ j < offAt x (nOf x), tgtAt x j < nOf x
  last : x.getD (x.length - 1) 0 = kOf x

theorem Dom.off_le {x : List ℕ} (hd : Dom x) {i i' : ℕ} (h : i ≤ i') (h' : i' ≤ nOf x) :
    offAt x i ≤ offAt x i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact (ih (by omega)).trans (hd.mono t (by omega))

theorem Dom.n_le {x : List ℕ} (hd : Dom x) : nOf x + 4 ≤ x.length := by
  have := hd.len; omega

theorem Dom.off_le_len {x : List ℕ} (hd : Dom x) {i : ℕ} (hi : i ≤ nOf x) :
    offAt x i + nOf x + 4 ≤ x.length := by
  have := hd.len; have := hd.off_le hi le_rfl; omega

theorem dom_of_encodes {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : Lax271696.VertexCover.EncodesParamInstance x n G k) : Dom x := by
  obtain ⟨g, hx, hg⟩ := h
  have hn := nOf_eq hx hg
  have hlast : offAt x (nOf x) = 2 * Lax271696.GraphEncoding.edgeCount g := by
    rw [offAt_eq hx hg (by omega), hn]; exact hg.offset_last
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [length_eq hx hg, hlast, hn]
  · intro i hi
    rw [offAt_eq hx hg (by omega), offAt_eq hx hg (by omega)]
    exact hg.offset_mono i (by omega)
  · intro j hj
    rw [hlast] at hj
    rw [tgtAt_eq hx hg hj, hn]
    exact hg.target_lt j hj
  · subst hx
    simp [kOf]

theorem dom_of_mem {x : List ℕ} (hx : x ∈ Lax496464.WH_C1_GraphProblems.GraphInstances) : Dom x := by
  obtain ⟨n, G, k, h⟩ := hx
  exact dom_of_encodes h

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs
