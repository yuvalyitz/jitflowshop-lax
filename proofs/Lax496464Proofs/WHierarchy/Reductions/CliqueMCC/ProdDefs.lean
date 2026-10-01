import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath

/-!
# p-Clique to Multicoloured Clique: the IMP+ program

The array `a` holds the word `x` (graph block, then `k`). The body writes `prodWord x`: the
multicoloured graph on the `N = k n` copies `s` (colour `s / n`, vertex `s % n`), in compressed
sparse row form with increasing adjacency lists, then the colours and `k`. It is the program of
mcc-lax (`Lax369822Proofs.Ram.BodyDefs`) with its adjacency test replaced: two copies are adjacent
when their colours differ and the vertex of the second is listed in the block of the vertex of the
first, found by a scan of that block (`scanLoop`).

All scalars of the body are prefixed `b_`.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs

open Lax808846Proofs.Imp
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- The division step: `b_cs, b_us, b_ct, b_ut` are the colour and the vertex of `b_s` and
`b_t`. -/
def adjPrep : Com :=
  .seq (.assign "b_cs" (.div (V "b_s") (V "b_n")))
  (.seq (.assign "b_us" (.sub (V "b_s") (.mul (V "b_cs") (V "b_n"))))
  (.seq (.assign "b_ct" (.div (V "b_t") (V "b_n")))
        (.assign "b_ut" (.sub (V "b_t") (.mul (V "b_ct") (V "b_n"))))))

/-- One step of the scan of a block: `b_f := 1` if the entry is `b_ut`. -/
def scanBody : Com :=
  .seq (.ite (.eq (.get "a" (.add (V "b_st") (V "b_j"))) (V "b_ut")) (.assign "b_f" (.lit 1)) .skip)
    (bump "b_j")

/-- The scan of the `b_dg` entries from `b_st` on. -/
def scanLoop : Com := .seq (.assign "b_j" (.lit 0)) (.while (.lt (V "b_j") (V "b_dg")) scanBody)

/-- The scan of the block of the vertex `b_us`, looking for `b_ut`. -/
def scan : Com :=
  .seq (.assign "b_o1" (.get "a" (.add (V "b_us") (.lit 2))))
  (.seq (.assign "b_o2" (.get "a" (.add (V "b_us") (.lit 3))))
  (.seq (.assign "b_st" (.add (V "b_tb") (V "b_o1")))
  (.seq (.assign "b_dg" (.sub (V "b_o2") (V "b_o1"))) scanLoop)))

/-- `b_f := 1` iff the colours differ and the vertices are adjacent. -/
def adjTest : Com := .seq (.assign "b_f" (.lit 0)) (.ite (.eq (V "b_cs") (V "b_ct")) .skip scan)

/-- Sets `b_f` to `1` if the copies `b_s` and `b_t` are adjacent, else `0`. -/
def adjCom : Com := .seq adjPrep adjTest

/-- `b_d :=` the degree of `b_s`. -/
def rowCount : Com :=
  .seq (.assign "b_d" (.lit 0))
   (.seq (.assign "b_t" (.lit 0))
    (.while (.lt (V "b_t") (V "b_N"))
     (.seq adjCom (.seq (.assign "b_d" (.add (V "b_d") (V "b_f"))) (bump "b_t")))))

/-- Write `b_t` if `b_f = 1`. -/
def emitIf : Com := .ite (.eq (V "b_f") (.lit 1)) (.write (V "b_t")) .skip

/-- Writes the neighbours of `b_s` in increasing order. -/
def rowEmit : Com :=
  .seq (.assign "b_t" (.lit 0))
   (.while (.lt (V "b_t") (V "b_N"))
    (.seq adjCom (.seq emitIf (bump "b_t"))))

/-- `b_M :=` the sum of the degrees. -/
def pass1 : Com :=
  .seq (.assign "b_M" (.lit 0))
   (.seq (.assign "b_s" (.lit 0))
    (.while (.lt (V "b_s") (V "b_N"))
     (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))))

/-- Writes the running offsets after each vertex. -/
def pass2 : Com :=
  .seq (.assign "b_off" (.lit 0))
   (.seq (.assign "b_s" (.lit 0))
    (.while (.lt (V "b_s") (V "b_N"))
     (.seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
       (.seq (.write (V "b_off")) (bump "b_s"))))))

/-- Writes the targets. -/
def pass3 : Com :=
  .seq (.assign "b_s" (.lit 0))
   (.while (.lt (V "b_s") (V "b_N")) (.seq rowEmit (bump "b_s")))

/-- Writes the colours. -/
def pass4 : Com :=
  .seq (.assign "b_s" (.lit 0))
   (.while (.lt (V "b_s") (V "b_N"))
    (.seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s")))

/-- The header: `b_N = k n` and the start `b_tb = 3 + n` of the target array (`b_n`, `b_k` are
read before). -/
def header : Com :=
  .seq (.assign "b_N" (.mul (V "b_k") (V "b_n"))) (.assign "b_tb" (.add (.lit 3) (V "b_n")))

/-- **The body**: array `a` holds the word, `b_n` and `b_k` its `n` and `k`; the word of the
construction is written. -/
def body : Com :=
  .seq header
  (.seq pass1
  (.seq (.write (V "b_N"))
  (.seq (.write (.div (V "b_M") (.lit 2)))
  (.seq (.write (.lit 0))
  (.seq pass2
  (.seq pass3
  (.seq pass4 (.write (V "b_k")))))))))

/-- The fixed no-instance `[0, 0, 0, 1]`. -/
def noCom : Com :=
  .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1))))

/-- Reads `n` and `k` and branches. -/
def mainCom : Com :=
  .seq (.assign "b_n" (.get "a" (.lit 0)))
  (.seq (.assign "b_k" (.get "a" (.sub (V "rt_n") (.lit 1))))
    (.ite (.lt (V "b_n") (V "b_k")) noCom body))

/-- The scalars `body` may assign. -/
def bodyVars : List String :=
  ["b_N", "b_tb", "b_M", "b_s", "b_t", "b_f", "b_d", "b_off",
    "b_cs", "b_us", "b_ct", "b_ut", "b_o1", "b_o2", "b_st", "b_dg", "b_j"]

/-! ### Names for the pieces of the word -/

/-- The neighbours of the copy `s`. -/
abbrev nb (x : List ℕ) (s : ℕ) : List ℕ := CsrWord.nbW (adjW x) (NOf x) s

/-- The degree of the copy `s`. -/
abbrev dg (x : List ℕ) (s : ℕ) : ℕ := CsrWord.degW (adjW x) (NOf x) s

/-- The sum of the first `s` degrees. -/
abbrev ps (x : List ℕ) (s : ℕ) : ℕ := CsrWord.psum (adjW x) (NOf x) s

/-- The shape of the word the machine relies on: the offsets of every vertex are nondecreasing
and its block lies inside the word. -/
def Good (x : List ℕ) : Prop :=
  nV x + 3 < x.length ∧
    ∀ u < nV x, offX x u ≤ offX x (u + 1) ∧ 3 + nV x + offX x (u + 1) < x.length

theorem good_of {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ} (hx : x = g ++ [k])
    (hg : Lax271696.GraphEncoding.EncodesGraph g n G) : Good x := by
  have hl := hg.length_eq
  have hlast := hg.offset_last
  have hn := nV_eq hx hg
  have hxl : x.length = g.length + 1 := by rw [hx]; simp
  have hoff : ∀ i ≤ n, offX x i = Lax271696.GraphEncoding.offset g i := fun i hi => by
    unfold offX Lax271696.GraphEncoding.offset
    rw [hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  refine ⟨by omega, fun u hu => ?_⟩
  rw [hn] at hu ⊢
  rw [hoff u (by omega), hoff (u + 1) (by omega)]
  have h1 := hg.offset_mono u hu
  have h2 := offset_mono' hg (show u + 1 ≤ n by omega) le_rfl
  omega

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs
