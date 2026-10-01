import Lax496464Proofs.WHierarchy.Machine.ReadTape
import Lax496464Proofs.WHierarchy.HittingSet.Firsts

/-! # The IMP+ program of `p-WSat(d-CNF) ≤fpt p-MC(Σ_1)`: definitions

After `readTape` (array `a` = the word `x`, `rt_n = |x|`), `body d` runs these phases:

1. `parse`: the clause offsets into `co`, the literal codes into `cd`, `w_m`, `w_L`, `w_k`;
2. `consts`: `w_M = L + 4`, `w_dk = d ^ k`, `hs_t = 2L + m + m d^k` (the size of the array of
   numbers), `w_md = M ^ (d + 2)`, `w_K1 = k + 1`, `w_F = (k + 1) ^ (d + 1)`, `w_nv`, `w_d1 = d + 1`;
3. `varRows`: the numbers of the variables of the occurrences into `hs_mem`;
4. `firstsLoop` (from `HittingSet.Firsts`): the first occurrences into `fp_f`;
5. `canonRows`, 6. `nRows`: the numbers of the tuples of `C` and of `N`;
7. `lRows`: for every clause and branch word the bounded search, and the number of its tuple;
8. `firstsLoop` again, over all numbers;
9. `structOut`: the word of the structure;
10. `formOut`: the code of the sentence.

All scalars of `body` are prefixed `w_`, except those of `firstsLoop`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))
/-- `i := 0; while i < n do body`. -/
abbrev loop (i n : String) (body : Com) : Com := .seq (.assign i (.lit 0)) (.while (.lt (V i) (V n)) body)
/-- `e mod n`. -/
abbrev modE (e n : Expr) : Expr := .sub e (.mul (.div e n) n)
/-- The parity of `e`. -/
abbrev par (e : Expr) : Expr := .and e (.lit 1)

/-- Write a list of constants. -/
def writeLits : List ℕ → Com
  | [] => .skip
  | n :: l => .seq (.write (.lit n)) (writeLits l)

/-! ### 1. Parsing -/

def copyBody : Com :=
  .seq (.store "cd" (.add (V "w_L") (V "w_i")) (.get "a" (.add (.add (V "w_pos") (.lit 1)) (V "w_i"))))
    (bump "w_i")

def parseBody : Com :=
  .seq (.store "co" (V "w_c") (V "w_L"))
  (.seq (.assign "w_ln" (.get "a" (V "w_pos")))
  (.seq (loop "w_i" "w_ln" copyBody)
  (.seq (.assign "w_L" (.add (V "w_L") (V "w_ln")))
  (.seq (.assign "w_pos" (.add (.add (V "w_pos") (V "w_ln")) (.lit 1)))
  (bump "w_c")))))

def parse : Com :=
  .seq (.assign "w_m" (.get "a" (.lit 0)))
  (.seq (.assign "w_pos" (.lit 1))
  (.seq (.assign "w_L" (.lit 0))
  (.seq (loop "w_c" "w_m" parseBody)
  (.seq (.store "co" (V "w_m") (V "w_L"))
  (.assign "w_k" (.get "a" (V "w_pos")))))))

/-! ### 2. Constants -/

/-- `w_pr := w_pb ^ w_pn`. -/
def powCom : Com :=
  .seq (.assign "w_pr" (.lit 1))
    (loop "w_pi" "w_pn" (.seq (.assign "w_pr" (.mul (V "w_pr") (V "w_pb"))) (bump "w_pi")))

def consts (d : ℕ) : Com :=
  (.seq (.assign "w_M" (.add (V "w_L") (.lit 4)))
  (.seq (.assign "w_pb" (.lit d))
  (.seq (.assign "w_pn" (V "w_k"))
  (.seq powCom
  (.seq (.assign "w_dk" (V "w_pr"))
  (.seq (.assign "hs_t" (.add (.add (.mul (.lit 2) (V "w_L")) (V "w_m")) (.mul (V "w_m") (V "w_dk"))))
  (.seq (.assign "w_pb" (V "w_M"))
  (.seq (.assign "w_pn" (.lit (d + 2)))
  (.seq powCom
  (.seq (.assign "w_md" (V "w_pr"))
  (.seq (.assign "w_K1" (.add (V "w_k") (.lit 1)))
  (.seq (.assign "w_pb" (V "w_K1"))
  (.seq (.assign "w_pn" (.lit (d + 1)))
  (.seq powCom
  (.seq (.assign "w_F" (V "w_pr"))
  (.seq (.assign "w_nv" (.add (V "w_K1") (.mul (V "w_F") (V "w_K1"))))
  (.assign "w_d1" (.lit (d + 1)))))))))))))))))))

/-! ### 3–6. The numbers of the variables, of `C` and of `N` -/

def varRows : Com :=
  loop "w_j" "w_L" (.seq (.store "hs_mem" (V "w_j")
    (.mul (.div (.get "cd" (V "w_j")) (.lit 2)) (V "w_M"))) (bump "w_j"))

def canonRows : Com :=
  loop "w_j" "w_L" (.seq (.store "hs_mem" (.add (V "w_L") (V "w_j"))
    (.add (.lit 1) (.mul (V "w_M") (.get "fp_f" (V "w_j"))))) (bump "w_j"))

/-- Entry `w_p` of the key of the clause at offset `w_o` with `w_ln` literals, into `w_e`. -/
def keyEc : Com :=
  .ite (.lt (V "w_p") (V "w_ln"))
    (.ite (.eq (par (.get "cd" (.add (V "w_o") (V "w_p")))) (.lit 0)) (.assign "w_e" (V "w_L"))
      (.assign "w_e" (.get "fp_f" (.add (V "w_o") (V "w_p")))))
    (.assign "w_e" (V "w_L"))

def keyBody : Com :=
  .seq keyEc (.seq (.assign "w_acc" (.add (V "w_acc") (.mul (V "w_e") (V "w_pw"))))
    (.seq (.assign "w_pw" (.mul (V "w_pw") (V "w_M"))) (bump "w_p")))

def nBody : Com :=
  .seq (.assign "w_acc" (.lit 2))
  (.seq (.assign "w_pw" (V "w_M"))
  (.seq (.assign "w_o" (.get "co" (V "w_c")))
  (.seq (.assign "w_ln" (.sub (.get "co" (.add (V "w_c") (.lit 1))) (V "w_o")))
  (.seq (loop "w_p" "w_d1" keyBody)
  (.seq (.store "hs_mem" (.add (.mul (.lit 2) (V "w_L")) (V "w_c")) (V "w_acc"))
  (bump "w_c"))))))

def nRows : Com := loop "w_c" "w_m" nBody

/-! ### 7. The searches -/

/-- `w_hit := 1` if `w_f` is among the chosen elements. -/
def chLoop : Com :=
  loop "w_q" "w_nch" (.seq (.ite (.eq (.get "ch" (V "w_q")) (V "w_f")) (.assign "w_hit" (.lit 1)) .skip)
    (bump "w_q"))

def hitLit : Com :=
  .ite (.eq (par (.get "cd" (.add (V "w_o") (V "w_i")))) (.lit 0))
    (.seq (.assign "w_f" (.get "fp_f" (.add (V "w_o") (V "w_i")))) chLoop) .skip

def hitLoop : Com := loop "w_i" "w_ln" (.seq hitLit (bump "w_i"))

/-- Hit the unhit clause by the literal the next digit names, or fail. -/
def pick (d : ℕ) : Com :=
  .ite (.eq (V "w_nch") (V "w_k")) (.assign "w_ok" (.lit 0))
    (.seq (.assign "w_dg" (modE (.div (V "w_b") (V "w_pw")) (.lit d)))
      (.ite (.lt (V "w_dg") (V "w_ln"))
        (.ite (.eq (par (.get "cd" (.add (V "w_o") (V "w_dg")))) (.lit 0))
          (.seq (.store "ch" (V "w_nch") (.get "fp_f" (.add (V "w_o") (V "w_dg"))))
            (.seq (bump "w_nch") (.assign "w_pw" (.mul (V "w_pw") (.lit d)))))
          (.assign "w_ok" (.lit 0)))
        (.assign "w_ok" (.lit 0))))

def grpHead : Com :=
  .seq (.assign "w_o" (.get "co" (V "w_c2")))
  (.seq (.assign "w_ln" (.sub (.get "co" (.add (V "w_c2") (.lit 1))) (V "w_o")))
  (.assign "w_hit" (.lit 0)))

def grpTail (d : ℕ) : Com := .ite (.eq (V "w_hit") (.lit 0)) (pick d) .skip

def grpCom (d : ℕ) : Com := .seq grpHead (.seq hitLoop (grpTail d))

def c2Grp (d : ℕ) : Com :=
  .ite (.eq (.get "hs_mem" (.add (.mul (.lit 2) (V "w_L")) (V "w_c2"))) (V "w_key")) (grpCom d) .skip

def c2Step (d : ℕ) : Com := .ite (.eq (V "w_ok") (.lit 1)) (c2Grp d) .skip

def c2Body (d : ℕ) : Com := .seq (c2Step d) (bump "w_c2")

def padBody : Com :=
  .seq (.ite (.lt (V "w_q") (V "w_nch")) (.assign "w_e" (.get "ch" (V "w_q"))) (.assign "w_e" (V "w_L")))
  (.seq (.assign "w_acc" (.add (V "w_acc") (.mul (V "w_e") (V "w_pw2"))))
  (.seq (.assign "w_pw2" (.mul (V "w_pw2") (V "w_M"))) (bump "w_q")))

/-- Store the number of the tuple found. -/
def lRow : Com :=
  .seq (.assign "w_acc" (.add (V "w_key") (.lit 1)))
  (.seq (.assign "w_pw2" (V "w_md"))
  (.seq (loop "w_q" "w_K1" padBody)
  (.seq (.store "hs_mem" (V "w_cur") (V "w_acc"))
  (bump "w_cur"))))

def simHead : Com :=
  .seq (.assign "w_nch" (.lit 0))
  (.seq (.assign "w_pw" (.lit 1))
  (.seq (.assign "w_ok" (.lit 1))
  (.assign "w_key" (.get "hs_mem" (.add (.mul (.lit 2) (V "w_L")) (V "w_c"))))))

def simTail : Com := .ite (.eq (V "w_ok") (.lit 1)) lRow .skip

def simBody (d : ℕ) : Com :=
  .seq simHead (.seq (loop "w_c2" "w_m" (c2Body d)) (.seq simTail (bump "w_b")))

def lBody (d : ℕ) : Com := .seq (loop "w_b" "w_dk" (simBody d)) (bump "w_c")

def lRows (d : ℕ) : Com :=
  .seq (.assign "w_cur" (.add (.mul (.lit 2) (V "w_L")) (V "w_m"))) (loop "w_c" "w_m" (lBody d))

/-! ### 9. The structure -/

/-- Run `c` when the number at `w_t` has tag `w_tg` and is the first of its value. -/
def tagIte (c : Com) : Com :=
  .ite (.eq (modE (.get "hs_mem" (V "w_t")) (V "w_M")) (V "w_tg"))
    (.ite (.eq (.get "fp_f" (V "w_t")) (V "w_t")) c .skip) .skip

def digBody : Com :=
  .seq (.write (modE (V "w_e") (V "w_M"))) (.seq (.assign "w_e" (.div (V "w_e") (V "w_M"))) (bump "w_p"))

def digits : Com :=
  .seq (.assign "w_e" (.div (.get "hs_mem" (V "w_t")) (V "w_M"))) (loop "w_p" "w_ar" digBody)

def emitCom : Com :=
  .seq (.assign "w_cn" (.lit 0))
  (.seq (loop "w_t" "hs_t" (.seq (tagIte (bump "w_cn")) (bump "w_t")))
  (.seq (.write (V "w_cn"))
  (loop "w_t" "hs_t" (.seq (tagIte digits) (bump "w_t")))))

def structHead (d : ℕ) : Com :=
  .seq (writeLits [4, 1, 1, d + 1])
  (.seq (.write (.add (V "w_k") (.lit (d + 2))))
  (.seq (.write (.add (V "w_L") (.lit 1)))
  (.seq (.write (.lit 1)) (.write (V "w_L")))))

/-- The block of the tuples with tag `g` and the arity the value of `e`. -/
def emitT (g : ℕ) (e : Expr) : Com :=
  .seq (.assign "w_tg" (.lit g)) (.seq (.assign "w_ar" e) emitCom)

def structOut (d : ℕ) : Com :=
  .seq (structHead d) (.seq (emitT 1 (.lit 1)) (.seq (emitT 2 (.lit (d + 1)))
    (emitT 3 (.add (V "w_k") (.lit (d + 2))))))

/-! ### 10. The sentence -/

def qOut : Com :=
  loop "w_v" "w_nv" (.seq (.write (.lit 6)) (.seq (.write (V "w_v")) (bump "w_v")))

def cOut : Com :=
  loop "w_ii" "w_k" (.seq (writeLits [4, 0, 1, 1]) (.seq (.write (V "w_ii")) (bump "w_ii")))

def dInner : Com :=
  loop "w_jj" "w_ii" (.seq (writeLits [4, 3, 2]) (.seq (.write (V "w_ii"))
    (.seq (.write (V "w_jj")) (bump "w_jj"))))

def dOut : Com := loop "w_ii" "w_k" (.seq dInner (bump "w_ii"))

/-- The digits of `w_t` in base `w_K1`. -/
def vtOut : Com :=
  .seq (.assign "w_e" (V "w_t"))
    (loop "w_p" "w_d1" (.seq (.write (modE (V "w_e") (V "w_K1")))
      (.seq (.assign "w_e" (.div (V "w_e") (V "w_K1"))) (bump "w_p"))))

/-- The variable `y_{w_t, w_jj}`. -/
abbrev yvE : Expr := .add (.add (V "w_K1") (.mul (V "w_t") (V "w_K1"))) (V "w_jj")

def ytOut : Com := loop "w_jj" "w_K1" (.seq (.write yvE) (bump "w_jj"))

def yInner : Com :=
  loop "w_ii" "w_K1" (.seq (writeLits [5, 2]) (.seq (.write yvE) (.seq (.write (V "w_ii"))
    (bump "w_ii"))))

def yOut : Com :=
  .seq (loop "w_jj" "w_K1" (.seq (.write (.lit 4)) (.seq yInner (.seq (writeLits [3, 2, 0, 0])
    (bump "w_jj"))))) (writeLits [2, 0, 0])

def clauseOut (d : ℕ) : Com :=
  .seq (writeLits [5, 3, 0, 2, d + 1])
  (.seq vtOut
  (.seq (writeLits [4, 0, 3])
  (.seq (.write (.add (V "w_k") (.lit (d + 2))))
  (.seq vtOut (.seq ytOut yOut)))))

def eOut (d : ℕ) : Com :=
  .seq (loop "w_t" "w_F" (.seq (.write (.lit 4)) (.seq (clauseOut d) (bump "w_t"))))
    (writeLits [2, 0, 0])

def formOut (d : ℕ) : Com :=
  .seq qOut
  (.seq (writeLits [4, 0, 0, 1]) (.seq (.write (V "w_k")) (.seq (writeLits [4])
  (.seq cOut (.seq (writeLits [2, 0, 0, 4])
  (.seq dOut (.seq (writeLits [2, 0, 0]) (eOut d))))))))

/-! ### The program -/

def body (d : ℕ) : Com :=
  .seq parse (.seq (consts d) (.seq varRows (.seq Lax496464Proofs.WHierarchy.HittingSet.Firsts.firstsLoop
  (.seq canonRows (.seq nRows (.seq (lRows d) (.seq Lax496464Proofs.WHierarchy.HittingSet.Firsts.firstsLoop
  (.seq (structOut d) (formOut d)))))))))

/-- **The program.** -/
def cmd (d : ℕ) : Com := .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape (body d)

/-! ### Framing -/

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

/-- **Writing constants.** -/
theorem writeLits_spec {B : ℕ} : ∀ (l : List ℕ), (∀ n ∈ l, n < B) →
    Spec B (fun _ => True) (writeLits l)
      (fun σ σ' => σ' = { σ with out := σ.out ++ l }) (3 * l.length + 1)
  | [], _ => by
    intro σ _
    exact ⟨σ, Run.skip.mono (by simp), by simp⟩
  | n :: l, h => by
    intro σ _
    have h1 : Run B (.write (.lit n)) σ { σ with out := σ.out ++ [n] } 2 :=
      Run.write (evalB_lit (h n (by simp)))
    obtain ⟨σ', h2, rfl⟩ := writeLits_spec l (fun m hm => h m (by simp [hm]))
      { σ with out := σ.out ++ [n] } trivial
    refine ⟨_, (h1.seq h2).mono (by simp; omega), by simp⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs
