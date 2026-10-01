import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom

/-! # Where the tokens of the formula stand in the word

The formula starts at `fs = bo x s`; after the tokens `done`, the next token `t` stands at
`fs + |code done|` (`tokAt_of_split`), and its code can be read there entry by entry. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok

open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom

/-- The start of the formula. -/
abbrev fsOf (x : List ℕ) : ℕ := bo x (sOf x)

/-- The length of the code of a list of tokens. -/
def clen (l : List Token) : ℕ := (l.flatMap Token.code).length

theorem clen_append (l l' : List Token) : clen (l ++ l') = clen l + clen l' := by
  simp [clen]

theorem clen_singleton (t : Token) : clen [t] = t.code.length := by simp [clen]

/-- The token `t` stands at position `p` of the word. -/
def TokAt (x : List ℕ) (p : ℕ) (t : Token) : Prop :=
  p + t.code.length ≤ x.length ∧ ∀ m < t.code.length, x.getD (p + m) 0 = t.code.getD m 0

variable {x : List ℕ} {φ : Formula}

theorem drop_split (hd : Dom x φ) {done rest : List Token} (h : toks φ = done ++ rest) :
    x.drop (fsOf x + clen done) = rest.flatMap Token.code := by
  rw [← List.drop_drop, hd.drop_eq, encode_eq_toks, h, List.flatMap_append, clen,
    List.drop_left]

theorem pos_split (hd : Dom x φ) {done rest : List Token} (h : toks φ = done ++ rest) :
    fsOf x + clen done + clen rest = x.length := by
  have := hd.fs_eq
  rw [encode_eq_toks, h] at this
  simp only [clen, List.flatMap_append, List.length_append, fsOf] at this ⊢
  omega

theorem tokAt_of_split (hd : Dom x φ) {done rest : List Token} {t : Token}
    (h : toks φ = done ++ t :: rest) : TokAt x (fsOf x + clen done) t := by
  have hp := pos_split hd h
  have hdrop := drop_split hd h
  simp only [clen, List.flatMap_cons, List.length_append] at hp
  refine ⟨by simp only [clen] at hp ⊢; omega, fun m hm => ?_⟩
  rw [← Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse.getD_drop, hdrop, List.flatMap_cons,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hm, ← List.getD_eq_getElem?_getD]

theorem code_length_pos (t : Token) : 0 < t.code.length := by cases t <;> simp [Token.code]

theorem rest_ne_nil (hd : Dom x φ) {done rest : List Token} (h : toks φ = done ++ rest)
    (hlt : fsOf x + clen done < x.length) : rest ≠ [] := by
  rintro rfl
  have := pos_split hd h
  have h0 : clen ([] : List Token) = 0 := rfl
  omega

theorem clen_le (hd : Dom x φ) {done rest : List Token} (h : toks φ = done ++ rest) :
    fsOf x + clen done ≤ x.length := by
  have := pos_split hd h; omega

theorem nrelT_le_clen (l : List Token) : nrelT l ≤ clen l := nrelT_le_length l

theorem rmaxT_le_clen (l : List Token) : rmaxT l ≤ clen l := rmaxT_le_length l

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok
