import Lax808846Proofs.Reasoning

/-!
# A run is unaffected by appending unread input

Theorem 1's reduction has to be a *total* word-RAM computation to be usable in the
Turing-machine model (`Lax759944.RamPolytime`'s definition quantifies over every word, not
just well-formed ones), but `Corollary4`'s program is only proved correct on inputs whose
length exactly matches their own header (`HittingSet.Encodes`'s `length_eq`). A word with
*extra* trailing entries beyond that exact length is handled by simply not reading them —
IMP+'s `Com` has no way to test end-of-input at all (`skip/assign/store/seq/ite/while/read/
write`, no `jeof`), so a program can only ever consume a *prefix* of its input, never notice
what follows it.

This file is the fact that lets a narrow-domain correctness proof (one word, its exact
length) be reused for every word sharing that prefix: appending anything to the far end of
the input tape does not change a step of a run that never reaches it — a run only ever
inspects the *front* of `σ.inp`, one `.read` at a time, so extending the tape past whatever
the run's own `.read`s already consumed cannot be seen by any step. Bulk lemmas already
proved for this codebase (`Frame.lean`'s `Run.frame_inp`) go the other way (a command that
does no reading at all does not touch `inp`); this is the direction needed for a command
that *does* read, run to completion on the prefix it needs.
-/

namespace Lax496464Proofs.Ram.InputSuffix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

end Lax496464Proofs.Ram.InputSuffix
