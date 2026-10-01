In the two-stage flexible flow shop $FF(1,m) \mid\mid \sum_j w_j Z_j$ every job is first
preprocessed on a single machine and then processed on one of $m$ identical machines, and
the objective is the total weight of the jobs whose second operation finishes exactly at
their due date. This submission formalizes the paper of Heeger, Hermelin, Itzhaki,
Schieber and Shabtay on that problem: the characterization of the sets of jobs that can
all be completed just in time, the five algorithms built on it, and the hardness of the
general case.

The characterization decouples the two stages. A set of jobs is feasible exactly when the
single first-stage machine can preprocess each of its jobs in time and at most $m$ of its
second operations are alive at any one instant. Everything else rests on it: a dynamic
program over sets of machine thresholds, running in $O(W n^m)$ time; a sweep over the
$2n$ endpoints carrying the selected jobs alive at each, in $O(W 2^{\omega} n)$; a sweep
carrying only how many of them are due at each of the next $q_{\max}$ instants, in
$O(W m^{q_{\max}} n)$; a greedy for equal preprocessing times without weights, in
$O(n \log n)$; an integer program for equal preprocessing times on proper instances,
whose constraint matrix is totally unimodular; and an approximation scheme obtained by
rounding the weights. The general problem is strongly NP-hard, and W[2]-hard for the
number of machines, by a reduction from Hitting Set.

Running times are stated on the word RAM of the archive, against an explicit word
encoding of an instance, so that they are claims about the instructions a machine
executes. The theorem of Fulkerson and Gross, that a matrix with the consecutive ones
property is totally unimodular, is proved rather than assumed, and so is the NP-hardness of
Hitting Set, by the standard reduction from satisfiability composed with the archive's
Cook–Levin theorem.

Several points are done slightly differently from the printed text. The reduction is
carried out for hitting sets of size at least two, where its unit of time is positive, and
with $k(n-1)+2$ segments, which is what the pigeonhole extracting the hitting set uses. The
greedy is ordered by a counting order that it also maintains, rather than by domination of
due dates. The recursion over due-date profiles is shown correct as printed: an entry that
no selection realizes only overstates how many machines are busy, and this is proved. The
running-time statements additionally assume positive processing times, and ask that the
numbers involved fit in the word.

Every statement about what the algorithms compute carries a proof here: the
characterization and its depth form, the earliest-start-time normal form, the
normalization that separates the endpoints, the recursions of all five programs and their
read-offs, the greedy's invariant and its optimality, the integer program and its total
unimodularity, the rounding argument, and the reduction from Hitting Set in both
directions. What the running-time statements assert about a word RAM — that there is a program, and
how many instructions it executes — is proved for every one of them: each algorithm, and the
construction of the reduction from Hitting Set, is written as a word RAM program, compiled by
the archive's IMP+ pipeline, and shown to compute the stated function within the stated
number of instructions, the reduction in time polynomial in the length of the word. The
reduction from satisfiability to Hitting Set is likewise a word RAM program, and its
polynomial running time is transferred to a Turing machine. For the reduction from Hitting
Set the encoding of Hitting Set requires the universe to be no larger than the word that
presents it, since otherwise a word of a few entries could name a universe no reduction could
write in time bounded by the word.

**The W-hierarchy.** The submission also formalizes the theory that W[1]- and W[2]-hardness proofs
rely on, following Flum and Grohe (*Parameterized Complexity Theory*, 2006). Fixed-parameter time is
$f(k)\cdot|x|^{O(1)}$ with computable $f$, on the word RAM with the bit size of the input as input
size; fpt-reductions are stated as three separately provable conditions — construction and
correctness, a computable bound on the new parameter, and the running time. On top of these come
finite relational structures, first-order formulas and the classes $\Sigma_t$ and $\Pi_t$, model
checking and weighted Fagin definability, and the classes W[$t$] and A[$t$]. Clique, Independent Set,
Dominating Set, Hitting Set — the problem of the flow shop reductions above — and weighted CNF
satisfiability are defined on the archive's existing word formats.

The results are the calculus of fpt-reductions and the conditional lower bound "not in FPT unless
W[$t$] $\subseteq$ FPT"; bridges turning the polynomial-time and strict fpt-reductions already in the
archive into fpt-reductions; that Clique, Independent Set and Multicoloured Clique are
W[1]-complete, Clique is A[1]-complete, and W[1] = A[1]; that Hitting Set and Dominating Set are
W[2]-complete; and that Multicoloured Clique is NP-hard, by a reduction from Independent Set that is
both an fpt-reduction and a polynomial-time reduction. The intermediate results are stated
separately — Lemmas 6.11, 6.13 and 6.14, Lemma 6.37, Theorem 6.28, and Theorem 7.1 for $t = 2$ — and
every reduction is proved with its construction, its parameter bound, and a verified word-RAM program
bounding its running time.
