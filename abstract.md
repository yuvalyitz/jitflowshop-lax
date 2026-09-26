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
