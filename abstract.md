This submission formalizes just-in-time scheduling in two-stage flexible flow shops,
following Heeger, Hermelin, Itzhaki, Schieber and Shabtay.

**Flow-Shop Scheduling.** In $FF(1,m) \mid\mid \sum_j w_j Z_j$, each job is preprocessed
on a single machine and then processed on one of $m$ identical machines. The objective
is to maximize the weight of jobs that finish exactly at their due dates. The
formalization proves the feasibility characterization, dynamic programs with running
times $O(W n^m)$, $O(W 2^\omega n)$ and $O(W m^{q_{\max}} n)$, an $O(n\log n)$ greedy
algorithm for equal preprocessing times and unit weights, a totally unimodular integer
program for proper instances with equal preprocessing times, and approximation schemes
for bounded $m$, $\omega$ or $q_{\max}$. Here $W$ is the total job weight, $\omega$ is
the maximum overlap of second-stage intervals, and $q_{\max}$ is the largest second-stage
processing time. A reduction from Hitting Set establishes strong NP-hardness and
W[2]-hardness for the number of machines, even with unit weights.

The submission also formalizes the W-hierarchy foundations used in the parameterized
hardness arguments, following Flum and Grohe (2006). This supporting development includes
FPT-reductions and the relevant completeness results for standard parameterized problems.

**Machine Model and Hypotheses.** Algorithms and reductions are implemented on the
archive's word RAM through its verified IMP+ compiler. Scheduling running-time
statements assume positive processing times and sufficient word size for the input
and intermediate values. FPT bounds use the bit size of the input and a computable
parameter-dependent factor. The scheduling reduction uses hitting sets of size at least
two and $k(n-1)+2$ segments; its input encoding bounds the universe size by the length
of the input word. The concept pages state the precise hypotheses and explain the
other differences from the printed scheduling paper. Hitting Set's NP-hardness is
proved using the archive's Cook–Levin theorem, and the consecutive-ones theorem used
for total unimodularity is also proved.

The annotated manuscript presents the flow-shop results. The W-hierarchy results are
documented in the archive's concept pages and Lean modules.
