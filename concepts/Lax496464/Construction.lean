import Lax496464.FlowShop
import Lax496464.HittingSet

/-!
---
title: The Construction of Section 8
type: definition
---
The shop built from a Hitting Set instance $(F_1, \dots, F_m)$ over $\{1, \dots, n\}$
with solution size $k$. It has $k$ second-stage machines and unit weights.

The time axis is measured in the unit $Q = (k-1)(n+1)$ and divided into $R$ *segments*,
each of which is divided into $m$ *epochs*, one per set of the family. The epoch of
segment $r$ and set $j$ is numbered $g(r,j) = rm + j$ and occupies the interval from
$G(r,j) = g(r,j)^2 Q$ to $G(r,j) + (2g(r,j)+1)Q = (g(r,j)+1)^2 Q$; the squares make each
epoch exactly $(2g+1)Q$ long, which is what the jobs are cut to fit.

Each epoch carries three families of jobs.

* One *selection job* for every element $i$ of $F_j$. It needs no preprocessing, occupies
  the whole epoch, and is due at its end, offset by $i$.
* Two *dummy jobs* for every element $i$ of the universe. The first occupies the first
  $g(r,j)Q$ of the epoch, the second the last $(g(r,j)+1)Q$; both need $g(r,j)(n+1)$ units
  of preprocessing, which is what limits how many of them an epoch can afford.

A hitting set of size $k$ selects, in every epoch, one selection job — the one for the
element hitting that epoch's set — and $2(k-1)$ dummies, one pair for each of the other
$k-1$ elements. The target is $R \cdot m \cdot (2k-1)$ just-in-time jobs.

# Formalization Notes

**Two corrections to the published construction.** Both are recorded here because the
construction below is the corrected one.

The first is the number of segments. The paper takes $R = k(n-1)+1$, and that is one too
few. The extraction of a hitting set is a pigeonhole: each machine's offset is
nondecreasing across segments and confined to $\{1, \dots, n\}$, so it changes at most
$n-1$ times, and at most $k(n-1)$ of the gaps between consecutive segments see any
change. A gap across which nothing changes therefore exists only if there are *more* than
$k(n-1)$ gaps, that is only if $R - 1 > k(n-1)$. The published value gives exactly
$R - 1 = k(n-1)$, and the count is not slack: let the first machine change across the
first $n-1$ gaps, the second across the next $n-1$, and so on, and every gap is consumed
with no two segments alike. Taking $R = k(n-1)+2$ repairs it, and costs nothing: every
statement about the construction is generic in $R$.

The second is the range of $k$. The paper writes $p(A^r_{i,j}) = \frac{1}{k-1} g(r,j) Q$,
which presupposes $k \ge 2$ and says so nowhere. At $k \le 1$ the construction does not
merely degenerate, it is wrong: there $Q = 0$, so every second operation has length zero,
every interval $[s, d)$ is empty and no two jobs conflict at all. Every dummy still costs
more to preprocess than it has time for, but *all* selection jobs become schedulable
simultaneously, whatever the family looks like, and the target is met with no hitting set
in sight. The problem reduced from is accordingly restricted to $2 \le k \le n$, which
costs nothing.

Two smaller things: the printed $\frac{1}{k-1} g(r,j) Q$ is the integer $g(r,j)(n+1)$,
which is what appears below, and the target size printed in the opening paragraph of the
section as $2m(2k-1)$ is the $R \cdot m \cdot (2k-1)$ that the section's own subsections
and lemmas use.

**Numbering.** Jobs are numbered rather than tagged, because an instance is something a
machine is handed and a word presents its jobs in an order. The selection block comes
first, $R$ copies of one job per membership pair $(j, i)$ with $i \in F_j$, in the order
in which the pairs are enumerated; then the two dummy blocks, each $R \cdot m \cdot n$
jobs indexed by segment, set and element in that order. Only the memberships that exist
are given jobs, so the weights are all one and the hardness claim lands on the
unit-weight slice, which is the problem $FF(1,m) \mid\mid \sum_j Z_j$ the paper's first
theorem is about.

The universe is counted from zero here and from one in the paper, and the offset that
distinguishes the $n$ jobs of an epoch from one another is correspondingly $i+1$. It has
to be nonzero: an offset of zero would make two jobs of one epoch share a due date, and
the extraction of the hitting set reads the element off the due date.

The element offsets are smaller than $Q$, so they perturb the due dates without
disturbing the tiling of an epoch. That $n < Q$ is exactly what $k \ge 2$ buys.
-/

namespace Lax496464.Construction

open Lax496464.FlowShop

variable (P : HittingSet.Instance) (k : ℕ)

/-- `R = k(n − 1) + 2`, the number of segments. The paper's value is one smaller; see the
notes above. -/
def R : ℕ := k * (P.n - 1) + 2

/-- `Q = (k − 1)(n + 1)`, the unit the whole time axis is measured in. -/
def Q : ℕ := (k - 1) * (P.n + 1)

/-- `g(r,j) = rm + j`, the position of the epoch of segment `r` and set `j`, counted from
one. -/
def g (r j : ℕ) : ℕ := r * P.m + (j + 1)

/-- `G(r,j) = g(r,j)²Q`, the instant that epoch begins. -/
def G (r j : ℕ) : ℕ := g P r j ^ 2 * Q P k

/-- The membership pairs `(j, i)` with `i ∈ F j`, enumerated. Each of them contributes one
selection job per segment. -/
def memberList : List (ℕ × ℕ) :=
  (List.finRange P.m).flatMap fun j =>
    (P.members j).map fun i : Fin P.n => ((j : ℕ), (i : ℕ))

/-- The number of selection jobs: one per segment and membership pair. -/
def selCount : ℕ := R P k * (memberList P).length

/-- The number of jobs in one dummy block: one per segment, set and universe element. -/
def dumCount : ℕ := R P k * P.m * P.n

/-- The number of jobs of the constructed shop. -/
def numJobs : ℕ := selCount P k + 2 * dumCount P k

/-- Job `t` described: which of the three families it belongs to — `0` selection, `1` the
first dummy, `2` the second — and its segment, set and element. -/
def slot (t : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if t < selCount P k then
    let e := (memberList P).getD (t % (memberList P).length) (0, 0)
    (0, t / (memberList P).length, e.1, e.2)
  else
    let u := t - selCount P k
    let v := if u < dumCount P k then u else u - dumCount P k
    (if u < dumCount P k then 1 else 2,
      v / (P.m * P.n), v % (P.m * P.n) / P.n, v % P.n)

/-- Which of the three families job `t` belongs to. -/
def family (t : ℕ) : ℕ := (slot P k t).1

/-- The segment of job `t`. -/
def seg (t : ℕ) : ℕ := (slot P k t).2.1

/-- The set of the family job `t` belongs to. -/
def setIdx (t : ℕ) : ℕ := (slot P k t).2.2.1

/-- The universe element of job `t`. -/
def elem (t : ℕ) : ℕ := (slot P k t).2.2.2

/-- Preprocessing times: a selection job needs none, a dummy of epoch `(r,j)` needs
`g(r,j)(n+1)`, which is the paper's `g(r,j)Q/(k−1)`. -/
def jp (t : ℕ) : ℕ :=
  if family P k t = 0 then 0 else g P (seg P k t) (setIdx P k t) * (P.n + 1)

/-- Processing times: a selection job fills its whole epoch, and the two dummies split it
in the ratio `g : g+1`. -/
def jq (t : ℕ) : ℕ :=
  if family P k t = 0 then (2 * g P (seg P k t) (setIdx P k t) + 1) * Q P k
  else if family P k t = 1 then g P (seg P k t) (setIdx P k t) * Q P k
  else (g P (seg P k t) (setIdx P k t) + 1) * Q P k

/-- Due dates: the first dummy is due a `g(r,j)Q` into its epoch, the other two at its
end; all three are offset by the element they carry. -/
def jd (t : ℕ) : ℕ :=
  if family P k t = 1 then
    G P k (seg P k t) (setIdx P k t) + g P (seg P k t) (setIdx P k t) * Q P k
      + (elem P k t + 1)
  else
    G P k (seg P k t) (setIdx P k t) + (2 * g P (seg P k t) (setIdx P k t) + 1) * Q P k
      + (elem P k t + 1)

/-- The shop built from `P` and `k`: `k` machines and unit weights. -/
def construct : FlowShop.Instance where
  jobs := numJobs P k
  machines := k
  p t := jp P k t
  q t := jq P k t
  d t := jd P k t
  w _ := 1

/-- The number of just-in-time jobs the construction asks for: one selection job and
`2(k−1)` dummies in each of the `R·m` epochs. -/
def target : ℕ := R P k * P.m * (2 * k - 1)

end Lax496464.Construction
