import Lax496464.FlowShop

/-!
---
title: Earliest-Start-Time Order, and Distinct Endpoints
type: definition
---
Two standing conventions of the paper's algorithmic sections, and the rescaling that
establishes the second.

An instance is *in earliest-start-time order* when its jobs are numbered so that the
start times $s_1 \le \dots \le s_n$ are nondecreasing. Every algorithm of the paper
begins by sorting the jobs this way, and its tables are indexed by the resulting order.

The *endpoints* of an instance are the $2n$ numbers $s_j$ and $d_j$. They are *distinct*
when no two of them coincide. Section 4 assumes this, and obtains it by the rescaling
$$d'_j = (n+1)d_j + j, \qquad q'_j = (n+1)q_j, \qquad p'_j = (n+1)p_j ,$$
which leaves the weights alone.

# Formalization Notes

Earliest-start-time order is a property of an instance rather than a separate kind of
object, so that every result about instances applies to one in that order without
transport.

The rescaling shifts the *whole* interval of job $j$ by $j$, not only its right endpoint,
since $s'_j = d'_j - q'_j = (n+1)s_j + j$. That is what makes it sound, and also what
makes it depend on the numbering: two intervals that merely touch, $s_i = d_j$ with no
conflict between them, would begin to overlap if the later-starting job had the smaller
index. Under earliest-start-time order that cannot happen, because $s_i = d_j > s_j$
forces $j < i$. So the assumption is not about the size of the multiplier alone, and the
statements about the rescaling carry the order as a hypothesis.

The rescaled instance has the same number of jobs, so a set of jobs of one is a set of
jobs of the other with no coercion.
-/

namespace Lax496464.EstOrder

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The jobs are numbered in nondecreasing order of their start times. -/
def EstOrdered (I : Instance) : Prop := ∀ i j : I.Job, i ≤ j → s i ≤ s j

/-- No two of the `2n` endpoints `s j` and `d j` coincide. -/
structure DistinctEndpoints (I : Instance) : Prop where
  /-- Distinct jobs have distinct start times. -/
  start_inj : ∀ i j : I.Job, s i = s j → i = j
  /-- Distinct jobs have distinct due dates. -/
  due_inj : ∀ i j : I.Job, (I.d i : ℤ) = (I.d j : ℤ) → i = j
  /-- No start time is a due date. -/
  start_ne_due : ∀ i j : I.Job, s i ≠ (I.d j : ℤ)

/-- The rescaled instance `d' j = (n+1) d j + j`, `q' j = (n+1) q j`, `p' j = (n+1) p j`,
with the weights unchanged. -/
def scale (I : Instance) : Instance where
  jobs := I.jobs
  machines := I.machines
  p j := (I.jobs + 1) * I.p j
  q j := (I.jobs + 1) * I.q j
  d j := (I.jobs + 1) * I.d j + (j : ℕ)
  w j := I.w j

end Lax496464.EstOrder
