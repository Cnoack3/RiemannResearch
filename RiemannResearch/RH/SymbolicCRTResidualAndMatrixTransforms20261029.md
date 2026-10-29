# Symbolic CRT residuals and complete constrained matrix transformations

29 October 2026. This continuation uses symbolic Hilbert-space identities and
exact matrix algebra. It adds no numerical approximations. Earlier fixed-stage
minimizers, arithmetic certificates, and conductor-gap inequalities are unchanged.

## Exact result for the actual squarefree residual

Let S be the closed legal squarefree CRT span in the complete Q Hilbert space,
r = 1 - P_S 1 its actual orthogonal residual, P_H the physical head projection,
h_H = P_H 1, and t_H = r - P_H r. For every legal F equal to one through H,

\[
\|r\|_Q^2=\langle t_H,1-F\rangle_Q,
\qquad
\|r\|_Q^4\leq\|t_H\|_Q^2\|1-F\|_Q^2.
\]

The first identity is exact and signed. Orthogonality gives
<r,F> = 0 and <r,1> = ||r||^2; exact-head matching removes the finite head
from its pairing with 1-F. The inequality is Cauchy--Schwarz applied only
after that identity. Every norm and inner product contains the infinite tail.

There is also an exact completion, with a retained nonnegative remainder.
Write a_H = <r,h_H>. Whenever ||t_H||^2 is nonzero,

\[
\boxed{\quad
\|F\|_Q^2=\|h_H\|_Q^2+
\frac{a_H^2}{\|t_H\|_Q^2}+
\left\|F-h_H+\frac{a_H}{\|t_H\|_Q^2}t_H\right\|_Q^2.
\quad}
\]

The sign is fixed by <t_H,F-h_H> = -a_H. If r is nonzero, any feasible
exact-head vector forces ||t_H|| > 0, so the denominator is justified.
This is a period-independent lower certificate applying to every feasible
vector, including the actual constrained minimizer. It is not a numerical
lower bound, since the actual residual has not been computed or proved nonzero.

## What the epsilon and weak arguments establish

The tails t_H tend to zero without an arithmetic hypothesis. The new Lean
module proves the following stronger alternative: if r is nonzero, then
for **every** legal family F_n with exact heads H_n tending to infinity,

\[
\|1-F_n\|_Q\longrightarrow+\infty,
\qquad \|F_n\|_Q^2\longrightarrow+\infty.
\]

A separate corollary instantiates this with the repository's actual primorial
minimumAt(sigma(n), H_n), under the existing head-feasibility condition
H_n <= sigma(n)+1. No monotonicity or rate assumption on period growth is
needed for this conditional divergence theorem.

Consequently a finite energy bound on infinitely many members of a cofinal
exact-head family already forces r=0. A bound on the entire original canonical
schedule is unnecessary. The theorem does not establish the needed bounded
subsequence or assert which residual branch occurs.

The quantifier issue is explicit. Knowing that for every epsilon>0 some H has
||t_H||<epsilon, and that every H has a legal finite-norm exact head, does not
control their product. The norm of the chosen head depends on H. If r is
nonzero, the exact identity forces

\[
\|t_H\|_Q\,\|1-F_H\|_Q\geq\|r\|_Q^2
\]

at every stage. Choosing a faster decreasing epsilon sequence does not negate
this inequality. In contrast, actually proving for every epsilon>0 the
existence of a legal F with ||1-F||<epsilon would settle the required closure;
that existence assertion remains open.

The missing weak test is equally explicit. Every legal F_n has <r,F_n>=0.
The new theorem residual_moment_tendsto_iff proves that convergence of these
moments to <r,1> is equivalent to r=0. Genuine weak convergence would include
this test; coordinatewise or finite-mode convergence does not supply it.
This uses the standard Hilbert-space interpretation of weak topology, as in
[Mathlib's weak-space documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/Spaces/WeakDual.html).
The reference supports the terminology, not the arithmetic closure conclusion.

## Complete signed matrix transformations

For a finite dictionary, let G be its complete Gram matrix, A the head matrix,
b the head target, and c its coefficients. Under c=S z,

\[
G'=S^TGS,\quad A'=AS,\qquad
z^T G'z=(Sz)^TG(Sz),\quad A'z=A(Sz).
\]

The new matrix module proves these identities and equality of the entire
feasible-energy sets whenever z -> S z is surjective. This includes invertible
changes of basis and redundant new coordinates. No entrywise positivity,
positive definiteness, or independence of head rows is needed for the set
equality. Under positive definiteness and independent effective constraints,
the existing actual attained minimum and unique original minimizing
coefficients are also preserved.

Applied to a complete Q Gram matrix, this result retains every cross term
and infinite Q-tail contribution. It is a coordinate change inside the same
legal span. Adjoining new conductor directions can enlarge the span and lower
the minimum; the theorem does not identify that operation with reparametrizing
old directions. Likewise, stagewise Gram whitening changes the head matrix
along with the Gram matrix and supplies no uniform estimate by itself.

## Ramanujan, Pareto, and a possible dual route

Existing RamanujanTransfer.q_span_eq, q_closure_eq, q_projection_eq, and
q_orthogonal_eq identify the residue and Ramanujan-packet subspaces for positive
divisor-closed dictionaries. Thus the exact transforms are useful for arithmetic
organization, but their use alone does not remove the residual. The existing
Q/Pareto continuous linear equivalence preserves physical sequences and
closure membership, while their numerical inner products differ.

A natural symbolic target is to identify enough continuous annihilators to
rule out this residual. For example, density of finite-support annihilators
in S-perp would suffice: finite exact-head feasibility makes every such
annihilator pair to zero with 1, and continuity would then eliminate r. This
core-density property has not been proved. It is an additional sufficient
hypothesis; residual vanishing alone has not been shown to establish it for
this arithmetic space. It must not be inferred from finite matrix invertibility.

## Formalization and status

- `RH/QSquarefreeExactHeadResidualBarrier.lean`: exact tail pairing, signed
  completion, quantitative lower inequalities, cofinal error and energy
  divergence conditional on r != 0, actual minimumAt corollary, frequent-bound
  consequences, and the precise missing weak moment.
- `LinearAlgebra/FiniteConstrainedMatrixReparametrization.lean`: full signed
  congruence, transformed constraints, equal feasible-energy sets, and exact
  preservation of the attained constrained minimum.

The final publication checkpoint validates these modules and their aggregate
import. There are no sorry/admit declarations or new axioms. The source proofs
are symbolic; Wolfram separately confirmed the scalar completion algebra,
which is not used as a Lean proof premise. Numerical certificates from earlier
work keep their earlier, separately documented verification status.

Open: establish r=0 arithmetically, or construct genuine all-epsilon witnesses,
or prove a bounded cofinal subsequence. No unconditional cofinal convergence,
uniform energy bound, or RH proof is claimed.
