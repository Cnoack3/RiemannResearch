# Squarefree CRT/Parseval block averages, 2026-10-16

Source: Christian Noack's squarefree continuation request in the CRT carry,
bounded-tail and arithmetic Parseval research program.

## Exact setting

Let \(Q(n)=1/(\zeta(2)n^2)\), \(g_d(n)=(n\bmod d)/d\), and let
\(S_{\rm sf}\) be the **algebraic**, finite span of \(g_d\) with
\(d\ge2\) squarefree. Its closure is a separate operation.

A vector lies in \(S_{\rm sf}\) exactly when its physical sequence belongs
to the divisor residue span of some squarefree common period \(L\).
For a given finite expansion one can use the lcm of its conductors.
The Lean proof obtains the common-period representation from the existing
coordinate-preserving Q/P span map; it does not assert a new quantitative
bound for the period.

## Conditional bounded-head theorem

Assume actual vectors \(F_N\in S_{\rm sf}\) satisfy

\[
F_N(k)=1\quad(1\le k\le N),\qquad
\|1-F_N\|_Q^2\le B\quad\hbox{for every }N
\]

with one real constant \(B\). There is a strictly increasing selection
\(q:\mathbb N\to\mathbb N\) such that

\[
A_m=\frac1m\sum_{i=0}^{m-1}F_{q(m+i)}
\]

remains squarefree legal, has a squarefree common period, equals one through
\(m\) for \(m>0\), and converges strongly to one. The exact block identity is

\[
A_m=2\overline F_{2m}-\overline F_m.
\]

For the complete divisor wavelets \(V_r\) and Jordan weight \(J_2(r)\),

\[
\sum_{r\ge1}\frac{|\langle 1-A_m,V_r\rangle_Q|^2}{J_2(r)}
=\|1-A_m\|_Q^2\longrightarrow0.
\]

All positive indices are included. Squarefree conductors do not restrict
these coordinates to squarefree indices or divisors of the period.

## Literal finite-period provider

If \(L_N\) is squarefree and the physical \(F_N\) belongs to its divisor
residue span, boundedness and \(L_N\)-periodicity follow algebraically.
Exact heads and the full periodic comparison give

\[
\|1-F_N\|_Q^2
\le \sum_{a=1}^{L_N}\frac{|1-F_N(a)|^2}{a^2}
= \sum_{a=N+1}^{L_N}\frac{|1-F_N(a)|^2}{a^2}.
\]

Thus a uniform bound for the displayed literal tails supplies the full
norm bound in the conditional theorem, without assuming periodicity or
pointwise boundedness separately.

## Actual squarefree capacity and RH

The same hypotheses yield \(1\in\overline{S_{\rm sf}}\).
For the existing exhaustive squarefree optimizer stages,

\[
\delta_n=\frac1{1+\kappa_n},\qquad
\kappa_n=\frac{1-\delta_n}{\delta_n},
\]

and hence \(\kappa_n\to+\infty\). The existing Mellin-obstruction consumer
then gives Mathlib's actual RiemannHypothesis proposition.

This is a **conditional research reduction**.
Open: supply the uniform bound for the same squarefree family that matches
the growing exact heads. The automatic error bound for finite orthogonal
projections does not supply such a family, because those projections need
not interpolate the growing heads exactly.

## Lean declarations and verification evidence

Owner module: RH/QSquarefreeExactHeadAverages.lean, namespace
RiemannResearch.RH.QSquarefreeExactHeadAverages.

- squarefree_span_iff_common_period
- exists_squarefree_exact_head_block_averages
- squarefree_full_error_bound_of_periodic_tail_bound
- squarefree_closure_capacity_and_rh_of_bounded_exact_heads

The complete four-declaration source passed isolated server job
job_1t9-G09LjsZcj2mnjRXM4Pr6uSefOO8m with exit code zero, verified=true.
The two principal declarations' axiom reports contained only propext,
Classical.choice, and Quot.sound. Local hypotheses, including the
uniform arithmetic bound, remain visible in their theorem types and are
not discharged by an axiom report.

Publication is performed only through the mandatory server checkpoint,
which audits and validates the project and changed child module before
pushing; any integrated source must pass the same gate.
