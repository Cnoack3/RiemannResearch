# A sharper complete Q Mellin witness

Research update, 18 October 2026. This formalizes the discrete witness
refinement in `BurnolQWitnessRefinement20261018.md` and retains its full
nonnegative cell remainder. The motivating paper is J.-F. Burnol,
*A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, arXiv:math/0103058v2 (2001). The discrete Q argument
is an independently developed continuation of the repository's Mellin
energy estimates; no historical novelty is claimed.

## Main theorem and its scope

Write beta = Re(s) > 1/2, a = 2 beta - 1, and

\[
Q(n)=\frac{1}{\zeta(2)n^2},\qquad
\Delta_s(n)=n^{-s}-(n+1)^{-s},\quad n\ge1,
\]
\[
S_s=\sum_{n\ge1}n^2|\Delta_s(n)|^2,\qquad
B(\beta)=\sum_{n\ge1}\frac{n^{-2\beta}}{n+1}.
\]

The new declarations prove genuine summability, not merely identities
involving Lean's default value for an unsummable `tsum`. They establish

\[
0<S_s\le\frac{|s|^2 B(\beta)}{a},\qquad
\frac12+\frac{2^{1-2\beta}}6\le B(\beta)
\le1-\frac{1-2^{1-2\beta}}6<1.
\]

For a zeta zero s with beta > 1/2 and s != 1, every finite real legal
combination F = sum_i c_i g_{d_i}, with d_i > 0 and
 g_d(n) = (n mod d)/d, satisfies

\[
\boxed{\quad
\|1-F\|_Q^2\ge\frac1{\zeta(2)S_s}
\ge\frac{2\beta-1}{\zeta(2)|s|^2 B(\beta)}
>\frac{2\beta-1}{\zeta(2)|s|^2}.
\quad}
\]

The rightmost expression is the earlier global Pareto-to-Q transfer bound.
The strict comparison is a separate checked theorem. It does not assert a
comparison with every target-dependent metric-correction bound elsewhere
in the repository.

The hypotheses on s are explicit zero-obstruction hypotheses, not a
presumption that an off-critical zero exists. The cell estimates, series
identities, functional representation, and bound comparison require no
zeta-zero assumption. The final legal-error theorem uses that assumption
to annihilate the actual legal residues.

## Exact identities before inequalities

The actual signed functional is

\[
L_s(f)=s\,\mathrm{qMellin}(f,s)
      =\sum_{n\ge1} f(n)\Delta_s(n).
\]

`qMellin_hasSum` proves this for every actual `QHilbert` vector. Weighted
Cauchy--Schwarz gives

\[
|L_s(f)|^2\le\zeta(2) S_s\|f\|_Q^2.
\]

There is exactly one factor of zeta(2). The formal domain is the repository's
real Hilbert space and the codomain is complex. The theorem is a norm
bound, not a claim of equality with the real operator norm. Equality with
zeta(2) S_s as squared dual norm belongs to the complexified space and is
not a new Lean declaration in this update.

The exact complete metric identity is

\[
\sum_{n\ge1} n(n+1)|\Delta_s(n)|^2
=S_s+\sum_{n\ge1}n|\Delta_s(n)|^2.
\]

The last series is nonnegative and summable. In particular,

\[
S_s\le\frac{|s|^2}{a}-|1-2^{-s}|^2<\frac{|s|^2}{a}.
\]

The B-factor estimate comes from the sharper cell envelope

\[
E_n:=n^2|\Delta_s(n)|^2\le
U_n:=|s|^2\frac{n}{n+1}\int_n^{n+1}x^{-2\beta}\,dx.
\]

Let r_n = U_n-E_n >= 0. Both the energy and remainder series are summable,
and the new source proves the complete equality

\[
\boxed{S_s+\sum_{n\ge1}r_n=\frac{|s|^2 B(\beta)}a.}
\]

For every N >= 0 it therefore proves

\[
S_s\le\frac{|s|^2 B(\beta)}a-\sum_{n=1}^N r_n,
\qquad
\|1-F\|_Q^2\ge
\frac1{\zeta(2)\left(|s|^2B(\beta)/a-\sum_{n=1}^N r_n\right)}.
\]

Every denominator is positive because it dominates S_s > 0. The refinement
is non-strict in general; it is strict if a positive retained remainder is
certified. No tail is discarded from the energy or its proof.

## Abel boundary and its discharge

With b_n = n^(1-2 beta), the exact finite identity is

\[
\sum_{n=1}^N\frac{n}{n+1}(b_n-b_{n+1})
=\sum_{n=1}^N\frac{b_n}{n(n+1)}
 -\frac{N}{N+1}b_{N+1}.
\]

The finite terminal term is retained. The profile and its boundary are
proved to tend to zero for beta > 1/2. Both infinite series are proved
summable, giving the exact identity

\[
\sum_{n\ge1}\frac{n}{n+1}\int_n^{n+1}x^{-2\beta}\,dx
=\frac{B(\beta)}{2\beta-1}.
\]

The generic analysis module also preserves both boundaries on shifted
blocks, handles a nonzero limiting profile in tail estimates, and retains
an arbitrary summable cell remainder.

## Source map

- `Analysis/ReciprocalCellAbel.lean`: exact finite and infinite Abel identities,
  shifted boundaries, tails, and remainder identities.
- `RH/WeightedPowerCellMass.lean`: actual power profile, summability,
  vanishing boundary, exact B-factor sum, and strict B bounds.
- `RH/QMellinCellEnergy.lean`: actual complex Mellin differences, complete
  Q/P metric identity, energy envelope, and exact remainder.
- `RH/QMellinWitness.lean`: signed series on actual QHilbert, weighted
  functional bound, positivity, legal-error bounds, and strict comparison.

Main declarations are `legal_error_lower_envelope`,
`legal_error_lower_envelope_sub_slack`, `old_bound_lt_envelope_bound`,
`q_energy_add_slack_eq_envelope`, and `weightedPowerCellMass_tsum`.

## Remaining RH obligation

This is a stronger quantitative obstruction, not a proof of RH. It gives
no unconditional sequence of legal approximants with complete Q error
tending to zero. Establishing that upper approximation estimate remains
the main open task. The current legal-error declarations quantify over
finite combinations. A closed-span extension follows mathematically from
continuity, but is not presented as a new checked declaration here.

The previous appendix's additional elementary bound
B(beta) <= (2 beta + 1)/(4 beta) and proposed sharper finite-head tail
certificate remain ordinary mathematics unless separately formalized.
Likewise, no Burnol growing-zero-family uniformity or critical-line
second-order asymptotic has been proved by these declarations.
