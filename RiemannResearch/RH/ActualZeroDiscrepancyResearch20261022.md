# Actual zero discrepancy: exact argument increments and the high-moment interface

Date: 22 October 2026.

## Result and scope

The existing unconditional counting infrastructure supplies the requested
interface. The new module is
`Analysis/ActualZeroDiscrepancy.lean`. It uses the actual multiplicity-weighted
count, the exact gamma density, and the already proved folded argument principle.
It does not substitute principal `Complex.arg` for a continued argument.

This is an exact discrepancy formulation. A separate formal construction of a
globally normalized argument lift is not claimed. Its increments are identified
with the genuine zeta logarithmic-derivative contour at good heights. That is the
analytic interface needed for interval moments.

## Exact normalization and endpoints

Write

\[
\mu(t)=\frac{\Re\psi(\tfrac14+\tfrac{it}{2})-\log\pi}{2\pi},
\qquad
G(t)=\int_0^t\mu(u)\,du,
\qquad
D(t)=N(0,t]-G(t).
\]

Here `Ncount` counts all nontrivial zeros in the strip, with their actual
analytic multiplicities. The lower endpoint is excluded and the upper endpoint
included. No simplicity or critical-line assumption occurs. The base point of
the smooth primitive is exactly zero; no asymptotic main term replaces it.

In classical notation, $G=\theta/\pi$, so $D=S+1$ away from zero heights on
the positive axis. This interpretation is ordinary mathematics; the checked
interface is the exact contour-increment theorem below, not a new Lean theorem
identifying an independently defined conventional argument lift. A fixed
normalization constant cancels from every increment.

At a zero height the discrepancy uses the upper-inclusive count. Conventional
midpoint values may instead be used for moment integrals. We prove this
independence through countable exceptional sets; we do not silently identify the
pointwise endpoint conventions or claim a formal midpoint-limit construction.

## Exact identities verified

For $0\le a\le b$,

\[
D(b)-D(a)=N(a,b]-\int_a^b\mu(u)\,du.
\]

This identity includes zero-height endpoints without restrictions. In particular,
for $t,h\ge0$,

\[
D(t+h)-D(t)=N(t,t+h]-\int_t^{t+h}\mu(u)\,du.
\]

For good heights $1\le a<b$, the stronger analytic identity is

\[
D(b)-D(a)=\frac1\pi\Im\left(
\int_{1/2}^{2}\frac{\zeta'}{\zeta}(\sigma+ia)\,d\sigma+
i\int_a^b\frac{\zeta'}{\zeta}(2+iu)\,du-
\int_{1/2}^{2}\frac{\zeta'}{\zeta}(\sigma+ib)\,d\sigma
\right).
\]

Both signed horizontal terms and the vertical contribution are retained.
The proof composes `N_eq_halfContour_completedZeta`,
`halfContour_completedZeta_split`, and `gamma_side`, then subtracts the exact
smooth increment. The continuous gamma provider is
`RvM.mu_continuous gammaFacts`; `gammaFacts` is the existing proved provider,
not an unproved parameter in the new conclusions.

The primary declarations are `smoothCount_sub`, `discrepancy_sub`,
`discrepancy_increment`, and `discrepancy_sub_eq_zeta_halfContour`.
The theorem `centered_window_evenMoment_eq` turns the pointwise window identity
into exact equality of the actual moment integrals.

## Regularity and zero-height conventions verified

- `smoothCount_continuous`: the gamma primitive is continuous.
- `discrepancy_measurable` and `discrepancy_intervalIntegrable`: the actual
  discrepancy is measurable and locally integrable.
- `discrepancy_shift_pow_intervalIntegrable`: every finite natural norm power
  of every fixed translate is integrable on every compact interval.
- `discrepancy_increment_pow_intervalIntegrable`: the same holds for increments.
- `discrepancy_sub_continuous_shift_pow_intervalIntegrable`: it also holds for
  remainders against any continuous approximating function.
- `badHeights_countable`, `ae_goodHeight`, and `ae_goodHeight_shift`: the
  exceptional ordinates and their translates have Lebesgue measure zero.
- `evenMoment_eq_of_eqOn_goodHeights` and its positive-interval version:
  changing the values at zero heights and adding a constant does not change
  increment moments.

The proof uses monotonicity of the nonnegative counting function and integrable
powers of continuous functions. It does not assume continuity of the discrepancy.
The general subtraction lemma belongs to `HighMomentTransfer`.

## Existing argument estimates reused

After proving the exact contour equality, `discrepancy_sub_abs_le_contour`
bounds the vertical argument variation by pi, retaining both horizontal
endpoint norms. Backlund's existing bound then gives
`discrepancy_sub_log_bound`:

\[
|D(b)-D(a)|\le
\pi^{-1}\{C\log a+\pi+C\log b\}
\]

for sufficiently large good endpoints $1\le a<b$. All exceptional heights are
already known to be null. This supplies the logarithmic increment estimate
needed for a complementary large-moment-order argument; the uniform all-order
asymptotic assembly is still to be formalized. No new zero-density estimate is
used for this bound.

## High-moment consumer

For any continuous real approximant $f$, put
$P_h(t)=f(t+h)-f(t)$ and $R(t)=D(t)-f(t)$. The decomposition

\[
D(t+h)-D(t)=P_h(t)+R(t+h)-R(t)
\]

is exact. `increment_evenMoment_le_continuous_approximation` applies the
existing transfer inequality with every integrability premise discharged.
The budget theorem `increment_evenMoment_le_of_continuous_budgets` assumes only

\[
\int_a^b|P_h|^{2k}\le T U^k,\qquad
\int_a^b|R(t+h)|^{2k}\le T V^k,\qquad
\int_a^b|R|^{2k}\le T V^k
\]

and concludes $J_{2k}\le T[9(U+V)]^k$, for $k\ge1$ and nonnegative budgets.
It remains a **conditional research reduction** until the quantitative
component bounds are supplied. Merely defining (R=D-f) proves no smallness.

## Precise remaining analytic obligations

1. **Open formalization: quantitative Selberg approximation.**
   Supply a prime trigonometric approximant to this discrepancy (allowing its
   constant normalization), with bounds for its remainder. The log-derivative
   contour identity alone is not an approximation theorem. The density
   estimates used in a Selberg proof need actual proved providers; the existing
   density interfaces must not be treated as providers merely because their
   conditional consumers compile.

2. **Open formalization: uniform shifted remainder moments.**
   Prove estimates on $t\in[T,2T]$, uniformly for shifts $0\le u\le1$,
   at the chosen cutoff and admissible moment order. The known STTB estimates
   cited in the earlier memorandum are unconditional results of ordinary
   mathematics, not conjectures. Their analytic proofs remain to be supplied
   in Lean.

3. **Open formalization: variance and exact polynomial asymptotics.**
   For the usual sine approximant, the diagonal variance is
   $V_X(h)=\pi^{-2}\sum_{p\le X}(1-\cos(h\log p))/p$.
   An upper bound suffices for a coarse moment estimate. The Gaussian main term
   requires quantitative variance comparison, diagonal combinatorics, and
   controlled off-diagonal error, with all dependence on $X,h,k,T$ retained.
   When $X=T^{c/k}$, replacing log X by log T inside this comparison is not an
   exact identity. The existing complex-polynomial upper bound alone does not
   establish the real/imaginary polynomial's Gaussian asymptotic.

4. **Open formalization: asymptotic transfer and uniform assembly.**
   Control the difference between actual and polynomial moments, including
   mixed/remainder terms, rather than using only an upper-bound transfer.
   Combine the admissible Selberg range with the complementary large-k range,
   using the logarithmic increment estimate now available. Preserve the
   quantifier order: constants precede T, k, and h.

The classical Tsang theorem is an established unconditional theorem. Its
specialization in this repository remains unproved in Lean. This work does not
assert that theorem, microscopic pair correlation, simplicity, or RH.

## Provenance and verification

Sources support the classical statement and analytic roadmap:
Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd edition,
Sections 9.3--9.4;
Tsang (1986), Theorem 4, as recorded in the earlier high-moment memorandum;
Simonic, Trudgian and Turnage-Butterbaugh, Sections 1, 3--4,
https://arxiv.org/abs/2010.10675.
The new proofs reuse the repository's existing RvM and gamma providers.

Complete combined candidate:
`job_HkkFjWlYfozQSbXmwzgnN9cmBPY8Udfh`,
exit code 0, verified=true, reported checking duration 6.308 seconds.
Five central axiom audits reported only propext, Classical.choice, and Quot.sound.
The module-level import check and the terminal publishing checkpoint are
separate gates; the combined candidate by itself is not publication validation.

Actual module import and six central axiom audits:
`job_eqml2yKNIJOnPviainijxpwYCf4bmip4`,
exit code 0, verified=true, reported duration 18.124 seconds, including builds
of the two affected modules. Every audit used only the same three standard
foundational axioms. The new discrepancy module built without warnings; the
existing HighMomentTransfer file retained its pre-existing header-style warning.

Workspace opening was batched with an independent GitHub read; its individual
request duration and subsequent polling delays were not separately measured.
Server-reported queue-to-start delay for each successful check was below
0.01 seconds. Checking durations are distinct from request latency and polling.
The terminal checkpoint result remains the final publication gate.

The first checkpoint, `job_9LKCOjBM9xp1-Zkd4GF-aX-to_FV7oMO`,
retained commit `6c5ee51e40178fb350c1c8f0493f713e0e1b6406` but did not publish:
integration with newer main conflicted in the catalog. Its queue delay was
92.339 seconds and total running duration was 74.161 seconds; the latter is not
a pure Lean checking time. Recovery preserved that work and applied the
verified modules to main at `7f80c4113620f776e0b1305b8d3bcd86ad170f00`,
placing the catalog entry beside the existing high-moment development.
The final recovery checkpoint must validate the integrated source before push.
