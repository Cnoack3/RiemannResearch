# Ingham continuation: actual damped divisor series and L2 limits

Prepared 16 November 2026, America/Los_Angeles.
Initial investigation base: d5344689e606c9b71462ed475eaed00ddbe57337.
Integration base: 6491cfe923f3125a929f1b88d4d4606d276bad55.

## Status

The actual exponentially damped divisor series now has an unconditional
positive-damping convergence provider. Finite cutoffs converge uniformly on
the entire real height axis and in L2 on every finite interval. Square
moments converge after subtracting any fixed continuous function, including
the actual finite head.

This proves quantitative convergence for every positive real damping scale.
During verification, the separate integer-scale uniform moment theorem was
published in [6491cfe](https://github.com/Cnoack3/RiemannResearch/commit/6491cfe923f3125a929f1b88d4d4606d276bad55).
The present update integrates with that result and proves exact agreement
of the two series definitions. The geometric truncation bound is not a
replacement for that sharper moment theorem.

The Mellin representation, complete contour estimates, and full actual-zeta
residual bound remain open. I1 and Z03 are not closed.

Module: [Analysis/DampedDivisorSeries.lean](Analysis/DampedDivisorSeries.lean).
The reusable coefficient bound belongs to
[Analysis/DivisorPolynomialMoment.lean](Analysis/DivisorPolynomialMoment.lean).
Both are exported by RiemannResearch.lean. The existing coefficient bound
is moved from SmoothedDivisorMoment into its owning DivisorPolynomialMoment
module, preserving its name and its stronger all-natural-number statement.

## Actual terms and exact tail identity

Let \(d(n)\) be the divisor count and \(Y>0\). With the repository's actual
critical divisor coefficient and exponential phase, put

\[
 P_{N,Y}(t)=\sum_{n=1}^{N} d(n)n^{-1/2}
                   e^{-n/Y}e^{-it\log n},\qquad
 S_Y(t)=\sum_{n=1}^{\infty} d(n)n^{-1/2}
                   e^{-n/Y}e^{-it\log n}.
\]

The finite expression is exactly the existing divisorPolynomial with
weights \(\exp(-n/Y)\), not a newly substituted approximation.
divisorPolynomial_eq_sum_dampedDivisorTerm proves that identification.

The equality precedes every estimate:

\[
 S_Y(t)-P_{N,Y}(t)
   =\sum_{n>N}d(n)n^{-1/2}e^{-n/Y}e^{-it\log n}.
\]

Declaration: dampedDivisorSeries_sub_polynomial_eq_tsum.
Absolute summability is established before rewriting the tail.

## Explicit quantitative convergence

The elementary bound criticalDivisorCoefficient_norm_le gives
\(d(n)n^{-1/2}\le n\) for \(n\ge1\). Set \(r=e^{-1/Y}\), so \(0<r<1\).
The complete scalar tail majorant has the exact closed form

\[
 B_Y(N)=\sum_{n>N}n e^{-n/Y}
       =r^{N+1}\left(\frac{N+1}{1-r}+\frac{r}{(1-r)^2}\right).
\]

For every real \(t\), every \(N\ge0\), and \(H\le T\),

\[
 |S_Y(t)-P_{N,Y}(t)|\le B_Y(N),\qquad
 \int_H^T |S_Y(t)-P_{N,Y}(t)|^2\,dt
       \le (T-H)B_Y(N)^2 \longrightarrow 0.
\]

The bound is independent of \(t\), and the scale dependence is explicit.
The proof uses absolute geometric majorization; it asserts no arithmetic
cancellation and no optimality of this majorant.

| Declaration in RiemannResearch.Analysis | Result |
| --- | --- |
| summable_dampedDivisorMajorant | Summable actual geometric majorant for every Y>0 |
| summable_norm_dampedDivisorTerm | Absolute convergence of the actual terms |
| tendstoUniformly_damped_divisorPolynomial | Uniform convergence for all real heights |
| continuous_dampedDivisorSeries | Continuity supplied without a separate premise |
| dampedDivisorTailBudget_eq | Exact closed form of the complete majorant |
| norm_dampedDivisorSeries_sub_polynomial_le | Explicit uniform tail bound |
| integral_dampedDivisor_tail_sq_le | Quantitative finite-interval L2 error |
| tendsto_integral_dampedDivisor_tail_sq | Vanishing L2 error |

## Moment limits with the finite head retained

For every continuous \(g:\mathbb R\to\mathbb C\) and fixed real \(H,T\),

\[
 \lim_{N\to\infty}\int_H^T |P_{N,Y}(t)-g(t)|^2\,dt
   =\int_H^T |S_Y(t)-g(t)|^2\,dt.
\]

Declaration: tendsto_integral_damped_divisorPolynomial_sub_sq.
The dominating function is explicitly
\((B_Y(0)+|g(t)|)^2\); continuity makes it integrable on the finite interval.

The specialization integral_dampedDivisor_tail_sq_le_of_eventually takes
\(g=P_{L,Y}\). Any one constant bounding all sufficiently large finite
cutoff differences then bounds the actual infinite tail. This last transfer
lemma is conditional on that displayed finite bound. It does not convert
the earlier estimate growing with the upper cutoff into a uniform estimate.


## Connection to the uniform integer-scale moment

The new declaration smoothedDivisorSeries_eq_dampedDivisorSeries in
SmoothedDivisorMoment proves, for every positive integer N and real t,

\[
 \operatorname{smoothedDivisorSeries}(N,t)
   =\operatorname{dampedDivisorSeries}((N:\mathbb R),t).
\]

The proof removes the zero term from the absolutely convergent ordinary
series. Thus the already published uniform moment and smoothing-defect
bounds and the new quantitative real-scale convergence results concern
exactly the same function at integer scales.

## Next obligations

1. Use the published integer-scale moment bound in the central contour
   estimates. Extending that sharp moment statement to arbitrary real
   damping scale is a separate possible strengthening.
2. Establish the complete smoothed zeta-square Mellin representation,
   including all residues and contour sides.
3. Prove the off-critical chi and moving Gamma/Gamma-derivative estimates.
4. Supply one height-independent constant for the complete actual residual.

The new convergence theorem supplies explicit cutoff control and
fixed-head moment limits. The integer-scale arithmetic moment is established;
the remaining central contour and complete residual estimates stay visible.

## Verification and provenance

The complete coherent candidate passed Bazel/BuildBuddy in
job_IFTyjKylS7ogF3Kzi2DZkfzDekAEpTDs (server build: 26.585 seconds):
[BuildBuddy record](https://app.buildbuddy.io/invocation/9ca721bd-77b9-49ad-abcb-b06c1a81683e).

The persisted module includes four guarded axiom audits for the L2 limit,
closed-form budget, moment limit, and finite-to-infinite bound transfer.
They allow exactly propext, Classical.choice, and Quot.sound.

The integrated source, including the unchanged four guards and the new
integer/real-scale identification, passed focused Bazel acceptance:
job_T6h7wYQy-9K2bvuSs3YnAi6pxElk2Q5p (57.105 seconds):
[BuildBuddy record](https://app.buildbuddy.io/invocation/d0f55ed8-e23e-4666-a839-8dfb5834dad1).
The checked application was SmoothedDivisorMoment.lean, including its
transitive imports DampedDivisorSeries and DivisorPolynomialMoment.
Its SHA-256 is
3c7d48aec81206d09bccffb6e980bd52bb14e95b50d91c6dde012796d494240e.

Mathematical inputs are elementary divisor counting, geometric series,
Weierstrass majorization, and dominated convergence. The analytic motivation
and remaining contour agenda are recorded in the preceding
[dyadic continuation](THEOREM_CATALOG_INGHAM_DYADIC_L2_20261116.md).
No mathematical novelty is claimed.

The final managed checkpoint must validate the complete Bazel target
//:RiemannResearch before publishing; its terminal record supplies the
exact published commit.
