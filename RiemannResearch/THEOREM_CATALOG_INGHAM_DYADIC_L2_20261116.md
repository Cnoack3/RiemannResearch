# Ingham I1 continuation: dyadic assembly, sharp L2 transfer, and actual phase

Prepared 16 November 2026 (America/Los_Angeles).
Investigation base: `d414397c292ff465a2c3351929b22d942ff848a2`.

## Status

This continuation closes the dyadic-to-global assembly and the critical-line
phase obligations in the preceding fourth-moment catalog. It also proves
finite damped-shell and smoothing-correction estimates and the finite L2
assembly needed to combine remainder pieces.

**I1 is not yet an unconditional Lean theorem.** The canonical consumer still
requires a uniform bound for the *actual* residual on each window `[U,2U]`.
The Mellin representation, complete contour estimates, and infinite-tail
limit passage are not supplied by these new declarations. Z03 is not closed.

No existing theorem statement is weakened. There are no new project axioms
or unfinished proofs.

## Definitions and exact identities

Write
```text
K = 12 * sqrt(2*pi) * exp(1/2)
P(N,w,t) = divisorPolynomial N w t
R(P,Q,t) = zeta(1/2+i*t)^2 - P(t) - Q(t)
phi(t) = chiFE(1/2+i*t)^2.
```

The original exact zeta-square and signed fourth-power residual identities
remain primary; all cross terms are still present there.

| Declaration | Exact result |
| --- | --- |
| `divisorPolynomial_sub` | Coefficient subtraction equals subtraction of the actual polynomials |
| `divisorPolynomial_lower_mask` | Exact zero-extension of the finite head to any larger cutoff |
| `divisorPolynomial_shell_identity` | The upper masked sum equals `P(N,w)-P(L,w)`, for `L<=N` |
| `divisorPolynomial_smoothing_correction_identity` | The correction is precisely the damped head minus the undamped head |
| `integral_dyadic_increment` | The integral primitive increment equals the integral on `[U,2U]` |
| `zetaSquareCriticalPhase_eq_gamma_ratio` | The actual squared phase equals `(conj(G(t))/G(t))^2` |
| `zeta_phase_reflected_divisor_moment` | Multiplying the conjugated polynomial by the actual phase preserves its square moment exactly |

The phase identities reuse the vendored Hardy development's `chiFE_sline`,
`Gfun_ne_zero`, and `hasDerivAt_Gfun`. The critical parameterizations
`1/2 + I*t` and `sline t = 1/2 + t*I` are explicitly identified.

## Unconditional strengthening of the finite arithmetic inputs

All the following estimates are uniform in the indicated finite cutoffs and
intervals. Assume `N>=1`, `H<=T`.

* `weighted_divisor_coefficient_energy_le_mul` and
  `divisorPolynomial_second_moment_le_of_norm_le` allow arbitrary amplitude
  `B`: if `norm(w(n))<=B` on `1<=n<=N`, then the square moment is at most
  `B^2 K (T-H+N) (1+log N)^4`. No separate sign assumption on `B` is needed.
* `divisorPolynomial_smoothing_correction_second_moment_le` gives the
  additional factor `(N/Y)^2` for `w(n)=exp(-n/Y)-1`, for every `Y>0`.
  This improves the unit-weight bound when `N<Y`.
* `damped_divisorPolynomial_shell_second_moment_le` gives the factor
  `exp(-L/Y)^2` for weights `1_{L<n} exp(-n/Y)`. Together with the exact
  shell identity, this bounds every finite damped cutoff difference for
  `L<=N`.

These finite-shell bounds retain the exponential gain. They do **not** claim
that a bound growing with the upper cutoff can be passed directly to infinity.

## L2 assembly and sharper residual transfer

In `Analysis/IntervalL2Triangle.lean`, the reusable namespace is
`intervalIntegral`; the range may be any normed additive commutative group.

* `integral_norm_mul_le_sqrt`: interval Cauchy--Schwarz.
* `sqrt_integral_norm_sq_add_le`: interval Minkowski.
* `sqrt_integral_norm_sq_sum_le`: the finite-sum Minkowski inequality.
* `integral_norm_sq_sum_le_of_bounds`: for continuous pieces `f_i`,
  nonnegative costs `B_i`, and a common nonnegative scale `W`,
  `integral norm(f_i)^2 <= B_i^2 W` implies
  `integral norm(sum f_i)^2 <= (sum B_i)^2 W`.

Zero costs, an empty family, and a degenerate interval are allowed. The
theorem is finite; an infinite family needs an additional convergence proof.

The actual-zeta specialization
`zeta_fourth_moment_le_residual_l2` proves

\[
 \int_H^T|\zeta(1/2+it)|^4\,dt
 \le \left(
 \sqrt{\int_H^T|P|^2}+
 \sqrt{\int_H^T|Q|^2}+
 \sqrt{\int_H^T|R(P,Q)|^2}
 \right)^2.
\]

`zeta_fourth_moment_le_two_cutoffs_residual` permits *independent* cutoffs
`N,M` and coefficient sequences for the two polynomials, retaining their
separate square-root costs.

## Dyadic assembly with no extra logarithm

`Analysis/DyadicIntegralBound.lean` proves
`bound_of_dyadic_linear_weight` for any nonnegative increasing weight
`W` on `[H,infinity)`, and a function `F` increasing there:

\[
 F(2U)-F(U)\le D U W(U),\qquad
 F(2H)\le C H W(H),\qquad 0\le C,\ D\le C
 \quad\Longrightarrow\quad F(T)\le C T W(T)
 \quad(T\ge H).
\]

`integral_bound_of_dyadic_linear_weight` specializes to a continuous
nonnegative integrand, keeping the finite head explicit.

`exists_fourth_moment_bound_of_dyadic` applies this with `W(T)=(log T)^4`.
One explicit constant used by its proof is

\[
 C=D+1+\frac{\int_0^{2H}|\zeta(1/2+it)|^4\,dt}
                         {H(\log H)^4},\qquad H\ge2.
\]

The numerator is finite by continuity and is fixed independently of the
outer height. The logarithmic degree remains four.

## Stronger conditional residual criterion

`zeta_fourth_moment_dyadic_le_of_residual` proves the one-window bound with
the improved constant

\[
 D=\left(2\sqrt{162K}+\sqrt{C_R}\right)^2
\]

when `1<=N,M<=U`, both weight sequences have norm at most one on their
respective finite supports, the continuous phase has norm at most one on
`[U,2U]`, and the actual residual square moment is bounded by
`C_R U (log U)^4`.

`dyadic_residual_l2_constant_le` proves
`(2 sqrt A + sqrt C)^2 <= 3(2A+C)` for `A,C>=0`. Thus the new constant is
never worse than the previous `3(324K+C_R)` after setting `A=162K`.

`exists_fourth_moment_bound_of_dyadic_residual` needs only such residual
bounds on dyadic windows. Both cutoffs, both weight sequences, and the
continuous phase can be chosen afresh for each `U`. No regularity,
coherence, or monotonicity across these choices is assumed. The constant
`C_R` must be independent of `U`.

Finally, `exists_fourth_moment_bound_of_actual_dyadic_residual` fixes the
canonical data
`N=M=floor U`, unit weights, and the actual phase
`zetaSquareCriticalPhase`. The phase is continuous and has norm exactly
one for every real height, including zero. Its only domain-specific input is

\[
 \forall U\ge H:\quad
 \int_U^{2U}|R(P_{\lfloor U\rfloor,1},
       \chi(1/2+i\,\cdot)^2\overline{P_{\lfloor U\rfloor,1}};t)|^2\,dt
 \le C_R U(\log U)^4.
\]

**This is a conditional research reduction, not a proof of that input.**

## Remaining analytic obligations and next check

| Obligation | Status |
| --- | --- |
| Critical-line continuity and unit modulus of the actual squared phase | Proved |
| Finite head smoothing correction | Proved, with an additional amplitude gain |
| Finite exponentially damped shell estimates | Proved |
| Finite L2 assembly of the five remainder pieces | Proved for arbitrary continuous finite families |
| Dyadic windows to global I1 shape, with finite head | Proved |
| Exact smoothed zeta-square representation and its contour shifts | Open |
| Actual damped divisor series and fixed-positive-damping L2 limit passage | Proved for all positive real scales in [the damped-series continuation](THEOREM_CATALOG_DAMPED_DIVISOR_L2_20261116.md) |
| Sharp smoothed moments for positive integer scales | Proved in [the uniform remainder continuation](THEOREM_CATALOG_INGHAM_REMAINDER_PROGRESS_20261116.md) |
| Uniform central off-critical chi bounds on Re s=-1/4 and 3/4 | Proved in [the residue and contour continuation](THEOREM_CATALOG_ZETA_REMAINDER_RESIDUE_20261116.md) |
| Actual moving double-pole coefficient and uniform rapid decay | Proved, including every polynomially weighted dyadic square moment |
| Weighted divisor head/tail moments and complete transformed contour estimates | Open |
| Complete actual residual bound with one height-independent constant | Open |
| Unconditional I1 and remaining Ingham/Z03 obligations | Not closed |

The real-scale convergence and L2 limit passage are proved in
[DampedDivisorSeries.lean](Analysis/DampedDivisorSeries.lean), with a closed-form
tail bound and convergence of moments after subtraction of any fixed continuous
function. The sharp integer-scale block moment is separately proved in
[SmoothedDivisorMoment.lean](Analysis/SmoothedDivisorMoment.lean); the two series
are identified by smoothedDivisorSeries_eq_dampedDivisorSeries.
The next checks are the exact Mellin representation, the weighted divisor
head/tail mean values, and the complete functional-equation contour assembly.
The moving residue and central chi factors are now proved unconditionally;
the original left-line tails have decay to every inverse-power order in
ActualZetaSquareMellinTail.lean.

External reference for the representation strategy:
[Chourasiya--Simonic, Section 5.1](https://arxiv.org/html/2507.15184v2).
The source supports the analytic agenda, not a claim that these remaining
obligations have been formalized.

## Verification evidence

Focused Bazel/BuildBuddy acceptance passed for
`//RiemannResearch/Analysis:ActualZetaFourthMomentDyadic` and its transitive
imports: job `job_Pjtm-qwOvghalinqy-Ouv62QszRqEjHL`,
[log](https://app.buildbuddy.io/invocation/f3f0738b-c60e-4a77-9769-73f87c632739).
The checked application SHA-256 is
`cf122cdbbdf51e6850e7778b4d194b8ff5a04ddc55f3674300ee9472ad107b71`.

Eight explicit axiom guards passed: job `job_eKVwfUf8a2ShZh7ClJ1Kg3M_ZI4Jh51I`,
[log](https://app.buildbuddy.io/invocation/c4af9416-5c85-4a27-bb91-bb1cb943c383).
They require exactly `propext`, `Classical.choice`, and `Quot.sound` for
the dyadic integral assembly, finite L2 sum bound, smoothing correction,
damped shell bound, sharp residual transfer, actual phase norm, canonical
dyadic residual consumer, and comparison of constants.
The guards ignore only message whitespace; theorem assumptions remain
visible and are not discharged by an axiom audit.

The final managed checkpoint must validate the full
`//:RiemannResearch` target before publication. Its terminal job record,
rather than this pre-publication note, records the final commit and any
integration with newer main.
