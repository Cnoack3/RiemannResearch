# Actual zeta analytic providers: checked progress, 5 October 2026

Source base: `e2471e031283ee81b7f87e31b33906402a50aba1`.
This ledger distinguishes exact actual-zeta providers from analytic estimates
that remain Open. All actual zero sums retain analytic multiplicity.

## Established providers

| Provider | Checked declaration or module | Scope |
|---|---|---|
| Euclidean PSD centering | `ContinuousLinearMap.norm_center_le_of_positive` in Analysis/HorizontalEuclideanMoments.lean | Derives the norm bound from actual positive operators using Mathlib's Rayleigh theorem |
| Complete finite moment domination | `weightedCopyGram_domination_identity`, `weightedCopyGram_center_norm_le` | Exact finite rank-one identity; original index set and normalizer retained |
| Actual-zero moments | `ActualZeroPhaseMoments.goodMoment_center_norm_le` and `evenMomentCorrection_summable_and_norm_le` | Every actual zero copy, every integer frequency; discharges the old centered-moment norm premise |
| Actual count normalization | `ActualZeroOrdinate.eventually_count_ge_log`, `eventually_count_pos` in Analysis/ActualZeroCountAsymptotics.lean | Eventually Ncount(0,T) >= T log(T)/(16 pi), with no remaining density, Landau or RH hypothesis |
| Exact symmetric split | `weighted_sum_split`, `good_exact_signed_correction`, `bad_exact_signed_correction` in Analysis/ActualZeroOrdinate.lean | Good means absolute displacement <= delta; bad means > delta; equality-boundary copies stay in good |
| Weighted actual zero contours | `RvM.rectangleIntegral'_mul_logDeriv_completedZeta_eq_zero_sum` and `rectangleIntegral'_mul_logDeriv_riemannZeta_eq_zero_sum`, with both exponential specializations | Exact completed-zeta and direct zeta contours; ordinary analyticity and horizontal boundary conditions explicit |
| Exact finite rational kernels | `ZeroOrdinate.integral_phase_eq_finitePhaseKernel`, `norm_finitePhaseKernel_rational_le`, `finitePhaseKernel_rational_resonance` in Analysis/FiniteOscillatoryKernel.lean | Nonresonance gives norm <=4*n; resonance retains the exact signed value B-A |

The actual count proof instantiates the existing
`RvM.riemannVonMangoldt gammaFacts`, then the existing dyadic lower bound at
T/2, and uses Ncount(T/2,T) <= Ncount(0,T).
The moment norm is the ContinuousLinearMap norm on EuclideanSpace over C,
not an entrywise matrix norm. Empty cutoffs use totalized division.

The checked snippets reported only `propext`, `Classical.choice`,
and `Quot.sound` for all principal declarations. Source-file integration
and the affected import graph are validated by the publication checkpoint.
No domain-specific conclusion is inferred from that foundational axiom list.

## Open analytic and assembly obligations

| Obligation | Status | Existing infrastructure and missing work |
|---|---|---|
| Actual even commutator identity | Open | Actual reflection, symmetric masks and finite moments are proved; still identify the full operator series with H_good-G_good and retain the entire bad contribution |
| Uniform rational Landau estimate | Open | Weighted contour, actual good heights, actual von Mangoldt Dirichlet series and logarithm spacing exist; finite-line interchange and bounds on all contour sides remain |
| Uniform zero density | Open | Ingham/Selberg estimate is established in the literature; no checked actual-zeta provider in this repository |
| Weighted bad-zero tail | Open | Requires the actual density provider and a checked finite layer-cake identity |
| Microscopic ordinate square budget | Open | The known unconditional Fujii/Selberg/Tsang second moment is still a separate marked-tail formalization gap |
| Growing-support spectral assembly | Open | Needs the quantitative providers and the exact actual operator identity above |

### A smaller sufficient rational Landau target

The bootstrap only needs rational frequencies x=n/m, with 1<=m<n<=X.
It can use a fixed contour c=2 instead of the sharper nearest-prime-power
formula. Write lambda_rat(n,m)=vonMangoldt(n/m) if m divides n, and zero
otherwise. A sufficient actual provider, still **Open**, is a uniform bound

    ||landauSum T (log x) + T*lambda_rat(n,m)/(2*pi*sqrt x)||
      <= C*(X^(5/2) + X^(3/2)*log(T+3)^2 + X*log(T+3)).

It would give a normalized matrix remainder at most

    C*(X^(7/2)/(T*log T) + X^(5/2)*log T/T + X^2/T),

which tends to zero when log X=O(sqrt(log T)).
Analysis/ActualZeroLandauContour.lean supplies the direct zeta contour,
so gamma factors can be handled through the left functional equation.
Analysis/FiniteOscillatoryKernel.lean now proves the exact right-line kernel
and its zero-frequency value B-A. For every nonresonant k, the existing
`Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub`, applied to n and m*k,
gives |log(n/m)-log k| >= 1/(2n). The checked kernel norm is <=4n.
The known summability of vonMangoldt(k)/k^2 then controls the right-line
nonresonant sum. The remaining analytic steps are finite-interval series
interchange, horizontal good-height bounds, the left functional equation,
explicit logarithm integration by parts, and transfer to arbitrary T.
The existing digamma Stirling O(t^-2) remainder is absolutely integrable;
a new trigamma theorem is unnecessary for this sufficient target.

Primary source supporting the sharper comparison statement and contour
strategy: Ford--Zaharescu, Lemma 1,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf.
The reduced rational target above is an independently derived sufficient
formalization target, not a quotation of their theorem.

### Density source and stronger paper-level bad budget

Chourasiya--Simonic, Theorem 1 and Corollary 1,
https://arxiv.org/html/2507.15184v2, support the paper-level density input.
The literal Corollary 1 threshold T>=3*10^12 uses the cited finite
computational RH verification. For an eventual provider one can instead
use Theorem 1 on N(sigma,T)-N(sigma,H), keep the actual finite N(H),
and absorb that fixed count eventually. This avoids importing that finite
RH certificate, but still requires the missing analytic proof machinery:
Littlewood's zero-count inequality, Gabriel convexity, mollifier mean
values and the fourth zeta moment. A cited paper is not a Lean provider.

Reflection averaging the complete bad family, followed by the same
centering half-factor, gives the stronger paper-level bound

    beta <= d/(2N) * sum_bad [cosh(|a_rho|*ell)-1]
         <= d/(4N) * sum_bad exp(|a_rho|*ell).

Under B(s)<=400*T*L^3*exp(-4*L*s/3), with
L=log T, ell=log X, A=4*L/3-ell>0 and 0<=delta<=1/2, this yields

    beta <= 100*d*T*L^3/N *
      [(1+ell/A)*exp(-A*delta) - (ell/A)*exp(-A/2)].

This retains the finite upper endpoint and improves the earlier coarse
coefficient by a factor of eight. Exact layer-cake uses the strict bad
count B_>(s); the non-strict paper density count dominates it.
Wolfram checked the exponential integral, the algebraic density exponent
comparison, and (cosh(t)-1)/2 <= exp(|t|)/4. Those computations are
symbolic checks, not Lean proofs of the actual analytic providers.

The RH-strength signed saturation, cofinal arithmetic O(log N) bound,
and bounded-frequency signed marked cancellation remain unproved.
