# Actual zeta analytic providers: checked progress, 5 October 2026

Source base: `9aad406831dd6b017a6cb592e07b22a2389cd4cc`.
This ledger distinguishes exact actual-zeta providers from analytic estimates
that remain Open. All actual zero sums retain analytic multiplicity.

## Established providers

| Provider | Checked declaration or module | Scope |
|---|---|---|
| Euclidean PSD centering | `ContinuousLinearMap.norm_center_le_of_positive` in Analysis/HorizontalEuclideanMoments.lean | Derives the norm bound from actual positive operators using Mathlib's Rayleigh theorem |
| Complete finite moment domination | `weightedCopyGram_domination_identity`, `weightedCopyGram_center_norm_le` | Exact finite rank-one identity; original index set and normalizer retained |
| Actual-zero moments | `ActualZeroPhaseMoments.goodMoment_center_norm_le` and `evenMomentCorrection_summable_and_norm_le` | Every actual zero copy, every integer frequency; discharges the old centered-moment norm premise |
| Sharp actual count normalization | `ActualZeroOrdinate.eventually_count_ge_log_of_lt`, `eventually_count_ge_seven_log` in Analysis/ActualZeroCountAsymptotics.lean | Every lower coefficient c<1/(2 pi), and concretely 7/(16 pi); no density, Landau or RH hypothesis |
| Exact scalar even expansion | `weightedCoshCorrection_hasSum_evenMoments`, `weightedCoshCorrection_eq_tsum_evenMoments` in Analysis/ActualZeroHorizontalExpansion.lean | Actual finite multiplicity sum, arbitrary weights, full convergent series |
| Actual logarithmic diagonal | `logDiagonal_norm_eq` in Analysis/ActualZeroLogDiagonal.lean | Euclidean operator norm exactly log(d)/2 for d>=1; all integer frequencies |
| Complete actual operator identity | `landauGram_sub_phaseGram` in Analysis/ActualZeroPhaseOperators.lean | H-G equals the complete even commutator series plus the entire signed bad correction; no analytic distribution premise |
| Actual correction norm | `norm_landauGram_sub_phaseGram_le`, `badCorrection_norm_le_cosh`, `badCorrection_norm_le_exp` in Analysis/ActualZeroBadPhaseTail.lean and ActualZeroPhaseOperators.lean | Sharp half factor for good and bad cosh corrections; original N retained |
| Exact finite strict-tail layer cake | `badExp_layerCake`, `badCosh_layerCake` in Analysis/ActualZeroTailLayerCake.lean | Both finite endpoints retained, with strict bad cutoff and all multiplicities |
| Actual reflection density bridge | `strictTail_eq_twice_right`, `strictTail_le_twice_inclusive` in Analysis/ActualZeroTailReflection.lean | Strict absolute tail exactly twice the right strict tail; dominated by the paper's inclusive count |
| Actual density-to-operator transfer | `badCorrection_norm_le_of_expTail` in Analysis/ActualZeroBadTailDensity.lean | Complete bad correction bounded by the exact finite density factor; the original normalizer remains, including empty cutoffs |
| Actual finite Gram bootstrap | `phaseGram_norm_sub_one_le`, `phaseGram_isUnit` in Analysis/ActualZeroPhaseBootstrap.lean | Actual moment and operator identity providers discharged; only explicit Landau/bad norm estimates and the scalar gap remain |
| Density-to-tail transfer | `badCoshSum_le_of_expTail_closed` in Analysis/ActualZeroTailDensityTransfer.lean | Exact closed finite-interval factor from an explicit actual strict-tail bound; actual density input remains Open |
| Full integer arithmetic operator | `primePowerMainOperator_norm_le`, `primePowerMainOperator_norm_ge` in Analysis/PrimePowerCovarianceEuclideanNorm.lean | log(d)-2 <= norm <= log(d)+log(4)+4; complete composite-frequency interactions, no analytic hypothesis |
| Exact actual right contour | `integral_centered_two_neg_logDeriv_eq_kernel_tsum`, `rightLandauLine_rational_eq_split`, `norm_rightLandauLine_rational_add_resonance_le` in Analysis/ActualRationalLandauRightLine.lean | Actual zeta Dirichlet series, finite-interval interchange, exact integer resonance and uniform nonresonant bound |
| Exact symmetric split | `weighted_sum_split`, `good_exact_signed_correction`, `bad_exact_signed_correction` in Analysis/ActualZeroOrdinate.lean | Good means absolute displacement <= delta; bad means > delta; equality-boundary copies stay in good |
| Weighted actual zero contours | `RvM.rectangleIntegral'_mul_logDeriv_completedZeta_eq_zero_sum` and `rectangleIntegral'_mul_logDeriv_riemannZeta_eq_zero_sum`, with both exponential specializations | Exact completed-zeta and direct zeta contours; ordinary analyticity and horizontal boundary conditions explicit |
| Exact finite rational kernels | `ZeroOrdinate.integral_phase_eq_finitePhaseKernel`, `norm_finitePhaseKernel_rational_le`, `finitePhaseKernel_rational_resonance` in Analysis/FiniteOscillatoryKernel.lean | Nonresonance gives norm <=4*n; resonance retains the exact signed value B-A |

The sharp actual count proof instantiates the existing
`RvM.riemannVonMangoldt gammaFacts`, proves every dyadic lower coefficient
below 1/(2 pi), and accumulates finitely many disjoint geometric windows.
The concrete coefficient 7/(16 pi) is seven times the former 1/(16 pi).
The moment norm is the ContinuousLinearMap norm on EuclideanSpace over C,
not an entrywise matrix norm. Empty cutoffs use totalized division.

The final coherent source check succeeded in 10.447 seconds. All 21 principal
axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`. Source-file integration
and the affected import graph are validated by the publication checkpoint.
No domain-specific conclusion is inferred from that foundational axiom list.

## Open analytic and assembly obligations

| Obligation | Status | Existing infrastructure and missing work |
|---|---|---|
| Actual even commutator identity | Established | `landauGram_sub_phaseGram` supplies the complete actual operator series with the signed bad term retained |
| Uniform rational Landau estimate | Open | Weighted contour, actual good heights, actual von Mangoldt Dirichlet series and logarithm spacing exist; the exact right-line interchange and bound are now proved; the other contour sides and arbitrary-height transfer remain |
| Uniform zero density | Open | Ingham/Selberg estimate is established in the literature; no checked actual-zeta provider in this repository |
| Weighted bad-zero tail | Conditional research reduction | Exact strict layer cake, reflection bridge and finite density-to-tail transfer are checked; the substantive actual zero-density provider is Open |
| Microscopic ordinate square budget | Open | The known unconditional Fujii/Selberg/Tsang second moment is still a separate marked-tail formalization gap |
| Growing-support spectral assembly | Open | The exact actual operator identity is proved; still needs quantitative Landau/density inputs and asymptotic assembly |

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
nonresonant sum. The right-line finite-interval series interchange and rational split are now
proved in Analysis/ActualRationalLandauRightLine.lean. The remaining analytic
steps are horizontal good-height bounds, the left functional equation,
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

The checked actual complete bad correction, followed by positive moment
centering, gives the unconditional finite bound

    beta <= d/(2N) * sum_bad [cosh(|a_rho|*ell)-1]
         <= d/(4N) * sum_bad exp(|a_rho|*ell).

The density specialization remains conditional. Under the explicit actual
strict-tail premise B_>(s)<=400*T*L^3*exp(-4*L*s/3), with
L=log T, ell=log X, A=4*L/3-ell>0 and 0<=delta<=1/2, this yields

    beta <= 100*d*T*L^3/N *
      [(1+ell/A)*exp(-A*delta) - (ell/A)*exp(-A/2)].

This retains the finite upper endpoint. The sharp count family lets the
coarse coefficient after normalization approach 200*pi instead of 1600*pi.
The bound still depends on the unproved actual density premise. Exact layer-cake uses the strict bad
count B_>(s); the non-strict paper density count dominates it.
Wolfram checked the exponential integral, the algebraic density exponent
comparison, and (cosh(t)-1)/2 <= exp(|t|)/4. Those computations are
symbolic checks, not Lean proofs of the actual analytic providers.

The RH-strength signed saturation, decisive screened-Pareto cofinal
arithmetic O(log N) bound, and bounded-frequency signed marked cancellation
remain unproved. The checked full-integer prime-power matrix norm is a
different arithmetic object.

### Sharper sufficient Landau target and density scope

Ford--Zaharescu Lemma 1 also supports the literature-derived rational target
for 1<=m<n<=X, x=n/m:

    ||landauSum T (log x) + T*lambda_rat(n,m)/(2*pi*sqrt x)||
      <= C*[X*log(2X) + sqrt(X)*log(2XT)^2 + X*log(2T)].

The nearest prime power k<=2x and rational logarithm spacing control the
nonresonant main term. This sharper full-contour estimate is not a checked
Lean declaration. The fixed c=2 right-line formula is exact, but alone does
not prove this error; the sharper contour chooses a line depending on x.
The checked full-integer main operator has norm log(d)+O(1), with leading
constant 1, so its normalized main term is O(log(d)/log(T)).

Only a uniform density estimate on 0<=s<=1/32 is necessary for the
sqrt(log T) support scale. Split the exact layer cake at b=1/32 and use
monotonicity for the farther tail. Under the paper input that farther piece
is O(exp(-log(T)/24+O(sqrt(log T)))). Table 1's first interval has constants
5.069, 9.461 and 167.8; after absorbing additive errors the leading reflected
coefficient approaches 10.138 rather than 400. This is an informal
strengthening of the missing analytic target, not a new density proof.

For q>ell>=0 the checked density-to-cosh-tail transfer retains the exact
finite factor

    F=(cosh(ell*delta)-1)*exp(-q*delta)
      + (ell/2)*[(exp(-(q-ell)*delta)-exp(-(q-ell)/2))/(q-ell)
                -(exp(-(q+ell)*delta)-exp(-(q+ell)/2))/(q+ell)].

The tail is at most K*F under the explicit strict-tail premise
B_>(t)<=K*exp(-q*t). Wolfram independently checked its equivalent expanded
closed form. Wolfram algebra and literature statements are kept separate
from the Lean kernel verification of each provider.
