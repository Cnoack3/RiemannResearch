# Prime-logarithm phase coding: PDF audit and formalization

Date: 2026-11-15.
Initial inspection checkout: f1df51cb44c3b28bd0087864c316c8915271cef4.
Publication integration base: 0b6554aad967f5135202b8b65d0a98f33e64a57c.

## Source documents and scope

1. [Empirical Phase Coding of Zeta Zero Ordinates by Prime Logarithm Moduli](https://drive.google.com/file/d/1quuQlmUyGYSn5E8FmkfbdOeg9fIfI_KR/view), 11 pages.
2. [Modular Phase Reconstruction of Zeta Zeros from Pole Lattices](https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view), 10 pages.

Both PDFs were read, with the mathematical target pages also rendered.
Their numerical tables are reported experiments, not certified input data:
the linked ZIP/CSV bundles were not supplied or independently reproduced.
Independent Wolfram checks below are numerical cross-checks, not Lean proofs.

## What already existed

- Analysis/PrimePhaseTorus.lean:
  two_prime_phase_injective, phase_family_injective,
  irrational_prime_log_ratio, finite_prime_phase_character.
- RH/PrimePhaseCRT.lean:
  modularMap_injective, modularMap_exact, intPrimeLogRelation.
- Analysis/ActualPrimeTorusFMZContinuous.lean:
  tendsto_centered_continuous_div_poisson_of_selberg,
  with the explicit premise UniformSelbergDensity (1/4).
- Analysis/ActualInfinitePrimeTorus.lean:
  existsUnique_actual_orbit_limit, with the same density premise.

Thus the exact ordinate injection was already formalized. It does not
recover a zero's real part or multiplicity from its ordinate phases.

## New unconditional decoding theorems

Namespace RiemannResearch.Analysis.PhaseDecoding;
module Analysis/PhaseDecoding.lean.

| Declaration | Exact content |
|---|---|
| same_bin_fract_close | Equal M-bin labels give fractional-coordinate error < 1/M. |
| same_bin_circle_close | The same estimate holds in the actual circle metric. |
| finite_phase_collision | More than M^d candidates force two vectors closer than 1/M in every coordinate. |
| separated_card_le | Coordinatewise separation at scale 1/M forces N <= M^d. |
| arbitrarily_far_collisions | For every finite real-valued phase family, resolution M and R>0, two nonnegative inputs at least R apart have all circular errors <1/M. |
| prime_phases_arbitrarily_far_close | Specializes to the actual prime phases, with arbitrary epsilon>0 and arbitrary R>0. Primality is not needed for this obstruction. |
| unique_nearest_of_separation | A nearest candidate is unique if twice the noise radius is strictly below every competing codeword distance. |
| compact_inverse_modulus | Every continuous injective map on a compact metric space has a uniform inverse modulus. |
| two_prime_compact_stability | Two distinct prime phases stably recover an ordinate on any specified compact set. The modulus is existential, not an effective Baker bound. |
| one_phase_local_injective | A nonzero linear phase is injective between inputs separated by less than one period. |
| one_prime_local_injective | One base p>1 suffices if the input separation is <2*pi/log(p). |
| one_prime_seed_unique | One prime and a common height seed identify at most one ordinate within pi/log(p) of that seed. |
| anchor_round_recovers | The nearest-integer anchor floor(H/L-u+1/2) exactly recovers the integer lift under the strict half-period seed bound. |
| noisy_anchor_error_identity | The signed physical reconstruction error is exactly the period times the phase error. |
| noisy_anchor_reconstruction | Seed error + L*abs(phase error) < L/2 certifies the actual rounding decoder and its exact signed error. |

Distances here use the unit-circle metric and the product sup metric.
The PDF's Euclidean torus statistics require the appropriate norm conversion.
The distant-collision theorem concerns arbitrary real inputs, not actual
zero ordinates; it must not be mislabeled as a theorem about close zero pairs.

The deterministic N<=M^d bound is a necessary capacity condition. It does
not establish the heuristic random-pair threshold involving N^2(2*eta)^d,
nor is it a sufficient decoding condition.

## New complex reconstruction and the exact RH boundary

Namespace RiemannResearch.Analysis.PrimeLogProjection;
module Analysis/PrimeLogProjection.lean.

Define projection(p,z) = exp(-log(p)*z), so its modulus is
exp(-log(p)*Re(z)).

- norm_projection and log_norm_projection retain the exact radius identity.
- re_from_log_radius reconstructs Re(z) for every integer base p>1.
- norm_projection_eq_iff identifies any prescribed vertical line Re(z)=b.
- log_relative_radius retains the signed radial discrepancy.
- horizontal_error_eq gives the exact horizontal error from the logarithmic
  relative radial error.
- two_prime_projection_injective proves injectivity on all of C, for two
  distinct primes, without RH.

RH/PrimeLogProjectionCriterion.lean proves
RiemannResearch.RH.riemannHypothesis_iff_log_projection_radius:
for any integer p>1, Mathlib RH is equivalent to every open-strip zeta zero
having projected modulus exp(-log(p)/2).
This identifies the missing horizontal condition; it does not establish it.

No theorem here asserts a globally meromorphic infinite local object whose
isolated poles are all projected zeros. The PDFs themselves acknowledge
that this stronger analytic construction is unproved.

## Fixed-prime window results (updated 2026-11-20)

Namespace RiemannResearch.Analysis.PrimePhaseWindows;
module Analysis/PrimePhaseWindows.lean.

Let S_f(T) be the actual multiplicity-weighted phase sum, N(T) the actual
zero count, I_f its Haar integral, and J_f the signed FMZ correction.
`ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson` gives
(S_f(T)-N(T)*I_f)/T -> J_f by fractional Wiener interpolation.

- centered_scaled_window_limit is a general unconditional transfer lemma:
  [S_f(rT)-S_f(T)-(N(rT)-N(T))*I_f]/T -> (r-1)*J_f for every fixed r>0.
- `scaled_window_signed_limit` specializes this to actual zeros and every
  fixed finite prime set. For 0<r<1 the boundary difference is oriented.
- eventually_dyadic_count_ge_log and tendsto_height_div_dyadic_count use
  the already proved actual Riemann-von Mangoldt theorem, unconditionally.
- `dyadic_equidistribution` proves
  [S_f(2T)-S_f(T)] / N(T,2T] -> I_f.

For a fixed prime `p`, `dyadicPrimeCosineMean p T` averages `cos(log p * γ)`
over this window with analytic multiplicities. The dyadic count divided by
`T * log T` tends to `1 / (2π)` by `Assembly.tendsto_dyadic_count_div_height_log`.
The theorem `tendsto_log_mul_dyadicPrimeCosineMean` gives the signed limit
`(log T) * dyadicPrimeCosineMean p T → -log p / √p`. At `p = 2` this is
`-log 2 / √2`. The theorem `dyadicPrimeCosineMean_isBigO_log_rpow_iff`
shows that the raw mean is `O((log T)^(-α))` exactly when `α ≤ 1`.

The two general window theorems require Fourier decay
|f_hat(k)| <= C*(1+||k||)^(-B), C>=0, B>card(P)+1.
The signed correction is `haarIntegral (f * primeDensity P)`. Both limits
are unconditional in this class and count zeros with analytic multiplicity.

The measure convention is (T,2T], matching the actual count API.
The statement does not concern fixed-length or microscopic windows.

## Literature correction

Equidistribution is not an uncharted conjecture. Hlawka's unconditional
one-dimensional theorem, applied to nonzero integer combinations of the
prime logarithms and Weyl's criterion, gives the fixed finite-prime Haar law.
The dyadic version follows by subtracting cumulative sums and using
Riemann-von Mangoldt. The Lean declarations above use the project's signed
FMZ limit on the stated Fourier class.

Primary references:
- Ford and Zaharescu, On the distribution of imaginary parts of zeros of
  the Riemann zeta function:
  https://ford126.web.illinois.edu/wwwpapers/fz.pdf
- Ford, Meng and Zaharescu, Simultaneous distribution of the fractional parts
  of Riemann zeta zeros, Corollary 1.1:
  https://arxiv.org/abs/1511.06814

The first-order flattening retains a nontrivial signed lower-order bias;
it should not be interpreted as independence at growing resolution.

## Wolfram checks

- pi/log(2) = 4.53236014182719380962768294572.
  The first PDF reports a maximum low-table seed error 3.7131,
  leaving a reported margin about 0.8192601418.
  If that seed bound is certified, the one-prime theorem already explains
  exact indexed reconstruction; the second coordinate is not needed for
  uniqueness in that narrow interval.
- With t = 2*pi*15601/log(2) approximately 141418.7011452921,
  the p=2 phase is exactly zero and the p=3 phase is within
  approximately 0.00002624924241314 of zero, because
  15601*log(3)/log(2)-24727 has that absolute value.
  This is an illustrative near-return of the real phase flow, not a zero.
- For the first 30 Wolfram ZetaZero ordinates and primes {2,3,5},
  the numerical minimum circular sup distance is approximately
  0.11457881987534. This is not a certified minimum for a zero table.

## Unconditional growing-primorial FMZ

In [ActualPrimeTorusFMZPrimorial](Analysis/ActualPrimeTorusFMZPrimorial.lean),
set X(T) = (log T)^(1/3) and take all primes at most X(T). The coefficient-one
character with every exponent equal to one has squared weight
(1 + sum_{p <= X(T)} log p)^2. The elementary bound (1 + X(T) log X(T))^2
gives the rate (log log T)^4 / (log T)^(1/3).

- `eventually_primorial_boundedMode_FMZ` gives that rate uniformly for all
  modes with exponents in {-1, 0, 1}, keeping Haar centering and the signed
  prime-density correction.
- `primorialCharacter_sample_div_isBigO` and
  `tendsto_primorialCharacter_sample_div` give the rate and zero limit for
  the actual multiplicity-weighted ordinate sum divided by T. Both Haar
  coefficients vanish once the cutoff contains 2 and 3.

The uniform bound covers the phase products indexed by pairs of squarefree
divisors. The existing CRT code still needs a relative discrepancy estimate
for the joint half-open cells at their shrinking Haar mass. The carry criteria
use the signed residual pairing in the complete Q inner product.

## Remaining research agenda

1. Prove `UniformSelbergDensity (1/4)` for the separate one-log quantitative
   remainder in `eventually_continuous_remainder_bound_of_selberg`.
2. Prove an effective two-prime inverse modulus on a prescribed height
   interval using explicit lower bounds for integer logarithmic forms.
   The compactness result gives existence, not a practical precision budget.
3. Certify the actual zero-table phase vectors and the height-seed bounds,
   then apply the finite separation and nearest-neighbor certificates.
4. State the nearest-neighbor conjecture precisely: minimum, typical, and
   median distances have different scales even for independent random points.
   Fixed-mode equidistribution does not imply shrinking-scale separation.
5. Derive phase and radial data from independently controlled prime-side
   objects. Re-encoding already known ordinates does not locate new zeros.
6. For RH, prove the radius condition (or an independently proved equivalent
   analytic estimate). Exact phase reconstruction and Haar equidistribution
   alone do not constrain Re(rho).

## 2026-11-15 verification record

The focused Bazel/BuildBuddy check succeeded for all four new modules and
transitive imports: job_kh4GAtVjAIFg5ASQLvx9LjwxRoI2yt5d, server-reported
verification duration 54.316 seconds (not total session or polling time).
BuildBuddy invocation: 84290bdf-220f-4402-a56e-1ab20bcc026d.

That run checked the original window declarations with their Selberg premise.
The publication response records the full-project checkpoint and commit.

Publication recovery: the first full-project checkpoint reached integration
and retained commit f3dc3894f8a39fe7301a0970b6c7e5ef02e44a5a, but concurrent
imports at the top of RiemannResearch.lean caused a cherry-pick conflict.
That commit was not published. A fresh checkout preserves the newer main
commits; identical theorem files are exported beside PrimePhaseTorus and
are submitted again to the managed full-project publication gate.

## Consecutive ordinates

The [prime-coordinate determinants and signed Fourier sums](THEOREM_CATALOG_PRIME_ORDINATE_MINORS_20261121.md) use these coordinates on successive copies of zeta zeros.
