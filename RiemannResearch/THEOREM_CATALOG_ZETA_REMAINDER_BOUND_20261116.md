# Uniform actual zeta remainder and unconditional Ingham I1

Prepared 16 November 2026 (UTC).
Investigation base: `b9d28e2775cfe2f846798fb307b9460e99f6b59f`.
Integration base: `c43f21adf9f58d600f23baa8a074cf771440e82a`; concurrent
research modules and their aggregate imports are preserved.

## Status

The actual uniform zeta-square residual bound and the actual zeta fourth-moment
bound (Ingham I1) are proved without a supplied analytic provider. The construction
uses the repository's existing moving-residue, smoothed-divisor, Gamma, actual
zeta-growth, and finite mean-value results. The complete Mellin inversion,
contour shifts, ordinary infinite-series split, and remaining weighted moments
are now supplied.

The global theorem is

```text
exists_actual_zeta_fourth_moment_bound:
  ∃ C > 0, ∀ T ≥ 2,
    ∫ t in 0..T, ‖riemannZeta (1/2 + I*t)‖^4 ≤ C*T*(log T)^4.
```

This closes I1; it does not assert RH or close the separate remaining Z03
zero-density, cancellation, or other analytic obligations.

## Exact identity and contour normalization

Let

```text
P_N(t) = ∑_{1≤n≤N} d(n)/sqrt(n) * exp(-I*t*log n),
φ(t)   = chiFE(1/2 + I*t)^2,
R_N(t) = zeta(1/2 + I*t)^2 - P_N(t) - φ(t)*conj(P_N(t)).
```

For every natural N, every positive real smoothing scale Y, every real t,
and every 0 < b < 1/2, `zetaSquareResidual_eq_mellin_remainder` proves

```text
R_N(t) = (dampedDivisorSeries Y t - P_N(t))
         - zetaSquareMovingResidue Y t
         - (1/(2*pi)) * ∫_{v∈R} zetaSquareFiniteHeadKernel N Y t (b+I*v)
         - zetaSquareInfiniteTailIntegral N Y t.
```

All signs, the moving double-pole residue, and the full vertical integrals are
retained. The left contour is Re(z) = -3/4. The right finite-head contour may
be any 0 < b < 1/2; the quantitative moment uses b = 1/4. The functional
equation on Re(s) = -1/4 includes its real-axis point. Absolute integrability
justifies each integral split and limit; no formal integral of an unproved
integrable function substitutes for an analytic identity.

## Uniform contour estimate

`exists_zetaSquareResidual_comparable_cutoff_bound` establishes one C ≥ 0,
independent of N and U, with

```text
∫ t in U..2*U, ‖R_N(t)‖^2 ≤ C*U*(log U)^4
  for N > 0, U ≥ 2, N ≤ U ≤ 2*N.
```

Thus every comparable integer cutoff is allowed, not only N = floor(U).
`exists_actual_zetaSquareResidual_dyadic_bound` supplies the exact canonical
provider required by the previously conditional dyadic-to-global consumer.
The fourth-moment theorem follows from this provider; the proof does not
assume the fourth moment in order to establish this contour estimate.

## Stronger final uniformity

After I1 has been established by the contour proof, it gives the stronger
`exists_actual_uniform_two_cutoff_residual_bound`: one positive constant C
works for every U ≥ 2, every independent pair of positive integers N,M ≤ U,
every pair of complex coefficient weights u,v with norm at most one on their
respective finite supports, and every continuous phase φ with norm at most
one on [U,2U]:

```text
∫ t in U..2*U,
  ‖zeta(1/2+I*t)^2 - divisorPolynomial N u t
    - φ(t)*conj(divisorPolynomial M v t)‖^2
  ≤ C*U*(log U)^4.
```

There is no lower-cutoff comparability assumption. The two cutoffs, the
coefficients, and the phase may vary independently from window to window;
the constant is independent of all these choices. The theorem
`exists_actual_zetaSquareResidual_uniform_cutoff_bound` specializes to the
actual functional-equation phase and unit weights, for every 1 ≤ N ≤ U.

The exact signed norm-square identity and the sharper square-root L2
triangle transfer are retained in `ActualZetaResidualFlexibility`. Its
conditional fourth-moment transfer is supplied with the proved actual I1
provider in `ActualZetaResidualFlexibilityBound`. The dependency is acyclic:
comparable-cutoff contour estimate → I1 → arbitrary-cutoff strengthening.

## Complete proof chain

| Module | New proved responsibility |
| --- | --- |
| `DivisorLSeries` | Absolute divisor L-series convergence and ζ(s)^2 identity for Re(s) > 1 |
| `ZetaSquareMellinRepresentation` | Actual damped-series Mellin inversion for every Y > 0 and right line c > 1/2 |
| `ActualZetaSquareMellinShift` | Exact actual zeta-square contour shift, actual strip decay, and all residues |
| `ActualZetaSquareFiniteHeadShift` | Finite-head contour shift for every -1 < a < 0 < b < 1/2 |
| `WeightedDivisorMoment` | Quarter-weight finite-head and five-quarter infinite-tail moments on arbitrary translated intervals |
| `ZetaSquareMellinWeights` | Uniform translated chi bounds valid at every height, including real-axis crossings |
| `MellinGammaEnvelope` | Integrability of the full quadratic Gamma envelope |
| `WeightedIntegralMeanSquare` | Weighted Cauchy–Schwarz/Fubini transfer with explicit integrability conclusions |
| `ActualZetaSquareRightHeadMoment` | Full right-head integral moment, uniformly for N ≤ U and 0 < Y ≤ U |
| `ZetaSquareInfiniteTailKernel` | Actual tail kernel and joint continuity for every natural N and positive Y |
| `ZetaSquareInfiniteTailMoment` | Full left-tail integral moment at Y = N for U ≤ 2N, with no N ≤ U requirement |
| `ActualZetaSquareRemainderIdentity` | Exact residual identity and ordinary-series head/tail splitting |
| `SmoothedDivisorDyadicMoment` | Actual smoothing-defect moment on the required dyadic interval |
| `ActualZetaSquareResidualBound` | Unconditional comparable-cutoff bound, floor-cutoff provider, and I1 |
| `ActualZetaResidualFlexibility` | Exact signed residual identity, L2 transfer, and conditional independent-cutoff bound |
| `ActualZetaResidualFlexibilityBound` | Unconditional arbitrary independent cutoffs, bounded weights, and bounded phase |

Every name in the module column denotes a file under `Analysis/`.

The translated arithmetic moments hold on arbitrary intervals H ≤ T. In
particular, the finite head has bound

```text
K*(T-H+N)*N^(1/2)*(1+log N)^4,
```

and the ordinary infinite tail has bound

```text
K_tail*(T-H+16*N)*N^(-3/2)*(1+log N)^4.
```

The tail is partitioned into geometric blocks and recombined by a proved
L2 argument. The actual contour moments integrate over the whole vertical
line against an integrable Gamma envelope. This removes any need for an
unproved central/far-region transition or a growing-tail interchange.

## Downstream actual mollifier improvement

The existing unconditional I2 bound and the newly proved I1 give

```text
InghamMollifier.exists_actual_critical_error_moment_log_bound:
  ∃ C > 0, ∀ T ≥ 2, ∀ X ∈ N, 1 ≤ X ≤ T,
    ∫ t in 0..T,
      ‖zeta(1/2+I*t)*mollifier X (1/2+I*t)-1‖^(4/3)
      ≤ C*T*(log T)^2.
```

The exponent two on the logarithm is the result of combining the fourth
moment's four logarithms with the actual mollifier second moment's single
logarithm via Hölder. It is uniform in the actual finite Möbius cutoff X,
including X = 1. The version with `(1+log T)^2` is also provided.
`ActualInghamMixedMoment` retains the reusable conditional transfer;
`ActualInghamMixedMomentBound` supplies its unconditional actual provider.

## Provenance and verification

The contour organization follows Chourasiya–Simonič, arXiv:2507.15184v2,
Section 5.1: <https://arxiv.org/html/2507.15184v2>. This citation supports the
proof strategy, not a claim of mathematical novelty. Exact actual-function
bridges, domain extensions, and integration with the repository are part
of this formalization.

Important focused checks of the component development:

| Scope | Terminal successful Bazel job |
| --- | --- |
| Ordinary divisor series and translated weighted moments, seven axiom guards | `job_9YHIEeWzNKWLC8UDxC0k2aqLLyBQelUg` |
| Exact Mellin representation and its foundation audit | `job_EdPRuuvsbAZw-v9Zn_VKeYdoyHL6cF7M` |
| Exact actual residual identity, five axiom guards | `job_YM6UOo-yTFA8O7gpw7lopx9rIAT42vq4` |
| Right-head moment and its axiom audit | `job_UMD3WwdZIbe5-fuLDxK88eCuqAtAP5Yc` |
| Full infinite-tail moment and joint continuity, two axiom guards | `job_FbXEd6hCGfU3FzLM_PzlLoIZ6nVPst-9` |
| Integrated unconditional residual, I1, and mixed-moment endpoints, three axiom guards | `job_ms-VBwEuypylWTt3PbXGOS0GZkZfXY47` |
| Final strengthened endpoints and four axiom guards after direct-import cleanup | `job_5M5-DcXrONPOy03JWkeH-IJOlCRx9Mcl` |

The final managed checkpoint audits the complete source delta and validates
`//:RiemannResearch` with Bazel/BuildBuddy before committing and pushing.
Its retained job record identifies the exact published commit and full-project
validation outcome. Focused checks alone are not the publication gate.

No new project axioms or unfinished proofs are introduced. Exact foundation
audits use only `propext`, `Classical.choice`, and `Quot.sound`; hypotheses are
also inspected in the actual public theorem types.
