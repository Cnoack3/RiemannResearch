# Uniform actual remainder: historical progress and current I1 closure

Prepared 16 November 2026, America/Los_Angeles.
Investigation base: d414397c292ff465a2c3351929b22d942ff848a2.
The user approved committing and publishing these additions on 16 November 2026.
The managed checkpoint records final validation, integration, and publication.

## Current status: I1 is closed

The open I1 entries in this note describe its original checkpoint and are
superseded by commit
[`8885be09052bffe132cf1a52eeb115065c88e6de`](https://github.com/Cnoack3/RiemannResearch/commit/8885be09052bffe132cf1a52eeb115065c88e6de).
The [completed remainder catalog](THEOREM_CATALOG_ZETA_REMAINDER_BOUND_20261116.md)
records the full proof chain. In namespace `RiemannResearch.Analysis`,
[ActualZetaSquareResidualBound.lean](Analysis/ActualZetaSquareResidualBound.lean)
now supplies:

- `exists_zetaSquareResidual_comparable_cutoff_bound`: one constant controls
  the complete actual residual for all `U >= 2` and positive integer cutoffs
  `N <= U <= 2*N`.
- `exists_actual_zetaSquareResidual_dyadic_bound`: the exact canonical
  `N = floor(U)` provider, with bound `C*U*(log U)^4`.
- `exists_actual_zeta_fourth_moment_bound`: the unconditional actual I1
  estimate on `[0,T]`, uniformly for every `T >= 2`.

The complete smoothing defect, moving residue, right finite-head integral,
and left infinite-tail integral are retained in the exact identity. Their
proved moments give the residual bound before I1 is invoked; this is not a
reformulation assuming the desired fourth moment. None of these three public
theorems has a supplied analytic, growth, contour, or residual premise.

A fresh Bazel/BuildBuddy audit at repository revision
`d6c2e61ea06de4f6d75c142a86dab8fbcb895a79` passed on 16 November 2026:
`job_6EurI1MJOugH9WxBX49K5_l49i5Sw2Kt`,
[verification log](https://app.buildbuddy.io/invocation/b147f193-3cf6-4872-8948-d3e13a1aedd7).
It elaborated the exact canonical residual and I1 statements and enforced
three axiom-output guards: only `propext`, `Classical.choice`, and `Quot.sound`.
Its scope was an ephemeral audit snippet and its transitive imports, not a
new whole-project checkpoint. Server verification took 53.508 seconds;
workspace setup and polling are separate. This status correction changes
documentation only and does not assert closure of the separate Z03 work.

## Original checkpoint conclusion (historical)

The complete uniform actual-zeta remainder bound was **not proved by this
original checkpoint**. Two unconditional contributions were established:

1. The ordinary infinite exponentially smoothed divisor series, and its
   difference from the unsmoothed finite divisor polynomial, have uniform
   square-moment bounds with the fourth logarithmic power.
2. The actual zeta-square Mellin kernel on Re z = -3/4 has arbitrary-order
   far-tail decay and integrable outward tails bounded uniformly in the
   outer height and the real smoothing scale.

Neither result assumes I1, RH, a zeta-moment estimate, or an unproved analytic
growth provider. They did not discharge the complete residual hypothesis in
ActualZetaFourthMomentReduction.lean at that checkpoint. I1 was closed by
the later provider identified above; this audit does not close Z03.

## New modules

| File | Responsibility |
| --- | --- |
| Analysis/GeometricL2Series.lean | Finite weighted Cauchy inequality, geometric series with polynomial factors, and justified L2 infinite summation |
| Analysis/SmoothedDivisorMoment.lean | Actual coefficients, exact block partition, absolute convergence, uniform infinite-series moment, smoothing-defect moment |
| Analysis/ActualZetaSquareMellinTail.lean | Actual zeta growth on fixed vertical lines, actual Mellin kernel, uniform power decay, integrability and bounds for both outward far tails |
| ../RiemannResearch.lean | Exports all three modules |

## The full infinite smoothed series

Write

```text
K = 12 sqrt(2 pi) exp(1/2),
Q = sum_{j>=0} (j+2)^5 (9/16)^j,
Cs = 2 K Q,
P_N(t) = sum_{1<=n<=N} d(n) n^(-1/2-it),
S_N(t) = sum_{n>=1} d(n) n^(-1/2-it) exp(-n/N),
D_N(t) = S_N(t) - P_N(t).
```

Here N is a **positive integer**. Q is an explicitly specified convergent
positive numerical series; this continuation does not claim a kernel-checked
decimal evaluation of it. K and Cs are independent of N, the interval
location, and all truncations.

For every real H <= T with T-H <= N:

```text
integral_H^T |S_N(t)|^2 dt <= Cs N (1+log N)^4,
integral_H^T |D_N(t)|^2 dt <= (2 Cs + 4 K) N (1+log N)^4.
```

The public declarations in RiemannResearch.Analysis are:

- smoothedDivisorSeries_eq_tsum_blocks
- smoothedDivisorSeries_second_moment_le
- divisorSmoothingDefect_second_moment_le

The exact finite partition is sum_dampedDivisorBlock_eq; the exact identity
S_N = P_N + D_N is smoothedDivisorSeries_eq_polynomial_add_defect.
No infinite limit is justified merely by a cutoff-dependent finite estimate.

### Why the logarithmic power is preserved

Block j contains jN < n <= (j+1)N. Its coefficient damping is at most
exp(-j) <= 2^(-j), so its moment is bounded by

```text
K N (1+log N)^4 (j+2)^5 4^(-j).
```

A weighted Cauchy inequality with factors (2/3)^j and (3/2)^j bounds the
square of a finite block sum by twice the sum of (9/4)^j times the individual
squares. The resulting numerical series has ratio 9/16 and a fixed
polynomial factor. There is no factor counting the blocks.

The ordinary divisor series is absolutely convergent at every real t.
The formal proof uses d(n) <= n and exponential decay. Exact consecutive
interval sums identify its limit with the block sum. A summable global norm
majorant supplies dominated convergence for the squared partial sums.
The code proves continuity of S_N as well as the asserted moment bound.

## Actual zeta-square contour tails

Define the actual kernel, without replacing zeta by a model:

```text
F(Y,t,z) = Gamma(z) Y^z zeta(1/2+it+z)^2.
```

exists_riemannZeta_vertical_quadratic_bound proves that, for each fixed
sigma > -1 with sigma != 1, a constant C_sigma > 0 satisfies

```text
|zeta(sigma+iv)| <= C_sigma (1+|v|)^2  for every real v.
```

It reuses the actual Hurwitz Euler--Maclaurin growth theorem and controls
the remaining compact range by continuity. It is deliberately a coarse
pointwise estimate; it does not imply I1 by itself.

For every natural m, exists_zetaSquareMellinKernel_left_far_bound proves
that a constant B_m >= 0 exists such that

```text
|F(Y,t,-3/4+iv)| |v|^m <= B_m
```

whenever Y >= 1, |v| >= 1, and |t| <= 4|v|. The quantifier for B_m precedes
Y, t, and v.

The proof applies the Gamma strip theorem with damping **one**, at order
m+4. It retains Y^(-3/4) <= 1 explicitly. Thus the Gamma constant does not
depend on Y. The inequality 1+|t+v| <= 6|v| supplies the fourth-power cost
1296; a valid constant is 1296 G_(m+4) Z^2, where G_(m+4) and Z are fixed
Gamma and vertical-zeta constants.

exists_zetaSquareMellinKernel_left_tail_integral_bound further proves that
one B >= 0 works for all real Y,t,U,tau with

```text
Y >= 1, U >= 2, |t| <= 2U, |tau| = 1:
```

each function v -> F(Y,t,-3/4+i tau v) is integrable on (U/2,infinity), and

```text
|integral_(U/2)^infinity F(Y,t,-3/4+i tau v) dv| <= 2 B/U.
```

Both signs are covered with outward parametrization. This is a bound on
the original left-line Gamma*zeta-square kernel. It is **not** a bound on
every head/tail integral introduced after applying the functional equation.
The central range |v| <= U/2 is outside this theorem's conclusion.

## Exact relation to the unresolved actual remainder

With the intended reflected polynomial Q_N(t) = chi(1/2+it)^2 conjugate(P_N(t)),
the existing actual residual is

```text
R_N(t) = zeta(1/2+it)^2 - P_N(t) - Q_N(t)
       = D_N(t) + [zeta(1/2+it)^2 - S_N(t) - Q_N(t)].
```

The new smoothing-defect theorem controls D_N without an analytic premise.
It gives no smallness assertion for the bracketed expression.

The intended contour representation of that bracket contains the moving
double-pole residue and the two functional-equation contour integrals.
This representation and the missing estimates must be supplied before
the existing uniform-residual theorem can establish I1.

## Exact remaining work

| Obligation | Status and needed provider |
| --- | --- |
| Infinite exponentially smoothed series and its smoothing defect | Proved here for positive integral smoothing scale N |
| Far tails of the original left-line actual kernel | Proved here, uniformly for all real Y >= 1 |
| Moving collision at z = 1/2-it | Open: establish the actual shifted double-pole contour identity, including its derivative term and all vanishing sides |
| Moving residue moment | Open: control Gamma and Gamma derivative at 1/2-it uniformly when Y is comparable to U |
| Critical-line phase | Connect the actual chi factor, its continuity and modulus one to the existing reflected-polynomial consumer |
| Central left-tail Dirichlet integral | Open: actual functional equation, power-weighted divisor-tail moment, and justified L2 integration in the contour variable |
| Right finite-head contour integral | Open: uniform chi quotient estimate, central L2 estimate, and its own far-tail control |
| Complete actual residual | Open: combine the exact terms with one constant independent of U |
| Dyadic-to-global I1 | Open: absorb the compact initial interval and sum geometric window lengths without adding a logarithm |
| Moving right-line Ingham estimate, Gabriel interpolation, near-line Selberg, Z03 | Unchanged |

The inspected base already contains
ConreyBaluyotEstermannActualGrowth.lean and the unconditional fixed-damping
Estermann shifts. Their constants may depend on the complex shifts, so
specializing a shift to 1/2+it is not a uniform-height estimate.
The diagonal collision theorem at shifts zero is not automatically the
moving collision theorem needed here.

For the next power-weighted left tail, base-16 blocks are compatible with
the new geometric L2 summation theorem: at c=-3/4 the length and squared
weight contribute 16^((1+2c)j)=4^(-j). This is an informal implementation
route, not an additional checked result.

## Sources and verification status

The analytic setting and the decomposition into smoothing, residue, and
contour contributions follow Chourasiya--Simonic, *An explicit form of
Ingham's zero density estimate*, arXiv:2507.15184v2, Section 5.1:
https://arxiv.org/html/2507.15184v2
That paper supplies classical external support, not a Lean assumption
silently passed to the new declarations.

The arithmetic input and finite mean value are reused from the published
d414397 continuation. The actual Hurwitz growth provider is also reused.

Successful candidate checks:

- Infinite series and smoothing defect:
  job_dpjyWqkjKjNnPdcK515tBokhyfZ4pVVn,
  https://app.buildbuddy.io/invocation/8f88d0ef-4e3e-454f-ad12-affa938593e7
- Actual far-tail integrability and uniform integral bound:
  job_BOWk49dms-Td4d9qmfysjL464mWsLn7w,
  https://app.buildbuddy.io/invocation/8651c265-cb9f-4cd2-bf39-4083510d3035

Final module checks and four explicit axiom guards passed:
job_xSGtlQbI35VSD4BNv6RnAOGKZ7oVAzhc,
https://app.buildbuddy.io/invocation/42a96ec0-952e-4d8f-9d29-3b8479b78528

The guards check the ordinary-series/block identity, the infinite moment,
the smoothing-defect moment, and the actual far-tail integral theorem.
Each uses exactly propext, Classical.choice, and Quot.sound. These guards
do not discharge hypotheses in a declaration's type. No domain-specific
axiom or unfinished proof was added.

Full-project Bazel/BuildBuddy validation passed for //:RiemannResearch,
including the three module exports and all project source modules:
job_YVt-gWjfguUjgCcmseWrblq96qsM7QNL,
https://app.buildbuddy.io/invocation/60729149-555d-4372-aa76-ae4545361f15
Reported server duration: 195.769 seconds, separate from task and polling time.

The validated source is the uncommitted delta based on d414397c, not a new
published commit. Only this documentation was updated after validation.

Final Lean source SHA-256 digests:

| Module | SHA-256 |
| --- | --- |
| GeometricL2Series.lean | fe95efcf2e46eb53b0688700b578f37805d7edd5118a64b5c7a7a1e645e66dc8 |
| SmoothedDivisorMoment.lean | c3fe9a7053b208c015fd352a639f0149b3134c4fc1525555d96f3a57527abcaf |
| ActualZetaSquareMellinTail.lean | 5453c592144b74f97880576a2842d9510e1bce5cb9bd2fdfc0559850c6b256cc |

The user approved committing and publishing these additions on 16 November 2026.
Use the managed checkpoint record for the publication commit and validation
of any integration with newer main.
