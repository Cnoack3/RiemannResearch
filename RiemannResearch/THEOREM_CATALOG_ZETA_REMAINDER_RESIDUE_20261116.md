# Uniform zeta-square remainder: moving residue and contour estimates

Prepared 16 November 2026 (UTC).
Investigation base: `193c19fe16fcef2d8a0d9b56a06b74bea9baffb9`.

## Status and precise boundary

This continuation proves the actual moving double-pole Laurent coefficient,
its uniform rapid decay, both central functional-equation multipliers, and
arbitrary-order decay of the original left Mellin tails. It also bounds the
actual zeta factor and actual original Mellin kernel in the central region.

**Current status:** [the completed uniform remainder proof](THEOREM_CATALOG_ZETA_REMAINDER_BOUND_20261116.md) now establishes the complete actual
residual estimate and the unconditional Ingham I1 fourth-moment theorem.
This catalog preserves the preceding residue/contour checkpoint and its
inputs. The remaining separate Z03 obligations are unchanged.

No hypothesis asserting a residue estimate, Gamma quotient estimate,
zeta growth estimate, or the target residual estimate is used in the
new analytic bounds.

## Exact moving pole and its strongest uniform estimates

The actual kernel is
`F(Y,t,z) = Gamma(z) Y^z zeta(1/2+it+z)^2`.
Put `p(t)=1/2-it`, and let gamma denote Euler's constant. The proved coefficient is

```text
Res(Y,t) = Gamma(p(t)) Y^p(t)
           (digamma(p(t)) + log(Y) + 2 gamma).
```

All complex powers and logarithms are principal. The proof first establishes
the exact pole separation
`F(Y,t,z) = N(Y,t,z)/(z-p(t))^2`, away from the pole, where
`N = Gamma(z) Y^z riemannZeta1(1/2+it+z)^2`. It then differentiates this
holomorphic numerator. The pole-subtracted Laurent limit is proved for
every real `Y>0` and every real `t`, including `t=0`.

For every natural `m` there is a nonnegative constant `C_m`, independent
of all displayed height and smoothing parameters, such that

```text
|Res(Y,t)| |t|^m <= C_m Y^(1/2) (1 + |log Y|)
    for Y>0, |t|>=1;

|Res(Y,t)| U^m <= C_m
    for 1<=Y<=U<=|t|;

U^(2m) integral_U^(2U) |Res(Y,t)|^2 dt <= C_m U
    for 1<=Y<=U.
```

Thus the moving-pole contribution has decay to every inverse-power order;
the dyadic square moment is O_m(U^(1-2m)). This is substantially smaller
than the required U(log U)^4 scale. The constants can depend on the order m.

| Declaration | Role |
| --- | --- |
| `zetaSquareMellinKernel_eq_numerator` | Exact double-pole separation |
| `hasDerivAt_zetaSquareMellinNumerator_pole` | Actual derivative and residue coefficient |
| `zetaSquareMellinKernel_moving_residue` | Exact pole-subtracted Laurent limit |
| `exists_zetaSquareMovingResidue_pow_bound` | Complete real-scale dependence |
| `exists_zetaSquareMovingResidue_uniform_pow_bound` | Uniform rapid decay for 1<=Y<=U<=|t| |
| `exists_zetaSquareMovingResidue_uniform_second_moment` | Every polynomially weighted dyadic square moment |

Owner: [ActualZetaSquareMovingResidue.lean](Analysis/ActualZetaSquareMovingResidue.lean).

## Both directions of the Gamma quotient

For arbitrary a,b in (0,1] and |t|>=1/2, the signed logarithmic estimate is

```text
|log |Gamma(b+it)| - log |Gamma(a+it)| - (b-a) log |t||
  <= 5 |b-a| / t^2.
```

It yields matching multiplicative lower and upper estimates
`exp(+-5 |b-a|/t^2) |t|^(b-a)`. The exponent can be negative;
the original ordered-abscissa API is retained.

Owner: [GammaRatioVertical.lean](Analysis/GammaRatioVertical.lean).
Declarations:
`abs_log_norm_Gamma_ratio_error_le`,
`norm_Gamma_ratio_le_of_pos`,
`le_norm_Gamma_ratio_of_pos`,
`norm_Gamma_symmetric_ratio_le_of_abs_lt`.

## The actual central functional-equation factors

For |t|>=1, the new theorems prove

```text
|chi(-1/4+it)| <= 2 pi^(-3/4) exp(5/t^2) (|t|/2)^(3/4),
|chi( 3/4+it)| <=   pi^( 1/4) exp(5/t^2) (|t|/2)^(-1/4).
```

The first is a specialization of a uniform theorem covering
-1<=Re(s)<=0, obtained by one exact Gamma recurrence.
The second uses the reversed Gamma quotient, preserving its negative power.

For U>=2, U<=t<=2U and |v|<=U/2, the central versions give

```text
|chi(-1/4+i(t+v))| <=
  [2 pi^(-3/4) exp(5) (5/4)^(3/4)] U^(3/4),

|chi(3/4+i(t+v))| <=
  [pi^(1/4) exp(5) (1/4)^(-1/4)] U^(-1/4).
```

Owner: [SymmetricZetaRatio.lean](Analysis/SymmetricZetaRatio.lean).
Declarations:
`norm_chiFE_symmetric_le_of_abs_lt`,
`norm_chiFE_symmetric_le_of_half_le`,
`norm_chiFE_neg_quarter_central_le`,
`norm_chiFE_three_quarters_central_le`.

Absolute convergence gives |zeta(5/4+iw)|<=5. Consequently the actual
left-line zeta factor has a fully explicit U^(3/4) bound, and the actual
original kernel has an explicit bound proportional to

```text
|Gamma(-3/4+iv)| Y^(-3/4) U^(3/2).
```

Owner: [ActualZetaSquareMellinCentral.lean](Analysis/ActualZetaSquareMellinCentral.lean).
Declarations:
`norm_riemannZeta_neg_quarter_central_le`,
`norm_zetaSquareMellinKernel_left_central_le`.

This last pointwise bound does not itself give the sharp arithmetic
mean-square estimate. The subtraction of the reflected finite polynomial
and the weighted divisor head/tail contributions must still be handled.

## Uniform rapid decay of the original Mellin tails

For every natural m there is C_m>=0 such that, for every real Y>0 and U>=2,
|t|<=2U and |tau|=1, both outward tails are absolutely integrable and

```text
U^m |integral_(U/2)^infinity F(Y,t,-3/4+i tau v) dv| <= C_m Y^(-3/4)/U.
```

This strengthens the earlier O(1/U) tail estimate to every inverse-power
order, retains the exact smoothing factor Y^(-3/4), and covers every Y>0.
The constants are independent of Y. For Y>=1 the scale factor is at most
one; both earlier scale-independent interfaces remain available as corollaries.

Owner: [ActualZetaSquareMellinTail.lean](Analysis/ActualZetaSquareMellinTail.lean).
Declarations:
`norm_zetaSquareMellinKernel_left_scale`,
`exists_zetaSquareMellinKernel_left_far_bound_scaled`,
`exists_zetaSquareMellinKernel_left_tail_integral_pow_bound_scaled`,
and the scale-independent `exists_zetaSquareMellinKernel_left_tail_integral_pow_bound`.

These are the tails of the **original** kernel. They should not be silently
substituted for the separate tails after the functional equation and the
arithmetic head/tail split.

## Previously remaining steps (now completed)

All five steps below are discharged by the completed remainder continuation.
Its full-line translated chi bounds and integrable Gamma envelopes handle
the transformed contours without a separate central/far split.

1. Prove the exact smoothed zeta-square Mellin representation at the moving
   critical parameter and its global contour shift, using the newly
   evaluated moving double pole and the Gamma pole at zero.
2. Apply the functional equation, split the actual divisor series at
   floor(U), and move the finite head to the right contour. Retain the
   exact signs of the reflected polynomial and all remainder pieces.
3. Prove the weighted infinite divisor-tail mean value on Re(s)=5/4
   and weighted finite-head mean value on Re(s)=1/4, uniformly on every
   translated interval of length U. For N=floor(U), retain N<=U<=2N;
   a theorem assuming interval length <=N cannot be applied directly to
   the full dyadic window. Existing finite divisor mean values,
   coefficient energy, and geometric L2 series estimates are available.
4. Combine these arithmetic estimates with the proved central chi factors;
   control the separate far regions of the transformed kernels.
5. Assemble the complete residual in L2 and apply
   `exists_fourth_moment_bound_of_actual_dyadic_residual`.

## Sources and verification

The analytic organization follows
[Chourasiya--Simonic, Section 5.1](https://arxiv.org/html/2507.15184v2).
The formal residue calculation uses Mathlib's entire regularized zeta
function and its derivative at one, the repository's unconditional wide
digamma growth theorem, and its arbitrary-order Gamma recurrence bounds.

The combined proof candidate passed Bazel/BuildBuddy:
job `job_2MjhuQ_RF3_PMfIe9SvHDwURx9P138e9`,
[verification log](https://app.buildbuddy.io/invocation/d3237c05-760c-41a5-95b0-645ae52d780a).
Six explicit axiom guards on the integrated modules passed in job
`job_K7xdImZdWF0HTzTaAKfhJYvVITEbyGCx`,
[verification log](https://app.buildbuddy.io/invocation/3337ca5e-afce-4388-a157-527030dca9b2).
They require exactly `propext`, `Classical.choice`, and `Quot.sound` for the
actual moving residue, its uniform second moment, the actual central kernel,
the right chi estimate, the lower Gamma quotient, and the arbitrary-order
scale-independent tail theorem. The final seven-guard audit also passed
for the stronger all-positive-scale tail theorem:
job `job_4TIMHF6NqTJloCNQSpQsYmYcuf9Y_GTC`,
[verification log](https://app.buildbuddy.io/invocation/79849eb9-7710-4005-8f11-f554ceea736b).
All seven guards require exactly the same three standard axioms.

The final module checks and managed full-project checkpoint supply the
publication evidence. Their terminal job records identify the exact final
source hashes and published commit; this note does not treat a queued job
as successful verification.
