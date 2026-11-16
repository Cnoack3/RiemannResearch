# Actual Hurwitz strip provider and fixed-damping Estermann shifts

Prepared 16 November 2026 (UTC).

## Established results

This development supplies the previously missing polynomial-growth input.
It does **not** supply UniformSelbergDensity or the cofinal mollified moment.

**M06 status: closed.** A subsequent checked strengthening supplies explicit
uniform Hurwitz-parameter and modulus bounds, including one Mellin-tail
constant after an explicit power of the modulus is factored out. See
[uniform modulus continuation](THEOREM_CATALOG_HURWITZ_UNIFORM_MODULUS_20261116.md).

### Exact identities first

In Analysis/HurwitzEulerMaclaurin.lean, namespace
RiemannResearch.Analysis.HurwitzEulerMaclaurin, set
B(x) = fract(x)(fract(x)-1). For q>0 and Re(s)>-1:

```text
sum_{n<N} (q+n)^(-s)
 = [q^(-s)-(q+N)^(-s)]/2
   + integral_q^(q+N) x^(-s) dx
   - s(s+1)/2 * integral_q^(q+N) B(x-q)x^(-s-2) dx.
```

The finite theorem is sum_range_cpow_eq. Both endpoint terms are retained.

For 0<q<=1, Re(s)>-1 and Im(s)!=0,
hurwitzZeta_eq_eulerMaclaurinValue identifies Mathlib's actual continuation with

```text
Hurwitz(q,s)
 = q^(-s)*(1/2 + q/(s-1))
   - s(s+1)/2 * integral_q^infinity B(x-q)x^(-s-2) dx.
```

The proof establishes the finite formula by integration by parts, identifies
the infinite limit for Re(s)>1 using the actual Dirichlet series, proves
holomorphy of the remainder through its cutoff Mellin transform, and uses
analytic uniqueness on the upper and lower half-planes.

### Bounds supplied without a growth assumption

| Declaration | Result |
|---|---|
| abs_bernoulliRemainder_le | Absolute value of B is at most 1/4. |
| integrable_remainderIntegrand | Absolute integrability for q>0 and Re(s)>-1. |
| norm_remainderIntegral_le | Remainder integral bounded by q^(-Re(s)-1)/(4(Re(s)+1)). |
| norm_hurwitzZeta_strip_le | Explicit quadratic bound for the actual Hurwitz zeta, uniformly for r in [a,b], a>-1, and absolute t>=1. |
| exists_hurwitzZeta_shifted_strip_bound | Every circle parameter, any fixed complex shift alpha, and a+Re(alpha)>-1 admit a positive quadratic constant; threshold is 2(1+absolute Im(alpha)). |

Writing R=max(absolute a,absolute b), the explicit unshifted bound is

```text
|Hurwitz(q,r+it)|
 <= [q^(-b)*(1/2+q)
     + (R+1)*(R+2)/8 * q^(-b-1)/(a+1)] * |t|^2.
```

No equality with the EM expression at real s is asserted by this module;
off-real equality suffices for the vertical tails.

### Actual contour consumers

Analysis/ConreyBaluyotEstermannActualGrowth.lean, namespace
RiemannResearch.Analysis.ConreyBaluyot:

| Declaration | Exact scope |
|---|---|
| exists_estermann_shifted_strip_bound | Quartic growth, uniform over all numerator classes at fixed K>0, provided a+Re(alpha)>-1 and a+Re(beta)>-1. |
| exists_estermannMellinKernel_tail_bound | Actual O((1+t^2)^(-1)) tail for fixed Re(lambda)>0 and a>-1, with the same shifted left-edge conditions. |
| estermannDampedSeries_eq_residues_add_mellinIntegral | Distinct-pole global shift with the growth hypothesis discharged. Retains the exact residue sum and left vertical integral. |
| estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral | Actual zero-shift double-pole collision formula, with no growth-provider premise. |

The distinct-pole identity also requires Re(alpha),Re(beta)<1, alpha!=beta,
Im(w)>0, -1<a<0, and b+Re(alpha),b+Re(beta)>1.
The diagonal identity requires Im(w)>0, -1<a<0, and b>1.

The old generic transfer theorems retain their explicit hypotheses. The new
consumer declarations discharge them with actual proved bounds.

## Density status and next obligation

**Still open in this Lean development:** the positive-exponent uniform
Selberg density provider. The new constants may depend on the modulus,
shift, strip and positive damping. The subsequent uniform-modulus development
quantifies the modulus dependence as an explicit real power of K, with the
remaining constant independent of K. It does not give a modulus-independent
bound or a bound uniform as the damping approaches its boundary.

The existing density consumer in ActualConreyBaluyotDensity.lean needs:

1. UniformDyadicMollifiedMoment theta epsilon (or the proved Gaussian-to-dyadic
   reduction supplied with UniformGaussianMollifiedMoment).
2. InghamDensityBound.

The dyadic estimate must hold uniformly on the moving near-line interval:

```text
mollifiedSecondMoment(sigma,T^theta,epsilon,sigma,T,2*T)
 <= T + C*T^(1-2*theta*(sigma-1/2)),
1/2 + 1/log(T^theta) <= sigma <= 1/2 + eta.
```

For a requested a>0 one needs theta with a<=2*theta. The full a<8/7 route
uses a cofinal family theta<4/7. In particular, the literal a<7/8 request
still needs the uniform moment; a fixed-parameter contour identity does not
supply it.

Next: obtain domination for the actual Gaussian-ray integration, retaining
both signed rays and every residue, then estimate the finite arithmetic sums
with their dependence on the mollifier length and height. The proved I2
estimate controls the mollifier alone; it is not a bound for zeta times the
mollifier. The separate Ingham inputs also remain required.

## Sources and verification

Classical source: [NIST DLMF 25.11.6](https://dlmf.nist.gov/25.11.E6),
the corrected Euler--Maclaurin formula. The strip bound and continuation
proof are formal derivations from that identity.

Contour setting: [Baluyot (2017), pp. 95–97](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320),
equation (3.1.7) and Lemma 3.1.3.

Focused acceptance: Bazel job job_3ebCwE8_rBzIJ0Sgy95k9T8_uoz6CshS succeeded for
ConreyBaluyotEstermannActualGrowth and its transitive imports (including the new
HurwitzEulerMaclaurin module).
[BuildBuddy log](https://app.buildbuddy.io/invocation/031e712a-f588-4a91-9fcb-3bb0eed36523).

Eight guarded axiom audits passed in Bazel job
job_mpQVNwSqX3CbeqvncZZP9nYRSI-Hk4Ub. Each audited declaration depends exactly
on propext, Classical.choice and Quot.sound.
[Guarded audit log](https://app.buildbuddy.io/invocation/49f43b55-7414-41a5-a14a-4301bb6b7be9).

The managed publication checkpoint containing this catalog audits source and
validates the full project with Bazel/BuildBuddy. Standard-foundation axiom
audits are separate from inspection of each theorem's explicit hypotheses.
