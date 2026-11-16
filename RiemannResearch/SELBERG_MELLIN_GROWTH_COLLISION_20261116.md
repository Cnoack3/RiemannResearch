# Selberg–Estermann: strip decay, exact singular part, and collision residue

Prepared 16 November 2026, America/New_York.

Base: 61c1b4bcb0bac1bef3027c5dd5159541e618f6fa.
The resumed workspace was synchronized and main still matched this base.
Publication of this file is subject to the full managed checkpoint; the
checkpoint's terminal record identifies the final verified commit.

## Established results in this continuation

### 1. Arbitrary-order damped Gamma decay

File: Analysis/DampedGammaStripBounds.lean.

For Re(lam)>0, any real a,b, and natural n with 0<a+n, Lean proves

    exists C>=0, forall r in [a,b], forall t!=0,
      |Gamma(r+i*t) lam^(-r-i*t)| |t|^n <= C.

This is exists_gamma_mul_cpow_neg_strip_pow_bound. It follows from an exact
one-step recurrence and the already proved complex Laplace integral.
The pointwise lemma gamma_mul_cpow_neg_im_pow_bound retains an explicit
bound involving Real.Gamma(Re(s)+n). Taking arbitrarily large n gives
arbitrarily high inverse-power tail decay on any fixed bounded strip.

No Stirling asymptotic, unproved growth input, unit-class hypothesis,
or positivity of the left endpoint is used. The constants depend on the
fixed damping, strip, and order. This is not a uniform statement as the
damping approaches the imaginary axis or zero.

### 2. Exact separation of all Estermann singularities

File: Analysis/ConreyBaluyotEstermannRegularPart.lean.

For positive K and a unit h modulo K, the exact continued identity is

    E_h(u,v) = K^(1-u-v) zeta(u) zeta(v) + R_h(u,v),

where

    R_h(u,v) = K^(-u-v) sum_a sum_b e(h*a*b/K)
      (Hz(a,u)-zeta(u)) (Hz(b,v)-zeta(v)).

The zero residue class means Hurwitz parameter 1. The two cross terms
vanish by character orthogonality. All remaining finite summands and
their complex signs are retained.

Declarations:

- estermannRegularPart;
- estermann_eq_zeta_product_add_regular;
- analyticAt_estermannRegularPart_shifted;
- analyticAt_estermann_sub_estermann_shifted.

For every complex alpha,beta, s -> R_h(s+alpha,s+beta) is entire.
Consequently, the difference of two unit twists with the same modulus
is entire along every such common shift, even at coincident poles.
No claim about growth follows from entireness alone.

### 3. Explicit collision coefficient

File: Analysis/ConreyBaluyotEstermannMellinCollision.lean.

For alpha=beta=0, positive K, a unit h, and lam!=0, put
F(s)=Gamma(s) lam^(-s) E_h(s,s). The leading coefficient is still
A=1/(K*lam), and Lean now evaluates the missing simple coefficient:

    lim_(s->1, s!=1) (s-1) (F(s)-A/(s-1)^2)
      = (gamma-log(lam)-2*log(K))/(K*lam).

Here gamma is Real.eulerMascheroniConstant and all logarithms are
principal complex logarithms. The coefficient is independent of h.

The explicit numerator uses Mathlib's entire riemannZeta₁:

    g(s)=Gamma(s) lam^(-s)
      (K^(1-2*s) riemannZeta₁(s)^2 + (s-1)^2 R_h(s,s)).

The formal results are:

- estermannDiagonalNumerator;
- estermannMellinKernel_diagonal_eq_numerator;
- estermannDiagonalNumerator_one;
- hasDerivAt_estermannDiagonalNumerator_one;
- estermannMellinKernel_diagonal_residue_explicit.

The exact identity F(s)=g(s)/(s-1)^2 holds for every s!=1.
Mathlib supplies riemannZeta₁(1)=1, riemannZeta₁'(1)=gamma,
and Gamma'(1)=-gamma. There is no unresolved residue provider.

The original kernel still has a double pole. The repository's
simple-pole residue API is not being applied to it.

### 4. A more concrete remaining global-shift hypothesis

File: Analysis/ConreyBaluyotEstermannMellinGrowth.lean.

The following polynomial estimate is now sufficient:

    forall r in [a,b], forall |t|>=T0,
      |E_h(r+i*t+alpha,r+i*t+beta)| <= C |t|^n,

with C>=0 and natural n. The proved Gamma estimate of order n+2 gives

    exists B>=0, forall r in [a,b], forall |t|>=max(1,T0),
      |F(r+i*t)| <= B/(1+t^2).

This implication does not require distinct shifts. The resulting
distinct-pole global shift retains the original hypotheses on alpha,beta,
the unit numerator, the negative line, and the upper-half-plane damping.

Declarations:

- exists_estermannMellinKernel_tail_bound_of_polynomial_growth;
- estermannDampedSeries_eq_residues_add_mellinIntegral_of_polynomial_growth.

**Conditional research reduction:** the actual polynomial Estermann
strip bound has not been proved. The global theorem is not unconditional.
Once the bound is supplied for each supported summand, the existing finite
tail-bound assembly applies with all original coefficients.

## Research agenda after this checkpoint

1. **Next concrete analytic task: continued Hurwitz growth.**
   For the actual shifts alpha=2*l-1, beta=0 and 0<l<1, choose a=-l.
   On r>=a, both r and r+alpha are strictly greater than -1:
   r>=-l>-1 and r+alpha>=l-1>-1.
   NIST DLMF 25.11.6 gives an Euler–Maclaurin integral representation on
   this half-plane, with the corrected numerator B2-periodic(x)-B2.
   Prove the representation for the project's Hurwitz continuation,
   bound that periodic factor, and bound the remainder integral uniformly
   over the fixed real interval.
   The expected bound is O(|t|^2) per Hurwitz factor for |t|>=1.
   The finite identity then gives an O(|t|^4) Estermann bound; the new
   order-six Gamma bound supplies the required quadratic kernel tail.
   These exponents are a proposed deduction, not Lean-verified providers.
   Reference: https://dlmf.nist.gov/25.11.E6
   For an arbitrary negative line with shifted real parts down to -2,
   the higher Euler–Maclaurin formula 25.11.7 is another route:
   https://dlmf.nist.gov/25.11.E7

2. **Collision rectangle accounting.**
   The residue evaluation is now closed. Subtract A/(s-1)^2,
   prove the subtraction has zero rectangle boundary integral, and apply
   the simple-pole theorem to the remainder. Then derive the global
   collision identity from the actual tail estimate. Neither rectangle
   nor global collision identity is included in this checkpoint.

3. **Actual Gaussian rays.**
   Insert the completed global shifts into both outward rays. Establish
   endpoint domination, integral splitting, and every Fubini interchange.
   Fixed-damping convergence is insufficient for integration over damping
   parameters approaching the boundary.

4. **Complete signed decomposition.**
   Identify M1+M2+D1+D2+E and preserve the existing signed
   -(2*sqrt(pi)/Delta)*mollifiedGaussianPoleCoeff correction.

5. **Arithmetic and cofinal estimates.**
   Supply the complete/multilinear Kloosterman estimates with their
   modulus, gcd, coefficient, and range hypotheses, then the common
   eta,C,H valid at all later parameters and padded centers.

6. **Independent density provider.**
   ActualZeroOrdinate.InghamDensityBound remains a separate formalization
   obligation. Ingham I2 is already closed and must not be restarted.

No new uniform density bound, dyadic-equidistribution theorem, or RH
conclusion is claimed.

## Verification

The coherent proof candidate passed Bazel/BuildBuddy as
job_FmppvLpqa7OgCby2l4hemj2Im47OXDi3 (server build time 40.506 seconds):
https://app.buildbuddy.io/invocation/a31ad71b-b7a1-41a3-836e-83b4f2170abb

The persisted modules, their transitive imports, and six guarded axiom
checks passed as job_j9QwqrmCTFf6SaYEnp3MmuJE9mdbEVwM:
https://app.buildbuddy.io/invocation/c582dd9a-b24e-4040-90aa-6f283fa01cc0
Server-reported build time: 28.429 seconds. Each guarded declaration
depends exactly on propext, Classical.choice, and Quot.sound.

The managed full-project checkpoint is the final publication gate.
A focused module pass does not certify the full project. See the terminal
checkpoint record for the exact publication SHA and full validation.

## Provenance and retained workspace

The contour setting and finite Hurwitz identity come from S. A. C. Baluyot,
On the Zeros of Riemann's Zeta-function (2017), Lemma 3.1.3, pp. 95–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

The exact character separation and recurrence estimates are derived from
the existing project and Mathlib theorems; no novelty claim is made.

Workspace token: ws_O5g_HcTqMq11Vgoxn1u4_9Rz7BHKrorF

Project root:
/home/cri_2025/lean-agent-workspaces/ws_O5g_HcTqMq11Vgoxn1u4_9Rz7BHKrorF/RiemannResearch
