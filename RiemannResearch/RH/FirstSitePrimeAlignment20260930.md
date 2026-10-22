# First-site prime alignment: exact squares and a weaker remaining provider

Date: 2026-09-30.
Base: Cnoack3/RiemannResearch 2e18190a98441778f47d5fdf7542e73bc5d68868.
Modules: Analysis/WeightedScalarEnergy.lean and RH/ParetoFirstSitePrimeAlignment.lean.

Follow-up: [RH consequences and the angular channel](FirstSiteRHAngularContinuation20260930.md).
That continuation distinguishes the classical RH implication from its explicit
Lean analytic provider, adds a monotone angular channel, and explains why
fixed-fraction source saving is incompatible with the classical growth scales.

The arithmetic provider remains **Open**. This continuation establishes exact
identities, stronger necessary cancellation under bounded capacity, and weaker
sufficient providers. It establishes no unconditional capacity divergence or RH.

## Complete accounting

Keep the base module's notation:
\[
C_{N+1}=C_1+U_N+V_N+2X_N+J_N,
\]
where the sums are over \(j<N\), prospective prime \(p=j+3\),
\(\delta_j>0\), actual signed correction \(\kappa_j\), and actual Schur
pivot \(\sigma_{j+1}>0\). The prime survivor is
\(\eta_{j+1}=\delta_j+\kappa_j\). Every nonprime increment is in \(J_N\).
The modulus-two initial capacity remains \(C_1\). The source \(U_N\to\infty\)
is established in the preceding modules.

For \(N\ge1\), \(U_N>0\). Define
\[
Y_N=U_N+X_N,\qquad R_N=Y_N^2/U_N,
\]
and retain the full centered square
\[
W_N=\sum_{\substack{j<N\\j+3\ {\rm prime}}}
 \frac{(\kappa_j-(X_N/U_N)\delta_j)^2}{\sigma_{j+1}}.
\]
The new exact identity is
\[
\boxed{C_{N+1}=C_1+R_N+W_N+J_N.}
\]
In particular,
\[
W_N=\frac{U_NV_N-X_N^2}{U_N}\ge0,
\]
with the complete ordered-pair formula
\[
\boxed{W_N=
 \frac1{2U_N}
 \sum_{\substack{i,j<N\\i+3,j+3\ {\rm prime}}}
 \frac{(\delta_i\kappa_j-\delta_j\kappa_i)^2}
 {\sigma_{i+1}\sigma_{j+1}}.}
\]
There is no independence assumption. Every pair, signed correlation inside
the square, error square, nonprime gain, and physical tail is retained.
The physical tails occur in the original Hilbert vectors defining
\(\kappa_j,\eta_j,\sigma_j\); this is an exact finite budget rearrangement,
not a physical-tail truncation.

Declarations:
- capacity_eq_prime_alignment_budget
- primeCancellationVariance_eq_pair_budget
- primePairCancellationBudget_eq
- primeCrossBudget_sq_le

## Stronger cancellation forced by bounded capacity

Let \(G_N=\sum_{\rm prime}\eta_{j+1}^2/\sigma_{j+1}\).
If \(C_n\) is bounded, the nonnegative prime gain series is summable.
Finite-head/tail Cauchy--Schwarz gives
\[
\boxed{R_N=\frac{(U_N+X_N)^2}{U_N}\longrightarrow0.}
\]
This is stronger than a uniform bound for \(R_N\) from one global
Cauchy--Schwarz estimate.

The argument keeps a fixed head \(M\) first. The actual signed tail satisfies
\[
(Y_N-Y_M)^2\le (U_N-U_M)(G_N-G_M),
\]
and therefore
\[
R_N\le \frac{2Y_M^2}{U_N}+2(G_N-G_M).
\]
The first term vanishes for fixed \(M\). Summability makes the second term
uniformly small when \(M\) is large. The Lean proof implements the epsilon
argument; it does not exchange nonsummable series or moving limits.

Define the error/source fluctuation quantity
\[
H_N=(V_N-U_N)^2/U_N.
\]
Its comparison also retains an exact square:
\[
\boxed{H_N+\frac{(G_N+2Y_N)^2}{U_N}
       =\frac{2G_N^2}{U_N}+8R_N.}
\]
Only after this equality is the displayed nonnegative completion square
discarded. Consequently bounded capacity also forces
\[
\boxed{H_N\longrightarrow0.}
\]
In ordinary asymptotic notation these statements are
\(U_N+X_N=o(\sqrt{U_N})\) and \(V_N-U_N=o(\sqrt{U_N})\).
They imply \(X_N/U_N\to-1\) and \(V_N/U_N\to1\); the displayed fluctuation
limits are the formalized stronger statements.

Declarations:
- Analysis.WeightedScalarEnergy.normalized_product_tendsto_zero
- factorialPrimeGain_summable_of_capacity_bounded
- primeMeanMismatchBudget_tendsto_of_capacity_bounded
- primeMeanMismatchBudget_tendsto_of_not_RH
- primeErrorMismatchBudget_completion
- primeErrorMismatchBudget_tendsto_of_capacity_bounded

## Weaker sufficient arithmetic providers

Each of the following explicit hypotheses supplies \(C_n\to\infty\), hence
the existing first-site error, offsite transfer, and RH endpoints:

1. Some \(\varepsilon>0\) has \(R_N\ge\varepsilon\) at arbitrarily late stages.
2. Some \(\varepsilon>0\) has \(H_N\ge\varepsilon\) at arbitrarily late stages.
3. Some fixed \(c>0\) and finite real \(K\) have, cofinally,
   \[
   \boxed{V_N\le U_N-c\sqrt{U_N}+K.}
   \]

These hypotheses are **Open**. The square-root saving in (3) allows the
relative error fraction to approach one, unlike a fixed \(\theta<1\).
A fixed additive constant is explicitly retained. No rate for capacity
growth follows merely from a cofinal mismatch without quantitative control
of the stages.

Declarations:
- tailCapacity_tendsto_of_prime_mean_mismatch_not_tendsto
- tailCapacity_tendsto_of_prime_mean_mismatch_cofinal
- tailCapacity_tendsto_of_prime_error_mismatch_cofinal
- tailCapacity_tendsto_of_prime_error_sqrt_gap_additive
- riemannHypothesis_of_prime_error_sqrt_gap_additive

Nonvanishing of \(R_N\) is sufficient, not necessary for RH.
A fixed positive variance \(W_N\) is insufficient: bounded capacity can
have a finite positive limiting prime gain. Unbounded variance or unbounded
nonprime gains suffice by the exact capacity identity.

The **weakest exact remaining inequality** remains
\[
\boxed{\forall B\in\mathbb R\ \exists N\ge1:
 R_N+W_N+J_N>B.}
\]
tailCapacity_tendsto_iff_prime_alignment_unbounded proves this equivalence
to capacity divergence, without constructing the arithmetic provider.

## The explicit screened CRT target

Set
\[
b_j=\langle {\rm tailInnovation}(j+1),
             {\rm infiniteCoprimeCertificate}(2!)\rangle,\quad
T_{jm}=\langle {\rm tailInnovation}(j+1),
                    {\rm factorialPrimeRefinement}(m)\rangle.
\]
The existing lower-triangular identities give
\(\kappa_j=b_j+\sum_{m<j}T_{jm}\).
The new prime_source_add_cross_eq_screened_rows proves exactly
\[
Y_N=\sum_{\substack{j<N\\j+3\ {\rm prime}}}
 \frac{\delta_j}{\sigma_{j+1}}
 \left(\delta_j+b_j+\sum_{m<j}T_{jm}\right).
\]
Thus one useful remaining signed arithmetic inequality is
\[
\exists\varepsilon>0\ \forall N_0\ \exists N\ge N_0:
 \left|\sum_{\rm prime\ j<N}\frac{\delta_j}{\sigma_{j+1}}
       \left(\delta_j+b_j+\sum_{m<j}T_{jm}\right)\right|
 \ge\varepsilon\sqrt{U_N}.
\]
This is the fluctuation-scale sufficient provider, not the weakest exact
provider. No signed summand may be replaced by an atomwise absolute bound.

Both orthogonal families and the positive diagonal are already established.
The raw tail-atom matrix has negative earlier-prime entries and a vanishing
raw row/source ratio. Those are raw identities; replacing screened
innovations by raw atoms would omit inverse-Gram screening.
Fixed-column Bessel bounds do not control the growing triangular row sum.

## Arithmetic import and primary-source review

The existing local additive_large_sieve provides an upper sampling bound
with constant \(\delta^{-1}+4\pi L\). mult_large_sieve_final provides an
upper character-energy bound of size \(C(L+Q^2)\). Neither statement
supplies the signed lower estimate above. An application still needs a
verified transfer through the actual inverse-Gram screening coefficients
and \(1/\sigma_{j+1}\). That transfer is **Open**.

The following primary sources were reviewed for applicability, not used
as unproved premises of the new Lean results:

- E. Kowalski, *Amplification arguments for large sieve inequalities*,
  Section 1, equations (2)--(3):
  https://people.math.ethz.ch/~kowalski/two-remarks-large-sieve.pdf.
  The harmonic and dual bounds and CRT amplification support upper
  square-energy control. They do not directly provide a one-sided bound
  for this adaptive screened correction.
- S. Bettin, J. B. Conrey, D. W. Farmer,
  *An optimal choice of Dirichlet polynomials for the Nyman--Beurling
  criterion*, Theorem 1: https://arxiv.org/abs/1211.5191.
  The optimal error asymptotic assumes RH and a reciprocal zeta-derivative
  moment estimate. It cannot supply an unconditional provider.
- L. Baez-Duarte, *On Nyman--Beurling's criterion for the Riemann
  hypothesis*, Lemma 2.1: https://arxiv.org/abs/math/0205003.
  The quoted Balazard--Saias estimate assumes a zero-free half-plane;
  its critical-boundary use does not remove that hypothesis.
- W. Ehm, *On certain Gram matrices and their associated series*:
  https://arxiv.org/abs/2405.06349.
  Exact continuous Gram decompositions are relevant comparison material;
  the discussion of component asymptotics is tentative and supplies no
  proved inverse-Gram or signed prime-budget estimate.

The conductor cost must be attached to the actual representation.
A factorial certificate may have a huge conductor; the residue features
with moduli at most \(N\) have reduced Fourier denominators at most \(N\).
Neither observation licenses a bound for adaptive screening.

## Verification and integration

The complete candidate and decisive endpoint axiom checks passed serialized
isolated Lean verification, exit code 0, with only propext, Classical.choice
and Quot.sound. The exact theorem types retain all substantive arithmetic
hypotheses. Standard axiom output does not discharge those hypotheses.

Both modules are exported from RiemannResearch.lean, and the theorem catalog
records the established identities separately from conditional research
reductions. Publication is through the workspace checkpoint with affected
modules and their reverse dependents validated. No fresh standalone full
repository rebuild is claimed.
