# Selberg density: formalization status and constructive proof route

28 October 2026.

The November 19 audit lists the current providers, the normalized second-moment route, the dyadic assembly and the status of the 2026 density results. [Current Selberg source audit](SelbergDensitySourceAudit20261119.md)

## Status

**Updated request, 14 November 2026:** the analytic proof is now requested,
superseding the earlier decision to defer it. The density estimate is an
unconditional published theorem, but its provider remains **open as a Lean
formalization**. The work recorded in
[the current coverage catalog](../THEOREM_CATALOG_SELBERG_PUBLISHED_RANGE_20261114.md)
closes the strict/inclusive count interface and the real-order Jordan finite
arithmetic. It does not discharge the uniform mollified zeta moment.
`ActualZeroOrdinate.ConreyBaluyotDensityHypothesis` is the proposition
`∀ a : ℝ, 0 < a → a < 8 / 7 → UniformSelbergDensity a`.
It includes every fixed exponent below 8/7, not the endpoint, and permits
the constants and height thresholds to depend on a. It is a definition of
a hypothesis, not a global axiom or an unconditional provider theorem.

Existing FMZ entry points retain their compatible one-quarter premise.
The new `ActualConreyBaluyotConsequences` module admits every fixed
frequency width b < 8/7 and proves that any positive density exponent
suffices for fixed-mode convergence. Its analytic density premise remains
explicit.
Given `hDensity : ConreyBaluyotDensityHypothesis`, use
`hDensity.classical` for that premise, `hDensity.one` for exponent 1,
or `hDensity a ha_pos ha_lt` for any admissible exponent. For example,
the existing fixed-mode result is invoked as
`tendsto_ordinate_landau_error_of_uniformSelberg u hDensity.classical`.

The positive-exponent provider remains **Open (formalization incomplete)**.
The proof route below is active work, not a completed formal Selberg proof.
The full Conrey--Baluyot range additionally requires the Chapter 3
Kloosterman/Estermann machinery; the shorter optimized-mollifier route below
does not by itself supply that strongest exponent.

New checked components are exact finite mollifier optimization, direct
uncentered-second-moment to logarithmic-integral transfer, optimal
logarithmic shifting of weighted zero counts, partial-strip extension, and
unconditional elementary endpoint/narrow-strip bounds. Neither the zero
exponent nor the narrow-strip bound supplies a positive-exponent global
density estimate.

## Published input and an optional future proof route

The conventional strict count satisfies
N(sigma,T) <<_c T^(1-c(sigma-1/2)) log T for every fixed 0<c<8/7.
Baluyot's thesis, Theorem 1.2.1 and Chapter 3, proves the Conrey strengthening;
its parameter is theta=c/2. Its analytic proof uses Kloosterman sums:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

A more modest constructive route follows Simonic, arXiv:1910.08274,
Sections 2–4, especially Proposition 2:
https://arxiv.org/html/1910.08274v2 .
For an optimized mollifier of length X=T^(1/6-epsilon), the uncentered
second moment is at most T+O(T X^(1-2sigma)) above
sigma=1/2+1/log X and below any fixed sigma0<1. This requires the
approximate functional equation and a twisted zeta second-moment estimate;
a finite Dirichlet-polynomial mean-square theorem does not replace them.

Our proposed choice epsilon=1/96 gives the raw exponent 5/16.
A bound with this exponent through sigma0=9/10 extends to exponent 1/4 on
the full strip because (5/16)(9/10-1/2)=(1/4)/2.
That extension is formally proved, conditional on the stronger partial-strip
density estimate. This is a derivation from the source strategy, not a
claim that its analytic premise has been formalized.

## Exact logarithmic transfer

For nonzero z define
D(z)=(|z|^2-1)/2-log|z| >= 0.
The new generic interval theorem retains the full equality
integral log|f| = (integral |f|^2-(T-H))/2 - integral D(f).
Consequently a bound integral |f|^2 <= T-H+E implies
integral log|f| <= E/2.

Nonvanishing and genuine interval-integrability conditions remain explicit.
The identity alone is valid with Mathlib's totalized log, but the defect
nonnegativity requires nonzero values. Boundary avoidance can supply a
nonvanishing contour in a later actual-zeta application.

The classical object here is Phi=zeta*M. It is different from the existing
quadratic detector 1-(zeta*M-1)^2. A theorem for integral |zeta*M|^2
does not, by itself, bound integral |zeta*M-1|^2: that would also need the
signed linear mean. The direct logarithmic bridge avoids that substitution.

## Exact count recovery and exponent preservation

Put q=c log T>0 and alpha=sigma-1/q. The proved window identity is
N_[H,T](sigma)=q[W(alpha)-W_above(sigma)-W_band(alpha,sigma)].
Every zero retains its analytic multiplicity, the top height is closed,
and both excess terms are retained.

If W(alpha)<=D T exp(-q(alpha-1/2))+E log T, then
N_[H,T](sigma)<=c e D T log T exp(-q(sigma-1/2))+c E(log T)^2.
The source exponent c is unchanged.
The shift is optimal for this argument: exp(qh)/h >= e q for every h>0.
Wolfram independently checked the derivative and the rational exponent
arithmetic; the persisted proofs are checked by Lean.

To reach the full uniform theorem one must still prove the source estimate,
absorb its lower-order terms uniformly, sum height windows, and handle the
critical-line band. The strict/inclusive convention is now proved in
`ActualSelbergDensityConventions`, with the critical-line endpoint supplied
by the unconditional total-count bound. The elementary
narrow-strip theorem provides the band where (sigma-1/2)log T is bounded.

## Finite arithmetic component

The diagonal completion keeps the complete residual:
sum v_i y_i^2 = 1/G + sum v_i(y_i-mu_i/(v_i G))^2,
where G=sum mu_i^2/v_i and sum mu_i y_i=1.
Positive v_i make the residual nonnegative.

Divisor incidence and its Mobius inverse give explicit optimizer
coefficients. The gcd-kernel identity is exact, retaining every
off-diagonal term. The divisor-lattice construction by itself has a
different support condition from n<=X. The cutoff realization proves the
optimizer vanishes above X; using L=X! gives exactly the set 1<=n<=X.
The concrete totient specialization supplies positivity, nonzero capacity,
and an unconditional attained minimum for the ordinary gcd kernel.
Writing a_n=n*coeff_n converts it to the classical critical-line form
sum a_m a_n gcd(m,n)/(m n).

The November 14 extension `SelbergRealJordanMollifier` proves the real-order
identity sum_{d|n} J_a(d)=n^a, its Euler product, J_a(n)>0 for a>0 and n>0,
and the exact supported gcd-power optimum. Its positivity and nonzero-mass
premises are discharged. Uniform reciprocal-mass asymptotics and the
analytic zeta moment are still not proved.

## Existing providers and remaining obligations

Established elsewhere in the project: actual zero multiplicities and
reflection, total zero-count asymptotics, Littlewood's contour identity,
compatible logarithmic lifts, boundary avoidance, and the right-boundary
estimate for the existing Mobius quadratic detector.

Open formalization obligations for the classical optimized-mollifier route:

1. Uniform estimates for the reciprocal mass G_X, including the cutoff tail.
   The real-order Jordan divisor identities, positivity, exact gcd-power
   diagonalization and supported optimizer are now proved.
2. A uniform approximate functional equation and the twisted zeta
   second moment, with both signed main terms and all remainders.
3. The resulting optimized-mollifier moment uniformly in sigma and T.
4. Compatible horizontal argument bounds for the chosen direct mollifier,
   with analytic zero-order transfer for that function.
5. Final uniform height-window assembly. The strict-to-inclusive count
   specialization is now proved, including sigma=1/2.

The negative secondary main term involving zeta(2-2sigma) must be retained
before deriving the upper bound. Its sign is part of the classical argument.

No new axiom or placeholder proof is used. This note records proved
components and an incomplete analytic formalization, not a completed
Selberg proof or an RH proof. Density consequences must continue to expose
their analytic premise until an actual provider is proved.
