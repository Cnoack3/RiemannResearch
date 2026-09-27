# Sparse signed heads, divergence, and damping accumulation

Date: 2026-09-27.
Base inspected: Cnoack3/RiemannResearch, commit
4f6f423803bbba6cfbcbe1af877f79e99ba90d9c.

## Outcome

This development does not prove RH. It proves a sparse-head energy transfer
with no factor-two loss, an exact fixed-damping sparse criterion, a signed
Gram divergence theorem, and a zero-free-strip consequence of accumulating
finite-energy dampings. None supplies a new unconditional finite-energy
parameter below epsilon=1/2.

The completed endpoint, the summable positive-damping diagonal, the
polynomial-cutoff criterion, and the signed Abel transfer were already
present at the base commit. They are inputs, not new achievements here.

## Definitions

For epsilon > 0 and integers n >= 1, put

\[
 w_n=\frac1{n(n+1)},\qquad
 c_\varepsilon=\operatorname{Re}\frac1{\zeta(1+\varepsilon)},\qquad
 g_\varepsilon(n)=
 \sum_{d\le n}\frac{\mu(d)}{d^\varepsilon}\lfloor n/d\rfloor
 -nc_\varepsilon .
\]

The zero coordinate and its weight are zero. Define the actual residue atoms

\[
 u_{\varepsilon,d}(n)=
 \frac{\mu(d)}{d^{1+\varepsilon}}(n\bmod d),\qquad d\ge1,
 \qquad F_{\varepsilon,M}=-\sum_{d=1}^M u_{\varepsilon,d}.
\]

For a physical head H, write

\[
 P_\varepsilon(H,M)=\sum_{n<H}w_n F_{\varepsilon,M}(n)^2,
\]
\[
 D_\varepsilon(H,M)=
 \sum_{d\le M}\sum_{n<H}w_n u_{\varepsilon,d}(n)^2,
\]
\[
 O_\varepsilon(H,M)=
 \sum_{\substack{d,e\le M\\d\ne e}}\sum_{n<H}
 w_n u_{\varepsilon,d}(n)u_{\varepsilon,e}(n).
\]

Both pair orientations occur in O. No absolute values are placed around
its individual terms. The exact finite Gram identity is

\[
 P_\varepsilon(H,M)=D_\varepsilon(H,M)+O_\varepsilon(H,M).
\]

The previously proved diagonal estimate gives

\[
 0\le D_\varepsilon(H,M)\le
 \mathcal D_\varepsilon,\qquad
 \mathcal D_\varepsilon=2\sum_{d=1}^\infty d^{-1-2\varepsilon}<\infty .
\]

The norm of an individual residue atom and the diagonal estimate are
unconditional at every positive damping.

The scalar Dirichlet series is absolutely convergent. Once M >= n,

\[
 F_{\varepsilon,M}(n)=
 \sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor
 -n\sum_{d\le M}\frac{\mu(d)}{d^{1+\varepsilon}},
\]

so F_{\varepsilon,M}(n) tends to g_\varepsilon(n) at each fixed n.
This is coordinate convergence, not a premise of Hilbert convergence.

## Theorem 1: sparse signed heads give the full energy bound

Let M(H) be any natural-valued function tending to infinity. It need not
be monotone, polynomial, or at least H. If some finite B satisfies

\[
 \forall H_0\ \exists H\ge H_0,\qquad
 O_\varepsilon(H,M(H))\le B,
\]

then the actual arithmetic energy exists and satisfies

\[
 \boxed{\quad
 E_\varepsilon=\sum_{n\ge1}w_n g_\varepsilon(n)^2
 \le \mathcal D_\varepsilon+B<\infty.\quad}
\]

There is no approximation-error term in this conclusion.

Proof. Fix a finite physical head N. At each good H >= N, nonnegative
coordinate energies and the exact Gram identity give

\[
 \sum_{n<N}w_nF_{\varepsilon,M(H)}(n)^2
 \le P_\varepsilon(H,M(H))
 \le\mathcal D_\varepsilon+B.
\]

The left side tends to \(\sum_{n<N}w_ng_\varepsilon(n)^2\) as H tends
to infinity. A convergent real sequence bounded above by the same
constant along arbitrarily large indices has limit at most that constant.
Thus every true finite-head energy is at most \(\mathcal D_\varepsilon+B\).
Their summands are nonnegative, so taking the supremum of the finite
partial sums proves summability and the displayed full-energy bound. QED.

The cutoff may have arbitrarily slow growth because only fixed physical
heads are passed to the limit. The arithmetic hypothesis is still the
bound on the actual signed off-diagonal, formed on growing heads.

Lean declaration:
centered_damped_energy_of_frequently_bounded_moving_heads.

## Theorem 2: exact sparse polynomial criterion and divergence

For an integer k satisfying 2*k*epsilon >= 1,

\[
 \boxed{\quad
 E_\varepsilon<\infty
 \ \Longleftrightarrow\
 \exists B\ \forall H_0\ \exists H\ge H_0:
 O_\varepsilon(H,(H+1)^k)\le B.\quad}
\]

Proof. The reverse direction is Theorem 1. For the forward direction,
the previously verified exact density-tail collapse and scalar tail bound
give

\[
 \sum_{n<H}w_n
 \bigl(F_{\varepsilon,(H+1)^k}(n)-g_\varepsilon(n)\bigr)^2
 \le \frac{H(H+1)^{-2k\varepsilon}}{\varepsilon^2}
 \le \frac1{\varepsilon^2}.
\]

The elementary inequality \((x+y)^2\le2x^2+2y^2\), summed with the
nonnegative weights, therefore gives

\[
 P_\varepsilon(H,(H+1)^k)\le2E_\varepsilon+2/\varepsilon^2.
\]

Since the diagonal is nonnegative, the same upper bound holds for O
at every head H, and in particular at arbitrarily large heads. QED.

More generally, if the actual energy is not finite, then for EVERY
M(H) tending to infinity,

\[
 \boxed{\quad O_\varepsilon(H,M(H))\longrightarrow+\infty.\quad}
\]

Proof. Otherwise, for some finite B the signed sum would be at most B
at arbitrarily large H. Theorem 1 would imply finite energy, a
contradiction. This proves eventual exceedance of every B, not merely
unboundedness. QED.

For polynomial cutoffs satisfying the stated exponent condition, the
two alternatives are thus globally bounded signed sums or divergence
to positive infinity. No analogous converse boundedness assertion is
made for arbitrary cutoff schedules.

Lean declarations:
centered_damped_energy_iff_frequently_bounded_polynomial_heads;
dampedMobius_moving_offDiagonal_tendsto_atTop_of_not_summable.

## Theorem 3: accumulation of dampings gives a zero-free strip

Let a >= 0, let epsilon_j > a tend to a, and let M_j(H) tend to infinity
for each j. Suppose that at arbitrarily large j there exists a finite
B_j for which

\[
 O_{\varepsilon_j}(H,M_j(H))\le B_j
\]

at arbitrarily large H. Then

\[
 \zeta(\rho)\ne0\qquad\text{if}\qquad
 \tfrac12+a<\operatorname{Re}\rho<1.
\]

Neither the B_j nor the full energies must be uniformly bounded in j.
No rate of accumulation is required.

Proof. Suppose a zero rho lay in this strip. Put z_0=rho-a; then z_0
is not the pole at 1. Analyticity and nontriviality of zeta give a
punctured zero-free neighborhood of z_0. This applies whether or not
z_0 itself is a zero.

For arbitrarily large good j, Theorem 1 gives actual finite energy at
epsilon_j. Burnol's zero-propagation argument, already formalized for
the actual centered arithmetic family, yields

\[
 \zeta(\rho-\varepsilon_j)=0
\]

once \(1/2+\varepsilon_j<\operatorname{Re}\rho\).
But \(\rho-\varepsilon_j\ne z_0\) because epsilon_j>a, and these
points approach z_0. A sufficiently large good j therefore places a
zero in the punctured zero-free neighborhood. Contradiction. QED.

Lean declaration:
zero_free_of_accumulating_frequently_bounded_signed_heads.

At a=0, the right-half-strip zero-free conclusion implies Mathlib's
RiemannHypothesis by the repository's verified symmetry reduction.
At positive a this is a partial zero-free conclusion, not RH.

## Explicit remaining hypothesis

Take epsilon_j=1/(j+3) and M_j(H)=(H+1)^(j+3).
The following arithmetic-only statement suffices for RH:

\[
 \boxed{
 \begin{aligned}
 &\text{for arbitrarily large }j,\ \exists B_j\in\mathbb R\\
 &\qquad\forall H_0\in\mathbb N\ \exists H\ge H_0:
 O_{1/(j+3)}\bigl(H,(H+1)^{j+3}\bigr)\le B_j.
 \end{aligned}}
\]

This weakens the required quantifiers in the existing sufficient
condition: one need not establish a bound at every damping index or
every physical head. It does not establish the displayed condition.
Because it implies RH, the condition remains an RH-strength arithmetic
obligation. No converse from RH is newly formalized here.

Lean declarations:
riemannHypothesis_of_doubly_frequent_signed_heads;
riemannHypothesis_of_sparse_reciprocal_polynomial_signed_heads.

## What failure of RH would force

The existing isolated-zero obstruction says that an off-line zero
prevents actual finite energy at every sufficiently small positive
damping, regardless of centering. Combining this with Theorem 2 gives

\[
 \neg\mathrm{RH}\Longrightarrow
 \exists\delta>0\ \forall\varepsilon\in(0,\delta)\
 \forall M(H)\to\infty,\quad
 O_\varepsilon(H,M(H))\to+\infty.
\]

This is a proved implication, not a contradiction. No theorem here
rules out that divergence.

Lean declarations:
right_half_zero_small_damping_moving_offDiagonal_diverges;
not_RH_small_damping_moving_offDiagonal_diverges.

## Source audit and provenance

The sparse finite-head proof is an elementary consequence of the actual
arithmetic coordinate limits, the summable diagonal, and nonnegative
finite-head energies. No mathematical novelty is claimed.

- J.-F. Burnol, On an analytic estimate in the theory of the Riemann zeta
  function and a theorem of Baez-Duarte, Section 4, Corollary 4.1 and
  Theorem 4.2: https://arxiv.org/pdf/math/0202166.
  This supports zero propagation and the accumulating-zero strategy.
  Its unconditional endpoint covers epsilon >= 1/2. Its subhalf
  membership lemma assumes RH.
- J. B. Conrey and G. Myerson, On the Balazard-Saias criterion,
  Theorem 1 and Remark 1: https://arxiv.org/pdf/math/0002254.
  Uniform fractional-part convergence does not settle the small-boundary
  weighted-square integral; the paper explicitly retains this gap.
- H. Maier and M. Th. Rassias, Estimates of sums related to the
  Nyman-Beurling criterion: https://arxiv.org/pdf/1705.09921.
  The existing repository audit records the separated-scale restriction.
  No whole signed-head estimate is inferred from it.
- S. Bettin, J. B. Conrey, D. W. Farmer, An optimal choice of Dirichlet
  polynomials for the Nyman-Beurling criterion:
  https://arxiv.org/abs/1211.5191.
  The optimal asymptotic assumes RH and an inverse-derivative moment
  bound, so it cannot be used to discharge the present unconditional gap.

Wolfram independently simplified the reciprocal-polynomial head-error
majorant to \((j+3)^2H/(H+1)^2\). This is supplementary symbolic evidence,
not the Lean proof and not an arithmetic cancellation estimate.

## Verification and remaining work

The source is in RH/DampedMobiusSparseHeadDichotomy.lean, exported from
RiemannResearch.lean. The project checkpoint validates the final module
and affected dependents before publication. Exact job evidence is
recorded below after the final candidate check.

Open: establish the displayed sparse signed upper bounds for the actual
Mobius coefficients. Even one specified new subhalf finite-energy
provider is not obtained here. The unconditional range remains
epsilon >= 1/2.

Final combined candidate check: job_-qNuqYLpowcSqsLgOoABXjJ1vHi8-Pms.
Result: verified=true, exit_code=0, 4.505 seconds, no warnings.
All five principal dependency reports contain only propext,
Classical.choice, and Quot.sound. No proof placeholders or project-local
axioms are introduced. Axiom reports do not discharge hypotheses in
the theorem types.
