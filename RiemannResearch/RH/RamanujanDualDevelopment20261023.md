# Ten transfers to the integrated Ramanujan dual

Source: user-requested research program, 23 October 2026. These are ordinary
Lean proofs in the persistent RiemannResearch project. Each numbered stage is
verified and published separately.

## Formal RH boundary

The existing checked coefficient stabilization chain is equivalent to the
constant target belonging to the closed legal residue span, and it implies RH.
The repository records RH-to-natural-approximation as an open formalization
dependency. The classical converse is proved by Luis Baez-Duarte,
"A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis",
https://arxiv.org/abs/math/0202141; citing that paper does not discharge a Lean
hypothesis. Any full RH iff below must explicitly supply the missing provider.

With positive residue fractions g_d(n) = (n mod d)/d approximating +1, the
original stabilized coefficients are -mu(d). The positive mu convention
corresponds to negating the dictionary or target.

## Transfer 1: quantitative finite-support obstruction

For every finite conductor set S with d>1, and every common multiple Q,
all packet combinations vanish at Q. Consequently the actual optimal mass
satisfies mass(S) <= 1 - P(Q), where P(Q)=1/(Q(Q+1)).
The exact identity error(S)=1-mass(S) remains in force.
Choosing the positive product of the conductors proves mass(S)<1.
The mean-one optimizer has strictly positive variance whenever its signal is
nonzero, without the old divisibility-by-2-or-3 hypothesis.

Saved in RH/RamanujanMeanOptimizer.lean. The previous unrestricted strict
inequality from RH/RamanujanSignalNoise.lean is consolidated into that lower
module, so downstream covariance results use the same quantitative argument.
This finite-support lower bound tends to zero when the common multiple grows;
it does not preclude RH approximation.

## Transfer 2: arbitrary dual moments and their exact inverse metric

For every finite set S of conductors greater than one and every moment vector y,
the actual arithmetic Gram solve defines a Hilbert representer D_S(y).
Its packet moments are exactly y and
inverseMetric(y,z) = <D_S(y),D_S(z)>.
The metric is symmetric and strictly positive on nonzero vectors.
Every Hilbert vector f with those same moments satisfies the exact identity

||f||^2 = inverseMetric(y,y) + ||f-D_S(y)||^2.

This proves minimality and an equality-if-and-only-if uniqueness statement.
It strengthens the bounded-sequence formulation to all Hilbert vectors and
retains the full orthogonal remainder. See RH/RamanujanDualInterpolation.lean.

## Transfer 3: actual canonical legal packet optimizers

Stage n uses conductors 2 through n+1. The actual packet coefficients are
a_n=H_n^{-1} Lambda_n. Their synthesis is exactly the original Pareto
projection, with no assumed normal equation or invertibility witness.
The captured mass is Lambda_n^T H_n^{-1} Lambda_n and the full error is
1-mass_n. For arbitrary trial coefficients b, the full error equals this
minimum plus the squared norm of the synthesis of b-a_n. Equality occurs
exactly when b=a_n. All signed mixed-conductor terms remain present.
See RH/RamanujanCanonicalOptimizer.lean.

## Transfer 4: coefficient stabilization in actual dual coordinates

Define C_n(m)=m sum_{q<=n+1, m|q} mu(q/m) a_n(q), with q>=2.
Lean proves C_n(m)=c_n(m) for every m>1, without any infinite sum interchange.
Thus these finite multiple transforms stabilize unconditionally. Their exact
correction C_n(m)+mu(m) is the Mobius test of the full residual.
The squared convergence error is at most
||MobiusTest_m||^2 (1-mass_n-limitEnergy).
All limits equal -mu(m) if and only if the limiting residual is zero, if and
only if the full packet approximation error tends to zero.
Individual a_n(q) convergence is not claimed.
See RH/RamanujanCoefficientLimits.lean.

## Transfer 5: a cofinal equivalence chain and exact gain structure

Let M_n=Lambda_n^T H_n^{-1}Lambda_n,
g_n=M_(n+1)-M_n, and r_n=g_n/(1-M_n).
Lean proves 0<=M_n<1, monotonicity, sum(g_n)=1-limitEnergy, and the exact
finite product 1-M_n=product_{j<n}(1-r_j).
Each fixed signed multiple coordinate has summable total variation.
The following are equivalent:
- M_n tends to 1;
- the full packet error norm tends to 0;
- every signed multiple coefficient tends to -mu(m);
- sum(g_n)=1;
- the relative gains r_n are not summable.

The first three tests may be sampled along ANY cofinal map from a nontrivial
filter, strengthening the original sequence statements. Each implies RH.
The complete RH iff package takes the explicit analytic converse provider
RH -> BaezDuarte.NaturalApproximation. That provider remains Open.
See RH/RamanujanSaturationCriteria.lean.

## Transfer 6: the actual Q-measure dual optimizer

The Q packet Gram matrix is positive definite on every finite initial family.
Its inverse applied to the actual Q source moments defines the unique finite
projection. The source is the divisor sum of Q residue means, not Lambda.
The full error has the same exact inverse-Gram minimum plus squared excess.
The signed multiple coordinates equal the original Q residue coefficients,
stabilize unconditionally, and reach -mu(m) exactly when the Q target lies in
the closed legal span. Full-norm convergence and Q mass tending to one are
equivalent to that condition, and hence to the corresponding Pareto tests.
A three-way Q RH iff package records the explicit Baez-Duarte converse
hypothesis; no equality of the different finite-measure optimizers is assumed.
See RH/QRamanujanCanonicalOptimizer.lean.
