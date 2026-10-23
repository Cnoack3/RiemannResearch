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
