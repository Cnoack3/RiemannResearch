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
