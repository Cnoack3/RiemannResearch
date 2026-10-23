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

## Transfer 7: arbitrary-conductor exact Schur enlargement

For every finite S of conductors greater than one, every q>1 outside S has
strictly positive Schur pivot. The former ordering condition q>max(S) is
unnecessary. The signed score is the old residual's correlation with R_q.
The Schur update has an explicit legal coefficient vector and equals the
independently constructed inverse-Gram optimizer on S union {q}.
Consequently M_(S union {q})=M_S+score^2/pivot exactly, and the actual mass
increases strictly if and only if the screened score is nonzero.
The complete error and all Pareto tails remain in the formula.
See RH/RamanujanSchurEnlargement.lean.

## Transfer 8: complete determinant and determinantal probability structure

For every Hilbert target, packet inverse-Gram regression is the actual finite
projection. The complete packet Gram determinant is strictly positive.
The first-site determinant polynomial equals 1-z*fullCapacity/2 for every real z
and equals the original residue determinant polynomial. Its value at z=1 is
the actual first-site vacancy probability. Tending to zero is equivalent to
tailCapacity tending to infinity, constant-target approximation, full legal
span density, natural approximation, and constant-target packet mass tending
to one. Thus the Moebius-marked and Lambda-marked finite quantities have the
same limiting criterion, without being identified at finite stages.

The complete finite-window kernel is U H^{-1} U^T. For every real z, its
characteristic determinant equals det(H-z*U^T U)/det(H), including repeated
observations. For injective windows, z=1 is the actual law's gap probability.
The determinant-zero criterion implies RH unconditionally; its converse is
stated with the explicit analytic provider. See RH/RamanujanGramDeterminants.lean.

## Transfer 9: complete annihilators, sharp certificates, and adjoint duality

For every packet set S and every Hilbert target x, membership in the complete
closed packet span is equivalent to every packet annihilator pairing to zero
with x. Outside that span, the normalized projection residual is a separator
with pairing one and exactly ||h||^2 * distance(x,span)^2 = 1.
For every competitor in the full closed span, the sharp Cauchy certificate is
< h,x >^2 <= ||h||^2 ||x-v||^2; the canonical residual attains equality.
No finiteness, divisor closure, independence, or arithmetic sign hypothesis
is imposed on these arbitrary-set certificates.

The adjoints of the P/Q continuous equivalences are explicit inverse maps
on dual vectors, preserve every target pairing, and transfer individual
annihilators bijectively. A sequence-preserving primal map is not substituted
for this dual map, and equality of the two metric norms is not asserted.
For the full legal conductor set, triviality of the annihilator under either
measure is equivalent to natural approximation and implies RH. The reverse
RH implication explicitly requires the Baez-Duarte provider.
See Analysis/HilbertAnnihilatorCertificate.lean and RH/RamanujanDualCertificates.lean.

## Transfer 10: exact finite-zero obstructions and forced coefficient defects

Every arbitrary finite family of actual zeta zeros with Re(z)>1/2 and z!=1
gives a signed Cauchy-Gram charge. The exact canonical error is that charge
plus the complete Mellin integral remainder. Repeated zeros and singular
families are allowed; no inverse or nondegeneracy assumption is inserted.
For every legal trial coefficient vector, the exact identity additionally
retains its squared full-Gram displacement from the canonical optimizer.

The conjugate-pair certificate strictly improves the single-zero floor.
All finite-zero charges also bound the limiting energy. In particular an
actual right-hand zero forces positive limiting energy and the existence
of m>1 for which the stabilized coefficient differs from -mu(m).
Consequently the corresponding signed packet multiple coordinate cannot
converge to its Mobius target. Its unconditional convergence to the actual
limit remains valid. No individual packet synthesis-coordinate limit is claimed.
See RH/RamanujanZeroCertificates.lean.

The Mellin obstruction strategy is consistent with J.-F. Burnol,
"A note on Nyman's equivalent formulation of the Riemann Hypothesis",
https://arxiv.org/abs/math/9910055. The actual statements above are Lean proofs
from the project's exact complete-residual identities.

## Combined criterion and remaining proof target

Let R_q=sum_{d|q} mu(q/d)*d*g_d, with g_d(k)=(k mod d)/d.
For S_n={2,...,n+1}, let H_n be the complete Pareto packet Gram matrix,
a_n=H_n^{-1}Lambda_n, F_n=sum a_n(q)R_q, and
M_n=Lambda_n^T H_n^{-1}Lambda_n.
Let C_n(m)=m*sum_{q in S_n,m|q} mu(q/m)*a_n(q).
The exact error is ||1-F_n||^2=1-M_n.

The following conditions are equivalent WITHOUT the external analytic provider:
- M_n tends to one;
- the full error norm tends to zero;
- every C_n(m), m>1, tends to -mu(m);
- the sum of successive packet mass gains equals one;
- the relative gains are not summable;
- the first-site packet determinant tends to zero;
- tailCapacity tends to infinity;
- the full legal packet span is dense;
- every complete Pareto packet annihilator is zero;
- every complete Q packet annihilator is zero;
- actual Q optimizer mass tends to one;
- actual Q optimizer error tends to zero;
- every actual Q signed multiple coordinate reaches its Mobius target;
- BaezDuarte.NaturalApproximation holds.

The P norm/mass/coordinate tests are valid along arbitrary cofinal maps from
nontrivial filters. Q uses its own complete Gram metric and source moments.

Every condition implies RH in Lean. The full RH iff packages take the named
provider RH -> BaezDuarte.NaturalApproximation. No provider proof or RH proof
has been supplied by these transfers. An intrinsic remaining Ramanujan goal
is to prove full packet annihilator rigidity, equivalently mass saturation.

## Verification and publication record

Each transfer is separately audited, built with the root aggregate and its
changed modules, committed, and pushed to main. The first nine publication
records are below; transfer 10 is the commit containing this completed ledger.

| Transfer | Commit | Successful checkpoint job | Build seconds |
| --- | --- | --- | --- |
| 1 | `3d5579d247b254cfa89fc87f45bdb8fe2cd2361e` | `job_uhjTWAq54pnmdzisg5LdJyJplogbgyLx` | 45.943 |
| 2 | `9df994eaa6cdb7b36c8481f04a25f953ac8e8e81` | `job_dbkjBdyy5FQkodDx4HwpupuG7KbNoFBa` | 44.758 |
| 3 | `b53ff8b0a6c0a85ff7ebc6855ab984b38a3792fa` | `job__Y3MgN60VC0w5zLM5EF5zVEPY0xBS6Ta` | 38.264 |
| 4 | `01c1324dc9aac1128e24efd4b3d5f4d51337a959` | `job_xHqYIGbdOBeTDi-MtxqdXHVCfKzpdHrr` | 38.765 |
| 5 | `1a534fbc8e5f4231dffbace47c2ffefabfb3fae4` | `job_gwhuxd-UkbpCUk_qiD0ma7iWShxcYeKw` | 39.361 |
| 6 | `9f0b6f28f93637552bf95e8f7e7481cbad58a2bd` | `job_zCCQBZZYmuC6nWYNE-FJPwzUGj2luLhB` | 39.154 |
| 7 | `860c15bedd01fb1a26474581044357b3871fcfba` | `job_TThlqCOxdHvlDq3gYCIRqzDSoDaa-plz` | 40.475 |
| 8 | `ce09b678cc21b131c2ed1cb21b51345ad46db737` | `job_SiTLDGdX6OviIKgNXCOZfRC2e_j6pAjX` | 37.274 |
| 9 | `279da8b57f2157c27a16d621ceccb836e90fafa5` | `job_gdhX5lGppmeGOkq5G8myXMUCMWs3Kpo5` | 41.23 |

Transfer 10 and representative results from all ten transfers passed snippet
job `job_dHQ_59JtsPZEds36ZzROYyi4QcHF7hQn` in 5.958 seconds.
The 13 representative axiom audits returned only propext, Classical.choice,
and Quot.sound. Conditional RH theorem hypotheses remain explicit despite
that axiom result. No project axiom or proof placeholder was introduced.

This requested development stops after transfer 10.
