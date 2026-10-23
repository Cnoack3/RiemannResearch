# Ramanujan dual transfers 11–20

Source: user-requested continuation, 23 October 2026. Each numbered transfer
is verified on the Lean server and published separately to main.

The complete P and Q metrics, signed arithmetic terms, and full residuals
are retained. Full RH iff statements explicitly require the open analytic
provider RH -> BaezDuarte.NaturalApproximation unless a checked provider is
supplied. No saturation or RH assertion follows from a change of coordinates.
The residue dictionary approximating +1 has target coefficients -mu(d).

## Transfer 11: normalized legal optimizers and attained variance floor

Every nonempty canonical packet family has strictly positive mass M_n.
U_n=F_(n+1)/M_(n+1) is legal, has mean exactly one, and uniquely minimizes
energy among all mean-one vectors in its entire finite Hilbert span.
The exact identity is ||f||^2=1/M_(n+1)+||f-U_n||^2.
For m<=n, ||U_m-U_n||^2=1/M_(m+1)-1/M_(n+1).
The sequence converges unconditionally to U_inf=P_V1/(1-E_inf).
For every mean-one f in the full closed legal space, the original variance
floor strengthens to the exact attained identity
||f-1||^2=E_inf/(1-E_inf)+||f-U_inf||^2.
Energy(U_n)->1 iff E_inf=0, with the explicit analytic provider for RH iff.
Generic theorem: Analysis/ProjectionMeanOne.lean; consumer: RH/RamanujanUnitMean.lean.


## Transfer 12: exact error budgets for the actual P and Q optimizers

For every independent finite Q dictionary and every target x, both optimizers
retain their own inverse-Gram source. The full scaled Q error equals the full
P optimal error plus the P norm squared of the optimizer displacement plus the
exact reciprocal metric correction of the Q residual. The reversed identity
retains the Q displacement with its zeta(2) scale. Equality in the lower scaled
comparison holds exactly at exact interpolation. Applied to the actual
Ramanujan constant-target optimizers, the comparison is strict at every finite
stage. No equality of the two source vectors or metric optimizers is assumed.
Modules: RH/QParetoOptimizerError.lean; RH/RamanujanMetricOptimizer.lean.

## Transfer 13: arbitrary conductor blocks and exact screened inverse updates

Every finite family of distinct conductors greater than one is independent.
For any disjoint old/new conductor blocks, independence and positive determinant
of the entire screened Gram matrix follow automatically. For arbitrary source
vectors the joined inverse solution includes both new screened coefficients and
the signed correction to every old coefficient. Capacity is exactly old capacity
plus full screened capacity, with strict gain iff the screened source is nonzero.
For the actual constant target the source is Lambda at each conductor, and the
complete new error is one minus both capacities.
Module: RH/RamanujanBlockEnlargement.lean.

## Transfer 14: complete inverse-metric defects and sharp strictness

For every independent finite Q dictionary and every common source b, the
complete upper inverse-capacity gap is the sum of a squared P displacement and
the reciprocal metric correction. The upper bound is strict iff b is nonzero.
An exact identity for the lower comparison retains its displacement and full
correction defect as well. The actual finite Ramanujan Gram inverse quadratic
forms therefore satisfy strict upper comparison at precisely nonzero sources.
Modules: RH/QParetoInverseMetricDefect.lean; RH/RamanujanInverseMetric.lean.

## Transfer 15: exact optimizers with prescribed original coefficients

The arithmetic source r_m(q)=m*mu(q/m) when m divides q, and zero otherwise,
represents the original legal coefficient at m. Its inverse-Gram capacity K is
strictly positive whenever 1<m<=n+1, with no separate positivity assumption.
Prescribing coefficient t has the unique optimizer
a_constrained=a_n+(t-C_n(m))/K * H_n^(-1)r_m.
The full error is 1-M_n+(t-C_n(m))^2/K, and every feasible trial vector adds
the full squared synthesis norm of its coefficient displacement.
Feasibility holds exactly when m<=n+1 or t=0 (for m>1).
For t=-mu(m), the exact cost is (C_n(m)+mu(m))^2/K.
Module: RH/RamanujanCoefficientConstraints.lean.

## Transfer 16: exact two-sided legal coefficient linear equivalence

For every finite coefficient vector, the signed multiple transform
C(m)=m*sum_(m|q) mu(q/m)*a(q) has the explicit inverse
a(q)=sum_(q|m) C(m)/m over the same finite conductor range.
Both inverse laws and equality of the corresponding Hilbert syntheses are
proved. coefficientEquiv packages the result as a linear equivalence.
The actual P and Q packet optimizers each satisfy their own inverse formula,
and arbitrary finite reference vectors give exact correction decompositions.
No infinite multiple sum or exchange of an infinite sum with a limit is used.
Module: RH/RamanujanCoefficientInversion.lean.

## Transfer 17: actual Q gains, complete error products, and cofinal RH criteria

For the actual Q optimizer, E_n=1-M_n is strictly positive at every finite
stage (the candidate vanishes at a common factorial multiple). The exact
identity E_n=E_inf+||F_inf-F_n||_Q^2 gives coordinate rates in the energy excess.
The innovation gain is M_(n+1)-M_n; its finite sum is M_n. With r_n=gain_n/E_n,
0<=r_n<1 and E_n=product_(j<n)(1-r_j), including the exact logarithmic identity.
Nonsummability of r is equivalent to E_inf=0. Along every cofinal map from a
nontrivial filter, mass tending to one and all signed-multiple coordinates
tending to -mu(m) are each equivalent to E_inf=0. The RH package retains
hBaezDuarte explicitly. These are the Q optimizer's own coefficients and source.
Module: RH/QRamanujanSaturationCriteria.lean.

## Transfer 18: complete packet annihilators and Noor tail regularity

The canonical limiting residual is defined directly from the full closed
Ramanujan packet span and identified with the existing Pareto residual.
Every full P packet annihilator satisfying TailRegular is zero. Every Q
annihilator is zero when its correctly weighted inverse-adjoint P image is
TailRegular. For the canonical residual, zero residual, zero limiting energy,
TailRegular, square summability of centered complete tail averages, and full
packet mass saturation are equivalent. The exact tail-difference Parseval
identity retains its endpoint term E_inf-E_inf^2. TailRegular implies actual RH;
the reverse direction keeps the explicit hBaezDuarte provider.
Primary source for the existing shifted-density strategy: Noor,
https://arxiv.org/abs/1809.09577, Theorems 9 and 12.
Module: RH/RamanujanTailRegularity.lean.
