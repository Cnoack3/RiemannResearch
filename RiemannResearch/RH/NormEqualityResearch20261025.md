# L1/L2 equality cases for Q and Pareto

Date: 2026-10-25.

Source: the user's norm-convergence and equality-case discussion. The arguments
are standard Hilbert-space Cauchy–Schwarz and exact centered-energy identities.
The actual squarefree specialization uses the previously checked residual-tail
criterion. No new arithmetic cancellation or RH assertion is assumed.

## Measures and convergence

Use P(n)=1/(n(n+1)) and Q(n)=1/(zeta(2)n^2), for n>=1. Both are probability
laws with strictly positive mass at every positive integer. The Hilbert
realizations have an artificial zero anchor; all physical constant-function
claims therefore quantify n>=1.

For either measure nu, strong L2 convergence implies L1 convergence through
the sharp bound
```
||F_M - F_infinity||_(L1(nu)) <= ||F_M - F_infinity||_(L2(nu)).
```
These are norm limits, not uniform convergence over all physical coordinates.

The Q generic and optimizer limits remain in QHilbertConvergence and
QSquarefreeProjectionLimits. The Pareto projection limit remains in
MobiusCoefficientStabilization and ResidueProjectionL1. The new generic Pareto
norm-difference limit is ParetoL1Equality.hilbertL1Norm_sub_tendsto_zero.

The named standard Pareto dictionary uses all conductors. The current Q
optimizer dictionary uses squarefree conductors. Orthogonal projections are
taken with the respective inner products; equivalent norms do not identify
the projections.

## Exact inequalities and equality cases

For every real f in either L2 space,
```
|E_nu f| <= ||f||_(L1(nu)) <= ||f||_(L2(nu)).
```
The exact differences of squares are
```
||f - (E_nu f) * 1||_2^2 = ||f||_2^2 - (E_nu f)^2,
|||f| - (E_nu |f|) * 1||_2^2 = ||f||_2^2 - ||f||_1^2.
```

Consequently:
- ||f||_1 = ||f||_2 iff |f(n)| is constant for every n>=1.
- |E_nu f| = ||f||_2 iff f(n) itself is constant for every n>=1.
- For nonnegative f the distinction disappears, but no positivity assumption
  is available for a general projection residual.

Generic normalized-unit identities are in Analysis/UnitVectorVariance.lean.
The actual weighted-space results are QL1Equality.lean and ParetoL1Equality.lean.

The explicit Q counterexample qParitySign = qOne - 4*g_2 has physical values
-1 at odd n and +1 at even n. Its magnitude is identically one, hence its L1
and L2 norms agree, but it is not constant. The theorem
qL1_equality_nonconstant_example verifies this counterexample.
This is an ambient Hilbert vector, not an assertion of squarefree legality.

## Projection residuals retain their variance

For r=1-P_V 1 and delta=||r||_2^2, the projection identities give
E_nu r=E_nu r^2=delta. They do not give (E_nu r)^2=E_nu r^2.

The exact retained square is
```
||r - delta*1||_2^2 = delta*(1-delta).
```
The Q statement is QProjectionMoments.qResidual_variance_eq.
The actual Pareto residual and projection statements extend
ResidueProjectionL1. In particular, limitResidual_cs_equality_iff identifies
absolute-mean/L2 equality with delta=0 or delta=1.

## Conditional research reduction for the actual squarefree Q projection

QSquarefreeNormEquality proves
```
||r||_1 = ||r||_2 iff r=0,
||F_infinity||_1 = ||F_infinity||_2 iff F_infinity=1.
```
Constant magnitude implies physical boundedness. The actual squarefree tail
criterion then rules out a nonzero residual. Thus a nonzero residual and a
strict limiting projection both have strict L1/L2 inequalities.

Open: establish either norm equality for the actual limiting squarefree
projection or residual. The equivalences are verified reductions, not a
provider of equality. Convergence of norms and matching first/second moments
do not supply that provider.

## The proposed second-moment argument

For F=P_V 1, orthogonality gives the exact chain
```
E[F^2] = <F,F> = <1,F> = E[F] = a.
```
The last term is a, not a squared. Therefore Var(F)=a-a^2, which is zero
only for a=0 or a=1. With a=1-delta this equals delta*(1-delta).
Second-moment convergence passes this valid identity to the limit but does
not introduce the missing square.

Also ||F||_1=E|F|; it need not equal E[F] for a signed projection.

The already established odd-space projection is 2*g_2, the odd indicator.
Its Q first and second moments are both 3/4, while its squared mean is 9/16
and its variance is 3/16. QStrictProjectionCountermodel now records the exact
failed step as oddSpace_secondMoment_ne_mean_sq. This is a counterexample to
the proposed general projection inference, not a separator of the full
squarefree span.
