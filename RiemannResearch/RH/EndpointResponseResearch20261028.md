# Orthogonal squarefree endpoint and physical absolute tails

Source: the user-provided argument and items 2 and 3 of
[InfiniteSquarefreeResponseResearch20261027.md](InfiniteSquarefreeResponseResearch20261027.md),
at [commit abd42dee](https://github.com/Cnoack3/RiemannResearch/commit/abd42dee58b969ce9c28ecfbf3cfec1e974c8b1a).
The implementation continues repository base ecf0cd3f4339af9af136f44eb1441408aa28b4b6.
These references support the statements and orthogonal-tail strategy.

## Exact objects and identities

All vectors live in the existing complete Q Hilbert realization, with
Q(n)=1/(zeta(2)n^2) for n>=1 and the zero physical anchor at n=0.
Canonical stage N contains the squarefree residue atoms with 2<=d<=N+1.
Write D_N=P-P_N, r=1-P1, r_N=1-P_N1, b=PBr, b_N=P_NBr_N,
and Bf(n)=f(n)/(n+1). The innovations u_j keep their original natural-number
indices, including every zero direction and dependent dictionary entry.

The new endpoint module proves the exact signed equality

    b-b_N = D_N B r - P_N B D_N 1,

the orthogonality of its two outputs, and the exact norm-square equality

    ||b-b_N||_Q^2 = ||D_N B r||_Q^2 + ||P_N B D_N 1||_Q^2.

No triangle inequality is applied to the complete signed endpoint series.
The first output is orthogonal to V_N; the second belongs to V_N.

Existing infinite innovation Parseval, together with the canonical rank-one
identity, yields for every f and N

    ||D_N f||_Q^2 = sum_(j>=N) <f,u_j>_Q^2.

Self-adjointness of B and Cauchy--Schwarz therefore give

    ||D_N B f||_Q^2 <= ||f||_Q^2 T_N,
    T_N = sum_(j>=N) ||B u_j||_Q^2.

For the opposite operator order, put d=D_N1. The proof uses duality:

    ||Bd||_Q^2 = <D_N B(Bd),d>_Q.

Squaring Cauchy--Schwarz and applying the preceding tail bound yields
||Bd||_Q^4 <= ||Bd||_Q^2 ||d||_Q^2 T_N. The zero case is handled separately
before cancellation. Projection contraction then bounds the second output.
The exact residual-energy identity is

    E_N = E_inf + A_N,
    A_N = ||D_N1||_Q^2 = sum_(j>=N) a_j^2,
    a_j = <1,u_j>_Q.

The two endpoint squares are bounded by E_inf T_N and A_N T_N respectively.
Their sum proves, for every canonical stage N,

    ||b-b_N||_Q^2 <= E_N T_N.

This is an endpoint theorem, distinct from the existing sum of squared
response increments. Every norm and every tail includes all physical sites.

## Quantitative physical absolute tails

Let c_j=<B r_(j+1),u_j>_Q and C_N=sum_(j>=N)c_j^2. The new physical-tail
module reuses the exact signed update and the existing variation bound to prove

    C_N <= E_N T_N.

The complete physical absolute tail is

    V_N(n) = sum_(j>=N) |b_(j+1)(n)-b_j(n)|.

For every N and physical n, including the zero anchor, Lean proves

    V_N(n) <= sqrt(zeta(2))*n*(sqrt(C_N)+sqrt(A_N*T_N)).

The orthogonal term uses coordinate Bessel on the nonzero innovation subtype,
then restores zero directions at their original indices. The correction uses
projection contraction and Cauchy--Schwarz on a_j and ||Bu_j||. Estimates for
arbitrary finite sets of stage indices pass to genuine summable infinite tails.
There is no finite physical-coordinate approximation.

Since the coefficient and smoothing-energy series converge, these divided
tails tend uniformly to zero over all physical sites:

    for every epsilon>0, eventually in N, for every n,
      |V_N(n)/n| < epsilon.

Division at n=0 uses Lean's real division convention; V_N(0)=0 independently.
Every individual QHilbert vector satisfies f(n)/n -> 0. A finite canonical
head therefore vanishes after division by n; the uniformly small remaining
absolute tail proves

    V(n)/n -> 0,  where V(n)=V_0(n).

The proof needs no periodicity lemma and makes no claim that the unsmoothed
absolute-variation envelope itself belongs to QHilbert.

## Declaration map

- `Analysis/ProjectionResponseEndpoint.lean`: reusable nested-projection
  signed identity, output orthogonality, exact Pythagoras, duality transfer,
  and factor-one endpoint bound with its explicit operator-tail hypothesis.
- `RH/QSquarefreeResponseEndpoint.lean`, namespace `QCanonicalInnovation`:
  `projection_tail_energy`, `projection_B_tail_norm_sq_le`,
  `movingCorrection_endpoint_eq`, `movingCorrection_endpoint_orthogonal`,
  `movingCorrection_endpoint_norm_sq`, `movingCorrection_endpoint_norm_sq_le`,
  and `targetEnergyTail_eq_error_sub`.
- `RH/QSquarefreeResponsePhysicalTail.lean`, namespace `QCanonicalInnovation`:
  `responseEnergyTail_le`, `physicalAbsoluteTail_le`,
  `physicalAbsoluteTail_div_nat_uniform`, and
  `physicalTotalVariation_div_nat_tendsto_zero`.
  The general helper `ZetaTwoHilbert.qSequence_div_nat_tendsto_zero`
  records sublinearity of individual complete-Q vectors.

The specialized endpoint and physical-tail conclusions have only their
displayed natural-number parameters. They assume neither RH nor residual
vanishing, dictionary independence, nonzero innovations, a logarithmic
envelope, or an exponential-moment provider.

## Residual-vanishing boundary

The new endpoint estimate strengthens quantitative approximation control.
It does not weaken a residual-vanishing criterion or discharge its arithmetic
premise. In particular, T_N -> 0 holds even when E_inf is not known to vanish.
The norm error can therefore tend to zero without forcing E_inf=0.

The checked consumer
`QSquarefreeExponentialMoment.residual_zero_iff_frequently_exponential_finiteSum_bound`
still requires a positive kappa and ONE common finite M such that every
finite physical set S admits cofinally many stages N satisfying

    sum_(n in S) Q(n)*exp(kappa*|b_N(n)|) <= M.

The checked consumer
`QSquarefreeMovingHeadEnergy.residual_zero_of_frequently_moving_head_energy_bound`
still requires a common unnormalized weighted-head-energy budget along an
expanding physical head. Neither provider is supplied here. Their status is **Open**.

Sublinearity cannot replace these hypotheses: a physical sequence n^alpha,
0<alpha<1/2, belongs to QHilbert and is o(n), yet has no positive exponential
or stretched-exponential Q moment. This elementary comparison is an informal
counterexample to a general functional implication; it is not asserted to be
the actual squarefree response, and it is not a new Lean declaration.

The arbitrary-signed finite-tail norm estimate in item 1 of the source
memorandum is not separately formalized by this change. The existing
infinite-stage variation theorem and separate parity-energy calculation are
reused or left unchanged, not re-proved.

## Verification record

Endpoint candidate and principal axiom audits: job_HuoPvohccTuJ4Ig_DtYFGhG7CyOleoj3,
verified=true, exit code 0, reported duration 7.985 seconds.
Physical-tail and sublinearity candidate audits: job_3DOQVfX_Jr1AEnAB3VW5AOKLsDBnzTb6,
verified=true, exit code 0, reported duration 5.952 seconds.
Both queue delays were approximately 0.0006 seconds; polling intentionally
waited for the server's 30-second retry interval. These reported durations
include preparation and checking, not isolated kernel time.

The initial workspace-opening request ran in a concurrent retrieval batch;
its individual round-trip duration was not separately measured. Subsequent
server connection timeouts produced no accepted verification job. Recovery
confirmed an empty queue before verification continued.

Saved-module audit: job_9_hCYyCA_h6DZgPmayLtKIK_p8Lbaden succeeded with
verified=true, exit code 0, and reported duration 15.490 seconds (queue delay
approximately 0.0006 seconds). It imported the saved modules, requested the
axioms of all 38 new public theorems, and printed the principal specialized
types. Bounded follow-ups recovered audit output omitted from the first
response: job_ugmjcZPCLMJm2mXUlRXdPl36uj8RXMQB (47.215 seconds) and
job_-jj4x4yc0xeEYh0myyHKFZiZnZfT0tY9 (28.951 seconds), both verified=true
and exit code 0. Every one of the 38 public theorem axiom lists contains only
propext, Classical.choice, and Quot.sound. There are no sorry, admit, project-local axiom, or unsafe
declarations in the new modules.

Final acceptance and publication use the server checkpoint, which validates
the saved modules and their required dependency scope before pushing.
