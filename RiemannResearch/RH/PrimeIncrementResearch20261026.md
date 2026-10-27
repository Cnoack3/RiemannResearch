# Prime-increment detection of the squarefree residual

26 October 2026. Continuation of the supplied `PrimeResamplingResearch20261027.md`.

## Result and verification boundary

The new Lean result is an exact local criterion for vanishing of the actual
squarefree residual. Its sufficient direction is connected to Mathlib's
`RiemannHypothesis`. The arithmetic estimate in that criterion remains open;
this development does not prove RH.

The following modules have passed a targeted server check:

- `Analysis/PrimeIncrementEnvelope.lean`: three general prime-factor
  telescoping statements.
- `Analysis/ProjectionAveragingDefect.lean`: seven exact projection identities,
  estimates, and membership criteria.
- `RH/QSquarefreePrimeIncrement.lean`: seven results for the actual limiting
  correction and its finite moving approximants.

The targeted project-module/axiom job is
`job_ytnmjKLl4AFpV4MK_haGwroMAIFc-idG`, exit code 0, verified true, reported
elapsed time 15.705 seconds. The four inspected principal declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`. This check does not hide
the prime-increment premise: it remains explicit in the theorem type.
Workspace-opening duration was not measured and is separate from this duration.
Publication requires the final checkpoint validation.

The countable prime-product construction, identification of its resampling
energy, extended Poincare inequality, and near-pole integral arguments in the
handoff remain paper results. The new abstract averaging theorem does not
silently formalize that probability construction.

## Definitions and strongest exact criterion

Use the repository's physical Q space,
\[
 Q(n)=\frac1{\zeta(2)n^2},\quad g_d(n)=\frac{n\bmod d}{d},\quad
 V=\overline{\operatorname{span}\{g_d:d\ge2\text{ squarefree}\}},
\]
and its actual stages and corrections
\[
 r_N=(I-P_N)1,\quad r=(I-P_V)1,\quad
 (Bf)(n)=\frac{f(n)}{n+1},\quad b_N=P_NBr_N,\quad b=P_VBr.
\]
Existing results supply L2(Q) and coordinatewise convergence of b_N to b.

For **each fixed** integer m>=0 and real L>0, Lean proves
\[
\boxed{r=0\quad\Longleftrightarrow\quad
 \forall p\text{ prime}\ \forall n\ge1\ \forall N_0\ \exists N\ge N_0:
 |b_N(pn)-b_N(n)|\le L\log p\,(6+\log(pn))^m.}
\]
The stage N may depend on p, n, and N_0. There is no requirement that one
subsequence work for every edge, that all stages obey the bound, or that an
entire CRT period be controlled at one stage.

In particular, set m=0 and L=1 to obtain the especially simple exact target
\[
 \forall p\text{ prime},n\ge1,N_0\ \exists N\ge N_0:
 |b_N(pn)-b_N(n)|\le\log p.
\]

Declarations in namespace `RiemannResearch.RH.QSquarefreePrimeIncrement`:

- `residual_zero_iff_frequently_moving_prime_increments` is the exact criterion.
- `riemannHypothesis_of_frequently_moving_prime_increments` is its RH consumer.
- `residual_zero_iff_correction_prime_increments` is the corresponding exact
  criterion directly on b (L>=0 is permitted there).

Only r=0 implies RH is used. No converse from RH to squarefree density is claimed.

## Proof of the sufficient direction

First pass each fixed edge inequality to the coordinatewise limit. Cofinality
is sufficient: a strict violation by the limit would make all sufficiently
late stages violate the same closed upper bound.

For an arbitrary real sequence f, the new elementary theorem proves
\[
 |f(pn)-f(n)|\le L\log p(6+\log(pn))^m\ \text{ for every prime edge}
\]
implies
\[
 |f(n)-f(1)|\le L\log n(6+\log n)^m,
\qquad
 |f(n)|\le(|f(1)|+L)(6+\log n)^{m+1}.
\]
Strong induction chooses a prime divisor of n. The smaller cofactor stays
positive, its logarithmic weight is no larger than the weight at n, and
log(pn)=log p+log n. Repeated prime factors are fully included.

Apply this with f=b. The existing `exists_log_scaled_tail_bound_of_polylog`
gives a bounded logarithmically scaled complete tail, with exponent 2m+4.
The existing squarefree logarithmic-tail dichotomy then forces r=0, and the
checked Q-to-Pareto bridge gives RH.

For necessity, r=0 makes b=0. Each fixed prime increment of b_N tends to zero,
while its chosen allowance is strictly positive. The inequality eventually
holds for that edge, hence holds cofinally.

## Verified obstruction alternative

For every m>=0 and L>=0, if r is nonzero, there are a **fixed** prime p and
positive integer n such that
\[
 |b_N(pn)-b_N(n)|>L\log p(6+\log(pn))^m
\]
for every sufficiently large N. This is
`eventually_large_moving_prime_increment_of_residual_ne_zero`.
The limiting version is `exists_large_prime_increment_of_residual_ne_zero`.
These are unconditional implications; they do not assert that r is nonzero.

## Exact averaging identities

In a real Hilbert space, let P be the orthogonal projection onto V and C the
orthogonal projection onto W. Suppose h belongs to V and Ch=alpha u. Put
r=u-Pu. The new general module proves
\[
 (CP-PC)h=\alpha r,\qquad
 \|(CP-PC)h\|^2=\alpha^2\|r\|^2,
\]
and retains the exact signed pairing before estimating it:
\[
 \langle(I-C)r,(I-C)h\rangle=-\alpha\|r\|^2,
\qquad
 \alpha^2\|r\|^4\le\|(I-C)r\|^2\|(I-C)h\|^2.
\]
For alpha nonzero, either vanishing commutator on this one witness or
invariance of this one residual is equivalent to u belonging to V.

The prime-two paper identification has h=g_2, u=1, alpha=3/8, and
norm-square of (I-C_2)g_2 equal to 3/64. The numerical specialization is
Lean-verified **with those two averaging identities as explicit premises**:
\[
 3\|r\|^4\le\|(I-C_2)r\|^2.
\]
The arithmetic realization of C_2 is still a paper application, not a new
verified probability operator. The formula explains why assuming averaging
invariance would already assume a condition sufficient to close the problem.

## Further paper strengthening: arbitrary near-pole polynomial growth

The exponent alpha<1 in the handoff is needed only for its fixed exponent-two
profile. The repository permits all integer profiles
\[
 a_k(n)=\frac{n}{(k+6+\log n)^k},\qquad k\ge2.
\]
Writing F(t)=E_{Q_{1+t}}[b^2], the Laplace identity and Tonelli give
\[
 E_{Q_2}[a_kb^2]=\frac1{\zeta(2)\Gamma(k)}
 \int_0^\infty t^{k-1}e^{-(k+6)t}\zeta(1+t)F(t)\,dt.
\]
Since 1<=t*zeta(1+t)<=1+t, its near-zero integrability is equivalent to
integrability of t^(k-2) F(t). Consequently **any fixed finite** alpha>=0
in F(t)<=C t^(-alpha) suffices: choose k>alpha+1. A common bound for b_N
at cofinally many stages passes to b by Fatou for each t.

Likewise, the covariance differential inequality in the handoff is sufficient
with any fixed finite alpha>=0, provided it holds for all 1<s<2 at each
selected stage in a cofinal stage set. Integrating
F_N'(s)>=-alpha F_N(s)/(s-1) yields
F_N(1+t)<=F_N(2)t^(-alpha); the all-profile theorem absorbs the resulting
polynomial growth. No such covariance bound has been proved for the actual
canonical projections.

Another elementary paper simplification: a finite stretched-exponential
moment M=E_Q exp(kappa |b|^p), p,kappa>0, gives at every positive integer
\[
 \kappa|b(n)|^p\le\log(\zeta(2)M)+2\log n.
\]
This follows from bounding one positive summand by the whole expectation.
It directly gives a polylog envelope, so an Orlicz inequality is unnecessary.

## Wolfram diagnostics

The symbolic checks returned Gamma(k)/(c+log n)^k for the Laplace integral,
d[t^alpha F(t)]/dt=t^(alpha-1)(alpha F(t)+t F'(t)), and geometric unequal-copy
probability 2q/(1+q). These are diagnostics, not Lean verification.

For the complete Q Gram projection with all squarefree conductors 2<=d<=D,
Wolfram used exact period sums through polygamma functions, evaluated to 35
digits. The displayed maximum checks only p in {2,3,5,7} and 1<=n<=100.

| D | Number of legal atoms | Residual norm squared | Sample max of abs(b_D(pn)-b_D(n))/log p |
|---:|---:|---:|---:|
| 2 | 1 | 0.250000000000 | 0 |
| 3 | 2 | 0.068685282485 | 0.013772836214 |
| 5 | 3 | 0.027236901036 | 0.013058857559 |
| 7 | 5 | 0.017257969991 | 0.036774513210 |

No tail-truncated Gram matrix was substituted for the Q inner product.
These small computations neither establish uniform control nor test every edge.

## Research obligations

1. **Open:** prove a fixed-edge cofinal logarithmic increment allowance for the
   actual canonical moving corrections. The new exact theorem identifies the
   precise quantifiers sufficient for RH.
2. **Open:** establish a canonical-Gram estimate on the actual smoothed forcing;
   abstract projection contraction alone does not establish it.
3. **Open alternative:** prove a finite polynomial near-pole bound, or its
   covariance provider, with any fixed exponent. The restriction alpha<1 can
   be removed by changing logarithmic profile.
4. Formalize the actual countable prime-resampling kernel and its Poincare
   inequality if that route provides useful estimates. The current local
   increment criterion avoids requiring that probability infrastructure.
5. Preserve the distinction between the exact unproved provider and the
   already verified implication from that provider to residual vanishing.

Primary probability reference checked during this continuation:
L. Decreusefond and H. Halconruy, *Malliavin and Dirichlet structures for
independent random variables*, https://arxiv.org/abs/1707.07915 . This supports
the countable-product Poincare framework, not a weighted stability estimate
for these squarefree projections. The new arithmetic increment arguments are
direct derivations from the user-supplied agenda and existing repository results.

## Additional paper results on the actual projection forcing

Two complete paper proofs are saved alongside this memo. They have not been
formalized or certified by the Lean checkpoint.

- `SingleConductorProjectionBound.md`: for every fixed finite legal space U,
  adjoining an arbitrary conductor d gives
  abs(P_(U+span(g_d)) B (I-P_(U+span(g_d)))1(n)) <= C_U (1+log n),
  uniformly in d and n. It follows that each logarithmic weight of exponent
  k>3 has a common energy bound for this one-conductor family. The constant
  depends on U; controlling that dependence over canonical stages remains open.
- `LegalSubspaceProjectionObstruction.md`: for prime d>3, take
  W_d=span(g_2, g_3+10 sqrt(d) g_d). With the actual residual and forcing,
  raw resampling energy is at most 1/128, while projected weighted energy
  grows at least as a positive constant times d/(8+log d)^2. Prime-two
  increments also diverge. This disproves a transfer estimate based only
  on legal squarefree subspaces, parity inclusion, and orthogonal projection.
  It does not refute the canonical initial spans, which contain g_3
  independently.

Together they identify the remaining analytic issue more narrowly:
one remote conductor is controllable over a fixed prior space, while
generic legal-subspace arguments are insufficient. The canonical growing
Gram geometry is the part that still needs a uniform estimate.
