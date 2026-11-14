# Parity residue convolution: theorem catalog and RH investigation

Started: 2026-11-13; completed: 2026-11-14. Input: G2_Dirichlet_Convolution_Pareto_Work_Analysis(1).md.
Workspace base: 9a4631b138d9c07b4fe8755aaa591cd906bc4ef7.
All arithmetic functions are extended by zero at 0. The measures on positive
integers are P(n)=1/(n(n+1)) and Q(n)=1/(zeta(2)n^2).
No density, RH, convolution-closure, or profinite-continuity assumption is
introduced into the new unconditional theorems.

## Lean results

The modules use the existing actual residue atoms, physical-sequence maps,
complete Hilbert inner products, and orthogonal projections.

| Module and namespace suffix | Main declarations | Result |
|---|---|---|
| NumberTheory/ParityResidueConvolution.lean; ParityResidueConvolution | residue_two_eq, paritySquare_eq, paritySquare_parity | h=g_2*g_2 is tau(n)/4 on odd n and zero on even n |
| Same | paritySquare_odd_prime_pow, paritySquare_three_pow, paritySquare_not_bounded | h(p^a)=(a+1)/4 for odd primes; h is unbounded |
| NumberTheory/ParityResidueConvolutionMoments.lean; DivisorSquareMoment | hasSum_square_succ_geometric, local_factor, divisor_square_sum | Independent summability and the exact divisor-square Euler product at s=2 |
| Same | odd_divisor_square_sum | Sum over odd n of tau(n)^2/n^2 = 3*pi^4/128 |
| Same; ParityResidueConvolution | paritySquare_exact_moment | Sum h(n)^2/n^2 = 3*pi^4/2048 |
| Same; DivisorSquareMoment | bounded_convolution_abs_le, bounded_convolution_moment | If abs(f)<=C and abs(g)<=D, C,D>=0, then abs(f*g)<=CD*tau and its inverse-square moment is at most (CD)^2*5*pi^4/72 |
| NumberTheory/ParityResidueLSeries.lean; ParityResidueLSeries | residue_two_hasSum, paritySquare_hasSum | Absolutely convergent Dirichlet-series formulas, with Re(s)>1 explicit |
| RH/ParetoParityConvolution.lean; ParetoParityConvolution | paritySquare_inv_sq_summable, paritySquare_pareto_summable, pTarget_sequence, qTarget_sequence | Actual P and Q vectors realizing h |
| Same | target_mem_q_iff_p | The same physical target has equivalent closed-span membership in P and Q |
| Same | pTarget_not_mem_atomSpan, no_continuous_compact_extension | No finite residue-atom representation and no continuous real-valued extension to any compact space along any map from N |
| Same | qTarget_norm_exact, pTarget_norm_bound | Q-norm squared 9*pi^2/1024; P-norm squared at most 3*pi^4/2048 |
| Same | atoms_independent, gram_posDef, fit_eq_projection | Actual finite Gram matrices are positive definite; inverse-Gram synthesis is the Q orthogonal projection |
| Same | residual_identity_exact, exact_saturation_iff | Exact residual and the equivalence of capacity saturation with h in V |
| Same | coefficient_target_two, coefficient_target_prime | Canonical coefficients are 1/2 at 2 and -1/4 at every odd prime |
| Same | coefficient_limit, coefficient_limit_signed_defect | Actual P-projection coefficients converge to coefficients of the full projection, retaining the signed defect |
| Same | all_coefficient_limits_iff_mem | Matching all canonical coordinates, at every m>1, is equivalent to h in V |

The full namespace prefixes are RiemannResearch.NumberTheory and
RiemannResearch.RH, respectively. paritySquare is an ArithmeticFunction real
product, hence Dirichlet convolution, not pointwise multiplication.

Lean stage n contains n atoms of conductors 2,...,n+1. Thus the note's V_N
corresponds to stage N-1. Stage zero is also included; there is no hidden
positive-capacity assumption.

Existing infrastructure reused includes QParetoEquivalence,
QCovarianceInvertibility, QFullResidueProjection, FiniteHilbertGramMatrix,
ExhaustiveProjectionWalk, ParetoDirichletExponential, and the actual
Möbius-difference continuous linear maps. The continuous Pareto step-function
realization and measure comparison are supplied by the existing project;
this change does not replace those definitions with abstract surrogate vectors.

## Strongest exact target

With G_N and b_N formed using the complete Q inner product,

    dist_Q(h,V_N)^2 = 9*pi^2/1024 - b_N^T G_N^{-1} b_N,

and

    h in V  iff  b_N^T G_N^{-1} b_N -> 9*pi^2/1024.

This is an equivalence, not a proof of the limit.

Let P_N be the actual P orthogonal projection onto V_N, P_V the full P
projection, and d=h-P_V h. Set c_m(f)=-[mu * Delta f](m). The new results give

    c_2(h)=1/2; c_p(h)=-1/4 for every odd prime p;
    lim_N c_m(P_N h)=c_m(P_V h)=c_m(h)-c_m(d).

Matching the target value for every m>1 is equivalent to d=0. Matching only
prime coordinates is not asserted to suffice. The prime limit -1/4 has an
explicit h-in-V hypothesis.

Unboundedness also rules out a continuous profinite representative of this
particular h. Hilbert convergence of periodic functions supplies no uniform
bound or continuity on a compact profinite space.

## Finite residue reduction and external interval evidence

These identities and numerical certificates are mathematical/external
computations; the finite residue reduction is not a new Lean theorem here.
For 1<=r<=L let A(L,r)=sum_{a>=0}(r+aL)^(-2). Periodicity gives

    G_jk = 1/zeta(2) * sum_{r=1}^{lcm(j,k)}
             {r/j}{r/k} A(lcm(j,k),r).

Expanding the divisor convolution and separating residue classes gives

    b_j = 1/(4*zeta(2)) *
          sum_{1<=r,s<2j; r,s odd} {rs/j} A(2j,r) A(2j,s).

This works even though h is not periodic. CRT may reorganize the compatible
residue classes; coprimality of j and k is not assumed.

The Python program in [ParityConvolutionExperiments20261113.md](ParityConvolutionExperiments20261113.md) chooses rational coefficients
using a floating solve, then independently encloses their full residual.
It uses 60-digit directed Decimal rounding, a Machin-formula enclosure for pi,
and 128 head terms in each residue class. For y=r+128L, the remaining tail is
between 1/(Ly) and 1/(Ly)+1/y^2. Signed linear and quadratic terms are retained.
The recorded computation used NumPy 2.3.5 and SciPy 1.17.0.
Conditioning is reported but is not trusted for the certificate: any fixed
coefficient vector gives an upper bound on the optimal residual.

| Largest conductor N | Numerical optimal squared residual | External upper bound on optimal squared residual |
|---:|---:|---:|
| 2 | 0.01540002083428 | 0.015401336 |
| 4 | 0.01130660890436 | 0.011308434 |
| 8 | 0.00718114440671 | 0.007183851 |
| 16 | 0.00474119941372 | 0.004745429 |

Exact decimal rational coefficients and interval endpoints are retained in
[ParityConvolutionExperiments20261113.json](ParityConvolutionExperiments20261113.json). The lower interval endpoint bounds only
that chosen approximant, not the optimum. Wolfram independently confirmed the
Euler-factor constants, parity identity through n=200, and the finite numerical
Gram residuals. Neither computation establishes an infinite-stage limit.

## Convolution stability

The new Lean bounded-convolution theorem supplies a useful sufficient
hypothesis for ambient square integrability; its conclusion is not membership
in V. In particular all pairs of bounded residue combinations have legal
ambient convolutions.

A smaller convolution-stable class is sum_{n>=1}|f(n)|/n<infinity:
the weighted l1 norm is submultiplicative by the absolute double-sum estimate.
Mathlib's LSeriesSummable.convolution at s=1 supplies the corresponding complex
summability theorem. This class is contained in H_Q, but does not contain g_2.

There is also a direct counterexample to closure of the whole ambient space
under convolution (paper-level derivation here, not Lean-checked in this
change). Fix a prime p, put f(p^a)=p^a/(a+1)^(3/4), and put f=0 off its powers.
Then

    zeta(2)*norm_Q(f)^2 = sum_{a>=0}(a+1)^(-3/2) < infinity,

whereas

    (f*f)(p^a)/p^a
      = sum_{j=0}^a [(j+1)(a-j+1)]^(-3/4)
      >= (a+1)^(-1/2).

Thus the square norm of f*f dominates the divergent harmonic series. Norm
equivalence transfers the counterexample to H_P. This alone gives no
unconditional conclusion about convolution closure of V. Combining it with
the published equivalence RH iff V=H_P gives the paper-level inference:
under RH, V is not an algebra under unrestricted Dirichlet convolution.
A proof for the special target g_2*g_2 must therefore use more than a universal
convolution-closure assertion.

## Published connections and unresolved RH step

Balazard identifies the weighted step-sequence space with D_0 and its atoms
with e_k-e_1/k. Proposition 10 gives RH iff the atom closure is the entire
space; consequently RH implies h in V. Proposition 11 uses the jump series
F_h(s)=sum Delta h(n)n^(-s), not the ordinary series of h. Its holomorphy
converse is posed as Question 2 in that paper. These literature statements
are not new Lean proofs of an RH bridge in this change.

The checked formula

    sum h(n)n^(-s) = (1/4)(1-2^(-s))^2*zeta(s)^2, Re(s)>1,

therefore does not settle membership. No implication h in V -> RH is proved.

Next precise obligation: prove the capacity deficit tends to zero, or prove
all actual P-projection coordinate limits match c_m(h), or exhibit an actual
annihilator with nonzero pairing. Finite decay, ambient legality, the formal
Möbius expansion, and the raw Dirichlet series do not provide that missing
arithmetic estimate.

## Sources

- Michel Balazard, An arithmetical function related to Baez-Duarte's criterion
  for the Riemann hypothesis, arXiv:1812.04309, sections 1-2, Propositions 10-11,
  Question 2. https://arxiv.org/abs/1812.04309
  Published chapter: https://doi.org/10.1007/978-3-030-61887-2_3
- Luis Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the
  Riemann hypothesis, Rend. Lincei Mat. Appl. 14 (2003), 5-11.
  https://arxiv.org/abs/math/0202141
- S. L. Hill, M. N. Huxley, M. C. Lettington, K. M. Schmidt,
  Some properties and applications of non-trivial divisor functions,
  Ramanujan Journal 51 (2020), 611-628, Remark 1.
  https://doi.org/10.1007/s11139-018-0093-9
- Mathlib, L-series convolution and Euler products:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Convolution.html
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EulerProduct/Basic.html

## Verification record

All four saved source modules compiled successfully with Bazel/BuildBuddy:
job_XLRdZ1UkxdFuEYqD1MiVMXVQdmolUpBj, exit code 0.
[Source acceptance](https://app.buildbuddy.io/invocation/c5b89072-966a-4e53-bb7c-aa07b192ba64).

A separate accepted snippet asserts the exact axiom output for 14 principal
declarations using #guard_msgs. Every audited list is precisely
[propext, Classical.choice, Quot.sound], with no sorryAx or local axioms:
job_DEkh9RBcpT3qeeWfGu_0CwxUxtrNMngO, exit code 0.
[Axiom audit](https://app.buildbuddy.io/invocation/db4215ee-2f94-4169-977a-6035f365cd7b).

The four modules contain 56 theorem declarations. The reproducible audit
source, exact source hashes, and evidence distinctions are retained in
[ParityConvolutionVerification20261113.json](ParityConvolutionVerification20261113.json).
This records focused source acceptance. The final checkpoint separately
records full-project acceptance and the published commit.
