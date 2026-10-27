# Squarefree moment budgets: resampling obstruction and stage variation

Continuation of commit 39e1140d1b2f0fd67b96e67dfb11569aea81493f, checked against
the later main revision 6acdb532eef7ca1d811cf891681ee5d7abdb650b.
Source: the user's request to obtain a uniform finite-test exponential budget
from the actual squarefree normal equations and prime resampling.

No unconditional exponential budget or proof of RH is obtained. The new results
separate a useful Hilbert-space variation estimate from two invalid shortcuts:
commuting legal projection with dyadic conditional expectation, and treating
the actual canonical correction stages as a martingale.

## Objects and conventions

Q(n)=1/(zeta(2)n^2), n>=1. Set g_d(n)=(n mod d)/d, and let V_N contain all
squarefree g_d with 2<=d<=N+1, as in ZetaTwoOptimizerStage.stage. Thus a
conductor cutoff H corresponds to repository stage N=H-1. Set
r_N=1-P_N1, b_N=P_N B r_N, Bf(n)=f(n)/(n+1), V=closure of the union,
r=1-P_V1, and b=P_VBr. All norms, inner products, and infinite sums below
retain the complete Q law.

## Exact unconditional obstruction for dyadic resampling

Let f=C_2 g_3, where C_2 is the genuine conditional average over the 2-adic
valuation. The complete geometric sum gives

    f(1)=f(2)=f(4)=2/5,    f(3)=0.

For example, the residues of 2^k modulo 3 alternate between 1 and 2, so

    f(1)=(3/4) sum_{k>=0} 4^(-k) ((2^k mod 3)/3)=2/5.

Consequently the continuous square-jump functional

    L(f)=f(4)-f(3)-f(2)+f(1)

has value 2/5. The existing squarefree radical-difference theorem says that
L vanishes on W=closure(V+R1). Its Riesz witness w_2 has norm squared
30 zeta(2). The exact orthogonal decomposition is therefore, for every v in W,

    ||C_2 g_3-v||^2 = 2/(375 zeta(2))
       + ||C_2 g_3-v - w_2/(75 zeta(2))||^2.

In particular C_2g_3 is outside W. This strengthens the older observation
that C_2V subset V would imply RH: that whole-space invariance is actually
false, even if constants are allowed in the image. It does not contradict
the possible inclusion 1 in V.

For every closed legal subspace S subset W containing g_3,

    ||(C_2 P_S-P_S C_2)g_3||^2 >= 2/(375 zeta(2)).

Thus canonical P_N do not asymptotically commute with C_2 on all inputs.
A residual-specific estimate on B r_N remains possible.

Formal declarations are in QSquarefreeResamplingObstruction.lean. The final
publication response records the terminal server checkpoint; this note does
not turn an accepted or pending verification request into a verified result.

## New unconditional variation estimate: full paper proof

Skip zero innovations in the nested canonical spans, and choose a unit vector
u_j in each nonzero new direction. These vectors are orthonormal. Let P_j
denote the projection after adding u_j, a_j=<1,u_j>, and
c_j=<B r_j,u_j>. The exact signed update is

    r_j=r_{j-1}-a_j u_j,
    b_j-b_{j-1}=c_j u_j-a_j P_{j-1}B u_j.

Its two output terms are orthogonal. Hence, without dropping any cross term,

    ||b_j-b_{j-1}||^2=c_j^2+a_j^2 ||P_{j-1}B u_j||^2.

Self-adjointness of B and Cauchy-Schwarz give
c_j^2<=||r_j||^2||Bu_j||^2. Projection contraction gives
||P_{j-1}Bu_j||^2<=||Bu_j||^2. The exact residual energy split
||r_{j-1}||^2=||r_j||^2+a_j^2 therefore proves

    ||b_j-b_{j-1}||^2 <= ||r_{j-1}||^2 ||Bu_j||^2.

The one-step exact identity and factor-one inequality are formalized in
Analysis/SingleDirectionResponseDifference.lean. The following infinite-stage
assembly is a paper proof unless separately identified in the final report.

In normalized physical-coordinate space B is diagonal with eigenvalues
1/(n+1), n>=1. For any orthonormal family, Bessel's inequality and Tonelli give

    sum_j ||Bu_j||^2
      = sum_{n>=1} (n+1)^(-2) sum_j |u_j[n]|^2
      <= sum_{n>=1} (n+1)^(-2)=zeta(2)-1.

Here u_j[n] denotes the normalized Hilbert coordinate, not the unweighted
physical value. After g_2 is included, ||r_j||^2<=1/4. The zero stage and the
first parity stage both have b=0. Thus, also with the original masked indexing,

    sum_{N>=0} ||b_{N+1}-b_N||_Q^2 <= (zeta(2)-1)/4.

There is a stronger convergence conclusion. The series sum_j c_j u_j is an
orthogonal square-summable series, since sum c_j^2<infinity. The other part
is absolutely summable in Hilbert norm:

    sum_j ||a_j P_{j-1}Bu_j||
      <= (sum_j a_j^2)^(1/2) (sum_j ||Bu_j||^2)^(1/2)<infinity.

Therefore sum_N (b_{N+1}-b_N) is unconditionally summable in QHilbert.
This is deterministic orthogonal-series reasoning, not an application of
the probabilistic three-series theorem. It supplies no exponential budget.

For comparison, f_N(n)=1_{n<=N} exp(sqrt(log(n+1))) has orthogonal square-summable
increments in L2(Q), bounded individual stages, and infinite limiting
positive stretched exponential moments for every positive stretch exponent.
Indeed f belongs to every finite Lp(Q), whereas exp(kappa*f^alpha)/n^2
does not tend to zero for any kappa,alpha>0. This example is not an actual
squarefree projection; it explains the limitation of the variation argument.

## Computer-assisted obstructions for actual canonical stages

The scripts embedded in SquarefreeMomentDiagnostics20261027.md use directed
Decimal arithmetic and elementary
infinite-tail bounds. These are reproducible computer-assisted certificates,
not Lean kernel proofs. NumPy/SciPy supply candidate inverses and coefficients
only; interval residual bounds certify those candidates independently of
special-function accuracy.

At cutoff H=17 (stage 16), they certify the rational bounds

    |b_16(296581)| > 91/2000,
    sup_{n>=1}|B r_16(n)| < 417/10000.

Taking kappa=10000, the exponent gap is greater than 38. Moreover zeta(2)<2
and the exact integer inequality

    36^20 > 2*296581^2*20!

proves exp(36)>2*296581^2. One atom of the correction moment therefore exceeds
the complete raw-source upper bound:

    E_Q exp(10000 |b_16|) > E_Q exp(10000 |B r_16|).

Thus a blanket exponential Jensen contraction for P_N on these very inputs
is false. This does not refute a common budget for some smaller fixed kappa,
or a bound with a larger multiplicative/additive constant.

At cutoff H=2 (stage 1), parity gives b_1=0 exactly. At cutoff H=3 (stage 2),
the second certificate gives

    -0.003846961740 < sum_{n>=1} b_2(n)/n^2 < -0.003846959801.

In particular E_Q b_2<0=E_Q b_1. The full sequence b_N cannot be an integrable
martingale for any filtration, since a martingale has constant expectation.
This does not rule out constructing a different martingale for each fixed N.

### Complete-tail computation and interval justification

Let L be a common period. For 1<=a<=L, the full progression weights are

    w_L(a)=psi_1(a/L)/(zeta(2)L^2),
    v_L(a)=w_L(a)+(psi(a/L)-psi((a+1)/L))/(zeta(2)L).

The first is sum Q(a+kL), the second is sum Q(a+kL)/(a+kL+1).
These give exact finite formulas for the complete Gram matrix G, the
B-weighted Gram matrix K, and target/source vectors v,s. Solve

    G c=v,    G beta=s-K c.

Then b_N(n)=sum beta_d g_d(n), and the complete exponential moment is
sum_{a=1}^L w_L(a) exp(kappa |b_N(a)|). The polygamma identity used in the
floating-point diagnostic is NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15.E1.

The certificates do not assume special-function error bounds. They enclose
unnormalized progression sums by rational partial sums and the following
elementary bound. For f(t)=(a+Lt)^(-p), x=a+KL,

    integral_K^infty f + f(K)/2 <= sum_{k>=K} f(k)
      <= integral_K^infty f + f(K)/2 + pL/(8x^(p+1)).

Indeed, the trapezoidal error on each unit interval is
(1/2) integral_0^1 t(1-t)f''(k+t)dt, between zero and (1/8) integral f'';
sum the intervals. For the reciprocal B weight use S_3-S_4<=S_B<=S_3.
Forty-five-digit outward rounding encloses all operations. The approximate
inverse is certified by ||I-AG||_infinity<1, so
||G^(-1)||_infinity<=||A||_infinity/(1-||I-AG||_infinity).
For H=17 the inverse defect is below 3.154e-9. Residual bounds then give
global coefficient error bounds. Raw-source sites n<1000 are checked with
interval arithmetic; the entire remaining tail is bounded by
(1+sum |c_d|)/(n+1), with the certified coefficient uncertainty included.

### Floating-point evidence only

For kappa=1, complete moments at cutoffs H=3,5,7,10,13,14 are approximately
1.004400599105, 1.005557733212, 1.007375412849, 1.007321738484,
1.007530470726, 1.006800460254. They are not monotone. At H=3 the head
n<=100 gives only 0.998330730351; its omitted tail is about 0.006069868754.
This illustrates why a truncated physical sum cannot certify a complete budget.

## Precise surviving arithmetic obligation

The existing finite-test criterion still requires one kappa>0 and one finite
M such that for every finite S and every N0 some N>=N0 satisfies

    sum_{n in S} Q(n) exp(kappa |b_N(n)|) <= M.

No estimate above supplies it. The remaining problem is control of the
pointwise amplification of the full canonical projection on the special
source B r_N, uniformly as the conductor set grows. Legality, Hilbert norm
contraction, finite quadratic variation, and conditional averaging alone
do not discharge this obligation.

A useful next target is a canonical, signed estimate on the rank-one update
c_j u_j(n)-a_j P_{j-1}Bu_j(n). A common logarithmic envelope of the summed
updates would imply a small positive exponential budget, but remains Open.
Estimating the absolute terms separately may lose the cancellation needed.

Under Q the prime valuations are independent geometric variables and
sum_p P(v_p(X)>0)=sum_p p^(-2)<infinity. Their log expansion for log X is
almost surely finite. The three-series theorem addresses convergence of
independent series, not exponential integrability of b(X). See Durrett,
Probability: Theory and Examples, fifth edition, Theorem 2.5.8:
https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf.
For example X^a is in L2(Q) for 0<a<1/2 but has no positive stretched
exponential moment. An actual growth or conditional-increment estimate on
b_N is essential before using this probabilistic route.

## Verification and scope ledger

- Saved-module Lean verification: exact resampling obstruction and noncommutation; exact
  one-step response energy and factor-one bound; complete Bessel budget and
  generic finite-family variation budget with displayed hypotheses.
- Paper proof: the infinite canonical variation budget and unconditional
  summability, using the actual diagonal multiplier and orthonormal innovations.
- Directed-arithmetic certificates: failure of exponential contraction at
  stage 16, and failure of martingale mean preservation at stages 1 and 2.
- Floating-point diagnostics: the listed complete moments.
- Open: the requested common finite-test exponential budget, r=0, and RH.

Saved-module audit job_ZR8dQQ_IdhfgyM72z-TYXI36kVUuDxj- succeeded with
verified=true and exit code 0. It imported the saved resampling and
finite-variation modules, inspected three principal declaration types, and
audited four principal axiom dependencies. Those dependencies were exactly
propext, Classical.choice, and Quot.sound. No proof placeholder or project-local
axiom was introduced.

The server reported 117.288 seconds for this successful verification, including
dependency preparation and module checking; this is not pure kernel time.
Its recorded queue delay was under 0.001 seconds. Workspace-opening request
latency was not separately instrumented. Client polling delay is separate from
the server verification duration.

The final server checkpoint and published commit are reported separately.
