# Growing-support phase Gram bootstrap: audit and strengthening

Source base: `be751019201ab4f48e41c2e46b750e3c2edb63ac`.
Research continuation requested 4 October 2026.
This note supersedes the estimates in `UnverifiedHorizontalBootstrapRoute20261004.md`.
The source review and the mathematical argument below are paper-level work.
The abstract normed-algebra commutator series and bootstrap are separately
formalized in `Analysis/HorizontalPhaseBootstrap.lean`. Euclidean moment
centering, the actual finite-copy moment provider, masked signed corrections,
weighted actual zero contour and eventual count normalization are now checked;
see `ActualZetaAnalyticProviderAudit20261005.md`. The quantitative Landau,
density, weighted bad-tail and complete operator-series providers remain Open.

## Full dictionary and exact reflection identity

Let N=N(T) count every complex nontrivial zero rho=beta+i gamma with
0<gamma<=T, including its analytic multiplicity. For d=floor X and 1<=n,m<=d,

    G_nm = N^(-1) sum_rho (n/m)^(i gamma),
    H_nm = N^(-1) sum_rho (n/m)^(rho-1/2).

G is a positive semidefinite Hermitian Gram matrix. All norms in this note
are Euclidean operator norms. A default entrywise matrix norm cannot replace
them. The full integer dictionary includes primes, prime powers, and every
composite integer. It is distinct from the physical Pareto residue Gram.

Set L=log T, ell=log X, D=diag(log n-ell/2), a_rho=beta-1/2, and
v_rho=(n^(i gamma))_n. Reflection rho -> 1-conj(rho) preserves gamma and
multiplicity and changes a_rho to -a_rho. For a symmetric good cutoff
|a_rho|<=delta, define

    M_k = N^(-1) sum_good a_rho^(2k) v_rho v_rho*.

Then 0<=M_k<=delta^(2k) G in Loewner order and, exactly,

    H_good-G_good = sum_(k>=1) ad_D^(2k)(M_k)/(2k)!,
    ad_D(M)=DM-MD.

This follows by expanding exp(aD) v v* exp(-aD) and pairing reflection
copies. Finite zero cutoffs permit absolute convergence and exchange with the
finite zero sum. No odd moment, multiplicity, or bad-copy term is discarded.

## Sharp factor one-half

For 0<=M<=bI, the spectral theorem gives
||M-(b/2)I||<=b/2. Positive commutator powers annihilate scalar identities.
Since 2||D||<=ell,

    ||ad_D^j(M)|| <= ell^j b/2,  j>=1.

Use b=delta^(2k)||G|| and sum the actual even series to obtain

    ||H_good-G_good|| <= epsilon ||G||,
    epsilon = [cosh(delta ell)-1]/2.

The factor 1/2 is sharp. In two coordinates take
G=[[1,1],[1,1]], D=diag(-ell/2,ell/2), and equal reflected defects +/-delta.
Then H=[[1,cosh(delta ell)],[cosh(delta ell),1]], so ||H-G||=cosh(delta ell)-1
while ||G||=2. H_good need not be positive; positivity is used for M_k.

The Lean theorem `evenCorrection_summable_and_norm_le` proves absolute
summability and this bound in an arbitrary complete real normed algebra
from the explicit centered-moment norm premise. It does not silently assume
that a Lean matrix norm is the Euclidean operator norm. The PSD implication
of that premise and the exact actual-zero commutator expansion remain to
be instantiated formally.

## Uniform density and the optimized cutoff

Chourasiya--Simonic, arXiv:2507.15184v2, Corollary 1 and its proof, give a
uniform estimate including shrinking sigma-1/2. Their range near the line
explicitly covers sigma-1/2<=0.28/log T. Counts include all multiplicities.
For T>=3*10^12 and 0<=s<=3/8, the tabulated constants and exponent imply

    N(1/2+s,T) <= 200 T^(1-4s/3) L^3.

Indeed the main exponent is 1-2s/(3/2-s)<=1-4s/3 and is at least 1/3.
The coordinatewise maxima sum to 21.77+9.461+167.8=199.031<200, so the
additive L^2 and L terms are absorbed. For 3/8<=s<=1/2 use monotonicity
at sigma=7/8 and 1-4s/3>=1/3. Reflection gives

    B(s) = # {copies with |a_rho|>=s}
         <= 400 T L^3 exp(-(4/3)L s).

For a bad copy, the centered rank-one operator has norm at most d exp(|a|ell)
and its unweighted Gram term has norm d. Therefore the difference is at most
2d exp(|a|ell). Retain this factor in the unspecified absolute constant.
Using N(T)>=c0 T L eventually and Stieltjes layer cake, if
A=(4/3)L-ell>0,

    beta := ||H_bad-G_bad||
       <= C d L^2 exp(-A delta) (1+ell/A).

For any fixed r>0 choose

    delta = [ell+(2+r)log L]/A.

Whenever ell=O(sqrt L), delta lies in [0,1/2] eventually and beta=O(L^(-r)).
This improves the earlier numerator 2ell+4log L. In particular r=2 works.

Primary source: https://arxiv.org/pdf/2507.15184 .
Ford--Zaharescu Lemma 2 also gives a uniform Selberg estimate
N(sigma,T)<<T^(1-(sigma-1/2)/4)log T; it gives a less favorable explicit
critical-scale coefficient and is not needed for the 4/3 rate here.

## Centered Landau provider and a sharper remainder

Ford--Zaharescu, *On the distribution of imaginary parts of zeros of the
Riemann zeta function*, Lemma 1, equation (3.1), is uniform for x,T>1:

    sum_(0<gamma<=T) x^rho
      = -Lambda(n_x)/(2pi)
          [exp(i T log(x/n_x))-1]/[i log(x/n_x)]
        + O(x log^2(2xT)+log(2T)/log x),

with the main fraction replaced by T when x=n_x, the nearest prime power.
Use it directly for H, without presuming horizontal weight removal.
For 2<=X<=T write, exactly,

    H = I - [T/(2pi N)] A + R,
    A_nn=0,
    A_nm=Lambda(x)/sqrt x, x=max(n,m)/min(n,m).

Lambda(x) is zero off integer prime powers; R is defined by the equality.
Reflection makes H Hermitian. With a=max(n,m), b=min(n,m) and x=a/b,
a nonresonant nearest prime power k obeys k<=2x and

    |a-bk|>=1,
    |log(x/k)|>=1/(2a).

The nearest-prime-power error after division by sqrt x is at most
C sqrt(nm) log(2x). The complete entrywise remainder is bounded by

    (C/N)[sqrt(nm)log(2x)
          +sqrt x log^2(2xT)
          +log(2T)/(sqrt x log x)],  n!=m,

and R_nn=0. The three majorant matrices have norms respectively
O(X^2), O(X sqrt(log(2X))) and O(X log(2X)): use absolute row sums for
the first and third, and the Hilbert--Schmidt norm for the second.
For the first, after splitting m<n and m>n, the terms log2 have row sum
O(X^2), while sqrt(t)log(1/t) is bounded on (0,1].
For the third use 1/(sqrt x log x)<=sqrt(nm)/|n-m|.

Weighted Schur with weights n^(-1/2) gives ||A||<=log X+C.
The downward divisor sum is sum_(q|n) Lambda(q)=log n, and the upward
multiples sum is sum_(q<=X/n) Lambda(q)/q<=log(X/n)+C.
Consequently

    alpha := ||H-I||
      << ell/L + X^2/(T L)
           + X sqrt(log(2X)) L/T + X log(2X)/T.

The original, coarser bound was safe. This sharper estimate still concerns
the centered zero phase Gram, not the decisive screened Pareto inverse.

Primary source: https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .

## Exact norm absorption and conditioning

Let tau=alpha+beta and epsilon=[cosh(delta ell)-1]/2. The complete signed
decomposition is H-G=(H_good-G_good)+(H_bad-G_bad). Hence, for epsilon<1,

    ||G-I|| <= (tau+epsilon)/(1-epsilon),
    lambda_max(G) <= (1+tau)/(1-epsilon),
    lambda_min(G) >= (1-tau-2epsilon)/(1-epsilon).

The lower bound is positive when tau+2epsilon<1. Lean proves the abstract
norm absorption and a Banach-algebra invertibility consumer, retaining the
exact correction identity and bad-copy norm premise.

For ell=o(sqrt L), alpha,beta,epsilon ->0 and ||G-I||->0.
For ell/sqrt L -> c>=0, let q=cosh(3c^2/4). The optimized cutoff gives
delta ell ->3c^2/4 and epsilon ->(q-1)/2. Therefore if

    c < c_star = sqrt((4/3) arcosh 2)
               = 1.325120320033778...,

then the paper-level argument yields

    liminf lambda_min(G) >= 2(2-q)/(3-q) > 0,
    limsup lambda_max(G) <= 2/(3-q),
    limsup ||G^(-1)|| <= (3-q)/[2(2-q)],
    limsup condition_number(G) <= 1/(2-q).

These are limiting inequalities. Finite-height assertions must retain tau
and epsilon. Fixed c>0 proves uniform conditioning; it does not prove
||G-I||->0. The threshold is a sufficient constant, not an optimality claim.

## Verification scope and next concrete provider

Established abstract Lean results include scalar centering of every positive
commutator power, its factor-one-half bound, actual cosh-series absolute
summability, exact norm absorption, correction assembly, and invertibility
under an explicit strict gap. Source scans and kernel checks must precede
publication; the checkpoint is the publication record.

Open for the actual-zeta Lean specialization:

1. The actual-zero operator-series identity for the good correction and the
   complete complementary bad contribution. The Euclidean moment centering
   provider and scalar masked signed corrections are already Established.
3. The uniform centered Landau formula with rational-frequency remainders.
4. Uniform zero density and its weighted bad-copy tail.
5. The asymptotic support and spectral eigenvalue assembly.

Actual multiplicity cutoffs and reflection are already proved in
Analysis/ActualZeroOrdinate.lean; they are not new assumed providers.
The microscopic Fujii second-moment provider remains a separate marked-tail
formalization gap. Goldston--Lee--Schettler--Suriajaya arXiv:2503.15449v4,
Propositions 1--2 and (5.4)--(5.6), support its unconditional paper-level
O(N(T)) budget; this argument does not formalize it.

RH-equivalent signed inverse saturation, the decisive cofinal O(log N)
arithmetic estimate, and bounded-frequency signed marked cancellation remain
unproved. The phase Gram is a sampling matrix on zero ordinates; its inverse
bound cannot replace the screened physical Pareto inverse without a proved
transfer estimate.
