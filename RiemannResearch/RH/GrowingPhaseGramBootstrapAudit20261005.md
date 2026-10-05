# Growing-support phase Gram bootstrap: audit and strengthening

Source base: `9aad406831dd6b017a6cb592e07b22a2389cd4cc`.
Research continuation requested 4 October 2026.
This note supersedes the estimates in `UnverifiedHorizontalBootstrapRoute20261004.md`.
The source review and the mathematical argument below are paper-level work.
The abstract normed-algebra commutator series and bootstrap are separately
formalized in `Analysis/HorizontalPhaseBootstrap.lean`. Euclidean moment
centering, the actual finite-copy moment provider, masked signed corrections,
weighted actual zero contours, sharp eventual count normalization, complete
actual operator identity, strict finite layer cake, actual right-contour
Dirichlet-series formula and full-integer arithmetic operator bounds are now
checked; see `ActualZetaAnalyticProviderAudit20261005.md`. The quantitative
full-contour Landau and actual zero-density providers remain Open. The weighted
bad-tail transfer is checked under its explicit actual density premise.

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
of that premise is proved in HorizontalEuclideanMoments.lean. The exact
actual-zero expansion is `landauGram_sub_phaseGram` in ActualZeroPhaseOperators.lean;
its actual centered log diagonal has norm exactly log(d)/2 for d>=1.

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

The complete bad family has a checked exact finite cosh-correction identity.
Positive rank-one moment centering gives the sharper unconditional finite bound

    beta <= d/(2N) sum_bad [cosh(|a|ell)-1]
         <= d/(4N) sum_bad exp(|a|ell).

The checked strict finite layer cake retains e^(ell*delta) B_>(delta) and the
upper endpoint 1/2. It identifies B_>(s) exactly with twice the right strict
tail and dominates it by the paper's inclusive count. Under the explicit
actual density input and the now-sharp N(T)>=c0 T L eventually, if
A=(4/3)L-ell>0,

    beta := ||H_bad-G_bad||
       <= (100/c0)*d*L^2*
          [(1+ell/A)*exp(-A*delta) - (ell/A)*exp(-A/2)].

The checked count family permits any c0<1/(2*pi), so the leading coarse
coefficient can approach 200*pi. The old 1/(16*pi) normalization gave 1600*pi.

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

The checked Euclidean arithmetic provider now gives, for d>=1,

    log(d)-2 <= ||A_d|| <= log(d)+log(4)+4.

It retains every integer frequency and all composite divisor interactions.
The lower bound uses the exact weighted row on w_n=n^(-1/2), so the leading
log(d) term is real and cannot be replaced by a bounded prime-only direct sum.
Weighted Schur with weights n^(-1/2) gives the stated upper bound.
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
norm absorption and a Banach-algebra invertibility consumer. The actual
specialization discharges the centered-moment and full signed identity
providers; its Landau and bad-copy norm estimates remain explicit premises.

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

1. The uniform centered Landau formula with rational-frequency remainders.
   The actual zeta right-line series interchange, integer resonance split and
   nonresonant norm bound are Established; horizontal and left contour estimates
   and transfer to arbitrary heights remain Open.
2. Uniform actual zero density. The exact strict finite layer cake, reflection
   bridge and density-to-cosh-tail transfer are Established; their quantitative
   actual density premise remains Open.
3. The asymptotic support and spectral eigenvalue assembly.

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

## Stronger finite tail transfer and smaller remaining density target

The exact finite cosh tail factor keeps both q-ell and q+ell endpoints, rather
than bounding cosh by a single exponential at the outset. Under
B_>(s)<=K*exp(-q*s), q>ell>=0, the checked transfer is

    sum_bad[cosh(ell*|a|)-1] <= K*F,
    F=(cosh(ell*delta)-1)*exp(-q*delta)
      +(ell/2)*[(exp(-(q-ell)*delta)-exp(-(q-ell)/2))/(q-ell)
               -(exp(-(q+ell)*delta)-exp(-(q+ell)/2))/(q+ell)].

For q=4L/3 and delta=(ell+p*log L)/(q-ell), this gives a smaller bad budget
than the coarse exponential formula. At ell=o(sqrt L), the additional small
cosh factor allows p=2 for the paper-level isotropy conclusion. This asymptotic
analysis still depends on the actual density and Landau providers; it is not
presented as a hypothesis-free Lean theorem.

Only the near-line range 0<=s<=1/32 is necessary on the sqrt L support scale.
Splitting layer cake there and bounding the farther count by B_>(1/32) gives
an exponentially small farther contribution, O(exp(-L/24+O(sqrt L))). The
first interval in Chourasiya--Simonic Table 1 has leading constant 5.069;
reflection yields leading coefficient 10.138 after the additive logarithmic
terms are retained and absorbed eventually. This improves constants without
requiring a new large-sigma density formalization. The actual analytic density
proof remains Open.

Wolfram checked the closed finite cosh integral and the value of c_star.
These symbolic checks support the calculations above; Lean verifies the exact
finite identities and explicit-premise transfer declarations separately.
