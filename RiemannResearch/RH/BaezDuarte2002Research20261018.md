# Baez-Duarte 2002 audit, Bombieri smoothing, and reciprocal-cell energy

Date: 18 October 2026.

## Scope and sources

The uploaded nine-page paper is Luis Baez-Duarte, *A strengthening of the
Nyman-Beurling criterion for the Riemann hypothesis, 2*,
[arXiv:math/0205003v1](https://arxiv.org/abs/math/0205003), dated 28 March 2002
and posted 1 May 2002. All nine pages were read, and the normalization and
majorant displays on pages 4 and 5 were inspected visually.

The paper supplies the natural-dilation criterion and proposes Bombieri's
linear cutoff in equation (3.1). This update audits those arguments, preserves
their RH assumptions, and develops exact arithmetic and energy refinements.
It does not prove RH or claim an improvement of the best known asymptotic rate.

Related primary sources:

- Burnol, [arXiv:math/0202166](https://arxiv.org/abs/math/0202166), for the
  conditional critical-line ratio estimate and the finite-energy perspective.
- Balazard and de Roton, [arXiv:0812.1689](https://arxiv.org/abs/0812.1689),
  for a later improvement of the approximation estimate under RH.
- Bettin, Conrey, and Farmer,
  [arXiv:1211.5191](https://arxiv.org/html/1211.5191v1), Introduction and
  Theorem 1, for the historical bounds and the additional hypotheses in the
  optimal logarithmic asymptotic.
- Bagchi, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733), for the
  discrete Pareto formulation and squarefree refinement. See the existing
  `BagchiDilationEnergyResearch20261018.md` for its separate audit.

## Historical results and the precise analytic gap

Write rho_d(x)={1/(dx)}, chi=1_(0,1], and

    f_(epsilon,N) = sum_(d<=N) mu(d) d^(-epsilon) rho_d.

The paper proves RH equivalent to chi belonging to the closed natural-dilation
span. Under RH it establishes the two strong limits: first the cutoff N tends
to infinity at fixed sufficiently small positive epsilon, and then epsilon
tends to zero. Its quantitative construction takes epsilon=c/log log N and
obtains norm error O((log log N)^(-1/3)), hence squared error
O((log log N)^(-2/3)). Pointwise convergence alone supplies neither strong limit.

The later Balazard-de Roton result gives, under RH,

    d_N^2 << (log log N)^(5/2+delta) / sqrt(log N), for every delta>0.

Burnol's lower bound includes zero multiplicities squared. Bettin-Conrey-Farmer
obtain the matching 1/log N asymptotic for the Selberg polynomial assuming RH
and a bound on the reciprocal squared derivatives at the zeros. Their extra
hypothesis implies simplicity and is not a consequence of RH established here.
Thus the 2002 rate is not the appropriate target for a claim of a new best rate.

Three local corrections in the uploaded version should be made in a formal
translation:

1. Its unnormalized Mellin transform has Plancherel measure dt/(2*pi), whereas
   page 4 prints (2*pi)^(-1/2)dt.
2. The displayed majorant (1+|t|)^(-1+2*epsilon) is in L2 only for
   epsilon<1/4. Restrict to that range, which suffices, or choose the auxiliary
   growth exponent separately to cover a wider range.
3. Equation (2.9), for f_(2*epsilon,N), requires denominator d^(1+2*epsilon).

The phrase "now without the assumption" on page 5 refers to using the
functional-equation multiplier estimate after the Mellin identification.
That identification was obtained under RH. It must not be promoted to an
unconditional L2 statement for the explicit physical f_epsilon. Finite energy
for arbitrarily small positive dampings is already an RH-sufficient condition:
an off-critical-line zero creates a shifted Mellin pole for small damping.
The repository has this implication in `BurnolFixedDampingObstruction.lean`
and its Q transfer in `ZetaTwoDampedEnergyTransfer.lean`.

## Existing project results incorporated

The baseline already contains:

- Exact natural charge-tail and natural/centered approximation equivalence in
  `BaezDuarteNaturalApproximation.lean`; its squared-error centering factor is 2.
- The exact centered Pareto norm identity in `ParetoNymanNorm.lean` and
  `BaezDuarteCenteredBridge.lean`.
- Natural-order convergence and finite energy for damping epsilon>=1/2,
  including the endpoint, in the `DampedMobiusHalf*` modules.
- Genuine squarefree legality and P/Q closure transfer in
  `DampedMobiusSquarefreeClosure.lean`.
- Exact logarithmic Selberg taper identities in `ParetoSmoothing.lean`.
- The all-conductor and squarefree finite-energy RH consumers. Their
  small-damping arithmetic hypotheses remain open.

The new linear cutoff is distinct from the existing logarithmic taper.
No pre-existing conditional declaration is relabeled as unconditional.

## Bombieri's linear cutoff: the exact arithmetic term

For any arithmetic coefficient a(d), define

    F_(N,a)(k) = -sum_(1<=d<=N) a(d)(1-d/N) g_d(k),
    A_(N,a) = sum_(1<=d<=N) a(d)(1-d/N)/d,
    D_a(k) = sum_(m<=k) sum_(d|m) a(d),
    C_a(k) = sum_(m<=k) sum_(d|m) d*a(d).

For k<=N the exact identity is

    1-F_(N,a)(k) = 1-D_a(k)+C_a(k)/N+k*A_(N,a).

For a(d)=mu(d)d^(-epsilon), this is exactly the paper's proposed damped
linear cutoff after centering. The damping defect 1-D_a(k) is retained.
Both damping and taper preserve the vanishing of all nonsquarefree coefficients.

At zero damping D_mu(k)=1 for positive k, so

    1-F_N(k) = k*A_N+C(k)/N,
    C(k) = sum_(m<=k) sum_(d|m) d*mu(d).

Ordinary divisor switching also gives C(k)=sum_(d<=k) d*mu(d)*floor(k/d).
Multiplicativity identifies its inner divisor sum with product_(p|m)(1-p).
These latter reformulations explain the arithmetic but are not additional
declarations in this update unless explicitly listed below.

For 0<H<=N, put x_k=C(k)/k and let mean_H denote the arithmetic average;
Var_H is the unnormalized sum of squared deviations. Then

    sum_(k<=H) (1-F_N(k))^2/k^2
      = H*A_N^2 + (2*A_N/N)*sum_(k<=H) x_k
        + (1/N^2)*sum_(k<=H) x_k^2
      = Var_H(x)/N^2 + H*(A_N+mean_H(x)/N)^2.

For general damping the same exact variance identity uses

    R_(N,a)(k) = [1-D_a(k)+C_a(k)/N]/k,

and becomes Var_H(R)+H*(A_(N,a)+mean_H(R))^2. This exposes the necessary
arithmetic control while retaining the signed cross term. It is the finite
head of unnormalized Q energy. Complete probability-normalized Q error also
contains the infinite tail and is divided by zeta(2).

The signed term has no fixed sign: C(3)=-2 and C(95)=67. Wolfram independently
confirmed these exact integers. At N=2 the tapered seed is identically zero,
because conductor one gives the zero residue and the taper kills conductor
two. Thus smoothing cannot be assumed to improve every finite approximant.

## A sharper continuous-to-Pareto transfer

This section is an ordinary mathematical proof. The Lean status of its
components is specified separately below.

Let f=sum b_d rho_d be any finite real natural-dilation sum, A=sum b_d/d,
F(n)=-sum b_d g_d(n), and r(n)=1-F(n). Put

    E = integral_0^infinity |chi+f|^2 dx,
    P(n)=1/[n(n+1)].

Under t=1/x, and then t=n+u, integer conductors give the exact residual
r(n)+A*u on n>=1, 0<=u<1. On 0<t<1 the residual is A*t. Consequently

    E = A^2 + sum_(n>=1) integral_0^1 (r(n)+A*u)^2/(n+u)^2 du.

Each reciprocal cell has normalized density w_n(u)=n(n+1)/(n+u)^2. Its mean is

    m_n=n(n+1)*log((n+1)/n)-n,

and write v_n for its variance. The density is decreasing, so 0<=m_n<=1/2;
v_n>=0. One alternative proof of the upper bound uses

    log x <= (x-x^(-1))/2, x>=1,

whose difference has derivative (1-x^(-1))^2/2. The mean is identified by the
antiderivative log(n+u)+n/(n+u).

Since sum P(n)=1, the full error has the exact form

    E=sum_(n>=1) P(n)*[(r(n)+A*m_n)^2+A^2*(1+v_n)].

The cellwise identity

    5*[(r+A*m)^2+A^2*(1+v)]-4*r^2
      =(r+5*A*m)^2+5*A^2*(1-4*m^2+v)

has nonnegative right side when 0<=m<=1/2 and v>=0. Summing proves

    ||1-F||_P^2 <= (5/4)*E,
    ||1-F||_Q^2 <= [5/(2*zeta(2))]*E.

The second inequality uses Q(n)<=2P(n)/zeta(2). The tail charge A^2 is
essential: the apparent extra A^2 in each normalized cell sums to precisely
that charge, rather than creating an artificial error term. Squarefree
support is preserved because the transfer uses exactly the same coefficients.

There is a sharper ambient constant. If M=sum P(n)*m_n^2 and
V=sum P(n)*v_n, then K=1+M+V and the exact full energy is

    E=||r||_P^2+2*A*<r,m>_P+A^2*K.

Completing the square and applying Cauchy-Schwarz yields factor
K/(K-M)=1+M/(1+V)<=5/4. This is the optimal constant for the larger space
allowing arbitrary r in L2(P) and arbitrary A; optimality for the family of
finite legal combinations is not asserted. No numerical approximation to
this constant is needed for the proved 5/4 estimate.

## Lean declaration ledger and remaining obligations

`BombieriSmoothing.lean` contains the concrete finite arithmetic results:
`seed_head`, `damped_seed_head`, `damped_weight_eq_zero_of_not_squarefree`,
`moebius_seed_error`, `moebius_head_q_energy`, `moebius_head_q_variance`,
`moebius_head_q_variance_lower_bound`, and `head_q_variance`.
`seed_two_eq_zero` and the two exact signed-moment evaluations provide
finite certificates against unjustified monotonicity or fixed-sign arguments.

`BaezDuarteCellEnergy.lean` contains the reciprocal-cell mean bounds, its
integral identification, the exact scalar remainder, and the full infinite
weighted comparison `weighted_energy_le`. The comparison assumes ordinary
summability of the moment-energy expression and the stated mean/variance
bounds. It proves summability of the target energy as well as the inequality.

**Open formal integration:** identifying the complete existing `naturalError`
with this cell moment-energy model, including the reciprocal change of
variables, partition, and variance expansion. Therefore this update does not
claim that Lean has yet proved `centeredError <= (5/4)*naturalError`; the full
ordinary proof above and the checked component lemmas are distinct.

**Open analytic RH obligation:** prove finite canonical damped Q energy for
arbitrarily small positive epsilon, or prove a suitable complete smoothing
energy bound. The already checked finite-energy criterion would then imply
RH without requiring a common bound on all damping norms. The new finite
head identities and improved transfer constant do not discharge this step.

The next practical formalization step is the complete cell-partition bridge.
The next mathematical RH step is a signed arithmetic estimate controlling
both the variance/head term and the infinite tail; positive damping or CRT
alone does not supply it.

## Subsequent Lean result

[BaezDuarteNaturalCellTransfer](BaezDuarteNaturalCellTransfer.lean) identifies the full natural error with the reciprocal-cell integral, proves the signed charge quadratic, and gives an attained minimum over the conductor-one coefficient. Its centered-to-natural squared-error factor is strictly less than 6/5. Arbitrarily small actual approximation errors remain the analytic input needed for RH.
