# Finite moving corrections: complete-tail certificates and residual variance

25 October 2026. Source: the user's request to investigate commit
f9aacc3890c763589de22981ee87647447d0b416. Repository baseline inspected:
2f36e03ab444f75a0b55afe27a3a4adedeedb297.

## Conclusion and verification boundary

The expanding-head estimate remains open. No unconditional squarefree closure
or RH theorem is obtained. This investigation adds exact-rational numerical
certificates for every stage 1<=N<=127 and the two unconditional Lean
declarations `QShiftedReciprocal.movingCorrection_variance_exact` and
`QShiftedReciprocal.movingCorrection_variance_bound` in
`QShiftedReciprocalBounds.lean`.

The two declarations passed an isolated server check with no diagnostics
(job_bhHQQFixs_7JW7R0Gx1iZmKoxWCryi_B, 54.647 server-reported seconds).
The publication checkpoint is the final validation of the project edits.
The workspace-opening duration and time between polls were not separately
instrumented; the duration above is the server-reported snippet duration,
not total interaction time.
The exact-rational computation proves

    max_{1<=N<=127, 1<=n<=N} |b_N(n)| < 1/16.

Its outward upper bound is 0.06062571738925453, strictly below 0.0625.
The exact-rational numerical code is independently mathematically reviewed,
but it is not a Lean-verified numerical implementation. Floating diagnostics,
rational certificates, ordinary mathematical arguments, and conditional RH
reductions are identified separately below.

Current main already has the signed rank-one forcing decomposition, stronger
tail estimates, uniform conductor little-o, and Bessel estimates in
QSmoothedResidueAsymptotic, QSquarefreeForcingDecomposition, and
QSmoothedResidueBessel. The investigation reuses them; it does not claim to
introduce them.

## Actual stages and singular dictionaries

Write D for the conductor cutoff. Repository stage N=D-1 contains the masked
atoms g_d(n)=(n mod d)/d for 2<=d<=D. The tested physical head is 1<=n<=D-1.
Remove precisely the zero columns belonging to nonsquarefree d. The remaining
conductors are distinct and their atoms are linearly independent. The existing
declarations QCovarianceInvertibility.qResidue_linearIndependent and
QCovarianceInvertibility.qGram_posDef establish this structurally. No floating
rank threshold or unqualified inverse of the masked matrix is used.

If duplicate columns are introduced, combine their coefficients before solving;
restore a representative coefficient vector afterwards. Nullspace changes do
not alter either synthesized function. The repository's finite normal-equation
uniqueness results cover this more general singular representation.

An elementary proof also gives explicit coercivity. If f=sum_d c_d g_d and
f(0)=0, then

    Delta f(k) = sum_d c_d/d - sum_{d|k} c_d,
    c_d = -sum_{k|d} mu(d/k) Delta f(k),  d>1.

Let A be the atom evaluation matrix on sites 1,...,D; C the exact integer
coefficient-extraction matrix above; W=diag(Q(1),...,Q(D)). Then CA=I.
For L=C W^(-1) C^T, minimum weighted norm under Cf=c gives

    G >= A^T W A >= L^(-1),      G^(-1) <= L.

This is an ordinary mathematical argument, not newly formalized here. In
particular, writing sigma_2(d)=sum_{k|d} k^2,

    lambda_min(G) >= 1/[4*zeta(2)*sum_d sigma_2(d)].

Indeed each extraction coefficient is a difference of at most two Mobius
values; (a-b)^2<=2a^2+2b^2 gives L_dd<=4*zeta(2)*sigma_2(d).
For the unnormalized weight 1/n^2, omit zeta(2) from this bound.
This controls finite invertibility, but deteriorates with the dictionary.

## Signed arithmetic and the remaining amplification

All moments use the complete Q inner product. Set

    Gc=m,     G alpha=s=h-Hc,     b(n)=a(n)^T alpha.

Define u(n)=n/(n+1), A_N=<r_N,u>_Q, and
T_d(n)=d*floor(n/d)/(n+1). The exact identity is

    d*s_d = A_N - <r_N,T_d>_Q.

The tail starts exactly at n=d. Current main already proves the stronger
complete-tail estimate

    zeta(2)*d*|d*s_d-A_N|^2 <= ||1_{n>=d}r_N||_Q^2,

and uniform little-o over the actual convergent family of residuals. Also,
|s_d|<=||r_N||_Q/d follows directly from 0<=B g_d<=1/d.
These entrywise source bounds do not control the inverse Gram response.

For x_{N,n}=G^(-1)a(n), retain the exact signed decomposition

    b_N(n) = A_N * sum_d x_{N,n,d}/d
             - sum_d (x_{N,n,d}/d) <r_N,T_d>_Q.

One additional sufficient arithmetic assumption would be a uniform bound on
the first term and on this signed second term, for all n<=N. Bounding the two
terms separately is stronger than bounding their difference; no necessity is
claimed. Replacing the last sum by absolute values and individual tail
Cauchy bounds loses substantial information in the computations below.

For example at D=128, the actual head maximum is about .03837; the maximum
leading contribution is .00594, the maximum signed tail contribution .03348,
and the maximum absolute coefficient-weighted actual tail contribution .04280.
But bounding each tail pairing independently by Cauchy produces about 2.476.
At D=8 the analogous Cauchy bound is .455. Thus these experiments do not
support treating generic entrywise decay as a uniform stability estimate.
These decomposition diagnostics are floating results, not interval certificates.

## New exact residual variance identity

Let rho=||r_N||_Q^2>0, e=<r_N,Br_N>_Q, v=||Br_N||_Q^2,
beta=||b_N||_Q^2, and q=Br_N-b_N. For every real t,

    v = beta + 2*t*e - t^2*rho + ||q-t*r_N||_Q^2.

This equality retains all signed terms and the nonnegative remainder.
It follows from q perpendicular to b_N, r_N perpendicular to b_N, and the
norm-square expansion. Choosing t=e/rho yields

    v = beta + e^2/rho + ||q-(e/rho)*r_N||_Q^2,
    rho*beta + e^2 <= rho*v.

The exact arbitrary-t identity and division-free inequality are the new Lean
declarations named above. They have no RH or unresolved arithmetic premises.
They are useful unconditional control of total correction energy. They do not
bound physical evaluations uniformly because the evaluation norm grows with n.
With K_N(n,n)=a(n)^T G^(-1)a(n), one has the ordinary consequence

    |b_N(n)|^2 <= K_N(n,n)*(v-e^2/rho).

A uniform bound on this product would suffice, but remains an extra arithmetic
condition. The computed small beta does not by itself supply it. In fact, the
floating head bounds obtained from this scalar variance times the maximum
evaluation leverage are about .0526 at D=8, .1600 at D=32, .3962 at D=128,
and .6657 at D=256. This route does not prove the empirical constant 1/16
even at these finite stages; the actual head values are much smaller.

At D=128, floating diagnostics give beta=2.1981570e-5 and
v-e^2/rho=2.4713873e-5, versus the generic rho/16=3.9581889e-4.
At D=256 the corresponding values are 1.6821422e-5, 1.8692756e-5,
and 3.3378479e-4. The variance bound is materially sharper in energy.
For these diagnostics e uses the complete H matrix; v uses the first 100000
sites plus the explicit tail majorant
(1+sum|c_d|)^2/[3*zeta(2)*100000^3]. The double coefficients and finite sum
are not certified, so these are diagnostics only.

## Certified finite bound and the remaining proof obligation

Every stage N=1,...,255 was scanned with complete infinite-period Gram
formulas evaluated in float64. The largest observed head maximum was
.0604903245883 at N=95, n=95. This suggests testing the concrete conjecture
|b_N(n)|<=1/16 on every expanding head, but neither this constant nor any
stage-independent constant has been proved. The separate exact-rational
certificate establishes C=1/16 simultaneously for every 1<=N<=127. Stages
128<=N<=255 remain floating diagnostics. The floating scan itself is not the
certificate; the independent rational enclosure/solve calculation is.

Head maxima are nonmonotone, and correction coefficient l1 norms grow from
about .0835 at D=8 to 1.2992 at D=256. The Gram condition number grows from
about 42 to 88600. The relative signed cancellation
||h-Hc||_2/(||h||_2+||Hc||_2) decreases from about .00727 to .00279, but small
input cancellation alone does not imply a stable physical output.

The proof attempt therefore reaches a specific unresolved estimate: control
the actual signed inverse-Gram tail response, or an error-weighted residualized
kernel energy, uniformly in stage and head site. Existing source little-o and
Bessel estimates are already unconditional; the numerical data do not supply
the required arithmetic amplification bound. A finite check of C=1/16 is not
an induction step or an asymptotic theorem.

The strongest new unconditional formal result is the residual variance
identity and inequality. The strongest computational conclusion is the
certified common head bound C=1/16 for all stages 1<=N<=127, with all tails included.
The RH implication remains the conditional theorem
QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound.

## Primary references for the computational identities

- NIST DLMF 5.15.1: https://dlmf.nist.gov/5.15.E1 (trigamma series).
- NIST DLMF, Chapter 5: https://dlmf.nist.gov/5 (digamma/polygamma identities).
- The source commit and current repository modules supply the actual Q-space
  definitions and conditional RH bridge; no external source is used as a
  provider of the missing uniform estimate.


## Complete-tail computation and certification details

# Complete-tail finite squarefree correction experiments

The conductor cutoff is `D`; the repository stage is `N=D-1`. The nonzero dictionary is the set of distinct squarefree integers `2<=d<=D`. All matrices in the scripts use the unnormalized weight `1/n^2`; multiplying G,H,m,h by the common `1/zeta(2)` does not change c, alpha, F, or b. Reported residual and correction squared norms include this normalization.

## Exact infinite sums

For `L=lcm(a,b)` and `1<=r<=L`, define

- `W2(L,r) = sum_{k>=0} 1/(r+kL)^2 = psi_1(r/L)/L^2`;
- `WB(L,r) = sum_{k>=0} 1/[(r+kL)^2(r+kL+1)] = W2(L,r) + [psi(r/L)-psi((r+1)/L)]/L`.

Thus `G_ab=sum_r g_a(r)g_b(r) W2(L,r)` and `H_ab=sum_r g_a(r)g_b(r) WB(L,r)`. The vectors m and h use period a and one factor g_a. These expressions include the complete infinite tails. `numerical_correction.py` evaluates these expressions in IEEE double precision; that evaluation alone is not a rigorous enclosure.

## Exact-rational tail enclosure

`certify_correction.py` independently encloses the same weights with integer arithmetic at fixed scale `S=10^35`. It uses K=16 explicit periods and the Euler--Maclaurin correction through B14. Put `x=r+16L`.

For W2, the tail center is

`1/(Lx) + 1/(2x^2) + sum_{k=1}^7 B_(2k) L^(2k-1)/x^(2k+1)`.

For WB, put `f(x)=1/[x^2(x+1)]`. Its tail center is

`I(x)/L + f(x)/2 + sum_{k=1}^7 B_(2k)L^(2k-1)[x^(-2k-1) - (2k)^(-1)x^(-2k) + (2k)^(-1)(x+1)^(-2k)]`,

where `I(x)=1/x-log(1+1/x)` is enclosed by the alternating rational series from j=2 through j=24. The integral-series error is at most `1/[25 L x^25]`.

The Bernoulli remainder in either weight is bounded by

`(|B16| L^15)/x^17`, with `|B16|=3617/510`.

A justification of the single-next-term bound is important. The partial-fraction identity

`1/(1-exp(-y)) = 1/y + 1/2 + 2y sum_{m>=1} 1/(y^2+4 pi^2 m^2)`

and the finite geometric expansion of each denominator give an alternating remainder after B14 bounded by `|B16| y^15/16!`. Integrate against `exp(-xt) w(t)`, with `y=Lt`, where `w(t)=t` for W2 and `w(t)=t-1+exp(-t)` for WB. Since `0<=t-1+exp(-t)<=t`, the stated common bound follows. It is not justified merely by dropping an arbitrary Euler--Maclaurin remainder.

After summing L residues and multiplying by the atom product in [0,1], conservative entry radii are

`e2(L) = |B16|/[L 16^17] + 100 L/S`,

`eB(L) = e2(L) + 1/[25(16L)^25]`.

Each rational term is floored after multiplying by S. There are at most 62 such rounding contributions per residue including the final atom multiplication; the 100L/S allowance covers both signs. Every center and radius used in the solve certificate is an exact Python Fraction. No special-function floating result is trusted for the enclosure.

## Certified constrained solve

Redundant masked coordinates are removed exactly, not by a numerical rank threshold. Distinct g_d are linearly independent: for `F=sum c_d g_d`, `F(n)-F(n-1)=s-sum_{d|n}c_d` with `s=sum c_d/d=F(1)`. If F is zero, divisor induction gives every c_d=0. Thus the reduced complete-Q Gram matrix is positive definite. Retaining the original zero columns gives nonunique coefficient coordinates but the same unique physical functions F and b.

Let G0,H0,m0,h0 be the rational centers with their entry radii. Choose R from the double inverse of G and regard its binary floating entries as exact rational numbers. Compute an exact rational upper bound eta on `||I-RG||_infinity`. If eta<1, then

`||G^-1||_infinity <= ||R||_infinity/(1-eta) = M`.

For the binary-rational candidate c0, compute a rigorous bound rc on `||m-Gc0||_infinity`, yielding `||c-c0||_infinity<=M rc=ec`. For the candidate alpha0, compute a bound ra on `||h-Hc0-G alpha0||_infinity`. With an entry-certified bound HH on `||H||_infinity`,

`||alpha-alpha0||_infinity <= M(ra+HH ec)=ea`.

For each physical head coordinate n, the resulting error is at most `ea sum_d g_d(n)`. This gives an interval for the exact maximum over `1<=n<=D-1`; the maximum absolute candidate head value differs from the exact maximum by no more than the largest coordinate error. Output interval endpoints and all upper-bound fields are rounded outwards by one binary ULP.

The program and derivation received independent mathematical review by another agent. This is a rigorous-arithmetic numerical certificate conditional on the stated standard identities and exact Python integer/Fraction implementation, not a Lean theorem or a formally verified numerical program.

## Exact first stage

For D=2, `F=2g_2` is the odd-number indicator, while `r=1-F` is the even-number indicator. Consequently `Br` and g2 have disjoint support, so b=0 exactly and `||r||_Q^2=1/4`.

## Interpretation

Small finite-head maxima and substantial cancellation in h-Hc provide finite evidence. Head maxima are not monotone in D. The correction coefficient l1 norm grows over the tested stages, and Gram conditioning deteriorates. These experiments establish neither a stage-independent coefficient bound nor the required stage-independent physical-head bound. They do not prove RH.

## Executed floating diagnostics

Computed in this session with Python 3, NumPy 2.3.5 and SciPy 1.17.0. The matrix entries use the exact complete-tail special-function formulas above; displayed values are floating evaluations. The cancellation ratio is `||h-Hc||_2/(||h||_2+||Hc||_2)`.

| D | N | atoms | max head | alpha l1 | cancellation ratio | cond2(G) |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 7 | 5 | 0.0099823818 | 0.0835377 | 0.0072676 | 41.89 |
| 16 | 15 | 10 | 0.0148625981 | 0.1594426 | 0.0059718 | 252.59 |
| 32 | 31 | 19 | 0.0355178926 | 0.2980054 | 0.0053932 | 1280.52 |
| 64 | 63 | 38 | 0.0200613318 | 0.4633645 | 0.0039486 | 4897.76 |
| 96 | 95 | 59 | 0.0604903246 | 0.6454191 | 0.0036132 | 12549.18 |
| 128 | 127 | 77 | 0.0383728659 | 0.7915007 | 0.0033068 | 21029.16 |
| 192 | 191 | 116 | 0.0365347682 | 1.0463495 | 0.0031151 | 55291.57 |
| 256 | 255 | 156 | 0.0486479213 | 1.2992180 | 0.0027911 | 88599.78 |

The scan of every stage N=1 through 255 has largest floating head maximum 0.0604903245883 at N=95, physical site n=95. This is finite evidence only. The coefficient l1 norm is already approximately 1.29922 by N=255.

For the proposed variance estimate, D=256 gives rho≈0.00534055670915, beta≈1.68214222801e-5, e≈0.000161446608784, and v≈2.35733349819e-5. The ratio `(rho beta+e^2)/(rho v)` is approximately 0.920616. Here e uses the complete H identity; v is a floating sum through T=100000 with omitted-tail bound `(1+||c||_1)^2/[3 zeta(2) T^3]`, about 6.81e-13. This tail bound does not certify floating coefficient or summation errors; these variance values are diagnostics.

## Executed rational certificates

These intervals enclose the actual complete-tail head maxima, using the independent rational calculation and perturbation proof above. They certify the displayed individual stages, not all stages. No Lean verification of the arithmetic program is claimed.

| D | stage N | certified head-max interval | certified alpha coefficient error, infinity norm |
|---:|---:|---:|---:|
| 8 | 7 | [0.00998238, 0.00998239] | < 1.8315942732809019e-13 |
| 16 | 15 | [0.01486259, 0.01486260] | < 5.2989909906158674e-12 |
| 32 | 31 | [0.03551789, 0.03551790] | < 1.5566184903508635e-10 |
| 64 | 63 | [0.02006121, 0.02006146] | < 5.4363307603154140e-09 |
| 96 | 95 | [0.06048991, 0.06049074] | < 1.1941465332313816e-08 |
| 128 | 127 | [0.03836982, 0.03837591] | < 6.8612351135509081e-08 |

The rational interval computations used no assumptions about RH, residual vanishing, an unproved Gram spectral gap, or an unproved stage-uniform estimate. The Neumann inverse defects eta were checked to be below 1 by exact rational arithmetic at each stage. The independent audit confirmed the remainder and perturbation constants; outward rounding was applied to all reported bounds.

## Simultaneous finite-stage certification method

`certify_all_stages.py` reconstructs the complete D=128 interval system and saves every center and radius as a portable exact-rational JSON string. For any initial subdictionary of dimension q<=77, the smallest eigenvalue of its principal Gram submatrix is at least the smallest eigenvalue of the full Gram matrix: embed a q-vector in the full space by appending zeros and apply the Rayleigh-quotient characterization. Since the full inverse is symmetric,

`||G_q^-1||_infinity <= sqrt(q)||G_q^-1||_2 <= 9||G_128^-1||_2 <= 9||G_128^-1||_infinity`.

Thus the exact-rational full inverse certificate supplies a single rigorous inverse bound for every stage N<=127. The script recomputes floating coefficient candidates for each stage, converts them exactly to binary-rational numbers, and applies the residual and head-error bounds above with this common bound. The comparison of each final upper bound with 1/16 is an exact Fraction comparison; there is no floating threshold test.

## Selected certified intervals

| Conductor cutoff D | Repository stage N | Lower bound for head maximum | Upper bound |
|---:|---:|---:|---:|
| 8 | 7 | 0.0099823818436565893 | 0.0099823818446508859 |
| 16 | 15 | 0.014862598026268704 | 0.014862598087091172 |
| 32 | 31 | 0.035517890931789045 | 0.035517894222859399 |
| 64 | 63 | 0.02006121125184054 | 0.020061452423868208 |
| 96 | 95 | 0.060489910336303306 | 0.060490738840267289 |
| 128 | 127 | 0.038369827122889021 | 0.038375904710825276 |

The full numerical records, including solver residual certificates, follow.

```json
[
  {
    "D": 8,
    "dimension": 5,
    "eta_upper": 5.787905142589079e-15,
    "inverse_infty_upper": 68.86925087561077,
    "coefficient_c_error_infty": 6.844094057891264e-15,
    "coefficient_alpha_error_infty": 1.8315942732809016e-13,
    "head_error_upper": 4.971470170333876e-13,
    "head_max_center": 0.009982381844153737,
    "head_max_lower": 0.00998238184365659,
    "head_max_upper": 0.009982381844650886,
    "entry_radius_max": 1.2014581059683588e-20
  },
  {
    "D": 16,
    "dimension": 10,
    "eta_upper": 2.400173209273416e-14,
    "inverse_infty_upper": 325.2936609537021,
    "coefficient_c_error_infty": 3.167142532975374e-14,
    "coefficient_alpha_error_infty": 5.2989909906158666e-12,
    "head_error_upper": 3.0411232210679356e-11,
    "head_max_center": 0.014862598056679938,
    "head_max_lower": 0.014862598026268704,
    "head_max_upper": 0.014862598087091172,
    "entry_radius_max": 1.2014581059683588e-20
  },
  {
    "D": 32,
    "dimension": 19,
    "eta_upper": 9.652554554371602e-14,
    "inverse_infty_upper": 1539.1537685010367,
    "coefficient_c_error_infty": 1.572664539342254e-13,
    "coefficient_alpha_error_infty": 1.5566184903508632e-10,
    "head_error_upper": 1.6455351714390249e-09,
    "head_max_center": 0.035517892577324225,
    "head_max_lower": 0.035517890931789045,
    "head_max_upper": 0.0355178942228594,
    "entry_radius_max": 1.2014581059683588e-20
  },
  {
    "D": 64,
    "dimension": 38,
    "eta_upper": 4.474920281784265e-13,
    "inverse_infty_upper": 4894.232157516036,
    "coefficient_c_error_infty": 1.4110370838133331e-12,
    "coefficient_alpha_error_infty": 5.436330760315413e-09,
    "head_error_upper": 1.205860138301196e-07,
    "head_max_center": 0.020061331837854374,
    "head_max_lower": 0.02006121125184054,
    "head_max_upper": 0.02006145242386821,
    "entry_radius_max": 1.2014581059683588e-20
  },
  {
    "D": 96,
    "dimension": 59,
    "eta_upper": 2.0871813453814516e-12,
    "inverse_infty_upper": 10601.309031776274,
    "coefficient_c_error_infty": 1.281297225187791e-12,
    "coefficient_alpha_error_infty": 1.1941465332313814e-08,
    "head_error_upper": 4.1425198198318876e-07,
    "head_max_center": 0.060490324588285294,
    "head_max_lower": 0.060489910336303306,
    "head_max_upper": 0.06049073884026729,
    "entry_radius_max": 1.2014581059683588e-20
  },
  {
    "D": 128,
    "dimension": 77,
    "eta_upper": 3.93550468715982e-12,
    "inverse_infty_upper": 21296.05569110812,
    "coefficient_c_error_infty": 3.4452769670559815e-12,
    "coefficient_alpha_error_infty": 6.861235113550907e-08,
    "head_error_upper": 3.0387939681196093e-06,
    "head_max_center": 0.038372865916857145,
    "head_max_lower": 0.03836982712288902,
    "head_max_upper": 0.038375904710825276,
    "entry_radius_max": 1.2014581059683588e-20
  }
]
```


## Certificate covering every stage through 127

The exact-rational run exited successfully, and all 127 exact comparisons
against 1/16 passed. The maximum certified upper bound is
0.06062571738925453. Its worst certificate is at stage N=95; the largest
candidate head value there is .060490324588285294 and the common-inverse
error allowance is .00013539280096922199. The separate selected-stage
certificate above is tighter, because it certifies that stage's own inverse.

The common inverse bound uses the full 77-by-77 system at D=128. If M128
bounds its inverse infinity norm, every smaller principal inverse has
infinity norm at most sqrt(q)*M128<=9*M128: use minimum-eigenvalue
interlacing, symmetry, and the induced-norm comparisons. The outward-rounded
M128 is converted back to an exact rational upper bound. All remaining
residual and head comparisons are exact Fraction computations. This
argument was independently reviewed before the successful run.

This is an unconditional finite numerical certificate. The program and its
analysis are not a Lean-verified implementation; no arbitrary-stage bound
follows from the finite result.

```json
{
  "maximum_stage": 127,
  "all_below_one_sixteenth": true,
  "common_inverse_bound": 191664.50121997308,
  "maximum_certified_upper": 0.06062571738925453,
  "max_upper_exact": "458403788199642009876002625837244652181036214569599279653243625744648383247751258080379440879976147950582695808884337339940966576834846628045922785484061166615373892122916381680301709593334422344699535921776281221972664844150673240472793231456657450023644691601425450087039773487873559261680047324681552260442008921664767849135963180106809249023272547066034181942244905901414144513915795596363739067600777731887526900475630679306021894709279830554232453007785405632274099767355801320124180067447771635716371079916675808763028383537561994986911235768003666692106457830128192125840913628520010647118044306293344298875910174953010639224545029774386337184808969027235765738944421108338867351341519438969491700512311127275653076802333846545194923087139271873853831670792221802127995381150381187632901889516451415372386269737674507073292850153569502777873201155440713186432804949869362952119961272396520646736323724172714107597909465782786664177721343965389598893126919365552496649422324863738158605492171559504190937115524778494089004573759284369057/7561210125670048819931173712289143654602767125583868083242807533313049221088307465014933094126978377486849046694174994601666616328432331317505798677520484239134950644870883131831832704685159422106820324680814060526950938120166021121576141627940796517317999479128153750357851057763931723359983262356694787986374389306706989512318060581700105518474015639046763938845834405647882882763324437458268997589753987072371706328448832892361763349896161480231395160731805381411465688880093941457112832074084971389062463707219807752557712786561962425227674059767818605005133800105683218639386015325263749797627800875231642433633206531924846352103764976999678965809217974047783713219547583843459401991991314561622659739152193550147091754409051695300044938661021819818980399686854226561382591727656605748643177642616685120228038478007159798791776942749786007996469403396839422723607555553276153028110493414103330076539389229682284547133185738540770030963447827869444331969059877062652723200000000000000000000000000000000000000000000000000000000000000000000000",
  "verified_stage_count": 127,
  "worst_certificate": {
    "D": 96,
    "N": 95,
    "head_max_center": 0.060490324588285294,
    "head_error_upper": 0.00013539280096922199,
    "head_upper": 0.06062571738925453,
    "below_one_sixteenth": true
  }
}
```

## Reproduction

Save the following four code blocks under their indicated filenames in the same directory. NumPy and SciPy are required for candidates; certified bounds use exact Python integers and Fraction.

```bash
OPENBLAS_NUM_THREADS=1 python numerical_correction.py 256
OPENBLAS_NUM_THREADS=1 python certify_correction.py 8 16 32 64 96 128
OPENBLAS_NUM_THREADS=1 python numerical_all_stages.py
OPENBLAS_NUM_THREADS=1 python certify_all_stages.py
```

### numerical_correction.py

```python
"""Full infinite Q Gram systems via pairwise periodic trigamma/digamma sums.
No period cutoff or tail truncation. IEEE double evaluation, not interval certified.
Run: OPENBLAS_NUM_THREADS=1 python numerical_correction.py
"""
import json, math, time
from functools import lru_cache
from pathlib import Path
BASE = Path(__file__).resolve().parent
import numpy as np
from scipy.special import polygamma, digamma
from scipy.linalg import solve, eigvalsh
ZETA2=math.pi**2/6

def squarefree(n):
    return all(n%(p*p) for p in range(2,math.isqrt(n)+1))

@lru_cache(128)
def weights(L):
    # n=r+kL, 1<=r<=L, k>=0.  H kernel = 1/n^2 - 1/n + 1/(n+1).
    r=np.arange(1,L+1,dtype=float)
    w2=polygamma(1,r/L)/L**2
    wb=w2+(digamma(r/L)-digamma((r+1)/L))/L
    return w2, wb

def run(maxD=128):
    ds=np.array([d for d in range(2,maxD+1) if squarefree(d)])
    q=len(ds); G=np.zeros((q,q)); H=np.zeros((q,q)); m=np.zeros(q); h=np.zeros(q)
    for i,a in enumerate(ds):
        r=np.arange(1,a+1); v=(r%a)/a; w2,wb=weights(int(a))
        m[i]=v@w2; h[i]=v@wb
        for j,b in enumerate(ds[:i+1]):
            L=math.lcm(int(a),int(b)); r=np.arange(1,L+1)
            prod=((r%a)/a)*((r%b)/b); w2,wb=weights(L)
            G[i,j]=G[j,i]=prod@w2; H[i,j]=H[j,i]=prod@wb
    print('matrix complete',q,'cache',weights.cache_info(),flush=True)
    outputs=[]
    for D in [2,3,4,5,8,16,32,64,96,128,192,256]:
        if D>maxD: continue
        q=int(np.sum(ds<=D)); d=ds[:q]; g=G[:q,:q]; hb=H[:q,:q]; mm=m[:q]; hh=h[:q]
        c=solve(g,mm,assume_a='pos'); u=hb@c; rhs=hh-u
        alpha=solve(g,rhs,assume_a='pos')
        ns=np.arange(1,D+1); A=(ns[:,None]%d)/d
        b=A@alpha; F=A@c; r=1-F
        eig=eigvalsh(g)
        results=dict(D=D,repository_stage=D-1,dimension=q,
            head_max=float(max(abs(b[:D-1]))),head_max_including_D=float(max(abs(b))),
            head_argmax=int(np.argmax(abs(b[:D-1]))+1), b1=float(b[0]),bD=float(b[-1]),
            coeff_l1=float(sum(abs(alpha))),coeff_l2=float(np.linalg.norm(alpha)),
            residual_norm2=float(1-mm@c/ZETA2),correction_norm2=float(alpha@rhs/ZETA2),
            rhs_l2=float(np.linalg.norm(rhs)),h_l2=float(np.linalg.norm(hh)),Hc_l2=float(np.linalg.norm(u)),
            cancellation_ratio=float(np.linalg.norm(rhs)/(np.linalg.norm(hh)+np.linalg.norm(u))),
            rhs_inf=float(max(abs(rhs))),condition=float(eig[-1]/eig[0]),eigen_min=float(eig[0]),
            c_l1=float(sum(abs(c))),normal_residual_c=float(max(abs(g@c-mm))),
            normal_residual_alpha=float(max(abs(g@alpha-rhs))))
        outputs.append(results); print(json.dumps(results),flush=True)
        np.savez(f'{BASE}/numerical_correction_D{D}.npz',ds=d,G=g,H=hb,m=mm,h=hh,c=c,alpha=alpha,rhs=rhs,head_b=b,head_residual=r)
    with open(BASE/'numerical_correction_results.json','w') as f: json.dump(outputs,f,indent=2)
    np.savez(BASE/'numerical_correction_full.npz',ds=ds,G=G,H=H,m=m,h=h,maximum_cutoff=maxD)

if __name__=='__main__':
    import sys
    run(int(sys.argv[1]) if len(sys.argv)>1 else 256)

```

### certify_correction.py

```python
"""Exact-integer enclosure of complete infinite Gram entries, then rational residual certification.
Euler--Maclaurin remainder bound, 16 periods + 7 Bernoulli corrections.
All numerical enclosure arithmetic uses integers/Fraction; scipy only chooses candidates.
"""
import math,json,time
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
BASE = Path(__file__).resolve().parent
import numpy as np
S=10**35; K=16; P=8; J=24
BERN=[(1,6),(-1,30),(1,42),(-1,30),(5,66),(-691,2730),(7,6),(-3617,510)]

def term(num,den): return S*num//den

@lru_cache(None)
def weight_centers(L):
    w2=[]; wb=[]
    for r in range(1,L+1):
        a=sum(term(1,(r+k*L)**2) for k in range(K))
        b=sum(term(1,(r+k*L)**2*(r+k*L+1)) for k in range(K))
        x=r+K*L
        a+=term(1,L*x)+term(1,2*x*x)
        b+=sum(term((-1)**j,L*j*x**j) for j in range(2,J+1))+term(1,2*x*x*(x+1))
        for k,(bn,bd) in enumerate(BERN[:-1],1):
            fac=bn*L**(2*k-1)
            a+=term(fac,bd*x**(2*k+1))
            b+=term(fac,bd*x**(2*k+1))-term(fac,bd*2*k*x**(2*k))+term(fac,bd*2*k*(x+1)**(2*k))
        w2.append(a);wb.append(b)
    # A conservative pair-entry enclosure: L times weight errors, atoms <=1.
    # Euler remainder for f=n^-2: |B_16| L^15/x^17; for f=n^-2/(n+1)
    # derivative domination follows t-1+exp(-t) <= t in its positive Laplace kernel.
    euler=F(abs(BERN[-1][0]),BERN[-1][1]*L*K**(2*P+1))
    logrem=F(1,(J+1)*(K*L)**(J+1))
    rounderr=F(L*100,S) # <= 63 floored rational terms plus final weighted floor per residue
    return w2,wb,euler+rounderr,euler+logrem+rounderr

def interval_entries(ds):
    q=len(ds);G=[[None]*q for _ in ds];H=[[None]*q for _ in ds];Ge=[[None]*q for _ in ds];He=[[None]*q for _ in ds]
    m=[];h=[];me=[];he=[]
    for i,a in enumerate(ds):
        w2,wb,e2,eb=weight_centers(a)
        m.append(F(sum(w2[r-1]*(r%a)//a for r in range(1,a+1)),S));h.append(F(sum(wb[r-1]*(r%a)//a for r in range(1,a+1)),S));me.append(e2);he.append(eb)
        for j,b in enumerate(ds[:i+1]):
            L=math.lcm(a,b);w2,wb,e2,eb=weight_centers(L)
            G[i][j]=G[j][i]=F(sum(w2[r-1]*(r%a)*(r%b)//(a*b) for r in range(1,L+1)),S)
            H[i][j]=H[j][i]=F(sum(wb[r-1]*(r%a)*(r%b)//(a*b) for r in range(1,L+1)),S)
            Ge[i][j]=Ge[j][i]=e2;He[i][j]=He[j][i]=eb
    return G,H,m,h,Ge,He,me,he

def upper(q): return math.nextafter(float(q), math.inf)
def lower(q): return math.nextafter(float(q), -math.inf)

def mv(M,v):return [sum(a*b for a,b in zip(row,v)) for row in M]

def certify(D, entries=None):
    z=np.load(f'{BASE}/numerical_correction_D{D}.npz'); ds=[int(d) for d in z['ds']];q=len(ds)
    G,H,m,h,Ge,He,me,he=interval_entries(ds) if entries is None else entries
    c=[F(float(x)) for x in z['c']];al=[F(float(x)) for x in z['alpha']]
    R=[[F(float(x)) for x in row] for row in np.linalg.inv(z['G'])]
    eta=max(sum(abs(F(i==j)-sum(R[i][k]*G[k][j] for k in range(q)))+sum(abs(R[i][k])*Ge[k][j] for k in range(q)) for j in range(q)) for i in range(q))
    assert eta<1
    invnorm=max(sum(map(abs,row)) for row in R)/(1-eta)
    res_c=max(abs(m[i]-sum(G[i][j]*c[j] for j in range(q)))+me[i]+sum(Ge[i][j]*abs(c[j]) for j in range(q)) for i in range(q))
    err_c=invnorm*res_c
    res_a=max(abs(h[i]-sum(H[i][j]*c[j]+G[i][j]*al[j] for j in range(q)))+he[i]+sum(He[i][j]*abs(c[j])+Ge[i][j]*abs(al[j]) for j in range(q)) for i in range(q))
    Hnorm=max(sum(abs(H[i][j])+He[i][j] for j in range(q)) for i in range(q))
    err_a=invnorm*(res_a+Hnorm*err_c)
    head=[sum(F(n%d,d)*al[j] for j,d in enumerate(ds)) for n in range(1,D)]
    headerr=max(sum(F(n%d,d) for d in ds) for n in range(1,D))*err_a
    hm=max(map(abs,head))
    out=dict(D=D,dimension=q,eta_upper=upper(eta),inverse_infty_upper=upper(invnorm),coefficient_c_error_infty=upper(err_c),coefficient_alpha_error_infty=upper(err_a),head_error_upper=upper(headerr),head_max_center=float(hm),head_max_lower=lower(hm-headerr),head_max_upper=upper(hm+headerr),entry_radius_max=upper(max(max(row) for row in Ge)))
    print(json.dumps(out),flush=True)
    return out

if __name__=='__main__':
    import sys
    Ds=[int(x) for x in sys.argv[1:]] or [8,16,32]
    outs=[certify(d) for d in Ds]
    with open(BASE/'numerical_correction_certificates.json','w') as f:json.dump(outs,f,indent=2)

```

### numerical_all_stages.py

```python
"""All-stage floating scan from complete Gram matrices; not an interval certificate."""
from pathlib import Path
import json
import numpy as np
from scipy.linalg import solve
BASE=Path(__file__).resolve().parent
z=np.load(BASE/'numerical_correction_full.npz');ds=z['ds'];G=z['G'];H=z['H'];m=z['m'];h=z['h'];out=[]
for D in range(2,int(z['maximum_cutoff'])+1):
    q=int(np.sum(ds<=D));d=ds[:q]
    c=solve(G[:q,:q],m[:q],assume_a='pos');rhs=h[:q]-H[:q,:q]@c
    alpha=solve(G[:q,:q],rhs,assume_a='pos');n=np.arange(1,D);b=((n[:,None]%d)/d)@alpha
    out.append(dict(D=D,N=D-1,head_max=float(max(abs(b))),argmax=int(np.argmax(abs(b))+1),alpha_l1=float(sum(abs(alpha)))))
print('all-stage maximum',max(out,key=lambda row:row['head_max']))
with (BASE/'numerical_correction_all_stages.json').open('w') as f:json.dump(out,f,indent=2)

```

### certify_all_stages.py

```python
"""Certify every squarefree moving head for repository stages 1,...,127.
Uses a full128 exact-rational Gram enclosure and a common inverse bound.
This script is a rigorous-arithmetic numerical certificate, not Lean verification.
"""
import json, math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.linalg import solve
from certify_correction import interval_entries, certify, upper, lower
BASE=Path(__file__).resolve().parent
Dmax=128
z=np.load(BASE/'numerical_correction_full.npz');ds=[int(d) for d in z['ds'] if d<=Dmax]
entries=interval_entries(ds)
G,H,m,h,Ge,He,me,he=entries
cache={name:[[str(x) for x in row] for row in value] for name,value in zip(['G','H','Ge','He'],[G,H,Ge,He])}
cache.update({name:[str(x) for x in value] for name,value in zip(['m','h','me','he'],[m,h,me,he])})
cache['ds']=ds
with (BASE/'numerical_correction_exact128.json').open('w') as f:json.dump(cache,f)
full=certify(Dmax,entries)
# G^-1 is symmetric, so ||G^-1||2 <= ||G^-1||infty. Principal eigenvalue
# interlacing and sqrt(q)<=9 yield this common induced-infinity inverse bound.
M=9*F(full['inverse_infty_upper'])
outs=[]; all_verified=True; max_upper=F(0)
for D in range(2,Dmax+1):
    q=sum(d<=D for d in ds);d=ds[:q]
    gf=z['G'][:q,:q];hf=z['H'][:q,:q];mf=z['m'][:q];hh=z['h'][:q]
    cf=solve(gf,mf,assume_a='pos');af=solve(gf,hh-hf@cf,assume_a='pos')
    c=[F(float(v)) for v in cf];a=[F(float(v)) for v in af]
    rc=max(abs(m[i]-sum(G[i][j]*c[j] for j in range(q)))+me[i]+sum(Ge[i][j]*abs(c[j]) for j in range(q)) for i in range(q))
    ec=M*rc
    ra=max(abs(h[i]-sum(H[i][j]*c[j]+G[i][j]*a[j] for j in range(q)))+he[i]+sum(He[i][j]*abs(c[j])+Ge[i][j]*abs(a[j]) for j in range(q)) for i in range(q))
    Hnorm=max(sum(abs(H[i][j])+He[i][j] for j in range(q)) for i in range(q))
    ea=M*(ra+Hnorm*ec)
    head=[sum(F(n%dd,dd)*a[j] for j,dd in enumerate(d)) for n in range(1,D)]
    headerr=max(sum(F(n%dd,dd) for dd in d) for n in range(1,D))*ea
    hm=max(map(abs,head));hi=hm+headerr
    valid=hi<F(1,16);all_verified &= valid;max_upper=max(max_upper,hi)
    outs.append(dict(D=D,N=D-1,head_max_center=float(hm),head_error_upper=upper(headerr),head_upper=upper(hi),below_one_sixteenth=valid))
result=dict(maximum_stage=127,all_below_one_sixteenth=all_verified,common_inverse_bound=upper(M),maximum_certified_upper=upper(max_upper),max_upper_exact=str(max_upper),stages=outs)
with (BASE/'numerical_correction_all_stage_certificates.json').open('w') as f:json.dump(result,f,indent=2)
print(json.dumps({k:v for k,v in result.items() if k not in ['stages','max_upper_exact']}),flush=True)
print('worst certificate',max(outs,key=lambda x:x['head_upper']),flush=True)

```

## Selected floating diagnostics (not certificates)

```json
[
  {
    "D": 2,
    "repository_stage": 1,
    "dimension": 1,
    "head_max": 0.0,
    "head_max_including_D": 0.0,
    "head_argmax": 1,
    "b1": 0.0,
    "bD": 0.0,
    "coeff_l1": 0.0,
    "coeff_l2": 0.0,
    "residual_norm2": 0.2499999999999999,
    "correction_norm2": 0.0,
    "rhs_l2": 0.0,
    "h_l2": 0.2702766847881123,
    "Hc_l2": 0.2702766847881123,
    "cancellation_ratio": 0.0,
    "rhs_inf": 0.0,
    "condition": 1.0,
    "eigen_min": 0.3084251375340425,
    "c_l1": 2.0,
    "normal_residual_c": 0.0,
    "normal_residual_alpha": 0.0
  },
  {
    "D": 3,
    "repository_stage": 2,
    "dimension": 2,
    "head_max": 0.005223925018555573,
    "head_max_including_D": 0.006934640080467312,
    "head_argmax": 2,
    "b1": -0.004322677571189526,
    "bD": -0.006934640080467312,
    "coeff_l1": 0.021705167688767985,
    "coeff_l2": 0.01592978548290432,
    "residual_norm2": 0.06868528248534767,
    "correction_norm2": 2.0895029860325708e-05,
    "rhs_l2": 0.0028139616115373982,
    "h_l2": 0.35793170222093845,
    "Hc_l2": 0.36035923799316405,
    "cancellation_ratio": 0.003917579150724962,
    "rhs_inf": 0.002767110525618066,
    "condition": 4.918862978859145,
    "eigen_min": 0.09872920365293009,
    "c_l1": 2.5194010089707786,
    "normal_residual_c": 0.0,
    "normal_residual_alpha": 8.673617379884035e-19
  },
  {
    "D": 4,
    "repository_stage": 3,
    "dimension": 2,
    "head_max": 0.006934640080467312,
    "head_max_including_D": 0.006934640080467312,
    "head_argmax": 3,
    "b1": -0.004322677571189526,
    "bD": 0.0026119625092777864,
    "coeff_l1": 0.021705167688767985,
    "coeff_l2": 0.01592978548290432,
    "residual_norm2": 0.06868528248534767,
    "correction_norm2": 2.0895029860325708e-05,
    "rhs_l2": 0.0028139616115373982,
    "h_l2": 0.35793170222093845,
    "Hc_l2": 0.36035923799316405,
    "cancellation_ratio": 0.003917579150724962,
    "rhs_inf": 0.002767110525618066,
    "condition": 4.918862978859145,
    "eigen_min": 0.09872920365293009,
    "c_l1": 2.5194010089707786,
    "normal_residual_c": 0.0,
    "normal_residual_alpha": 8.673617379884035e-19
  },
  {
    "D": 5,
    "repository_stage": 4,
    "dimension": 3,
    "head_max": 0.006840905152541088,
    "head_max_including_D": 0.010033902933435333,
    "head_argmax": 1,
    "b1": 0.006840905152541088,
    "bD": 0.010033902933435333,
    "coeff_l1": 0.02129641837749038,
    "coeff_l2": 0.013145244262148126,
    "residual_norm2": 0.02723690103609655,
    "correction_norm2": 3.547951164378176e-05,
    "rhs_l2": 0.005647804121965665,
    "h_l2": 0.39434559306837114,
    "Hc_l2": 0.38870712762909865,
    "cancellation_ratio": 0.0072125464514511,
    "rhs_inf": 0.00402140536735357,
    "condition": 9.982135668877843,
    "eigen_min": 0.061331850193773685,
    "c_l1": 2.804624180492969,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 4.336808689942018e-19
  },
  {
    "D": 8,
    "repository_stage": 7,
    "dimension": 5,
    "head_max": 0.009982381844153738,
    "head_max_including_D": 0.009982381844153738,
    "head_argmax": 7,
    "b1": 0.008555268328966182,
    "bD": 0.006386891985258998,
    "coeff_l1": 0.08353766600041185,
    "coeff_l2": 0.043250376627404295,
    "residual_norm2": 0.01725796999056295,
    "correction_norm2": 6.237568043212526e-05,
    "rhs_l2": 0.006318240415312094,
    "h_l2": 0.4378079594006518,
    "Hc_l2": 0.43156450970725324,
    "cancellation_ratio": 0.007267587414857377,
    "rhs_inf": 0.004236068831014905,
    "condition": 41.885299920478374,
    "eigen_min": 0.0202780106240365,
    "c_l1": 3.8048653099930947,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 8.673617379884035e-19
  },
  {
    "D": 16,
    "repository_stage": 15,
    "dimension": 10,
    "head_max": 0.014862598056679936,
    "head_max_including_D": 0.016554929179912106,
    "head_argmax": 15,
    "b1": 0.007570931321612825,
    "bD": -0.016554929179912106,
    "coeff_l1": 0.15944264894228247,
    "coeff_l2": 0.05540804683138617,
    "residual_norm2": 0.01277462108799654,
    "correction_norm2": 5.290342036093756e-05,
    "rhs_l2": 0.005578939241482447,
    "h_l2": 0.4698550022074507,
    "Hc_l2": 0.46435916696897345,
    "cancellation_ratio": 0.005971799000223553,
    "rhs_inf": 0.003465767581735224,
    "condition": 252.5941955732166,
    "eigen_min": 0.0045962124408890975,
    "c_l1": 5.855062767644642,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 1.3010426069826053e-18
  },
  {
    "D": 32,
    "repository_stage": 31,
    "dimension": 19,
    "head_max": 0.035517892577324225,
    "head_max_including_D": 0.035517892577324225,
    "head_argmax": 31,
    "b1": 0.006517392369779684,
    "bD": 0.03433488602461218,
    "coeff_l1": 0.2980053657416464,
    "coeff_l2": 0.07487014994463652,
    "residual_norm2": 0.00986656002314179,
    "correction_norm2": 4.182347807756e-05,
    "rhs_l2": 0.0052201278012030915,
    "h_l2": 0.4865493505113695,
    "Hc_l2": 0.4813682427665631,
    "cancellation_ratio": 0.00539315313354797,
    "rhs_inf": 0.0030205854300573987,
    "condition": 1280.5161064606712,
    "eigen_min": 0.0011371099333430264,
    "c_l1": 9.350032030638653,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 1.5178830414797062e-18
  },
  {
    "D": 64,
    "repository_stage": 63,
    "dimension": 38,
    "head_max": 0.020061331837854378,
    "head_max_including_D": 0.020061331837854378,
    "head_argmax": 58,
    "b1": 0.005281730013655796,
    "bD": -0.0073060201174618405,
    "coeff_l1": 0.4633645484052967,
    "coeff_l2": 0.08882432905047313,
    "residual_norm2": 0.007582873755320851,
    "correction_norm2": 2.921197131974554e-05,
    "rhs_l2": 0.003902811386774119,
    "h_l2": 0.4961287260122288,
    "Hc_l2": 0.4922832037115961,
    "cancellation_ratio": 0.003948567666382391,
    "rhs_inf": 0.002350010140659664,
    "condition": 4897.755193277121,
    "eigen_min": 0.0003608115636173408,
    "c_l1": 17.036851795999045,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 3.469446951953614e-18
  },
  {
    "D": 96,
    "repository_stage": 95,
    "dimension": 59,
    "head_max": 0.0604903245882853,
    "head_max_including_D": 0.0604903245882853,
    "head_argmax": 95,
    "b1": 0.004857718725123932,
    "bD": -0.04381918351054824,
    "coeff_l1": 0.6454191401961052,
    "coeff_l2": 0.10142353198698277,
    "residual_norm2": 0.006986585659060185,
    "correction_norm2": 2.5451681874669827e-05,
    "rhs_l2": 0.003596902834357911,
    "h_l2": 0.4995205542099061,
    "Hc_l2": 0.4959761872250442,
    "cancellation_ratio": 0.003613173890627895,
    "rhs_inf": 0.0021389545504315044,
    "condition": 12549.178297876957,
    "eigen_min": 0.00015564067214412732,
    "c_l1": 23.639743686474844,
    "normal_residual_c": 2.220446049250313e-16,
    "normal_residual_alpha": 3.0357660829594124e-18
  },
  {
    "D": 128,
    "repository_stage": 127,
    "dimension": 77,
    "head_max": 0.038372865916857145,
    "head_max_including_D": 0.038372865916857145,
    "head_argmax": 95,
    "b1": 0.0045060911947475265,
    "bD": -0.007161484253843195,
    "coeff_l1": 0.7915007295067451,
    "coeff_l2": 0.10666215215396212,
    "residual_norm2": 0.006333102201087737,
    "correction_norm2": 2.1981570409571995e-05,
    "rhs_l2": 0.0033025002595327047,
    "h_l2": 0.5009759600915544,
    "Hc_l2": 0.4977207658581616,
    "cancellation_ratio": 0.003306809939115575,
    "rhs_inf": 0.0019828890018893652,
    "condition": 21029.157127451905,
    "eigen_min": 9.805816613856638e-05,
    "c_l1": 30.286332813207753,
    "normal_residual_c": 1.1102230246251565e-16,
    "normal_residual_alpha": 3.876022766635678e-18
  },
  {
    "D": 192,
    "repository_stage": 191,
    "dimension": 116,
    "head_max": 0.036534768219036395,
    "head_max_including_D": 0.036534768219036395,
    "head_argmax": 114,
    "b1": 0.00425807323873621,
    "bD": 0.02483039175899121,
    "coeff_l1": 1.0463494961831694,
    "coeff_l2": 0.11743936533316099,
    "residual_norm2": 0.005949741686293142,
    "correction_norm2": 2.0008676638710545e-05,
    "rhs_l2": 0.0031214014752090034,
    "h_l2": 0.5025499416533293,
    "Hc_l2": 0.499472341404627,
    "cancellation_ratio": 0.0031151018574987754,
    "rhs_inf": 0.0018617242719498606,
    "condition": 55291.57423626084,
    "eigen_min": 4.0157997434004255e-05,
    "c_l1": 42.78435405325427,
    "normal_residual_c": 4.440892098500626e-16,
    "normal_residual_alpha": 3.469446951953614e-18
  },
  {
    "D": 256,
    "repository_stage": 255,
    "dimension": 156,
    "head_max": 0.04864792130483572,
    "head_max_including_D": 0.04864792130483572,
    "head_argmax": 221,
    "b1": 0.0038765604827106738,
    "bD": -0.011510634769416054,
    "coeff_l1": 1.2992180063480248,
    "coeff_l2": 0.1307909160338124,
    "residual_norm2": 0.00534055670914535,
    "correction_norm2": 1.6821422280108718e-05,
    "rhs_l2": 0.002802201013486332,
    "h_l2": 0.5033619341628712,
    "Hc_l2": 0.5006018227097264,
    "cancellation_ratio": 0.0027911376225525737,
    "rhs_inf": 0.0016771334940462457,
    "condition": 88599.78301830673,
    "eigen_min": 2.631204139753223e-05,
    "c_l1": 56.95784757899075,
    "normal_residual_c": 2.220446049250313e-16,
    "normal_residual_alpha": 3.903127820947816e-18
  }
]
```

### Signed leading/tail decomposition diagnostics

```json
[
  {
    "D": 8,
    "A": 0.009930041325128033,
    "max_common": 0.01549752659099962,
    "max_signed_tail_remainder": 0.013100734030681285,
    "max_abs_sum_remainder": 0.04444180869506416,
    "max_tail_Cauchy_bound": 0.45490454882177894,
    "identity_error": 1.5612511283791264e-17
  },
  {
    "D": 16,
    "A": 0.0067201251798879895,
    "max_common": 0.010347575755327033,
    "max_signed_tail_remainder": 0.015044046087289436,
    "max_abs_sum_remainder": 0.042496872883221674,
    "max_tail_Cauchy_bound": 0.7060478726205092,
    "identity_error": 6.201636426617085e-17
  },
  {
    "D": 32,
    "A": 0.004591895831204854,
    "max_common": 0.010535273637440237,
    "max_signed_tail_remainder": 0.024982618939883895,
    "max_abs_sum_remainder": 0.047734011368304186,
    "max_tail_Cauchy_bound": 1.3108166048918597,
    "identity_error": 1.0581813203458523e-16
  },
  {
    "D": 64,
    "A": 0.0035780170281131,
    "max_common": 0.00627830000561043,
    "max_signed_tail_remainder": 0.017238422455844542,
    "max_abs_sum_remainder": 0.038330001955583407,
    "max_tail_Cauchy_bound": 1.6721848156494508,
    "identity_error": 4.996003610813204e-16
  },
  {
    "D": 96,
    "A": 0.003313668819841565,
    "max_common": 0.0076836642158926985,
    "max_signed_tail_remainder": 0.052806660372392615,
    "max_abs_sum_remainder": 0.06080588780919856,
    "max_tail_Cauchy_bound": 2.7604394782571977,
    "identity_error": 1.061650767297806e-15
  },
  {
    "D": 128,
    "A": 0.0029760740242479326,
    "max_common": 0.005943188837460431,
    "max_signed_tail_remainder": 0.033478891757420776,
    "max_abs_sum_remainder": 0.042803223031697264,
    "max_tail_Cauchy_bound": 2.4758079956361634,
    "identity_error": 1.4641066137244252e-15
  }
]
```
