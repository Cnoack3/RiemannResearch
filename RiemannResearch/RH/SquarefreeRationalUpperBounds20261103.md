# Complete squarefree rational upper bounds — 3 November 2026

Prepared for Christian Noack. Research base inspected:
`f7cf4a1a10227ecede3e3c6b9d9e05d734cb58de`.
The approved formal continuation was applied on 4 November 2026 to
`54d5ba4b3866eeb100fe597ab411997e48bb2784`.
Final saved-source validation and publication are supplied by the
checkpoint carrying this memorandum and its focused ledger entry.

## Result and verification status

For the actual probability law Q(n)=1/(ζ(2)n²), the supplied rational
121-atom vector, supported on every squarefree integer 2≤d≤200, proves

\[
0\le \operatorname{legalErrorInfimum}
\le \left\|1-\sum_d c_dg_d\right\|_Q^2
<\frac{5873}{1000000}=0.005873.
\]

This improves the published 59/1000 upper bound by more than a factor of ten.
The coefficients have denominator 10^6; every numerator and its conductor
is stored in the `certificates.json` block of the companion
`SquarefreeRationalReproduction20261103.md`.
The proof includes the entire infinite Q tail. It uses exact integer and
rational calculations plus the elementary analytic estimates proved below.
It does not rely on floating-point optimization being correct.

The rigorous outer interval for this particular rational vector is

\[
0.0058718315 < \|1-F\|_Q^2 < 0.0058726259.
\]

All bounds displayed in this memorandum are squared errors. The infimum
itself is not enclosed from below by the positive left endpoint: that
endpoint applies only to this one candidate.

Status distinctions:

- Existing source declarations and verification records were inspected at
  the base commit; their prior verification was not rerun.
- New rational certificate calculations passed, including a separate
  standard-library-only verifier for the strongest candidate.
- Complete-Gram coefficient solves and block-comparison decimal values
  are floating diagnostics unless explicitly certified below.
- The seven-atom complete norm bound 361/10000 and its two infimum
  corollaries passed the user's Lean server source check on 4 November 2026:
  job `job_0BXFq4iBPSSYeVblqeP0bxp77beikPg-`, verified=true, exit code 0,
  reported verification duration 60.222 seconds (including dependency
  preparation, not a measurement of kernel time alone).
- Earlier connection failures are historical: no theorem was reported as
  checked during those outages. The current continuation uses the restored
  server and the mandatory checkpoint publication route.
- A saved-module import and axiom audit passed job
  `job_8dcGsYn_Js5r8oIqES9H3bVFSHqemjYm`, verified=true, exit code 0,
  reported verification duration 28.203 seconds. All three endpoint
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- RH and the zero-infimum condition remain unproved.

## Complete finite-dimensional optimization

Put g_d(n)=(n mod d)/d. For a finite conductor set D, define

\[
b_d=\langle 1,g_d\rangle_Q,\qquad
G_{de}=\langle g_d,g_e\rangle_Q.
\]

These are complete infinite-law moments. If L=lcm(d,e), then

\[
G_{de}=\frac1{\zeta(2)L^2}
\sum_{r=1}^{L}g_d(r)g_e(r)\psi_1(r/L).
\]

The analogous formula with period d gives b_d. The identity follows by
partitioning the positive integers into residue classes and using the
trigamma series, NIST DLMF 5.15.1. The zero residue is represented by r=L,
so the entire progression is retained. For numerical computation only,
SciPy evaluated these complete residue weights.

The atoms with distinct d≥2 are linearly independent. Indeed, if their
finite combination vanishes, taking first differences gives
Σ_d c_d/d − Σ_{d|n}c_d=0. At n=1 the first sum is zero. Applying the remaining
identity in increasing order to the conductors gives c_d=0 for every d.
Consequently G is positive definite, and the unique exact minimizer is

\[
c_*=G^{-1}b,\qquad E_D=1-b^TG^{-1}b.
\]

For every rational candidate c there is the exact identity

\[
E(c)=E_D+(c-c_*)^TG(c-c_*)
=E_D+(Gc-b)^TG^{-1}(Gc-b).
\]

Repository consumers include `QCovarianceInverse.qError_eq`,
`qError_gram_solution`, and `FiniteHilbertGramProjection`.
No finite physical truncation was substituted for G in the candidate solves.

## An explicit seven-atom certificate

The particularly small reproducible improvement is

\[
F_{30}=\frac1{10^6}(985587g_2+963419g_3+823721g_5
-158232g_6+91952g_{10}+138611g_{15}+146439g_{30}).
\]

Exact arithmetic with the complete tail proves

\[
\|1-F_{30}\|_Q^2<\frac{25401}{10^6}=0.025401.
\]

The negative coefficient is retained throughout. The complete-Gram optimum
is numerically 0.0254002254357. A further exact-rational calculation proves
that the displayed rational vector is within 10^-11 of the true optimum.

For that optimality check, all complete entries of G and b were enclosed
rationally. Let M be the midpoint Gram matrix, R the entrywise radii,
and γ=max_i Σ_j R_ij. An exact rational LDLᵀ factorization verified that
M−(γ+1/250)I is positive definite. Since the symmetric perturbation
G−M has operator norm at most γ, this proves G≥(1/250)I. Rational bounds
v_i≥|(Gc−b)_i| then give

\[
0\le E(c)-E_D\le250\sum_i v_i^2
<8.36\times10^{-12}<10^{-11}.
\]

`gram_optimality.json` contains all rational intervals, the positive LDL
pivots, and the exact gap bound. This calculation is not Lean checked.

## Rational control of the complete infinite tail

Write r(n)=1−Σ_d c_d g_d(n). Its period can be enormous; we never need to
enumerate that common period. Write an overbar for a uniform period mean.
Elementary CRT gives

\[
\overline{g_d}=\frac{d-1}{2d},\qquad
\overline{g_dg_e}=
\frac{(d-1)(e-1)}{4de}+\frac{\gcd(d,e)^2-1}{12de}.
\]

For completeness, set g=gcd(d,e), d=ga, e=gb with gcd(a,b)=1, and write
n=gt+s, 0≤s<g. Over one lcm period, t mod a and t mod b are independent
uniform residues and are independent of s. Conditional on s, the two
residues have independent varying parts; their covariance is Var(s)/(de),
which is (g²−1)/(12de). This proves the formula. The certificate generator
also independently checked it by exact finite integer sums for every
conductor pair used in each candidate.

Thus the following number is an exact rational, nonnegative period mean:

\[
\mu=\overline{r^2}
=1-2\sum_d c_d\frac{d-1}{2d}
+\sum_{d,e}c_dc_e\left(
\frac{(d-1)(e-1)}{4de}+
\frac{\gcd(d,e)^2-1}{12de}\right).
\]

Here is a useful bound that retains the signed mean and uses only pair
periods. If h has period ℓ and takes values in [0,1], then, for every
starting position and every length k,

\[
\left|\sum_{j=1}^k(h(N+j)-\bar h)\right|\le\ell/4.
\]

Proof: discard whole periods and let m<ℓ be the remaining length. If A is
the sum over those m positions and B is the sum over the other ℓ−m
positions, the centered sum is (1−m/ℓ)A−(m/ℓ)B. Its absolute value is
at most m(ℓ−m)/ℓ≤ℓ/4. This argument works for every starting position.

Expand r² with its signed coefficients before using this lemma. Since
g_d and g_dg_e lie in [0,1], a valid rational bound is

\[
\left|\sum_{j=1}^k(r(N+j)^2-\mu)\right|\le D(c),
\quad
D(c)=\frac14\left(2\sum_d |c_d|d
+\sum_{d,e}|c_dc_e|\operatorname{lcm}(d,e)\right).
\]

The constant term has zero centered sum. The signed coefficients are
preserved in μ and in the exact head; absolute values are used only in
this explicit error bound for the centered tail.

Abel summation with the decreasing weights (N+j)^−2 now proves

\[
\sum_{n>N}\frac{r(n)^2}{n^2}
=\mu\sum_{n>N}\frac1{n^2}+\theta_N,
\qquad |\theta_N|\le\frac{D(c)}{(N+1)^2}.
\]

This is an identity with a bounded signed remainder, not an omitted tail.
It follows because the differences of consecutive weights telescope to
1/(N+1)², while the bounded partial-sum boundary term tends to zero.

Let H_N=Σ_{n≤N}r(n)²/n². The integral test gives the entirely rational
outer bounds

\[
H_N+\frac{\mu}{N+1}-\frac{D(c)}{(N+1)^2}
\le\zeta(2)E(c)\le
H_N+\frac{\mu}{N}+\frac{D(c)}{(N+1)^2}.
\]

The computation encloses H_N by exact integer division at scale S=10^20.
If A_n=C r(n) is its integer numerator, it sums
floor(S A_n²/(C² n²)); the enclosure width is at most N/S. This is exact
outward rounding. ζ(2) is enclosed by the same procedure for its first
10,000 terms, plus the integral-test tails 1/10001 and 1/10000. It is not
replaced by an unverified floating approximation to π²/6.

For the 121-atom certificate N=2,000,000 and

\[
D(c)=\frac{10451955150997945739}{4000000000000}.
\]

The exact H_N enclosure is

\[
\frac{482955104505085687}{50000000000000000000}
\le H_N\le
\frac{482955104506085687}{50000000000000000000}.
\]

Together with the recorded rational μ and ζ bounds, these data give the
strict bound 5873/10^6 by integer cross multiplication.

## Results across families

Every upper bound below is a strict rational bound for an explicit
rational vector, hence also for the global legal-error infimum. Decimal
Gram optima are numerical diagnostics, not certified exact minima except
for the seven-atom gap enclosure described above.

| Family | Atoms | Complete-Gram optimum, numerical | Rational strict upper bound |
|---|---:|---:|---:|
| Original g₂,g₃,g₆ | 3 | 0.0547669434 | 0.054767 |
| All nontrivial divisors of 30 | 7 | 0.0254002254 | 0.025401 |
| All nontrivial divisors of 210 | 15 | 0.0168704361 | 0.016871 |
| All nontrivial divisors of 2310 | 31 | 0.0135494811 | 0.013550 |
| All nontrivial divisors of 30030 | 63 | 0.0117529979 | 0.011754 |
| All squarefree 2≤d≤30 | 18 | 0.0098669304 | 0.009867 |
| All squarefree 2≤d≤60 | 36 | 0.0076133226 | 0.007614 |
| All squarefree 2≤d≤100 | 60 | 0.0068102038 | 0.006811 |
| All squarefree 2≤d≤200 | 121 | 0.0058722287 | 0.005873 |

The first row uses the previously published rational vector unchanged.
The squarefree-through-H families are nested; the primorial families form
another nested chain. The displayed ordering of all rows is not itself
a nested chain. The through-H experiments use a fixed number of atoms
more effectively than these full primorial divisor sets, in the tested range.

## Exact Gram, projected anchors, and signed blocks

Let P be an orthogonal projection whose range contains 1, T=I−P, and
F=Σ c_dg_d. For exact projection anchors b_d=Pg_d,

\[
\|P(1-F)\|^2+\|F-\sum_dc_db_d\|^2=\|1-F\|^2.
\]

This is precisely the role of the existing
`anchoredCertificate_projection_eq_error`. Projected anchors and the
complete Gram formulation therefore have identical mathematical optima.

For a partition into synthesized blocks F=Σ_j F_j, the block certificate is

\[
C_{\rm block}=\|P(1-F)\|^2+
\left(\sum_j\|TF_j\|\right)^2\ge E(c).
\]

Its exact excess is

\[
C_{\rm block}-E(c)=
2\sum_{j<k}\big(\|TF_j\|\|TF_k\|-\langle TF_j,TF_k\rangle\big).
\]

Thus merging blocks cannot increase the certificate. A single signed
block has zero excess and recovers the complete error. This comparison
does not depend on the numerical experiment. No block scheme can beat
the exact Gram minimum over the same legal family.

For illustration, use the 18 squarefree conductors through 30, retain
divisor-wavelet rows indexed by the divisors of 60, and hold the
complete-Gram coefficient vector fixed:

| Certificate | Floating value at that same vector |
|---|---:|
| Separate columns | 0.673975589 |
| Adjacent pairs of columns | 0.424492592 |
| Four consecutive blocks | 0.085035818 |
| One signed block | 0.009866930 |
| Exact projected anchors / complete Gram | 0.009866930 |

These figures are diagnostics, not separate rigorously optimized block
minima. The pair partition and four-block partition need not be nested;
their displayed ordering is observed, not a claim from merging alone.
The exact equality and dominance statements above are the rigorous
comparison. The strongest rational certificate obtained here is thus
available equally as a complete-Gram, exact-anchor, or one-block certificate.

## What sequence is justified, and what remains missing?

Let D_j be all squarefree d with 2≤d≤2^j, V_j their span,
F_j=P_{V_j}1, r_j=1−F_j, and e_j=||r_j||². Finite-dimensional projection
proves, unconditionally,

\[
e_{j+1}\le e_j,\qquad
e_j-e_{j+1}=\|F_{j+1}-F_j\|^2,\qquad
e_j\downarrow\operatorname{legalErrorInfimum}.
\]

The limit is the actual infimum because the nested union exhausts every
finite squarefree combination. Strict improvement requires a nonzero new
residual correlation; it does not follow solely from adding conductors.
Our computed nested rational candidates have disjoint error enclosures,
so their strict improvements are certified in the tested range.

Rational approximants are also justified: choose coefficients within
2^-j/|D_j| in each coordinate of the exact optimizer. Since ||g_d||≤1,
orthogonality gives a rounding excess at most 4^-j. The tail certificate
above can be refined to arbitrary precision for each fixed rational
vector by increasing N and the rounding scale. Taking running minima of
certified upper bounds produces a nonincreasing rational certificate
sequence converging to the same infimum. This does not identify its limit
as zero.

Here is a precise sufficient additional arithmetic estimate. Let B_j be
the new conductors, let C_j=G_{D_j,B_j}, and define

\[
S_j=G_{B_j,B_j}-C_j^TG_{D_j,D_j}^{-1}C_j,\qquad
t_j=b_{B_j}-C_j^TG_{D_j,D_j}^{-1}b_{D_j}.
\]

Linear independence makes S_j positive definite. Exact block elimination
gives the complete signed gain

\[
e_j-e_{j+1}=t_j^TS_j^{-1}t_j.
\]

A genuinely useful provider would prove, for some fixed κ>0 and all
sufficiently large j,

\[
\boxed{t_j^TS_j^{-1}t_j\ge\frac{\kappa}{j+1}\,e_j.}
\]

This explicit inequality involves complete arithmetic Gram matrices and
their residual correlations. It would imply e_j=O(j^-κ) by multiplication
of 1−κ/(j+1), hence errors tending to zero and RH. More generally a lower
fraction γ_j with 0≤γ_j≤1 and Σγ_j=∞ suffices. This is a sufficient
quantitative estimate, stronger than a bare assertion of density, and it
has **not** been proved here or assumed in any numerical certificate.

Positive gains without a divergent total fraction are insufficient.
Neither pointwise convergence, monotonicity, the small bound above, nor
the finite trend proves that the limiting residual is zero. A uniform
arithmetic gain estimate is the remaining substantive obligation.

Bagchi's Remark 8 supplies the published squarefree closure equivalence,
and his equivalent-weight discussion after Theorem 1 permits Q. The
repository's checked consumer `riemannHypothesis_of_legalErrorInfimum_zero`
can be used only once the zero equality has actually been proved.

## Repository changes and publication gate

1. Add `RH/QSquarefreeRationalUpperBounds.lean`, proving the seven-atom
   complete squared error is below **361/10000**, and transferring this
   bound to both actual infima. Its exact first-period reciprocal sum is
   195633097896924498929385142872658201 /
   5424658191543895143840000000000000000, which is below 0.0361.
2. Export that module from `RiemannResearch.lean`.
3. Add this memorandum and `SquarefreeRationalReproduction20261103.md`,
   containing all scripts and exact data as documentary code blocks.
   The workspace protects executable changes in the tools directory;
   no protected infrastructure is modified.
4. Add the verification record to the focused prime-tensor ledger.
   The 121-atom Python certificate remains distinguished from Lean results.

The stronger 121-atom result is not yet a Lean declaration. Its next
formalization tasks are the periodic centered-sum lemma, the Abel tail
bound, the exact CRT product mean, and a kernel-checkable arithmetic
certificate evaluation. None is silently supplied as a hypothesis to an
alleged unconditional Lean theorem.

The user approved the proposed change set with the instruction “patch”.
Publication uses `agent_workspace_checkpoint` with push enabled, after
validation of the final source and required dependents. No direct GitHub
write, alternate push route, or hosted CI substitutes for that gate.

## Reproduction

Reconstruct the named files from `SquarefreeRationalReproduction20261103.md`
in one local directory, preserving the `reference/` subdirectory. In that
directory:

```
python verify_certificate.py
```

This verifies the strongest saved result using only the Python standard
library. It does not regenerate or trust a floating-point optimizer.
Expected output includes `PASS: exact complete-Q certificate < 5873/1000000`.

With NumPy and SciPy available:

```
OPENBLAS_NUM_THREADS=1 python explore.py
OPENBLAS_NUM_THREADS=1 python certify.py
python gram_optimality.py
OPENBLAS_NUM_THREADS=1 python compare_methods.py
```

`explore.py` reproduces the full-Gram numerical solves;
`certify.py` creates exact rational enclosures for their rounded candidates;
`gram_optimality.py` checks the seven-atom optimality gap;
`compare_methods.py` compares certificates at the same complete-Gram vector.
The saved `exploration.json` is sufficient to run the exact certificate
generator without rerunning the floating stage.

## Sources and ownership of claims

- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis*, Proc. Indian Acad. Sci.
  (Math. Sci.) 116 (2006), 137–146. Remark 8 and the discussion after
  Theorem 1 support the RH context. https://arxiv.org/pdf/math/0607733
- NIST DLMF 5.15.1 supports the trigamma-series formula used for floating
  complete-Gram evaluation. https://dlmf.nist.gov/5.15.E1
- Existing source: `QTensorCertificateInfimum.lean`, `QTensorCertificate.lean`,
  `QCovarianceInverse.lean`, `ZetaTwoCRTReciprocalEnergy.lean`,
  `Analysis/FiniteHilbertGramProjection.lean`, and `Analysis/FiniteTensorTail.lean`
  at commit f7cf4a1a. These provide the existing exact error, projection,
  signed-block, infimum, and conditional-RH infrastructure.
- The numerical coefficients, exact arithmetic certificates, elementary
  centered-tail argument, and the proposed next estimate were developed
  for this request. No claim of mathematical novelty is made for the
  standard CRT, Abel summation, projection, or Schur-complement arguments.
