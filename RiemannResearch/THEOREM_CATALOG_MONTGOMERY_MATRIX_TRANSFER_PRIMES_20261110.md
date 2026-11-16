# Montgomery: actual-zero matrices, ordinate transfer, and signed prime correlations

Continuation (2026-11-16): [Uniform boundary and actual diagonal estimates](THEOREM_CATALOG_MONTGOMERY_SC_PROGRESS_20261116.md)
proves the sub-square-root endpoint corollary and the full interior diagonal estimate.
The complete signed-prefix estimate and the analytic SC transfer remain open.

Continuation (2026-11-14): [Exact signed interval and countable criteria](THEOREM_CATALOG_MONTGOMERY_INTERVAL_20261114.md)
adds sharp actual zero-count normalization and rational anchored reductions.
The signed cancellation and full PCC remain open.

Date: 2026-11-10. Development baseline: 869857d79633cf098a2431836349f11c52fd1f3e.
Continuation of MontgomeryGammaAudit20261110.md and THEOREM_CATALOG_MONTGOMERY_GAMMA_20261110.md.

## Outcome and proof status

| Requested obligation | Result of this development |
| --- | --- |
| Identify the spatial matrix with the actual-zero matrix and evaluate its diagonal | Completed for the stated compact C2 window and homogeneous integer block. Exact poles and logarithmic diagonal correction are retained. |
| Transfer smoothed complex-zero formulas to raw ordinates | Unconditional localized height-taper removal, stronger conditional horizontal transfer, exact signed identities, and an obstruction to the all-frequency positive-budget route. See the precise height-cutoff scope below. The complete transfer remains open. |
| Prove signed prime correlations above Fourier support one | Exact endpoint and signed-prefix identities, an unconditional logarithmic raw odd-gap bound, and a uniform odd-gap asymptotic using the proved PNT. Even-gap cancellation and the complete high-support asymptotic remain open. |

No theorem here proves Montgomery's pair-correlation conjecture or the Riemann Hypothesis.
An implication with an explicit analytic hypothesis is not a proof of that hypothesis.
All references to actual zeros use the repository's actual zeta-zero multiset and multiplicities.

## 1. The complete actual-zero matrix

Let F be a real, even C2 function supported in [-1,1]. Write

\[
N_T=\frac{T\log T}{2\pi},\qquad
h_{T,u}(z)=\int_{\mathbb R}
 \frac{T\,F(T(v-u))}{2\pi\cosh(v/2)}e^{izv}\,dv.
\]

For an actual nontrivial zero \(\rho=\beta+i\gamma\), set
\(z_\rho=(\rho-\tfrac12)/i=\gamma+i(\tfrac12-\beta)\).
The complete matrix is

\[
Z_{T,F}(n,m)=\sum_\rho m_\rho\,h_{T,\log n-\log m}(z_\rho).
\]

The sum includes both signs of the ordinate, with analytic multiplicity \(m_\rho\).
"Actual-zero matrix" means a matrix constructed from these zeta zeros.
It does not mean a matrix whose entries vanish. It is a smoothed single-zero
matrix, not the hard-height-cutoff double-pair statistic.

The Lean definitions are PrimeBandlimitedWeil.actualZeroEntry,
zeroNormalizer, normalizedDiagonal, and centeredZeroEntry. Set

\[
a_T=Z_{T,F}(1,1)/N_T,\qquad
\widetilde Z_{T,F}(n,m)=Z_{T,F}(n,m)/N_T-\mathbf1_{n=m}a_T.
\]

All diagonal entries of Z are exactly equal. Assume additionally
\(\int_{-1}^1F(x)\,dx=0\). Let \(D\in\mathbb N\), and let S be a finite set of positive integers at most D,
all with the same total number \(\Omega(n)\) of prime factors, counted with
multiplicity. If \(T\ge4\) and \(2D\le T\), then

\[
\widetilde Z_{T,F}(n,m)=E_{T,F}(n,m)\quad(n,m\in S),
\]
\[
E_{T,F}(n,n)=0,\qquad
E_{T,F}(n,m)=-\frac1{T\log T}\int_{-1}^1
 F(x)A(|\log n-\log m|+x/T)\,dx\quad(n\ne m),
\]
\[
A(t)=\frac1{2\sinh t}+\frac1{4\cosh^2(t/2)}.
\]

This is a full complex equality, with the spatial entry embedded in the complex
numbers. The proof first extends the gamma functional to shifted real tests,
proves reality and reflection, retains the exact Guinand--Weil pole identity,
and then proves the affine change of variables and support restriction.

Principal declarations:

- SignedWeilCorrelation.gammaFunctional_real_spatial and gammaFunctional_of_positive_support.
- Analysis.integral_affine_window and integral_window_restrict.
- PrimeBandlimitedWeil.gammaContribution_abs_spatial.
- PrimeBandlimitedWeil.centeredZeroEntry_eq_spatial.
- PrimeBandlimitedWeil.actual_zero_centered_quadratic_bound.

Consequently, for arbitrary complex coefficients c,

\[
\left|\sum_{n,m\in S}c_n\overline{c_m}\,
 \widetilde Z_{T,F}(n,m)\right|
 \le \frac{72M_2(F)}{\log T}\left(\frac DT\right)^3
 \sum_{n\in S}|c_n|^2,
\quad
M_2(F)=\int_{-1}^1x^2|F(x)|\,dx.
\]

This is now an estimate for the actual-zero matrix, with no RH or
prime-pair asymptotic among the hypotheses.

## 2. Exact diagonal and improved remainder

Define

\[
B(t)=A(t)-\frac1{2t},\qquad
c_F=-(\gamma_{\rm E}+\log(2\pi))F(0)
       +\int_0^1\frac{F(0)-F(x)}x\,dx.
\]

SechGammaDiagonal proves the regulated scaling identities, including the
logarithmic term, and the bound

\[
|B(t)-\tfrac14|\le \frac{11}{48}t\qquad(0<t\le1).
\]

For the same real, even compact C2 window, but WITHOUT a zero-mean assumption,
PrimeBandlimitedWeil.normalizedDiagonal_exact proves, for \(T>2\),

\[
a_T=\frac{1}{\pi N_T}\int_{\mathbb R}F(x)\,dx
 +F(0)+\frac{c_F}{\log T}
 -\frac2{T\log T}\int_0^1F(x)B(x/T)\,dx.
\]

The first term is the exact contribution of both poles. The generally nonzero
\(c_F/\log T\) is not removed by setting the ordinary mean to zero.

If the mean is zero, evenness gives \(\int_0^1F=0\), so the constant \(1/4\)
in B cancels. With
\(M_1(F)=\int_{-1}^1|x|\,|F(x)|\,dx\), Lean proves for \(T>2\)

\[
\left|a_T-F(0)-\frac{c_F}{\log T}\right|
 \le\frac{11M_1(F)}{48T^2\log T}.
\]

The final assembled theorem,
PrimeBandlimitedWeil.actual_zero_quadratic_corrected_bound, is

\[
\boxed{\;
\left|\sum_{n,m\in S}c_n\overline{c_m}\frac{Z_{T,F}(n,m)}{N_T}
 -\left(F(0)+\frac{c_F}{\log T}\right)\sum_{n\in S}|c_n|^2\right|
 \le\left[
 \frac{72M_2(F)}{\log T}\left(\frac DT\right)^3
 +\frac{11M_1(F)}{48T^2\log T}
 \right]\sum_{n\in S}|c_n|^2.\;}
\]

The centered quadratic identity is also proved exactly before taking a norm.
For a degree-k polynomial in integer modes bounded by \(D_0\), the full integer
length entering this estimate may be \(D_0^k\). Additional torus coordinates
do not remove the requirement on this full length.

## 3. Horizontal transfer to actual raw ordinates

This part concerns the finite multiset of actual zeros with \(0<\gamma\le T\),
repeated according to multiplicity. Let \(O_T(v)\) be the ordinate exponential
sum, and let \(C_T(v)\) be the reflected cosh correction defined in
ActualZeroOrdinate. The complex-zero sum equals \(O_T+C_T\) exactly.

MontgomeryHorizontalPairing.sharp_sub_raw_exact proves

\[
I_T^\sharp(u)-I_T^{\rm raw}(u)
 =2\int_{\mathbb R}e^{-2|s|}
   \Re\!\left(O_T(u+s)\overline{C_T(u+s)}\right)\,ds
  +\int_{\mathbb R}e^{-2|s|}|C_T(u+s)|^2\,ds.
\]

The cross term is signed and is retained. All integrability requirements are proved.

For each zero copy put \(\delta_\rho=\beta_\rho-\tfrac12\), and define the
existing nonnegative budget and its new averaged version by

\[
B_T(u)=\sum_{0<\gamma_\rho\le T}
 \left((e^{u\delta_\rho}-1)^2+\delta_\rho^2\right),
\qquad
\overline B_T(f)=\int_{\mathbb R}|f(\alpha)|
             \frac{B_T(\alpha\log T)}T\,d\alpha.
\]

For any continuous compactly supported signed test f, some absolute C>0,
all \(T\ge9\), and every \(\varepsilon>0\), Lean proves

\[
\left|\int f(\alpha)(F_T^{\rm raw}(\alpha)-F_T^\sharp(\alpha))\,d\alpha\right|
 \le\varepsilon\int|f|F_T^\sharp
       +(1+\varepsilon^{-1})C\,\overline B_T(f).
\]

A second version uses \(F_T^{\rm raw}\) as the reference. These imply:

1. If \(\overline B_T(g)\to0\) and the absolute complex reference pairing is
   bounded, every continuous compact test family dominated by g transfers.
2. Using the already proved unconditional \(F_T^{\rm raw}\le A\log T\), the
   stronger condition \((1+\log T)\overline B_T(g)\to0\) removes the separate
   bounded-complex-reference hypothesis.
3. Under that stronger one-point condition, a Gaussian-damped complex pairing
   limit transfers directly to the raw pairing limit:
   \[
   \int f(\alpha)e^{-(\alpha/\log T)^2}F_T^\sharp(\alpha)\,d\alpha\to\ell
   \quad\Longrightarrow\quad
   \int f(\alpha)F_T^{\rm raw}(\alpha)\,d\alpha\to\ell.
   \]
   The Gaussian-removal step consumes the existing unconditional theorem.

Principal declarations: pairing_sub_tendsto_zero_of_averagedBudget,
pairing_sub_tendsto_zero_of_log_averagedBudget, and
raw_pairing_limit_of_damped_complex_log_budget.

The budget decay and the complex pairing limit are explicit, unproved
research inputs. They are not asserted as facts about the actual zeros.

### Obstruction to a positive-majorant shortcut

MontgomeryHorizontalObstruction proves that a fixed off-line zero with
\(\delta_\rho\ne0\) has the fixed frequency \(\alpha=1/\delta_\rho\) at which

\[
B_T(\alpha\log T)/T\ge1
\]
for every sufficiently large cutoff. Hence it proves the exact equivalence

\[
\bigl[\forall\alpha,\ B_T(\alpha\log T)/T\to0\bigr]
 \quad\Longleftrightarrow\quad
\bigl[\forall\rho\text{ with }\Im\rho>0,\ \Re\rho=\tfrac12\bigr].
\]

This audits the all-frequency positive-budget approach. It does not assert
that every possible transfer using signed cancellation has this obstruction.

### Height-cutoff smoothing

MontgomeryHeightCutoff defines a weighted form factor on exactly the finite
multiset \(0<\gamma_\rho\le T\):

\[
F_T^w(\alpha)=\frac1{N_T}\Re\sum_{\rho,\sigma}
 w_\rho\overline{w_\sigma}\,
 e^{i\alpha\log T(\gamma_\rho-\gamma_\sigma)}
 \frac4{4+(\gamma_\rho-\gamma_\sigma)^2}.
\]

The weights are complex, and each zero copy is included. The hard cutoff is
exactly \(w=1\). An exact identity retains twice the signed cross term plus
the defect form \(D_T^w=F_T^{w-1}\). The coefficient-sensitive bound is

\[
D_T^w(\alpha)\le \frac CT\sum_\rho|w_\rho-1|^2.
\]

Suppose \(0\le\Delta\le T\), \(|w_\rho-1|\le1\), and \(w_\rho=1\) whenever
\(\gamma_\rho\le T-\Delta\). ActualZeroBandCount proves unconditionally that

\[
\sum_\rho|w_\rho-1|^2
 \le N(T-\Delta,T)\le C'(\Delta+1)\log T.
\]

Here \(N(a,b)\) is the actual multiplicity count in \((a,b]\).
Consequently, there are fixed positive constants A,B such that, for \(T\ge9\)
and every real \(\alpha\),

\[
|F_T^w(\alpha)-F_T^{\rm raw}(\alpha)|
 \le B\frac{(\Delta+1)\log T}{T}
       +2\sqrt{\frac{AB(\Delta+1)(\log T)^2}{T}}.
\]

The theorem height_sub_raw_tendsto_zero therefore allows any varying frequency
\(\alpha(T)\) and any admissible varying taper with

\[
\frac{(\Delta(T)+1)(\log T)^2}{T}\longrightarrow0.
\]

The concrete theorem linear_height_sub_raw_tendsto_zero instantiates the taper

\[
w_\rho=\min\!\left(1,\frac{T-\gamma_\rho}{\Delta}\right)
\]
for any fixed \(\Delta>0\), and proves \(F_T^w(\alpha(T))-F_T^{\rm raw}(\alpha(T))\to0\).
This result has no RH, zero-density, or pair-correlation hypothesis.

These weights are defined inside the cutoff only. Zeros above T are not
represented by this finite form. Thus this proves a genuine localized
height-taper removal, while identifying the original full-height analytic
matrix with an admissible taper still requires a separate tail comparison.

## 4. Signed additive prime correlations

Set \(a(n)=\Lambda(n)-1\), and

\[
R_N(h)=\sum_{x=0}^{N-1}a(x+2)a(x+2+h).
\]

ShortIntervalBoundary proves the exact triangular identity

\[
C(N,H)=2\sum_{1\le h<H}(H-h)R_N(h)+\mathcal B(N,H),
\]
where C is the existing centered short-interval off-diagonal and the boundary
correction is explicitly

\[
\mathcal B(N,H)=
2\sum_{h=1}^{H-1}\sum_{j=0}^{H-h-1}\sum_{x=0}^{j-1}
 [a(N+x+2)a(N+x+2+h)-a(x+2)a(x+2+h)].
\]

No endpoint term has been dropped. If

\[
E_N(k)=\sum_{h=1}^kR_N(h)
 +\frac N2[(k+1)\log(k+1)-k\log k],
\]
with \(0\log0=0\) and empty sums equal to zero, the exact signed-prefix reduction is

\[
C(N,H)+HN\log H
  =2\sum_{k=0}^{H-1}E_N(k)+\mathcal B(N,H).
\]

The analogous exact variance identity retains the separate diagonal error.
The raw/centered conversion also retains the shifted Mangoldt mass exactly.

An unconditional endpoint estimate is proved:

\[
|\mathcal B(N,H)|
 \le\frac23 H(H-1)(H-2)(\log(N+H+2)+1)^2.
\]

This coarse \(H^3\) estimate cannot justify dropping the correction throughout
the desired polynomial range. When logarithms are comparable, the normalized
upper bound is \(O(H^2\log N/N)\), so an additional restriction or a sharper
signed estimate is needed.

### Unconditional odd-gap results

For odd h, every nonzero product \(\Lambda(n)\Lambda(n+h)\) has a positive
power of 2 at one endpoint. The two exceptional sums are retained exactly
in OddGapPrimeCorrelation. This gives, for all N and odd h,

\[
0\le\sum_{x=0}^{N-1}\Lambda(x+2)\Lambda(x+2+h)
 \le2\log^2(N+h+2).
\]

OddGapPrimeAsymptotic consumes the existing proved
NumberTheory.PrimeNumberTheorem.WeakPNT, rather than assuming a PNT provider.
OddGapPrimeUniform then proves the strongest asymptotic in this branch:

\[
\boxed{\quad
 h(N)\text{ eventually odd},\quad h(N)\le N\text{ eventually}
 \quad\Longrightarrow\quad \frac{R_N(h(N))}{N}\longrightarrow-1.
 \quad}
\]

There is no RH assumption, no additional rate in PNT, and no condition such
as \(h\log N/N\to0\). The proof uses an exact three-mass endpoint identity
and a finite-head/PNT-tail argument that controls sublinear errors at every
argument in [0,2N].

The theorem covers all moving odd gaps in every polynomial range inside [1,N].
It does not control even-gap correlations. Large signed contributions of
opposite signs still have to cancel in the complete triangular sum.

## 5. Remaining research obligations

1. Connect the full-height smoothed single-zero matrix in Sections 1--2
   to the hard-height-cutoff pair statistic with a proved analytic comparison.
   A same-cutoff coefficient perturbation theorem does not establish that
   the analytic smoothing has the required support and boundary form.
2. Prove adequate horizontal transfer for the actual zeros. The averaged
   budget criteria above are sufficient conditions, not discharged estimates.
   The exact signed cross identity may permit a less restrictive route.
3. Prove the signed prime-prefix/endpoint estimate needed for
   \[
   C(N,H)=-HN\log H+o_\varepsilon(HN\log N)
   \]
   uniformly for \(N^\varepsilon\le H\le N^{1-\varepsilon}\), for each fixed \(0<\varepsilon<1/2\).
   Odd-gap information and PNT do not supply the required even-gap cancellation.
   The separate short-interval diagonal asymptotic must also be supplied.
4. Complete transition control near \(|\alpha|=1\) and retain all hypotheses
   in the prime-to-zero equivalence before claiming the full raw pair limit.

The repository's TriangularSingularSeriesProvider is an explicitly named
remaining provider obligation. Proved Euler-product convergence does not
silently instantiate it or establish an actual prime-pair estimate.

## 6. Source map

All paths below are relative to RiemannResearch/.

| Module | New role |
| --- | --- |
| RH/WeilGammaSymmetry.lean | Reality, reflection, and the gamma functional for shifted real compact C2 tests. |
| Analysis/AffineWindowIntegral.lean | Exact affine integral substitution and compact-window restriction. |
| Analysis/PrimeBandlimitedMatrix.lean | Actual-zero matrix identity, centered quadratic estimate, exact scalar-diagonal assembly. |
| Analysis/SechGammaDiagonal.lean | Regulated integrals, logarithmic scaling, and the 11/48 remainder estimate. |
| Analysis/PrimeBandlimitedDiagonal.lean | Explicit c_F and diagonal gamma expansion. |
| Analysis/PrimeBandlimitedMatrixDiagonal.lean | Complete pole/diagonal identity and corrected actual-zero quadratic bound. |
| Analysis/WeightedSqrtTransfer.lean | Abstract Young-bound convergence argument. |
| Analysis/MontgomeryHorizontalPairing.lean | Exact signed horizontal identity and averaged transfer criteria. |
| Analysis/MontgomeryHorizontalObstruction.lean | Fixed off-line-zero lower bound and the all-frequency budget equivalence. |
| Analysis/ShortIntervalBoundary.lean | Exact endpoint, triangular, prefix, and variance identities. |
| Analysis/OddGapPrimeCorrelation.lean | Exact exceptional power-of-two sums and unconditional odd-gap estimate. |
| Analysis/OddGapPrimeAsymptotic.lean | Actual proved PNT consumer for fixed and growing odd gaps. |
| Analysis/OddGapPrimeUniform.lean | Uniform moving odd gaps all the way up to N. |
| Analysis/CauchyWeightPerturbation.lean | Exact signed Cauchy-form perturbation and reverse-triangle estimate. |
| Analysis/ActualZeroBandCount.lean | Actual multiplicity count and coefficient error in a height band. |
| Analysis/MontgomeryHeightCutoff.lean | Uniform taper removal, width criterion, and unconditional linear-taper example. |

## 7. Verification evidence and scope

All new modules are exported from RiemannResearch.lean. Development checks
use Bazel/BuildBuddy. No sorry, admitted proof, custom axiom, unsafe result,
or new unproved analytic provider is introduced.

- Saved gamma-symmetry, affine-integral, and matrix modules:
  job_Zx16_lwnf6iMgh_SXNobLweDuMTIYEGL, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/3fd65e92-9b8e-4bed-8e6d-a604ce18f667
- Saved matrix with exact scalar-diagonal assembly:
  job_DX6kkhVny86q-QrgiUUs1jLleMgu0zYv, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/403e8f4d-f8fc-4217-8995-f19cc1890d4c
- Saved diagonal modules:
  job_igPg_eJDyBUk7e4IAasH5Yj56F4JoBe2, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/ba61aab9-2361-4e12-9285-e1066765509f
- Saved complete matrix/diagonal module:
  job_lP2LKojWvsDDG-wZrBsmZvHZfTcK9oX5, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/6e2df7a4-58b3-4f1f-9eb5-2c61facb64b8
- Complete corrected matrix/diagonal proof and explicit axiom guard:
  job_Xz6US6d-Zqk5IVpfZ0-PhB6cjs426tc_, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/d39f2aea-8b52-40e8-b290-e3f90d4e52b0
- Horizontal transfer and obstruction modules:
  job_TyhZopWqzBza8y2Zvta2CPsLXYpx0ldI, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/66d46e61-68f3-444a-b84b-ab61e8830b00
- Expanded logarithmically weighted horizontal transfer:
  job_Ou90W8m46LilTcHTlVRlGlPHJbpulRU4, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/1489ae46-a895-40a5-add2-fcc0f162a499
- Saved uniform odd-gap module and all four transitive prime modules:
  job_4Rm6C4uCVlRI8w_xk_-aMKFnM7k4Hcnh, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/ff055898-1753-42d6-a524-61ec031a17d9
- Saved unconditional height-transfer module and its two support modules:
  job_ZA_OXw-tHwK20GmU00gScTcVWq1FI-wK, succeeded, verified=true, exit 0.
  Its in-source axiom guard for linear_height_sub_raw_tendsto_zero also passed.
  https://app.buildbuddy.io/invocation/a1bde8ff-e46a-4316-b49f-f94460ba71fe
- Prime branch explicit axiom guards:
  job_-fqlKCY8bV_OMuSytodhhroC6L1Zxo8y, succeeded, verified=true, exit 0.
  https://app.buildbuddy.io/invocation/57c10596-d1d4-4a54-85c0-c83a1b50e65f

The explicit guard for actual_zero_quadratic_corrected_bound asserts exactly
[propext, Classical.choice, Quot.sound]. The same standard-foundation audit
passed for WeakPNT and the principal prime results including the uniform
odd-gap theorem, and for the concrete fixed-width height-taper theorem.
These are kernel axiom reports, not merely source-text scans.

The final publication checkpoint additionally runs the full
//:RiemannResearch build, source audit, commit, and push. The release response
records its terminal job, published commit, and verification link. Development
checks are not represented as whole-project validation.

## References and provenance

- User-provided MontgomeryGammaAudit20261110.md, especially Sections 4--6:
  spatial matrix and regulated diagonal route.
- Garrett, Guinand's explicit formula, Theorem 0.0.1:
  https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2015-16/04_Guinand_explicit_fml.pdf
- DLMF 5.9.16, digamma representation: https://dlmf.nist.gov/5.9.E16
- Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, unconditional complex-zero
  pair framework: https://doi.org/10.4064/aa230612-20-3
- Montgomery--Soundararajan, Primes in short intervals:
  https://arxiv.org/abs/math/0409258
- Chan, A note on Primes in Short Intervals:
  https://arxiv.org/abs/math/0503441

References motivate conventions and reductions. None is imported as an axiom.
