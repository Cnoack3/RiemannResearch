# FRZ strengthening: formalization and sharper research targets

Source manuscript: `FRZ_Strengthening_2026-11-10.pdf` (18 pages), including
Section 8 First–Fifth. The spelling/date variant in the request was resolved
to that manuscript. Baseline repository commit:
`4990152321b0c1926efeeebc10cc0e33b46cd562`.

The addition contains **41 modules and 258 public theorem/lemma declarations**
(6,238 source lines), all exported from `RiemannResearch.lean`. See the
[declaration manifest](FRZ_DECLARATIONS_20261110.md) for module links, hashes,
and declaration names.

This catalogue separates proved identities and estimates, proved implications
with named analytic hypotheses, and mathematical obligations still open.
It does **not** certify every displayed assertion in the manuscript. In
particular, the unconditional classical S1 providers and the complete
growing-block asymptotic estimates have not all been formalized.

## What is stronger than the manuscript

1. **Actual Pareto inverse-Gram transfer at every fixed Taylor order.** The
   source built from actual zeros and retained horizontal moments is compared
   with the actual von Mangoldt observation vector, then passed through the
   actual Pareto inverse matrix. The squared metric error is bounded by an
   explicit matrix/frequency budget divided by `(log T)^(4J+2)`. Signed cross
   terms and the complete target capacity deficit are retained.
2. **Sharper arithmetic budgets.** On prime support,
   `J4 ≤ Δ² J2 ≤ Δ⁴ E²/2`; the factor 1/2 is sharp. Product-fiber bounds extend
   to different degrees d,e with constant `choose(d+e,d)`. Unrestricted
   supports have bounds in terms of their actual multiplicative energy and
   coefficient-weighted fiber multiplicities. Exact integer and rational
   frequency gaps improve to `1/M` and `1/M²`.
3. **A single signed residual defect.** A necessary-and-sufficient condition
   controls the residual S1 energy through one combined signed defect,
   allowing cancellation between energy, polynomial, and correlation errors.
   Exact normal-equation Pythagoras and optimality hold. The actual-zero
   integration formula retains the gamma integral and both endpoint terms.
4. **Full-height centered measure criterion.** Under an eventual mass bound,
   existence of all nonconstant Fourier limits is equivalent to existence of
   a centered weak limit. A candidate limit and convergence of total mass
   need not be supplied. One subsequence works for every continuous test and
   every Fourier mode. Explicit logarithmic-square concentration is proved
   for marked laws with an exponential mark tail.
5. **All-order endpoint and uniform weighted classes.** The A2 endpoint,
   arbitrary fixed higher even-order endpoints, and saturated sum envelopes
   are proved. Any positive extra weight Φ tending to infinity gives uniform
   convergence on its weighted unit ball. This extends to all positive
   rational modes, allowing the finite prime supports to vary. Interpolation
   gives the explicit `C (log T)^(1-s) W_s` bound for `2 ≤ s ≤ 4`.

These statements retain the hypotheses specified below. They do not prove
RH, Montgomery pair correlation, convergence of actual nonconstant energy
modes, or a dimension-independent bound for the Pareto inverse matrix.

## Notation and hypotheses

For a positive integer support S and coefficients a, put

\[
A(t)=\sum_{n\in S}a_n n^{it},\quad
E=\sum_{n\in S}|a_n|^2,\quad
b_q=\sum_{n/m=q}a_n\overline{a_m},\quad
J_j=\sum_{q\ne1}|b_q|^2|\log q|^j.
\]

All repeated ratios are aggregated before taking squared norms. All actual
zero sums use analytic multiplicities and the interval `0 < γ ≤ T`.
The logarithmic width is Δ. Let `L=log T` and let w denote the arithmetic
mode weight used in the source (`1+|log n+log m|` for positive pairs).

`UniformSelbergDensity a` is an **explicit unproved provider in these
applications**. It bounds horizontal tails of the actual zero multiset with
an exponential in `a log T`. The endpoint modules use `a=1/4`; the Pareto
transfer allows any positive a. These are checked conditional theorems,
not new axioms and not a proof of the classical density theorem.

The S1 modules define the actual discrepancy and its primitive. Their
`MeanSquareError`, `ModeCorrelationError`, and `CanonicalNormalization`
are named analytic assertions, not declarations silently assumed globally.
The exact finite and integration identities do not require these providers;
the quantitative residual theorem takes the needed bounds explicitly.

## Manuscript coverage

| Manuscript item | Formal coverage | Remaining obligation |
|---|---|---|
| Exact aggregation and constant mode | Product/ratio energies, `b_1=E`, off-diagonal energy, exact rational Fourier polynomial | None for these finite identities |
| Theorem 1 / (7)–(10) | Actual-zero Abel identity, second integration, exact boundaries, actual S1 primitive, MV26 and J4 remainder bound | Classical S1 estimate, pointwise endpoints, smooth gamma asymptotics, and final uniform asymptotic assembly |
| Complementary S estimate (11) | Existing counting/first-integration machinery is reusable | Complete S mean-square specialization and minimum envelope are not added here |
| Prime identities (12) and quartic bound | Exact J2/J4 identities; improved sharp factor 1/2 | None for the finite identities/inequalities |
| Fixed and bounded multiplicative degree | Constructive binomial fiber bounds, repeated primes allowed, off-diagonal E² subtraction | Full degree-profile Minkowski summation not assembled |
| Theorems 6–7 / (17d)–(17k) | Exact actual S1 residual reduction; mixed-degree arithmetic; partial-shift bias; homogeneous cancellation | Actual S1 spectral providers, prime-power tail estimates, polynomial bias extraction with its uniform error, final operator rates |
| Resonance (18) | Exact integral kernel, value at zero, closed form, min envelope, moving `c/T` resonance | Nearest-prime-power Landau estimate (19) is not proved by this addition |
| Horizontal moments and remainder | Explicit actual even-moment bounds and fixed-order normalized Taylor bounds | Classical density provider remains explicit |
| Theorem 8 / A2 endpoint | Actual corrected rational endpoint and literal sample/Haar/energy expansion | Density provider only; no horizontal moment limit needed for the remainder |
| Higher even corrections | Exact corrections, global saturation, fixed endpoints at every order, summed envelopes | No uniformity as Taylor order grows with T |
| Stronger uniform topology | Arbitrary diverging Φ, finite-prime and all-positive-rational modes | No uniform little-oh on the entire unstrengthened A2 unit ball is claimed |
| Proposition 9 | Full real-atTop existential centered weak-limit equivalence and actual all-mode subsequence | Actual nonconstant Fourier limits are still unknown |
| Equation (39) | Exact logarithmic-square marked-energy concentration and RN representation | Complete actual joint weak-limit / unbounded moment identification remains open |

## Section 8 First: the actual working Gram matrix

Modules: `RH/RamanujanFRZSignal.lean`, `RH/RamanujanFRZHierarchy.lean`,
`Analysis/ActualEvenHorizontalMomentRate.lean`.

Let `v_J(T)` be `correctedVector J s T`, let `λ=signal s`, and let H be
the actual Pareto Gram matrix. The source includes every retained even
horizontal moment through degree 2J. The exact decomposition keeps the
signed inverse-metric cross term:

\[
\|v_J-\lambda\|_{H^{-1}}^2
=\|v_0-\lambda\|_{H^{-1}}^2
+2\langle v_0-\lambda,v_J-v_0\rangle_{H^{-1}}
+\|v_J-v_0\|_{H^{-1}}^2.
\]

`eventually_corrected_metric_all_orders` proves, for every fixed J,

\[
\|v_J(T)-\lambda\|_{H^{-1}}^2
\le \frac{\mathcal B_s(w_J)}{L^{4J+2}},\qquad
\mathcal B_s(w)=\sum_{i,j}|(H^{-1})_{ij}|w_iw_j,
\]

uniformly over finite supports satisfying `log q ≤ L/8` and
`log q ≤ aL/2`. The actual coordinate weight is

\[
w_J(q)=2\pi\sqrt q\left[B+
\left(\frac2a\right)^{2J+2}\frac{2C}{3}(\log q)^{2J+2}\right].
\]

Thus the logarithmic exponent does not hide growth of the frequency weights,
support, or inverse matrix. The J=1 specialization has exponent 6.

`corrected_target_error_exact` identifies the complete normalized Pareto
approximation error as

\[
\|1-f_{J,s,T}\|^2
=\frac1{C_s}-1+
\frac{\|\operatorname{screenedSource}(\lambda,v_J)\|_{H^{-1}}^2}
{\langle\lambda,v_J\rangle_{H^{-1}}^2}.
\]

If the metric error is at most `ε² C_s`, with `0≤ε<1`, then
`corrected_target_error_le_of_budget` gives

\[
\|1-f_{J,s,T}\|^2
\le \frac1{C_s}-1+\frac{\varepsilon^2}{C_s(1-\varepsilon)^2}.
\]

This is a concrete bridge for a corrected actual-zero source into the
working Pareto inverse metric. It is not an identification of the empirical
zero Gram matrix with the Pareto matrix. Controlling the capacity deficit
and the complete inverse budget on a cofinal family remains necessary.

## Section 8 Second: arithmetic interactions and sharp energy

The arithmetic modules prove:

\[
\sum_q|b_q|^2=\sum_k\left|\sum_{nm=k}a_na_m\right|^2,
\qquad b_1=E.
\]

For `Ω(n)≤d`, including repeated prime factors, the product-fiber constant
is `choose(2d,d)`. Subtracting the diagonal gives the factor
`choose(2d,d)-1`. For two supports bounded by degrees d and e the analogous
constant is `choose(d+e,d)`, and unequal total degrees have disjoint product
frequencies. For unrestricted supports, actual product energy or weighted
fiber multiplicities replace a worst-case binomial constant.

On prime support the exact centered identity is

\[
J_4=2EM_4+6V^2,
\quad J_4\le\Delta^2J_2\le\tfrac12\Delta^4E^2.
\]

An equal-weight two-point example attains the last constant. The key
declarations are `prime_rationalAutocorrelation_fourth_eq_centered`,
`prime_rationalAutocorrelation_fourth_le_half_diameter`, and
`weightedFourthFrequencySpread_two_points`.

`PartialMultiplicativeShifts.lean` identifies integer-ratio coefficients
with partial-shift correlations, proves reciprocal conjugation, preserves
the signed Hermitian bias, and proves its bound by `2 E Σ|α_k|`. Shifts with
`log k>Δ` vanish exactly. `HomogeneousPrimePowerCovariance.lean` proves the
bias is identically zero on a single degree block.

`RationalFrequencyHeightSeparation.lean` gives the explicit gaps `1/M` and
`1/M²`; `ActualRationalAutocorrelation.lean` makes the finite exponential
polynomial literally equal to `|A|²−E`, including its actual-zero sum.

The full growing-support two-term operator expansion is not certified
solely by these finite identities. Its analytic polynomial extraction and
actual S1 approximation estimates are listed below.

## Section 8 Third: retain one signed defect

Modules: `SpectralResidualMeanSquare`, `SpectralDerivativePairing`,
`ActualIntegratedDiscrepancy`, `ActualZeroAbelPairing`,
`ActualZeroIntegratedPairing`, and the literal Dirichlet consumer.

For an actual S1 primitive U and a finite exponential polynomial P,
`SpectralResidualMeanSquare.lean` proves the exact identity

\[
\int_0^T|U-P|^2=T(C-E_P)+D,
\]

where D is the single signed sum of the U-energy defect, polynomial-energy
defect, and minus twice the real weighted mode-correlation defect.
An upper bound on this D is necessary and sufficient for the corresponding
residual bound. Bounding the separate absolute errors is sufficient but
stronger. Normal equations also give exact Pythagoras and optimality within
the chosen finite trial span.

The separated-frequency theorem retains local weights; its uniform-gap
corollary gives

\[
\left|\int_0^T(U-P)F''\right|^2
\le \left(\int_0^T|U-P|^2\right)(T+26/\delta)J_4.
\]

`actual_zero_remainder_sq_le` attaches this bound to the actual zero sum,
with exact gamma integral, signed endpoint terms, and exact polynomial
integral retained. The literal Dirichlet consumer uses the aggregated
rational frequencies of `|A|²−E`. Its normalized statement is

\[
\left|\mathcal Q_T-E-\frac{\operatorname{Correction}_T}{N(T)}\right|^2
\le \frac{B_X(T)(T+26M^2)J_4}{N(T)^2},
\]

where `B_X(T)` is the explicit spectral approximation budget, with the
actual energy/mode providers and their local separation weights retained.
This holds for `T≥2`, positive support bounded by M, and `N(T)≠0`.

The stronger target `O(TE/log T)` for the signed residual integral has not
been proved. Nor is it assumed under a renamed error premise: the current
quantitative theorem exposes actual S1 energy and individual mode providers.
For the large-cutoff strategy, the sharp next target is a bound on the
single combined signed defect D, together with the polynomial bias estimate.

## Section 8 Fourth: centered energy, common subsequences, regularity

The actual energy measure is

\[
\nu_T=\frac{L}{T}\sum_{0<\gamma\le T}
m_\rho(\beta-\tfrac12)^2\delta_{\theta(\gamma)}.
\]

`ActualPrimeTorusEnergy.lean` proves the exact mass and Fourier coefficients,
the Selberg mass bound, exchange with absolutely convergent Fourier series,
and a weak subsequence valid for all continuous tests. The measure uses all
actual zeros with multiplicity, without assuming RH.

`PrimeTorusEnergyLimits.actual_centered_limit_iff` is the full-height
existential equivalence: all nonconstant Fourier coefficients converge iff
the centered measures converge weakly against every continuous test. Only
an eventual mass bound is required in the general theorem. Haar mass is
invisible to zero-Haar-mean tests.

`ActualPrimeTorusHorizontalExpansion.lean` identifies the literal statistic

\[
\Psi_T(f)=L\left[\frac{\sum_\rho m_\rho f(\theta(\gamma))
-N(T)\int f\,dH}{T}-\int f\,g_P\,dH\right]
\]

and proves at A2

\[
\Psi_T(f)-\tfrac12\int D_P^2f\,d\nu_T\longrightarrow0.
\]

Here `D_P²f` denotes the continuous Fourier-defined
`directionalSecondSeries`; the separate analytic `HasDeriv` identification
is not asserted by this bridge. The sign follows from
`D_P² e_k=−u_k² e_k`. A weak energy subsequence gives
the third coefficient for every A2 test along that same subsequence.
Centered weak convergence alone suffices for the full-height limit; a
separate limit of total horizontal energy is unnecessary.

For a marked law with probability phase marginal H, `a>0`, `K≥1`,
and `P(|Y|>t)≤K exp(−at)`, the marked-energy modules prove absolute continuity,
Radon–Nikodym representation by conditional second-moment density, and

\[
\int_{\theta\in E}Y^2\,d\eta
\le\frac h{a^2}\left[\log^2(K/h)+2\log(K/h)+2\right],
\quad 0<h=H(E)\le K.
\]

Here E is measurable. The manuscript's exact additional factor `1/(2π)`
is included in `scaled_energyMarginal_le_log_square`. No independence is
used. These estimates do not prove uniqueness of the actual horizontal
limit or convergence of its nonconstant modes.

`ActualPrimeTorusMarkedLaw.lean` goes further than a supplied abstract law:
it constructs the actual empirical joint law of phase and
`Y=L(β−1/2)`, proves that it is a probability measure when `N(T)>0`, and
identifies exactly, for `T>1` and `N(T)>0`,

\[
\nu_T=\frac{N(T)}{TL}\,\operatorname{energyMarginal}(\eta_T).
\]

The existing actual zero-count lower bound and the density provider give an
eventual common exponential mark-tail constant. The quadratic tails obey

\[
\int_{|Y|>R}Y^2\,d\eta_T
\le K e^{-aR}\left(R^2+\frac{2R}{a}+\frac2{a^2}\right),
\]

and tend to zero uniformly over sufficiently large heights. This proves
the actual uniform integrability ingredient. The passage through joint weak
limits and identification with every previously extracted energy limit is
still a separate obligation.

## Section 8 Fifth: endpoint hierarchy and moving tests

`ActualRationalHorizontalEndpoint.lean` proves the exact correction,
diagonal cancellation, conjugation, fixed-mode convergence, and the A2
endpoint by dominated convergence. The literal torus expansion above uses
this theorem rather than assuming the final statistic has a limit.

Retained order r means adding the first r nonconstant terms
`Σ_{j=1}^r u^(2j) M_(2j) / ((2j)! T)` to the centered ordinate
statistic minus its arithmetic main term. For every fixed r≥1 the
higher-order modules prove the global saturated estimate

\[
|R_{r,T}(n,m)|\le K\frac{w(n,m)^{2r}}{L^{2r-1}}
\min\{1,w(n,m)^2/L^2\}.
\]

They also prove the summed envelope with one common eventual threshold for
all coefficient families. Consequently, if `Σ|c|w^(2r)<∞`, then
`L^(2r-1) Σ c R_(r,T) → 0`. No horizontal moment limit is required.

For r=1, the arbitrary-Φ result gives `L Σ c R_(1,T) → 0` uniformly over
`Σ|c|w² Φ(w)≤1` for every positive diverging Φ. Arithmetic-height sublevels
are proved finite, including over all positive rational numerator/denominator
pairs. This does not construct a countably infinite prime torus measure.

For r=1, `ActualRationalHorizontalInterpolation.lean` proves the explicit
bound `K L^(1-s) Σ|c|w^s`, simultaneously for real `2≤s≤4`. The constants and
height thresholds for the higher-order hierarchy may depend on r; no
growing-order claim is made.

## Obligations that remain open

1. Formalize the unconditional classical mean-square and correlation
   providers for the actual normalized S1 primitive. Identify its canonical
   constant without importing an RH-dependent refinement.
2. Prove the prime-power spectral tail bounds and extract `T C_X` from the
   exact polynomial integral with its stated uniform error. Combine these
   with gamma/endpoints and counting normalization to certify the complete
   manuscript Theorems 1, 6, and 7 and their growing-support corollaries.
3. Prove the stronger combined signed-defect / residual bound needed for
   corrected `O((log T)^−2)` on growing spaces. The reductions alone do not
   establish this rate.
4. Prove convergence of the actual nonconstant horizontal-energy modes.
   Compactness and quantitative absolute continuity do not imply it.
5. Complete the actual joint marked weak-limit and unbounded quadratic
   moment identification, then attach all marked-law regularity statements
   to each actual energy subsequence. Full subcritical exponential RN
   regularity is an additional paper-level strengthening, not yet checked.
6. Prove the precise near-prime-power Landau estimate (19), and assemble the
   full mixed degree-profile bound if that route is pursued.
7. Control the actual cofinal Pareto capacity deficit and inverse-matrix
   budget. The accurate corrected source is not itself a proof of RH.

## Verification and provenance

Every accepted source is ordinary Lean 4/mathlib mathematics with no added
axioms or proof placeholders. Acceptance uses server-side
`bazel build --config=buildbuddy`; a submitted job or timed-out check is not
reported as a proof. A source/declaration manifest accompanies this catalogue.

Representative accepted checks during development:

- Actual Pareto source, all-even moments, resonance kernel:
  BuildBuddy `a85356a1-47bf-4bc2-803f-3440f748d734`.
- All-orders actual Pareto metric:
  `c9351dfb-d886-4490-9af5-151d6a2f955f`.
- Literal sample/Haar/energy expansion and centered-limit transfer:
  `dc1ae6c1-bcdd-4848-aa20-20ef7626676b`.
- Nine-module finite arithmetic bundle:
  `a33f09a3-8f42-4a32-87e1-2d8be33c1f3a`.
- All twelve endpoint modules, including interpolation and all-rational Φ:
  `8798d106-0116-437a-b6b2-697b09908fc3`.
- Actual-zero twice-integrated S1 theorem:
  `ad2586a4-bd98-4949-b99a-b45c72a391f5`.
- Measure core: accepted job `job_W0tUemubeAVMJllButE97stmyBRAd3KK`.
- Marked-law, actual uniform integrability, and normalized concentration:
  `f444f0f3-bc9b-4a5a-8f37-8ef567aaafea`.
- Literal rational autocorrelation/actual-zero bridge:
  `e17a2b8e-bebf-484d-9b4f-2d6198d6627c`.
- Literal normalized Dirichlet quadratic-form consumer:
  `64327e57-538a-4d3d-b8de-34c0d5887663`.

All 41 modules were then imported together in the root workspace. The
combined Bazel/BuildBuddy check succeeded with exit 0 and `verified=true`:
job `job_c0mFjavPUstwwj6pKYaz0jvx7UgKrIK8`, invocation
[056adb6f-5507-44aa-a5c6-ea1b651fc454](https://app.buildbuddy.io/invocation/056adb6f-5507-44aa-a5c6-ea1b651fc454).
The final publication checkpoint additionally audits the exported source
revision. Temporary check snippets are not part of the publication.

External analytic provenance: Ford–Zaharescu's uniform Landau/density
method; Montgomery–Vaughan's separated-frequency mean value theorem;
Chirre–Quesada-Herrera, arXiv:2006.08503v2, equation (1.5), for the recalled
unconditional S1 mean square. The latter paper's stronger conditional
second-order result is not used as an unconditional input. The source
manuscript contains the full bibliographic references. No literature-novelty
claim is made for these formalizations or rearrangements.
