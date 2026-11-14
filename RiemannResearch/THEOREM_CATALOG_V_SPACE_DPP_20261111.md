# V-space, determinantal laws, microscopic scaling, and duality

Source: the user-provided **V_vector_space_RH.pdf**, titled *Prime-power vector
spaces, zeta-zero sampling, and the topology of the RH obstruction*
(16 September 2026). Audit and extensions: 11 November 2026.
Inspected starting revision: `b4d564c6cf909906b66481aa5f2eecc4d0616d8c`.

This is a coverage ledger and a research continuation. It is **not a claim that
every result cited in the PDF has now been formalized**, nor a proof of RH or
Montgomery's pair-correlation conjecture. New source contains no placeholders,
project-local axioms, or substituted arithmetic coefficients.

“ZMF” is interpreted here as Ford--Meng--Zaharescu (FMZ). Ford--Zaharescu (FZ)
and Ford--Soundararajan--Zaharescu (FSZ) are also relevant. Their results must
be distinguished from the explicit assumptions in the corresponding Lean
declarations.

## 1. Coverage of the PDF

“Conditional” below describes a declaration's exact type; some missing inputs
are classical published theorems, rather than open mathematical conjectures.

| PDF result | Lean coverage and precise remaining issue |
|---|---|
| §1 full Dirichlet log/exp equivalence | `PrimePowerFormalCoordinates` proves all-degree local inverse identities. `PrimePowerFormalCoordinates.dirichletExpLogEquiv` in `PrimePowerMultiplicativeEquiv.lean` reconstructs a unique globally multiplicative arithmetic function from every prime-local logarithmic family; `dirichletExp_eta` gives the constant-one function on positive integers. This is a coefficientwise formal Euler-factor realization, with no convergence hypothesis. |
| §2 coordinate recovery and sampled completeness | Existing `SampledGaugeCompleteness`; new `SampledGauge.sampled_orbit_closure_eq_support` removes the full-support restriction. It assumes the stated phase-average limits. |
| §2 actual-zero Fourier cancellation | The Fourier-to-Haar/orbit bridge is proved in `ZeroOrdinateEquidistribution`. Actual ordinate estimates retain analytic inputs. Published unconditional cancellation is not a new axiom or a discharged provider here. |
| §2 independent prime phases and compact infinite orbit law | `CompactGaugeOrbit` proves norm continuity, compactness, and exact norm preservation. New `CompactGaugeOrbitLaw.existsUnique_orbit_limit` constructs the unique torus probability law and proves infinite Hilbert-orbit weak convergence from all joint finite-character limits. No Haar or independence premise is imposed. `ActualInfinitePrimeTorus.existsUnique_actual_orbit_limit` now supplies the actual multiplicity-weighted empirical specialization under the explicit `UniformSelbergDensity (1/4)` hypothesis. |
| §3 exact sampled energy | Existing finite signed covariance/Parseval identities. The PDF's general trace-norm operator convergence is not fully formalized by the finite identities. |
| §3 no scalar weighted frame | New `SampledGaugeSupport` supplies the coordinate energy identity and weighted-frame obstruction on any infinite nonzero support, including sparse support. Completeness does not give a lower frame bound. |
| §4 signed arithmetic correction | Existing rational FMZ formulas retain the arithmetic correction and exact diagonal. `ActualRationalFMZRate` explicitly assumes `UniformSelbergDensity (1/4)` for its actual-ordinate rates. |
| §4 bounded prime-power correction | New `PrimeBlockCovariance` proves support-independent finite geometric/prime-block bounds, including the full finite-prime sum with constant $\log 2/[\pi(\sqrt2-1)]$. Infinite self-adjoint extension and norm optimality are not claimed as new Lean results. |
| §4 finite-height counterexamples | Existing `FinitePolynomialSampling` supplies vanishing sample polynomials and the lower-bound obstruction. New `FinitePolynomialResonance` proves the upper obstruction, including exact coefficient energy, the centered estimate, and the concrete powers-of-two phases. |
| §5 zeta Hilbert kernel | New `ZetaDirichletKernel` realizes the actual integer Dirichlet-series feature vector, its zeta inner product and finite Gram energy, with bounded evaluation on the right half-plane. Lean uses the conjugate-first convention. |
| §5 prime-power log kernel and Fock regrouping | `LogEulerFeature` constructs the actual prime-power logarithmic Hilbert feature. `CoherentFock` constructs square-summable coherent vectors and proves their exponential mixed Gram identity. `ZetaFockKernel` obtains the actual zeta kernel from Mathlib's proved Euler product. `ZetaDirichletTotality` and `ZetaFockSpan` identify the zeta-generated closed subspace with all integer l2 and construct an integer Hilbert basis with the Dirichlet expansion. This proves the Hilbert conclusion without the PDF's explicit occupation-regrouping formula; that particular combinatorial coefficient identity is not asserted here. |
| §5 obstruction to continuation | Strengthened `RealZetaNonvanishing` and `ZetaKernelObstruction` rule out a positive Gram kernel on any domain meeting $0<\Re s<1/2$. No RH premise. |
| §6 dense classes and zero topology | Existing `ZeroDivisorTopology` proves dense finite-coordinate classes, vanishing tails, zero-divisor invariance under exponential factors, and the discontinuity reduction with its continuation-formula premise. |
| §6 sharp prime-power evaluation threshold | `PrimePowerEvaluation.exists_finite_bound_iff` proves boundedness exactly when Re(w)>sigma+1/2, including boundary failure by prime reciprocal divergence. `evaluation_hasSum`, `evaluation_bound`, and `vector_norm_sq` give the actual convergent functional and its Riesz-vector norm on l2 coordinates. |
| §7 exact cumulative and cutoff Gram | Existing `CumulativeTailKernel` retains complex cross terms and the cutoff boundary. Existing cell/affine modules preserve the background and all square remainders. |
| §7 free optimum, correction, and tail cost | Existing `FiniteCumulativeCellEnergy` already contains exact correction cost and boundary-reset refinements. The optimizer is not the prescribed von Mangoldt vector. |
| §7 tridiagonal inverse | New `FiniteCumulativeGramInverse` proves both inverse identities in operator form, including the endpoint term before setting it to zero. |
| §7 summation unboundedness and truncated von Mangoldt divergence | `MangoldtCumulativeDivergence` proves that the actual von Mangoldt truncations converge in the weighted source Hilbert space for s>1, their cumulative energies are finite for s>0 and tend to infinity for s<=2, and the finite-cutoff main-term ratios tend to zero whereas psi(x)/x tends to one. It proves summation unboundedness for 1<s<=2. The PDF's general all-s>0 cluster argument remains unformalized. |
| §7 damped-energy RH criterion | Existing `ChebyshevEnergyCriterion` proves sufficiency and the sharp off-line-zero pole obstruction. The reverse RH-to-energy direction and the critical almost-periodicity theorem are not newly formalized. |
| §8 continuous Nyman Mellin formula | Continuous generators exist, but `NymanCommonZeros` explicitly distinguishes Mellin symbols from the continuous integral formula. The full all-theta integral formula remains a gap. |
| §8 bounded off-line-zero obstruction | The actual Pareto/discrete counterpart is proved in `ParetoBeurlingMellinObstruction`, with exact lower bound $(2\Re\rho-1)/\lvert\rho\rvert^2$. Its DPP vacancy consequence is already in `IntegerDPPMellinObstruction`. |
| §8 Burnol Sonine completeness and dual minimality | External classical results; no complete Lean transfer found in this audit. |
| §9 actual arithmetic energy and Montgomery target | Still open. The new duality gives equivalent certificates, not the missing uniform arithmetic estimate. |

## 1a. Additional transfer, 14 November 2026

Eleven additional modules close the formal-coordinate, prime-torus compactness,
sharp-evaluation, and zeta-Fock Hilbert-construction gaps described above.
They also establish the concrete von Mangoldt discontinuity in Section 7.
They use ordinary Lean/Mathlib foundations and proved analytic theorems, including
the repository's proved prime number theorem, without
introducing a new arithmetic hypothesis.

The main declarations are:

- `PrimePowerFormalCoordinates.dirichletExpLogEquiv` and `dirichletExp_eta`.
- `CompactGaugeOrbit.continuous_orbit` and `primeOrbit_isCompact`.
- `PrimePowerEvaluation.exists_finite_bound_iff` and `evaluation_hasSum`.
- `CoherentFock.vector_inner` and `vector_norm_sq`.
- `LogEulerFeature.vector_inner` and `ZetaFockKernel.coherent_inner`.
- `ZetaDirichletKernel.span_features_dense`.
- `ZetaFockKernel.fullIsometry`, `integerBasis`, and `coherent_basis_hasSum`.
- `MangoldtCumulativeDivergence.coordinate_truncations_tendsto`,
  `real_energy_tendsto_atTop`, and `no_uniform_mangoldt_summation_bound`.

Lean's conjugate-first convention gives
`inner (coherent s) (coherent w) = riemannZeta (star s + w)`.
The constructed Fock space contains a distinguished zeta-generated closed
subspace. Its identification with integer l2 does **not** identify the entire
Fock space with that subspace.

Focused acceptance evidence: job `job_Hi3gFGifYcjYIQRuhzJpS48S_SR8gXBs`
succeeded with Bazel/BuildBuddy. Exact `#guard_msgs` checks on 15 construction,
basis, evaluation, and arithmetic-limit declarations confirmed precisely
`propext`, `Classical.choice`, and `Quot.sound`; no additional axioms occurred.
[Audit build](https://app.buildbuddy.io/invocation/7765f352-0a83-4dda-8b99-ab074872de2e).
The final publication checkpoint separately validates the integrated repository.

Coverage is still incomplete: actual-ordinate analytic providers,
general trace-norm covariance convergence,
the infinite signed operator and its sharp norm, the all-s summation
unboundedness extension outside 1<s<=2,
the RH-to-damped-energy/critical almost-periodicity directions, the
all-theta continuous Nyman Mellin integral, and Burnol's Sonine theorems still
require formalization. The actual RH energy estimate and microscopic
zero-pair transfer remain open mathematical obligations.


## 1b. Finite-character to infinite-orbit transfer (14 November 2026)

The new transfer consists of:

- `Probability/CompactMomentConvergence.lean`: convergence from a dense
  family of continuous moments; existence and uniqueness of the limiting
  probability measure using compactness.
- `Analysis/InfiniteTorusCharacters.lean`: continuous finite-coordinate
  Laurent characters on an arbitrary product of circles, their finite
  coordinate dependence, and uniform density by complex Stone-Weierstrass.
- `Analysis/CompactGaugeOrbitLaw.lean`: weak convergence of the full
  prime-torus laws and their norm-continuous Hilbert-orbit pushforwards;
  convergence of uncentered and centered covariance pairings; positivity
  and an explicit contraction bound for the uncentered quadratic form.

Write K = product_p Circle and
chi_m(z) = product_p z_p^(m_p), for finitely supported integer m.
For a nontrivial filter and probability measures mu_i on K, the only
substantive input is convergence of every joint character integral
integral chi_m dmu_i -> c(m). The theorem constructs a unique probability
measure nu with these moments and proves mu_i -> nu and
(primeOrbit h)_* mu_i -> (primeOrbit h)_* nu.
Lean indexes characters by finite words of prime/integer pairs; repeated
coordinates add their exponents. The locality theorem records their
finite-coordinate dependence. Individual coordinate marginals alone do
not suffice.

For moments arising as these limits, normalization, positive definiteness,
conjugation symmetry, and finite-marginal compatibility follow from the
constructed probability measure. No Haar law or independence is assumed.
For independently specified finite-dimensional probability laws, the
required compatibility is pushforward under every coordinate restriction.
For independently specified Fourier data, normalization c(0)=1 and positive
definiteness on the direct sum of the integer character groups are the
corresponding conditions; the new code uses the stronger concrete input
that these data are limits of actual probability measures.

Normalization matters. The usual zero empirical probability measure is
N(T)^(-1) sum_{0<gamma<=T} delta_{(p^(i gamma))_p}, with multiplicities.
Hlawka's unconditional fixed-frequency equidistribution, as described in
Ford--Zaharescu, plus rational independence of prime logarithms gives
c(m)=0 for m != 0 and c(0)=1. Thus the leading probability limit is Haar.
The arithmetic bias survives in the separate signed functional
T^(-1)(sum f(z_gamma) - N(T) integral f dHaar), not as a non-Haar leading
probability measure. The new exact normalized_centered_identity and its
limit theorem preserve this distinction.

Existing ActualPrimeTorusFMZ.tendsto_centered_character_div retains
UniformSelbergDensity (1/4). ActualZeroSelbergDensity explicitly records
that its published unconditional provider was deliberately deferred.
ActualZeroCountAsymptotics supplies an unconditional eventual positive
count and a T log T lower bound. The finite-prime smooth FMZ extension
also states its Fourier-decay and density assumptions explicitly.
The actual-zero empirical interface is now connected by
ActualInfinitePrimeTorus, as recorded in Section 1c. The analytic density
provider remains an explicit, intentionally deferred hypothesis.

Published analytic sources:
Ford--Zaharescu, J. reine angew. Math. 579 (2005), 145--158,
https://arxiv.org/abs/math/0405459;
Ford--Meng--Zaharescu, Bull. London Math. Soc. 49 (2017), 1--9,
https://arxiv.org/abs/1511.06814, Theorem 1 and Corollary 1.1.
The latter assumes a Diophantine condition and Fourier decay B > dimension+2;
its full-rank prime-log case satisfies the Diophantine condition by Baker.
These are published analytic inputs, not newly kernel-checked providers.

The pairing theorem uses genuine infinite Hilbert vectors. For a possibly
non-Haar law the centered version subtracts both mean factors.
The uncentered form satisfies 0 <= Q_mu(u) <= ||h||^2 ||u||^2;
division by 1+||h||^2 gives a positive-contraction quadratic bound, including
h=0. This is not a new DPP construction or identification with actual zeros.
Existing SampledCovarianceDPP supplies finite-sample positive-contraction
laws under an explicit energy budget. Existing ZeroOrdinateInfiniteDPP
constructs a separate projection thinning on actual zero-copy labels.
Neither construction proves Montgomery pair correlation.

A mathematical consequence, not newly formalized here, is trace-norm
convergence of the uncentered covariance for fixed h. For a finite
coordinate projection P_F and tau_F = ||(I-P_F)h||, the exact constant-norm
orbit gives the uniform estimate
||C_i-C||_1 <= 4 ||h|| tau_F + ||P_F(C_i-C)P_F||_1.
First fix F and use the proved pairing limits, then let F exhaust the
coordinates. The signed order-T correction has no such automatic
probability bound: extension to arbitrary infinite observables requires
an appropriate uniform remainder/tail bound. Weak convergence against all
continuous tests for the centered signed measures is not justified by
finite-character limits.

Scoped Bazel/BuildBuddy verification succeeded for
`//RiemannResearch/Analysis:CompactGaugeOrbitLaw`, including all three new
modules, in job `job_ARo-hgCEv2bs6lMgwTEC444ly_QkX5Xm`.
[Transfer build](https://app.buildbuddy.io/invocation/a0eca4c5-e185-4101-8023-692dde4f76d6).
Exact `#guard_msgs` axiom checks on eight principal declarations succeeded in
job `job_xaC9TSr1OWK5Fb3iuh8RrWMooHv-sn84`, confirming only
`propext`, `Classical.choice`, and `Quot.sound`.
[Audit build](https://app.buildbuddy.io/invocation/9a1aaeb4-9268-4a77-9411-f11e90af6798).
Publication of the transfer and actual-zero specialization is gated by the
full repository checkpoint. Its terminal record identifies the validated
integrated source and published commit.


## 1c. Actual empirical infinite-prime-torus law (13 November 2026)

**Conditional research reduction.** `Analysis/ActualInfinitePrimeTorus.lean`
now assembles the actual-zero specialization. The sole domain-specific premise
of `existsUnique_actual_orbit_limit` is
`ActualZeroOrdinate.UniformSelbergDensity (1 / 4)`.

- `phasePoint t` simultaneously records every prime phase
  `Circle.exp (log p * t)`.
- `rawEmpiricalMeasure T` is the sum of Dirac atoms over
  `ActualZeroOrdinate.Copies T`, each with weight `1/N(T)`.
  `rawEmpiricalMeasure_isProbability` requires only `0 < N(T)`.
  `empiricalProbability T` uses the Dirac probability at the identity when
  the cutoff is empty. The unconditional eventual positivity theorem removes
  this convention from every limit.
- `integral_empiricalProbability` identifies every complex test integral
  with the actual multiplicity-weighted normalized sum, without a continuity
  assumption. `integral_character_eq_sampleFunctional` identifies every
  word-character integral with the existing finite-prime FMZ functional.
  `wordMode` adds exponents at repeated primes, so cancellation and the
  empty word are included.
- `haarMoment_eq` computes the limiting moment as one precisely when all
  combined exponents vanish, and zero otherwise.
  `integral_character_centered_identity` retains the exact signed correction:
  `integral chi_s dmu_T = c_s + (T/N(T)) * ((S_s(T)-N(T)*c_s)/T)`.
- `ActualZeroOrdinate.tendsto_height_div_count` and its complex version,
  added to `ActualZeroCountAsymptotics.lean`, prove `T/N(T) -> 0`
  from the existing unconditional count lower bound.
- `tendsto_integral_character` combines that ratio with the existing
  conditional centered FMZ limit. `existsUnique_actual_orbit_limit`
  applies the new compact transfer theorem to obtain one uniquely determined
  probability law with all finite joint Haar moments, convergence of the
  full actual empirical laws, and weak convergence of every fixed Hilbert
  orbit pushforward.

**Open formal provider:** `UniformSelbergDensity (1 / 4)`. Its classical
provider is intentionally deferred, as requested. No RH or zero-simplicity
hypothesis is introduced. This theorem does not assert an infinite signed
operator limit, a trace-norm limit, or a DPP law for the actual zeros.

The scoped source check passed with Bazel/BuildBuddy in
`job_I08YOY_MSNkWY_B4PQmFL0F2UxXhwFyq`
([source build](https://app.buildbuddy.io/invocation/410fc3d0-5111-42d6-820d-13aa140abed3)).
After the final direct-import update, the module and eight exact axiom guards
passed in `job_g6jyPCin_8xk7cBS9PvmTRA-faVPO0A5`
([axiom audit](https://app.buildbuddy.io/invocation/8636e0a9-67d0-4a0e-b10f-bcddda7f07b9)).
The guards confirm only `propext`, `Classical.choice`, and `Quot.sound`.
These are scoped checks; full integrated acceptance is the publication
checkpoint's responsibility.

## 2. New quantitative obstruction at the microscopic scale

For a finite frequency family $q_j\in\mathbb R$, nonnegative weights $b_j$
with $\sum_j b_j=1$, put
$$
H(t)=\sum_j b_j e^{i q_jt},\qquad
V_b(q)=\frac12\sum_{j,k}b_jb_k(q_j-q_k)^2
      =\sum_jb_j\left(q_j-\sum_k b_kq_k\right)^2.
$$
The new module `Analysis/PrimeProbeMicroscopic.lean` proves the **exact** identity
$$
1-|H(t)|^2=\sum_{j,k}b_jb_k\{1-\cos((q_j-q_k)t)\}
$$
and then
$$
0\le1-|H(t)|^2\le t^2V_b(q).
$$
The theorem `microscopic_repulsion_tendsto_zero` allows the finite index type,
weights, and frequencies to vary. If $V_{b_T}(q_T)/a_T^2\to0$, then
$$
1-|H_T(u/a_T)|^2\longrightarrow0
\quad\text{for each fixed }u.
$$

Take $a_T=\log T/(2\pi)$ to match unfolded zero spacings. Any route through
these positive feature probes needs frequency spread on that scale to retain
nonzero two-point repulsion. Merely increasing the number of sample vectors
does not supply that spread. The inequality is necessary information, not a
sufficient condition for a sine limit.

`Analysis/PrimeProbeBudgetObstruction.lean` connects this directly to the
existing FMZ moving-test criterion. For rational frequencies
$q_j=\log(n_j/m_j)$, $n_j,m_j\ge1$, write
$$
W(n,m)=1+|\log n+\log m|,\qquad
\mathcal M(b,n,m)=\sum_{j,k}b_jb_k
 W(n_jm_k,m_jn_k)^2.
$$
This is the complete squared-height absolute budget for the displayed rational
representation of the Fourier expansion of $|H|^2$. Lean proves
$$
2V_b(q)\le\mathcal M(b,n,m).
$$
It also proves, for varying finite families,
$$
\frac{\mathcal M(b_T,n_T,m_T)}{\log T}\longrightarrow0
\quad\Longrightarrow\quad
1-|H_T(u/\log T)|^2\longrightarrow0.
$$
The analogous single-mode budget theorem is included. The factor $2\pi$ in
the usual zero-spacing scale is absorbed into the fixed parameter $u$.

Thus the present sufficient absolute FMZ budget and a nondegenerate
microscopic positive probe cannot be combined by merely enlarging support.
The bound itself needs strengthening, for example through signed cancellation
or a wider-band estimate. This obstruction requires neither RH nor Selberg
density. It is not an impossibility theorem for other FMZ methods or for
Montgomery's conjecture.

For these normalized feature probes, $1-|H(t)|^2$ is a two-site Gram determinant. For a **discrete
DPP**, the entire kernel also needs to be a positive contraction. A
unit-diagonal correlation matrix is not automatically such a contraction.
This distinction prevents interpreting the displayed minor as a probability
without the required normalization/construction.

The companion `Analysis/FinitePolynomialResonance.lean` closes the fixed-height
upper obstruction from the PDF. At any selected unit phase $z_0$, the polynomial
$$
P_d(z)=\sum_{k=1}^{d}\overline{z_0}^{\,k}z^k
$$
has coefficient energy $d$, vanishes at zero, and has $P_d(z_0)=d$.
Its complete sampled energy is therefore at least $d^2$. After normalizing
the coefficients, the centered sampled value is at least $(d-N(T))/T$.
Thus no support-independent upper bound exists even at one fixed positive
height with a nonempty sample. Multiplicities and all other nonnegative sample
terms are retained. This is an explicit obstruction, not just an absence of
an available estimate.

## 3. What the coordinate/sample dual says

For a finite feature matrix $A$, set $C=AA^*$ and $G=A^*A$.
`Analysis/PrimeProbeDualGram.lean` proves
$$
\det(I+zC)=\det(I+zG),\qquad
\operatorname{tr}C=\operatorname{tr}G,\qquad
\operatorname{tr}C^2=\operatorname{tr}G^2.
$$
With $A_{qj}=a_qe^{i\gamma_jq}$, real $a_q$,
$$
G_{ij}=\sum_q a_q^2e^{iq(\gamma_j-\gamma_i)},\qquad
\operatorname{tr}C^2
 =\sum_{i,j}\left|\sum_q a_q^2e^{iq(\gamma_j-\gamma_i)}\right|^2.
$$
There is no omitted diagonal. Repeated ordinates, including multiplicities,
remain in the index set. Normalizing $A$ rescales both sides identically.

This is the useful finite dual: a coordinate covariance calculation becomes a
weighted pair statistic on the sample side. For an actual positive-contraction
DPP, count variance is trace minus square trace. Neither equality evaluates
the statistic for actual zeta zeros as their height grows.

## 4. DPP constructions and their different infinite limits

A signed arithmetic correction is not itself a DPP kernel. We construct both
an affine transform of that correction and normalized covariance kernels,
proving positivity of each kernel and its complement.

### A correlated arithmetic law on all prime powers

The new `Probability/PrimeBlockDPP.lean` works on the countable set of sites
$(p,k)$, where $p$ is prime and $k\ge1$. Let
$$
B_{(p,k),(q,\ell)}=
\begin{cases}
-\dfrac{\log p}{2\pi}\,p^{-|k-\ell|/2},&p=q,\ k\ne\ell,\\
0,&\text{otherwise},
\end{cases}
\qquad C=\frac{\log 2}{\pi(\sqrt2-1)}.
$$
The arbitrary-finite-site Schur estimate gives $-CI\le B\le CI$ as quadratic
forms. Consequently
$$
K=\frac12(I+B/C),\qquad I-K=\frac12(I-B/C)
$$
are both positive. The module constructs the actual infinite probability
measure from these proved inequalities; it does not merely posit a DPP.
No zero-height asymptotic or abstract infinite operator extension is needed.

The checked finite laws include
$$
\Pr((p,k)\in X)=\frac12,
$$
and, for distinct sites $x,y$,
$$
\Pr(x,y\in X)=\frac14-\left(\frac{B_{xy}}{2C}\right)^2.
$$
For $k\ne\ell$ in one prime block this is
$$
\frac14-\frac{(\log p)^2}{16\pi^2C^2}\,p^{-|k-\ell|}.
$$
For distinct primes the two-site probability is $1/4$. More strongly, every
occupied/vacant pattern on any finite selection of one site per distinct
prime has probability $2^{-m}$. This last theorem is full finite independence
for those selections, not just pairwise independence.

The hole process has the kernel $(I-B/C)/2$. Particles and holes have equal
one- and two-site probabilities; equality of their complete laws is not
asserted. This DPP lives on prime powers, not on zero ordinates.

The companion `Probability/PrimeBlockDPPInfinite.lean` gives, for every finite
window $F$ and its count $N_F$,
$$
\mathbb E N_F=\frac{|F|}{2},\qquad
\operatorname{Var}N_F=\frac{|F|}{4}
 -\frac{1}{4C^2}\sum_{x,y\in F}B_{xy}^{,2}.
$$
It also proves that **both the particle set and the hole set are infinite
almost surely**. The proof selects one site along a strictly increasing
sequence of primes, constructed using Euclid's theorem. Every constant finite
tail pattern has probability $2^{-m}$, so any constant infinite tail has
probability zero. Countable null unions exclude finitely many particles or
finitely many holes. Infinite expectation alone is not used to infer this.

### Normalized covariance and diagonal laws

The new `Probability/DeterminantalDiagonal.lean` constructs an actual law on
the infinite discrete configuration space for $0\le p_q\le1$. Every finite
occupied/vacant pattern satisfies
$$
\Pr(X\cap F=S)=\prod_{q\in S}p_q\prod_{q\in F\setminus S}(1-p_q).
$$
This proves full independence, not just zero pair covariance. The module also
proves particle-hole duality, finite-window variance, exact expected total
count for summable weights, almost-sure finite particle count, and convergence
of finite configuration probabilities when positive-contraction kernels
converge entrywise to the diagonal.

The companion sampled-covariance constructor uses real Hilbert vectors $v_j$,
nonnegative weights $w_j$, and an orthonormal coordinate family $e_q$:
$$
K(q,r)=\sum_j w_j\langle v_j,e_q\rangle\langle v_j,e_r\rangle,
\qquad\sum_jw_j\|v_j\|^2\le1.
$$
Positivity of $K$ and $I-K$ is derived, not assumed as an unexplained
analytic input. The complementary identity retains the unused energy budget.

| Construction | Infinite limit | Particle-hole dual |
|---|---|---|
| Projection onto increasing sampled spans with dense union | Identity kernel; all discrete sites occupied almost surely | Zero kernel; no holes |
| Covariance divided by $\lVert h\rVert^2$, with the PDF's diagonal covariance limit | Diagonal weights $p_q=\lvert\widetilde h_q\rvert^2/\lVert h\rVert^2$; independent Bernoulli occupations | Independent holes with probabilities $1-p_q$ |
| The arithmetic kernel $(I+B/C)/2$ | An actual law on all prime powers; infinitely many particles and holes almost surely | $(I-B/C)/2$; the arithmetic correction changes sign |
| A genuinely rescaled frequency-space projection | May have a nontrivial continuous limit only after proving the appropriate local kernel/trace limits | The corresponding complementary or reduced-Palm projection, with its own boundary conditions |

For nonzero $h$ and its normalized covariance weights, $\sum_qp_q=1$. Thus the limiting law
has expected total particle count one and finitely many particles almost
surely. Its particle count is generally **not identically one**.
Its finite-window variance is $\sum_{q\in F}p_q(1-p_q)$.
It is not a sine process.

The PDF's random phases $Z_p^k$ are another random object: same-prime powers
share a phase. Turning a covariance into a DPP does not transfer higher phase
moments to the new occupations.

The exact complex covariance and its real part also require care. Writing a
complex vector as $a+ib$ gives
$\Re(vv^*)=aa^T+bb^T$. Treating it as one real vector and keeping only its
cosine coordinates is a different kernel. The finite complex Gram identities
above do not assert a general complex-law existence theorem in the present
real-kernel discrete DPP infrastructure.

## 5. Arithmetic duality, with the remainder retained

For nonnegative weights, the new `FiniteWeightedQuadraticDual` proves
$$
D_S(e,y)=\sum_{i\in S}w_i(2e_iy_i-y_i^2),\qquad
E_S(e)-D_S(e,y)=\sum_{i\in S}w_i(e_i-y_i)^2.
$$
Consequently $E_S(e)=\max_yD_S(e,y)$, attained at $y=e$, uniquely on
positive-weight sites. On a countable index set,
$$
\sum_iw_ie_i^2<\infty
\iff \exists C\ \forall N,y,\ D_{\{0,\ldots,N-1\}}(e,y)\le C.
$$
This quantifier over **all tests and all cutoffs** cannot be replaced by
convergence for each fixed Fourier test.

`RH/ChebyshevEnergyDual.lean` specializes the identity to the actual
Chebyshev error, including the deterministic geometric remainder.
For damped weights $n^{-a}/(n(n+1))$, uniform finite dual bounds for every
$a>0$ imply the actual Mathlib RH via the existing Mellin-energy theorem.
That uniform bound is the explicit open arithmetic hypothesis.

Conversely, if an actual zero has $\beta>1/2$, the module proves arbitrarily
large finite dual witnesses at the endpoint $a=2\beta-1$.
This is a conditional obstruction from a hypothetical off-line zero, not an
assertion that one exists.

The new tridiagonal inverse is an operator-form identity for
$L^T\operatorname{diag}(w)L$. Before imposing a terminal condition it reads
$G(\operatorname{precision}(b))_i=b_i-b_N$. Only after stating $b_N=0$
does this become an inverse. The boundary is part of the theorem.

The sampled-orbit annihilator and the Nyman obstruction are different duals.
A full-support orbit can have zero annihilator in its coordinate Hilbert space
while a forbidden zeta zero still gives a nonzero bounded Mellin obstruction
in the legal approximation space. No identification between those spaces is
silently made.

## 6. How to use FMZ and harmonic analysis next

The existing `ActualZeroOrdinate.tendsto_moving_rational_fourier_remainder` in
`ActualRationalFMZRate.lean`
controls moving tests when their squared-log-height weighted Wiener mass is
$o(\log T)$, with `UniformSelbergDensity (1/4)` explicit. The published FZ/FMZ
estimates justify investigating this route; they do not remove the checked
declaration's provider obligation.

1. **Close the classical provider gap.** Formalize the Selberg-density input
   used by the actual-ordinate comparison; keep it distinct from a new
   pair-correlation estimate.
2. **Design moving probes and sharpen their remainder estimates together.**
   Positive probes whose frequency variance is $o((\log T)^2)$ cannot work
   at the desired scale. The new `rational_pair_budget_microscopic_repulsion_tendsto_zero`
   proves that remaining within the present sufficient $o(\log T)$ absolute
   FMZ budget forces precisely this degeneracy. More support within that
   budget is insufficient; preserve cancellation or prove a wider-band rate.
3. **Estimate the complete signed pair statistic.** Use the exact dual Gram
   and existing `MontgomeryFormFactor.shifted_probe` in `MontgomeryPrimeProbe.lean`; retain both diagonal
   and cross-prime terms. A fixed-support FMZ limit does not control a moving
   family beyond Fourier support one.
4. **Separate an auxiliary sine model from actual zeros.** The repository
   already has an unconditional fixed-center finite-determinant sine limit
   for the auxiliary residue-partition kernel in `ParetoResidueSineLimit`.
   Its high-height error budget needs $T=o(\log L)$; matching the zero scale
   would need $\log L\asymp\log T$, outside that bound.
5. **Target the missing transfer estimate.** Near a prescribed actual zero,
   the correct comparison is reduced-Palm, not the unconditioned sine
   projection. A vanishing local trace difference and suitable high-height
   control remain open. The arithmetic dual provides finite lower witnesses
   and an exact residual, but no upper bound closing that gap.

For a full point-process/GUE conclusion, convergence of all required
correlations and tightness/moment control is stronger than Montgomery's
two-point conjecture alone. Arias de Reyna--Rodgers supplies a precise
framework for randomly translated deterministic zero sequences; it does not
make an arbitrary auxiliary DPP equal to the zero process.

## 7. Provenance and verification

New modules and their principal declarations:

| Module | Main checked declarations |
|---|---|
| `Analysis/SampledGaugeSupport` | `sampled_orbit_closure_eq_support`, `mem_sampled_orbit_orthogonal_iff`, `no_scalar_weighted_frame_on_infinite_support` |
| `Analysis/PrimeBlockCovariance` | `prime_constant_le_two`, `prime_block_uniform_bound`, `finite_prime_blocks_bound` |
| `Analysis/FinitePolynomialResonance` | `resonancePolynomial_sample_energy_ge`, `no_uniform_one_prime_centered_upper_bound` |
| `Analysis/ZetaDirichletKernel` | `feature_memℓp_iff`, `vector_inner`, `finite_gram_energy`, `dirichlet_series_bound` |
| `Analysis/PrimeProbeMicroscopic` | `probeRepulsion_exact`, `probeRepulsion_le_variance`, `microscopic_repulsion_tendsto_zero` |
| `Analysis/PrimeProbeBudgetObstruction` | `spectralVariance_eq_secondMoment_sub`, `two_mul_spectralVariance_le_rationalPairBudget`, `rational_pair_budget_microscopic_repulsion_tendsto_zero` |
| `Analysis/PrimeProbeDualGram` | `gram_determinant_duality`, `gram_square_trace_duality`, `primeFeature_square_trace` |
| `Probability/DeterminantalDiagonal` | `diagonalLaw_configuration`, `diagonalLaw_finite_ae`, `contractionDPP_configuration_tendsto_diagonal` |
| `Probability/SampledCovarianceDPP` | `covariance_complement_posSemidef`, `law_isDPP`, `law_configuration_tendsto_diagonal` |
| `Probability/PrimeBlockDPP` | `signedEntry_quadratic_bound`, `shiftedKernel_posSemidef`, `law_isDPP`, `two_point`, `distinct_prime_configuration`, `law_holes_isDPP` |
| `Probability/PrimeBlockDPPInfinite` | `expected_window_count`, `variance_window_count`, `infinitely_many_along_distinct_primes`, `infinite_particles_and_holes_ae` |
| `Analysis/FiniteWeightedQuadraticDual` | `gap`, `isGreatest`, `summable_iff_uniform_dual_bound` |
| `RH/ChebyshevEnergyDual` | `continuousEnergy_dual_gap`, `riemannHypothesis_of_all_damped_dual_bounds`, `dual_unbounded_at_offline_zero_endpoint` |
| `LinearAlgebra/FiniteCumulativeGramInverse` | `precisionAction_gramAction`, `gramAction_precisionAction_boundary`, `precisionAction_tridiagonal` |

Existing `RH/RealZetaNonvanishing` and `RH/ZetaKernelObstruction` are strengthened
by `riemannZeta_ofReal_re_neg` and
`no_zeta_gram_on_domain_meeting_left_halfstrip`, respectively.

The new modules are submitted together to the repository's final full-project
Bazel/BuildBuddy checkpoint before publication. Individual module/snippet
checks are development evidence, not substitutes for that integrated result.
The final checkpoint ID, result and published SHA are reported with delivery.

Primary references used for interpretation and proof strategy:

- FZ, *On the distribution of imaginary parts of zeros of the Riemann zeta
  function*, equations (1.1), (3.8):
  https://ford126.web.illinois.edu/wwwpapers/fz.pdf
- FMZ, *Simultaneous distribution of the fractional parts of Riemann zeta
  zeros*, Theorem 1, Corollary 1.1:
  https://arxiv.org/abs/1511.06814
- FSZ, *On the distribution ... II*, including its conditional connections:
  https://arxiv.org/abs/0805.2745
- Hedenmalm--Lindqvist--Seip, *A Hilbert space of Dirichlet series and systems
  of dilated functions in L2(0,1)*:
  https://arxiv.org/abs/math/9512211
- Montgomery, *The pair correlation of zeros of the zeta function* (1973):
  https://websites.umich.edu/~hlm/paircor1.pdf
- Lyons, *Determinantal probability measures*:
  https://arxiv.org/abs/math/0204325
- Hough--Krishnapur--Peres--Virag, *Determinantal Processes and Independence*:
  https://arxiv.org/abs/math/0503110
- Soshnikov, *Determinantal random point fields*:
  https://arxiv.org/abs/math/0002099
- Arias de Reyna--Rodgers, *On convergence of points to limiting processes,
  with an application to zeta zeros*:
  https://arxiv.org/abs/2311.13441

No priority or novelty claim is made for these mathematical consequences.

## 8. Signed moving-test investigation (11 November 2026)

See [FMZ_Signed_Microscopic_Investigation_20261111.md](FMZ_Signed_Microscopic_Investigation_20261111.md)
for the positivity audit, explicit probe families, all Fourier corrections,
published FMZ/FSZ range comparison, and a reproducible numerical experiment.

New unconditional declarations:
- `Analysis/RationalLandauMovingBand.eventually_rational_landau_error_power_band`
  proves normalized complex-zero Landau error O(1/log T) on each fixed
  numerator band n <= T^theta, 0 <= theta < 2/5, using the existing provider.
- `Analysis/FejerSignedRemainder` retains the exact triangular signed sum,
  bounds it by signed prefixes or their mean-square energy, and supplies
  bounded-difference and alternating examples. Its exact square example
  shows why linear cancellation does not control pair-square errors.
- `Analysis/PrimeProbeExplicitFamilies` gives two-mode and three-mode
  variance/repulsion identities, the exact two-mode rational budget, and
  the failure of nonnegative variance/repulsion for signed spectral weights.
- `Analysis/ActualFejerMovingFMZ.fejer_remainder_exact` and
  `eventually_fejer_ordinate_remainder_le` retain the actual signed horizontal
  prefixes and the complete unconditional Landau remainder.

**Conditional research reduction:** `tendsto_fejer_ordinate_of_horizontal_prefix`
has no RH or Selberg premise but requires averaged signed-horizontal-prefix
smallness. Provider status: **Open**. Neither finite Gram duality nor a
manufactured DPP supplies it. The actual pair-square and high-support
signed additive prime-correlation estimates also remain **Open**.

The stronger external prime-power band theta < 2 follows on paper from
FMZ Lemma 1; it is not claimed as a newly formalized provider. Source
publication is subject to the full-project Bazel/BuildBuddy checkpoint.
