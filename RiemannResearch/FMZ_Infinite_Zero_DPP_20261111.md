# Infinite zero-ordinate FMZ DPP and quantitative pair transfer

Date: 11 November 2026.
Starting revision: 8d91c2e44fa978205f4d8b4a59a636398f4bca9d.

## November 18 continuation

The [updated Lean catalog](THEOREM_CATALOG_INFINITE_ZERO_DPP_20261111.md) identifies the limiting kernel on actual ordinate fibres, the exact multiplicity-weighted pair and translated-window statistics, weak convergence of the discrete laws, and the RH criteria from horizontal marks. It also records the finite-rank trace theorem and improved integrated vacancy bounds. The sections below describe the November 11 checkpoint.

## Outcome

The infinite zero-label construction, finite-feature inclusion limits,
collision exclusion, exact pair-statistic transfer, and third-moment
vacancy-transfer theorem are formalized in Lean. Montgomery pair correlation
and RH are not proved.

The user clarified that “ZFC” referred to the FMZ/infinite-DPP construction.
No extension of set-theoretic axioms is introduced.

The strongest analytic reduction obtained here replaces uniform control of
every sampling error by an averaged diagonal-vacancy condition, provided a
local third-moment bound and a model pair limit are available. The relevant
zeta-zero moment estimate is published; it has not been formalized in this
change. The actual vacancy estimate and model pair limit remain Open.

## 1. An infinite law on the actual zeta zeros

Let
\[
 \mathcal Z_+=\{(\rho,a):\zeta(\rho)=0,\quad\Im\rho>0,\quad
             0\le a<\operatorname{mult}(\rho)\}.
\]
This is the repository's countable PositiveCopies type. Different copies and
different zeros sharing an ordinate are retained. For every real H, only
finitely many labels satisfy \(\gamma_i\le H\).

Work in the single Hilbert space \(\ell^2(\mathcal Z_+;\mathbb R)\), with its
coordinate vectors \(e_i\). For any frequency sequence \(q_k\), define
\[
 v_{n,k,0}(i)=\mathbf1_{\gamma_i\le n}\cos(q_k\gamma_i),\qquad
 v_{n,k,1}(i)=\mathbf1_{\gamma_i\le n}\sin(q_k\gamma_i).
\]
These are finitely supported vectors. This is essential: the unrestricted
unit-modulus Fourier sequence on all zeros is not automatically in counting
\(\ell^2\). For FMZ one can use \(q_k=\log(k+1)\), which includes prime powers;
Gram differences then include rational logarithms.

Enumerate all triples \((n,k,b)\), let \(V_m\) be the span of the first m
features, and put
\[
 V=\overline{\operatorname{span}}\{v_{n,k,b}\},\qquad
 K_m(i,j)=\langle P_{V_m}e_i,P_{V_m}e_j\rangle,\quad
 K(i,j)=\langle P_Ve_i,P_Ve_j\rangle.
\]
Every finite principal compression of K and I-K is positive semidefinite.
The repository's determinant-weight construction therefore produces an actual
probability measure on \(\{0,1\}^{\mathcal Z_+}\), with
\[
 \mathbb P(I\subset X)=\det K_I.
\]
No DPP existence, finite-law consistency, RH, Selberg density, or
distinct-ordinate hypothesis is assumed.

The new kernel_tendsto and inclusion_tendsto prove, respectively,
entrywise convergence \(K_m\to K\) and convergence of every finite inclusion
probability. Finite configuration convergence follows by finite
inclusion-exclusion; the latter packaging as weak convergence is a paper
consequence, not an additional new Lean declaration.

These finite-feature laws live on one fixed ground set. They are not asserted
to be restrictions of the earlier law recomputed separately at each height.

## 2. Local finiteness and collision exclusion

Every subset of \(\mathcal Z_+\) is locally finite in ordinate, counting labels.
This is proved by embedding each bounded-height set into the finite cutoff.

More is true for this Fourier-projection law. If \(\gamma_i=\gamma_j\), every
feature has equal i and j coordinates. This property survives closed linear
span, hence \(e_i-e_j\perp V\) and
\[
 P_Ve_i=P_Ve_j.
\]
For distinct such labels, the corresponding two-point determinant is zero:
\[
 \mathbb P(i,j\in X)=K_{ii}K_{jj}-K_{ij}^2=0.
\]
Countability upgrades these individual null events to the Lean theorem
ordinate_injective_ae: almost surely the selected labels have distinct
ordinates. Their image is therefore a simple locally finite point
configuration. A full random-measure/topological packaging is not introduced
in this change.

This does not show that the original zeros are simple or critical.
The construction can delete coincident labels. Indeed, the new
collision_vacancy_lower proves the necessary cost
\[
 \gamma_i=\gamma_j,\ i\ne j
 \quad\Longrightarrow\quad
 (1-K_{ii})+(1-K_{jj})\ge1.
\]
Thus collisions cannot disappear for free in a comparison with the complete
zero multiset.

## 3. Complete pair-transfer identity

For a finite labelled window I, let \(w_{ij}\) be arbitrary real signed
weights with \(w_{ii}=0\). The zero pair statistic and DPP statistic are
\[
 F_I=\sum_{i,j\in I}w_{ij},\qquad
 F_X=\sum_{i,j\in I}w_{ij}\mathbf1_{i\in X}\mathbf1_{j\in X}.
\]
Write \(d_i=1-K_{ii}\). The exact equality is
\[
 \boxed{
 F_I-\mathbb EF_X
 =\sum_{i,j\in I}w_{ij}
       \bigl(d_i+d_j-d_id_j+K_{ij}K_{ji}\bigr).
 }
\]
Every signed term is retained. The pair defect is the probability of losing
at least one endpoint, so for \(i\ne j\)
\[
 0\le d_i+d_j-d_id_j+K_{ij}K_{ji}\le d_i+d_j.
\]
The resulting checked weighted bound is
\[
 \boxed{
 |F_I-\mathbb EF_X|
 \le\sum_{i\in I}d_i\sum_{j\in I}
       \bigl(|w_{ij}|+|w_{ji}|\bigr).
 }
\]
No symmetry of the weights is needed. The general real-kernel theorem uses
only an actual DPP law; for the constructed projection kernel,
\(K_{ij}K_{ji}=K_{ij}^2\).

In the zero-label application, Lean identifies the vacancy exactly as
\[
 d_i=\|e_i-P_Ve_i\|^2
\]
and substitutes these projection residuals into the displayed bound.
If \(|w_{ij}|\le M\), \(Z=|I|\), and \(D=\sum_{i\in I}d_i\), it also proves
\[
 0\le D\le Z,\qquad
 |F_I-\mathbb EF_X|\le2MZD.
\]
The weighted inequality is usually sharper than this last simplification.

## 4. Averaged vacancy suffices with a third moment

Let t be a random window center, z(t) its original zero count, and d(t)
the conditional expected number deleted by the DPP. Thus \(0\le d\le z\).
Let f(t) be the signed difference between the original pair statistic and
the conditional expected DPP statistic, so
\[
 |f(t)|\le2M z(t)d(t).
\]

The key checked inequality, for every a>0, is
\[
 2zd\le az^3+\frac d a.
\]
Its complete nonnegative remainder is
\[
 a^2z^3+d-2azd
 =d(az-1)^2+a^2z^2(z-d)\ge0.
\]
Integration gives the new theorem integral_pair_error_le:
\[
 \boxed{
 \left|\int f\,d\nu\right|
 \le M\left(a\int z^3\,d\nu+\frac{\int d\,d\nu}{a}\right).
 }
\]
The Lean statement records integrability of f, \(z^3\), and d explicitly.
It applies to varying measures and does not require a fixed probability
space across heights.

The new integral_tendsto_zero_of_vacancy proves that
\[
 \sup_T\int z_T^3\,d\nu_T<\infty,\qquad
 \int d_T\,d\nu_T\longrightarrow0
 \quad\Longrightarrow\quad
 \int f_T\,d\nu_T\longrightarrow0.
\]
There is no hypothesis of uniform sitewise convergence or convergence of
every higher correlation.

As a paper corollary, if \(\int z^3\le C\), \(\delta=\int d\), optimizing a
gives
\[
 \left|\int f\right|\le2M\sqrt{C\delta}.
\]
Wolfram checked the nonnegative-remainder factorization and the optimizer.
Lean proves the full parameterized inequality and the limit theorem; the
optimized square-root display is not a separate checked declaration.

Hölder gives a further paper improvement: for any p>2 with
\(\int z^p\le C_p\),
\[
 \left|\int f\right|
 \le2M C_p^{1/(p-1)}\delta^{(p-2)/(p-1)}.
\]
Indeed \(zd\le z^{p/(p-1)}d^{(p-2)/(p-1)}\), and the two exponents are
conjugate after integration. This higher-moment corollary is not formalized
here. Constants depend on p and the window; taking p large is not a uniform
exponential estimate.

## 5. Published input and the precise PCC reduction

Arias de Reyna--Rodgers, Theorem 34 and Corollary 35, use Fujii's corrected
moment theorem to obtain uniform moments of counts in random intervals of
length \(A/\log T\). This supplies the external third-moment input, without
RH, for fixed bounded unfolded windows. Their Theorem 2 also distinguishes
and relates GUE correlation, process, and spacing formulations. Their
theorem does not prove GUE. This number-theoretic input remains an external
provider in this Lean development.

For \(t\) uniform on [T,2T], use the actual unfolding
\[
 x_i(t)=\frac{\log T}{2\pi}(\gamma_i-t).
\]
For each bounded window B, the new sufficient transfer target is
\[
 \delta_T(B)=\frac1T\int_T^{2T}
     \sum_{x_i(t)\in B}(1-K_{T,t}(i,i))\,dt\longrightarrow0.
\]
For a measurable DPP-kernel family, the exact finite estimates above and the
published count moment bound show that this transfers compactly supported
two-point statistics from that same thinned family to the original zeros.

To conclude Montgomery pair correlation one must ALSO prove, for this same
family, that its averaged pair law converges to
\[
 1-\left(\frac{\sin\pi(x-y)}{\pi(x-y)}\right)^2.
\]
Both the actual vacancy estimate and this model limit are Open. Their
measurability/integrability assembly with the published moment provider has
not been specialized into a new Lean theorem stating full PCC.
For a Schwartz-test formulation, include the appropriate tail control.

A mixture over random translations of DPPs is not automatically a DPP.
The transfer argument uses conditional pair expectations and remains valid
without making that additional assertion.

Soshnikov's Theorem 5 gives a published route to convergence for genuine
continuous DPP kernels via weak-operator and local-trace convergence. It
cannot be applied to the raw zeros or to a translation mixture without
checking its hypotheses.

The older auxiliary residue/Mellin sine limit is not identified with this
zero-label thinning. Substituting it for the required same-family limit
would leave the comparison gap untouched.

## 6. What the infinite extension does not remove

Fixed-window convergence cannot be exchanged with a moving-height limit
without a uniform estimate. Even coordinate projections onto the first m
basis vectors converge strongly to the identity, while the vacancy at the
moving site m+1 stays one.

The rank obstruction also persists for finite approximants. A rank-r
projection has, in any N-site window,
\[
 \sum_i(1-K_{ii})=N-\operatorname{tr}K_I\ge N-r.
\]
Thus a tiny global feature dictionary cannot retain most labels in a large
window. The previous three-prime Parseval/frame-potential identity records
the corresponding exact pair-energy obstruction. The displayed trace
consequence is a paper deduction, not a new declaration here.

The repository's improved arithmetic estimates remain useful:
equal prime-degree blocks have zero arithmetic covariance; the full integer
arithmetic covariance has logarithmic operator growth; the proved rational
Landau moving band extends to exponents below 2/5. These estimates do not
by themselves bound the actual zero-projection residual at microscopic
moving heights. Complex-zero Landau weights must also be distinguished
from raw ordinate weights.

Ford--Soundararajan--Zaharescu connects strong pair correlation to stronger
ordinate cancellation. That implication cannot be reversed merely from
fixed-frequency FMZ asymptotics.

A search also found the preprint arXiv:2511.18275v2 claiming PCC under RH.
It is not imported as a theorem. Its Section 9 requires justification of
the Gaussian/stationary model for the derivative process and its use to
transfer ensemble behavior to the specific zeta sequence. Covariance decay
alone does not establish those hypotheses, or identify the limiting mean.
This is a screening observation, not a complete audit of the preprint.

### Three primes and the twin-prime connection

For three normalized prime-phase vectors, write their Hermitian Gram matrix
as
\[
 G=\begin{pmatrix}1&a&b\\\bar a&1&c\\\bar b&\bar c&1\end{pmatrix}.
\]
The existing checked ThreePointGram declarations give
\[
 \det G=1-|a|^2-|b|^2-|c|^2+2\Re(ac\bar b),\qquad
 |c-\bar a b|^2\le(1-|a|^2)(1-|b|^2).
\]
Thus three primes retain a cycle phase that pairwise absolute-value bounds
discard. The infinite construction preserves these finite Gram constraints;
it does not turn fixed prime-frequency estimates into microscopic
moving-height estimates. The existing DeterminantalThreePoint module gives
the corresponding complete third inclusion determinant and connected cycle.

The relationship to twin primes runs through the explicit formula and
shifted prime-pair sums. Under RH, the appropriate strong pair-correlation
statement is equivalent to short-interval prime variance asymptotics.
Sufficiently uniform Hardy--Littlewood prime-pair estimates can supply such
asymptotics. Infinitely many pairs with the single gap 2 is a different
statement: no implication from this construction to that claim is proved.
See Chan, *More precise pair correlation of zeros and primes in short
intervals*, https://arxiv.org/abs/math/0206292, and Conrey--Keating,
*Pair correlation and twin primes revisited* (2016),
https://pmc.ncbi.nlm.nih.gov/articles/PMC5095450/.

## 7. Lean map and remaining providers

| Module | Main established results |
|---|---|
| Probability/DeterminantalPairTransfer.lean | Exact signed pair defect; nonnegative defect and vacancy upper bound; weighted pair-error bound; actual expected pair statistic; total-vacancy and count bounds |
| Probability/ZeroOrdinateInfiniteDPP.lean | Countable actual-zero law; bounded-window finiteness; exhaustive projection and inclusion limits; exact residual vacancies; collision exclusion almost surely; actual-zero pair-transfer bound |
| Analysis/PairVacancyMoment.lean | Scalar Young remainder inequality; integral error bound; general vanishing-vacancy/third-moment transfer |

Open analytic providers:
1. Formalize the published Fujii local count moments.
2. Establish the averaged actual vacancy bound for a specified moving FMZ family.
3. Establish the averaged sine pair limit for that same family.
4. Supply moving-height and tail estimates needed by the chosen PCC formulation.

Priority is item 2 together with a nontrivial candidate for item 3, using
windowed homogeneous blocks and exact Gram residuals. Choosing the identity
kernel makes vacancies zero but leaves item 3 equal to PCC itself, so that
choice is not progress on the analytic conjecture.

## References and verification

* Ford--Meng--Zaharescu, Simultaneous distribution of the fractional parts of
  Riemann zeta zeros, BLMS 49 (2017), 1--9.
  https://arxiv.org/abs/1511.06814
* Ford--Soundararajan--Zaharescu, On the distribution of imaginary parts of
  zeros of the Riemann zeta function, II.
  https://arxiv.org/abs/0805.2745
* Lyons, Determinantal probability measures.
  https://arxiv.org/abs/math/0204325
* Soshnikov, Determinantal random point fields, Theorem 5.
  https://arxiv.org/abs/math/0002099
* Arias de Reyna--Rodgers, On convergence of points to limiting processes,
  with an application to zeta zeros (2024), Theorem 2 and Section 5.3.
  https://arxiv.org/abs/2311.13441

The combined candidate including collision exclusion passed Bazel/BuildBuddy,
job job_HrXVkgzbYPk_hIfMkbeNq73eOEp1oKBk, exit code 0:
https://app.buildbuddy.io/invocation/3ea3fdf5-cb72-47c8-9fd9-6f802679ae77.
This is focused candidate evidence. Separate module imports, axiom audits,
and the final full-project publication checkpoint are reported with the
delivered commit. No unresolved analytic estimate is introduced as an axiom.


The separately saved modules and an executable transitive-axiom assertion
passed in job job_Lq7_97JgXwqdcLRpMwUMsQ-kM-2fdv-8, exit code 0:
https://app.buildbuddy.io/invocation/fd432e69-e579-4487-84e1-753a66d485ec.
The six audited declarations were IsDPP.pairStatistic_error_le,
limitingLaw_isDPP, inclusion_tendsto, ordinate_injective_ae,
zero_pair_transfer_bound, and integral_tendsto_zero_of_vacancy.
Their transitive axiom sets contain only propext, Classical.choice,
and Quot.sound. The last theorem still has the analytic hypotheses
displayed in its statement.
