# FMZ, three primes, Parseval–Gram, and zero-ordinate DPPs

Date: 11 November 2026. Starting revision:
ac1bee28482212700b25cb401ff8e3263868eda1.

## Outcome and status

This development constructs an actual auxiliary DPP on the labelled copies of
zeta zeros, proves exact three-point and frame-potential identities, and connects
the existing FMZ provider to homogeneous Gram sampling. It does not prove
Montgomery pair correlation, RH, or twin primes.

There are three different kinds of statements below:

* New Lean declarations: exact finite identities, a projection-DPP probability
  law, its pair law, and FMZ assembly with its explicit Selberg hypothesis.
* Existing repository providers: imported rather than re-proved; their precise
  hypotheses remain in force.
* Paper deductions: inverse-Gram formulas, fixed-prime tensor estimates, scaling
  consequences and proposed sufficient conditions. These are not labelled
  newly kernel-checked theorems.

The terminal publication checkpoint, its exact commit and full-project scope
are the verification evidence. A successful exploratory snippet alone is not
publication verification.

## 1. What FMZ says for three distinct primes

Take distinct primes p,q,r and
z(γ)=(exp(iγ log p),exp(iγ log q),exp(iγ log r)).
For fixed smooth h, Ford–Meng–Zaharescu gives
\[
 \frac1T\left(\sum_{0<\gamma\le T}h(z(\gamma))-N(T)\int h\,dm\right)
 \longrightarrow\int h\,g\,dm,
\]
with multiplicities and product Haar m. In angular coordinates,
\[
 g(x)=g_p(x_p)+g_q(x_q)+g_r(x_r),\qquad
 g_p(x)=-\frac{\log p}{\pi}\sum_{k\ge1}p^{-k/2}\cos(2\pi kx).
\]
The published fixed-prime statement is unconditional. Its repository provider
still assumes UniformSelbergDensity (1/4); that is a formalization gap, not
an extra hypothesis of the published theorem. Source: FMZ, Theorem 1 and
Corollary 1.1, https://arxiv.org/abs/1511.06814.

The crucial arithmetic fact is **axis support**, not probabilistic independence.
A mixed mode with at least two nonzero coordinates has zero first correction.
Unique factorization proves that a ratio of distinct equal-degree prime
monomials cannot be a nontrivial prime power.

### Homogeneous Parseval improvement

If P is homogeneous in prime coordinates, every Fourier mode of |P|^(2k)
has total degree zero. Thus
\[
 \int |P|^{2k}g\,dm=0
\]
exactly, for every nonnegative integer k. Existing
PrimeTorusHomogeneous and PrimeTorusMoments establish this.

The new ActualPrimeTorusHomogeneousGram assembly connects the cancellation
to the actual multiplicity-weighted sample. In particular,
\[
 \frac{\sum_\gamma |P(z(\gamma))|^2-N(T)\int|P|^2dm}{T}\to0.
\]
Its finite polynomial quantitative theorem retains the explicit Fourier
height mass
\[
 M(h)=\sum_\nu |\widehat h(\nu)|
 \left(1+\sum_{p\in\mathcal P}|\nu_p|\log p\right)^2
\]
and gives, conditionally on the existing Selberg provider,
\[
 \left|\frac{\sum_\gamma h(z(\gamma))-N(T)\int h\,dm}{T}\right|
 \le \frac{C M(h)}{\log T}
\]
when every mode has degree zero. Riemann–von Mangoldt then gives the
paper corollary O(M(h)/log²T) after division by N(T).
For fixed homogeneous tests this improves the generic first-order
O(1/log T) bias scale. Moving tests still pay their complete M(h).

For P=a z_p+b z_q+c z_r, put A=|a|²+|b|²+|c|²,
B=|a|⁴+|b|⁴+|c|⁴ and C=|a|⁶+|b|⁶+|c|⁶. Orthogonality gives
\[
 \int|P|^2=A,\qquad
 \int|P|^4=2A^2-B,\qquad
 \int|P|^6=6A^3-9AB+4C.
\]
The fourth-moment and all-order density-cancellation theorems already exist
in Lean. The displayed closed sixth-moment evaluation is an elementary
paper deduction by matching exponent triples; Wolfram checked its polynomial
expansion. Actual zeros are not assumed to be independent.

## 2. The genuinely three-way quantity

For three normalized vectors write their Hermitian Gram matrix as
\[
 G=\begin{pmatrix}1&a&b\\\bar a&1&c\\\bar b&\bar c&1\end{pmatrix}.
\]
The new ThreePointGram declarations prove
\[
 \det G=1-|a|^2-|b|^2-|c|^2+2\Re(ac\bar b)
 =(1-|a|^2)(1-|b|^2)-|c-\bar a b|^2.
\]
Consequently, positive semidefiniteness implies the sharp Schur disk
\[
 |c-\bar a b|^2\le(1-|a|^2)(1-|b|^2).
\]
This retains the cycle phase. Pairwise absolute bounds discard it.
For phase samples the entries are normalized exponential sums at log(q/p),
log(r/p), and log(r/q). The three frequencies have an additive relation;
the product of their empirical sums need not equal one.

For a Hermitian DPP kernel the connected third inclusion function is
\[
 \rho_3-\rho_1(x)\rho_2(y,z)-\rho_1(y)\rho_2(x,z)
 -\rho_1(z)\rho_2(x,y)+2\rho_1(x)\rho_1(y)\rho_1(z)
 =2\Re(K_{xy}K_{yz}K_{zx}).
\]
The new DeterminantalThreePoint module proves the general real-kernel version
as the sum of the two directed cycles. In particular it applies to our
constructed real Fourier-projection DPP. The complex version above follows
by the same determinant expansion, and is a paper statement here.

Three-point connected correlations have no fixed sign. For example,
G(a,b,c) with a=b=1/2 and c=±1/2 is positive semidefinite in both cases,
with eigenvalues (2,1/2,1/2) and (3/2,3/2,0). Both K=G/3 are contractions.
They have identical one- and two-point probabilities; their triple
probabilities are 1/54 and 0, and connected third correlations are
+1/108 and -1/108. This example was checked symbolically by Wolfram;
it is not a claim about actual primes.

## 3. Parseval gives an exact global pair statistic

Let t_1,...,t_N be any labelled ordinates, including repeated values, and
let q_1,...,q_d be frequencies. With real b_k define
\[
 A_{ki}=b_k e^{iq_k t_i},\quad
 C=AA^*,\quad S=A^*A,\quad
 H(t)=\sum_k b_k^2e^{iq_kt}.
\]
Then S_ij=H(t_j-t_i). The repository already proves trace, square-trace
and determinant duality for C and S.

The new frame-potential theorem supplies the complete remainder:
\[
 \boxed{\ \sum_{i,j}|H(t_j-t_i)|^2
 =N^2\sum_k b_k^4+
 \|C-\operatorname{diag}(N b_k^2)\|_{\rm HS}^2.\ }
\]
Every off-diagonal Gram entry survives inside the squared norm. This is
a finite Parseval/frame-potential identity and requires no zero asymptotic.

If \(\sum b_k^2=1\), define
\(d_{\rm eff}=1/\sum b_k^4\). Subtracting the exact i=j contribution gives
\[
 \frac1N\sum_{i\ne j}|H(t_j-t_i)|^2
 =\frac N{d_{\rm eff}}-1+
 \frac{\|C-\operatorname{diag}(N b_k^2)\|_{\rm HS}^2}{N}.
\]
For equal weights b_k²=1/d, and normalized frequency Gram
G_kl=N^(-1)sum_i exp(i(q_k-q_l)t_i), this becomes
\[
 \boxed{\ \frac1N\sum_{i\ne j}|H(t_j-t_i)|^2
 =\frac Nd-1+\frac N{d^2}\|G-I\|_{\rm HS}^2.\ }
\]
These displayed normalizations are paper consequences of the checked
unnormalized identity. They require N,d>0. This refines the usual Welch
lower bound by retaining the exact error.

### A rigorous limitation of three fixed primes

A three-prime exponent box with each exponent O(log T) has only
d=O((log T)^3) modes, whereas N(T) is of order T log T.
Consequently its complete unweighted pair energy above diverges at least
as N(T)/d-1. The associated H_T cannot have bounded global pair energy
merely because H_T(u/log T) has a local pointwise limit.

This is an obstruction to that particular unwindowed finite-mode argument.
It does not exclude localized tests, a larger dictionary, or another route
to PCC. Multiplicities and all distant pairs matter here. For a tensor box
the local kernel typically limits to a *product* of sinc functions, not a
single sinc, unless the spectral weights are redesigned.

Reference for the frame-potential viewpoint:
Datta–Howard–Cochran, Geometry of the Welch Bounds,
https://arxiv.org/abs/0909.0206.

## 4. A DPP built from the actual zero ordinates

For each T the new ZeroOrdinateProjectionDPP uses the repository's actual
Copies T type, so every analytic multiplicity is retained as a label.
Given any frequency family q, take the span in real Euclidean label space
of the vectors
\[
 (\cos(q_k\gamma_i))_i,\qquad(\sin(q_k\gamma_i))_i.
\]
Let P_T be the orthogonal projection onto this span. Its matrix K_T is a
positive contraction. The module constructs an actual probability measure
on Boolean subsets of the labels and proves all its determinant inclusion
probabilities, not just an assumed DPP interface. In particular,
\[
 \Pr(i,j\in X)=K_{ii}K_{jj}-K_{ij}^2\quad(i\ne j).
\]
Existence has no RH, density, distinct-ordinate or invertibility premise.
The ground set is labels; pushing forward to ordinates need not preserve
simplicity if there are coincident values.

The following useful complex counterpart is a paper construction.
For the N-by-d feature matrix F_ik=exp(iq_k γ_i)/sqrt(N), set G=F*F.
If G is invertible,
\[
 K=FG^{-1}F^*.
\]
Otherwise \(FG^\dagger F^*\) is the projection onto range(F).
This is a projection DPP with exactly rank(F) selected labels. It is a
random selection from the zeros, not a law for the full deterministic set.

For invertible G, with C=FF*, singular-value decomposition gives the exact
whitening identity
\[
 \|K-C\|_{\rm HS}^2=\|G-I\|_{\rm HS}^2.
\]
If \(\|G-I\|_{\rm op}\le\delta<1\),
\[
 \|G^{-1}-I\|_{\rm op}\le\frac{\delta}{1-\delta},\qquad
 \left|K_{ij}-\frac dN H(\gamma_i-\gamma_j)\right|
 \le\frac dN\frac{\delta}{1-\delta}
\]
(up to transposing the convention for H). Thus the Gram residual is exactly
the quantity controlling whitening; positivity alone supplies no such bound.

The existing DPP modules also provide finite-window expectation, variance,
hole determinants and limit tools. They apply once their stated kernel and
convergence hypotheses are supplied. They do not identify this auxiliary
DPP with the zero process.

Sources: Lyons, https://arxiv.org/abs/math/0204325;
Hough–Krishnapur–Peres–Virág, https://arxiv.org/abs/math/0503110.

## 5. The three-prime arithmetic main is unusually tractable

This section is a paper deduction, not a new Lean operator provider.

On a rectangular exponent box the FMZ correction matrix is a Kronecker sum:
\[
 B=B_p\otimes I\otimes I+
   I\otimes B_q\otimes I+
   I\otimes I\otimes B_r,
\]
where (B_p)_ab=-(log p)/(2π) p^{-|a-b|/2} off the diagonal and zero on it.
Mixed differences are exactly zero. The one-coordinate Toeplitz symbol
is g_p, whose exact range is
\[
 -\frac{\log p}{\pi(\sqrt p-1)}
 \le g_p\le
 \frac{\log p}{\pi(\sqrt p+1)}.
\]
Parseval transfers this pointwise bound to every finite compression. Thus
the lower and upper spectral bounds for B are independent of exponent-box
size. Put
\[
 C_-=\sum_{s\in\{p,q,r\}}\frac{\log s}{\pi(\sqrt s-1)},\qquad
 C_+=\sum_{s\in\{p,q,r\}}\frac{\log s}{\pi(\sqrt s+1)}.
\]
Then \(-C_- I\le B\le C_+I\). For p,q,r=2,3,5, Wolfram gives
C_-=1.424818789506 and C_+=0.377698437271.

Write the *actual* normalized Gram exactly as
\[
 G_T=I+\varepsilon_T B+E_T,\qquad\varepsilon_T=T/N(T).
\]
A sufficient coercivity condition is
\[
 \varepsilon_T C_-+\|E_T\|_{\rm op}<1.
\]
For homogeneous blocks B=0 exactly. The analytical task is to estimate E_T,
not to delete it. This separates a bounded structured main from the
growing-family sampling error. It also avoids claiming positivity of
1+g: the normalized model is 1+ε_T g, which is eventually positive for
these fixed primes.

## 6. Use the repository's better asymptotics

| Provider | Actual conclusion | Boundary |
|---|---|---|
| PrimeBlockCovariance | Exact support-independent per-prime geometric covariance bounds | Arithmetic blocks; no zero-sampling estimate |
| PrimePowerCovarianceEuclideanNorm | log d-2 ≤ ||B_d|| ≤ log d+log 4+4 for the full integer main, d≥1 | Arithmetic operator, not the actual zero Gram error |
| HomogeneousPrimePowerCovariance | Equal positive prime-factor degree makes the arithmetic matrix exactly zero | Does not kill analytic residuals |
| RationalLandauMovingBand | Uniform normalized complex-zero error O(1/log T) for numerator ≤T^θ, any fixed θ<2/5 | Complex zero weights retained |
| ActualPrimeTorusFMZRate | Moving/growing Fourier tests controlled by their complete squared-height mass | Explicit UniformSelbergDensity (1/4) premise |
| ActualFejerMovingFMZ | Signed horizontal-prefix smallness transfers a moving Fejer test | Actual prefix estimate remains Open |
| MontgomeryHorizontalBessel | Horizontal form-factor defect bounded by a weighted one-point displacement budget /T | Vanishing budget remains Open |

FMZ Lemma 1 offers an external stronger prime-power complex-zero range
x≤T^θ with θ<2 after dividing its error by T sqrt(x), with the fixed
prime-power lower endpoint understood. This sharper provider has not been
formalized here. It is not a raw-ordinate estimate: removing horizontal
weights still needs a justified comparison.

The corrected 2026 BGSTB low-support theorem has an additive
O((log T)^(-1/2)) normalized error. Its complex-zero form factor cannot be
silently replaced by the raw ordinate one:
https://arxiv.org/html/2501.14545v3#S3.

## 7. Conditions that would actually advance pair correlation

**First priority: actual signed residuals.** For the homogeneous dictionaries,
use the new exact Gram structure and prove a *local, height-dependent*
operator or mean-square estimate for E_T at microscopic bandwidth.
Fixed-family FMZ limits do not provide uniformity for this step.

**Second priority: a tail estimate matched to the test.** A pointwise local
sine profile must be accompanied by uniform integrability of its weighted
pair statistic. Section 3 shows why this cannot be omitted. Use height
windows and smooth frequency weights, and include the window's exact
boundary contribution before estimating it.

**Third priority: a two-point comparison, not the full determinantal
hierarchy.** If an auxiliary continuum DPP has kernel K_T, local diagonal
L1 convergence to 1 and local Hilbert–Schmidt convergence to
\[
 S(x-y)=\frac{\sin\pi(x-y)}{\pi(x-y)}
\]
imply convergence of its two-point density to 1-|S(x-y)|².
Indeed, on a bounded window B, writing d_T(x)=K_T(x,x), the L1 error is at most
\[
 (\|d_T\|_{L^1(B)}+|B|)\|d_T-1\|_{L^1(B)}
 +(\|K_T\|_{L^2(B^2)}+\|S\|_{L^2(B^2)})
   \|K_T-S\|_{L^2(B^2)}.
\]
This supplies a quantitative pair-only criterion without asking for every
higher determinant or Fredholm determinant to converge.
To transfer that conclusion to the randomly translated/unfolded zero
process, one must separately prove agreement of its second factorial
moment measures against the chosen test class. This is a genuine Open
provider; defining it equal to the desired PCC error would merely rename
the conjecture. Full DPP convergence is stronger than necessary.

**A more economical horizontal target.** If U is the weighted raw signal
and Δ is the exact complex-zero correction in the repository's L2 space,
\[
 \|U+\Delta\|^2-\|U\|^2
 =2\Re\langle U,\Delta\rangle+\|\Delta\|^2.
\]
Vanishing of this *signed complete expression*, in the required integrated
frequency class, suffices for transfer of form factors. Requiring
||Δ||→0 is stronger. Neither condition is established here. This preserves
the cross term rather than losing it to Cauchy–Schwarz immediately.

**Arithmetic alternative above support one.** Retain the signed
short-interval variance identity V=D+C already in ShortIntervalVariance.
The central target is the uniform negative off-diagonal main
\[
 C(N,H)=-HN\log H+o_\epsilon(HN\log N)
\]
in the interior range, together with the diagonal, endpoint and transfer
estimates. Three multiplicative prime phases do not settle these additive
near-pair correlations.

The minimum worthwhile next calculation is a windowed homogeneous
three-prime Gram block with every exact residual recorded, followed by
a proved average-square bound over growing blocks. A deterministic
frame/DPP identity alone is not the missing analytic estimate.

## 8. Relation to twin primes

There is a real connection through Hardy–Littlewood prime-pair correlations.
Under RH and the requisite uniform ranges, the strong pair-correlation
conjecture is equivalent to a prime short-interval variance asymptotic.
Suitable uniform prime-pair hypotheses imply the needed averaged
correlations. The single assertion that infinitely many n,n+2 are prime
does not supply these uniform weighted asymptotics, and no equivalence
between ordinary twin primes and Montgomery PCC is asserted here.

The operations differ: FMZ uses multiplicative ratios p^a q^b r^c;
prime pairs use additive shifts n,n+h. The explicit formula connects the
two analytic settings, but a third multiplicative coordinate is not
an automatic prime-triplet theorem.

Primary references:
* Goldston–Montgomery (1987), Pair correlation of zeros and primes in
  short intervals, https://doi.org/10.1007/978-1-4612-4816-3.
* Languasco–Perelli–Zaccagnini (2012), quantitative transfers,
  https://doi.org/10.1016/j.jmaa.2012.04.058.
* Montgomery–Soundararajan, Primes in short intervals,
  https://arxiv.org/abs/math/0409258.
* Conrey–Keating, Pair correlation and twin primes revisited (2016),
  https://pmc.ncbi.nlm.nih.gov/articles/PMC5095450/.

For the current distinction from RH, Goldston–Lee–Schettler–Suriajaya
prove that full-ordinate PCC implies asymptotically 100% simple and
critical zeros; this still permits an exceptional set and is not RH:
https://arxiv.org/abs/2503.15449.

## 9. Formal declaration map

| Module | New result | Assumptions |
|---|---|---|
| Analysis/ThreePointGram | determinant_real; determinant_imaginary; schur_identity; determinant_nonneg; schur_disk | PSD for inequalities |
| Analysis/PrimeProbeFramePotential | frame_potential_exact; frame_potential_lower; coordinateGram_primeFeature_diagonal; phase_pair_energy_exact; phase_pair_energy_lower | Finite index types; arbitrary real phases |
| Analysis/ActualPrimeTorusHomogeneousGram | tendsto_centered_degree_zero_polynomial_div; tendsto_centered_homogeneous_gram_div; homogeneous_gram_polynomial_eq; eventually_degree_zero_polynomial_bound | Actual zero sample; primality and degree; explicit Selberg premise for analytic statements |
| Probability/DeterminantalThreePoint | IsDPP.three_point; IsDPP.connected_three | Given real DPP |
| Probability/ZeroOrdinateProjectionDPP | law_probability; law_isDPP; law_two_point | Constructed from actual zero labels; no analytic hypothesis |

The new constructions use ordinary Mathlib foundations. No unresolved
analytic assertion is introduced as a project axiom. The proposed sine
limit, microscopic residual bounds and transfer to PCC remain Open.


## 10. Focused verification evidence

All five new modules compiled through their own imports with Bazel/BuildBuddy,
exit code 0, in job job_6VS5GIfNhaOksODY9PH9gziHza3smDLX:
https://app.buildbuddy.io/invocation/763383a2-fd15-467b-b9f9-676200b59544.

A second successful Bazel job, job_GYue0NS6YsUHa2aN3XxpXuIMhSLN8Dnr,
collected the transitive axiom dependencies of schur_disk,
phase_pair_energy_exact, eventually_degree_zero_polynomial_bound,
IsDPP.connected_three, and ZeroOrdinateProjection.law_isDPP. An executable
assertion rejected any dependency outside propext, Classical.choice, and
Quot.sound; it passed:
https://app.buildbuddy.io/invocation/befc700e-5dde-451e-8301-461df31033e3.

This axiom check does not discharge explicit theorem hypotheses such as
UniformSelbergDensity (1/4). The full-project publication checkpoint is a
separate validation step; its terminal result is reported with the commit.
