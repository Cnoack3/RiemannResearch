# Mellin sine kernels, prime words and the zeros

The declarations below follow the 27 November 2026 Mellin / prime-orbit handoff. The physical counting convention includes every analytic occurrence. The pair test has a strict lower gap endpoint and retains the full height normalization $D_T=T\log T/(2\pi)$.

## What the auxiliary projection determines

At a fixed frequency center the unfolded auxiliary residue kernel has limiting kernel $e^{-\pi i(x-y)}k(x-y)$, where $k(x)=\operatorname{sinc}(\pi x)$. Removing evaluation at the anchor gives a Schur complement. Its limiting kernel, up to the same diagonal conjugation, is $k(x-y)-k(x)k(y)$. The convergence holds entrywise and for every fixed finite determinant. On the diagonal its intensity plus the continuum von Mangoldt probe energy is exactly one. A local process convergence deduction uses additional trace and local convergence arguments. The finite-determinant theorems apply at fixed centers. [Bulk determinant](RH/ParetoResidueSineLimit.lean) · [Reduced Palm kernel](RH/ParetoResiduePalmSineLimit.lean)

At a prime period the full-divisor legal space is spanned by a single transported residue atom. Every one-feature kernel has zero two-point determinant, whereas the reduced sine kernel has determinant one at offsets $1$ and $2$. An all-period determinant transfer to the legal projection therefore fails. On $[0,3]$ a normalized one-feature projection has local trace at most one, while the limiting reduced sine trace is at least $5/2$. The formal trace bound states its diagonal regularity and feature-normalization assumptions explicitly. The growing lcm periods used in the legal approximation have a different divisor dictionary. [Prime-period obstruction](RH/ParetoPrimePeriodPalmObstruction.lean)

Chronologically neighboring ordinate phases converge to diagonal Haar at fixed observation orders. Rounding growing orders recovers the Fourier transform of two adjacent gaps with error $O(T/N_T)$. Orthogonality of translated characters bounds the reconstruction error. The values of the resulting consecutive-gap distributions require arithmetic information. [Chronological Haar](Analysis/ActualPrimeChronologicalHaar.lean) · [Two-gap reconstruction](Analysis/ActualThreePrimeAdjacentGaps.lean) · [Parseval](Analysis/ThreePrimeGapParseval.lean)

## Every positive pair and the forward atom

Let $Z_T(u)=\sum_j e^{iu\gamma_j}$, $a_T=\log T/(2\pi)$, and $C_T=\sum_y m_T(y)^2$, with $m_T(y)$ the number of occurrences at height $y$. For an even test $f$ with integrable real cosine-inversion weight $w$, the exact formula is

$$
  \frac1{D_T}\sum_{\gamma_j>\gamma_i} f(a_T(\gamma_j-\gamma_i))
   =\frac1{2D_T}\int_{\mathbb R} w(v)
        \left(|Z_T(v\log T)|^2-C_T\right)\,dv .
$$

Replacing $v\log T$ by its nearest multiple of $h>0$ changes the right side by at most $\|w\|_1 hTN_T(N_T-1)/(4D_T)$. Any fixed three ordered primes, including $2,3,5$, supply ratio words with arbitrarily small positive frequency. Their integer powers are exact prime characters. For $0<h_T\le T^{-3}$ eventually the error is $O_w(\log T/T)$. The Fourier inversion provider applies in particular to real even Schwartz functions, hence to smooth even compactly supported tests. [Frequency mesh](Analysis/ThreePrimeFrequencyMesh.lean) · [Collision subtraction and rounding](Analysis/MontgomeryAllPairWordRounding.lean) · [Moving-height limit](Analysis/MontgomeryAllPairWordLimit.lean) · [Even Fourier tests](Analysis/MontgomeryEvenFourierTests.lean) · [One mesh for every test](Analysis/MontgomeryThreePrimeSchwartz.lean)

**Open for unconditional ordinary PCC.** For every positive rational $q$, write $A_T(q)$ for the signed argument increment on an interval starting at an actual zero occurrence. The uncovered arithmetic assertion is

$$
 A_T(q)\longrightarrow -\int_0^q k(x)^2\,dx .
$$

Equivalently, its limit is the integrated reduced Palm diagonal minus $q$. The prime probe supplies the positive integrated squared sine term. The zero-sampled increment requires the opposite signed term. Evaluation of the squared-word integrals at the sine-law value for all even smooth compactly supported tests is equivalent to ordinary PCC. [Three-prime PCC criterion](Analysis/MontgomeryThreePrimePCC.lean) · [Compact tests](Analysis/MontgomeryCompactGapTests.lean) The available fixed-weight FMZ mean-square limit has height normalization $T$ for one amplitude, while this pair formula integrates a squared moving amplitude with normalization $D_T$. [Prime trace criterion](Analysis/MontgomeryPrimeProbeEnergy.lean) · [Finite-rank alternative](Analysis/MontgomeryFiniteIndexGap.lean) · [FMZ on diagonal Haar](Analysis/InfiniteDiagonalFMZ.lean)

## What would establish RH with every zero simple

For every fixed physical height bound $H$ and unfolded width bound $Q$, deleting any set of occurrences below or at $H$ eventually leaves the exact positive-gap counts unchanged simultaneously for every $q\le Q$. Distinct ordinates through $H+1$ give finitely many positive gaps, each eventually wider than $Q/a_T$. Incident zero gaps are excluded by definition. [Bounded-height deletion](Analysis/MontgomeryBoundedHeightGaps.lean)

The absolute forward atom does detect finite exceptions. The checked target for RH and analytic simplicity of every strip zero is $C_T<N_T+2$ at arbitrarily large heights. An exceptional positive-height zero contributes a reflected or repeated occurrence at the same ordinate. The two ordered orientations account for the integer threshold two. Conjugation carries the conclusion to negative heights. The equivalent Fejér condition permits a height-dependent bandwidth. Proving the absolute bound remains open. [Global collision and Fejér criteria](Analysis/MontgomeryPhysicalGapTransfer.lean)

The density consequence of positive-gap PCC is that a proportion tending to one of *all* occurrences are both simple and critical. The Lean theorem takes a short-window moment upper estimate explicitly. Goldston, Lee, Schettler and Suriajaya provide the analytic input. [Lean density implication](Analysis/MontgomeryPositiveGapDensity.lean) · [Published theorem](https://arxiv.org/abs/2503.15449)

For an operator symmetric on its specified domain, a point eigenvalue is real. Point-spectrum coverage of every nontrivial zero at parameter $-i(\rho-1/2)$ therefore implies RH. If eigenspace dimensions equal zeta analytic orders and those dimensions are at most one, each derivative $\zeta'(\rho)$ is nonzero. Such an operator and complete correspondence remain open. A projection has only zero and one as possible point eigenvalues. More generally, the eigenvalue moduli of any bounded operator are bounded by its operator norm, whereas the actual zeta ordinates are unbounded. Thus a Hamiltonian realizing the usual unrescaled spectral parameters must be unbounded. The moment-pencil factorization recovers two real ordinates when the measure consists of exactly two distinct positive-weight atoms and its four moments are known. [Spectral transfer](RH/HilbertPolyaZeroTransfer.lean) · [Projection and bounded-operator obstruction](RH/HilbertPolyaProjectionObstruction.lean) · [Two-atom pencil](Analysis/TwoAtomMomentPencil.lean)

## The independent Pareto criterion

For a fixed finite family of distinct positive critical-line zeros, let $E_M$ be the legal projection error squared, $R_M$ the squared remainder after screening, and $E_\infty$ the squared distance of the constant to the closed legal span. If RH fails then

$$
 E_\infty>0,\qquad R_M/E_M\longrightarrow1,\qquad
 M(E_M-R_M)/E_M\longrightarrow
   \frac{2\sum_i |\rho_i|^{-2}}{E_\infty}.
$$

For each fixed $\theta<1$, RH is equivalent to the existence of a nonnegative $B_M\to0$ for which $R_M\le\theta E_M+B_M$ at arbitrarily large cutoffs. Proving this independently is the remaining Pareto obligation. This criterion yields the critical line location. Simplicity requires multiplicity information, as in the collision or spectral statements above. [Pareto dichotomy](RH/ParetoZeroAbsorptionDichotomy.lean) · [Cofinal absorption](Analysis/CofinalRemainderAbsorption.lean)
