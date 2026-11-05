# Mertens estimates and squarefree displacement criteria (2026-11-05)

Write $M(x)=\sum_{n\le x}\mu(n)$ and $\Phi(x)=(\log x)^{3/5}(\log\log x)^{-1/5}$. Let $V$ be the closed legal squarefree span in $L^2(Q)$, $r=1-f_Q$ its projection residual and $d=f_Q-f_P$ the displacement between the two projections. $T_N$ keeps all physical coordinates beyond $N$.

## Recursive prime carries

**Unconditional.** Along a finite Bézout chain the integer floors telescope
with exact path multipliers. On a finite tree the charge at a composite equals
its incoming coefficient less the signed sum from its children. For normalized
infinite chains with exact Bézout coefficients the identity passes to
absolutely convergent series at each fixed physical site. The positive radix
digit for a child $r$ has full physical eighth-power sum at most $3/r$.
[Finite recursion](RH/QRecursivePrimeCarry.lean) · [Tree charges](RH/QRecursiveCarryDetection.lean) ·
[Infinite recursion](RH/QInfiniteRecursiveCarry.lean) · [Digit estimates](RH/QRecursiveDigitBounds.lean).

**Checked tree criteria.** The signed finite Euler leaf sum extends from $\Re s>1$
holomorphically to $\Re s>1/2$ exactly under RH. Deleting finitely many fixed primes
preserves this equivalence. The compact space of prime masks has clopen prefix
cones. Upward recursion, signed child escape, finite-head pooling and finite-fit
budget convergence hold as identities or limits. [Theorems, proofs and examples](RH/PrimeTreeCriteria20261105.md).

**Conditional research reductions.** A one-sided pruned budget bounded along
cofinal horizons at every physical integer, with a common constant, implies RH;
the same implication holds with a nested cofinal condition on matched finite fits.
Vanishing of every fixed descendant sum plus a local signed child-tail bound also
implies RH. **Open:** proving either estimate for the matched displacement, or
the moving eighth-moment bound. The matched-tree converses take Báez-Duarte's
published approximation theorem as an explicit parameter. The prime-2 Möbius
subtree transfer is internal; the arithmetic RH equivalence invokes the
published Littlewood criterion. [Earlier carry analysis](RH/RecursivePrimeCarryResearch20261105.md).

## All-order squarefree carries and the signed Möbius charges

**Unconditional.** The centered residue components at all divisors reconstruct
each atom. Each squarefree primitive component has a nonpositive prefix given
by a Ramanujan Gram form. Its complete-period and incomplete signed block bounds
hold in every order. Its exact Haar variance is $J_2(D)/(12D^2)$. Exact finite
Ramanujan rows express the physical jump and its antiderivative using the
signed multiple sums of the charges. Balazard’s scalar limit removes the slope
in the naturally ordered centered translation formula at each fixed physical site.
The inverse-square absolute charge mass is finite for every physical vector.
[Components](RH/QAllOrderCarryPackets.lean) · [Gram sign](RH/QRamanujanContrastGram.lean) ·
[Block bounds](RH/QAllOrderCarryBlocks.lean) · [Variance](RH/QAllOrderCarryVariance.lean) ·
[Finite charge rows](RH/QChargeRamanujanPackets.lean) · [Matched Bézout carry](RH/QManyPrimeMatchedCarry.lean) ·
[Limit formula](RH/QHeadSlopeLimit.lean) · [Absolute charge mass](RH/QAbsoluteChargeMass.lean).

The physical first difference has normalized Jordan coefficient
$\sqrt{J_2(s)}$ times the signed inverse-square charge sum over multiples of $s$.
Parseval gives its exact squared norm for every physical vector.
[Jordan charge identities](RH/QJordanChargeRows.lean).
A composite charge extracts its own carry coefficient from each linear combination
of prime carries and commutes with fixed-site limits. For noncoprime factors a
quotient digit recovers the missing modulus.
[Composite detection](RH/QCompositeCarryDetection.lean) · [Repeated factors](RH/QMixedRadixCarry.lean).
The one-sided finite charge hypothesis may also be applied after subtracting the
Möbius profile of any constant (QChargeDilation). Vanishing composite charges
and a one-sided bound on the actual difference imply RH by testing finite prime
products. **Open:** either sign bound and the requisite composite cancellation
for the actual displacement. [Prime support criterion](RH/QPrimeChargeRigidity.lean).

**Conditional research reductions.** Any ordinary finite limit of the unscaled
physical difference is equivalent to zero displacement. Either asymptotic
one-sided sign for the difference already implies RH. Bounded partial sums
of either sign of the actual Möbius charges suffice, as does the stated
cofinal polylogarithmic harmonic bound on the one-sided charge rows.
**Open:** establishing any of these sufficient hypotheses for the actual
displacement, or the uniform eighth moment on growing LCM blocks.
[Difference limits](RH/QDifferenceLimits.lean) · [Dilation and charge criteria](RH/QChargeDilation.lean) ·
[Derivations, four- and five-prime examples, infinite GCD rows, and obstruction](RH/AllOrderCarryAndDifferenceResearch20261105.md).

## LCM blocks and physical CRT carries

**Conditional research reduction.** For distinct increasing LCMs, a uniform
eighth-power budget on the blocks of the limiting displacement implies RH
given physical approximation at a pair of conjugate exponents with $q<8$.
A common bound attained arbitrarily late on each fixed block also suffices.
**Open:** the actual uniform bound and the in-project physical approximation
provider at such an exponent. [Block criterion](RH/QLcmDisplacementCriterion.lean) ·
[Exponent transfer](RH/QSubcriticalDisplacementMoment.lean).

**Unconditional.** The matched fit stopped at conductor $M$ has summable
block contributions beyond its own LCM, uniformly in the block lengths.
For the limiting displacement, translation by the LCM removes every carry
supported only on primes through $M$. The centered identity retains the
finite boundary slope. The centered pair interaction has a signed
inverse-square block estimate, and the Bézout carry cancels the common
energy in the matched projection equations.
[Frozen fits](RH/QFrozenConductorBlocks.lean) · [Translation](RH/QDisplacementTranslationCarry.lean) ·
[Physical pair interaction](RH/QCRTPairCarryBlocks.lean) · [Matched equations](RH/QMatchedCRTCarry.lean) ·
[Exact identities, full-period covariance, signed coefficient tests, and remaining estimate](RH/LcmDisplacementCarryResearch20261105.md).

## Aligned finite eighth moments

The actual displacements are $d_N=f_{Q,N}-f_{P,N}$ on the matched finite spans.
The cofinal bound is $\liminf_N\sum_{n\le N}|d_N(n)|^8/n^2<\infty$.
The liminf takes values in the extended nonnegative reals.

**Conditional research reduction.** Given physical $L^{8/7}(Q)$ approximation
of $1$ by the squarefree closure, the cofinal bound implies RH. The fixed-head
limit gives $d\in L^8(Q)$, and Hölder makes the actual witness mean vanish.
**Open in the project:** the subcritical approximation provider and the cofinal
bound on the actual displacements. The paper provider uses J. Lee's natural
approximation and the strict margin below $7/8$ in B. Liu's zero-free
half-plane. [Finite criterion](RH/QFiniteEighthMoment.lean) ·
[Lee's theorem as recorded by Báez-Duarte](https://arxiv.org/pdf/math/0011254) ·
[Liu, Theorem 27.1](https://arxiv.org/html/2610.12234v2).

**Unconditional finite forcing estimates.** Project the first $T$ physical
coordinates of the smoothed finite Pareto residual using the full $Q$ stage.
The signed error is exactly the projection of the omitted forcing. Its
$Q$-weighted eighth moment through $N$ tends to zero when $T\to\infty$ and
$N^6\le(T+2)^8$. Every conductor $m>T$ has truncated forcing $A_{N,T}/m$.
For the RH implication alone, $T\to\infty$ may be arbitrarily slow because
the projected truncated forcing converges in Hilbert norm to the actual
displacement. Its own aligned cofinal bound is then sufficient under the
same approximation premise. [Forcing estimates](RH/QFiniteEighthForcing.lean).

**Matched evaluation kernels and reconstruction bounds.** The unconditional identity
`finiteDisplacement_eq_paretoDual_pairing` expresses each site as a Pareto residual
pairing after both projections. The aligned bound uses three explicit Gram matrices.
`full_conductor_forcing_bessel` controls all signed, scaled Gram deficits at once.
`adjacent_full_data_difference` controls their adjacent differences. The finite prime
innovation shows that the Euclidean bound on the Gram inputs alone permits diverging
inverse norms. [Signed forcing](RH/QFiniteForcingData.lean) ·
[Prime obstruction](RH/QPrimeForcingObstruction.lean) ·
[Reconstruction diagonal](RH/QFiniteEighthReconstruction.lean) ·
[Matched evaluation kernels](RH/QFiniteParetoDualKernel.lean).

**Conditional research reductions.** With the same physical subcritical approximation,
any one of the following suffices: a cofinal bound on the matched kernel product, a
cofinal bound on the Q error and reconstruction product, a bound on the aligned sum
after removing at most a fixed number of sites at each good stage, or a separate
cofinal eighth bound for each projected squarefree physical coordinate. **Open:** the
corresponding cofinal upper estimates and a project provider for the physical approximation.
The signed identities and unconditional finite inequalities do not use either input.
[Trimmed criterion](RH/QFiniteEighthCapped.lean) · [Squarefree columns](RH/QFiniteColumnEighth.lean) ·
[Derivations, limitations, and numerical tests](RH/MatchedEighthMomentResearch20261105.md).

## Unconditional ordinary Mertens estimates

There exist $c,B>0$ such that for every real $x\ge1$,
\[
 |M(x)|\le Bx\exp(-c\sqrt{\log x}).
\]
For the certified classical strip width $a>0$, every $0<c<\sqrt a/2$ works. The declaration `M_sqrt_log_global_of_lt_contourEndpoint` supplies a constant $B(c)$ for the whole interval. The declaration `M_sqrt_log_eventually_of_lt_contourEndpoint` gives prefactor one for all sufficiently large $x$. At the endpoint, write $u=\sqrt{a\log x}$. The more precise theorem `classical_mertens_at_weighted_contourEndpoint` gives
\[
 M(x)=O\bigl(x(1+u)e^{-u/2}\bigr).
\]
The declaration `M_sqrt_log_weighted_endpoint_global` gives a single multiplicative constant for this endpoint bound for every real $x\ge1$. The proof bounds $1/\zeta$ on an all-height zero-free rectangle and takes $\log T=u$ in the Mellin contour for the smoothed Möbius sum. The exact identity $\int_T^\infty (\log t)^2t^{-2}\,dt=((\log T)^2+2\log T+2)/T$ retains logarithmic powers on the contour edges. Taking the smoothing parameter $(1+\log T)/\sqrt T$ balances the edges with the error in passing to the ordinary sum. The proof supplies existence of $a$ and the big-O constants. The stronger Vinogradov–Korobov and explicit Lee–Leong estimates used below still require a separate proof in this project. [Reciprocal of zeta](NumberTheory/PrimeNumberTheorem/ClassicalReciprocalMertens.lean) · [All-height rectangle](NumberTheory/PrimeNumberTheorem/ClassicalMertensReciprocalRectangle.lean) · [Möbius contour and Mertens theorem](NumberTheory/PrimeNumberTheorem/MertensClassicalContour.lean) · [Bialer's contour formalization](https://github.com/gersh/ternary-goldbach-lean/tree/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/PrimeCounting).

Consequently $\log(2+|d(n)|)=o(\sqrt{\log n})$ implies RH. More generally, for every fixed $0<b<\sqrt a/4$, the eventual estimate $|d(n)|=O(\exp(b\sqrt{\log n}))$ implies RH. Proving this growth condition for the actual projection displacement remains open. [Square-root displacement criterion](RH/QSquarefreeSqrtLogDisplacement.lean).

There is also a general transfer from a Chebyshev error to a Mertens error. Fix $0<\alpha<1$, $a>0$, and assume $\psi(x)-x=O(x\exp[-a(\log x)^\alpha])$. Then every $0<d<a^{1/(1+\alpha)}$ admits a constant $B$ with $|M(x)|\le Bx\exp[-dS(x)^{\alpha/(1+\alpha)}]$ for all real $x\ge1$, where $S(x)=(6+\log x)\log(6+\log x)$. The proof tracks the prime-error coefficient through the finite Möbius recurrence and its choice of cutoff. [Arithmetic transfer](NumberTheory/PrimeNumberTheorem/MertensPrimeErrorTransfer.lean) · [Ramaré and Zuniga Alterman](https://doi.org/10.7169/facm/250121-19-5).

Taking $\alpha=1/2$ in the classical prime number theorem gives $d>0$ and $B\ge0$ such that
\[
 |M(x)|\le Bx\exp(-dS(x)^{1/3}) \qquad (x\ge1).
\]
`M_cubeRoot_logProduct` supplies this bound without an arithmetic hypothesis. `M_logProduct_eventually_of_lt_one_third` gives eventual prefactor one and every fixed exponential coefficient at each exponent $0\le\beta<1/3$, including the former $1/11$. The exponent follows from the classical Chebyshev error: in logarithmic time $T$, the proof takes $z=((T+6)\log(T+6))^{1/3}$ and a delay $L=\ell z^2$ with fixed $\ell>0$, so $\sqrt L=\sqrt{\ell}z$. The real-cutoff estimate uses the same coefficient as the integer bound. [Mertens theorem](NumberTheory/PrimeNumberTheorem/MertensCubeRoot.lean) · [PNT+ classical prime-error proof](NumberTheory/PrimeNumberTheorem/Quantitative/ClassicalStrongPNT.lean) · [Upstream source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/commit/747e480362ef6a0a7341055a84372333d72fa62a).

A separate explicit theorem gives $9|M(x)|\le 2x+8$ for every real $x\ge0$ and $9|M(x)|\le 2x-5$ for $x\ge18$. At the fixed slope $2/9$, the global additive term $8/9$ is sharp since $M(5)=-2$. Odd-pair cancellation first restricts the signed sum to odd indices in $(x/2,x]$. The proof removes multiples of nine, then finds opposite Möbius signs using Bertrand's postulate. [Finite bounds](NumberTheory/PrimeNumberTheorem/MertensOddSquareSieve.lean).

**Conditional research reduction.** For the actual squarefree displacement, $\log(2+|d(n)|)=o(S(n)^{1/3})$ implies RH. **Open:** the displayed growth estimate for the actual displacement. [Cube-root displacement theorem](RH/QSquarefreeCubeRootDisplacement.lean).

## Cofinal gaps between the two finite minimum errors

For each finite squarefree space, let $e_{Q,N}$ and $e_{P,N}$ be the two minimum squared errors for the constant 1. The gap $G_N=\zeta(2)e_{Q,N}-e_{P,N}$ equals the squared Pareto norm of the finite displacement plus the metric correction of the Q residual. Each gap is positive. The gaps converge, and the limiting residual is zero exactly when for every $\epsilon>0$ arbitrarily large stages have $G_N\le\epsilon$.

**Conditional research reduction.** `riemannHypothesis_of_cofinal_finiteMetricGap` derives Mathlib RH from this gap condition. **Open:** establish the cofinal bound for the actual finite distances. [Finite metric gap](RH/QFiniteMetricGap.lean).

## Square-sampled Mertens estimates and the boxed displacement criterion

`NumberTheory.PrimeNumberTheorem.mertens_vk_of_square_samples` retains the exponent $a>0$ from an eventual bound $|M(k^2)|\le Ck^2e^{-a\Phi(k^2)}$ with $C\ge0$. Filling the gaps between squares gives $|M(x)|\le(C+3)xe^{-a\Phi(x)}$ on the full real half-line beyond a threshold. `riemannHypothesis_of_square_sample_vk_log_displacement` specializes this to the logarithmic displacement criterion. Walfisz supplies the arithmetic estimate in the literature (Gerhold, Acta Arith. 142 (2010), equation (2), DOI 10.4064/aa142-2-8). The square-sampled estimate has **Open** formal-provider status.

`QMertensFirstMoment.residual_zero_iff_vk_log_displacement` identifies zero squarefree projection residual with $\log(2+|d(n)|)=o(\Phi(n))$ under the ordinary VK Mertens bound. The upper-growth condition on the actual displacement is **Open**. Every interior rate $0<b<a$ already forces zero residual under $|d(n)|\le D e^{b\Phi(n)}$ eventually. The equivalence with zero residual uses the signed pairing and needs no reverse implication from RH.

`QDisplacementVKSignCount` gives a separate conditional test. Under the same VK arithmetic input, at arbitrarily large $X$ it suffices that one strict sign of $d$ occurs on at most $D e^{b\Phi(X)}$ sites through $X$, with $0\le b<2^{2/5}a$. The choice of sign may depend on $X$. The sign-count premise for the actual displacement is **Open**.

## Ordinary power estimates and the displacement at the critical exponent

Write $E_N$ for the canonical Möbius head, $m_N=\sum_{k\le N}\mu(k)/k$, and $J=\lfloor n/(N+1)\rfloor$. Its signed defect for positive sites is
$$1-E_N(n)=\sum_{k=1}^{J}(M(\lfloor n/k\rfloor)-M(N))+(N+1)m_NJ.$$
The finite identity preserves the reciprocal-charge term. Under $|M(n)|\le Cn^s$, $0\le s<1$, Abel summation in natural order bounds $m_N$. The finite identity then yields $|1-E_N(n)|\ll_{C,s}\min(N,nN^{s-1})$ uniformly. See [the reciprocal sum](RH/MertensPowerReciprocal.lean) and [the finite defect](RH/MertensDefectPowerArithmetic.lean).

The bracket also has an unconditional probabilistic interpretation. Under $P(K=k)=1/[k(k+1)]$, the full Pareto mean of $M(K)$ is zero and
$$ (N+1)m_N-M(N)=-\mathbb E_P[M(K)\mid K>N]. $$
The conditional law here is discrete: its weights are $(N+1)/[k(k+1)]$ for $k>N$. The expectation is absolutely convergent. Consequently $1-E_N(n)$ is exactly the sum over $1\le k\le J$ of $M(\lfloor n/k\rfloor)-\mathbb E_P[M(K)\mid K>N]$. See [MertensParetoCorrection](RH/MertensParetoCorrection.lean).

Put $\beta=(1-s)/(2-s)$. Each of the following hypotheses on $d=f_Q-f_P$ suffices for RH under this ordinary Mertens bound.

| Displacement premise | Lean declaration |
|---|---|
| $\sum_{n\ge1}\lvert d(n)\rvert\,n^{-1-\beta}<\infty$ | [riemannHypothesis_of_mertens_power_and_displacement_moment](RH/MertensPowerCriterion.lean) |
| $d(n)=o(n^\beta)$ | [riemannHypothesis_of_mertens_power_and_critical_little_o](RH/MertensCriticalPowerDisplacement.lean) |
| $\sum_{n\le X}\lvert d(n)\rvert=o(X^{1+\beta})$ | [riemannHypothesis_of_mertens_power_and_critical_prefix](RH/MertensCriticalAverageDisplacement.lean) |

Under the averaged hypothesis, summation by parts against a decreasing weight bounds the signed pairing. The endpoint argument sums the cutoff-dependent minimum. With $a=1-s$ its row against the weight $n^{\beta-2}$ is at most $1/\beta+1/(1-\beta)$, uniformly in $N\ge1$. The vanishing head and the little-o hypothesis force its pairing with the actual witness to vanish. See [the row estimate](Analysis/MertensPowerEndpoint.lean). If Mertens power bounds are supplied only for $s>7/8$, the immediate strict growth range is $\gamma<1/9$.

For a concrete application, `riemannHypothesis_of_mertens_87499_and_ten_ninths_prefix` takes $M(n)=O(n^{87499/100000})$ and $\sum_{n\le X}\lvert d(n)\rvert=O(X^{10/9})$. Since $0.8749570195<0.87499$, the former estimate follows on paper from [Liu, arXiv:2610.12234v2](https://arxiv.org/abs/2610.12234v2) and [Gerhold, Proposition 3](https://doi.org/10.4064/aa142-2-8). The local Lean theorem explicitly accepts the Mertens estimate.

**Conditional research reduction.** The fixed power bound on $M$ is an explicit arithmetic premise. Gerhold, *Acta Arith.* 142 (2010), Proposition 3, relates the family of such bounds above a boundary to the corresponding zero-free half-plane. Its use here as a provider is **Open** in this development. Proving either displayed condition for the actual displacement is **Open**.

An estimate on a sampling set suffices if every $n$ has a lower sample at distance $O(n^s)$. [MobiusPowerSamples](NumberTheory/PrimeNumberTheorem/MobiusPowerSamples.lean) specializes this to perfect $r$th powers, preserving the exponent $s$ for $s\ge1-1/r$.

**Shifted tests.** [MertensHolomorphicPairing](Analysis/MertensHolomorphicPairing.lean) recovers the archive’s abstract interior and boundary continuation arguments. [MertensShiftedLocalMajorant](RH/MertensShiftedLocalMajorant.lean) proves cancellation separately at each admissible shift by absolute summation over conductors and sites. Along shifts approaching zero, a summable lower bound on the real rows and the stated power moments imply vanishing of the projection residual. The signed witness identity supplies its nonnegative mean. For a common arithmetic envelope $E(n)$ dominating every fixed $n^{1-\eta}$ eventually and integrable against $Q$, $\sum Q(n)E(n)\lvert d(n)\rvert<\infty$ suffices when $|H_{s_j}(n)|\le E(n)$ along a sequence approaching zero. A sufficient estimate on those rows for the actual displacement is **Open**.

**Interpolation and exact-head energy.** [MertensSumVK](NumberTheory/PrimeNumberTheorem/MertensSumVK.lean) and [MertensStretchedFloor](NumberTheory/PrimeNumberTheorem/MertensStretchedFloor.lean) transfer bounds from integers to reals with both constants preserved for the stated profiles. [QMobiusMertensProfileEnergy](RH/QMobiusMertensProfileEnergy.lean) keeps $(1+t)e^{-t}$ in the complete exact-head energy. When replacing rate $b>0$ by $c<b$, [MertensEntropyOptimum](Analysis/MertensEntropyOptimum.lean) proves that the optimal scalar multiplier on the real line is $b e^{-c/b}/(b-c)$. Only this scalar maximization is claimed to be optimal.

## Previously catalogued transfers

| Module | Declarations and scope |
|---|---|
| [MertensExponentialEntropy](Analysis/MertensExponentialEntropy.lean) | `exponential_entropy_eq`, `exponential_entropy_le`, `exponential_entropy_small`. For $\eta(\varepsilon)=\varepsilon(1+\log(1/\varepsilon))$, one has $\eta(e^{-u})=(1+u)e^{-u}$, at most $1/2$ for $u\ge6$. Every $0\le c<b$ gives $\eta(e^{-bu})\le[b/(b-c)]e^{-cu}$ by the elementary exponential inequality. |
| [MertensPowerPairing](Analysis/MertensPowerPairing.lean) | `min_cutoff_power_le`, `power_defect_pairing_tendsto_zero`, `summable_power_pairing_of_growth`. For $a>0$, defects bounded by $C\min(N,(n+1)N^{-a})$ that eventually vanish at each fixed coordinate pair to zero against a weight $v$ if $\sum(n+1)^{1/(1+a)}\lvert v_n\rvert<\infty$. For $v_n=w_n/(n+1)^2$, growth $w_n=O((n+1)^\beta)$ suffices when $\beta<a/(1+a)$. The defect bound is an input to this scalar result. |
| [VinogradovKorobovProfile](Analysis/VinogradovKorobovProfile.lean) | `vkProfile_tendsto_atTop`, `vkProfile_eventually_mono`, `vkProfile_eventual_log_increment`, `vkProfile_dominates_logLog_sq`. The profile diverges and is eventually increasing. For every $\delta>0$, $\Phi(y)-\Phi(x)\le\delta\log(y/x)$ for all sufficiently large $x$ and all $y\ge x$. `vk_second_order_of_variable_coefficient` extracts a correction $k\Phi/\log\log x$ for $k<Ar/5$ from its stated variable-coefficient bound on an arbitrary $F$. |
| [QProfileTailEnergy](RH/QProfileTailEnergy.lean) | `profile_tail_energy_le` bounds $\lVert T_Nu\rVert_Q^2$ by $2C^2H(N)^2/(\zeta(2)N)$ from $\lvert u(n)\rvert\le CH(n)$ and $H(n)^2/\sqrt n\le H(N)^2/\sqrt N$ beyond $N\ge1$. `profile_weighted_tail_tendsto_zero` and its `of_little_o` variant give a vanishing weighted tail with $\eta_jH(q_j)^2\to0$, or with this product bounded and $u=o(H)$ in the stated envelope sense. |
| [QSquarefreeMertensProfileCriterion](RH/QSquarefreeMertensProfileCriterion.lean) | `defect_energy_of_uniform_mertens_log` combines the repository's uniform Mertens energy estimate with the complete exact-head defect. `annihilator_mean_zero_of_mertens_profile` and `profile_B_tail_tendsto_zero` supply the two estimates used by `residual_zero_iff_mertens_profile_tail`. The tail and physical-envelope RH corollaries apply the repository's squarefree capacity criterion. |
| [QSquarefreeVKDisplacement](RH/QSquarefreeVKDisplacement.lean) | `riemannHypothesis_of_vk_exponential_displacement`, `riemannHypothesis_of_vk_log_displacement`, `mertens_vk_absorb_constant`, `riemannHypothesis_of_walfisz_displacement`. Under an eventual Mertens bound $\lvert M(x)\rvert\le Cx e^{-a\Phi(x)}$, the eventual bound $\lvert d(n)\rvert\le D e^{b\Phi(n)}$ suffices for RH for every $0<2b<a$. In particular $\log(2+\lvert d(n)\rvert)=o(\Phi(n))$ suffices. Euclid's theorem supplies cofinal legal heads. |
| [MertensFirstMomentEnvelope](RH/MertensFirstMomentEnvelope.lean) | An explicit finite defect bound and dominated convergence for the signed Schur witness imply RH from a summable first-moment majorant along cofinal legal heads. |
| [MertensVKFirstMoment](RH/MertensVKFirstMoment.lean) | Under the VK Mertens estimate at rate $a$, for each fixed $0<c<a$, finiteness of the pure weighted absolute moment is equivalent to zero projection residual and implies RH. The pointwise corollary admits every $0<b<a$, with arbitrary fixed prefactors. The full infinite-range Mertens estimate and the actual displacement bound are explicit premises. |

The residual equivalence has explicit quantifiers. Take $q_j\to\infty$ with $q_j+1$ eventually squarefree, $0<\varepsilon_j\le1$, $\eta_j=\eta(\varepsilon_j)\le1/2$ eventually, and $\eta_j\to0$. Assume $\lvert M(y)\rvert\le\varepsilon_j y$ for **every** real $y\ge q_j$ for all sufficiently large $j$. Then

$$r=0\quad\Longleftrightarrow\quad q_j\eta_j\lVert T_{q_j}d\rVert_Q^2\longrightarrow0.$$

Residual vanishing implies `RiemannHypothesis` through the existing closure theorem. The outstanding displacement problem is to prove one of these upper bounds for the actual $d$ with no RH assumption.

Walfisz proved the full VK bound for the ordinary Mertens function. Its proof remains external to this Lean development. [Gerhold, *Acta Arithmetica* 142 (2010), equation (2)](https://doi.org/10.4064/aa142-2-8).

## Displacement criteria at the VK and $1/11$ scales

Write $Z=\zeta(2)$, $Q(n)=1/(Zn^2)$ for $n\ge1$, and $\Psi(x)=((6+\log x)\log(6+\log x))^{1/11}$. Define the two nonnegative series

$$J_c=\frac1Z\sum_{n\ge1}\frac{|d(n)|e^{-c\Phi(n)}}n,
\qquad K_a=\frac1Z\sum_{n\ge1}\frac{|d(n)|^2e^{-a\Psi(n)}}n.$$

The Lean sums run over the naturals. Their terms at zero vanish.

**Vinogradov–Korobov scale.** Assume $|M(x)|\le Cxe^{-a\Phi(x)}$ for all sufficiently large real $x$. For every fixed $0<c<a$, `residual_zero_iff_vk_displacement_absolute_moment` proves $r=0\iff J_c<\infty$ and `riemannHypothesis_of_vk_displacement_absolute_moment` gives $J_c<\infty\Rightarrow\mathrm{RH}$. In particular, for every $0<b<a$ and every constant $D$, an eventual bound $|d(n)|\le D e^{b\Phi(n)}$ implies RH. The pointwise argument chooses an intermediate moment exponent $b<c<a$. An eventual power saving $|M(x)|\le Cx^s$ with $C\ge 0$ and $s<1$ supplies the VK bound, with prefactor one, at every fixed $a>0$. See [MertensVKFirstMoment](RH/MertensVKFirstMoment.lean) and [MertensPowerToVK](RH/MertensPowerToVK.lean).

**Earlier unconditional $1/11$ scale.** The project's unconditional `M_stretched_loglog_bound` supplies a fixed $b>0$ such that $r=0$ if and only if there exists $D\in\mathbb R$ with $|d(n)|\le D e^{b\Psi(n)}$ for all sufficiently large $n$. The theorem `riemannHypothesis_of_stretched_log_displacement` gives $\log(2+|d(n)|)=o(\Psi(n))\Rightarrow\mathrm{RH}$. Establishing this bound for the actual displacement remains open. A separate theorem supplies a fixed $a>0$ such that $K_a<\infty\Rightarrow\mathrm{RH}$. Both coefficients are existential and precede the respective displacement test. The profile comparison used in these implications holds for $\Psi_\beta(x)=((6+\log x)\log(6+\log x))^\beta$: for each $0\le\beta<1/2$ and $A\ge0$, eventually in $x$ one has $A(\Psi_\beta(y)-\Psi_\beta(x))\le\log y-\log x$ for every $y\ge x$. See [MertensUnconditionalStretched](RH/MertensUnconditionalStretched.lean), [MertensStretchedWeightedMoment](RH/MertensStretchedWeightedMoment.lean), and [StretchedLogProductIncrement](Analysis/StretchedLogProductIncrement.lean).

**Explicit Lee–Leong scale.** Put $W=53.99$ and $A=(5/(3W^3))^{1/5}$. `LeeLeongMertensEstimate` is the following external premise for every real $x\ge\exp(\exp(10.01))$:

$$|M(x)|<25.85\,x\log x\,\exp\!\left[-A\left(1-\frac{\log W}{\log\log x}\right)^{-1/5}\Phi(x)\right].$$

From this input, `mertens_vk_of_leeLeong` retains the full leading coefficient in $|M(x)|\le x e^{-A\Phi(x)}$ eventually. Thus for every $0<c<A$, $r=0\iff J_c<\infty$ and $J_c<\infty\Rightarrow\mathrm{RH}$. For every $0<b<A$ and constant $D$, an eventual bound $|d(n)|\le D e^{b\Phi(n)}$ also implies RH. The first-moment statement here uses strict interior rates. See [MertensLeeLeongCriterion](RH/MertensLeeLeongCriterion.lean) and Lee–Leong, Theorem 1.1, [v5 PDF, (11)](https://arxiv.org/pdf/2208.06141v5) or [v5 HTML, (12)](https://arxiv.org/html/2208.06141v5).

**Pointwise endpoint.** [MertensEndpointEnvelope](RH/MertensEndpointEnvelope.lean) and [MertensEndpointPairing](RH/MertensEndpointPairing.lean) prove `riemannHypothesis_of_leeLeong_endpoint`. Under the same explicit arithmetic premise, an eventual bound $|d(n)|\le D\exp(A\Phi(n))$ suffices at the leading coefficient $A$ itself. The second-order term in the published estimate gives enough decay to retain a factor $\exp(-\sqrt{\Phi(n)}/8)$ in a common majorant for the finite-head errors. With the Lee–Leong input the residual vanishes if and only if the following endpoint series converges:
$$J_* = \sum_{n\ge3}\frac{|d(n)|}{n}\exp\left(-A\Phi(n)-\tfrac18\sqrt{\Phi(n)}\right).$$
Convergence implies RH. In particular $|d(n)|=O(\exp(A\Phi(n)+t\sqrt{\Phi(n)}))$ suffices for each fixed $t<1/8$. The proofs absorb the remaining factor $\exp(-(1/8-t)\sqrt{\Phi(n)})$ into $1/(\log n)^2$.

## Converse from the explicit squarefree approximants

[MertensBaezDuarteConverse](RH/MertensBaezDuarteConverse.lean) takes Báez-Duarte’s squared-error convergence under RH as an explicit input. Its finite coefficients are $-\mu(m)\exp(-c\log m/\log\log N)$. The Lean proof checks squarefree support, transfers the continuous approximation to the discrete Pareto norm and to the $Q$-norm, and deduces $r=d=0$ under RH. Together with the Lee–Leong estimate this proves the literal equivalences
$$\mathrm{RH}\iff J_c<\infty\quad(0<c<A),\qquad
\mathrm{RH}\iff\log(2+|d(n)|)=o(\Phi(n)).$$
The same two inputs yield $\mathrm{RH}\iff J_*<\infty$ in `riemannHypothesis_iff_leeLeong_endpoint_displacement_moment`. At the smaller scale $\Psi$ the reverse direction uses the same Báez-Duarte input, and the forward-to-RH proof uses only the repository’s arithmetic estimates. See [Báez-Duarte, Rend. Lincei 14 (2003), Theorem 2, formula (3.1)](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0) and [Bagchi, Remark 8](https://arxiv.org/pdf/math/0607733).

## Shifted tests

[MertensShiftedPairing](RH/MertensShiftedPairing.lean) proves the analytic continuation and boundary passage for the actual Schur witness. A family of holomorphic tests must have a locally summable majorant in the open domain, an absolutely summable squarefree expansion near one interior point, and a separate summable majorant along a sequence where the weighted tests converge coordinatewise to the witness charge. These hypotheses imply RH. [MertensShiftedMobiusSeed](RH/MertensShiftedMobiusSeed.lean) proves absolute summability of the Möbius atom coefficients and exact witness cancellation for their series throughout $\Re(s)>1$.

[MertensShiftedTest](NumberTheory/MertensShiftedTest.lean) defines the finite divisor test with the pole at one removed using Mathlib’s completed zeta factor. Each physical test is holomorphic for $\Re(s)>0$ and tends to one at $s=0$ for $n\ge1$.

[MertensShiftedFloorSum](NumberTheory/MertensShiftedFloorSum.lean) counts each divisor through its positive multiples. [MertensShiftedTestIdentity](RH/MertensShiftedTestIdentity.lean) identifies the finite test with its squarefree residue series throughout $\Re(s)>0$, using the absolutely convergent Dirichlet series for $1/\zeta(1+s)$. On $\Re(s)>1$ the actual witness pairs to zero with this finite test.

[MertensShiftedLocalMajorant](RH/MertensShiftedLocalMajorant.lean) gives $|H_s(n)|\le n^{1-\eta}\sum_{k\ge2}k^{-1-\eta}$ for $0<\eta<1$ and $\Re(s)\ge2\eta$. [MertensActualShiftedCriterion](RH/MertensActualShiftedCriterion.lean) supplies the concrete continuation step. The remaining hypotheses for `riemannHypothesis_of_actual_shifted_boundary` are the interior moments of the actual witness charge and one summable boundary dominator. A proof of the sharper uniform shifted Perron estimate and a proof of the required displacement growth would give further progress.

## Critical secondary Lee–Leong coefficient

Put $L(x)=\log\log x$, $S(x)=\Phi(x)/L(x)$, $A=(5/(3\cdot53.99^3))^{1/5}$,
$\kappa=A\log(53.99)/5$, and $U_t(x)=A\Phi(x)+\kappa S(x)+t\sqrt{\Phi(x)}$.
The term $\kappa S(x)$ comes from the linear term of the variable coefficient
in Lee–Leong, Theorem 1.1. Its positive quadratic remainder absorbs the
factor $25.85\log x$ and every fixed multiple of $\sqrt{\Phi(x)}$.

| Conditional research reduction | Hypotheses and conclusion |
|---|---|
| [Critical Mertens estimate](RH/MertensCriticalEstimate.lean) | `mertens_critical_sqrt_of_leeLeong` derives $\lvert M(x)\rvert\le x\exp(-U_t(x))$ eventually, for every fixed real $t$, from the explicit Lee–Leong estimate. |
| [Critical displacement moment](RH/MertensCriticalDisplacement.lean) | For each $s\ge0$, convergence of $\sum_{n\ge3}\lvert d(n)\rvert e^{-U_s(n)}/n$ implies RH. Under Báez-Duarte's explicit approximation theorem, RH also implies convergence. |
| Pointwise and exceptional-set forms | For every fixed real $t$, $\lvert d(n)\rvert=O(e^{U_t(n)})$ implies RH. For fixed $s\ge0$ with $s>t$, the same bound may be restricted to $n\notin E$ if $\sum_{n\in E}e^{-2U_s(n)}<\infty$. The proof uses the complete $Q$-energy of $d$ on the exceptional sites. |

The [finite envelope](RH/MertensCriticalEnvelope.lean) controls the variation
between the cutoff and the physical site. The [pairing theorem](RH/MertensExponentialCutoffPairing.lean)
uses the existing signed identity along legal squarefree heads.
**Open in Lean** — providing the Lee–Leong estimate from its published proof,
and Báez-Duarte's approximation for the reverse implication.
**Open displacement obligation** — prove one of these bounds for the actual
projection displacement independently of RH. The generic convergence lemmas
assume neither of the two external analytic inputs.

## Full variable-coefficient exponent

Write $r_0=\log(53.99)$ and $F(x)=A(1-r_0/L(x))^{-1/5}\Phi(x)$ for sufficiently large $x$. This is the full exponent in Lee–Leong's estimate. Their prefactor is $25.85x\log x$. For each fixed $\delta>0$, put $H_\delta(x)=F(x)-\delta\sqrt{\Phi(x)}$.

| Conditional research reduction | Hypotheses and conclusion |
|---|---|
| [Uniform arithmetic bound](RH/MertensFullProfile.lean) | $F-\delta\sqrt{\Phi}$ is eventually increasing. The printed estimate implies $\lvert M(x)\rvert\le x e^{-H_\delta(x)}$ eventually. |
| [Finite Möbius envelope](RH/MertensFullEnvelope.lean) | In a window close to the cutoff, variation in $F$ costs $O(\Phi^2/\log x)$ in the exponent, and the harmonic factor costs $O(\log\log x)$. Each is $o(\sqrt\Phi)$. The physical bound is uniform over all sufficiently large cutoffs and all sites. |
| [Full-profile first moment and pointwise criterion](RH/MertensFullDisplacement.lean) | `riemannHypothesis_iff_leeLeong_full_moment` gives $\mathrm{RH}\iff\sum_{n\ge3}\lvert d(n)\rvert e^{-H_\delta(n)}/n<\infty$ under the two stated literature inputs. `riemannHypothesis_of_leeLeong_full_displacement` needs only the Lee–Leong input and $\lvert d(n)\rvert=O(e^{H_\delta(n)})$. |
| Exceptional sites | Fix $0<\eta<\delta$. The growth bound with margin $\delta$ need only hold outside $E$ if $\sum_{n\in E}e^{-2H_\eta(n)}<\infty$. |

**Open displacement obligation** — establish a convergent moment, or a sufficient bound, for the actual $d$ without assuming RH. This theorem uses the printed Theorem 1.1 as its arithmetic input. The implicit truncation result below uses the stronger intermediate estimate in Proposition 5.2.

## A sign-count criterion using the repository's arithmetic estimates

For $\varepsilon\in\{-1,1\}$, let $N_\varepsilon(X)$ count the positive integers $n\le X$ with $\varepsilon d(n)>0$. The zero coordinate contributes nothing. [QDisplacementSignCounts](RH/QDisplacementSignCounts.lean) proves
$$
\left(\sum_{1\le n\le X}\frac{(\varepsilon d(n))_+}{n}\right)^2
\le N_\varepsilon(X)\sum_{n\ge1}\frac{|d(n)|^2}{n^2}.
$$
The complete sum on the right is finite. For fixed $B,C\ge0$, if arbitrarily large $X$ have $\min(N_+(X),N_-(X))\le C(\log X)^B$, then RH follows by the cofinal harmonic-prefix theorem. The sign may vary with $X$. **Open** — proving that count bound for the actual displacement. This implication requires neither external analytic premise.


## Finite Gram tests and the implicit truncation

**Conditional research reduction with internal arithmetic.** Set the stage to $2k^4$, so that all squarefree conductors through $2k^4+1$ enter the two Gram systems. At their exact displacement take the smaller of the two signed positive harmonic masses over $n\le k^8$. A bound of $C(\log k)^E$ on arbitrarily large $k$, for fixed nonnegative $C,E$, implies RH. **Open:** prove that bound. The exact finite prime and Möbius tests avoid a convergence-rate assumption. [Proof and scope](RH/FiniteGramDisplacementResearch20261105.md) · [Lean declaration](RH/QFiniteHarmonicProbe.lean) · [Finite computations](RH/FiniteGramDisplacementExperiment20261105.md)

| Result | Declaration or file |
|---|---|
| The limiting residual vanishes exactly when arbitrarily large heads admit one matched finite stage beyond the head passing a fixed unit harmonic budget. Grid and iterated polylog tests are also sufficient. | [QFiniteHarmonicPrefix](RH/QFiniteHarmonicPrefix.lean) |
| Signed harmonic mass identity, prefix stability, and the uniform allowance $\sqrt{61\zeta(2)/7200}$ for the centered iteration when $X\le 9^j$. | [QResolventHarmonicPrefix](RH/QResolventHarmonicPrefix.lean) |
| On the squarefree closure the quadratic residual polynomial $(18R^2-I)/17$ gives an exact signed remainder and norm factor $1/17$ per two-step cycle. | [QDisplacementChebyshevResolvent](RH/QDisplacementChebyshevResolvent.lean) |
| A projected finite head of the Pareto residual has vanishing harmonic error on windows $(N+2)^2$. The infinite projector and actual source enter this construction. | [QDisplacementProjectedHead](RH/QDisplacementProjectedHead.lean) |
| Four legal atoms give opposite plateaux and $h(s_p;5p)\ge1/5$, with $\zeta(2)\|s_p\|_Q^2\le1/(p-1)$. Exact block equalities apply to the actual residual and witness. | [SquarefreeHarmonicPulse](RH/SquarefreeHarmonicPulse.lean) · [SquarefreePulseEquations](RH/SquarefreePulseEquations.lean) |
| For bounded legal tests supported above physical cutoff $N$, the pairing with $d$ is $o(N^{-3/2})$. The finite-horizon inequality retains the norm of the actual Pareto residual tail. | [QDisplacementTailTests](RH/QDisplacementTailTests.lean) |
| **Paper counterexample.** Within the closed squarefree span, $h(v;X)\asymp\sqrt X/(\log X)^\beta$ for all large $X$ is attainable for every $\beta>1/2$ and impossible for $\beta=1/2$. | [Construction and sharpness proof](RH/SquarefreeHarmonicObstruction20261105.md) |

**Conditional research reduction with a literature input.** Lee–Leong Proposition 5.2 with its implicit optimized truncation supplies a reserve beyond the printed exponent $F$. The formal transfer accepts every fixed real $s$ in $|d(n)|=O(\exp(F(n)+s\sqrt{\Phi(n)}))$. It also accepts an eventual polynomial bound on the weighted dyadic masses at any fixed signed square-root margin. A finite signed-kernel maximum recovers each block mass exactly. **Open in Lean:** a provider of the specialized published input. **Open for the RH argument:** a growth or moment bound on the actual displacement. The complete asymptotic expansion and stronger logarithmic-scale consequence in the associated note are paper deductions. [Implicit cutoff](RH/MertensImplicitTruncation.lean) · [Reserve transfer](RH/MertensTruncationReserve.lean) · [Signed dyadic blocks](RH/MertensDyadicDisplacement.lean) · [Literature derivation](RH/MertensImplicitTruncationResearch20261105.md)


**Single-probe reduction and sign obstruction.** With $a_p=\langle g_p,1-f_{P,p}\rangle_Q$ and squarefree conductors through $p+1$, the scaled entry $\zeta(2)p a_p$ tends along primes to the squared limiting Pareto residual norm. **Open:** show $p a_p\to0$ along a cofinal subsequence. The finite norm comparison transfers Burnol’s positive logarithmic lower bound into eventual positivity of the individual entries. The transfer of Burnol from his continuous family to this dictionary is a paper proof. [Finite identity, limit, and positivity comparison](RH/QFiniteSingleResidueTest.lean) · [Paper proof with the matched cutoff](RH/SingleResidueBurnolResearch20261105.md)

## The first projected correction and harmonic resolvent errors

In the notation of the [research note](HarmonicResolventAndFullMoment20261105.md), let $b=\Pi Br_Q$, $b_M=\Pi_M B r_M$, $u_1=4b/3$, and $h$ be the smaller signed harmonic prefix.

| Declaration | Conclusion |
|---|---|
| `QSquarefreeDisplacementResolvent.resolvent_error_weighted_energy` | $4\sum_{k<N}9^k\|d-u_k\|^2\le\|r_Q\|^2$ for every $N$. |
| `QSquarefreeDisplacementRigidity.harmonic_resolvent_sqrt_depth` | The prefix error at depth $j$ is at most $\sqrt{\zeta(2)X}\,3^{-j}\|r_Q\|/(2\sqrt{j+1})$. |
| `QSquarefreeDisplacementRigidity.harmonic_resolvent_adaptive_div_sqrt_tendsto_zero` | $h(u_{j(X)};X)=o(\sqrt X)$ if $X\le9^{j(X)}$. |
| `QFixedHarmonic.residual_zero_iff_fixed_firstStep_cofinal_polylog` | For fixed $C,B_1\ge0$, residual zero iff $h(u_1;X)\le C(\log X)^{B_1}$ at cofinal cutoffs. |
| `QFixedHarmonic.residual_zero_iff_cofinal_moving_harmonic_one` | Residual zero iff arbitrarily large physical cutoffs admit arbitrarily large finite stages with $h(b_M;X)\le1$. |
| `QMertensFirstMoment.residual_zero_iff_cofinal_full_moving_moment` | Under the Lee–Leong input, residual zero iff a single constant bounds the full-weight finite moments of $b_M$ at arbitrarily large stages for each fixed physical head. |
| `QMertensFirstMoment.riemannHypothesis_of_first_resolvent_full_moment` | Under the Lee–Leong input the weighted absolute moment of $u_1$ implies RH. |
| `QMertensFirstMoment.leeLeong_full_moment_iff_resolvent_shells` | Full displacement moment summability equals summability of the moments of $u_j$ on the dyadic shells, independent of the arithmetic premise. |

**Conditional research reductions.** Open — supply a cofinal one-sided estimate for the actual first correction, or the uniform finite weighted moment. Open in Lean — supply `LeeLeongMertensEstimate` for the full-weight forward implication. The harmonic forward implication uses the repository's established arithmetic. The RH-to-residual-zero converse in the equivalence with RH uses `BaezDuarteMobiusApproximation`. The accompanying numerical certificates give finite values and an upper bound for the residual norm.

## A translated full Lee–Leong moment

Let $F$ be the full printed exponent and $G(x)=(\log x)^2\exp[-F(\exp(\log x-F(x)))]$. The full logarithmic prefactor in Lee–Leong's estimate is retained.

| Declaration in `QMertensFirstMoment` | Conclusion |
|---|---|
| `errorEnvelope_eventually_le_leeLeongDelayed` | Uniform Möbius defect envelope at relative error $25.85\log N\,e^{-F(N)}$ is at most $2+400nG(n)$ for all sufficiently large cutoffs and every site. |
| `summable_leeLeongDelayedDamping_Q` | The scalar moment of $G$ is finite. |
| `leeLeongDelayedDamping_eventually_le_explicit` and `leeLeongDelayedDamping_le_full_margin` | A loss bounded by $(2A)^2\Phi(x)^2/\log x+2\log\log x$ suffices. Each earlier fixed positive square-root margin dominates the translated damping. |
| `residual_zero_iff_cofinal_delayed_heads` | With the Lee–Leong premise, a uniform constant for finite translated first-correction moments on cofinal conductor stages for each physical cutoff is equivalent to $r_Q=0$. |
| `riemannHypothesis_of_delayed_displacement_moment` | The translated absolute moment of the actual displacement suffices for RH under the same arithmetic input. |

**Conditional research reductions.** Open — bound the translated moment of the actual correction or displacement. Open in Lean — supply the published arithmetic input as a checked provider. The exact coefficient $3/5$ in the upper bound is proved by `leeLeongDelayedDamping_eventually_sharp_log_reserve`. Optimality for the raw uniform envelope is a paper deduction in the [research note](HarmonicResolventAndFullMoment20261105.md).

The new first-correction result `residual_zero_iff_cofinal_implicit_correction_heads` uses the stronger Proposition 5.2 specialization from the preceding section. At any fixed real $s$, its test uses the mass $|b(n)|e^{-F(n)-s\sqrt{\Phi(n)}}/n$, including the exact printed exponent when $s=0$. Open — prove the uniform finite-moment budget or provide a checked analytic input where required.
