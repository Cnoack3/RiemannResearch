# From the prime weights to the GUE bulk kernel

The input is the finite von Mangoldt probe from Compact Orbit. Its phases use logarithmic frequencies, and its sum includes prime powers. Ordinary positive-gap PCC is the assertion about the physical ordinates of zeta, counting occurrences with multiplicity and taking strictly positive gaps.

## The two kernels and the phase

Put $h=x-y$, $k(h)=\operatorname{sinc}(\pi h)$, with $k(0)=1$, and for $T>1$ set

$$
\lambda_n=\frac{\log n}{\log T},\qquad
w_n=\frac{\Lambda(n)}{n\log T},\qquad
\Phi_T(h)=\sum_{0<n\le T} w_n e^{2\pi i h\lambda_n},\qquad
m_T=\Phi_T(0).
$$

The continuum Fourier transform of the uniform distribution on $[0,1]$ is $e^{\pi i h}k(h)$. Lean proves $m_T\to1$ and the explicit bound

$$
\left|e^{-\pi i h}\Phi_T(h)-k(h)\right|
\le \frac{\log 4+4}{\log T}(1+2\pi |h|).
$$

Thus the centered prime kernel converges uniformly on bounded differences. More generally the error tends to zero along any moving differences $|h_T|=o(\log T)$, and the kernel tends to zero if also $|h_T|\to\infty$. Dividing by $m_T$ calibrates its diagonal to one when $m_T>0$, in particular for $T\ge 2$. Every fixed-size determinant of the unnormalized prime matrix converges to the corresponding sine determinant. The finite matrix is positive semidefinite. On the full real line an atom of mass $w>0$ gives a test function on $[0,B]$ with Rayleigh quotient at least $wB$. Taking $B=2/w$ violates the contraction condition for a Lebesgue DPP.

The auxiliary residue–Mellin kernel uses the opposite sign in its logarithmic phase. At center $t_0$, write $t(x)=t_0+2\pi x/\log(N+1)$. Its unfolded kernel and $e^{-2\pi i h}\Phi_T(h)$ approach the same $e^{-\pi i h}k(h)$ at fixed $t_0,x,y$. The finite comparison bound retains the center dependence. Both cutoffs can grow independently. Reduced Palm kernels at the origin converge as well, with every fixed determinant tending to the determinant of $k(x-y)-k(x)k(y)$.

Lean declarations include `centeredPrimeProbeKernel_error`, `centeredPrimeProbeKernel_moving_sub_sine`, `primeProbeKernel_det_tendsto`, `normalized_centeredPrimeProbeKernel_tendsto`, `exists_primeProbeRayleigh_exceeds_one`, `unfoldedResidueKernel_sub_orientedPrimeKernel_bound`, and `orientedPrimeKernel_palm_det_tendsto`.

## Two points and the physical PCC test

The two-by-two determinant is exactly

$$
d_T(h)=m_T^2-|\Phi_T(h)|^2
=\sum_{m,n} w_m w_n \bigl[1-\cos(2\pi h(\lambda_m-\lambda_n))\bigr]\ge0.
$$

The limiting bulk determinant is $1-k(h)^2$. Conditioning the limiting process at the origin and deleting that point gives the two-point reduced Palm determinant $1-a^2-b^2-c^2+2abc$, where $a=k(x)$, $b=k(y)$, $c=k(x-y)$. Wolfram independently evaluated the determinants and the continuum Fourier transform. The probe square itself is the Fourier transform of the weighted measure on literal log-frequency differences. Its normalized limit equals the transform of the triangular density $(1-|s|)_+$, namely $k(h)^2$. Consecutive unscaled prime log ratios have a further, distinct, degeneracy.

For a positive rational $q$ let $P_T(q)$ be the repository's normalized count of actual positive zero gaps up to width $q$. The integrated finite determinant is $q m_T^2-B_T(q)$ with $B_T(q)=\int_0^q |\Phi_T(h)|^2\,dh$. Lean proves

$$
\mathrm{PositiveGapPCC}\quad\Longleftrightarrow\quad
\forall q\in\mathbb Q_{>0},\quad
P_T(q)-\frac{1}{m_T^2}\int_0^q d_T(h)\,dh \longrightarrow 0.
$$

The arithmetic integral on the right tends unconditionally to $\int_0^q(1-k(h)^2)\,dh$. Identifying it with the physical zero statistic is the unsolved step. These assertions are `primePairDeterminant_eq_sum`, `normalizedPrimeLogPairTransform_tendsto_tent`, `integral_primePairDeterminant`, and `positiveGapPCC_iff_normalized_primePairMass`.

## The legal Pareto spaces

For the legal full-divisor trial space at $L=\operatorname{lcm}(1,\ldots,M)$, its rank $r_L$ is at most $\tau(L)$. A rank-$r$ orthonormal projection has total integrated two-point determinant $r(r-1)$. Moreover, any selection of ordered pairs among $r_L$ labeled points has at most $r_L^2$ pairs. If $T_M\to\infty$ and $L\le T_M^k$ eventually for any fixed positive integer $k$, both bounds divided by $D_{T_M}=T_M\log(T_M)/(2\pi)$ tend to zero. The sine gap mass is positive for every $q>0$. This rules out the proposed direct global pair transfer at those matched periods and heights. It leaves open the local behavior at other centers and scales.

For the inverse-Gram legal kernel let $Z(t)=\zeta(1/2+it)/(1/2+it)$ and write $A_n$ for the kernel core. Its actual two-by-two determinant at $t,u$ is
$$
|Z(t)|^2 |Z(u)|^2\bigl[A_n(t,t) A_n(u,u)-|A_n(t,u)|^2\bigr].
$$
The finite legal Mellin features vanish at a critical-line zeta zero. Lean factors their inverse-Gram kernel determinants by the zeta envelopes and proves exact zero rows at those ordinates. A unit-modulus phase preserves this vanishing. If scaled sampled critical zeros tend to a nonzero offset, local uniform convergence there to the reduced sine diagonal is impossible because $1-k(x)^2>0$ at every such offset.

Lean declarations include `total_pair_det_integral`, `lcm_divisorTrial_not_sine_gap_mass`, `lcm_divisorTrial_total_pair_det_tendsto_zero`, `kernel_two_point_det_factorization`, `kernel_sample_det_factorization`, and `not_locallyUniform_palm_at_sampled_criticalZeros`.

## Absolute precision and the Hilbert–Pólya question

At height $T$, let $N_T$ count occurrence labels, and let $C_T$ count ordered pairs with identical ordinate, including the diagonal. Reflecting a nontrivial off-line zero across the critical line produces a second zero of the same ordinate. A multiple zero also produces two distinct occurrence labels there. Either gives $C_T-N_T\ge2$ at every sufficiently large height. Adjoining one extra copy of an existing bounded ordinate in an abstract labeled configuration eventually preserves every bounded strictly-positive unfolded-gap test, while it increases $C_T-N_T$ by twice that ordinate's multiplicity. The normalized contribution of that change tends to zero.

For bandwidth $R\ge1$ and the actual normalized Fejér form factor $F_T(R)$ put

$$
\Delta_T(R)=D_T F_T(R)-N_T-\frac{D_T}{3R^2}.
$$

Lean proves the exact decomposition of $\Delta_T(R)$ into $C_T-N_T$, a nonnegative contribution from unequal ordinates, and $-D_T/(3R^2)$. If $R(T)\ge1$ eventually, $\Delta_T(R(T))\to c$, $D_T/R(T)^2\to\kappa$, and $c+\kappa/3<2$, then RH holds and every nontrivial zero has multiplicity one. For $c=0$ the permitted range is $\kappa<6$. The missing input is an absolute estimate on the actual Fejér energy. Bulk determinant convergence by itself loses the two-label signal. A Hilbert–Pólya approach would additionally need an exact spectral correspondence with all nontrivial zeros and multiplicities. Neither finite kernel supplied here establishes that correspondence.

There is also an exact equivalence when the bandwidth is free. Given any lower bandwidth schedule $B(T)$, global RH with simple zeros is equivalent to the existence of $R(T)\ge\max(1,B(T))$ for which both $\Delta_T(R(T))$ and $D_T/R(T)^2$ tend to zero. At fixed height, the limit as $R\to\infty$ of $\Delta_T(R)$ is exactly $C_T-N_T$. Constructing a bandwidth under the assumption of global simplicity and RH proves the forward implication. Establishing the estimates independently for physical zeros is the open direction.

The related declarations are `eventually_adjoin_actualPositiveTest_eq`, `extra_excess_invisible_after_normalization`, `fejerSineRampDiscrepancy_eq`, `global_of_fejerSineRamp_limits`, and `global_iff_exists_fejerSineRamp_schedule`.

## Sources

- [Compact Orbit, signed prime–zero calculation](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/proofs/signed-prime-zero.html) and [three-prime gap tests](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/current-proofs.html#three-prime-gap-tests), published version 47, source revision `b79a2e68c5be3ed2fd19b3d04d9b03d7098a2969`.
- [Mellin sine kernels, prime words, and the collision criterion](THEOREM_CATALOG_MELLIN_PRIME_ORBIT_TRANSFER.md) gives the earlier unconditional model limits and the exact global criterion.
