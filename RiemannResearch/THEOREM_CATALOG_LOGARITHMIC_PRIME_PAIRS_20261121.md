# Logarithmic-shift prime pairs

## Established Lean results

Write \(H=\lfloor d\log X\rfloor\), \(C_X(h)=\sum_{AX<n\le BX}\Lambda(n)\Lambda(n+h)\), and \(\mathfrak S(h)\) for the binary Hardy–Littlewood singular series in `AnnularPrimePairTargets`. The sharp statistic is \(F_X(d)=\sum_{1\le h\le H}C_X(h)/(X\log X)\).

* `AnnularPrimePair.sum_singularSeries_le` and `AnnularPrimePair.tendsto_singularSeries_mean` prove \(\sum_{1\le h\le H}\mathfrak S(h)\le H\) and convergence of its Cesàro mean to one. The proof expands the Euler factors over subsets of odd primes and counts multiples of each squarefree modulus. [Van de Bult and Korevaar, Proposition 4.1](https://arxiv.org/abs/0806.1667)
* `LogarithmicPrimePairs.pair_total_exact` splits the numerator into \((B-A)X\sum_h\mathfrak S(h)\), the signed even-shift residual, and the actual odd-shift mass. `tendsto_log_singularSeries` gives the normalized model limit, and `tendsto_oddMass_div` gives zero for the normalized odd mass, including powers of two.
* `LogarithmicPrimePairs.triangle_increment` gives the exact increment of the triangularly weighted statistic, including every newly admitted shift. `triangle_increment_bounds` puts its secant between the two sharp endpoint statistics.
* `LogarithmicPrimePairs.smallGapStarts_le_sharp` bounds the dyadic statistic below by \(\log X/X\) times the number of primes \(X<p\le 2X\) whose next prime lies within \(d\log X\). `eventually_lower_of_smallGapCount` transports a lower bound for that count. The counting input is available in the literature for sufficiently small fixed positive widths. Monotonicity then gives a positive lower bound at each fixed positive width. [Goldston, Pintz and Yıldırım, Theorem 1](https://doi.org/10.4064/aa160-1-3)

## Conditional research reductions

For \(0<A<B\) and \(d>0\), `sharpPairAverage_iff_evenResidual` proves that \(F_X(d)\to(B-A)d\) is equivalent to the first open condition below. The two subsequent conditions give alternative sufficient inputs.

| Status | Arithmetic input | Declaration |
| --- | --- | --- |
| Open | The signed sum over even \(h\le H\) of \(C_X(h)-(B-A)X\mathfrak S(h)\) is \(o(X\log X)\). | `sharpPairAverage_iff_evenResidual` |
| Open | Uniformly over positive even \(h\le H\), the absolute error is at most \(e(X)X\mathfrak S(h)\) for some \(e(X)\to0\). | `sharpPairAverage_of_uniform_even` |
| Open | At every fixed \(u>0\), \(\sum_{1\le h\le u\log X}(u-h/\log X)C_X(h)/(X\log X)\to (B-A)u^2/2\). | `sharpPairAverage_of_triangle` |

Gallagher's Poisson theorem assumes uniform prime-tuple estimates. Theorem 1.3(i) of Matomäki, Radziwiłł and Tao covers a power-sized range of shifts starting at \(X^{8/33+\varepsilon}\). The logarithmic even-shift estimate remains an arithmetic obligation. [Gallagher](https://doi.org/10.1112/S0025579300016442) · [Matomäki, Radziwiłł and Tao](https://arxiv.org/abs/1707.01315)

## Fractional Fejér energy and actual pairs

Write \(L=\log X\), \(s=uL\), \(H=\lfloor s\rfloor\), \(\delta=s-H\), \(I=(AX,BX]\cap\mathbb N\) and \(D_j(\alpha)=\sum_{0\le k<j}e^{2\pi i k\alpha}\). On the circle with probability Haar measure define
\[
K_s=(1-\delta)|D_H|^2+\delta |D_{H+1}|^2,\qquad
J_X(u)=\frac{1}{XL^2}\int K_s(\alpha)
 \left|\sum_{n\in I}(\Lambda(n)-1)e^{2\pi i n\alpha}\right|^2\,d\alpha .
\]
Here \(T_X(u)=(XL)^{-1}\sum_{1\le h\le H}(u-h/L)C_X(h)\).

| Proved statement | Lean declaration |
| --- | --- |
| The kernel has Fourier weights \((s-|h|)_+\), value \(s^2+\delta(1-\delta)\) at zero, and an exact energy identity for arbitrary finite real weights. | `FractionalFejer.integral_kernel_signed`, `kernel_at_zero`, `energy_eq` |
| For the actual Mangoldt sum the uncentered integral equals \(2XL^2T_X+s\sum_{n\in I}\Lambda(n)^2-2E_X\), where \(E_X\) includes the pairs crossing \(BX\). The centered expansion counts both clipped endpoints. Their weighted count is bounded using \(\sum_{h=1}^H h(s-h)=H(H+1)(H-1+3\delta)/6\). | `triangle_fejer_exact`, `centered_fejer_exact`, `fejer_endpoint_bounds`, `edge_weight_sum` |
| The endpoint errors vanish on division by \(XL^2\), and \(\sum_{n\in I}\Lambda(n)^2/(XL)\to B-A\). Thus \(J_X(u)-2T_X(u)\to(B-A)(u-u^2)\). | `annular_diagonal_limit`, `centered_energy_sub_triangle_limit` |
| The corresponding uncentered target is \((B-A)(u^2+u)\). At each fixed \(u>0\), the quadratic law for \(T_X(u)\) is equivalent to \(J_X(u)\to (B-A)u\). Having this last limit at all positive widths implies the sharp law. Positivity gives \(\liminf T_X(u)\ge(B-A)(u^2-u)/2\). | `triangle_iff_uncentered_energy`, `triangle_iff_centered_energy`, `sharpPairAverage_of_centered_energy`, `eventually_triangle_gt_of_centered_nonneg` |
| Only \(O_{A,B}(1)\) powers of two can occur in each translated fixed-ratio annulus. The entire normalized odd-shift contribution is \(O_{A,B,d}(L/X)\). | `odd_pair_annular_bound`, `oddMass_annular_rate` |
| The entire contribution to \(F_X(d)\) with at least one proper prime power is \(O_{B,d}(L/\sqrt X)\). This includes both possible positions and uses the proved Chebyshev bound for \(\psi-\theta\). | `properPower_sharp_rate` |

### Published estimates used provisionally

* Vaughan's estimate applies at sufficiently large real widths \(s\). With \(\beta=1-\gamma-\log(2\pi)\), the normalized triangular singular-series model equals
  \[
  (B-A)\left(\frac{u^2}{2}+\frac{u(\beta-\log u-\log L)}{2L}\right)
  +O_{A,B}\left(\frac{\sqrt{uL}}{L^2}
      \exp\!\left[-c\frac{(\log(2uL))^{3/5}}{(\log\log(3uL))^{1/5}}\right]\right).
  \]
  `triangle_model_exact` retains the signed difference between the actual pairs and their singular-series model. `vaughan_logarithmic_triangle` takes `VaughanCesaroBound` as a hypothesis. [Vaughan](https://doi.org/10.1112/plms/82.3.533) · [Goldston and Suriajaya, equations (1.3)–(1.4)](https://arxiv.org/abs/2007.16099)
* Goldston, Pintz and Yıldırım bound the number of positive prime pairs of gap at most \(H\) on a dyadic interval by \(O(HX/\log^2 X)\) in the applicable logarithmic range. Covering a fixed annulus takes finitely many such intervals. Pairs crossing an interval boundary add \(O(H^2)\) per boundary, and each pair has weight \(O(L^2)\). `GPYPrimePairSieve` records this fixed-annulus prime-only consequence as a hypothesis. `eventually_sharp_le_width_of_sieve` gives one constant depending only on the annulus such that \(F_X(u)\le C_{A,B}u\) eventually for every fixed \(u>0\). The threshold in \(X\) may depend on \(u\). [Goldston, Pintz and Yıldırım, equations (5.3)–(5.5)](https://doi.org/10.4064/aa160-1-3)

### What the two sampling calculations recover

For \(P_X=\{p\text{ prime}: p\le \lfloor BX\rfloor+H\}\), attach the character with exponent \(v_p(n+h)-v_p(n)\) at \(p\) to each pair. On the multiplicative orbit it has frequency \(\log((n+h)/n)\). `pairTorusPolynomial` is the continuous function on this prime torus with the actual triangular Mangoldt coefficients. Its Haar integral is zero, and `pairTorusPolynomial_sample` identifies its zero-ordinate sampling with the rational-mode sum at every height. When \(X\) is sufficiently large, \(1<(n+h)/n<2\) throughout the sum, so its Landau main term is also zero. Evaluation at the identity recovers \(T_X(u)\).

The sum of absolute coefficients times squared rational-mode weights is \(O_{B,u}(L^3)\) using the PNT, and \(O_{A,B,u}(L^2)\) under `GPYPrimePairSieve`. `eventually_sampled_pairs_le_mass` bounds the sampled observable by this mass times \(O((\log\log T)^2/\log T)\). In particular `tendsto_sampled_pairs_exp` gives zero at \(T=\exp X\). Under the same sieve input, `tendsto_sampled_pairs_logPower_of_sieve` gives convergence to zero at the smaller height \(T=\exp(L^{2+\varepsilon})\) for every fixed \(\varepsilon>0\). Here the remaining factor is \((2+\varepsilon)^2(\log L)^2/L^\varepsilon\). `tendsto_fixed_triple_test_of_gap` gives the fixed-window conditional conclusion under `VanishingCutoffGapEnergy`. For prime gaps, rank one and rank two leave all higher ranks in the sharp pair count. [Ford, Meng and Zaharescu](https://arxiv.org/abs/1511.06814)

On \(N=\lfloor BX\rfloor+H+1\) integer sites with counting measure, deleting one uniformly chosen site gives the projection \(I-\mathbf1\mathbf1^*/N\). For two distinct sites its determinant and pair-inclusion probability are \(1-2/N\). Thus the exact difference of the full triangle and the projected expectation is \(2T_X(u)/N\), which goes to zero. The projected expectation still contains \(T_X(u)\). See `deletionEntry_idempotent`, `uniform_deletion_inclusion`, `triangle_sub_deletionExpected` and `tendsto_deletion_vacancy`.

The unresolved normalized error is
\[
 \frac{1}{XL}\sum_{\substack{1\le h\le\lfloor dL\rfloor\\2\mid h}}
       [C_X(h)-(B-A)X\,\mathfrak S(h)].
\]
Proving that this tends to zero for each \(d>0\) would give the sharp asymptotic. Both literature estimates above leave this arithmetic cancellation open.

## Additive Fourier localization

Set \(S_X(\alpha)=\sum_{n\in I}(\Lambda(n)-1)e^{2\pi i n\alpha}\),
\(D_X=\sum_{n\in I}(\Lambda(n)-1)^2\), and
\(U_\rho=\{\alpha:|1-e^{2\pi i\alpha}|<\rho\}\).
Write \(J_X(u;E)=(XL^2)^{-1}\int_E K_{uL}|S_X|^2\,d\alpha\).
All these integrals use probability Haar measure on the additive circle.

| Status | Statement | Lean declaration |
| --- | --- | --- |
| Proved | \(D_X/(XL)\to B-A\). For \(0<\rho\), the exterior contribution satisfies \(0\le J_X(u;U_\rho^c)\le 4D_X/(\rho^2XL^2)\) for \(X>1\). This tends to zero if \(\rho^2L\to\infty\). | `annular_centered_diagonal_limit`, `FractionalFejer.offArc_energy_le`, `tendsto_centered_offArc` |
| Proved finite identity | For \(z=e^{2\pi i\alpha}\), \(\lvert1-z\rvert^2\sum_{j<m}\lvert D_j(\alpha)\rvert^2=2m-2\operatorname{Re} D_m(\alpha)\). Where \(m\lvert1-z\rvert\ge4\), this bounds \(mK_s\) above by \(4\sum_{j<m}\lvert D_j\rvert^2\), uniformly in \(s\ge0\). | `chord_sq_mul_sum_dirichlet_sq`, `kernel_le_dirichlet_average`, `offArc_energy_le_short_energies` |
| Proved implication | If \(F_X(1)\) is eventually bounded, there is a single \(C_{A,B}\) with \(J_X(u;U_\rho^c)\le C_{A,B}/(\rho L)\) for all sufficiently large \(X\), all \(0<\rho\le1\) with \(\rho L\ge5\), and every \(u>0\). The threshold in \(X\) is independent of \(\rho,u\). | `eventually_centered_offArc_le_of_sharp_bound` |
| Published input | The existing prime-only hypothesis `GPYPrimePairSieve` provides the required upper bound at width 1. Consequently every positive \(\rho\le1\) with \(\rho L\to\infty\) has negligible exterior energy. The sieve enters as a parameter to the Lean corollary. | `tendsto_centered_offArc_of_sieve` |

The proof of the sharper bound uses the exact Fejér expansion at the shorter integer widths \(j\le\lfloor L\rfloor\). Since \((\Lambda(n)-1)(\Lambda(n+h)-1)\le\Lambda(n)\Lambda(n+h)+1\), the single upper bound on \(F_X(1)\) gives \(E_j\ll_{A,B}jXL\). Take \(m=\lceil4/\rho\rceil\) in the finite identity. Equation (5.5) in the published paper is the upper sieve used here. [Goldston, Pintz and Yıldırım, *Primes in tuples IV*, p. 49](https://doi.org/10.4064/aa160-1-3)

### Conditional research reduction

Choose \(0<\rho_X\le1\) with \(\rho_XL\to\infty\), for instance \(\rho_X=(\log L)/L\) for large \(X\). Define the localized cosine moments
\[
 b_X(h)=\frac1X\int_{U_{\rho_X}}\cos(2\pi h\alpha)
                 (|S_X(\alpha)|^2-D_X)\,d\alpha .
\]

**Open arithmetic estimate.** For each fixed \(v>0\),
\(\max_{0\le h\le\lfloor vL\rfloor}|b_X(h)|\to0\).
These moments use ordinary cosine probes, include \(h=0\), and contain no Fejér kernel.
The exact cosine expansion has nonnegative weights summing to \(K_{uL}(0)\). Thus if the maximum at width \(u\) is \(e\), the absolute normalized local signed Fejér error is at most \((u^2+1)e\) for \(L\ge1\). With the published upper sieve this gives the centered, triangular, and sharp laws. See `integral_kernel_mul_eq_cosineMoments`, `abs_integral_kernel_mul_le_modes`, `abs_localCovariance_le_modes`, and `sharpPairAverage_of_localModes`. For the coarser radii \(\rho_X^2L\to\infty\), `centered_energy_of_localCovariance_plancherel` needs only the local signed error at the chosen width. No global axiom was added.

### An interval-mass criterion on paper

An alternative sufficient arithmetic estimate uses ordinary intervals. Represent the circle by \([-1/2,1/2)\). Suppose that for every fixed positive rational \(R\),
\[
 \frac1X\int_{-R/L}^{R/L}|S_X(\alpha)|^2\,d\alpha \ \longrightarrow\ 2(B-A)R .
\]
The integral is taken for \(L>2R\). Push the measure \(X^{-1}|S_X(\alpha)|^2\,d\alpha\) forward by \(t=L|\alpha|\). Differences of these cumulative masses give convergence on intervals with rational endpoints. Positivity and approximation by step functions give convergence against continuous tests on each fixed compact interval to \(2(B-A)\,dt\).

On \(0\le t\le R\), \(L^{-2}K_{uL}(t/L)\) converges uniformly to \((\sin(\pi ut)/(\pi t))^2\), with value \(u^2\) at zero. This follows from the geometric sum for \(D_j\) and uniform convergence of \(\sin(\pi t/L)/(\pi t/L)\) to one there. The bounded masses on that interval permit using the moving kernel. On \(|\alpha|>R/L\), the chord is at least \(4R/L\). The single-width sieve bound above makes the normalized exterior contribution \(O_{A,B}(1/R)\). Let \(X\to\infty\) first and then \(R\to\infty\). Plancherel for the indicator of \([0,u]\) gives \(\int_{\mathbb R}(\sin(\pi ut)/(\pi t))^2\,dt=u\), proving \(J_X(u)\to(B-A)u\) under the interval-mass hypothesis. The cumulative-mass hypothesis is open. This compact-interval argument is recorded here as a paper corollary of the formal tail bounds.

The ordinate sample of the multiplicative polynomial tends to zero, and its prime-torus Haar mean is zero. The deletion projection multiplies the polynomial's identity value by \(1-2/N\). The local additive moments remain an arithmetic input. The almost-all binary-correlation theorem of Matomäki, Radziwiłł and Tao assumes \(H\ge X^{8/33+\varepsilon}\). The later almost-all progression theorem assumes \(H\ge X^{1/3+\varepsilon}\). Both ranges grow faster than a fixed multiple of \(\log X\). [Matomäki–Radziwiłł–Tao](https://arxiv.org/abs/1707.01315) · [Matomäki–Radziwiłł–Shao–Tao–Teräväinen, Theorem 1.5](https://doi.org/10.1007/s00222-026-01408-6)
