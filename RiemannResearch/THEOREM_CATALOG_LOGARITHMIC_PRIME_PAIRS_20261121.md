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
