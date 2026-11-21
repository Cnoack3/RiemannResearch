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
