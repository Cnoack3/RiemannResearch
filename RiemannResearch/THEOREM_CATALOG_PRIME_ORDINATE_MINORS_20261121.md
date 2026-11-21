# Prime coordinates on consecutive zero pairs and triples

Write $z_p(t)=\exp(it\log p)$ and $d=|\log q-\log p|$. The zeros with $0<\gamma\le T$ are ordered by ordinate, with copies for analytic multiplicity and for different zeros at the same height. Every interior sum below omits starts whose last index would fall outside this list.

## Determinants and consecutive spacings

Define $D_{ij}=z_p(\gamma_i)z_q(\gamma_j)-z_q(\gamma_i)z_p(\gamma_j)$. Form $V_{012}$ with rows at three successive ordinates and columns $z_p^2,z_pz_q,z_q^2$. For $g=\gamma_1-\gamma_0$, $h=\gamma_2-\gamma_1$ and $C(x)=2|\sin(x/2)|$, the exact identities are

$$
 V_{012}=D_{01}D_{02}D_{12},\qquad |D_{01}|=C(dg),\qquad
 |V_{012}|=C(dg)C(dh)C(d(g+h)).
$$

The pointwise estimates keep the mixed term and its one-sided error. With $A=gh(g+h)$,

$$
 0\le dg-|D_{01}|\le (dg)^3/24,\qquad
 0\le d^3A-|V_{012}|\le d^5 A(g^2+gh+h^2)/12.
$$

The coefficient in the triple bound is attained to leading order when $(g,h)$ is replaced by $(\epsilon g,\epsilon h)$ with fixed positive gaps and $\epsilon\downarrow0$. Wolfram Language independently expanded the determinant, the cubic and quintic Taylor coefficients, and the reciprocal-square remainder. The Lean pointwise inequalities hold for arbitrary nonnegative gaps.

For $N=N(T)\ge 2$, define $S_k=\sum_{j=1}^{N-1}g_j^k$, $M_3=\sum_{j=1}^{N-2}g_jg_{j+1}(g_j+g_{j+1})$, and $L=\gamma_N-\gamma_1$. Let $A_2,A_3$ be the sums of absolute determinants on interior pairs and triples. Then

$$
 0\le dL-A_2\le d^3 S_3/24,\qquad 0\le d^3 M_3-A_3\le d^5 S_5/2.
$$

The part of the cubic gap moment that contributes to this statistic is given exactly by

$$
 M_3=2S_3-g_1^3-g_{N-1}^3-
 \sum_{j=1}^{N-2}(g_j-g_{j+1})^2(g_j+g_{j+1}).
$$

For fixed columns, $A_2/N\to0$ and $A_3/N\to0$ follow in Lean from its actual zero-count bound. The file declarations also cover empty and singleton cutoffs.

| Module | Principal declarations |
| --- | --- |
| [PrimeOrdinateMinors](Analysis/PrimeOrdinateMinors.lean) | `atom_eq_fourier`, `pairMinor_factor`, `tripleMinor_factor`, `pairMinor_norm`, `tripleMinor_defect`, `logDistance_add_le` |
| [ActualConsecutivePrimeMinors](Analysis/ActualConsecutivePrimeMinors.lean) | `mixed_cubic_balance`, `pairSum_defect`, `tripleSum_defect`, `tendsto_consecutive_minor_means` |
| [TwinPrimeOrdinateMinors](Analysis/TwinPrimeOrdinateMinors.lean) | `shifted_tripleMinor_le`, `twinIndices_exact`, `twin_mesh_remainder`, `twin_block_triple_bound` |

## Twin-prime contribution

For a positive integer shift $k$, $d(p,p+k)\le k/p$. In particular each twin contributes at most $8A/p^3$. For $Y=6K+5$ and $X=Y+6L$,

$$
 \sum_{\substack{Y<p\le X\\ p,\ p+2\ {\rm prime}}}|V_{012}(p,p+2)|
 \le \frac{2}{3}(Y^{-2}-X^{-2})A.
$$

Every twin in this interval is counted once. The lower entries 3 and 5 can be included separately when summing from the first twin. The proof majorizes each allowed term in the residue class by a telescoping reciprocal-square difference. It applies for every finite cutoff and gives absolute convergence of the triple statistic summed over all twins on paper. The Hardy–Littlewood pair-counting prediction remains a separate question. [Hardy and Littlewood, *Acta Math.* 44 (1923), Conjecture B](https://doi.org/10.1007/BF02403921)

## Signed Fourier sums

For $a+b+c=\log(n/m)\ne0$, consider the unnormalized sum $B_3=\sum_{j=1}^{N-2}\exp(i(a\gamma_j+b\gamma_{j+1}+c\gamma_{j+2}))$. The Lean reduction splits each summand at the middle ordinate and retains the signed outer-increment product. The total of those products has norm at most $|ac|E_2(T)$, where $E_2$ also includes the final truncated gap to $T$. The comparison with two pair sums and one one-point sum costs at most an additional four at the endpoints.

Under $E_2(T)/T\to0$, $B_3/T$ and the corresponding two-ordinate sum divided by $T$ both have the same rational FMZ coefficient as the one-ordinate character of their total frequency. The declarations are `tendsto_interiorPair_rational_of_gap` and `tendsto_interiorTriple_rational_of_gap`. For distinct primes $n=q,m=p$ this coefficient vanishes. For example, the signed sum of $p^{-i\gamma_j}(pq)^{i\gamma_{j+1}}p^{-i\gamma_{j+2}}$, divided by $T$, tends to zero. The one-ordinate assertion at $q/p$ and its extension to arbitrary fixed, finitely many weighted off-diagonal prime pairs are unconditional in Lean. [ActualConsecutiveTripleFourier](Analysis/ActualConsecutiveTripleFourier.lean)

## Consequences using the published gap estimates

Ford, Meng and Zaharescu use simultaneous characters at one zero ordinate. The signed result above transfers their fixed rational frequency to three successive ordinates and preserves its arithmetic coefficient. [Ford, Meng and Zaharescu, *Bull. Lond. Math. Soc.* 49 (2017), 1–9](https://doi.org/10.1112/blms.12001)

Fujii's Theorem 1 at fixed $r=1$ and $k=2,3,5$ gives $S_k(T)\ll_k T(\log T)^{1-k}$ after dyadic summation. In that sum heights below $\sqrt T$ contribute $O_k(\sqrt T)$ after absorbing the fixed initial interval. On the remaining dyadic blocks $\log U\asymp\log T$, and their lengths sum to $O(T)$. The last gap truncated at $T$ is bounded by the full forward gap at its starting ordinate. This supplies the squared-gap premise on paper. Combining the same estimates with the two finite determinant bounds gives

$$
 A_2=dL+O(d^3T/(\log T)^2),\qquad
 A_3=d^3M_3+O(d^5T/(\log T)^4).
$$

In particular $A_2/T\to d$ for fixed columns, since Riemann–von Mangoldt gives $L/T\to1$. Also $A_3/N\ll d^3/(\log T)^3$, with error $O(d^5/(\log T)^5)$ after subtracting $d^3 M_3/N$. The finite inequalities and the fixed-column count-normalized convergence are formalized. Fujii's gap-moment theorem is an external published input for these sharper rates. The formal obligation at height normalization is `ActualZeroOrdinate.VanishingCutoffGapEnergy`. The limiting value of $(\log T)^3 M_3/N$ is a further joint-spacing problem. [Fujii, *Proc. Japan Acad.* 51 (1975), 741–743, Theorem 1](https://doi.org/10.3792/pja/1195518466)

## Symbolic checks

These Wolfram Language expressions reproduce the signed factorization and the two leading odd coefficients for positive gaps.

```wolfram
p = {p0, p1, p2}; q = {q0, q1, q2};
w[i_, j_] := p[[i]] q[[j]] - q[[i]] p[[j]];
Expand[Det[Table[{p[[i]]^2, p[[i]] q[[i]], q[[i]]^2}, {i, 3}]] -
  w[1, 2] w[1, 3] w[2, 3]]
Table[Factor[SeriesCoefficient[
  8 Sin[d g x/2] Sin[d h x/2] Sin[d (g+h) x/2], {x, 0, k}]], {k, {3, 5}}]
```
