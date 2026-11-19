# A Fourier certificate for a positive proportion of small consecutive gaps

Let the positive ordinates of all nontrivial zeros of the Riemann zeta function be ordered with analytic multiplicity. Define
\[
 D(\lambda)=\liminf_{T\to\infty}\frac1{N(T)}
 \#\{n:0<\gamma_n\le T,\
       \gamma_{n+1}-\gamma_n\le 2\pi\lambda/\log T\}.
\]
The degree-285 certificate gives **\(D(0.784782678)>0\)** without RH. Separate degree-83 and degree-105 certificates give \(D(0.784981)>0\) and \(D(0.784905297)>0\), respectively. The analytic deduction uses Lamzouri's externally established sparse-deletion estimate. The finite certificate is verified with exact rational sign checks and rational interval arithmetic. Neither the numerical search nor a finite sample of zeta zeros enters the proof.

Lamzouri's November 10 preprint proves \(D(0.7892)>0\) in Theorem 1.1 and reports \(D(\lambda)>0\) for \(\lambda>0.7864\) in Remark 1.2. The statement above strengthens both thresholds. Durkan and Pearce-Crump obtain infinitely many gaps below any fixed threshold greater than \(1/2\) unconditionally. Their positive-proportion conclusion at that scale assumes RH. No positive value for the proportion itself is estimated here. [Lamzouri, Theorem 1.1, Remark 1.2 and §3](https://arxiv.org/html/2611.14486v1) · [Durkan and Pearce-Crump](https://arxiv.org/abs/2610.28527)

## From a Schwartz Fourier kernel to consecutive gaps

Fix \(1/2<\theta<4/7\), and suppose \(f\) is even, real, nonnegative and Schwartz. Use \(\widehat f(u)=\int_{\mathbb R}f(\alpha)e^{-2\pi i u\alpha}\,d\alpha\). Sufficient conditions at \(0<\lambda<1\) are
\[
 \widehat f(0)=1,\qquad \widehat f(u)\le0\quad (|u|>\lambda),
 \qquad M=f(0)+2\int_0^\theta \alpha f(\alpha)\,d\alpha>1.
\]
Theorem 3.3 is stated for compactly supported \(f\). The following argument establishes its Schwartz version using the compactly supported hypothesis of Proposition 3.2 exactly as stated.

Suppose \(D(\lambda)=0\), and select \(T\to\infty\) along which the fraction tends to zero. Inside the finite chronological list \((0,T]\), mark both endpoints of every adjacent gap at most \(2\pi\lambda/\log T\); call the resulting multiset \(E_T\). Each adjacent gap contributes at most two endpoints. The number of marked occurrences is \(o(N(T))\) because the internal gaps form a subset of those in the definition of \(D\). Every block of two or more identical ordinates is marked in full. Off-line zeros come in reflected pairs at the same height, so \(E_T\) is reflection invariant and the retained zeros are simple and on the critical line. Any two retained ordinates differ by more than \(2\pi\lambda/\log T\), since each internal adjacent gap touching a retained ordinate exceeds the threshold.

Choose fixed \(\theta'\in(\theta,4/7)\) and a real even smooth cutoff \(0\le\psi\le1\), equal to one on \([-\theta,\theta]\) and supported inside \((-\theta',\theta')\). Put \(g=\psi f\) and \(B_T=Z(T)\setminus E_T\). Write \(L=\log T\), \(w(y)=4/(4+y^2)\), and for either test \(h=f,g\) let
\[
 S_h(B_T)=\frac{1}{N(T)}\sum_{i,j\in B_T}
 w(\gamma_i-\gamma_j)\widehat h\!\left(\frac{L(\gamma_i-\gamma_j)}{2\pi}\right).
\]
All retained points are critical, so the ordinary \(S_g\) equals Lamzouri's complex tested pair sum. His Proposition 3.2 applies to \(g\) at \(\theta'\), with \(\delta=|E_T|/N(T)\to0\), giving
\[
 S_g(B_T)=g(0)+2\int_0^1\alpha g(\alpha)\,d\alpha+o(1)\ge M+o(1).
\]
At heights with \(E_T=\varnothing\), Lemma 3.1 gives the same conclusion.

The finite real-ordinate form factor is nonnegative at every frequency. This follows by writing \(w(y)=\int_{\mathbb R}e^{-2|v|}e^{ivy}dv\), turning the pair sum into an integral of a squared modulus. Fourier evaluation is therefore monotone in the frequency test: \(S_f(B_T)\ge S_g(B_T)\), since \(f\ge g\). The finite Fourier interchange holds for both tests by integrability. Direct summation also yields \(S_f(B_T)\le |B_T|/N(T)\le1\), because the diagonal terms equal one and every off-diagonal term is nonpositive. This contradicts \(M>1\), proving \(D(\lambda)>0\). In particular, removing the compact-support condition on \(f\) has incurred no uncontrolled truncation error. [Lamzouri, (3.1)–(3.5), Lemma 3.1, Proposition 3.2 and Theorem 3.3](https://arxiv.org/html/2611.14486v1#S3)

For a quantitative version with source-dependent constants, let \(e=1/8-7\theta'/32>0\). Suppose the error in normalized Proposition 3.2 for the fixed compact cutoff is at most \(C\delta^e+C_0/\sqrt{\log T}\), and put \(\eta=M-1\). At sufficiently large heights the second summand is at most \(\eta/2\). If fewer than a quarter of the internal gaps are small, the deletion fraction is at most twice their fraction and less than one. The same upper and lower pair estimates then give
\[
 D(\lambda)\;\ge\;\min\left\{\frac14,\ \frac12\left(\frac{\eta}{2C}\right)^{1/e}\right\}.
\]
The cited proposition leaves \(C\) implicit, so this formula supplies no absolute numerical percentage.

## A compact test satisfying Theorem 3.3 as stated

There is an independent way to retain the Fourier sign when passing to a compact test. Fix \(0<a<b<\lambda\), and take Lamzouri's compact nonnegative tests \(k_t(x)=t\widehat R(tx)\), where
\[
R(v)=\frac{\sin^2(\pi v)}{\pi^2v^2(1-v^2)}.
\]
The removable values are understood by continuity. Average over the dilations by setting \(k=(b-a)^{-1}\int_a^b k_t\,dt\). This is an even nonnegative \(C_c^2\) function with \(\widehat k(0)=1\). For \(u\ge\lambda\), its Fourier transform satisfies
\[
 -\widehat k(u)\ge \frac{a^4}{\pi^2u^4(b-a)}
     \int_a^b\sin^2(\pi u/t)\,dt.
\]
The integral is continuous and strictly positive for every \(u>0\). It tends to \((b-a)/2\) as \(u\to\infty\), by substituting \(v=1/t\) and using the Riemann–Lebesgue lemma. Hence some \(c>0\) gives \(\widehat k(u)\le -c(1+|u|)^{-4}\) for every \(|u|\ge\lambda\).

Take an even smooth cutoff \(0\le\chi\le1\) equal to one on \([-1,1]\), and put \(f_R(x)=\chi(x/R)f(x)\). As \(R\to\infty\), the Schwartz decay of \(f\) gives \(f_R\to f\) in \(W^{4,1}(\mathbb R)\). Fourier evaluation and four integrations by parts therefore give \(\sup_u(1+|u|)^4|\widehat f_R(u)-\widehat f(u)|\to0\). Fix \(0<\varepsilon<M-1\); all five kernel intervals permit \(\varepsilon=10^{-11}\). Choose \(R>\theta\) large enough that this weighted error is at most \(c\varepsilon\). Then \(h=f_R+\varepsilon k\) is nonnegative and compactly supported and \(\widehat h(u)\le0\) for \(|u|\ge\lambda\). Its zero-frequency mass satisfies \(0<\widehat h(0)\le1+\varepsilon\). Its objective is at least \(M>1+\varepsilon\) because \(f_R=f\) throughout \([-\theta,\theta]\) and \(k\ge0\). The compact test \(h/\widehat h(0)\) thus satisfies every hypothesis in Lamzouri's stated Theorem 3.3. [Lamzouri, Theorem 3.3 and the Selberg minorant following (3.15)](https://arxiv.org/html/2611.14486v1#S3)

## The explicit kernel

Take \(\lambda=784981/1000000,\ \theta=28571/50000,\ t=3\), \(r=32543467/40000000\), and \(s=\theta\sqrt{\pi}/r\). Degrees in this note refer to the variable \(y\); the even polynomial in the Fourier coordinate has twice that degree. This is the degree-83 kernel. The accompanying checker lists its integer coefficients \(b_0,\ldots,b_{83}\). In terms of generalized Laguerre polynomials set
\[
 P(y)=\sum_{j=0}^{83}b_jL_j^{-1/2}(2y),\qquad
 Q(y)=\sum_{j=0}^{83}(-1)^jb_jL_j^{-1/2}(2y).
\]
Define
\[
 f(\alpha)=\frac{e^{-\pi(\alpha/s)^2}P(\pi(\alpha/s)^2)}{sQ(0)},\qquad
 \widehat f(u)=\frac{e^{-\pi(su)^2}Q(\pi(su)^2)}{Q(0)}.
\]
To see the Fourier identity, the generating function of the unscaled Gaussian–Laguerre basis is
\((1-z)^{-1/2}\exp(-\pi x^2(1+z)/(1-z))\). Its Gaussian Fourier transform is the same generating function with \(z\) replaced by \(-z\). Comparing coefficients gives the factor \((-1)^j\), and the displayed scaling follows. Both functions are even Schwartz functions. The checker also independently compares their ordinary monomial coefficients. Differentiating the Gaussian transform gives \(\mathcal F[(\pi x^2)^k e^{-\pi x^2}](u)=k! L_k^{-1/2}(\pi u^2)e^{-\pi u^2}\). Equivalently, the coefficient of \(y^j\) contributed by a source monomial \(y^k\) is \((-1)^j\binom{k}{j}2^{j-k}\prod_{\ell=j}^{k-1}(2\ell+1)\).

The checker also replays a denominator-free Fourier recurrence directly in monomial coordinates. Write \(V=Q'-Q\) and \(B(Q)=-V-2y(V'-V)\). If \(G_Q(u)=e^{-\pi u^2}Q(\pi u^2)\), then \(-G_Q''/(4\pi)=G_{B(Q)}/2\), which is the Fourier transform of multiplication by \(\pi x^2\). Horner recursion on the input polynomial gives the complete Fourier output using integer addition and multiplication.

The exact polynomial checks give \(P(y)>0\) on \(y\ge0\), \(Q(0)>0\), and \(Q(y)<0\) on \(y\ge t\). The same rational interval computation gives \(\pi(s\lambda)^2\ge t\). These checks verify the Fourier sign conditions, including equality of the gap to the threshold. Let \(z=r^2=\pi(\theta/s)^2\), and \(H(y)=\sum_{k=0}^{83}P^{(k)}(y)\). Since \(H-H'=P\),
\[
 M=\frac{P(0)/s+(s/\pi)(H(0)-e^{-z}H(z))}{Q(0)}
 \in[1.000000857671924612,\ 1.000000857671924613].
\]

The degree-105 kernel uses the same Gaussian–Laguerre construction, with degree 105 in both sums, and the following exact parameters:
\[
 \lambda=\frac{784905297}{10^9},\qquad \theta=\frac47-10^{-12},\qquad
 t=\frac{31}{10},\qquad r=\frac{8002915605081}{10^{13}},\qquad s=\frac{\theta\sqrt{\pi}}r.
\]
Its independent polynomial signs hold on the same domains \(y\ge0\) and \(y\ge t\), and the checker certifies \(\pi(s\lambda)^2\ge t\). The normalized objective satisfies
\[
 M\in[1.000000000069163297,\ 1.000000000069163298].
\]
The strictly subcritical support parameter is essential in the application of Proposition 3.2. The constants implicit in the deletion loss can depend on this parameter.

The following three further kernels use the same normalized construction.
Write \(D(\lambda)>0\) for positive lower gap proportion and \(a\) for the exponent in a one-logarithm Selberg density estimate holding uniformly down to the critical line.

| Degree in \(y\) | Gap \(\lambda\) | Cutoff \(\theta\) | Fourier ray \(t\) | Rational radius \(r\) | Certified lower endpoint for \(M\) | Frequency-side premise |
|---:|---:|---:|---:|---:|---:|---|
| 285 | 0.784782678 | \(4/7-10^{-12}\) | 78/25 | 79759777828511/10¹⁴ | 1.000000000452054486 | Unconditional |
| 149 | 0.73995708 | \(2/3-10^{-8}\) | 77/25 | 44152955860237/50000000000000 | 1.000000000256212568 | One-log \(a=4/3\) |
| 205 | 0.603780886 | \(1-10^{-12}\) | 77/25 | 108082125014603/10¹⁴ | 1.000000000666644703 | One-log \(a=2\) |

For the conditional rows, uniform one-log density gives
\(\mathbb P((\log T)|\beta-1/2|>v)\ll e^{-av}\). Lamzouri's all-fixed-order row moments and the sparse-deletion argument then allow any fixed support below \(a/2\) and below one. The displayed cutoffs therefore suffice with any single exponent \(a>4/3-2\cdot10^{-8}\) and \(a>2-2\cdot10^{-12}\), respectively. A cofinal family at either endpoint gives the same conclusion. If the internal gap fraction tends to zero along a sequence, deleting its endpoints has negligible effect on the tested sum at this support. The finite separated-pair upper bound contradicts the certified excess. The same two kernels give \(D(0.70321)>0\) under one-log \(a=3/2\), and \(D(0.65181)>0\) under one-log \(a=7/4\). Lamzouri explicitly records 0.6039 under the one-log \(a=2\) premise. [Lamzouri, Introduction](https://arxiv.org/html/2611.14486v1#S1) · [Sparse-deletion proof](SparsePairDensityBounds20261119.md)

## Unconditional counts at smaller gap scales

Write \(d_T(\lambda)\) for the qualifying internal-gap count divided by \(N(T)\). The two known normalized density tails give a vanishing deleted-pair error whenever the discarded proportion is \(O((\log T)^{-p})\), the support is \(4/7\le\theta<2/3\), and \(p>6\theta/(2-3\theta)\). Applied to the endpoints of small gaps, the strict functional excess proves \((\log T)^p d_T(\lambda)\to+\infty\).

| Gap \(\lambda\) | Support \(\theta\) | Exponent yielding the unconditional limit | Degree |
|---:|---:|---:|---:|
| 0.77104 | 3/5 | every \(p>18\) | 285 |
| 0.75926 | 5/8 | every \(p>30\) | 285 |
| 0.74762 | 13/20 | every \(p>78\) | 149 |
| 0.74301 | 33/50 | every \(p>198\) | 149 |
| 0.74 | \(28352/(3(14176+2))-10^{-10}\) | \(p=14176\) | 149 |

The proof uses the log-prefactor density estimate of Chourasiya and Simonič together with the normalized one-log estimates for every fixed \(a<8/7\). Each row uses a strictly larger support for its smooth cutoff while preserving the stated strict inequality on \(p\). The final row gives a lower bound for the number of gaps at 74% of average spacing of order \(N(T)/(\log T)^{14176}\), with the ratio tending to infinity. [Sparse-deletion proof and phase diagram](SparsePairDensityBounds20261119.md) · [Chourasiya and Simonič](https://arxiv.org/abs/2507.15184)

## Polynomial counts in the height at smaller gap thresholds

Let \(A_T(\lambda)\) count the internal adjacent gaps at most \(2\pi\lambda/\log T\). The following rows give \(A_T(\lambda)/(T^{1-p}\log T)\to\infty\). The parameter \(p\) is a power of the height, whereas the preceding section uses powers of its logarithm.

| Gap \(\lambda\) | Support \(\theta\) | Degree | \(p\) | Count grows faster than | Density source |
|---:|---:|---:|---:|---|---|
| 0.70 | 0.757551 | 149 | 0.273 | \(T^{0.727}\log T\) | Ingham, Chourasiya–Simonič |
| 0.65 | 0.879554 | 205 | 0.4305 | \(T^{0.5695}\log T\) | Guth–Maynard |
| 0.6038 | 0.999949 | 205 | 9/16 | \(T^{7/16}\log T\) | Tao–Trudgian–Yang, Bourgain, Huxley |
| 0.603780886 | \(1-10^{-12}\) | 205 | 9/16 | \(T^{7/16}\log T\) | Same published sources |
| 0.603780886 | \(1-10^{-12}\) | 205 | 1/2 | \(T^{1/2}\log T\) | Lewko, independently kernel-checked and publicly registered |

The first four conclusions use published curves. Lewko's final-row input has a distinct October 2026 public verification record. The source support restriction stays strictly below one even for the last two rows; the large local moment order and implied constants are fixed after choosing that support. The scalar objectives for the 0.70, 0.65 and 0.6038 rows are respectively greater than 1.000000155848216828, 1.000000055412623522 and 1.000000061941525870. The original 0.603780886 objective is greater than 1.000000000666644703. [Height-profile proof and fixed-abscissa quantifiers](SparsePairDensityBounds20261119.md) · [Tao–Trudgian–Yang, Table 11.1](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html) · [Lewko registration](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1)

## Reproducibility

Run `python3 verify_small_gap_kernel.py` for every kernel and additional parameter row. The `--degree` option selects one kernel and its associated rows. The checker uses the Python standard library and accepts no optimizer output at runtime. It constructs both polynomials by the Laguerre three-term recurrence, translates \(-Q(t+y)\), and maps each positive half-line to \(0\le v\le1\) using \(y=v/(1-v)\). A polynomial \(\sum a_k y^k\) of degree \(n\) then has Bernstein coefficients \(a_k/\binom nk\) after multiplication by \((1-v)^n\). Exact subdivision at dyadic midpoints certifies every coefficient strictly positive on the final intervals. The physical/Fourier node counts are 399/323, 453/395, 543/393, 905/569 and 921/981 for degrees 83, 105, 149, 205 and 285 respectively.

The integral check uses integer-backed interval arithmetic with outward rounding at every operation. Machin's formula and alternating rational arctangent sums bound \(\pi\). Integer square roots bound \(s\), and Taylor's theorem with the signs of successive derivatives bounds \(e^{-z}\). The checker prints every enclosure rounded outward. The analytic small-gap conclusion remains a paper deduction from the cited theorem. [Certificate checker](BoundCertificateReplays20261119.md#verify_small_gap_kernelpy)
