# Sharp Wasserstein bounds for one dyadic zero

Let \(P\) be a fixed finite set of primes, possibly empty. Sample a zero occurrence uniformly with multiplicity in \(U<\gamma\le2U\). Write \(L=\log U\), \(s=(\gamma-U)/U\), \(z_p=\gamma\log p/(2\pi)\bmod1\), \(\mu_U=\mathcal L(\beta,s,z)\), and \(\nu=\delta_{1/2}\otimes ds\otimes m_P\), with uniform probability on \([0,1]\) and product Haar probability. Use the sum of ordinary real distances and the geodesic distances on the unit-period circles. Define
\[
 m_U=\mathbb E_{\mu_U}|\beta-1/2|,\quad \kappa=3/4-\log 2,\qquad
 C_p=\frac{2\log p}{\pi^2}\sum_{\substack{k\ge1\\k\ {\mathrm{odd}}}}\frac{p^{-k/2}}{k^2}.
\]

For either the transport-plan distance or its Lipschitz dual, the classical conclusions are
\[
 W_1(\mu_U,\nu)\ll_P L^{-1},\qquad
 \liminf_{U\to\infty}L\{W_1(\mu_U,\nu)-m_U\}\ \ge\ \kappa+\sum_{p\in P}C_p.
 \tag{1}
\]
In particular the order \(1/\log U\) is sharp even for the joint height and phase coordinates alone. Fixed finite \(P\) is essential. The constants on the right grow without bound as more primes are included. This is a statement about the law of one occurrence. Ordinary positive-gap pair correlation requires an estimate for two occurrences.

## 1. Exact horizontal cost

Writing \(\eta_U=\mathcal L(s,z)\) and \(\lambda=ds\otimes m_P\), one has the exact identity
\[
 W_1(\mu_U,\nu)=m_U+ W_1(\eta_U,\lambda). \tag{2}
\]
In the primal formula, every plan pays \(m_U\) in its first coordinate and projects to a coupling of \(\eta_U,\lambda\). Conversely, lift any projected plan by attaching \(\beta\) with its empirical conditional distribution at each \((s,z)\). This includes ties and preserves the two marginals. In the dual formula, restriction of a 1-Lipschitz potential to the slice gives the upper bound in (2). Extend an approximately extremizing oriented slice potential \(g\) by \(f(\beta,s,z)=|\beta-1/2|+g(s,z)\) for the reverse bound. Subtract the value at the anchor if needed. Consequently \(m_U=O(1/L)\), equivalently \(\sum_{U<\gamma\le2U}|\beta-1/2|=O(U)\), is the exact necessary horizontal condition for a sharp full-space upper bound.

This condition has a direct classical proof using Baluyot’s Theorem 1.3. Fix any \(0<\theta<1/22\), use zero shift, and let \(M\) be his quadratic Möbius mollifier. The dyadic mollified fourth moment bounds \(\int_{U-1}^{2U+1}\log^+|\zeta M(1/2+it)|dt\ll U\). At real part 4 both factors differ from 1 by at most \(\zeta(4)-1\); their product stays in a fixed disk about 1 of radius less than \(1/2\). For a rectangle with regular caps enclosing \([U,2U]\), Littlewood’s lemma now gives \(\sum(\beta-1/2)_+\ll U\). The right integral is \(O(U)\); Jensen applied to the symmetrized real part around 4 gives \(O(\log U)\) for each cap, just as in the [dyadic Ingham proof](INGHAM_DYADIC_ONE_LOG_20261125.md). Take regular left edges tending to \(1/2\), using continuity of \(\log^+|\zeta M|\) on the compact height interval. The zeros of \(\zeta M\) include all original occurrences. Functional-equation symmetry gives the absolute displacement bound. No zero-density estimate enters this proof.

## 2. The residual needs only a first absolute moment

Put \(X=\lfloor(2U)^{1/8}\rfloor\) and let \(R_U(t)\) be the cumulative zero count minus its Riemann–von Mangoldt main term plus \(\pi^{-1}\sum_{p\le X}\sin(t\log p)/\sqrt p\), in the repository’s convention. The prime trace argument uses just
\[
 \int_U^{2U}|R_U(t)|dt\ll U. \tag{3}
\]
The ordinary Riemann–von Mangoldt pointwise error and the trivial prime sum give \(|R_U(U)|+|R_U(2U)|=O(U)\). Thus no additional endpoint hypothesis is needed.

For an independent proof of (3), use the **second moment** in Goldston’s account of Selberg’s theorem, Theorem 8, equation (10.5), at \(k=1\), \(T=2U\). Its prime sum runs to \(2U\). Removing \(X<p\le2U\) costs \(O(U)\) in mean square by the Dirichlet-polynomial mean-value inequality, since \(\sum_{X<p\le2U}1/p=O(1)\) by Mertens. The difference between the conventional \(S(t)\) and the count remainder is \(O(1)\) almost everywhere on this window. Cauchy–Schwarz gives (3). Alternatively \(k=8\) in the same published theorem matches the cutoff exactly. The first-moment proof avoids any sixteenth-moment assumption.

For a fixed \(P\), approximate the centered slice \(f(1/2,s,z)-\nu f\), at degree \(n\asymp_P L\), as in §3. On the orbit, its approximating trace \(H\) has \(\|H\|_\infty+\|H'\|_\infty=O_P(1)\). Abel summation against \(R_U(t)\) costs \(O_P(U)\) by (3). The repository’s \(\mathtt{trace\_sum\_bound}\) controls the smooth count and prime terms by \(O_P(U)\), including the integrated zero mode, outside-prime frequency gaps and the fixed primes in \(P\). The slice approximation costs \(O_P(1/L)\) per occurrence. Divide by \(N(2U)-N(U)\asymp UL\) to obtain \(W_1(\eta_U,\lambda)\ll_P1/L\). Equation (2) proves the upper bound in (1).

## 3. A positive Jackson kernel for the specified prime set

Let \(d=|P|\), \(D=1+d/2\), and \(B_P=\sum_{p\in P}\log p\). Extend the centered slice as \(G(x,z)=f(1/2,2\|x\|,z)-\nu f\) on the \((d+1)\)-dimensional unit torus. It is even in \(x\), has mean zero, sup norm at most \(D\), and separate Lipschitz constants \(2,1,\ldots,1\). Put
\[
 K_n(x)=n^{-1}|\sum_{j=0}^{n-1}e^{2\pi ijx}|^2,\qquad J_n=K_n^2/\int K_n^2.
\]
The denominator is \((2n^2+1)/(3n)\) by Parseval. Since \(K_n\le\min(n,(4n\|x\|^2)^{-1})\), splitting at \(1/(2n)\) gives \(\int\|x\|J_n(x)dx\le3/(4n)\). Convolve with the product of \(d+1\) such kernels. The error is at most \(3(d+2)/(4n)\); positivity preserves all Lipschitz bounds. The angular modes have \(|k_p|\le2(n-1)\). Write \(b_k(s)\) for the angular Fourier coefficients of the convolution at \(x=s/2\). They satisfy \(|b_k|\le D\), \(|b_k'|\le1\), and \(\int_0^1 b_0(s)ds=0\) by evenness and mean preservation. One integration by parts gives a bound \((2D+1)/|v|\) for the transform of each coefficient at nonzero frequency \(v\), uniformly in \(U\).

The trace on \(s=(t-U)/U,\ z_p=t\log p/(2\pi)\) has derivative bounded by \(1/U+B_P/(2\pi)\). For each \(k\), encode the mode by the coprime pair \(\prod p^{k_p^+},\prod p^{k_p^-}\). Unique factorization gives injectivity, and each integer is at most \(e^{2nB_P}\). There are at most \((4n-3)^d\) modes. Thus the repository’s all-degree construction for this \(P\) admits \(A=d+3+B_P,\ B=2d+2B_P\), for every \(n\ge1,\ U\ge2\), including \(d=0\). The height test is smoothed as well, so the trace has a continuous derivative. The integrated zero mode vanishes even when its coefficient depends on height.

## 4. A second proof that bypasses the prime-counting residual

Alternatively take any published fixed positive uniform Selberg slope \(a>0\), for example Ford–Zaharescu, Lemma 2. This route uses no estimate for \(R_U\). Suppress the \(1/2\) coordinate in \(f\) and approximate its height–phase slice by the same positive convolution. Let its angular bandwidth be \(H\), and, for fixed \(s\), evaluate the resulting Laurent polynomial on the complexified orbit. On the real torus its derivative along the actual orbit has sup norm \(O_P(1)\). A Laurent polynomial of coordinate degree \(H\) and torus sup norm \(M\) obeys
\[
 |Q(z)|\le M\prod_{p\in P}\max(|z_p|,|z_p|^{-1})^H .
\]
Apply the one-variable maximum principle to the polynomial multiplied by \(z^H\), and to its reciprocal-variable version outside the disk, successively in each coordinate. Apply this bound to the orbital derivative and integrate along the imaginary segment. At a zero with \(\delta=\beta-1/2\), replacing the real height by \(\gamma-i\delta\) in its angular arguments costs \(O_P(|\delta|e^{B|\delta|})\), \(B=H B_P\). The real height used in \(b_k(s)\) stays fixed.

The symmetric displacement tail is \(O(UL e^{-Qx})\), \(Q\asymp aL\), by the positive slope and reflection. Integration of \((1+Bx)e^{Bx}\) against this tail costs \(O(UL\,Q/(Q-B)^2)=O_P(U)\) if \(B\le Q/2\). Choose \(H=c_PL\) small enough that this holds and all rational numerators and denominators are at most \(X=U^{1/10}\). For a positive angular frequency \(\log(n/m)\) the complexified value is exactly \((n/m)^{\rho-1/2}\). For a negative frequency use conjugation and reflection \(\rho\mapsto1-\bar\rho\), which leaves the height coefficient fixed. The repository’s uniform rational Landau bound for cumulative heights \(t\in[U,2U]\) is
\[
 O\bigl(X^{5/2}+X^{3/2}\log^2(t+3)+X\log(t+3)\bigr)
\]
before division by \(\sqrt{n/m}\ge1\). Abel summation with \(|b_k|+|b_k'|\ll_P1\) and summation over \(O_P((1+H)^d)\) modes gives total error \(o_P(U)\). Among nonconstant modes the main term is supported on single-prime powers. Its absolute sum is \(O_P(U\sum_{p\in P}\sum_{j\ge1}(\log p)p^{-j/2})=O_P(U)\). The zero mode has mean zero in \(s\); the uniform Riemann–von Mangoldt formula and one integration by parts give \(O_P(U)\). Approximation costs \(O_P(1/H)\) per occurrence. This proves the sharp upper rate again. If \(P\) is empty the angular step disappears.

The same argument with the repository’s proved tail \(\mathtt{eventually\_rightStrictTail\_loglog\_bound}\) uses \(Q\asymp L/\log L\), \(B\le Q/2\), and \(H\asymp_P L/\log L\). The resulting unconditional upper bound from these weaker number-theoretic inputs is \(O_P(\log\log U/\log U)\). The improvement to \(O_P(1/\log U)\) above can use either the published fixed positive slope or the first-moment route in §§1–2.

## 5. Explicit additive lower constants

The admissible test \(f(\beta,s,z)=|\beta-1/2|+s+\sum_{p\in P}\|z_p\|\) fits the sum metric without dividing by \(d\). The repository’s Riemann–von Mangoldt calculation gives \(L(\mathbb E s-1/2)\to\kappa\). For a prime \(p\), the Ford–Zaharescu signed correction on the dyadic probability scale has density
\[
 g_p(x)=-2(\log p)\sum_{k\ge1}p^{-k/2}\cos(2\pi kx).
\]
Indeed, subtract the cumulative formulas at \(2U\) and \(U\) and divide by \(N(2U)-N(U)\sim UL/(2\pi)\). Ford–Zaharescu’s Theorem 1 applies to the periodic tent \(x\mapsto\|x\|\). Its derivative has \(L^1\) translation modulus \(4h\) for \(0<h<1/2\). The tent’s cosine integral is \(((-1)^k-1)/(2\pi^2 k^2)\). Hence \(L(\mathbb E\|z_p\|-1/4)\to C_p\), proving (1) for the dual. Weak duality gives the same witness for every transport plan. Alternatively, smooth each tent by a fixed Fejér kernel, apply only fixed-character FMZ limits, and let the kernel degree tend to infinity after taking the lower limit. Fixed-character convergence alone suffices for this lower bound.

The coefficient \(C_p\) is the exact Lipschitz-dual norm of the signed marginal \(g_p(x)dx\). Its periodic primitive of mean zero has sign opposite to \(\sin(2\pi x)\), as follows from \(\sum r^k\sin(2\pi kx)/k=-\arg(1-r e^{2\pi ix})\). Integration by parts bounds the norm by the integral of the absolute primitive, attained by the tent. For \(P=\{p\le x\}\), the prime number theorem gives \(\sum_{p\in P}C_p\sim4\sqrt{x}/\pi^2\). This concerns constants for fixed \(P\) followed by \(x\to\infty\). A sharp upper leading constant for nonempty \(P\) remains undetermined.

When \(P=\varnothing\) equation (2) and the one-dimensional quantile formula give the stronger identity
\[
 \lim_{U\to\infty} L\{W_1(\mu_U,\nu)-m_U\}=\kappa .
\]
Indeed, the height CDF \(F_U(s)\) satisfies uniformly on \([0,1]\)
\[
 F_U(s)-s=\frac{(1+s)\log(1+s)-2s\log2}{L-\log(2\pi)-1+2\log2}+O(1/U).
\]
The numerator is nonpositive by convexity and its absolute integral is \(\kappa\). Integrate \(|F_U(s)-s|\) to get the height transport cost, including repeated ordinates.

## Formal and classical inputs

The existing [Lean module](Analysis/DyadicZeroWasserstein.lean) now exposes the first-moment entry point, direct approximation for one \(P\), the unconditional horizontal-plus-height lower witness and transport assembly along the actual sequence. The numerical constants \(C_p\), the Jackson construction, the alternative Landau upper bound and the classical analytic providers are proved here on paper. The whole sharp upper bound still requires those providers in Lean.

The sum metric induces the product topology. The compact empirical support and the compact support of \(\nu\) give finite first moments. The compact Kantorovich–Rubinstein theorem identifies the two distances automatically. Potentials on a common compact support extend by the real McShane extension, and subtracting their value at the anchor preserves their integral difference. This classical transport step introduces no arithmetic assumption. The Lean transport entry needs equality only for the actual pair eventually in \(U\).

- S. A. C. Baluyot, *On the zeros of Riemann’s zeta-function on the critical line*, [Theorem 1.3](https://sieg-baluyot.github.io/criticalline.pdf).
- D. Goldston, *Notes on pair correlation of zeros and prime numbers*, [Theorem 8, (10.5)](https://arxiv.org/html/math/0412313v1).
- K. Ford and A. Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, [Theorem 1 and Lemma 2](https://ford126.web.illinois.edu/wwwpapers/fz.pdf).
- B. Borda, *Berry–Esseen smoothing inequality for the Wasserstein metric on compact Lie groups*, [§3](https://arxiv.org/abs/2005.04925).
- C. Villani, *Topics in Optimal Transportation*, [Theorem 1.14](https://www.math.ucla.edu/~wgangbo/Cedric-Villani.pdf).
