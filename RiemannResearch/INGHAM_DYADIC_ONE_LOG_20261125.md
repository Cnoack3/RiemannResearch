# One logarithm in the dyadic Ingham bound

Let \(S\) be sufficiently large, \(L=\log S\), \(1/2\leq\sigma<1\), and let \(N_+(\sigma;S,2S)\) count the nontrivial zeta zeros in \(S<\gamma\leq2S\) with \(\beta\geq\sigma\), including multiplicity. Put
\[
 p=4/3,\qquad d=\sigma-1/2,\qquad
 \kappa(x)=1-(2-p)x,\qquad E(x)=\frac{1-2x}{\kappa(x)}.
\]
The dyadic specialization of rStation Paper 184, Theorem 1, gives
\[
 N_+(\sigma;S,2S)\ll L S^{E(d)},\qquad E(d)=\frac{3(1-\sigma)}{2-\sigma}.
 \tag{1}
\]
The following proof also gives its refinement
\[
 N_+(\sigma;S,2S)\ll L S^{E(d)}
 [1+(1-2d)L]^{-pd/\kappa(d)}. \tag{2}
\]
In fact \(pd/\kappa(d)=1-E(d)=(2\sigma-1)/(2-\sigma)\). At each fixed \(\sigma<1\), the right side of (2) is \(O_\sigma((S\log S)^{3(1-\sigma)/(2-\sigma)})\). Equation (2) keeps track of the constant as \(\sigma\) varies.

The implied constants in (1) and (2) are absolute once the auxiliary cutoffs have been fixed. Both estimates hold with the lower height endpoint included. The proof below specializes to \(H=S\). It uses Baluyot’s published ordinary dyadic fourth moment and gives a direct arithmetic proof of the coefficient bound.

## 1. A smooth flat mollifier with bounded fourth moment

Fix \(w\in C_c^\infty((1/2,4))\), nonnegative and equal to one on \([2/3,3]\). For each fixed \(0<\theta<1/22\) put
\[
 M_{S,\theta}(s)=\sum_n\mu(n)(1-\log n/(\theta L))_+^2 n^{-s}.
\]
At zero shift Baluyot’s Theorem 1.3, (1.4) and (1.8), with weight \(w(t/S)\) and \(T_0=S\), bounds
\[
 B_S(\theta)=S^{-1}\int |\zeta(1/2+it)M_{S,\theta}(1/2+it)|^4w(t/S)\,dt
 \ll_\theta 1 .
\]
Indeed, the non-main error is \(O(S^{11\theta/2+3/4+\epsilon})\). Choose \(\epsilon<1/4-11\theta/2\). The following uniformization permits a fixed smooth cutoff. For fixed \(S\), \(B_S\) is continuous in \(\theta\), since the taper vanishes where a summand enters. On every compact subinterval of \((0,1/22)\), the closed sets \(\{\theta:\ B_S(\theta)\leq m\ \forall S\geq2\}\), \(m\in\mathbb N\), cover the interval. Bounded initial heights follow by continuity and local finiteness. Baire’s theorem gives an open subinterval with one uniform constant.

Choose \(0<\lambda<\nu\) inside this subinterval. Fix \(0\leq f\leq1\) on \([0,\infty)\), smooth, equal to one on \([0,\lambda]\) and zero on \([\nu,\infty)\), with a smooth compactly supported extension to \(\mathbb R\). Three integrations by parts give, for \(x\geq0\),
\[
 f(x)=-\tfrac12\int_\lambda^\nu \theta^2 f'''(\theta)(1-x/\theta)_+^2\,d\theta.
\]
Minkowski applied to this identity proves, for \(M(s)=\sum_n\mu(n)f(\log n/L)n^{-s}\),
\[
 \int_{2S/3}^{3S}|\zeta(1/2+it)M(1/2+it)|^4\,dt\ll S. \tag{3}
\]

## 2. Exact cancellation through length \(S\)

Work first in the half-plane of absolute convergence. Use \(\delta\) for the Dirichlet convolution unit. Write the coefficients of \(A=\zeta M\) as \(\delta+v\). Since \(f=1\) on the plateau and \(\sum_{d\mid n}\mu(d)=\delta(n)\), \(v(n)=0\) for \(n\leq S^\lambda\). With \(J=\lfloor1/\lambda\rfloor\), define
\[
 q_n=\mathbf1_{n\leq S}\sum_{j=0}^J(-v)^{*j}(n),\quad
 Q(s)=\sum_nq_n n^{-s},\quad F=\zeta M Q-1.
\]
No product of \(J+1\) integers exceeding \(S^\lambda\) can be at most \(S\). The finite geometric identity for convolution therefore gives \(F(s)=\sum_{n>S} a_n n^{-s}\). The gap holds coefficient by coefficient. The bounds \(|v(n)|\ll d_2(n)\) and fixed convolution length majorize \(|q_n|\) and \(|a_n|\) by a constant times a fixed divisor function, uniformly in \(S\).

## 3. Coefficient energy, including the sharp inverse cutoff

For every fixed \(C\geq1\) we claim
\[
 \sum_{n\leq S}|q_n|^2/n+\sum_{n\leq S^C}|a_n|^2/n\ll_C 1,\qquad
 \sum_{N<n\leq2N}|a_n|^2/n\ll_C 1/\log N
 \quad(S/2\leq N\leq S^C). \tag{4}
\]
Write \(A_n=\sum_{m\mid n}\mu(m)f(\log m/L)\). Fourier inversion gives exactly
\[
 A_n=(2\pi)^{-1}\int_{\mathbb R}\widehat f(t)
           \prod_{\ell\mid n,\ \ell\ {\rm prime}}(1-\ell^{it/L})\,dt .
\]
Define the nonnegative multiplicative function \(b_t\) by \(b_t(1)=1\) and \(b_t(\ell^e)=|1-\ell^{it/L}|\) for \(e\geq1\). The integral with \(|\widehat f|\) and \(b_t(n)\) majorizes both \(|A_n|\) and \(|v(n)|\) (at \(n=1\), \(v(1)=0\)). Consequently \(|q_n|\) and \(|a_n|\) are majorized by a fixed finite sum of integrals of convolutions \(h=b_{t_1}*\cdots*b_{t_k}\), \(k\leq J+1\), and a multiple of \(\delta\). The restriction \(n\leq S\) in \(q\) preserves the majorant inside each convolution.

Put \(\tau=1+\max_j|t_j|\). For \(e\geq1\), each weak composition of \(e\) has a positive part, giving
\[
 h(\ell^e)\ll_k d_k(\ell^e)\min(1,\tau\log\ell/L).
\]
For \(c(n)=h(n)^2\), Euler multiplication gives
\[
 \sum_{n\leq S^C}c(n)/n\leq
 \prod_{\ell\leq S^C}\left(1+\sum_{e\geq1}c(\ell^e)/\ell^e\right)
 \ll_{C,k}(2+\tau)^{O_k(1)}.
\]
Indeed, \(\sum_{e\geq1}d_k(\ell^e)^2/\ell^e\ll_k1/\ell\). Splitting the prime sum at \(\exp(L/\tau)\) gives \(\sum_{\ell\leq S^C}\min(1,\tau\log\ell/L)^2/\ell\ll_C1+\log(2+\tau)\), by partial summation from Chebyshev’s bound below the split and Mertens’ prime reciprocal estimate above it. If the split is below 2 the latter estimate alone suffices.

For the dyadic improvement, expand \(\log n=\sum_{\ell^e\parallel n}e\log\ell\), separate \(m=n/\ell^e\), and drop the coprimality restriction after using multiplicativity. Thus
\[
 (\log N)\sum_{N<n\leq2N}c(n)/n
 \leq \left(\sum_{m\leq2N}c(m)/m\right)
 \sup_{y>0}\sum_{y<\ell^e\leq2y}c(\ell^e)e\log\ell/\ell^e .
\]
The last supremum is \(O_k(1)\). At \(e=1\) this follows from the dyadic Chebyshev estimate. For \(e\geq2\) the unrestricted sum converges because \(d_k(\ell^e)\) grows polynomially in \(e\) and \(\sum_\ell\log\ell/\ell^2\) converges. Apply the preceding energy bound with a slightly larger \(C\) to cover \(2N\). Finally apply Minkowski in \(\ell^2(dn/n)\) to each finite mixture. The product of the Schwartz densities \(|\widehat f(t_j)|\) integrates the polynomial in \(\tau\). This proves (4).

## 4. Interpolation inside the strip

The Montgomery–Vaughan mean-value inequality for a Dirichlet polynomial gives an upper bound \(\ll\sum_n (|I|+n)|b_n|^2\) for \(\int_I|\sum b_n n^{-it}|^2dt\). This follows from their Hilbert inequality with local spacing \(\min_{m\ne n}|\log n-\log m|\gg1/n\). Applied to \(Q\), (4) gives \(\int_{2S/3}^{3S}|Q(1/2+it)|^2dt\ll S\). Hölder with (3) then gives
\[
 \int_{2S/3}^{3S}|F(1/2+it)|^pdt\ll S,\qquad 1/p=1/4+1/2. \tag{5}
\]

Let \(v_0=1/2+u\), \(1/L\leq u<1/2\), \(S\leq Y\leq S^3\), \(I^*=[S-1,2S+1]\). Take a smooth probability density \(\phi\) compactly supported in \((0,1)\). Form \(P_Y\) by averaging the partial sums of \(F\) through \(Y e^{-r/u}\) with weight \(\phi(r)dr\), and set \(R_Y=F-P_Y\). The coefficients of \(P_Y\) vanish outside \(S<n\leq Y\) and have modulus at most \(|a_n|\). The mean-value inequality and (4) give, with \(b=1-2u\),
\[
 \int_{I^*}|P_Y(v_0+it)|^2dt\ll S^{b}+Y^b. \tag{6}
\]
The length term uses \(n>S\). For the spacing term, the second estimate in (4) improves \(Y^b\) to \(Y^b/(1+bL)\). Sum dyadic blocks backwards from \(Y\) down to \(S\), bounding each by \(O((Y2^{-j})^b/L)\). The geometric sum and the first bound in (4) give the minimum of \(O(Y^b/(bL))\) and \(O(Y^b)\).

For the remainder put \(D(z)=\int\phi(r)e^{-rz/u}dr\). Smoothed Perron inversion on \(\Re z=c\), \(v_0+c>1\), expresses \(P_Y(s)\) as the integral of \(F(s+z)Y^zD(z)/z\) divided by \(2\pi i\). Move to \(\Re z=-u\). The pole at zero contributes \(F(s)\). The pole at \(1-s\) contributes \((\operatorname{Res}_{w=1}F(w))Y^{1-s}D(1-s)/(1-s)\) (zero if removable). On the new line
\[
 |D(-u+i\tau)/(-u+i\tau)|\ll_j u^{-1}(1+|\tau|/u)^{-j}
\]
by integration by parts against \(\phi(r)e^r\). The kernel has \(L^1\) norm \(O(Y^{-u})\) with the factor \(Y^z\) included. For \(|\tau|\leq S/4\), shifts of \(I^*\) lie inside \([2S/3,3S]\) for large \(S\). Use Minkowski and (5). For larger translations the fixed divisor bounds on \(M,Q\) and polynomial vertical-strip growth of \(\zeta\) bound \(F(1/2+i(t+\tau))\) by a fixed polynomial in \(S+|\tau|\). Integrating the kernel with arbitrarily large \(j\) makes that tail \(O_A(S^{-A})\). At \(z=1-s\), \(\Re z\geq0\), \(|z|\asymp S\), and integration by parts gives \(|D(z)|\ll_j(u/|z|)^j\). The pole residue, including \(M(1)Q(1)\), is \(O_A(S^{-A})\). The same decay allows the contour shift using horizontal segments tending to infinity away from the pole. Therefore
\[
 \int_{I^*}|R_Y(v_0+it)|^pdt\ll S Y^{-pu}+O_A(S^{-A}). \tag{7}
\]

## 5. The optimal cutoff and the count

Set \(G=1-F^2=(\zeta M Q)(2-\zeta M Q)\). Since \(p=4/3\), the elementary inequality
\[
 \log^+|G|\leq\log(1+2|P_Y|^2)+\log(1+2|R_Y|^2)
 \ll |P_Y|^2+|R_Y|^p
\]
uses exactly the two available moments. Take \(Y=S^{1/\kappa(u)}\). It lies between \(S\) and \(S^{3/2}\), and
\[
 Y^{1-2u}=S Y^{-pu}=S^{E(u)},\qquad S^{1-2u}\leq S^{E(u)} .
\]
Equations (6) and (7) bound the integral of \(\log^+|G|\) by \(O(S^{E(u)})\). For (2), put \(B_u=1+(1-2u)L\) and choose \(Y=(S B_u)^{1/\kappa(u)}\leq S^3\) for large \(S\). Then \(Y^{1-2u}/B_u=S Y^{-pu}=S^{E(u)}B_u^{-pu/\kappa(u)}\). The ratio of \(S^{1-2u}\) to this common term equals
\[
 \exp\{(u/\kappa(u))[p\log(1+x)-(2-p)x]\},\qquad x=(1-2u)L .
\]
It is uniformly bounded because the bracket is bounded above on \([0,\infty)\).

If \(dL\leq2\), Riemann–von Mangoldt gives \(N_+\ll SL\), sufficient for both bounds since \(E(0)=1\), \(|E'|\leq3\), and \(d\log(1+L)=O(1)\). Otherwise choose a regular vertical edge \(v_0\in(\sigma-1/L,\sigma-1/(2L))\), giving \(u>1/L\), and horizontal edges inside \((S-1,S)\), \((2S,2S+1)\) missing zeros of \(G\). Every target zero is a zero of \(G\) with at least its original multiplicity and has weight \(\beta-v_0\geq1/(2L)\).

At the right edge \(K=4\), the gap and divisor majorant give \(|F(4+it)|\ll S^{-2}\) (e.g. use absolute convergence of the majorant at 2). The right integral of \(\log|G|\) is \(O(S^{-3})\). For a horizontal edge at height \(t\), the analytic function \(z\mapsto[G(z+it)+\overline{G(\bar z+it)}]/2\) is bigger than \(1/2\) at 4 and bounded in modulus by \(S^{O(1)}\) on the disk of radius 5 about 4. Its possible poles are outside the disk. Jensen gives \(O(L)\) zeros on the concentric disk of radius 4, which contains the horizontal segment. Between real zeros of this function the argument of \(G\) varies within a half-plane. With the branch initialized at the right edge, \(|\arg G|\ll L\) on both caps. Littlewood’s rectangle lemma now bounds the weighted sum by the left integral of \(\log^+|G|\) plus \(O(L)\).

The shift from \(u\) to \(d\) costs a constant since \(|E'|\leq3\), \(|d-u|\leq1/L\), \(B_u\geq B_d\), and the derivative of \(px/\kappa(x)\) is bounded on \([0,1/2]\). Hence the change of power on \(B_d\leq1+L\) costs at most \((1+L)^{O(1/L)}\). Finally, if the target count is positive, the Vinogradov–Korobov zero-free region gives \(1-\sigma\gg L^{-2/3}(\log L)^{-1/3}\). Since \(E(d)\geq2(1-\sigma)\) and \(pd/\kappa(d)\leq1\), even the refined main factor \(S^{E(d)} B_d^{-pd/\kappa(d)}\) dominates \(L\). If the count is zero the conclusions hold directly. Multiplication by \(2L\) proves (1) and (2), uniformly through both ends of the range.

## Consequence and formal status

The inequality \(E(d)\leq1-4d/3\) and dyadic summation give the global one-logarithm Selberg bound of slope \(4/3\). The linear exponent is at least \(1/3\), so the dyadic series is uniformly geometric. This is one finite slope. The repository criterion for RH requires arbitrarily large slopes.

[ActualDyadicInghamDetector.lean](Analysis/ActualDyadicInghamDetector.lean) formalizes both exact cutoff balances, the cost of shifting the threshold, the total-count argument at the critical line, and the conversion of the detector excess and zero-free cap to (1). The classical proofs of (3)–(7), the detector’s Littlewood inequality and the cap input are given above. They are not supplied as kernel-checked terms in this module. No new mathematical axiom is used to insert (1) or (2).

## Sources

- rStation Paper 184, v1, Theorem 1 and §§2–4, [paper and source record](https://rstation.ai/problems/riemann_hypothesis/papers/184).
- S. A. C. Baluyot, *On the zeros of Riemann’s zeta-function on the critical line*, formula (1.4), Theorem 1.3 and Corollary 1.2, [author’s paper](https://sieg-baluyot.github.io/criticalline.pdf).
- H. L. Montgomery and R. C. Vaughan, *Hilbert’s inequality*, J. London Math. Soc. (2) 8 (1974), 73–82, [DOI](https://doi.org/10.1112/jlms/s2-8.1.73).
- M. J. Mossinghoff, T. S. Trudgian and A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, Theorem 1.1, [preprint](https://arxiv.org/abs/2212.06867).
