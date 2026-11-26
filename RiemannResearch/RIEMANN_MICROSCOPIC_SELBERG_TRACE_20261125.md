# The Selberg prime covariance and the fixed-width pair-correlation problem

Take all nontrivial zeros \(\rho=\beta+i\gamma\) with \(0<\gamma\le T\), including their analytic multiplicities. Write \(L=\log T/(2\pi)\). For a fixed positive width \(q\), ordinary pair correlation asks whether
\[
  P_T(q)=\frac{1}{TL}\#\{(i,j):0<L(\gamma_j-\gamma_i)\le q\}
  \longrightarrow G(q)=\int_0^q\left[1-
  \left(\frac{\sin(\pi u)}{\pi u}\right)^2\right]du .
\]
It suffices to test positive rational widths. The equivalent conventional argument-variance criterion uses \(S(t)=\arg\zeta(1/2+it)/\pi\) with the continued argument and \(h=q/L\). Write \(\delta_hf(t)=f(t+h)-f(t)\). The required limit of \(T^{-1}\int_0^T(\delta_h S)^2 dt\) is
\[
 V_{\sin}(q)=V_{\rm low}(q)+V_{\rm high}(q),\qquad
 V_{\rm low}(q)=\frac1{\pi^2}\int_0^1\frac{1-\cos(2\pi qx)}x\,dx,
 \quad V_{\rm high}(q)=\frac1{\pi^2}\int_1^\infty\frac{1-\cos(2\pi qx)}{x^2}\,dx .
\]
The interval variance counts coincident occurrences. The equivalence with the strict positive-gap formulation uses the horizontal multiplicity consequence of PCC and the triangle identity. [Fixed-width variance criterion and proof](RIEMANN_SIGNED_PRIME_PROBE_CESARO_20261125.md#what-remains-at-a-fixed-width) · [Goldston, Lee, Schettler and Suriajaya, §§4–8](https://arxiv.org/html/2503.15449v4)

For the full Selberg polynomial, the following calculation identifies its mixed term with an explicit signed sum over off-line zeros. For a prime cutoff \(y\to\infty\) with \(\log y=o(\log T)\), a second calculation determines the actual covariance with this part of the polynomial. A third result bounds the fixed-width count coming from pairs with many intervening occurrences. The proofs of these estimates impose no hypothesis on the zeros' real parts.

## The mixed term as a signed trace of horizontal displacement

Let \(\ell=\log T,\ L=\ell/(2\pi),\ h=q/L\), and write
\(\langle f,g\rangle_T=T^{-1}\int_0^T f(t)g(t)\,dt\) and
\(\delta_h f(t)=f(t+h)-f(t)\). Put
\[
 X(t)=-\pi^{-1}\sum_{p\le2T}\frac{\sin(t\log p)}{\sqrt p},
 \qquad Y=S-X.
\]
Sum over all nontrivial zero occurrences with \(0<\gamma\le T\), repeating their analytic multiplicities. Define the real finite sum
\[
 H_T(q)=\frac{2}{\pi T}\sum_{p\le2T}
  \frac{1-\cos(h\log p)}{\sqrt p\,\log p}
  \sum_{\rho=\beta+i\gamma}
       [\cosh((\beta-\tfrac12)\log p)-1]\cos(\gamma\log p).
\]

**Theorem.** For each fixed \(q>0\),
\[
 \langle\delta_hX,\delta_hY\rangle_T=H_T(q)+o_q(1).
\]
Uniformly for \(0<q\le1\) the error is \(O(q^2\log(2\ell)/\ell)\). In particular the full fixed-width remainder criterion can be written
\[
 \|\delta_hY\|_T^2+2H_T(q)\longrightarrow V_{\rm high}(q)
 \quad(q\in\mathbb Q,\ q>0).
\]
The bracketed factor vanishes on the critical line. Its cosine multiplier carries a sign.

**Proof.** Denote by \(X_M\) the same polynomial stopped at \(M\le2T\). With \(a=\log p\), integrating a single occurrence through its window gives the exact identity
\[
 \int_{\gamma-h}^{\gamma}[\sin((t+h)a)-\sin(ta)]dt
 =2\frac{1-\cos(ha)}{a}\cos(a\gamma).
\]
Extending these windows past the cutoff changes the normalized integral by
\(O(q^2/(\sqrt T\,\ell))\) for bounded \(q\). Indeed the first positive ordinate eventually exceeds \(h\), and \((T,T+h]\) contains \(O(\log T)\) occurrences by Riemann–von Mangoldt. Their cut windows have length at most \(h\) and
\(\|\delta_h X_M\|_\infty\ll h\sum_{p\le2T}(\log p)/\sqrt p\ll h\sqrt T\).
Almost everywhere the zero count equals \(S(t)+1+\vartheta(t)/\pi\) with the classical Riemann–Siegel theta function. Its smooth increment on \([0,T]\) has supremum and total variation \(O(q)\), since \(\vartheta'(t)=O(\log(2+t))\) and \(\vartheta''(t)=O((1+t)^{-1})\). The primitive of \(\delta_hX_M\) is bounded by \(2h\|X_M\|_\infty\ll h\sqrt T/\ell\), by subtraction of two integrals of length \(h\). Integration by parts bounds the normalized smooth pairing by \(O(q^2/(\sqrt T\,\ell^2))\). Consequently
\[
 \langle\delta_h S,\delta_h X_M\rangle_T
 =-\frac{2}{\pi T}\sum_{p\le M}
   \frac{1-\cos(h\log p)}{\sqrt p\log p}
       \sum_{\rho}\cos(\gamma\log p)+O\!\left(\frac{q^2}{\sqrt T\,\ell}\right).
\]

For \(M=2T\), symmetry under \(\rho\mapsto 1-\bar\rho\) gives
\[
 \Re\sum_{\rho} p^{\rho-1/2}
   = \sum_{\rho}\cosh((\beta-\tfrac12)\log p)\cos(\gamma\log p).
\]
Gonek's uniform Landau formula evaluates the left side at every prime \(p\le2T\) as
\(-T\log p/(2\pi\sqrt p)+O(\sqrt p\,\ell\log(2\ell))\).
In Theorem 1, equation (3), the distance from the integer \(p\) to the nearest other prime power is at least 1. All three error terms obey the asserted upper bound after division by \(\sqrt p\). Since \(1-\cos(h\log p)\le h^2(\log p)^2/2\), the total error in the normalized real pairing is
\[
 \ll \frac{q^2\log(2\ell)}{T\ell}\sum_{p\le2T}\log p
 \ll q^2\frac{\log(2\ell)}{\ell}.
\]
Therefore
\[
 \langle\delta_h S,\delta_h X\rangle_T
 =\pi^{-2}\sum_{p\le2T}(1-\cos(h\log p))/p+H_T(q)
   +O\!\left(q^2\frac{\log(2\ell)}{\ell}\right).
\]
[Gonek, Theorem 1, equation (3)](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf)

Finally the Montgomery–Vaughan mean-value theorem applied to \(\delta_hX\) gives
\[
 \|\delta_hX\|_T^2=\pi^{-2}\sum_{p\le 2T}\frac{1-\cos(h\log p)}p+O(q^2/\ell)
 \quad(0<q\le1).
\]
The conjugate error is \(O(q^2\pi(2T)/T)\); the nonconjugate error is \(O(q^2(\sum_{p\le2T}p^{-1/2})^2/T)=O(q^2/\ell^2)\). Subtracting this energy from the full mixed pairing finishes the proof. The argument holds with constants depending on a fixed larger width. [Goldston, Dirichlet polynomial mean-value estimate (4.6)](https://arxiv.org/pdf/math/0412313)

## Covariance with short prime sums at actual zero ordinates

Put \(L=\log T/(2\pi)\), \(h=q/L\), \(\Delta f(t)=f(t+h)-f(t)\), and define the uncentered increment product
\[
   \langle f,g\rangle_{T,q}=T^{-1}\int_0^T\Delta f(t)\Delta g(t)\,dt.
\]
Write \(S(t)=\pi^{-1}\arg\zeta(1/2+it)\),
\(X_y(t)=-\pi^{-1}\sum_{p\le y}p^{-1/2}\sin(t\log p)\), and \(Y_T=S-X_{2T}\).
Endpoint conventions for \(S\) affect sets of measure zero. All sums over zeros count occurrences with multiplicity.

**Theorem.** Suppose \(\eta=\eta_T\to0\), \(\eta\log T\to\infty\), and put \(y=T^\eta\). For \(b=q\eta>0\) define
\[
 V(b)=\pi^{-2}\int_0^1\frac{1-\cos(2\pi b u)}u\,du,\qquad m(b)=\min(1,b^2).
\]
For every sequence \(0<h=q/L\to0\), the two covariance limits are
\[
 \frac{\langle S,X_y\rangle_{T,q}-V(b)}{m(b)}\longrightarrow0,
 \qquad
 \frac{\langle X_{2T},X_y\rangle_{T,q}-V(b)}{m(b)}\longrightarrow0 .
\]
The true remainder satisfies a uniform orthogonality estimate on the larger interval \(0<h\le1\),
\[
  \sup_{0<q\le L}\frac{|\langle Y_T,X_y\rangle_{T,q}|}{m(q\eta)}
   \longrightarrow0 .
\]
In particular, both covariance products divided by \(q^2\eta^2\) tend to one uniformly for \(0<q\le1\). If \(b\to\lambda>0\) with \(\lambda\) finite, both converge to \(V(\lambda)>0\). The formulas also give an absolute \(o(1)\) error for \(b\to\infty\) provided \(h\to0\).

For the full prime cutoff the following bounds hold uniformly for \(0<q\le1\),
\[
  |\langle S,X_{2T}\rangle_{T,q}|+\langle X_{2T},X_{2T}\rangle_{T,q}\ll q^2,
  \qquad
  |\langle Y_T,Y_T\rangle_{T,q}-\langle S,S\rangle_{T,q}|\ll q^2 .
\]
In particular, for every \(q_T\to0\) with \(q_T>0\),
\(\liminf_T\langle Y_T,Y_T\rangle_{T,q_T}/q_T\ge1\).
These estimates control a shrinking fraction of the prime spectrum and the first-order small-width error. The microscopic sine variance at a prescribed positive width still requires an asymptotic for the full remainder.

### Sampling and an ordinate trace

Set \(x=Lt\), \(H=TL\), \(g=L\gamma\), \(F_y(x)=X_y(x/L)\), and \(\ell_p=\log p/\log T\). Let \(n_k\) count scaled ordinates in \([k,k+1)\) up to \(H+2\). Fujii's short-window fourth moment implies \(\sum_k n_k^4\ll H\), hence \(\sum_k n_k^2\ll H\). For each cell, every length-two window starting in the preceding cell contains that cell, up to measure-zero endpoints. Integrating the fourth power of the window count proves the stated cell bound, with the initial empty cell and end handled by extending the height by \(O(1/L)\). [Fujii's estimate as stated and applied in Lamzouri, Lemmas 2.2–2.3](https://arxiv.org/html/2611.14486v1)

The Dirichlet-polynomial mean-value inequality gives
\(\int_{-3}^{H+3}|F_y^{(m)}(x)|^2dx\ll_m H\) for fixed \(m\ge1\) and \(y\le2T\).
Indeed, the sum of squared coefficients is
\(\ll_m \sum_{p\le2T}\ell_p^{2m}/p\ll_m1\) by partial summation and Chebyshev's bound. Local Sobolev on intervals of bounded overlap yields \(\sum_k\sup_{[k-1,k+2]}|F_y'|^2\ll H\). The same holds for each fixed higher derivative. [Montgomery–Vaughan mean-value inequality, Ivić, Theorem 5.2](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf)

For the full-cutoff estimates, take \(0<q\le1\) and let \(K(x)=\#\{g:x<g\le x+q\}\). Each ordinate contributes to \(K\) on an interval of length at most \(q\), where \(|F_y(x+q)-F_y(x)|\le q\sup|F_y'|\) on its enlarged cell. Cauchy–Schwarz now gives
\[
 H^{-1}\int_0^H K(x)|F_y(x+q)-F_y(x)|\,dx\ll q^2.
\]
The Riemann–von Mangoldt identity gives \(\Delta S=K-\Delta_q M\) almost everywhere, where \(M(x)=1+\vartheta(x/L)/\pi\) and \(\vartheta\) is the Riemann–Siegel theta function. Stirling's formula gives \(\|M'\|_\infty+\int_0^{H+L+2}|M''|\ll1\). Also \(H^{-1}\int|\Delta_q F_y|^2\ll q^2\), by the derivative bound. These inequalities give both full-cutoff bounds by expanding the square. For the last liminf, \(K^2\ge K\) and
\[
 H^{-1}\int_0^H K\,dx = qN(T)/H+O(q\log T/H)
                       = q(1+O(1/\log T)).
\]
Here at most \(O(\log T)\) zeros can affect the top boundary. The drift bound \(|\Delta_q M|\ll q\) therefore gives \(\langle S,S\rangle_{T,q}\ge q(1-O(1/\log T))-O(q^2)\).

For a more precise identity, each interior ordinate contributes exactly
\[
   \int_{g-q}^{g}\big(F_y(x+q)-F_y(x)\big)\,dx
       =\int_{-q}^{q}(q-|v|)F_y'(g+v)\,dv .
\]
For the trace identity take \(0<q\le L\), so the physical distance \(h\le1\). Only \(O(1)\) ordinates can affect the bottom boundary, and \(O(\log T)\) can affect the top by the unit-interval Riemann–von Mangoldt bound. Replacing the top truncated intervals by the sum over \(0<g\le H\) costs \(O(q^2\log T\sqrt T/H)\) after normalization, since \(\|F_y'\|_\infty\ll\sqrt T\). For the smooth drift, expand both differences as integrals of derivatives over \([0,q]\) and integrate \(\int_0^H M'(x+u)F_y'(x+v)dx\) by parts in \(x\). The preceding bounds on \(M\) and \(\|F_y\|_\infty\ll\sqrt T\) give \(O(q^2\sqrt T/H)\) after normalization. Thus, with \(s(z)=\sin(z)/z\) and \(s(0)=1\),
\[
 \langle S,X_y\rangle_{T,q}
 =-\frac{2q^2}{H}\sum_{0<\gamma\le T}\sum_{p\le y}
      \frac{\ell_p}{\sqrt p}\,s(\pi q\ell_p)^2\cos(\gamma\log p)
    +O(q^2T^{-1/2}).
 \tag{1}
\]
The error keeps its factor \(q^2\) even for arbitrarily small positive \(q\).

### Removing horizontal weights on a shrinking prime band

Put \(v_\rho=|\beta-1/2|\log T\). Define
\[
 B_y(q)=2q^2\sum_{p\le y}\frac{\ell_p^2}{p}s(\pi q\ell_p)^2 .
\]
In the double sum in (1), insert \(\cosh(v_\rho\ell_p)\) next to the cosine. By \(\rho\leftrightarrow1-\overline\rho\), the resulting zero trace is \(p^{-1/2}\Re\sum_{0<\gamma\le T}p^\rho\). Gonek's uniform Landau formula evaluates this last sum before taking the real part as \(-T\log p/(2\pi)+O(p\log^2 T)\) for primes \(p\le T\). Thus the horizontally weighted expression equals \(B_y(q)+O(q^2y\log^2 T/T)\). [Gonek, A Formula of Landau and Mean Values of ζ(s), Theorem 1](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf)

It suffices to take \(0<\eta\le1/32\) and \(y\ge2\). Let \(n_{k,j}\) count zeros in cell \(k\) with \(j\le v_\rho<j+1\), up to height \(T\). By symmetry and Selberg's uniform density bound,
\(\sum_k n_{k,j}\ll H e^{-j/4}\). Interpolating this \(\ell^1\) bound with \(\sum_k n_{k,j}^4\ll H\) gives \(\sum_k n_{k,j}^2\ll H e^{-j/6}\). [Ford–Zaharescu, Lemma 2](https://ford126.web.illinois.edu/wwwpapers/fz.pdf)

Define the real polynomial in \(x\) with real parameter \(v\) by
\[
 P_v(x)=\sum_{p\le y}\frac{\ell_p}{\sqrt p}s(\pi q\ell_p)^2
   (\cosh(v\ell_p)-1)\cos(2\pi\ell_p x).
\]
For \(j\le v\le j+1\), the coefficients of \(q^2P_v\) and its derivatives \(\partial_x,\partial_v,\partial_x\partial_v\) have absolute value at most a constant times
\[
 (j+1)^2 e^{\eta(j+1)}
       \frac{\min(q^2\ell_p^3,\ell_p)}{\sqrt p}.
\]
This follows from \(\cosh z-1\ll z^2e^{|z|}\), \(|\sinh z|\ll |z|e^{|z|}\), \(\ell_p\le\eta\), and \(q^2s(\pi q\ell_p)^2\ll\min(q^2,\ell_p^{-2})\). The derivatives leave this last factor intact. For \(d=2,6\), partial summation with Chebyshev's bound gives \(\sum_{p\le y}\ell_p^d/p\ll_d\eta^d\). Apply the mean-value inequality in \(x\), integrate in \(v\), and use one-dimensional Sobolev successively in each variable on the unit rectangles. The result is
\[
 \sum_k \sup_{[k,k+1]\times[j,j+1]}|q^2P_v(x)|^2
    \ll H\min(q^2\eta^3,\eta)^2(j+1)^4e^{2\eta(j+1)} .
\]
Cauchy–Schwarz against \(n_{k,j}\), followed by summation in \(j\), gives
\[
 \frac1H\sum_{0<\gamma\le T}|q^2P_{v_\rho}(L\gamma)|
    \ll \min(q^2\eta^3,\eta)\sum_{j\ge0}(j+1)^2e^{-j/12+\eta(j+1)}
    \ll \eta\,m(q\eta).
\]
Consequently, for \(0<q\le L\),
\[
 \langle S,X_y\rangle_{T,q}
    = B_y(q)+O\!\left(\eta\,m(q\eta)+q^2[T^{-1/2}+y\log^2 T/T]\right).
 \tag{2}
\]

### The prime–prime product

Let \(a_p=(e^{ih\log p}-1)/\sqrt p\) for \(p\le2T\) and \(b_p=a_p\mathbf1_{p\le y}\).
The product of imaginary parts gives half the real part of the conjugated product minus half the real part of the unconjugated product. The conjugated diagonal, including the \(1/\pi^2\) normalization, is exactly \(B_y(q)\). The bilinear mean-value error after division by \(T\) is
\[
  \ll T^{-1}\Big(\sum_p p|a_p|^2\sum_p p|b_p|^2\Big)^{1/2}
    \ll q^2\sqrt{y/T}.
\]
The bilinear bound follows by polarizing the quadratic mean-value error on the weighted space with squared norm \(\sum n|a_n|^2\), then rescaling the two arguments. For the unconjugated term, \(|\int_0^T(pr)^{it}dt|\le2/\log(pr)\) and \(\sum_{p\le u}|a_p|\ll q\sqrt u\), giving the same bound. It follows that
\[
   \langle X_{2T},X_y\rangle_{T,q}=B_y(q)+O(q^2\sqrt{y/T}).
 \tag{3}
\]
For \(0<q\le L\) we have \(q^2/m(q\eta)\le\max(\eta^{-2},L^2)\ll(\log T)^2\) eventually. All power-saving terms in (2) and (3) are therefore \(o(m(q\eta))\), uniformly on this interval. Subtracting the two estimates proves the asserted uniform bound for \(\langle Y_T,X_y\rangle_{T,q}\).

To evaluate the common diagonal for \(h\to0\), use the exact equality
\[
 B_y(q)=\pi^{-2}\sum_{p\le y}\frac{1-\cos(h\log p)}p .
\]
The classical prime number theorem with error gives \(\pi(u)-\operatorname{Li}(u)\ll u/(\log u)^4\) for \(u\ge2\). Against \(f(u)=(1-\cos(h\log u))/u\), the partial summation endpoint at \(y\) is \(O(h^2)\), since \(1-\cos(h\log y)\le h^2(\log y)^2/2\). The integral error is \(O(h^2)\) uniformly in \(y\) because
\[
 |f'(u)|\ll \frac{h^2(\log u+(\log u)^2)}{u^2},
 \qquad
 \int_2^\infty\frac{\log u+(\log u)^2}{u(\log u)^4}\,du<\infty .
\]
The lower endpoint and the omitted integral over \(0\le v\le\log 2\) in logarithmic coordinates each cost \(O(h^2)\). Thus \(B_y(q)=\pi^{-2}\int_0^{\log y}(1-\cos(hv))\,dv/v+O(h^2)=V(q\eta)+O(h^2)\). For \(q\eta\le1\) we have \(h^2/m(q\eta)=(L\eta)^{-2}\to0\), and for \(q\eta>1\) this ratio equals \(h^2\). The two covariance limits follow for every \(h\to0\). Finally \(V(b)=b^2+O(b^4)\) at zero, giving the fixed-width normalization. [Classical PNT error, Vaughan, The Prime Number Theorem](https://personal.science.psu.edu/rcv4/571s25/Class571-03.pdf)

## Truncating positive pairs by index distance

List the positive zero ordinates through \(T\) as \(\gamma_1\le\cdots\le\gamma_{N(T)}\), retaining multiplicity. Put \(L=\log T/(2\pi)\) and \(D=TL\). For \(j\ge1\), let \(F^+_{j,T}(q)\) be \(D^{-1}\) times the number of indices \(i\) with \(i+j\le N(T)\) and \(0<L(\gamma_{i+j}-\gamma_i)\le q\). The strictly positive pair count is \(P_T(q)=\sum_{j\ge1} F^+_{j,T}(q)\). These index distances refer to the full occurrence list, including tied ordinates.

For fixed \(q>0\) and every integer \(m\ge1\),

$$
0\le P_T(q)-\sum_{j=1}^J F^+_{j,T}(q)\ll_{q,m}J^{-m}
$$

uniformly for sufficiently large \(T\) and \(J\ge1\). Indeed, set

$$
M_i=\#\{a: L|\gamma_a-\gamma_i|\le q\},\qquad
H_i=\sum_a(1+((\gamma_a-\gamma_i)\log T)^2)^{-1}.
$$

Then \(M_i\le(1+4\pi^2q^2)H_i\). If an admissible pair starts at \(i\) and has \(j>J\), all intermediate occurrences lie in the same interval, so \(M_i>J\). Its starting index contributes at most \(M_i\mathbf1_{M_i>J}\le J^{-m}M_i^{m+1}\) to the unnormalized tail. Lamzouri's Lemma 2.3 gives \(\sum_iH_i^{m+1}\ll_m N(T)\), and \(N(T)/D\to1\). The same proof bounds the tail if equal-ordinate pairs are included. [Lamzouri, Lemma 2.3](https://arxiv.org/pdf/2611.14486)

In fact the error is \(\ll_q e^{-c_q J}\) for some \(c_q>0\). Set \(b=1/L\) and \(K_v(t)=N(t+v)-N(t)\). On every dyadic block \([A,2A]\) with sufficiently large \(A\le T+1\), Lemma 8 of Simonič–Trudgian–Turnage-Butterbaugh at \(\eta=1\) gives an exponential tail for \(|\Delta_vS|\) at \(v=4\pi/\log(A/(2\pi))\). Here \(b\le v\), the smooth counting-term increment is bounded absolutely, and \(K_b\le K_v\). Summing the blocks and absorbing the finite counts at bounded heights gives
\[
|\{0\le t\le T+1:K_b(t)\ge x\}|\ll T e^{-a x}.
\]
For \(h=qb\), cover a window of length \(2h\) by \(\lceil2q\rceil\) consecutive windows of length \(b\). The union bound gives \(|\{0\le t\le T:K_{2h}(t)\ge x\}|\ll_q T e^{-a_q x}\). Each pair of span at most \(h\) and rank greater than \(J\) lies in windows of width \(2h\) for at least \(h\) units of starting time. These windows have \(K_{2h}>J\). The normalized tail is bounded by \((hD)^{-1}\int_0^T K_{2h}^2\mathbf1_{K_{2h}>J}\,dt\), which gives the asserted exponential estimate by integration of the tail. [Simonič–Trudgian–Turnage-Butterbaugh, Lemmas 7–8](https://arxiv.org/pdf/2010.10675)

There is also a uniform deletion estimate. If a subset of occurrences of size \(\delta D\) is removed, the normalized number of affected pairs of span at most \(Q/L\) is \(O_Q(\delta\log(e/\delta))\) for \(0<\delta\le1\). Indeed, a deleted occurrence meets at most \(2J\) distinct indices of rank distance at most \(J\), and the entire remaining rank tail costs \(O_Q(e^{-c_QJ})\). Take \(J=\max(1,\lceil c_Q^{-1}\log(1/\delta)\rceil)\). The argument includes tied distinct occurrences. Restoring both orders doubles the bound, and self-pairs cost at most \(\delta\). Multiplying by a bounded triangle weight costs its supremum. Applying this to a projection still requires control of the fraction deleted.

### The prime projection with every self-pair restored

For the repository's prime-frequency projection, one label is selected per distinct ordinate. Consequently every realization deletes exactly \(d_TD\) occurrences, with
\[
 d_T=\frac{N(T)-\#\{\gamma:0<\gamma\le T\}}{D}.
\]
Let \(I=[a,b]\) with \(0<a<b\), and let \(\ell_T(I)\) be the expected loss in the ordered, self-pair-restored sum with weight \(w_I(u)=\int_a^b(r-|u|)_+\,dr\), divided by \(D\). For sufficiently large \(T\),
\[
  (b^2-a^2)d_T\ \le\ \ell_T(I)\
        \ll_I d_T\log(e/d_T).
\]
The upper bound uses the deletion estimate at \(Q=b\), with \(\sup w_I=(b^2-a^2)/2\), applied before taking the expectation. The upper bound is interpreted as zero at \(d_T=0\). For the lower bound, an ordinate of multiplicity \(m\) loses all \(m(m-1)\) ordered pairs of distinct occurrences at that height. Each has weight \(w_I(0)\), and \(m(m-1)\ge 2(m-1)\). Summing gives the lower bound without making any assumption on positive gaps.

Thus vanishing of loss on any one such interval, vanishing on all such intervals, and \(d_T\to0\) are equivalent. In particular the estimates control every omitted equal-ordinate pair once the vacancy fraction vanishes. Showing \(d_T\to0\) for the actual zeros is still an arithmetic obligation. Even its vanishing leaves the restored positive-spacing law to be identified. [Repository's finite projection identity](Analysis/ZeroDPPProjectionBridge.lean) · [Collision contribution](Analysis/ZeroDPPCollisionLoss.lean) · [Vacancy and density-one criterion](Analysis/ZeroDPPVacancyDensity.lean)

### Finite index distances and the remaining positive-gap law

Write \(G(q)=\int_0^q[1-(\sin(\pi u)/(\pi u))^2]\,du\). The positive-gap PCC criterion is equivalently

$$
\lim_{J\to\infty}\limsup_{T\to\infty}
\left|\sum_{j=1}^J F^+_{j,T}(q)-G(q)\right|=0
$$

at every positive rational \(q\). The reverse triangle inequality bounds the difference between the inner limsup and \(\limsup_T|P_T(q)-G(q)|\) by the displayed tail estimate. Identifying the aggregate of the finite-index gap laws remains open.

## A lower bound from short consecutive gaps

Let \(K=N(t+q/L)-N(t)\), with \(t\) uniform on \([0,T]\), and put \(W_T(q)=\mathbb E|\Delta_{q/L}S(t)|^2\). For fixed \(q\), Riemann–von Mangoldt and the Gallagher–Mueller second-moment identity give \(\mathbb E K=q+o(1)\) and \(\mathbb E K^2=q^2+W_T(q)+o(1)\). Thus, for \(k=\lfloor q\rfloor\) and \(r=q-k\),

$$
W_T(q)=r(1-r)+\mathbb E[(K-k)(K-k-1)]+o(1).
$$

The product is nonnegative for every integer count. For \(0<\beta<q\le1\), let \(d(\beta)\) be the liminf proportion of consecutive occurrence gaps at most \(\beta/L\). Every such pair with both endpoints below \(T\) lies in a moving window for at least \((q-\beta)/L\) units of starting time. For large \(T\) the first ordinate exceeds \(q/L\). Counting both orders in \(K(K-1)\) therefore gives

$$
\liminf_{T\to\infty}W_T(q)\ge q(1-q)+2(q-\beta)d(\beta).
$$

Distinct occurrences at the same height contribute here. Lamzouri's Theorem 1.1 gives \(d(0.7892)>0\) unconditionally. The repository's degree-285 theorem gives \(d(0.784782678)>0\) with the explicit Lean input **LamzouriCompactDeletion2026**. The variance lower bound transfers under this input. [Goldston–Lee–Schettler–Suriajaya, Proposition 1](https://arxiv.org/pdf/2503.15449) · [Lamzouri, Theorem 1.1](https://arxiv.org/pdf/2611.14486) · [Degree-285 Lean theorem](https://github.com/Cnoack3/RiemannResearch/blob/91f07fdffb60bc8a9b820800dbfa3ef33b14278d/RiemannResearch/Analysis/LamzouriGap285Certified.lean)

## A comparison process with the same leading width averages

Fix \(0<a\le1/2\). Take the translation-invariant determinantal process on \(\mathbb Z\) with kernel \(k_0=a,\ k_j=\sin(\pi a j)/(\pi j)\) for \(j\ne0\). Scale the occupied sites by \(a\) and add an independent uniform shift in \([0,a)\). The kernel is the Fourier projection onto an interval of length \(a\) in \(\mathbb R/\mathbb Z\). The scaled process has intensity one. Let \(P_a(q)\) be its mean number of positive pairs per unit length with gap at most \(q\). Then \(P_a(q)=0\) on \(0<q<a\). Its full pair measure, including self-pairs, is
\[
 \delta_0+a\sum_{j\in\mathbb Z}
 \left[1-\left(\frac{\sin(\pi a j)}{\pi a j}\right)^2\right]\delta_{aj}.
\]
At zero the ratio in brackets uses the continuous extension. By Poisson summation the Fourier transform is
\(\sum_{m\in\mathbb Z}\delta_{m/a}+1-\sum_{m\in\mathbb Z}(1-|\xi-m/a|)_+\).
It agrees with the full sine pair measure in frequency on \(|\xi|<1/a-1\). [Lagarias and Rodgers, the discrete sine process](https://arxiv.org/abs/1905.12123)

There is also a quantitative agreement for the integrated positive-gap counts. As \(Q\to\infty\), with \(\tau=\{Q/a\}\),
\[
 \frac{2}{Q}\int_0^Q[P_a(q)-G(q)]\,dq
 =\frac{\pi^{-2}\log\!\big(\sin(\pi a)/(\pi a)\big)+a^2\tau(1-\tau)}{Q}
   +O_a(Q^{-2}).
\]
To see this, the variance over \(n\) consecutive lattice sites is
\[
 v_n=\frac{2}{\pi^2}\left(\sum_{1\le j<n}\frac{\sin^2(\pi aj)}j+
                    n\sum_{j\ge n}\frac{\sin^2(\pi aj)}{j^2}\right)
 =\frac{\log n+\gamma_E+\log(2\sin(\pi a))+1}{\pi^2}+O_a(n^{-1}).
\]
The first equality follows from the determinantal site covariances and \(\sum_{j\in\mathbb Z}|k_j|^2=k_0\). For the second, expand the squared sine and use \(\sum_{j\ge1}\cos(2\pi a j)/j=-\log(2\sin(\pi a))\). Bounded partial sums of the cosines control both tails. With \(n=\lfloor Q/a\rfloor\), conditioning on the random shift gives the variance \((1-\tau)v_n+\tau v_{n+1}+a^2\tau(1-\tau)\). Subtract \(V_{\sin}(Q)=(\log(2\pi Q)+\gamma_E+1)/\pi^2+O(1/Q)\). The triangle identity for a stationary simple process of unit intensity makes this variance difference exactly \(2\int_0^Q(P_a-G)\).

In the signed statistic \(P_a(q)-q+B_T(q)\), keep the same finite von Mangoldt energy \(B_T\) as in the [previous research note](RIEMANN_SIGNED_PRIME_PROBE_CESARO_20261125.md). Its large-width Cesàro average differs from the one using \(G\) by \(O_a(1/Q)\), as does the adjacent-width contrast. At every fixed \(0<q<a\), its limit is \(-G(q)<0\). This example concerns the stationary point process and the specified deterministic prime probe. The covariance calculations for \(\arg\zeta\) above use additional information specific to actual zeros.

## Verification scope

Lean proves the finite chronological decomposition and its eventual variance floor in [MontgomeryAdjacentWindowFloor.lean](Analysis/MontgomeryAdjacentWindowFloor.lean). The positive specialization at unit width uses the scoped compact-deletion hypothesis and the verified degree-285 coefficient replay. The single-ordinate integral and its extension to a finite weighted sine dictionary are proved in [MontgomeryOrdinateSineTrace.lean](Analysis/MontgomeryOrdinateSineTrace.lean). The Fourier trace, the asymptotic covariance and the exponential bound for the index distances are mathematical deductions from the cited analytic theorems. The original fixed-width signed prime-probe equivalence is available in [MontgomeryPrimeProbeEnergy.lean](Analysis/MontgomeryPrimeProbeEnergy.lean). Full unconditional pair correlation would require the displayed fixed-width limit of the actual Selberg remainder and horizontal trace.

Subsequent Lean exports prove the rank-cover inequality, the count-tail-to-exponential-rank transfer and the logarithmic prime-deletion bound under explicit translated-count hypotheses. The unconditional analytic estimate supplying the exponential count tail is the written argument above. [Rank and distinct-ordinate theorem catalog](THEOREM_CATALOG_MONTGOMERY_WINDOW_VARIANCE_20261118.md#occurrence-ranks-distinct-ordinates-and-simple-zero-representatives)
