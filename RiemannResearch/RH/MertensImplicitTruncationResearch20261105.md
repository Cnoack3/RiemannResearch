# Crossing the printed Lee–Leong endpoint

Let \(W=53.99\), \(t=\log x\), \(L=\log t\), and \(U=L-\log W\). Set
\(A=(5/(3W^3))^{1/5}\), \(\Phi=t^{3/5}L^{-1/5}\), and
\(F=A t^{3/5}U^{-1/5}\). All statements about these functions concern sufficiently large positive \(x\).

**Published arithmetic input.** In Lee and Leong, Proposition 5.2, equation (60), set \(y=\log T_x\). With the parameters of §5.4, its equation and inequality (62) give
\[
y^5\log y=(t/W)^3,\qquad |M(x)|\le Kxt\,e^{-y}
\]
for a fixed \(K>0\). On this branch \(y>1\) tends to infinity. The right side of the normalized inequality (62) is \(2e+O((\log y)^{-1/12})+O(y/t)\), hence bounded. Indeed (60) gives \(y/t\to0\). Section 5.4 verifies condition (61) for the chosen \(W\). [Proposition 5.2, equations (60) and (62), and §5.4](https://arxiv.org/html/2208.06141v5)

**Gain available in the exact truncation.** Taking logs gives \(5\log y+\log\log y=3U\), while \(F^5=(5/3)(t/W)^3/U\). Thus
\[
\frac yF=(1-z)^{-1/5},\qquad z=\frac{\log\log y}{3U}.
\]
Here \(\log y\sim3U/5\), since \(\log\log y=o(\log y)\). Consequently \(z\sim \log L/(3L)\), \(F\sim A\Phi\), and
\[
\lim_{x\to\infty}\frac{y-F}{\Phi\log L/L}=\frac A{15}>0.
\]
For the formal transfer even the elementary tangent inequality \((1-z)^{-1/5}\ge1+z/5\) suffices. Eventually \(\log\log y\ge1\), \(0<U<L\), and \(F\ge A\Phi\), so
\[
y-F\ge\frac{A\Phi}{15L}.
\]
Because \(L=o(\sqrt\Phi)\), this lower bound absorbs \(\log K+L+k\sqrt\Phi\) for every fixed real \(k\). We therefore obtain
\[
 |M(x)|\le x\exp(-F-k\sqrt\Phi)
\]
eventually. This saving comes from Proposition 5.2 before the last simplification leading to Theorem 1.1. Wolfram's Taylor expansion independently gives \(1+z/5+3z^2/25+O(z^3)\).

**Transfer to the actual projection displacement.** For each fixed \(a\ge0\), use the repository's generic cutoff-envelope bound with profile \(G=F+(a+1)\sqrt\Phi\) and envelope loss parameter \(1\). On the increasing tail of \(\Phi\), its required relative increment bound follows from \(\sqrt q-\sqrt p\le q-p\) for \(1\le p\le q\) and the existing increment bound for \(F\). The arithmetic cutoff then uses \(-F-(a+3/4)\sqrt\Phi\); the physical weight is \(n\exp(-F-a\sqrt\Phi)\). The existing signed-cutoff pairing implies
\[
\sum_{n\ge n_0}\frac{|d(n)|}{n}\exp[-F(n)-a\sqrt{\Phi(n)}]<\infty
\quad\Longrightarrow\quad \mathrm{RH}.
\]
Given any fixed \(s\in\mathbb R\), the pointwise estimate \(|d(n)|\le D\exp[F(n)+s\sqrt{\Phi(n)}]\) implies this moment with \(a=\max(s,0)+1\), since the exponent gap eventually exceeds \(2\log\log n\). In particular the growth bound with \(s=0\) suffices. The estimate on the actual displacement remains open. The sharper asymptotic ratio is a paper derivation. The formal reserve extraction uses its elementary lower bound.

**A stronger paper consequence at the logarithmic scale.** Write \(Q_1(x)=\Phi(x)\log L(x)/L(x)\). For every fixed \(c<A/15\),
\[
 |d(n)|=O\!\left(\exp(F(n)+cQ_1(n))\right)\quad\Longrightarrow\quad\mathrm{RH}.
\]
Choose \(\max(c,0)<b<A/15\). The asymptotic ratio above gives \(y-F-bQ_1\gg Q_1\), and \(Q_1\gg\sqrt\Phi\gg L\). Apply the generic envelope transfer to \(G=F+bQ_1\) with loss parameter 1. The coefficient \(\log L/L\) of \(\Phi\) decreases eventually and is at most 1. This gives \(Q_1(v)-Q_1(u)\le\Phi(v)-\Phi(u)\) on the increasing tail \(u\le v\). Furthermore \(Q_1\) itself increases eventually, because its logarithmic derivative with respect to \(L\) is \(3/5-6/(5L)+1/(L\log L)>0\). Thus \(G-\frac14\sqrt\Phi\) is eventually increasing by the known monotonicity of the corresponding \(F\)-profile. The arithmetic hypothesis pays the prefactor \(Kt\). The final displacement moment has damping exponent \(F+bQ_1-\sqrt\Phi\), exceeding the proposed pointwise exponent by \((b-c)Q_1-\sqrt\Phi\ge2L\) eventually. This makes the harmonic moment summable. The argument uses the same signed residual identity. This last consequence is a paper deduction.
