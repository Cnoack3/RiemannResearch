# A target second-moment cap below the permanent universal floor

Research continuation, 9 October 2026. Starting published head:
`8fb96c3d991faf77d727e61870db9f98a4fc8a5e`.

## Conclusion and scope

For every integer stage \(n\ge4\), the actual squarefree optimizer satisfies
\[
0<\rho_n=\frac{\langle r_n,Dr_n\rangle_Q}{e_n}\le\frac3{10},
\qquad
\rho_n^2\le m_2(n)\le\frac{10745}{28906}\rho_n
\le\frac{6447}{57812}\approx0.111516640143915.
\]
Here \(Q(k)=1/(\zeta(2)k^2)\), \(D x(k)=x(k)/k\),
\(V_n=\operatorname{span}\{g_d:2\le d\le n+1,\ d\text{ squarefree}\}\),
\(g_d(k)=(k\bmod d)/d\), \(r_n=1-P_{V_n}1\), \(e_n=\|r_n\|_Q^2>0\),
and \(m_2(n)=\|P_{V_n^\perp}Dr_n\|_Q^2/e_n\).

This improves the previously published first-moment cap
\(39138061/126426000\approx0.309572881\) and second-moment cap
\(84107693089/730893991200\approx0.115075092\).
The new cap also gives the strict separation
\[
\frac{6447}{57812}
<
\left(\frac{1337}{3979}\right)^2
\approx0.112905457850751,
\]
with exact difference \(1271191901/915305079092>0\).
The right side is a lower bound for any second-moment cap covering
**every** vector in \(V_n^\perp\). It is not a lower bound for the
actual optimizer residual.

These are unconditional bounds for all \(n\ge4\), not finite-stage numerical
observations. They do not prove \(\rho_n\to0\), \(m_2(n)\to0\), or RH.

## Complete signed proof

Put \(Z=\zeta(2)\). The established actual normal equations for conductors
2, 3, and 5, together with
\(x(4)=-x(1)+x(2)+x(3)\), give for \(x=r_n\)
\[
X=(x(1),x(2),x(3))^{T}
=\sum_{k\ge5}W(k)x(k)/k^2,
\quad
W(k)=
\begin{pmatrix}
-9/10&-4/15&1/5\\
8/5&-8/5&-2/15\\
-9/10&12/5&-9/5
\end{pmatrix}
\begin{pmatrix}k\bmod2\\k\bmod3\\k\bmod5\end{pmatrix}.
\]
Every sum here is the entire signed tail.

Define
\[
N_H=x^2+y^2/4+z^2/9+(-x+y+z)^2/16,\qquad
R_H=x^2+y^2/8+z^2/27+(-x+y+z)^2/64,
\]
\[
J=R_H-\frac3{10}N_H
=\frac{223}{320}(x+y/223+z/223)^2
+\frac{209}{4460}(y-14z/209)^2+\frac2{5643}z^2.
\]
The site-four square is retained throughout. With \(X\) as above, set
\[
N_T=\sum_{k\ge5}x(k)^2/k^2,\qquad
T=\sum_{k\ge5}(31/100-1/k)x(k)^2/k^2.
\]
The exact complete identities are
\[
Z\|x\|_Q^2=N_H(X)+N_T,
\]
\[
Z\left(\frac{31}{100}\|x\|_Q^2-\langle x,Dx\rangle_Q\right)
=T-J(X)+\frac1{100}N_H(X).
\]
Consequently,
\[
Z\left(\frac3{10}\|x\|_Q^2-\langle x,Dx\rangle_Q\right)
=T-J(X)-\frac1{100}N_T. \tag{1}
\]
Thus no negative tail contribution has been silently removed.

For \(a=k\bmod2,\ b=k\bmod3,\ c=k\bmod5\), the exact recovery numerator is
\[
q(k)=J(W(k))
=\frac{621a^2+48ab-216ac+176b^2-64bc+24c^2}{900}.
\]
The negative cross terms remain. The complete weighted Cauchy argument gives
\[
J(X)\le\Lambda T,\qquad
\Lambda=\sum_{k\ge5}\frac{q(k)}{k^2(31/100-1/k)}.
\]

## Stronger rational certificate, including every tail site

The bound \(0\le q(k)\le1421/900\) holds in all residue channels.
Split the finite head \(5\le k\le200\) into seven blocks of length 28.
Their respective upper bounds, in units of \(10^{-6}\), are
\[
840429,\quad23560,\quad8787,\quad4383,\quad2470,\quad1751,\quad1299.
\]
Their sum is \(882679/10^6<883/1000\).
Each rational block inequality is proved with Lean arithmetic; the
Wolfram-selected values are not assumed.

For the full infinite tail,
\[
\sum_{k\ge201}\frac{q(k)}{k^2(31/100-1/k)}
\le\frac{1421/900}{31/100-1/201}\sum_{k\ge201}\frac1{k^2}
\le\frac{95207}{3678600}.
\]
The proof retains the finite terminal remainder
\[
\sum_{i=0}^{M-1}\frac1{(i+201)^2}
\le\frac1{200}-\frac1{M+200}
\]
before taking the infinite limit. Therefore
\[
\Lambda\le\frac{883}{1000}+\frac{95207}{3678600}
=\frac{8358527}{9196500}<\frac{10}{11}.
\]
Since \(T\ge(11/100)N_T\), identity (1) gives the retained positive margin
\[
Z\left(\frac3{10}\|x\|_Q^2-\langle x,Dx\rangle_Q\right)
\ge\left(\frac{10}{11}-\frac{8358527}{9196500}\right)T
=\frac{21203}{101161500}T\ge0. \tag{2}
\]
This proves the first-moment bound. The existing complete screening
inequality gives the second-moment bound and strict separation.

No radical compatibility is imposed on \(P_{V_n^\perp}Dr_n\).
The actual complete correction equality is still
\[
e_nm_2(n)=\texttt{quarticFloor}(n)+\texttt{weightedMismatch}(n)
-\texttt{screening}(n).
\]
Both optimizer correction squares and every infinite tail remain present.

## Formal coverage and verification

The strengthened declarations keep their existing names in
`RH/ReciprocalRadicalFourCertificate.lean`,
`RH/ZetaTwoRadicalFourBound.lean`, and
`RH/ZetaTwoTargetFirstMoment.lean`.
The additional declarations expose the strict trace threshold, retained
three-tenths gap, and separation from the permanent universal floor.
The theorem catalog and prior status note point to this continuation.

The seven-block finite certificate passed isolated Lean checking:
`job_tkDpzlXDLj-BogPyLV2mc_-lLlpmLTcQ`, exit 0; its axiom audit
uses only `propext`, `Classical.choice`, and `Quot.sound`.
The complete infinite certificate and scalar margin also passed together:
`job_e5D6gpDX8UJ8PaoJLRgDBBdExlij0bw0`, exit 0, source SHA-256
`81ddd2a3c05f72116aa69c55404f691ed95d6e361a34704f35edebc32865e4f7`.
Their audits use the same three standard foundations. Native project validation
and publication are reported by that checkpoint; an isolated certificate
alone is not claimed to verify the actual optimizer application.

## Remaining research obligation

The existing all-stage closure equivalence is
\[
qOne\in\overline{\operatorname{span}}\{g_d:d\ge2,\ d\text{ squarefree}\}
\iff \rho_n\longrightarrow0.
\]
One common cofinal sequence suffices. Its arithmetic decay provider is
still **Open**. A smaller fixed cap cannot discharge it by iteration:
the reciprocal screened image has not been shown to satisfy the actual
residual's radical relations.

The next quantitative finite-certificate direction is to bound the largest
eigenvalue of the full three-by-three weighted row Gram matrix, rather than
its trace. Wolfram exploration at threshold \(29/100\) gave a finite
2000-site largest eigenvalue near \(0.942\); this is an exploration only.
No all-tail certificate or formal \(29/100\) bound is asserted.
Even a successful fixed \(29/100\) bound would still leave the decay provider
open.

## Sources and computational provenance

- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis*, https://arxiv.org/pdf/math/0607733,
  Remarks 4 and 8. Supports the published squarefree closure framework,
  not the new numerical constants or an unconditional decay claim.
- NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15#E1. Supports the optional exact
  interpretation \(\sum_{k\ge201}k^{-2}=\psi^{(1)}(201)\);
  the formal tail proof here is elementary telescoping.
- Wolfram Language independently computed the rational block envelopes,
  complete-tail cap, and strict universal-floor separation. Lean checks
  rational inequalities and the infinite-series argument independently.
