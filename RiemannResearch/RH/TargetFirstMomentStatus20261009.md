# Target-specific reciprocal moments and an unconditional first-moment saving

> Later continuation, 9 October 2026: the current Lean statements sharpen
> the all-stage bounds to a/e <= 3/10 and m2 <= 6447/57812 for n>=4.
> The complete trace is at most 8358527/9196500 < 10/11, retaining every
> tail site. The actual second-moment cap is strictly below the permanent
> universal floor (1337/3979)^2. See `TargetMomentCapSeparation20261009.md`.
> The previous certificate and its verification record are preserved below
> as the historical calculation. Cofinal decay and RH remain open.

Research date: 9 October 2026. Starting point:
`d14989c6eb04be046707e69c72d4e1431e43e1ec`.

## Verified results and precise scope

For the actual inverse-square squarefree optimizer, write
\(Z=\zeta(2)\), \(r_n=qOne-P_{V_n}qOne\), \(e_n=\|r_n\|^2>0\),
\(a_n=\langle r_n,Dr_n\rangle\), and
\(s_n=Dr_n-P_{V_n}Dr_n\). Define \(\rho_n=a_n/e_n\) and
\(m_2(n)=\|s_n\|^2/e_n\).

The completed declarations establish, for every integer \(n\ge4\),

\[
0<\rho_n\le\gamma=\frac{39138061}{126426000}
 \approx0.3095728806,
\qquad
\rho_n^2\le m_2(n)\le\beta\rho_n
 \le\frac{84107693089}{730893991200}\approx0.1150750917,
\quad \beta=\frac{10745}{28906}.
\]

The cap \(\gamma\) is the strongest bound obtained from the certificate
below; no claim of an optimal arithmetic constant is made.
Its positive value does not prove decay or RH.

The universal first-moment floor \(1337/3979\) remains valid. There is no
conflict: the new input bound uses the actual residual's proved four-site
identity. No such identity is assumed for \(s_n\).

All 66 new public theorem bodies were checked together in coherent job
`job_P2B73ELz1Fwm918oQYI3VSs8fXWNjMTa`, exit code 0, with no warnings.
The eight decisive transitive axiom audits in that output use exactly
`propext`, `Classical.choice`, and `Quot.sound`; they include the target
bound, complete trace certificate, radical margin, exact Mobius correction,
closure equivalence and conditional RH consumer.
The checked coherent source SHA-256 is
`bb238b18272df56e0690e8b6ebc5d6d1e33576725d9169e0a61e0fa3c7af4a98`.

The new modules are exported from `RiemannResearch.lean`.
The proof commit is `250f947683292370d6ebbb0d284d7fb07b150d75`.
Checkpoint `job_TxK0Mz0aHBQNx9AJuAFotsQsr9Z_LwqC` completed successfully
and published it after a native affected-module build and a second build
against the integrated current main. Five modules, including the existing
conductor-five reverse dependent, passed. The native builds reported only
style warnings; the coherent theorem-body check reported none.
This is affected-module validation, not a claim of a new full-project build.

| Module | New public theorems | Responsibility |
| --- | ---: | --- |
| `RH/ZetaTwoReciprocalBound.lean` | 1 | Mixed positive-form screening estimate |
| `RH/ReciprocalRadicalFourCertificate.lean` | 21 | Signed rational head and complete tail |
| `RH/ZetaTwoRadicalFourBound.lean` | 18 | Actual normal equations and radical first-moment saving |
| `RH/ZetaTwoTargetFirstMoment.lean` | 26 | Target assembly, corrections, recovery and open-provider consumer |

Source provenance: the requested target assembly is section 4 of
`ConductorRecoveryStatus20261009.md`; the additional exact signed
normal-equation and radical certificate were developed independently during
this continuation. Computation selects rational constants; every displayed
certificate used by the Lean results is proved by ordinary Lean arithmetic
and complete infinite-series arguments.

## Safe target-only screening assembly

Full orthogonal projection gives the exact signed pairing

\[
\langle s_n,Dr_n\rangle=\|s_n\|^2.
\]

Positive-form Cauchy and the existing universal cap applied only to \(s_n\)
then give

\[
\|s_n\|^4
\le\langle s_n,Ds_n\rangle a_n
\le\beta\|s_n\|^2a_n.
\]

Cancellation, including the zero-screened-image case, proves
\(m_2(n)\le\beta a_n/e_n\).
The general theorem actually permits any input vector: only its screened
image must satisfy the universal complement cap.
It requires no radical compatibility of that image.

Ordinary Cauchy on the exact pairing
\(\langle r_n,s_n\rangle=a_n\) proves the complementary inequality
\(\rho_n^2\le m_2(n)\).

The existing complete correction equality remains

\[
e_nm_2(n)=\varepsilon_n+\delta_n-\sigma_n
=\texttt{quarticFloor}(n)+\texttt{weightedMismatch}(n)
-\texttt{screening}(n).
\]

Both correction squares and the entire infinite Hilbert-space remainder
remain present in `completeCorrection_le_firstMoment` and
`completeCorrection_le_radical_margin`.

## Exact actual normal equations

Every squarefree residue atom and the constant target obey
\(x(4)-x(3)-x(2)+x(1)=0\). The actual residual therefore satisfies

\[
r_n(4)=-r_n(1)+r_n(2)+r_n(3).
\]

Lean discharges this identity using the established literal four-site
dual pairing `fourWitness_inner_residual`. It is used only for \(r_n\).

For \(x=r_n\), let \(X=(x(1),x(2),x(3))^T\) and
\(t_d=\sum_{k\ge5}(k\bmod d)x(k)/k^2\). The complete signed normal equations
for conductors \(2,3,5\) are

\[
AX+(t_2,t_3,t_5)^T=0,\qquad
A=\begin{pmatrix}
1&0&1/9\\
15/16&9/16&1/16\\
3/4&3/4&7/12
\end{pmatrix}.
\]

Thus the head is recovered from the entire tail with rows

\[
W(k)=
\begin{pmatrix}
-9/10&-4/15&1/5\\
8/5&-8/5&-2/15\\
-9/10&12/5&-9/5
\end{pmatrix}
\begin{pmatrix}k\bmod2\\k\bmod3\\k\bmod5\end{pmatrix},
\qquad
X=\sum_{k\ge5}W(k)x(k)/k^2.
\]

These are exact signed, summable identities for every \(n\ge4\).

## Exact gap and the complete rational certificate

Define

\[
N_H=x^2+y^2/4+z^2/9+(-x+y+z)^2/16,
\quad
R_H=x^2+y^2/8+z^2/27+(-x+y+z)^2/64.
\]

The positive head form \(J=R_H-(3/10)N_H\) has both exact decompositions

\[
J=\frac{223}{320}(x+y/223+z/223)^2
 +\frac{209}{4460}(y-14z/209)^2+\frac2{5643}z^2,
\]

\[
J=\frac{223}{320}x^2+\frac1{160}xy+\frac1{160}xz
 +\frac3{64}y^2-\frac1{160}yz+\frac1{1728}z^2.
\]

At \(\tau=31/100\), let
\(T=\sum_{k\ge5}(\tau-1/k)x(k)^2/k^2\).
The complete signed identity is

\[
Z(\tau\|x\|^2-\langle x,Dx\rangle)
=T-J(x(1),x(2),x(3))+\frac1{100}N_H(x(1),x(2),x(3)).
\]

The site-four square remains in both \(N_H\) and \(R_H\).
Writing \(a=k\bmod2,b=k\bmod3,c=k\bmod5\), the signed recovery numerator is

\[
q(k)=J(W_1(k),W_2(k),W_3(k))
=\frac{621a^2+48ab-216ac+176b^2-64bc+24c^2}{900}.
\]

Both negative cross interactions remain. Lean proves \(0\le q(k)\le1421/900\)
in every residue channel, and the exact rational 34-site estimate

\[
\sum_{k=5}^{38}\frac{q(k)}{k^2(31/100-1/k)}\le17/20.
\]

The complete tail satisfies

\[
\sum_{k\ge39}\frac{q(k)}{k^2(31/100-1/k)}
\le\frac{1421/900}{38(31/100-1/39)}
=\frac{18473}{126426}.
\]

Its inverse-square comparison retains the finite terminal remainder
\(1/38-1/(M+38)\) before passing to the convergent infinite sum.
Consequently the full trace is at most

\[
\Lambda=\frac{17}{20}+\frac{18473}{126426}
=\frac{1259351}{1264260}<1.
\]

Infinite weighted Cauchy is applied to the three complete signed transformed
rows \(W_1+W_2/223+W_3/223\), \(W_2-14W_3/209\), and \(W_3\).
Their weighted sum proves \(J\le\Lambda T\).

Finally, the full raw norm is \(Z\|x\|^2=N_H+N_T\), where
\(N_T=\sum_{k\ge5}x(k)^2/k^2\), and \(T\ge(11/100)N_T\). Hence

\[
Z(\tau\|x\|^2-\langle x,Dx\rangle)
\ge(1-\Lambda)T+\frac1{100}N_H
\ge\frac{53999}{126426000}Z\|x\|^2.
\]

This proves \(\rho_n\le\gamma=\tau-53999/126426000\).
Every normal-equation, compatibility and tail assumption of the generic
certificate is discharged for the actual residual internally.

## Exact optimizer corrections and the remaining arithmetic requirement

Let \(F_{\mu,n}\) be the actual legal finite Mobius trial,
\(R_{\mu,n}=qOne-F_{\mu,n}\), and \(U_n=F_n-F_{\mu,n}\).
Lean retains actual normal-equation optimizer coefficients \(c_i\) and proves

\[
U_n=\sum_{i<n}\bigl(c_i+\mu(i+2)\bigr)\,\texttt{squarefreeAtom}_i,
\]

including redundant zero atoms. No inverse of a redundant Gram matrix is
assumed. The complete signed identities are

\[
e_n=\|R_{\mu,n}\|^2-\|U_n\|^2,
\]

\[
a_n=\langle R_{\mu,n},DR_{\mu,n}\rangle
 -2\langle R_{\mu,n},DU_n\rangle+\langle U_n,DU_n\rangle.
\]

The normalized ratio of these full expressions is exactly \(\rho_n\).
Smallness of a trial term alone cannot replace control of the signed cross
pairing or of the moving displacement energies.

The all-stage Lean theorem is

\[
qOne\in\overline{\operatorname{span}}\{g_d:d\ge2,\ d\text{ squarefree}\}
\quad\Longleftrightarrow\quad \rho_n\longrightarrow0.
\]

The same equivalence holds with one common cofinal stage sequence.
`riemannHypothesis_of_cofinal_firstMoment` is a **conditional research
reduction**: the displayed cofinal decay premise is **Open**.
Its complete norm transfer and Mellin RH consumer are established internally.
No RH-dependent Bagchi converse is used to discharge that premise.

A further paper characterization isolates what the signed tail charges must
accomplish. Let

\[
H_K(n)=\frac1{Ze_n}\sum_{k=1}^K r_n(k)^2/k^2,\qquad K\ge1.
\]

The exact complete norm and positive reciprocal form give

\[
H_K(n)\le K\rho_n,\qquad
\rho_n\le H_K(n)+1/(K+1).
\]

Thus \(\rho_n\to0\) is equivalent to \(H_K(n)\to0\) for every fixed \(K\),
also along a common cofinal sequence. This finite-head characterization is
a paper consequence here, not an additional formal declaration.
The infinitely many normalized head limits remain the arithmetic obligation.

The verified direct resolvent consequence also gives, for every \(n\) and
positive integer \(M\),

\[
e_n\le\frac{H_M^{\mathrm{harmonic}}}{Z}\bigl(\rho_n+1/M\bigr).
\]

It supplies quantitative recovery if the open first-moment decay is proved.
The positive fixed cap above supplies no unconditional decay of \(\rho_n\)
or \(m_2(n)\), and RH remains unproved.
