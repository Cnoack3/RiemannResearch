% Insert with \input; requires amsmath and amssymb.
% Lean sources in RiemannResearch/RH: ThresholdHilbertSpace, MobiusCoefficientStabilization,
% RamanujanFiniteSpanBridge, ParetoResidueMean, MixedConductorRankOne,
% MixedConductorSplitExact, MixedOrthogonalMean, and BaezDuarteNaturalApproximation.
\section{The Pareto--von Mangoldt reduction}

On the positive integers let \(P(\{n\})=1/[n(n+1)]\) and
\(H=L^2(P;\mathbb R)\). Write \(\mathbf 1(n)=1\) for \(n\ge1\) and
\(C(f)=\langle f,\mathbf 1\rangle_P\). Thus \(\|\mathbf 1\|_P=1\).
Lean represents \(f\) by the real \(\ell^2\) sequence
\(x_{n-1}=\sqrt{P(\{n\})}\,f(n)\) and sets the auxiliary value \(f(0)=0\).
For \(d\ge1\) write \(r_d(n)=n\bmod d\). For \(q\ge2\) put
\[
 J_q=\sum_{d\mid q}\mu(q/d)\,r_d,\qquad
 V=\overline{\operatorname{span}}\{r_d/d:d\ge2\}
  =\overline{\operatorname{span}}\{J_q:q\ge2\}.
\]
All closures and projections use the Pareto norm. The second description of
\(V\) follows by divisor inversion, since \(r_d=\sum_{q\mid d,\,q\ge2}J_q\).

\paragraph{Which conductors enter the kernel.}
Let \(\omega(q)\) count the distinct prime divisors of \(q\), and define
\[
 M=\overline{\operatorname{span}}\{J_q:\omega(q)\ge2\},\qquad
 M_{\mathrm{sf}}=\overline{\operatorname{span}}\{J_q:
          \omega(q)\ge2,\ q\text{ squarefree}\}.
\]
Equivalently, \(M\) is the closure of the increasing union of the mixed
spans with \(2\le q\le N\). The residue mean is \(C(r_d)=\log d\).
Divisor inversion therefore gives
\[
 C(J_q)=\sum_{d\mid q}\mu(q/d)\log d=\Lambda(q)
 =\begin{cases}\log p,&q=p^k,\ p\text{ prime},\ k\ge1,\\
                 0,&\omega(q)\ge2.\end{cases}
\]
In particular \(M\subseteq\mathbf 1^\perp\). The continuous coordinate
\(D_4(f)=f(4)-f(3)-f(2)+f(1)\) satisfies
\[
  D_4(J_q)=
  \begin{cases}-4\mu(q/4),&4\mid q,\\0,&4\nmid q.\end{cases}
\]
Every squarefree conductor avoids \(4\) as a divisor, so continuity gives
\(M_{\mathrm{sf}}\subseteq\ker D_4\). Yet \(12=2^2\cdot3\), whence
\(J_{12}\in M\) and \(D_4(J_{12})=-4\mu(3)=4\). Thus
\(M_{\mathrm{sf}}\subsetneq M\). More precisely, applying \((C,D_4)\) to
\(aJ_2+bJ_{12}\in M_{\mathrm{sf}}\) gives \((a\log 2,4b)=(0,0)\).
The two classes are independent in \(V/M_{\mathrm{sf}}\).
Indeed \(J_{12}-P_{M_{\mathrm{sf}}}J_{12}\) is a nonzero mean-zero vector
in \(V\cap M_{\mathrm{sf}}^\perp\).

\paragraph{The rank-one legal quotient.}
Put \(S=I-P_M\) and \(u=SJ_2/\log 2\). Then \(u\in V\cap M^\perp\)
and \(C(u)=1\). The screened-packet theorem gives
\(SJ_q=\Lambda(q)u\) for every \(q\ge2\). Its arithmetic input is the
rigidity theorem for mixed annihilators. For \(h\in M^\perp\) the residue
pairings \(\langle r_d,h\rangle_P\) are a common scalar times \(\log d\).
Divisor inversion gives the same scalar times \(\Lambda(q)\) for the
packet pairings. Testing against each \(h\in M^\perp\) identifies \(SJ_q\)
with \(\Lambda(q)SJ_2/\log 2\).

By continuity on the closed packet span, \(Sv=C(v)u\) for \(v\in V\).
Consequently
\[
 M=V\cap\ker C,\qquad V=M\oplus^\perp\mathbb Ru,\qquad
 V/M\xrightarrow{\ \simeq\ }\mathbb R,\quad [v]\longmapsto C(v).
\]
The inverse sends \(a\) to \([au]\). In particular every raw prime-power
packet has the decomposition \(J_{p^k}=P_MJ_{p^k}+(\log p)u\).

\paragraph{Projection and the open step.}
The mean maps \(au\) to \(a\) on \(V\cap M^\perp=\mathbb Ru\).
In \(H\) one has \(M^\perp=\mathbb Ru\oplus^\perp V^\perp\).
Since \(\mathbf 1\perp M\) and \(\langle\mathbf 1,u\rangle_P=1\),
\[
 \mathbf 1=\frac{u}{\|u\|_P^2}+P_{V^\perp}\mathbf 1,\qquad
 \|P_{V^\perp}\mathbf 1\|_P^2=1-\frac{1}{\|u\|_P^2}.
\]
Set \(d=\mathbf 1-u\). Both candidates have mean one and annihilate \(M\),
so \(d\in M^\perp\cap\ker C\). Using injectivity on the legal line to
deduce \(d=0\) would require \(d\in V\), which is already equivalent to
\(\mathbf 1\in V\). The mean on all of \(M^\perp\) has kernel
\(M^\perp\cap\mathbf 1^\perp\). Its injectivity forces \(u=\mathbf 1\).
Conversely, if \(\mathbf 1\in V\), the residue-space density theorem gives
\(V=H\), hence \(M^\perp=\mathbb R\mathbf 1\).

There is an exact scalar form of the missing condition. Write \(a=\log 2\).
Since \(J_2\) is the odd-site indicator, \(\|J_2\|_P^2=C(J_2)=a\).
Pythagoras for \(J_2=P_MJ_2+au\) and \(C(u)=1\) give
\[
 a-a^2-\|P_MJ_2\|_P^2=a^2\|\mathbf 1-u\|_P^2.
\]
Thus \(\|P_MJ_2\|_P^2=a-a^2\), ambient mean injectivity, and
\(\mathbf 1\in V\) are equivalent. Proving the reverse bound
\(\|P_MJ_2\|_P^2\ge a-a^2\) independently would complete this route.
The formalized approximation theorem yields \(\mathbf 1\in V\Rightarrow
\mathrm{RH}\). The formalized converse takes the B\'aez--Duarte implication
from RH to natural approximation as an explicit hypothesis.
