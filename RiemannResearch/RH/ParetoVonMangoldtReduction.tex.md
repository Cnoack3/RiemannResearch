% Include with \input{ParetoVonMangoldtReduction.tex.md}. Requires amsmath and amssymb.
\section{The mixed-conductor criterion}

Let \(P(n)=1/[n(n+1)]\) for positive integers \(n\), and put
\(H=L^2(P;\mathbb R)\). We use the constant vector \(\mathbf 1(n)=1\),
the inner product \(\langle f,h\rangle_P=\sum_{n\ge1}P(n)f(n)h(n)\),
and the mean \(C(f)=\langle f,\mathbf 1\rangle_P\). Telescoping gives
\(\sum_{n\ge1}P(n)=1\), so \(\|\mathbf 1\|_P=1\). At the auxiliary
site \(0\) we extend every vector by zero. In Lean the same Hilbert
space is represented by the sequence
\((\sqrt{P(n)}\,f(n))_{n\ge1}\) in real \(\ell^2\).

For integers \(d\ge1\) and \(q\ge2\) define
\[
 r_d(n)=n\bmod d,\qquad
 J_q=\sum_{d\mid q}\mu(q/d)r_d .
\]
Here \(\mu\) is the M\"obius function. Each residue is bounded for fixed
\(d\), so all the displayed vectors belong to \(H\). Write \(\omega(q)\)
for the number of distinct prime divisors of \(q\), and set
\begin{align*}
 V &=\overline{\operatorname{span}}\{J_q:q\ge2\},&
 M_N &=\operatorname{span}\{J_q:2\le q\le N,\ \omega(q)\ge2\},\\
 M &=\overline{\bigcup_{N\ge1} M_N},&
 a&=\log 2,\qquad g=J_2-a\mathbf 1 .
\end{align*}
All closures and projections use the norm of \(H\). Since \(r_1=0\),
divisor inversion gives \(r_d=\sum_{q\mid d,\ q\ge2}J_q\). Thus \(V\)
is also the closed span of \(r_d/d\) over \(d\ge2\).

\paragraph{Theorem.}
Let \(P_N\) and \(P_M\) denote the orthogonal projections onto
\(M_N\) and \(M\), respectively. Put \(u=(J_2-P_MJ_2)/a\).
Then \(C(u)=1\) and \(V=M\oplus^\perp\mathbb Ru\). The following
conditions are equivalent.
\begin{enumerate}
\item \(\mathbf 1\in V\).
\item \(u=\mathbf 1\).
\item \(\|P_MJ_2\|_P^2=a-a^2\).
\item For every \(\varepsilon>0\) there exist \(N\) and \(m\in M_N\)
      such that \(\|g-m\|_P^2<\varepsilon\).
\end{enumerate}
Each condition implies the Riemann hypothesis. The arithmetic estimate
still required is the lower bound \(\|P_MJ_2\|_P^2\ge a-a^2\).

\subsection{The mean of a packet}

Let \(H_j=\sum_{k=1}^j k^{-1}\). For \(T=dK\), summation by parts
and \(r_d(0)=r_d(T)=0\) give the finite identity
\[
 \sum_{n=1}^{T-1} P(n)r_d(n)
   =\sum_{n=1}^{T}\frac{r_d(n)-r_d(n-1)}n
   =\sum_{n=1}^{T}\frac{1-d\,\mathbf 1_{d\mid n}}n
   =H_{dK}-H_K.
\]
For fixed \(d\), the left side converges absolutely. On the right
\(H_j-\log j\) converges, so \(C(r_d)=\log d\). The divisor identity
\(\sum_{q\mid d}\Lambda(q)=\log d\) now yields
\begin{equation}\label{pvm:means}
 C(J_q)=\sum_{d\mid q}\mu(q/d)\log d=\Lambda(q)
 =\begin{cases}
 \log p,&q=p^k,\quad p\text{ prime},\ k\ge1,\\
 0,&\omega(q)\ge2.
 \end{cases}
\end{equation}
Continuity of \(C\) gives \(M\subseteq\mathbf 1^\perp\). In particular,
\(J_2(n)=n\bmod 2\) takes only the values zero and one, whence
\(\|J_2\|_P^2=C(J_2)=a\) and \(\|g\|_P^2=a-a^2\).

\subsection{The line in the closed packet space}

Let \(S=I-P_M\) and \(h\in M^\perp\). Write
\(F_h(d)=\langle r_d,h\rangle_P\). By divisor inversion, when \(b\) and
\(c\) are coprime positive integers, every divisor of \(bc\) involving a
prime from each factor contributes a mixed packet. Pairing with \(h\)
therefore gives \(F_h(bc)=F_h(b)+F_h(c)\). We use two established
analytic lemmas from the formalization. For every \(h\in H\),
\[
 \lim_{K\to\infty}
 \frac1K\sum_{d=K}^{2K-1}\lvert F_h(d+1)-F_h(d)\rvert=0 .
\]
The dyadic rigidity theorem states that a real coprime-additive
function with this property is a constant multiple of \(\log d\).
It follows that \(F_h(d)=c_h\log d\), where
\(c_h=\langle J_2,h\rangle_P/a\). A second divisor inversion gives
\(\langle J_q,h\rangle_P=c_h\Lambda(q)\).

Since \(h\perp M\), one has \(\langle Sx,h\rangle_P=\langle x,h\rangle_P\)
for all \(x\). Consequently \(SJ_q-\Lambda(q)u\) lies in \(M^\perp\) and
pairs to zero with every member of \(M^\perp\). Pairing with itself gives
\(SJ_q=\Lambda(q)u\). Also \(u\in V\cap M^\perp\), since \(P_MJ_2\in M\subseteq V\),
and \(C(u)=C(J_2)/a=1\). Equation~\eqref{pvm:means}, linearity, and
continuity on the closed packet span now give
\begin{equation}\label{pvm:screen}
 Sv=C(v)u\quad(v\in V),\qquad
 M=V\cap\ker C,\qquad V=M\oplus^\perp\mathbb Ru .
\end{equation}
Indeed, \(v=P_Mv+C(v)u\), and the two summands are orthogonal.
Thus \([v]\mapsto C(v)\) identifies \(V/M\) with \(\mathbb R\), with inverse
\(t\mapsto[tu]\). For a prime power the raw packet has the more precise
decomposition \(J_{p^k}=P_MJ_{p^k}+(\log p)u\).

\paragraph{Why all mixed conductors enter.}
Let \(M_{\mathrm{sf}}\) use only squarefree mixed conductors, with the same
norm closure. Each site evaluation is continuous since
\(P(n)^{1/2}|f(n)|\le\|f\|_P\). Hence
\(D_4(f)=[f(4)-f(3)]-[f(2)-f(1)]\) is continuous. The increment
formula for \(r_d\) gives \(D_4(r_d)=-4\mathbf 1_{d=4}\). Thus
\(D_4(J_q)=-4\mu(q/4)\) if \(4\mid q\), and is zero otherwise.
The functional kills \(M_{\mathrm{sf}}\), whereas
\(D_4(J_{12})=4\) and \(J_{12}\in M\). In fact \((C,D_4)\) takes the
values \((a,0)\) and \((0,4)\) on \(J_2\) and \(J_{12}\), respectively.
Their classes in \(V/M_{\mathrm{sf}}\) are linearly independent.

\subsection{An identity for every finite trial}

Because \(\mathbf 1\perp M_N\), \(P_Ng=P_NJ_2\). For every \(m\in M_N\),
write \(g-m=(g-P_Ng)+(P_Ng-m)\). The first term is perpendicular to
\(M_N\), and the second belongs to it. A second application of Pythagoras
to \(g=P_Ng+(g-P_Ng)\) gives
\begin{equation}\label{pvm:trial}
 \|g-m\|_P^2
 =\underbrace{a-a^2-\|P_NJ_2\|_P^2}_{\displaystyle\delta_N}
  +\|P_NJ_2-m\|_P^2 .
\end{equation}
The minimum over \(M_N\) is attained at \(m=P_NJ_2\). In particular
\(\delta_N\) is nonnegative and decreases with \(N\). If \(L\) is a positive
multiple of two and of all conductors used in \(M_N\), every \(m\in M_N\)
vanishes at \(L\), while \(g(L)=-a\). The term at this single site shows
\[
 \delta_N\ge \frac{a^2}{L(L+1)}>0 .
\]
One may take \(L=2(N+1)!\). This lower bound tends to zero for that choice
and leaves the value of \(\lim_N\delta_N\) undetermined.

From \(M=\overline{\bigcup_N M_N}\), the decreasing sequence of squared
distances to \(M_N\) tends to the squared distance to \(M\). Indeed, any
point of \(M\) can be approximated by a member of a finite stage, and
each finite stage is contained in \(M\). The full-stage residual has the
particularly simple form \(g-P_Mg=a(u-\mathbf 1)\). Therefore
\begin{equation}\label{pvm:full}
 \lim_{N\to\infty}\delta_N
 =a-a^2-\|P_MJ_2\|_P^2=a^2\|u-\mathbf 1\|_P^2 .
\end{equation}
Equation~\eqref{pvm:full} proves the equivalence of conditions 2--4.
If \(\mathbf 1\in V\), then \(S\mathbf 1=\mathbf 1\) because
\(\mathbf 1\perp M\), while \eqref{pvm:screen} gives
\(S\mathbf 1=C(\mathbf 1)u=u\). Conversely \(u\in V\), so
\(u=\mathbf 1\) implies \(\mathbf 1\in V\). This proves all four
equivalences and the upper bound \(\|P_MJ_2\|_P^2\le a-a^2\).

\paragraph{The ambient mean.}
Taking orthogonal complements relative to \(H\) in \eqref{pvm:screen}
gives \(M^\perp=\mathbb Ru\oplus^\perp V^\perp\). Since
\(C(u)=1\), projection of \(\mathbf 1\) onto \(V\) is
\(u/\|u\|_P^2\). Both \(u\) and \(\mathbf 1\) have mean one
in \(M^\perp\). Injectivity of \(C\) on \(V\cap M^\perp=\mathbb Ru\)
therefore identifies them once \(\mathbf 1\in V\) is known.
Injectivity on all of \(M^\perp\) also identifies them. Conversely,
if \(\mathbf 1\in V\), then \(V=H\). Indeed, the dilations
\(T_jf(n)=f(\lfloor n/j\rfloor)\) preserve \(V\), as
\(jT_jr_d=r_{jd}-r_j\) and \(\|T_jf\|_P^2=\|f\|_P^2/j\) by telescoping.
Under the assumption, \(T_j\mathbf 1-T_{j+1}\mathbf 1\) belongs to \(V\)
and is the indicator of site \(j\). Finite linear combinations of these
indicators are dense in \(H\). Thus \(M^\perp=\mathbb R\mathbf 1\)
and the ambient mean is injective. The ambient injectivity assertion is
another form of condition 1.

\paragraph{A certified finite tolerance.}
Write \(E=\|\mathbf 1-P_V\mathbf 1\|_P^2\). The projection formula just
proved gives \(1-E=1/\|u\|_P^2\), and \(C(u)=1\) gives
\(\|u-\mathbf 1\|_P^2=\|u\|_P^2-1=E/(1-E)\).
The conductor-241 residue trial, evaluated on 65,536 sites with a
complete tail bound, gives \(E\le 628101568132839/65537000000000000\).
Applying \eqref{pvm:full} and the monotonicity of \(t/(1-t)\) gives
\[
 \lim_N\delta_N\le
 c_{241}:=(\log 2)^2\frac{628101568132839}{64908898431867161}
 \simeq 0.00464918214215 .
\]
For every \(\varepsilon>c_{241}\), all sufficiently large \(N\) therefore
admit a finite mixed trial of squared error below \(\varepsilon\), namely
\(P_NJ_2\). Condition 4 requires this conclusion for every positive
\(\varepsilon\).
\ifdefined\href\href{https://github.com/Cnoack3/RiemannResearch/blob/6f8673015600a62e0d94158362d3913d46d8dd16/RiemannResearch/RH/ParetoGroupedResidueMass.lean\#L45}{[Lean source for the conductor-241 bound.]}\fi

\subsection{Why approximation implies the Riemann hypothesis}

For \(f\in H\) define \(F(x)=f(\lfloor 1/x\rfloor)\) on \(0<x\le1\).
The interval \((1/(n+1),1/n]\) has length \(P(n)\), so this map is
an isometry into \(L^2(0,1)\). For \(s\in\mathbb C\) with
\(\sigma=\Re s>1/2\), Cauchy--Schwarz gives
\[
 \left|\mathcal L_s(f)\right|
 :=\left|\int_0^1 F(x)x^{s-1}\,dx\right|
 \le \frac{\|f\|_P}{\sqrt{2\sigma-1}} .
\]
For \(f=r_d/d\) the corresponding step function is
\(\lfloor1/x\rfloor/d-\lfloor1/(dx)\rfloor\). If \(\Re s>1\), integration
of the series \(\lfloor1/x\rfloor=\sum_{n\ge1}\mathbf 1_{x\le1/n}\)
gives \(\zeta(s)/s\), with absolute convergence. Rescaling the second
floor term gives
\[
 \mathcal L_s(r_d/d)=(d^{-1}-d^{-s})\frac{\zeta(s)}{s}.
\]
The left side is holomorphic on \(\Re s>0\) because the step function is
bounded. The zero of \(d^{-1}-d^{-s}\) at \(s=1\) removes the zeta pole,
so analytic continuation gives the formula throughout that half-plane.
At a zeta zero \(\rho\) with \(1/2<\Re\rho<1\), the functional
\(\mathcal L_\rho\) vanishes on the residue span and therefore on \(V\).
But \(\mathcal L_\rho(\mathbf 1)=1/\rho\ne0\). Thus \(\mathbf 1\in V\)
excludes every such zero. The functional equation reflects a nontrivial
zero in the left half of the critical strip to one in the right half.
This proves the RH implication in the theorem. In the formalization of
the converse, B\'aez--Duarte's implication from RH to natural approximation
is an explicit hypothesis.

\subsection{What a finite-head construction still needs}

Head interpolation imposes a second requirement on the trial. For all
large \(K\), a finite mixed sum \(m_K\) can match \(g\) on every site
\(1\le n\le K\) with
\begin{equation}\label{pvm:headrate}
 \|g-m_K\|_P^2=O\!\left(\frac{K\log\log K}{\log K}\right).
\end{equation}
The support bound of \(m_K\) may depend on \(K\). The construction starts
from the canonical M\"obius residue sum \(w_K\in V\) matching
\(\mathbf 1\) on the first \(K\) sites. Its verified norm estimate is
\(\|w_K-\mathbf 1\|_P^2\le(K+1)Q_B(K)\) for some \(B\ge0\) and all large
\(K\), where, writing \(t_K=(1+\log(\log K+3))/\log K\),
\[
 Q_B(K)=9/K+2\{4+2(2+4B)^2\}\,t_K+8(2+4B)^2t_K^2 .
\]
To transfer this estimate, take any \(z\in V\) with \(C(z)=1\). Put \(b=C(w_K-\mathbf 1)\) and
\(d=(K+1)T_{K+1}z\). Then \(d\) vanishes on the head, has mean one by
telescoping, and has norm \(\sqrt{K+1}\,\|z\|_P\). Hence
\(x=z-w_K+bd\) belongs to \(V\), has mean zero, and lies in \(M\) by
\eqref{pvm:screen}. It agrees with \(z-\mathbf 1\) on the head.
Cauchy--Schwarz on the remaining sites gives
\(\lvert b\rvert\le\|w_K-\mathbf 1\|_P/\sqrt{K+1}\) because their total
mass is \(1/(K+1)\). Thus \(\|(z-\mathbf 1)-x\|_P\le
(1+\|z\|_P)\|w_K-\mathbf 1\|_P\). The finite-head repair lemma
approximates \(x\in M\) by a finite mixed sum with the same head and an
arbitrarily small additional norm error. Indeed, the restriction to the
first \(K\) sites maps the finite mixed span onto \(\mathbb R^K\) by the
mixed interpolation theorem. Lift the coordinate basis to fix a linear
right inverse. Its domain is finite dimensional, so it is bounded.
Correcting the heads of any finite mixed sequence converging to \(x\) with
this right inverse preserves convergence and gives exact agreement.
Setting \(z=J_2/a\), choosing an
additional error below one, and multiplying the fit by \(a\) proves
\eqref{pvm:headrate}.

\ifdefined\pvmStandaloneLayout\newpage\fi
\paragraph{Growth sufficient for the missing estimate.}
Put \(e=g-P_Mg\). For any such fit, orthogonality
to \(M\) gives \(\langle e,g-m_K\rangle_P=\|e\|_P^2\).
The error vanishes on the first \(K\) sites. Hence
\[
 \|e\|_P^4\le
 \left(\sum_{n>K}P(n)e(n)^2\right)\|g-m_K\|_P^2 .
\]
The tail in parentheses tends to zero. A uniform bound on the full
errors along any sequence \(K\to\infty\) would force \(e=0\),
which is condition 4.

A cofinal subpolynomial upper bound on the complete squared errors is
also sufficient for RH. Indeed, at any right-half-strip zero \(\rho\), the
vector \((J_2-m_K)/a\) lies in \(V\), so its Mellin evaluation is zero.
The difference between this vector and \(\mathbf 1\) vanishes on the first
\(K\) sites. Applying Cauchy--Schwarz on \((0,1/(K+1)]\) to its Mellin
evaluation, whose absolute value is \(1/|\rho|\), gives
\[
 \|g-m_K\|_P^2\ \ge \frac{a^2(2\Re\rho-1)}{|\rho|^2}(K+1)^{2\Re\rho-1}.
\]
The exponent is positive at every such zero, so a subpolynomial upper
bound excludes all of them. Since the exponent is also strictly below
one, the upper bound in \eqref{pvm:headrate} is compatible with this
power lower bound.

\paragraph{Formal counterparts.}
The packet mean is proved in \texttt{ParetoResidueMean}.
The variation and rigidity inputs appear in \texttt{ResidueConductorVariation}
and \texttt{DyadicAdditiveRigidity}. The line \eqref{pvm:screen} and the
full projection criterion are in \texttt{MixedConductorRankOne}, with the
squarefree obstruction in \texttt{MixedOrthogonalMean}. The finite-trial
identity \eqref{pvm:trial} and its RH criterion are proved in
\texttt{CenteredParityFiniteTrials}, using \texttt{MixedConductorCaptureGains}.
The interpolation estimate \eqref{pvm:headrate} uses the explicit ceiling in
\texttt{CanonicalMobiusQuantitativeEnergy}. The results for matching finite heads are in \texttt{ParetoMixedCenteredParityHeads}
and \texttt{MixedConductorHead}, with the cofinal subpolynomial test in
\texttt{MixedParityCofinalSubpower}. The zeta obstruction is formalized in
\texttt{ThresholdRiemannHypothesis} and the converse premise in
\texttt{BaezDuarteNaturalApproximation}.
