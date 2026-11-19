# Mesoscopic spike and unit slope for the ordinate form factor

Write $L=\log T$, $u=\alpha L$, $x=e^u$ and $S=L^2/x^2+u$. Use the positive-height cutoff $0<\gamma\le T$ with each zero counted with its analytic multiplicity. The statistic $F_{\rm raw}(T,\alpha)$ is the Montgomery Cauchy-weighted double sum of the actual ordinates, divided by $TL/(2\pi)$. The corresponding complex-zero statistic is $F_\sharp(T,\alpha)$. The repository's exact weighted Gram comparison gives
\[
 \left|\sqrt{F_{\rm raw}}-\sqrt{F_\sharp}\right|\le\sqrt{D(T,\alpha)},
\]
where $D$ denotes `horizontalDefect`.

For any fixed Selberg density exponent $a>0$ supplied on the full strip, reflection plus the fourth tilted moment gives $D(T,\alpha)\ll_a(1+|u|)^4/L^3$ for $|u|\le aL/4$. Suppose $u=u(T)\to\infty$ and $u^3/L^2\to0$. The Cauchy-weighted raw form factor then satisfies
\[
 \frac{F_{\rm raw}(T,u/L)}{L e^{-2u}+u/L}\longrightarrow1.
\]
If also $L^2 e^{-2u}/u\to0$, then
\[
 \frac{F_{\rm raw}(T,u/L)}{u/L}\longrightarrow1.
\]
Thus the linear term has coefficient one throughout the spike-negligible range below $u=o(L^{2/3})$. The lower condition can be written $2u+\log u-2\log L\to+\infty$. Near $u\sim\log L$, it is $u-\log L+\tfrac12\log\log L\to+\infty$. For example both conclusions apply when $u=L^q$ with $0<q<2/3$. The frequency $\alpha=u/L$ shrinks to zero on every such path.

## A finite relative bound for the complex-zero statistic

Use BGSTB's positive-cutoff decomposition (3.4). Normalize by $TS$ before dividing by $TL$. Write $M_1,M_2$ for the logarithmic and prime-signal energies, and $E=T/x^2+x$ for the bound on the third signal. Throughout $1\le u\le L/2$, one has $x^2\le T$, $u\le x$, $S\ge u$ and $T\le TS/u$. The logarithmic mean square satisfies
\[
 |M_1-TL^2/x^2|\ll TL/x^2\ll TS/u .
\]
The prime estimate $M_2=Tu+O(T+x^2)$ supplies an error $O(T)\subseteq O(TS/u)$. Its diagonal is $D_{\rm prime}(x)=\log x+O(1)$, and the spacing-weighted mean-square inequality bounds the error before evaluating the diagonal. The first two energies add to $O(TS)$. Multiplying $E\ll T/u$ uses $x^2\le T$ for the term $x$ and $u\le x^2$ for $T/x^2$. Therefore the cross terms involving the third signal are bounded by
\[
 \sqrt{(M_1+M_2)E}\ll T\sqrt{S/u}\le TS/u .
\]
The signed logarithmic–prime cross integral is $O(T)$, as are the positive-cutoff endpoint errors $O(\sqrt T+x)$. Hence
\[
 \left|\frac{F_\sharp(T,u/L)}{S/L}-1\right|\ll \frac1u
 \quad(1\le u\le L/2).
\]
All constants are uniform in $u$ on this range. The stated typed sources keep the BGSTB third signal and prime mean square explicit. [BGSTB, corrected text, §3, (3.4) and (3.5)](https://arxiv.org/html/2501.14545v3#S3.E4) · [Montgomery–Vaughan, Hilbert's inequality](https://doi.org/10.1112/jlms/s2-8.1.73)

## Relative transfer to actual ordinates

With $S/L\ge u/L$ and $u\ge1$, the quartic estimate gives
\[
 \frac{D(T,u/L)}{S/L}\ll_a\frac{u^3}{L^2}.
\]
Dividing the Gram comparison by $\sqrt{S/L}$ and squaring the limiting ratio proves the first asymptotic. The additional spike condition gives $(S/L)/(u/L)=1+L^2e^{-2u}/u\to1$, proving the unit slope. In the range $u^3\le L^2$, the same inequalities give a quantitative relative error
\[
 \left|\frac{F_{\rm raw}(T,u/L)}{S/L}-1\right|
 \ll_a \frac1u+\frac{u^{3/2}}{L}.
\]
Indeed $F_\sharp/(S/L)$ is bounded, and the difference of the two squares is at most $D/(S/L)+2\sqrt{F_\sharp/(S/L)}\sqrt{D/(S/L)}$. With $u^3\le L^2$ the linear term in $\sqrt{D/(S/L)}$ also controls the quadratic term.

At the boundary $u=cL^{2/3}$ for fixed $c>0$, these scalar estimates allow $D/(S/L)$ to remain of order $c^3$. For example the nonnegative quantities $F_\sharp=S/L$, $D=u^4/L^3$ and $F_{\rm raw}=(\sqrt{F_\sharp}+\sqrt D)^2$ attain equality in the square-root comparison. This scalar model shows why this argument needs $u^3/L^2\to0$ for a unit relative limit. It makes no assertion about a lower bound for the actual zeta defect.

## Crossover and the full shrinking window

If the spike divided by the linear term tends to a finite $\lambda$, the raw form factor divided by $u/L$ tends to $1+\lambda$. For fixed real $c$ take
\[
 \ell=\log L,\qquad u=\ell-\tfrac12\log\ell+c.
\]
Here $L^2e^{-2u}/u=e^{-2c}\ell/u$ exactly, so $F_{\rm raw}/(u/L)\to1+e^{-2c}$. The relative error bound gives more. Uniformly on every fixed bounded interval of $c$,
\[
 \frac{F_{\rm raw}(T,u/L)}{u/L}
 =1+e^{-2c}+\frac{e^{-2c}}{2}\frac{\log\ell}{\ell}
   +O\left(\frac1\ell\right).
\]
Indeed $\ell/u=(1-(\tfrac12\log\ell-c)/\ell)^{-1}$, and the quadratic term from expanding this factor is $O((\log\ell)^2/\ell^2)$. It follows that $(\ell/\log\ell)(F_{\rm raw}/(u/L)-1-e^{-2c})\to e^{-2c}/2$. This crossover compares the two leading terms. At the earlier phase $u=(\log L+c)/2$, the spike itself tends to $e^{-c}$ and the linear term tends to zero.

There is also an exact balancing center $u_*=\tfrac12 W(2L^2)$, the unique positive solution of $u_*e^{2u_*}=L^2$. At $u=u_*+c$, the spike-to-linear ratio is exactly $e^{-2c}u_* /(u_*+c)$, and therefore the raw ratio equals $1+e^{-2c}+O_A(1/u_*)$ for bounded $c$. The logarithmic correction in the preceding display records the difference between the elementary center $\ell-\tfrac12\log\ell$ and the exact center. Indeed, substituting the elementary center in the equation $2u+\log u=2\ell$ and using the positive derivative $2+1/u$ gives
\[
 u_*=\ell-\tfrac12\log\ell+\frac{\log\ell}{4\ell}
   +O\left(\frac{(\log\ell)^2}{\ell^2}\right).
\]

The combined spike and linear main term extends uniformly down to phase zero. The corrected BGSTB estimate (3.5) bounds the absolute complex error by $O((Le^{-2u}+1)/\sqrt L)$. If $0\le u\le\tfrac12\log L$, the spike is at least one, and division by $S/L$ gives a relative error $O(L^{-1/2})$. Above $\tfrac12\log L$, the finite component ratio bound supplies a relative error $O(1/\log L)$. For $0\le u\le1$, the defect divided by $S/L$ is $O_a(L^{-4})$, since $S/L\ge e^{-2}L$. For $u\ge1$ it is $O_a(u^3/L^2)$. Consequently every nonnegative phase ceiling $U(T)=o(L^{2/3})$ satisfies
\[
 \sup_{0\le u\le U(T)}
 \left|\frac{F_{\rm raw}(T,u/L)}{Le^{-2u}+u/L}-1\right|\longrightarrow0.
\]
The exact evenness of the ordinate form factor extends the same uniform conclusion to $|u|\le U(T)$, with $|u|$ substituted in the main term. For the linear-only ratio, the additional spike-negligibility condition remains necessary for this main term.

A directly integrable consequence identifies the atom at zero in the Fourier variable. For $U\ge0$ and $L>0$ the exact two-sided model mass in $|\alpha|\le U/L$ is
\[
 \int_{-U/L}^{U/L}\bigl(Le^{-2|\alpha|L}+|\alpha|\bigr)\,d\alpha
 =1-e^{-2U}+(U/L)^2.
\]
Multiplying the uniform relative error by this positive model bounds the absolute error in the integral by the same relative tolerance times the model mass. For $U(T)\to\infty$ and $U(T)^3/L^2\to0$, the mass of the raw statistic in this shrinking interval therefore tends to one. For constant $U=A\ge0$, it tends to $1-e^{-2A}$. More generally one may insert any fixed bounded test function continuous at zero, since throughout this interval its uniform distance from its value at zero tends to zero. This determines the coefficient of the narrowing Fourier spike on this family of shrinking intervals. Control at fixed positive frequencies is a further requirement for a full Fourier pair-correlation statement.

The repository also proves a fourth tilted moment on the Ingham route which uses no near-line Selberg premise. It yields $D(T,u/L)\ll(1+|u|)^4(\log L)^4/L^3$ when $2|u|\le B L/\log L$ for any fixed $B>0$. Therefore the preceding two-term and unit-slope results for diverging $u$ hold on this route with $u^3(\log L)^4/L^2\to0$. This includes every $u=L^q$ with $0<q<2/3$ and the full finite-shift crossover. The named positive-cutoff third-signal and prime-side analytic estimates are still required.

Existing mesoscopic central limit theorems analyze integrated linear statistics of the zeros. The normalization above concerns a single Fourier frequency and the complete Cauchy-weighted pair sum at each height. The proof uses no hypothesis that the individual zeros lie on the critical line. Fixed positive $\alpha$ lies outside the mesoscopic range established here. [Rodgers, Bootstrapped zero density estimates and a central limit theorem for the zeros of the zeta function](https://doi.org/10.1142/S1793042115500918)
