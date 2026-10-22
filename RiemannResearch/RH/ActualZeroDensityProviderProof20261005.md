# Actual zero-density provider: unconditional paper proof and formalization boundary

This is a mathematical derivation from published analytic theorems. It is **not a Lean proof of their analytic inputs**. The repository already verifies the actual finite multiplicity counts, reflection, strict-tail layer cake, and operator transfer. The remaining Lean obligation is the zero-density estimate used in Section 2 below.

## 1. Actual counts and conventions

Let \(\rho=\beta+i\gamma\) run over the actual nontrivial zeros of the Riemann zeta function, with analytic multiplicity \(m(\rho)\). Put

\[
N(T)=\sum_{0<\gamma\le T}m(\rho),\qquad
N_{\ge}(\sigma,T)=\sum_{0<\gamma\le T,\ \beta\ge\sigma}m(\rho),
\]
\[
B_>(T,s)=\sum_{0<\gamma\le T,\ |\beta-1/2|>s}m(\rho).
\]

These are respectively the repository's original `Ncount 0 T`, `rightInclusiveCount T σ`, and `strictTail T s`. Good copies satisfy \(|\beta-1/2|\le\delta\); bad copies satisfy the strict complementary inequality. No renormalization by the bad count occurs.

Reflection \(\rho\mapsto1-\overline\rho\) preserves positive height and analytic multiplicity. For every \(s\ge0\), the left and right strict families are disjoint and exchanged by reflection. Therefore

\[
B_>(T,s)=2N_>(1/2+s,T)\le2N_{\ge}(1/2+s,T).\tag{1}
\]

Zeros exactly on the threshold are absent from the strict count. This inequality therefore applies directly to an inclusive density theorem, without assuming boundary zeros are absent or simple. Actual strip geometry also gives \(B_>(T,s)=0\) for \(s\ge1/2\).

## 2. The unconditional analytic input, with the finite count retained

Use Chourasiya–Simonič, **An explicit form of Ingham's zero density estimate**, arXiv:2507.15184v2, Theorem 1, Table 1, and the algebra in its proof of Corollary 1:

<https://arxiv.org/html/2507.15184v2#S2.SS1>

Fix the numerical height \(H=3\cdot10^{12}\). This selects the paper's parameters \(T_0=H_0=H\), \(h=1\), and the individual Table-1 rows. It does **not** assume RH below \(H\). The theorem bounds
\(N_{\ge}(\sigma,T)-N_{\ge}(\sigma,H)\), rather than requiring the finite count to vanish.

Write \(L=\log T\),
\[
a(\sigma)=\frac{3(1-\sigma)}{2-\sigma},\qquad
b(\sigma)=\frac{7-5\sigma}{2-\sigma}.
\]
For each Table-1 cell, the same calculation as equation (10), **before discarding its finite count**, yields

\[
N_{\ge}(\sigma,T)
\le N_{\ge}(\sigma,H)+B_1T^{a(\sigma)}L^{b(\sigma)}+B_2L^2+B_3L.\tag{2}
\]

In the first cell \([1/2,17/32]\), the displayed constants are
\((B_1,B_2,B_3)=(5.069,9.461,167.8)\). Its nontrivial application initially requires \(\sigma>1/2+0.28/L\). The paper proves the parameter functions decrease in the lower cell endpoint, so these constants are uniform when that endpoint approaches \(1/2\) with \(T\). Other cells have their prescribed parameters and satisfy the theorem's conditions for \(T\ge H\).

The short interval \(0\le s=\sigma-1/2\le0.28/L\) can be covered independently, without a finite RH certificate. Unconditional Riemann–von Mangoldt gives \(N(T)\le TL\) eventually. For \(L\ge2\),

\[
\frac{2s}{3/2-s}(L+\log L)
\le\frac{0.56}{1.36}\left(1+\frac{\log L}{L}\right)
\le\frac{21}{34}<1.
\]

Consequently the main term defined in Section 3 is at least \(e^{-1}TL^3\ge TL\). This covers the short interval uniformly. Thus (2) holds throughout each required interval for all sufficiently large \(T\), with no assertion about the value of \(N_{\ge}(\sigma,H)\). The eventual threshold here can depend only on the unconditional upper count estimate and the fixed published parameters; it does not depend on \(s\).

## 3. Exact stronger near-line exponent and constants

Define
\[
r(s)=\frac{2s}{3/2-s},\qquad
P=L+\log L,\qquad
M(T,s)=TL^3e^{-r(s)P}.
\]
Direct algebra gives
\[
a(1/2+s)=1-r(s),\qquad b(1/2+s)=3-r(s),
\]
so \(T^{a(1/2+s)}L^{b(1/2+s)}=M(T,s)\) exactly. Furthermore
\[
r(s)=\frac43s+\frac{8s^2}{9-6s},\qquad
r'(s)=\frac3{(3/2-s)^2},\qquad r''(s)=\frac6{(3/2-s)^3}>0.\tag{3}
\]

Let \(N_H=N(H)\), a finite actual count. Applying (1) and (2) yields, uniformly on \(0\le s\le1/32\),

\[
B_>(T,s)\le 2N_H+10.138M(T,s)+18.922L^2+335.6L.\tag{4}
\]

This retains every finite-height zero, including multiplicity. Since \(r(1/32)=2/47\),
\[
\inf_{0\le s\le1/32}M(T,s)=T^{45/47}L^{139/47}.
\]
The three remainder terms in (4), divided by this infimum, tend to zero. Hence the following **uniform shrinking-window provider is unconditional at the paper level**:

> For every \(C>10.138\), there exists \(T_C\) such that for all \(T\ge T_C\) and every \(s\in[0,1/32]\),
> \[
> B_>(T,s)\le C\,TL^3\exp\left[-\frac{2s}{3/2-s}(L+\log L)\right].\tag{5}
> \]

For example, \(C=10.14\) is valid. The quantifiers permit any \(s=s(T)\to0\), including \(s\asymp1/\sqrt{\log T}\). No implied constant depends on that changing \(s\).

For the larger near-line interval \(0\le s\le3/8\), the coordinate maxima of the first twelve Table-1 rows are \(21.77,9.461,167.8\). Therefore
\[
B_>(T,s)\le2N_H+43.54M(T,s)+18.922L^2+335.6L.\tag{6}
\]
Here \(r(3/8)=2/3\), so the uniform minimum is \(T^{1/3}L^{7/3}\). Every \(C>43.54\), in particular \(44\), replaces the right side of (6) by \(CM(T,s)\) eventually, uniformly in \(s\).

## 4. A convenient provider on the entire actual strip

Put \(\bar r(s)=\min\{r(s),2/3\}\) for \(0\le s\le1/2\). Monotonicity of the actual strict tail gives \(B_>(T,s)\le B_>(T,3/8)\) for \(s\ge3/8\). Thus (6) proves

\[
B_>(T,s)\le44TL^3e^{-\bar r(s)(L+\log L)}
\quad(0\le s\le1/2)\tag{7}
\]
for all sufficiently large \(T\), uniformly over the entire interval. Since \(\bar r(s)\ge4s/3\) there, this immediately supplies the exponential hypothesis used by the verified operator consumer:

\[
\boxed{\ B_>(T,s)\le44TL^3
\exp\left[-\frac43(L+\log L)s\right]\quad(0\le s\le1/2).\ }\tag{8}
\]

The earlier proposed \(400TL^3e^{-4Ls/3}\) is therefore an eventual consequence with a looser constant and exponent. Equation (8) is a stronger substitute that needs no finite RH certificate.

If the exact nonlinear exponent is preferred on the whole strip, all sixteen rows can instead be used. Their maximum \(B_1+B_2\) is \(46.06+4.897=50.957\), while \(B_3\le167.8\). Since \(M(T,s)\ge L^2\) on \([0,1/2]\), they imply
\[
B_>(T,s)\le101.914M(T,s)+335.6L+2N_H.\tag{9}
\]
Thus the all-strip nonlinear version with constant \(102\) also holds eventually and uniformly. Equation (7) has a smaller constant; equation (9) retains stronger decay far to the right. Both finite-count versions (6) and (9) remain available when no unspecified eventual threshold is desired.

## 5. Exact weighted/operator consequences

For \(\phi(s)=\cosh(\ell s)-1\), \(\ell\ge0\), the verified finite layer cake is
\[
W(T,\delta,\ell)=\phi(\delta)B_>(T,\delta)
+\ell\int_\delta^{1/2}B_>(T,s)\sinh(\ell s)\,ds.
\]
The actual reflected bad operator obeys
\[
\|\mathcal B\|\le\frac{d}{2N(T)}W(T,\delta,\ell),\qquad\ell=\log d.
\]
With (8), use \(K=44TL^3\), \(q=\tfrac43(L+\log L)\). Whenever \(q>\ell\), the already verified closed transfer gives
\[
\|\mathcal B\|\le\frac{22dTL^3}{N(T)}F(q,\ell,\delta),
\]
\[
F=(\cosh(\ell\delta)-1)e^{-q\delta}
+\frac\ell2\left[
\frac{e^{-(q-\ell)\delta}-e^{-(q-\ell)/2}}{q-\ell}
-\frac{e^{-(q+\ell)\delta}-e^{-(q+\ell)/2}}{q+\ell}
\right].\tag{10}
\]
Original count normalization and both finite endpoint terms remain explicit.

The stronger local provider (5) can be retained by splitting the integral at \(s_0=1/32\); the part above \(s_0\) is bounded by
\[
B_>(T,s_0)\bigl(\phi(1/2)-\phi(s_0)\bigr).
\]
On \([\delta,s_0]\), convexity in (3) gives a tangent exponential majorant with
\[
q_\delta=Pr'(\delta),\qquad
K_\delta=CTL^3\exp\left[\frac{2\delta^2P}{(3/2-\delta)^2}\right],
\]
because \(r(\delta)-\delta r'(\delta)=-2\delta^2/(3/2-\delta)^2\). Apply the same exact integral formula with upper endpoint \(s_0\). This improves finite-height estimates without dropping the far-tail contribution.

## 6. The leading square-root-log coefficient

For the current norm bootstrap, the complete fixed-c=2 scalar provider in Analysis/ActualUniformRationalLandau.lean yields the Landau error \(\alpha(T)\to0\) by the elementary operator bound and actual count normalization at the scale below. This asymptotic operator assembly is a mathematical deduction, not a new Lean declaration. Let \(\ell=\log d\sim c\sqrt L\). A scalar exponential density rate \(q\sim\kappa L\) permits choosing
\[
\delta=\frac{\ell+(2+\varepsilon)\log L}{q-\ell},\qquad\varepsilon>0.
\]
Using \(N(T)\gg TL\), the exponential bad budget tends to zero, whereas \(\delta\ell\to c^2/\kappa\). The verified sufficient frame gap \(\alpha+\beta+\cosh(\delta\ell)<2\) follows when
\[
c<\sqrt{\kappa\operatorname{arcosh}2}.
\]
For (8), \(\kappa=4/3\), giving
\[
c<\sqrt{\frac43\operatorname{arcosh}2}=1.325120320033778\ldots.\tag{11}
\]
Exact nonlinear decay does not increase this leading coefficient: \(r(s)/s\to4/3\). At \(\delta\sim(3/4)\ell/L\), its quadratic improvement contributes a factor tending to \(e^{-c^2/2}\), a useful constant rather than a larger power-saving slope. The additional \(\log\log T\) in (8) is likewise lower order. These conclusions concern this theorem and this bootstrap; they do not assert an optimality barrier for future analytic or operator methods.

There is a distinct endpoint refinement. Let \(c_*=\sqrt{\kappa\operatorname{arcosh}2}\), set \(\ell=c_*\sqrt L-a\log L\), and keep the preceding choice of \(\delta\), with \(q=\kappa(L+\log L)\). Then
\[
\delta\ell=\operatorname{arcosh}2+
\frac{c_*}{\kappa}(2+\varepsilon-2a)\frac{\log L}{\sqrt L}
+\frac{c_*^3}{\kappa^2\sqrt L}
+O\left(\frac{(\log L)^2}{L}\right).
\]
Thus \(a>(2+\varepsilon)/2\), \(\varepsilon>1/2\), and an independent Landau rate \(\alpha=o(\log L/\sqrt L)\) give the frame gap even with the critical **leading** coefficient \(c_*\), at the price of this subleading dimension loss. This attains the same leading endpoint; it does not raise its value. The sufficient fixed-c=2 Landau provider gives the required rate after the arithmetic main operator and actual count normalization, while the actual exponential density theorem and asymptotic spectral assembly remain unformalized.

## 7. Other unconditional primary inputs checked

- Simonič, *Explicit zero density estimate for the Riemann zeta-function near the critical line*, arXiv:1910.08274v2, Theorem 1: a dyadic Selberg-type estimate with rate \(\tfrac14sL\), leading coefficient \(10395.2\), and additive \(1.104L^2+0.173L\log L+0.51L\). Its introduction distinguishes Jutila's improvement to rates \(1-\varepsilon\) and Conrey's announced \(8/7-\varepsilon\). Their leading logarithm is \(L\), useful very close to the line, but their rates do not exceed \(4/3\). Its finite-height aggregate corollary uses a verified low-height zero result; the dyadic theorem can instead be summed while retaining the finite initial count. <https://arxiv.org/pdf/1910.08274>
- Maples–Rodgers, *Bootstrapped zero density estimates and a central limit theorem for the zeros of the zeta function*, Theorem 2.4 and equation (18): for each fixed \(0<c<1\), a uniform \(TL e^{-csL}\) bound and its actual reflected displacement form. Their local-moment bootstrap supplies further weighted information, but does not increase the needed near-line slope beyond \(4/3\). <https://arxiv.org/pdf/1404.3080>
- Guth–Maynard, *New large value estimates for Dirichlet polynomials*, Theorem 1.2: exponent \(15(1-\sigma)/(3+5\sigma)+o(1)\). At \(\sigma=1/2\) it is \(15/11>1\), so this theorem alone does not provide a stronger shrinking near-line tail. Their paper combines it with Ingham below \(7/10\). <https://arxiv.org/pdf/2405.20552>
- The July 2026 survey by Turnage-Butterbaugh, *A decades-long breakthrough in zero-density estimates and primes in short intervals*, Theorem 4.3, confirms the uniformly stated Guth–Maynard exponent and its \(7/10\) crossover. It is an exposition of that result, not a new near-line slope improvement. <https://arxiv.org/pdf/2607.04632>

The sharper constants, nonlinear exponent, and finite-count retention above are deductions from the unconditional analytic theorem. Lean currently verifies the finite identities and transfer, while formalizing Theorem 1 still requires the mollifier estimates, critical-line fourth moment, Gabriel convexity, and Littlewood zero-count inequality. This draft supplies neither an axiom nor a placeholder declaration for those missing analytic proofs.
