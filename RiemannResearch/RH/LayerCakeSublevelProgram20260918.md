# RH Layer-Cake Sublevel Program and the Next Promising Attack

**Date:** 2026-09-16
**Program:** Semilocal/Weil-positivity route to the Riemann Hypothesis
**Status:** Research handoff; rigorous statements, counterexamples, and open obligations are separated explicitly.

> **Continuation and audit, 2026-09-16:** Sections 20–31 below are the current continuation. They make the pole completion explicit, correct the error metric in the certificate, strengthen the removable-layer estimate, and prove that cofinal lower bounds tending to zero already suffice for RH. They also establish a nonvanishing Fourier core-to-tail obstruction at \(L=\log5\). Sections 1–19 are retained as the supplied handoff; where there is a conflict, the corrections in Sections 20–31 take precedence. No proof of RH or new interval-certified endpoint positivity is claimed.

> **Second continuation, 2026-09-16:** Sections 32–40 are now the latest results. They prove unconditional positivity for sparse vectors in the shrinking-mesh matrices and show why this does not control collective directions. They also strengthen the research reduction: even a lower bound with polynomial loss in logarithmic support, relative to \(\mathcal D\), already implies RH. Such a bound remains open. The earlier vanishing-error targets are valid but stronger than necessary.

---

## Executive summary

The active route is to prove positivity of the localized Weil quadratic form on every compact logarithmic support interval. A cofinal sequence of positive support lengths would already imply global Weil positivity and therefore the Riemann Hypothesis.

The latest successful reduction writes the localized form as a compressed multiplication operator

\[
T_{c_L}=\mathcal F_{I_L}^{*}M_{c_L}\mathcal F_{I_L},
\]

where \(I_L\) is the physical logarithmic support interval and

\[
c_L(t)=c_{\infty,L}(t)+\mathcal P_L(t)
\]

is the completed archimedean-plus-prime multiplier. The prime-power term is

\[
\mathcal P_L(t)
=
-2\sum_{\substack{q=p^m\\ \log q\le L}}
\frac{\Lambda(q)}{\sqrt q}\cos(t\log q).
\]

Three parts of the most recent attack are rigorous:

1. exact one- and two-point means and covariances of \(\mathcal P_L\);
2. joint Bernstein–Chernoff estimates and a bivariate central-limit scaling law;
3. a layer-cake positivity criterion reducing the form to prolate concentration norms of arithmetic sublevel sets.

The program then encountered two exact obstructions:

- asymptotic or long-interval density does not control finite-scale prolate concentration;
- a low-band smoothing kernel that annihilates the prime polynomial cannot reproduce all test functions once the support length reaches the first prime displacement \(\log 2\).

The next promising attack is therefore not another global large-deviation estimate. It is a **physical-space displacement-layer decomposition**. Prime powers with \(\log q\) extremely close to the support diameter interact only through narrow boundary strips. Their entire contribution is explicitly form-small. This allows one to strip off the endpoint layer and reduce the problem to a finite middle block plus a coercive Fourier tail.

A new rigorous estimate proved below is:

\[
\left|\mathfrak P^{\mathrm{bd}}_{L,\Delta}[f]\right|
\le
C\,W_{L,\Delta}
\left[
\sqrt\Delta\,\|f\|_2^2
+
\frac{\mathcal E_{\log}[f]}
{\log(2+\Delta^{-1/2})}
\right],
\]

where

\[
W_{L,\Delta}
=
2\sum_{\substack{q=p^m\\L-\Delta<\log q\le L}}
\frac{\Lambda(q)}{\sqrt q}
\]

and \(\mathcal E_{\log}\) is the logarithmic archimedean energy. For \(\Delta_L=e^{-L}\), one gets

\[
W_{L,\Delta_L}=O(Le^{-L/2}),
\]

hence the boundary-displacement block is exponentially form-small. This is a genuine uniform cofinal reduction.

What remains is to prove positivity of the **interior displacement block**, after the exponentially thin endpoint layer has been removed. The best next implementation is a hybrid:

\[
\boxed{
\text{boundary-layer stripping}
+
\text{finite semilocal core}
+
\text{displacement-rank/rational-Krylov tail certification}.
}
\]

---

## 1. Source status and noncircularity

The published operator-algebraic RH equivalences still live in the adele-class-space trace formula and Weil positivity. The semilocal program provides unconditional trace-formula and local positivity mechanisms, but globalized semilocal positivity remains unproved.

The prime KMS tower provides a rigorous GNS norm for the prime-power side and a rigorous modular explicit-formula identity. It does **not** yet provide the archimedean correction as a semibounded operator on the same GNS space, nor the final positivity inequality.

Accordingly, every statement below is classified as one of:

- **proved rigorously**;
- **proved under stated assumptions**;
- **reduced to a precise lemma**;
- **false or obstructed**;
- **heuristic/numerically supported**.

No RH-strength inequality is treated as proved merely because it has been reformulated.

---

## 2. Localized multiplier formulation

Let \(I_L\subset\mathbb R\) be a logarithmic interval of length \(L\), and extend \(f\in L^2(I_L)\) by zero to \(\mathbb R\). With the unitary Fourier transform, the localized Weil form can be written

\[
Q_L[f]
=
\int_{\mathbb R}c_L(t)|\widehat f(t)|^2\,dt,
\]

where

\[
c_L(t)=c_{\infty,L}(t)+\mathcal P_L(t).
\]

The finite prime-power polynomial is

\[
\mathcal P_L(t)
=
-2\sum_{q\in\mathcal Q_L}a_q\cos(\lambda_qt),
\qquad
\mathcal Q_L=\{q=p^m:\log q\le L\},
\]

with

\[
a_q=\frac{\Lambda(q)}{\sqrt q},
\qquad
\lambda_q=\log q.
\]

The archimedean part has logarithmic high-frequency growth:

\[
c_{\infty,L}(t)
=
\kappa\log(2+|t|)+O_L(1),
\qquad \kappa>0.
\]

The corresponding compressed multiplier is

\[
T_{c_L}
=
\mathcal F_{I_L}^{*}M_{c_L}\mathcal F_{I_L}.
\]

Proving \(T_{c_L}\ge0\) for a cofinal sequence \(L_j\to\infty\) implies positivity for every compactly supported Weil test and hence RH.

**Status:** rigorous reduction.

---

## 3. Exact mean, covariance, and variance identities

### 3.1 Bohr mean

Distinct prime powers give distinct logarithmic frequencies. Therefore

\[
\mathbb M(\mathcal P_L)=0.
\]

### 3.2 Variance

Orthogonality of distinct cosine frequencies gives

\[
V_L
:=
\mathbb M(\mathcal P_L^2)
=
2\sum_{q\in\mathcal Q_L}\frac{\Lambda(q)^2}{q}.
\]

The higher prime powers contribute \(O(1)\), while the first powers give

\[
V_L=L^2+O(1).
\]

### 3.3 Two-point covariance

For every displacement \(u\),

\[
C_L(u)
:=
\mathbb M\bigl(\mathcal P_L(t+u)\mathcal P_L(t)\bigr)
=
2\sum_{q\in\mathcal Q_L}
\frac{\Lambda(q)^2}{q}
\cos(u\log q).
\]

Using the prime number theorem,

\[
C_L(u)
=
2\int_0^Ly\cos(uy)\,dy+O_u(1).
\]

Thus, for fixed nonzero \(u\),

\[
\frac{C_L(u)}{V_L}=O_u(L^{-1}),
\]

while on the microscopic scale \(u=s/L\),

\[
\frac{C_L(s/L)}{V_L}
\longrightarrow
\rho(s)
=
2\frac{\sin s}{s}
+2\frac{\cos s-1}{s^2}.
\]

Hence the natural prime-correlation length is \(L^{-1}\).

**Status:** proved rigorously.

---

## 4. Joint Chernoff and Gaussian scaling

Group harmonics prime by prime:

\[
X_{p,L}(\theta)
=
-2(\log p)
\sum_{1\le m\le L/\log p}
p^{-m/2}\cos(m\theta).
\]

On the finite prime torus the blocks are independent. Their uniform amplitude is bounded by

\[
|X_{p,L}|\le b_*
:=
\frac{2\log2}{\sqrt2-1}.
\]

For

\[
X_L=\sum_pX_{p,L}(\theta_p),
\qquad
Y_{L,u}=\sum_pX_{p,L}(\theta_p+u\log p),
\]

one has covariance matrix

\[
\begin{pmatrix}
V_L&C_L(u)\\
C_L(u)&V_L
\end{pmatrix}.
\]

For \(x,y>0\),

\[
\begin{aligned}
\Pr(X_L\le-x,Y_{L,u}\le-y)
\le
\inf_{\substack{s,t\ge0\\b_*(s+t)<3}}
\exp\Bigg[
&-sx-ty\\
&+
\frac{(s^2+t^2)V_L+2stC_L(u)}
{2(1-b_*(s+t)/3)}
\Bigg].
\end{aligned}
\]

At scale \(u=s/L\), the normalized vector converges to the corresponding bivariate Gaussian:

\[
\left(\frac{X_L}{L},\frac{Y_{L,s/L}}{L}\right)
\Longrightarrow
N\!\left(0,
\begin{pmatrix}
1&\rho(s)\\
\rho(s)&1
\end{pmatrix}
\right).
\]

This shows that thresholds of size \(O(L)\) have nonvanishing joint density. They are not rare events.

**Status:** proved rigorously.

---

## 5. Uniform long-interval transfer

The numbers \(\{\log p\}\) are rationally independent. The prime flow on every fixed finite prime torus is uniquely ergodic. Consequently, for each fixed \(L\), fixed displacement \(u\), and continuity set \(A\) in the finite torus,

\[
\lim_{H\to\infty}
\sup_T
\left|
\frac1H\int_T^{T+H}1_A\bigl((t\log p)_p\bigr)\,dt
-
\mu_{\mathrm{Haar}}(A)
\right|=0.
\]

This transfers the joint Chernoff estimate to physical intervals, uniformly in the starting point, provided the interval length tends to infinity **after \(L\) is fixed**.

The transfer is qualitative. A direct quantitative Kronecker estimate requires interval lengths of order

\[
\exp(\Theta(e^L)),
\]

while the full arithmetic sublevel set is already confined to a region of radius at most

\[
\exp(O(e^{L/2})).
\]

Thus the quantitative torus scale is much larger than the whole region where the sublevel set exists.

**Status:** qualitative theorem proved; quantitative route obstructed.

---

## 6. Deterministic spectral-gap smoothing

Every prime frequency satisfies \(|\lambda_q|\ge\log2\). Choose a nonnegative probability kernel \(K\) whose Fourier transform is supported in

\[
\left(-\frac{\log2}{2},\frac{\log2}{2}\right).
\]

Then

\[
K*\mathcal P_L=0.
\]

If

\[
G_{L,r}=\{t:\mathcal P_L(t)\ge-r\},
\]

then for every \(x\),

\[
(K*1_{G_{L,r}})(x)
\ge
\frac{r}{A_L+r},
\qquad
A_L=\|\mathcal P_L\|_\infty.
\]

Likewise, for the joint bad set

\[
B_{L,r,u}
=
\{t:\mathcal P_L(t)<-r,\ \mathcal P_L(t+u)<-r\},
\]

one has

\[
(K*1_{B_{L,r,u}})(x)
\le
\frac{A_L}{A_L+r}.
\]

This is a genuine finite-scale, uniform-in-\(x\) anti-concentration theorem.

### Bandwidth obstruction

If \(f\) is supported on an interval of length \(L\), then \(|\widehat f|^2\) has Fourier support in \([-L,L]\). To turn the smoothed density estimate into a direct prolate concentration bound, one would need \(\widehat K=1\) on \([-L,L]\). But annihilating \(\mathcal P_L\) requires \(\widehat K\) to be supported inside \((-\log2,\log2)\).

These requirements are incompatible once \(L\ge\log2\).

**Status:** finite-scale theorem proved; direct conversion to full-band positivity obstructed.

---

## 7. Layer-cake prolate criterion

Fix \(\tau>0\), and define

\[
S_{L,s}
=
\{t:c_L(t)<\tau-s\},
\qquad s\ge0.
\]

Pointwise,

\[
(\tau-c_L(t))_+
=
\int_0^\infty1_{S_{L,s}}(t)\,ds.
\]

After compression to the physical interval,

\[
T_{c_L}
\ge
\tau I-
\int_0^\infty
\mathcal C(S_{L,s})\,ds,
\]

where

\[
\mathcal C(S)
=
\mathcal F_{I_L}^{*}M_{1_S}\mathcal F_{I_L}.
\]

Therefore:

\[
\boxed{
\int_0^\infty\|\mathcal C(S_{L,s})\|\,ds<\tau
\quad\Longrightarrow\quad
T_{c_L}>0.
}
\]

This is the exact finite-scale layer-cake concentration theorem.

**Status:** proved rigorously.

---

## 8. Why density information does not finish the prolate step

The norm \(\|\mathcal C(S)\|\) depends on the full two-point geometry of \(S\), not only on its density. One has

\[
\|\mathcal C(S)\|_{\mathrm{HS}}^2
=
\int_{\mathbb R}
\left|\frac{\sin\pi u}{\pi u}\right|^2
|S\cap(S-u)|\,du.
\]

A set may have asymptotic density zero and still capture almost all Fourier mass. For example,

\[
S_R=[-R,R]
\]

has density zero as the averaging interval grows, but

\[
\|\mathcal C(S_R)\|\to1
\]

as \(R\to\infty\).

Thus exact means, one-point deviations, and even asymptotic two-point densities do not by themselves control the finite-scale prolate norm.

**Status:** concrete obstruction.

---

# Part II. The next promising attack

## 9. Split by physical displacement, not by torus frequency

For a prime power \(q\), put

\[
y_q=\log q,
\qquad
w_q=\frac{\Lambda(q)}{\sqrt q}.
\]

In physical logarithmic coordinates, multiplication by \(e^{ity_q}\) corresponds to translation by \(y_q\). The prime contribution is therefore a weighted sum of truncated shifts.

For \(0<\Delta<L\), split

\[
\mathcal Q_L
=
\mathcal Q_{L,\Delta}^{\mathrm{int}}
\sqcup
\mathcal Q_{L,\Delta}^{\mathrm{bd}},
\]

where

\[
\mathcal Q_{L,\Delta}^{\mathrm{bd}}
=
\{q:e^{L-\Delta}<q\le e^L\}.
\]

These are the prime powers whose shifts are within \(\Delta\) of the full support diameter.

The key observation is geometric: a shift by \(y>L-\Delta\) can pair only the left and right boundary strips of width at most \(\Delta\).

---

## 10. Boundary-overlap lemma

Let \(I_L=(0,L)\), extend \(f\) by zero, and let

\[
(\tau_yf)(x)=f(x-y).
\]

For \(L-\Delta<y\le L\), set \(h=L-y\in[0,\Delta)\). Then

\[
\langle f,\tau_yf\rangle
=
\int_0^h
\overline{f(x+y)}f(x)\,dx.
\]

Therefore

\[
|\langle f,\tau_yf\rangle|
\le
\|f\|_{L^2(0,h)}
\|f\|_{L^2(L-h,L)}.
\]

Using \(2ab\le a^2+b^2\),

\[
\boxed{
|\langle f,\tau_yf\rangle|
\le
\frac12
\|1_{\partial_\Delta I_L}f\|_2^2,
}
\]

where

\[
\partial_\Delta I_L
=(0,\Delta)\cup(L-\Delta,L).
\]

**Status:** proved rigorously.

---

## 11. Explicit logarithmic boundary-mass inequality

Define the logarithmic Fourier energy

\[
\mathcal E_{\log}[f]
:=
\int_{\mathbb R}
\log(2+|\xi|)
|\widehat f(\xi)|^2\,d\xi.
\]

Let \(E\subset\mathbb R\) be measurable with \(|E|=\delta\le1\). Split

\[
f=f_{\le R}+f_{>R}
\]

at Fourier radius \(R\ge1\). Then

\[
\int_E|f|^2
\le
2\int_E|f_{\le R}|^2
+2\|f_{>R}\|_2^2.
\]

By Cauchy–Schwarz in Fourier space,

\[
\|f_{\le R}\|_\infty^2
\le
C R\|f\|_2^2,
\]

while

\[
\|f_{>R}\|_2^2
\le
\frac{\mathcal E_{\log}[f]}
{\log(2+R)}.
\]

Choose \(R=\delta^{-1/2}\). Then

\[
\boxed{
\int_E|f|^2
\le
C\sqrt\delta\,\|f\|_2^2
+
\frac{C\,\mathcal E_{\log}[f]}
{\log(2+\delta^{-1/2})}.
}
\]

The constant depends only on the Fourier normalization.

Applying this to the two boundary strips, whose total measure is \(2\Delta\), gives

\[
\boxed{
\|1_{\partial_\Delta I_L}f\|_2^2
\le
C\sqrt\Delta\,\|f\|_2^2
+
\frac{C\,\mathcal E_{\log}[f]}
{\log(2+\Delta^{-1/2})}.
}
\]

**Status:** proved rigorously.

---

## 12. Exponentially thin boundary-displacement block

Define

\[
W_{L,\Delta}
:=
2\sum_{\substack{q=p^m\\L-\Delta<\log q\le L}}
\frac{\Lambda(q)}{\sqrt q}.
\]

The boundary prime block satisfies

\[
\begin{aligned}
|\mathfrak P_{L,\Delta}^{\mathrm{bd}}[f]|
&\le
W_{L,\Delta}
\sup_{L-\Delta<y\le L}
|\langle f,\tau_yf\rangle|\\
&\le
\frac12W_{L,\Delta}
\|1_{\partial_\Delta I_L}f\|_2^2.
\end{aligned}
\]

Hence

\[
\boxed{
|\mathfrak P_{L,\Delta}^{\mathrm{bd}}[f]|
\le
C W_{L,\Delta}
\left[
\sqrt\Delta\,\|f\|_2^2
+
\frac{\mathcal E_{\log}[f]}
{\log(2+\Delta^{-1/2})}
\right].
}
\]

Now use only the elementary estimates

\[
\Lambda(q)\le L,
\qquad
q^{-1/2}\le e^{-(L-\Delta)/2},
\]

and

\[
\#\{q\in\mathbb N:e^{L-\Delta}<q\le e^L\}
\le
 e^L-e^{L-\Delta}+1.
\]

Thus, for \(0<\Delta\le1\),

\[
\boxed{
W_{L,\Delta}
\le
C L\bigl(e^{L/2}\Delta+e^{-L/2}\bigr).
}
\]

Choose

\[
\Delta_L=e^{-L}.
\]

Then

\[
W_{L,\Delta_L}=O(Le^{-L/2}),
\]

and

\[
\log(2+\Delta_L^{-1/2})\asymp L.
\]

Therefore

\[
\boxed{
|\mathfrak P_{L,\Delta_L}^{\mathrm{bd}}[f]|
\le
C e^{-L/2}\mathcal E_{\log}[f]
+
CLe^{-L}\|f\|_2^2.
}
\]

This is a uniform cofinal form-smallness theorem for the endpoint displacement layer.

**Status:** proved rigorously.

---

## 13. What this reduction accomplishes

Write

\[
T_{c_L}
=
T_{L}^{\mathrm{int}}
+
T_{L}^{\mathrm{bd}},
\]

where the boundary block contains only shifts with

\[
L-e^{-L}<\log q\le L.
\]

Then

\[
\|T_{L}^{\mathrm{bd}}\|_{\mathrm{form}}
=O(e^{-L/2}).
\]

Therefore positivity reduces to the interior operator with all arithmetic displacements separated from the endpoint by at least \(e^{-L}\), plus an exponentially small form perturbation.

At an arithmetic endpoint \(L=\log N\), the endpoint shift \(q=N\) has zero overlap and contributes nothing. With \(\Delta_L<\log(N/(N-1))\), the entire boundary layer is empty except possibly for that vanishing endpoint term.

This gives a clean endpoint normalization for future interval certificates.

---

## 14. Next implementation: finite middle block plus coercive tail

The remaining operator is

\[
T_L^{\mathrm{int}}
=
T_{c_{\infty,L}}
+
\sum_{\log q\le L-e^{-L}}
T_q.
\]

The most promising route is now:

1. **Finite Fourier core.** Choose \(P_N\) on the Fourier basis and interval-evaluate the exact finite matrix.
2. **Displacement-rank compression.** Use the divided-difference/rank-two commutator structure to compress the core-to-tail block into a rational Krylov space.
3. **Coercive high Fourier tail.** Use the logarithmic growth of the diagonal archimedean term and a bounded commutator estimate for the off-diagonal part.
4. **Boundary-layer budget.** Add the explicit exponentially small error from Section 12.
5. **Interval Schur certificate.** Prove
   \[
   F_{L,N,k,m}(0)
   \succeq
   \eta_{L,N,k,m}I
   \]
   with a margin exceeding the sum of the rational-Krylov tail error and the boundary-layer budget.

This is a fully finite, self-adjoint certificate at each endpoint. The unresolved cofinal issue is to prove that these finite core margins remain positive along an unbounded endpoint sequence.

---

## 15. New narrow obligation

The endpoint layer is no longer the obstruction. The remaining decisive statement is:

### Cofinal interior-core theorem

Construct an unbounded arithmetic endpoint sequence \(L_j\to\infty\) and finite parameters \((N_j,k_j,m_j)\) such that

\[
\boxed{
\lambda_{\min}
F_{L_j,N_j,k_j,m_j}(0)
>
\eta_{L_j,N_j,k_j,m_j}
+
Ce^{-L_j/2}.
}
\]

The right side contains:

- the certified rational-Krylov/Feshbach tail error;
- the exponentially small boundary-displacement layer.

A proof produces localized positivity at a cofinal sequence and therefore global Weil positivity and RH.

**Status:** precise open theorem.

---

## 16. Circularity audit

The following are noncircular and rigorous:

- exact prime covariance and joint Chernoff bounds;
- bivariate Gaussian scaling;
- qualitative uniform long-interval transfer;
- spectral-gap smoothing;
- the layer-cake prolate criterion;
- the boundary-overlap lemma;
- the logarithmic boundary-mass estimate;
- exponential form-smallness of the endpoint displacement layer.

The following routes are false or insufficient:

- one-point density alone controlling prolate concentration;
- asymptotic two-point density alone controlling finite-scale concentration;
- low-band smoothing after \(L\ge\log2\);
- generic inner/Hardy positivity without arithmetic compensation.

The remaining cofinal interior-core theorem is RH-strength. It is not assumed or hidden in any previous estimate.

---

## 17. Companion certificate packages

- [Combined \(L=\log3\) and \(L=\log4\) endpoint certificates](./semilocal_endpoint_certificates_log3_log4.zip)
- [One-prime \(L=\log3\) certificate](./one_prime_log3_certificate.zip)
- [Two-prime \(L=\log4\) certificate](./two_prime_log4_certificate.zip)

These are the existing rigorous finite endpoint computations on which the next cofinal certificate program builds.

---

## 18. Recommended next calculation

The immediate practical target is \(L=\log5\):

1. remove the endpoint \(q=5\) term, which has zero overlap;
2. strip the \(e^{-L}\)-boundary layer using Section 12;
3. construct the exact finite core including \(q=2,3,4\);
4. use displacement-rank rational Krylov compression rather than the crude bound \(2\sup|b_n|\);
5. interval-certify the Schur complement.

Success at \(\log5\) would not prove cofinal positivity, but it would test whether the new boundary-layer reduction meaningfully improves the certificate margin beyond the existing \(\log3\) and \(\log4\) results.

---

## 19. Concise final status

### Proved rigorously

- Exact one- and two-point prime statistics.
- Joint Chernoff and bivariate CLT.
- Uniform long-interval transfer for fixed \(L\).
- Deterministic spectral-gap smoothing.
- Exact layer-cake prolate criterion.
- Boundary-overlap and logarithmic boundary-mass inequalities.
- Exponentially small endpoint displacement layer for \(\Delta_L=e^{-L}\).

### False or obstructed

- Density-only control of prolate concentration.
- Quantitative Kronecker transfer on the relevant finite scale.
- Low-band smoothing at full test bandwidth.

### Exact remaining theorem

\[
\boxed{
\text{Cofinal positivity of the finite interior Schur complements.}
}
\]

### Next promising attack

\[
\boxed{
\text{Boundary-layer stripping}
+
\text{exact arithmetic finite core}
+
\text{displacement-rank rational Krylov tail control}.
}
\]

---

# Part III. Continuation: exact boundary energy, cofinal tolerances, and the signed tail obstruction

## 20. What the continuation proves

The following results are proved below without assuming RH.

1. The archimedean term has an exact positive difference-energy decomposition with an explicit boundary potential. This gives a direct boundary-mass estimate without an auxiliary Fourier cutoff.
2. The endpoint layer can be enlarged from width \(e^{-L}\) to
   \[
   \Delta_L=\frac{e^{-L/2}}{L^2}.
   \]
   The resulting omitted prime operator has norm \(O(L^{-1})\). In the integer variable this layer has length asymptotic to \(e^{L/2}/L^2\), which tends to infinity.
3. A cofinal family of lower bounds tending to zero from below suffices for RH. This remains true for lower bounds relative to a fixed, compatible archimedean energy. Strictly positive endpoint margins are unnecessary for this implication.
4. At \(L=\log5\), the exact signed prime matrix has Fourier core-to-tail coupling whose norm has a strictly positive limsup. A rank-two displacement formula does not supply a vanishing truncation error.
5. The complete signed Schur complement admits an exact residual identity. It gives a valid certificate for the relaxed lower bounds in item 3.
6. There is an explicit nested family of finite matrices for which asymptotic approximate positivity is equivalent to RH. A uniform theorem for this family would avoid separately certifying an infinite tail at each support length.

Items 3 and 6 are reductions, not proofs of their RH-strength hypotheses. The missing estimate is still signed interior positivity, now formulated with the weaker and sufficient target of a lower bound tending to zero.

## 21. Specify the completed Weil form before estimating it

### 21.1 Conventions and the pole term

Use
\[
\widehat f(t)=\frac1{\sqrt{2\pi}}\int_{\mathbb R}f(x)e^{-itx}\,dx,
\qquad
\langle f,g\rangle=\int_{\mathbb R}\overline{f(x)}g(x)\,dx.
\]
Initially take \(f\in C_c^\infty(0,L)\), extended by zero. Write
\[
a(t)=\operatorname{Re}\psi\!\left(\frac14+\frac{it}{2}\right)-\log\pi,
\qquad
A[f]=\int_{\mathbb R}a(t)|\widehat f(t)|^2\,dt,
\]
\[
M_\pm(f)=\int_{\mathbb R}e^{\pm x/2}f(x)\,dx,
\qquad
R[f]=2\operatorname{Re}\bigl(M_+(f)\overline{M_-(f)}\bigr).
\]
The completed quadratic form in these conventions is
\[
\boxed{
\mathcal Q[f]
=A[f]+R[f]
-2\sum_{\log q<L}\frac{\Lambda(q)}{\sqrt q}
  \operatorname{Re}\langle f,\tau_{\log q}f\rangle .
}
\tag{21.1}
\]
Here and below \(q\) ranges over prime powers. A term with \(\log q=L\) has zero overlap and can be included harmlessly.

Formula (21.1) is the ordinary explicit formula applied to the autocorrelation of \(f\). The semilocal form and its relationship to Weil positivity are described in [Connes–Consani, *Spectral Triples and Zeta-Cycles*, Sections 1–2](https://arxiv.org/pdf/2106.01715).

The pole term is essential. On a centered interval, let
\[
c(x)=\cosh(x/2),\qquad s(x)=\sinh(x/2).
\]
Then
\[
R[f]=2|\langle c,f\rangle|^2-2|\langle s,f\rangle|^2.
\tag{21.2}
\]
It has one positive and one negative direction. It is not a positive rank-two correction.

If both exponential moments vanish,
\[
M_+(f)=M_-(f)=0,
\tag{21.3}
\]
then \(R[f]=0\). We do not silently impose these conditions or use positivity on this constrained subspace as positivity on the full space. The results below keep the full pole term.

### 21.2 An explicit meaning for the completed multiplier

For tests of support diameter at most \(L\), the pole term can also be represented by the multiplier
\[
r_L(t)=4\int_0^L\cosh(u/2)\cos(tu)\,du
=4\frac{\frac12\sinh(L/2)\cos(tL)
 t\cosh(L/2)\sin(tL)}{t^2+\frac14}.
\tag{21.4}
\]
Indeed its physical-space kernel is \(2\cosh(u/2)\) for \(|u|\le L\), which gives (21.2) on the support of every relevant autocorrelation. Thus one valid completion in Section 2 is
\[
c_{\infty,L}(t)=a(t)+r_L(t).
\tag{21.5}
\]
The term \(r_L(t)\) is \(O_L((1+|t|)^{-1})\). Consequently the asserted logarithmic high-frequency growth is valid, but that growth alone does not specify the low-frequency form.

All occurrences of localized positivity in this continuation refer to (21.1), or equivalently to the completed multiplier (21.5).

## 22. Corrections to the earlier certificate logic

### 22.1 Boundary strips must be disjoint for the stated factor

The bound
\[
|\langle f,\tau_yf\rangle|
\le\frac12\|1_{\partial_\Delta I_L}f\|_2^2
\]
holds as written when \(0<\Delta\le L/2\) and \(L-\Delta<y<L\). If the two strips overlap, their two integrals must be counted separately. Every asymptotic choice of \(\Delta\) below satisfies the disjointness condition.

### 22.2 A form error is not automatically an \(L^2\) eigenvalue error

From
\[
|B[f]|\le \epsilon\,\mathcal E_{\log}[f]
\]
one cannot infer \(\|B\|_{L^2\to L^2}\le\epsilon\). The logarithmic energy is unbounded on the \(L^2\) unit sphere.

Accordingly, the scalar margin \(Ce^{-L/2}\) in Section 15 requires a specified energy normalization or a separate operator-norm bound. Sections 24 and 28 provide both appropriate replacements. Section 25 also shows why strict positive margins are not necessary in a cofinal proof.

### 22.3 Exact reproduction by a positive smoothing kernel is more severely obstructed

If \(K\ge0\) is an integrable probability density and
\[
\phi_K(\lambda)=\int_{\mathbb R}K(t)e^{-i\lambda t}\,dt,
\]
then \(\phi_K(\lambda)\ne1\) for every nonzero \(\lambda\).

**Proof.** Equality would imply
\[
\int_{\mathbb R}K(t)(1-\cos(\lambda t))\,dt=0.
\]
Thus \(K\) would be supported, up to null sets, on the countable set
\(\{2\pi k/\lambda:k\in\mathbb Z\}\), which is impossible for an integrable density of mass one. \(\square\)

For general probability measures, reproduction on a nontrivial interval of frequencies forces the measure to be \(\delta_0\). Therefore a positive ordinary smoothing kernel cannot reproduce the entire test bandwidth exactly even below \(L=\log2\). The arithmetic bandwidth incompatibility in Section 6 is an additional obstruction.

### 22.4 Restore the interval scale in the Hilbert–Schmidt identity

For the Fourier convention above and an interval of length \(L\),
\[
\|\mathcal C_L(S)\|_{\mathrm{HS}}^2
=\int_{\mathbb R}
\left|\frac{\sin(Lu/2)}{\pi u}\right|^2
|S\cap(S-u)|\,du
\tag{22.1}
\]
whenever the right side is finite. The normalized sinc in Section 8 omitted this scale dependence. The density obstruction itself remains valid.

The claimed quantitative Kronecker scale in Section 5 is not accompanied by a quantitative theorem in the supplied file. It should be read as a warning about that method, rather than as a proved universal lower bound on every possible transfer argument.

## 23. Exact archimedean difference energy and boundary potential

Set
\[
a_0=a(0)=-\gamma-\frac{\pi}{2}-3\log2-\log\pi,
\qquad
k(u)=\frac{e^{-u/2}}{1-e^{-2u}}\quad(u>0).
\tag{23.1}
\]

### Theorem 23.1 — Exact difference-energy identity

For every compactly supported \(f\) in the logarithmic form domain,
\[
\boxed{
A[f]-a_0\|f\|_2^2
=\int_0^\infty k(u)\|f-\tau_uf\|_2^2\,du.
}
\tag{23.2}
\]
In particular the right side is nonnegative.

**Proof.** The integral representation of the digamma function gives
\[
\operatorname{Re}\psi\!\left(\frac14+\frac{it}{2}\right)-\psi(1/4)
=2\int_0^\infty k(u)(1-\cos(tu))\,du.
\]
This follows by subtracting the value at \(t=0\) and substituting \(v=2u\) in the standard representation; see [NIST DLMF, §5.9(ii)](https://dlmf.nist.gov/5.9#E16).
Plancherel gives
\[
\|f-\tau_uf\|_2^2
=2\int_{\mathbb R}(1-\cos(tu))|\widehat f(t)|^2\,dt.
\]
Tonelli applies because these integrands are nonnegative. \(\square\)

Define
\[
D_A[f]=A[f]-a_0\|f\|_2^2,
\qquad
\mathcal D[f]=\|f\|_2^2+D_A[f].
\tag{23.3}
\]
The weight \(1+a(t)-a_0\) is positive and comparable to
\(1+\log(2+|t|)\). Thus \(\mathcal D\) is a fixed positive archimedean energy, independent of the enclosing support interval.

### Theorem 23.2 — Boundary decomposition

For \(f\) supported in \((0,L)\),
\[
\boxed{\begin{aligned}
D_A[f]
={}&\int_0^L k(u)\int_0^{L-u}|f(x+u)-f(x)|^2\,dx\,du\\
&+\int_0^L\bigl(K(x)+K(L-x)\bigr)|f(x)|^2\,dx,
\end{aligned}}
\tag{23.4}
\]
where
\[
\boxed{
K(x)=\int_x^\infty k(u)\,du
=\operatorname{artanh}(e^{-x/2})+\arctan(e^{-x/2}).
}
\tag{23.5}
\]
Moreover,
\[
K(x)=\frac12\log(4/x)+\frac{\pi}{4}+O(x)
\quad(x\downarrow0).
\tag{23.6}
\]

**Proof.** For \(0<u<L\), decompose the squared translation difference into its interior overlap and its two exterior pieces:
\[
\begin{aligned}
\|f-\tau_uf\|_2^2
={}&\int_0^{L-u}|f(x+u)-f(x)|^2\,dx\\
&+\int_0^u|f(x)|^2\,dx+\int_{L-u}^L|f(x)|^2\,dx.
\end{aligned}
\]
For \(u\ge L\), it equals \(2\|f\|_2^2\). Integrating these identities against \(k(u)\) proves (23.4).
For (23.5), put \(r=e^{-u/2}\):
\[
K(x)=2\int_0^{e^{-x/2}}\frac{dr}{1-r^4}
=\operatorname{artanh}(e^{-x/2})+\arctan(e^{-x/2}).
\]
The expansion follows directly. \(\square\)

### Corollary 23.3 — Direct boundary-mass inequality

For \(0<\Delta\le L/2\),
\[
\boxed{
\|1_{\partial_\Delta I_L}f\|_2^2
\le\frac{D_A[f]}{K(\Delta)}.
}
\tag{23.7}
\]
Indeed at least one of \(K(x),K(L-x)\) is at least \(K(\Delta)\) on the boundary strips.

Consequently the boundary prime form satisfies
\[
\boxed{
|\mathfrak P^{\mathrm{bd}}_{L,\Delta}[f]|
\le\frac{W_{L,\Delta}}{2K(\Delta)}\,D_A[f].
}
\tag{23.8}
\]
This retains the entire archimedean difference energy and gives an explicit coefficient. It is an estimate on the endpoint block only; the interior prime correlations remain signed and unchanged.

## 24. A larger removable layer and a genuine operator-norm bound

The same boundary-overlap calculation also gives the elementary but useful bound
\[
\boxed{
\|T^{\mathrm{bd}}_{L,\Delta}\|_{L^2\to L^2}
\le\frac12W_{L,\Delta},
\qquad 0<\Delta\le L/2.
}
\tag{24.1}
\]
This is because the two disjoint boundary strips have total \(L^2\) mass at most \(\|f\|_2^2\). The bounded operator is self-adjoint, so its norm is controlled by the absolute quadratic form.

Using only integer counting and \(\Lambda(q)\le L\), for \(0<\Delta\le1\),
\[
\begin{aligned}
\frac12W_{L,\Delta}
&\le L e^{-(L-\Delta)/2}
  \bigl(e^L(1-e^{-\Delta})+1\bigr)\\
&\le L e^{\Delta/2}
  \bigl(e^{L/2}\Delta+e^{-L/2}\bigr).
\end{aligned}
\tag{24.2}
\]

### Theorem 24.1 — Growing removable endpoint layer

For sufficiently large \(L\), choose
\[
\Delta_L=\frac{e^{-L/2}}{L^2}.
\tag{24.3}
\]
Then
\[
\boxed{
\|T^{\mathrm{bd}}_{L,\Delta_L}\|
\le e^{\Delta_L/2}
\left(\frac1L+Le^{-L/2}\right)
=O(L^{-1}).
}
\tag{24.4}
\]
The corresponding interval of integers has length
\[
e^L-e^{L-\Delta_L}
\sim\frac{e^{L/2}}{L^2}\longrightarrow\infty.
\tag{24.5}
\]
No short-interval prime number theorem is used; (24.5) describes the interval length, not a claimed count of primes in it.

The stronger energy-relative version is
\[
\boxed{
|\mathfrak P^{\mathrm{bd}}_{L,\Delta_L}[f]|
\le O(L^{-2})D_A[f],
}
\tag{24.6}
\]
because
\[
K(\Delta_L)=\frac L4+\log L+O(1).
\]

More generally any choice with
\[
L e^{L/2}\Delta_L\longrightarrow0
\]
gives a vanishing operator-norm budget by (24.2).

The original choice \(\Delta_L=e^{-L}\) remains valid and gives
\(\|T^{\mathrm{bd}}\|=O(Le^{-L/2})\). Its stronger normalized form estimate is \(O(e^{-L/2})D_A\). These are distinct norms and should be labeled separately.

## 25. The cofinal target can be weakened to a vanishing lower error

This is the main correction to the research target in Sections 14–15.

Let \(I_L=(-L/2,L/2)\), and use \(\mathcal Q_L\) to denote the restriction of the same form (21.1) to \(I_L\). Translation of a test function leaves both \(\mathcal Q\) and \(\mathcal D\) unchanged. In particular the opposite exponential factors in \(M_+\overline{M_-}\) cancel under translation.

### Theorem 25.1 — Cofinal approximate positivity

Suppose \(L_j\to\infty\), \(\epsilon_j\ge0\), and \(\epsilon_j\to0\). Either of the following hypotheses suffices for RH:
\[
\mathcal Q_{L_j}[f]\ge-\epsilon_j\|f\|_2^2
\quad\text{for every admissible }f\text{ supported in }I_{L_j},
\tag{25.1}
\]
or the weaker energy-relative hypothesis
\[
\boxed{
\mathcal Q_{L_j}[f]\ge-\epsilon_j\mathcal D[f]
\quad\text{for every such }f.
}
\tag{25.2}
\]

**Proof.** Fix one compactly supported smooth \(f\). For all sufficiently large \(j\), its support lies in \(I_{L_j}\). Its value \(\mathcal Q_{L_j}[f]=\mathcal Q[f]\) is then independent of \(j\): all extra prime shifts have zero overlap, and neither the archimedean form nor the pole term changes. Also \(\mathcal D[f]\) is fixed and finite. Passing to the limit in (25.2) gives \(\mathcal Q[f]\ge0\). Weil positivity for all such \(f\) implies RH. Since \(\mathcal D[f]\ge\|f\|_2^2\), (25.1) is a special case. \(\square\)

The proof takes the limit for each fixed test function. It does not convert a logarithmic form error into a uniform \(L^2\) eigenvalue error.

### Theorem 25.2 — Interior forms suffice by local consistency

Define the interior form with the *same archimedean and pole terms* by
\[
\mathcal Q^{\mathrm{int}}_{L,\Delta}[f]
=A[f]+R[f]
-2\sum_{\log q\le L-\Delta}
\frac{\Lambda(q)}{\sqrt q}
\operatorname{Re}\langle f,\tau_{\log q}f\rangle.
\tag{25.3}
\]
Suppose
\[
L_j\to\infty,\qquad L_j-\Delta_j\to\infty,\qquad\epsilon_j\to0,
\]
and
\[
\boxed{
\mathcal Q^{\mathrm{int}}_{L_j,\Delta_j}[f]
\ge-\epsilon_j\mathcal D[f]
\quad\text{for every }f\text{ supported in }I_{L_j}.
}
\tag{25.4}
\]
Then RH holds.

**Proof.** Fix \(f\) of support diameter \(d\). Once \(L_j-\Delta_j>d\), every omitted shift has zero overlap with this particular \(f\). Hence
\(\mathcal Q^{\mathrm{int}}_{L_j,\Delta_j}[f]=\mathcal Q[f]\).
Now repeat the proof of Theorem 25.1. \(\square\)

No smallness estimate on the omitted operator is required for this implication. The smallness estimates matter for transferring quantitative certificates between the two forms, and for proving the converse below.

### Corollary 25.3 — An exact RH equivalence for the enlarged layer

With \(\Delta_L=e^{-L/2}/L^2\), RH is equivalent to the existence of a cofinal sequence \(L_j\) and numbers \(\epsilon_j\downarrow0\) satisfying (25.4).

**Proof of the converse.** Under RH, \(\mathcal Q_L[f]\ge0\). Equations (23.8) and (24.6) give
\[
\mathcal Q^{\mathrm{int}}_{L,\Delta_L}[f]
\ge-O(L^{-2})D_A[f]\ge-O(L^{-2})\mathcal D[f].
\]
The coefficients can be replaced by a decreasing envelope along a subsequence. \(\square\)

Thus the sufficient target is not a positive margin larger than every error. It is the following:
\[
\boxed{
\text{A cofinal, correctly normalized lower certificate whose negative error tends to zero.}
}
\tag{25.5}
\]

For perspective, the full-window quantities
\[
\lambda(L)=\inf_{f\ne0}\frac{\mathcal Q_L[f]}{\|f\|_2^2},
\qquad
\mu(L)=\inf_{f\ne0}\frac{\mathcal Q_L[f]}{\mathcal D[f]}
\]
are nonincreasing with \(L\), by inclusion of test spaces. A cofinal lower bound tending to zero therefore forces every fixed-window value to be nonnegative.

This is a reduction in the required certificate precision and strength. It does not establish the lower bounds.

## 26. Carry out the exact \(L=\log5\) core calculation

### 26.1 The original endpoint layer is already empty as an operator

At \(L=\log5\),
\[
e^{-L}=\frac15<\log(5/4).
\]
Thus the layer \(L-e^{-L}<\log q\le L\) contains only \(q=5\), and that shift has zero overlap. Boundary stripping contributes no improvement to this particular endpoint certificate. The surviving prime powers are exactly \(2,3,4\).

This is an exact consequence of the proposed calculation, not a numerical approximation.

### 26.2 Exact shift matrices

On \((0,L)\), put
\[
e_n(x)=L^{-1/2}e^{2\pi i n x/L},\quad n\in\mathbb Z,
\qquad
\omega_n=2\pi n/L.
\]
Let \(S_y\) be the truncated right shift:
\[
(S_yf)(x)=1_{(y,L)}(x)f(x-y),\qquad 0<y<L.
\]
Its exact matrix is
\[
\boxed{
(S_y)_{mn}=
\begin{cases}
(1-y/L)e^{-i\omega_n y},&m=n,\\[2mm]
\displaystyle
\frac{e^{-i\omega_n y}-e^{-i\omega_m y}}
{2\pi i(n-m)},&m\ne n.
\end{cases}
}
\tag{26.1}
\]
This follows by integrating
\[
\frac{e^{-i\omega_n y}}{L}
\int_y^L e^{i(\omega_n-\omega_m)x}\,dx.
\]
Write \(H_y=S_y+S_y^*\). Since the off-diagonal matrix in (26.1) is complex symmetric,
\[
(H_y)_{mn}
=\frac{\sin(\omega_m y)-\sin(\omega_n y)}{\pi(n-m)}
\quad(m\ne n),
\tag{26.2}
\]
and
\[
(H_y)_{nn}=2(1-y/L)\cos(\omega_n y).
\tag{26.3}
\]

### 26.3 Include the full archimedean and pole matrices

The archimedean matrix has the convergent integral representation
\[
\boxed{
\mathbf A_{mn}
=(a_0+2K(L))\delta_{mn}
+\int_0^L k(u)\bigl(2\delta_{mn}-(H_u)_{mn}\bigr)\,du.
}
\tag{26.4}
\]
The cancellation inside the integrand must be retained near \(u=0\). Formula (26.4) follows from Theorem 23.1 and \(S_u=0\) for \(u\ge L\).

The moment coefficients are
\[
m_{\pm,n}
=M_\pm(e_n)
=\frac{e^{\pm L/2}-1}{\sqrt L(\pm\frac12+i\omega_n)}.
\tag{26.5}
\]
Consequently the pole matrix is
\[
\boxed{
\mathbf R_{mn}
=\overline{m_{+,m}}m_{-,n}
 +\overline{m_{-,m}}m_{+,n}.
}
\tag{26.6}
\]
This retains both signs in (21.2).

For \(L=\log5\), the exact Galerkin matrix is therefore
\[
\boxed{
\mathbf T_N
=\left[
\mathbf A+\mathbf R
-\frac{\log2}{\sqrt2}H_{\log2}
-\frac{\log3}{\sqrt3}H_{\log3}
-\frac{\log2}{2}H_{\log4}
\right]_{|m|,|n|\le N}.
}
\tag{26.7}
\]
All entries have now been specified, including the previously implicit completion. The displayed integral and finite formulas give exact entries; they are not an interval-certified lower bound for the infinite operator.

The three companion ZIP files mentioned in Section 17 were not included with this attachment. Their asserted certificates have not been independently checked in this continuation.

## 27. Rank-two displacement does not make the Fourier tail small

### 27.1 Exact algebraic structure

Let \(z_n=e^{-2\pi i n y/L}\), and let \(\mathbf N\) denote the diagonal matrix of Fourier indices on any finite index set. Equation (26.1) gives
\[
(\mathbf N S_y-S_y\mathbf N)_{mn}
=\frac{z_m-z_n}{2\pi i}.
\tag{27.1}
\]
Thus every finite displacement matrix has rank at most two.

This finite identity is not a bounded rank-two commutator on the full Fourier Hilbert space: the sequences \((1)_n\) and \((z_n)_n\) do not belong to \(\ell^2(\mathbb Z)\). Such a conclusion would require additional domain and boundedness estimates.

Let \(\Pi_N\) project onto \(|n|\le N\). Already for the one-sided shift,
\[
\boxed{
\|(I-\Pi_N)S_y\Pi_N\|
\ge |(S_y)_{N+1,N}|
=\frac{\sin(\pi y/L)}{\pi}>0
}
\tag{27.2}
\]
for every \(N\).

The symmetric sum \(H_y\) can have cancellations; for example \(y=L/2\) makes \(H_y\) diagonal in this basis. Therefore (27.2) alone is not a proof about the completed signed prime operator. The next calculation addresses the actual signed prime block.

### Theorem 27.1 — Nonvanishing signed prime coupling at \(\log5\)

Set
\[
\mathbf P_5=-\sum_{q\in\{2,3,4\}}w_qH_{\log q},
\quad
w_2=\frac{\log2}{\sqrt2},\quad
w_3=\frac{\log3}{\sqrt3},\quad
w_4=\frac{\log2}{2},
\]
and \(r_q=\log q/\log5\). Then
\[
\boxed{
\limsup_{N\to\infty}
\|(I-\Pi_N)\mathbf P_5\Pi_N\|
\ge
\left(
\frac{2}{\pi^2}\sum_{q\in\{2,3,4\}}
w_q^2\sin^2(\pi r_q)
\right)^{1/2}>0.
}
\tag{27.3}
\]
The exact right side is approximately \(0.329\); the positivity assertion relies on its displayed formula, not on this decimal.

**Proof.** The crossing entry is
\[
b_N=(\mathbf P_5)_{N+1,N}
=\frac2\pi\sum_{q\in\{2,3,4\}}
w_q\sin(\pi r_q)\cos\bigl(2\pi(N+\tfrac12)r_q\bigr).
\tag{27.4}
\]
For distinct \(q,r\in\{2,3,4\}\), none of
\[
2r_q,\qquad r_q-r_r,\qquad r_q+r_r
\]
is an integer. Otherwise respectively \(q^2\), \(q/r\), or \(qr\) would be an integral power of \(5\), which is impossible.
Finite geometric-series averaging therefore gives
\[
\lim_{M\to\infty}\frac1M\sum_{N=0}^{M-1}b_N^2
=\frac{2}{\pi^2}\sum_{q\in\{2,3,4\}}
w_q^2\sin^2(\pi r_q).
\]
The limsup of \(|b_N|\) is at least the square root of this mean square, and each crossing-block norm is at least \(|b_N|\). \(\square\)

**Scope of the obstruction.** This proves nondecay for the signed prime block in the unweighted Fourier decomposition. It does not rule out cancellation with other parts of the full form, a useful energy preconditioner, or a successful rational Krylov approximation. It does rule out deriving a small unweighted prime truncation error merely from increasing \(N\) or from the finite rank-two identity.

## 28. The correct normalized signed Schur certificate

### 28.1 A compact signed operator with a specified normalization

Let \(D_L\ge I\) be the self-adjoint operator associated to the closed form \(\mathcal D\) on the interval \(I_L\). Its inverse is compact.

One way to see compactness is to observe that bounded \(\mathcal D\)-energy gives uniformly small high-frequency \(L^2\) tails. Restriction of a bounded-frequency Fourier transform to a fixed finite interval is compact. Combining the two statements gives compact embedding of the form domain into \(L^2(I_L)\).

For fixed \(L\), write
\[
\mathcal Q_L[f]=\mathcal D[f]+\langle f,V_Lf\rangle,
\]
where
\[
V_L=(a_0-1)I+R_L-\sum_{\log q<L}w_qH_{\log q}
\]
is bounded and self-adjoint. Define
\[
\boxed{
\mathcal K_L=-D_L^{-1/2}V_LD_L^{-1/2}.
}
\tag{28.1}
\]
This operator is compact and self-adjoint, and
\[
\mathcal Q_L[f]
=\left\langle D_L^{1/2}f,\,
(I-\mathcal K_L)D_L^{1/2}f\right\rangle.
\tag{28.2}
\]
In particular,
\[
\mathcal Q_L[f]\ge-\epsilon\mathcal D[f]\ \forall f
\quad\Longleftrightarrow\quad
\sup\sigma(\mathcal K_L)\le1+\epsilon.
\tag{28.3}
\]
Because \(\mathcal K_L\) is signed, replacing its top spectral value by its absolute operator norm can impose a strictly stronger, unnecessary condition.

The notation \(\mathcal K_L\) here is defined by (28.1); it does not presume identification with an operator of the same name in another handoff.

### Theorem 28.1 — Exact residual formula for the signed Schur complement

Choose an orthogonal finite-dimensional core projection and decompose the bounded operator
\[
G_\epsilon=(1+\epsilon)I-\mathcal K_L
=
\begin{pmatrix}
\mathsf A&\mathsf B\\
\mathsf B^*&\mathsf C
\end{pmatrix}.
\tag{28.4}
\]
Assume a separately proved tail lower bound
\[
\mathsf C\ge\gamma I,\qquad\gamma>0.
\tag{28.5}
\]
For any trial map \(X\) from the core to the tail, define
\[
\mathsf E=\mathsf B^*-\mathsf C X,
\]
\[
\mathsf F_X
=\mathsf A-\mathsf B X-X^*\mathsf B^*+X^*\mathsf C X.
\tag{28.6}
\]
Then the complete Schur complement satisfies
\[
\boxed{
\mathsf F
=\mathsf A-\mathsf B\mathsf C^{-1}\mathsf B^*
=\mathsf F_X-\mathsf E^*\mathsf C^{-1}\mathsf E.
}
\tag{28.7}
\]
Consequently
\[
\boxed{
\mathsf F_X-\gamma^{-1}\mathsf E^*\mathsf E
\preceq\mathsf F\preceq\mathsf F_X.
}
\tag{28.8}
\]

**Proof.** Expand
\[
\mathsf E^*\mathsf C^{-1}\mathsf E
=\mathsf B\mathsf C^{-1}\mathsf B^*
-\mathsf B X-X^*\mathsf B^*+X^*\mathsf C X.
\]
This proves (28.7). Equation (28.5) gives
\(0\preceq\mathsf C^{-1}\preceq\gamma^{-1}I\), proving (28.8). \(\square\)

Thus the finite verified inequality
\[
\boxed{
\mathsf F_X-\gamma^{-1}\mathsf E^*\mathsf E\succeq0
}
\tag{28.9}
\]
together with (28.5) proves \(\mathcal Q_L\ge-\epsilon\mathcal D\).
A rational Krylov space can be used to construct \(X\); it does not remove the obligation to bound the actual residual \(\mathsf E\).

This formula retains the signed arithmetic matrix, the pole correction, and every mixed term. The final positive residual square is subtracted with its correct sign.

For an \(L^2\)-normalized bound \(\mathcal Q_L\ge-\epsilon\|f\|_2^2\), replace \(G_\epsilon\) in (28.4) by
\[
I-\mathcal K_L+\epsilon D_L^{-1}.
\tag{28.10}
\]
Adding \(\epsilon I\) after this normalization gives an energy-relative bound, not an \(L^2\) bound.

For each fixed \(L\), compactness eventually supplies a positive tail in a sufficiently large core. This qualitative fact has no uniform cofinal rate. The remaining difficulty is to establish (28.5) and (28.9) with \(\epsilon=\epsilon_j\to0\) along unbounded \(L_j\).

## 29. A nested finite-matrix route, with exact arithmetic entries

For an RH proof, one may prove a uniform statement about a nested dense family of finite test spaces, rather than certify the entire infinite-dimensional operator separately at every endpoint.

### 29.1 Explicit spaces and exact refinement

Put \(d_0=\log2\), and for \(j\ge1\) set
\[
I_j=[-jd_0,jd_0],\qquad h_j=d_0\,2^{-j}.
\]
Let \(V_j\) consist of continuous piecewise-linear functions on the mesh \(h_j\mathbb Z\) in \(I_j\), vanishing at both endpoints and extended by zero. Then
\[
V_j\subset V_{j+1},\qquad \dim V_j=2j\,2^j-1.
\tag{29.1}
\]
The support diameter is the arithmetic endpoint
\[
L_j=2j\log2=\log(4^j).
\]
Use the hat functions
\[
\phi_h(x)=(1-|x|/h)_+,\qquad
\phi_{j,k}(x)=\phi_{h_j}(x-kh_j),\quad |k|<j2^j.
\tag{29.2}
\]
Every coarse hat satisfies the exact refinement identity
\[
\phi_{j,k}
=\tfrac12\phi_{j+1,2k-1}
+\phi_{j+1,2k}
+\tfrac12\phi_{j+1,2k+1}.
\tag{29.3}
\]
Let \(J_j\) denote this coefficient injection. Define the full signed form and mass matrices by
\[
(\mathsf W_j)_{kl}=\mathcal Q(\phi_{j,k},\phi_{j,l}),
\qquad
(\mathsf M_j)_{kl}=\langle\phi_{j,k},\phi_{j,l}\rangle,
\]
where \(\mathcal Q(\cdot,\cdot)\) is the Hermitian polarization of (21.1). Then
\[
\boxed{
J_j^*\mathsf W_{j+1}J_j=\mathsf W_j,\qquad
J_j^*\mathsf M_{j+1}J_j=\mathsf M_j.
}
\tag{29.4}
\]
The new prime shifts have zero overlap on each coarse test when they exceed its support diameter. These identities hold for the full arithmetic form.

### Theorem 29.1 — A concrete finite-matrix RH equivalence

The following statements are equivalent:

1. RH.
2. \(\mathsf W_j\succeq0\) for every \(j\).
3. For all sufficiently large \(j\),
   \[
   \boxed{\mathsf W_j+\frac1j\mathsf M_j\succeq0.}
   \tag{29.5}
   \]

In statement 3, any prescribed positive sequence tending to zero can replace \(1/j\). It is also enough to prove the inequalities on a cofinal subsequence.

**Proof.** RH implies positivity on smooth compact tests and, by approximation on each fixed interval, on these compactly supported \(H^1\) functions. Thus 1 implies 2, which implies 3.

Conversely fix \(v\in V_k\). Nesting gives \(v\in V_j\) for all \(j\ge k\), so statement 3 gives
\[
\mathcal Q[v]\ge-\frac1j\|v\|_2^2.
\]
Letting \(j\to\infty\) proves \(\mathcal Q[v]\ge0\).

For any \(f\in C_c^\infty(\mathbb R)\), sufficiently fine linear interpolants belong to \(V_j\), stay in one fixed compact interval, and converge in \(H^1\). On that fixed interval, the archimedean form is continuous in \(H^1\), only finitely many prime shifts occur, and the pole functionals are bounded. Their form values therefore converge to \(\mathcal Q[f]\), proving global Weil positivity. \(\square\)

At one fixed \(j\), positivity of \(\mathsf W_j\) is only a Galerkin statement. The theorem requires a proved assertion on an unbounded nested family; it does not turn finitely many computations into a proof of RH.

### 29.2 Closed expressions for every matrix entry

Let
\[
g_h(u)=\int_{\mathbb R}\phi_h(x)\phi_h(x-u)\,dx=hB(u/h),
\]
where
\[
B(v)=
\begin{cases}
\frac23-v^2+\frac12|v|^3,&|v|\le1,\\
\frac16(2-|v|)^3,&1\le|v|\le2,\\
0,&|v|\ge2.
\end{cases}
\tag{29.6}
\]
In particular \(g_h(0)=2h/3\) and \(g_h(h)=h/6\). Also put
\[
m_h=\int_{\mathbb R}e^{x/2}\phi_h(x)\,dx
=\frac{8(\cosh(h/2)-1)}h.
\tag{29.7}
\]
For \(x=(k-l)h_j\), the exact Toeplitz entry is
\[
\boxed{\begin{aligned}
(\mathsf W_j)_{kl}
={}&a_0g_{h_j}(x)
+\int_0^\infty k(u)
\bigl(2g_{h_j}(x)-g_{h_j}(x-u)-g_{h_j}(x+u)\bigr)\,du\\
&+2m_{h_j}^2\cosh(x/2)\\
&-\sum_{\log q<L_j}\frac{\Lambda(q)}{\sqrt q}
\bigl(g_{h_j}(x-\log q)+g_{h_j}(x+\log q)\bigr).
\end{aligned}}
\tag{29.8}
\]
The mass entry is \(g_{h_j}(x)\). The integral converges: its symmetric second difference is \(O(u^2)\) near zero, whereas \(k(u)=O(u^{-1})\). Formula (29.8) follows by polarizing (23.2), translating the hats, and using their exponential moments. It requires no zeros of zeta.

### Theorem 29.2 — Exact cancellation and the arithmetic residual

For \(x>2h\), define the smoothed prime discrepancy
\[
\boxed{
\mathcal E_h(x)
=\sum_q\frac{\Lambda(q)}{\sqrt q}\,g_h(x-\log q)
-m_h^2e^{x/2}.
}
\tag{29.9}
\]
Only prime powers with \(|\log q-x|<2h\) occur. Define the explicit positive correction
\[
\mathcal J_h(x)
=\int_0^\infty
\frac{e^{-5u/2}}{1-e^{-2u}}\,g_h(x-u)\,du.
\tag{29.10}
\]
Then the full completed off-diagonal kernel in (29.8) is exactly
\[
\boxed{
\mathcal W_h(x)=-\mathcal E_h(x)-\mathcal J_h(x),
\qquad x>2h.
}
\tag{29.11}
\]
For entries of \(\mathsf W_j\), all prime powers appearing in (29.9) already satisfy the support cutoff.

**Proof.** For \(x>2h\), \(g_h(x)=g_h(x+u)=0\) for \(u\ge0\). Fubini gives
\[
\int_{\mathbb R}e^{v/2}g_h(v)\,dv=m_h^2.
\tag{29.12}
\]
Since \(g_h(x-u)\) is supported in \([x-2h,x+2h]\subset(0,\infty)\),
\[
\int_0^\infty e^{u/2}g_h(x-u)\,du=m_h^2e^{x/2},
\qquad
\int_0^\infty e^{-u/2}g_h(x-u)\,du=m_h^2e^{-x/2}.
\]
Finally,
\[
k(u)=e^{-u/2}+\frac{e^{-5u/2}}{1-e^{-2u}}.
\]
The growing half of the pole term cancels the smooth prime-density contribution in (29.9). Its decaying half cancels the first term of the archimedean kernel. What remains is (29.11). \(\square\)

In particular,
\[
0\le\mathcal J_h(x)
\le\frac{h^2e^{-5(x-2h)/2}}{1-e^{-2(x-2h)}},
\qquad x>2h,
\tag{29.13}
\]
because \(\int_{\mathbb R}g_h=h^2\).

This is an exact recentering. No absolute values were placed on the arithmetic discrepancy, and the archimedean remainder retains its sign.

## 30. The remaining arithmetic obstruction is now explicit

### 30.1 What a necessary two-point estimate would say

All diagonal entries at a fixed mesh equal \(\mathcal W_h(0)\). Positivity of a two-by-two principal minor requires, for separated hats,
\[
\boxed{
|\mathcal E_h(x)+\mathcal J_h(x)|\le\mathcal W_h(0).
}
\tag{30.1}
\]
For the relaxed target (29.5), the necessary condition is
\[
|\mathcal E_{h_j}(x)+\mathcal J_{h_j}(x)|
\le\mathcal W_{h_j}(0)+\frac{2h_j}{3j}
\tag{30.2}
\]
at represented separations \(x>2h_j\).

These conditions are necessary, not sufficient. Control of every two-by-two minor would still leave the coupled higher-dimensional signed energy unresolved.

The discrepancy in (29.9) is actual local prime-power data centered against its smooth density. Bohr means and long-interval distributional laws do not estimate it at the required growing separations and shrinking mesh widths.

### 30.2 Why the proved estimates do not close the problem

The endpoint estimates control a vanishing endpoint operator. Theorem 27.1 concerns the surviving interior prime block.

A crude full-form lower bound on a centered interval is
\[
\mathcal Q_L[f]\ge D_A[f]
-\left(
|a_0|+
2\sum_{\log q<L}\frac{\Lambda(q)}{\sqrt q}
+2\sinh(L/2)-L
\right)\|f\|_2^2.
\tag{30.3}
\]
Here absolute values were used only to display the weakness of this fallback estimate; it is not substituted for the signed operator in the proposed proof. The pole bound follows from
\[
2\|\sinh(x/2)\|_{L^2(-L/2,L/2)}^2=2\sinh(L/2)-L.
\]
The coefficient in (30.3) grows on the scale \(e^{L/2}\), rather than tending to zero. It supplies no cofinal approximate positivity.

Equation (29.11) removes this large smooth contribution from the *formula*. It does not by itself bound the remaining matrix of prime discrepancies.

### 30.3 The next sharply stated proof target

The concrete target emerging from this continuation is
\[
\boxed{
\mathsf W_j+\frac1j\mathsf M_j\succeq0
\quad\text{for every sufficiently large }j,
}
\tag{30.4}
\]
with entries specified by (29.6)–(29.8) and separated entries recentered by (29.9)–(29.11).

A natural attempt is to use \(J_j\), choose a mass-orthogonal complement to the inherited subspace in \(V_{j+1}\), and estimate the full signed Schur complement of that extension. The residual identity (28.7) applies after orthonormalization and a proved positive lower bound for the eliminated block.

There is a real caution in this induction: knowing
\(\mathsf W_j+j^{-1}\mathsf M_j\succeq0\) does not imply that the inherited block is positive after replacing \(j^{-1}\) by the smaller \((j+1)^{-1}\). A valid proof must control this loss and the new signed coupling. It cannot assume the preceding certificate remains valid at the next tolerance.

For a certificate on all tests at one fixed support, use (28.5) and (28.9). For RH through an analytic theorem for an unbounded family, (30.4) is a direct finite-matrix formulation without a separate infinite-tail certificate at each scale. Neither route has its decisive uniform inequality established here.

## 31. Current status and verification record

| Result | Status |
|---|---|
| Full pole completion and exact multiplier | Specified in (21.1)–(21.5) |
| Archimedean difference energy and boundary potential | Proved, Theorems 23.1–23.2 |
| Enlarged layer of integer length \(\sim e^{L/2}/L^2\) | Proved, with \(O(L^{-1})\) operator error and \(O(L^{-2})\) energy-relative error |
| Cofinal approximate positivity implies RH | Proved, Theorems 25.1–25.2 |
| Exact complete Fourier core at \(L=\log5\) | Given by (26.7) |
| A new interval certificate at \(L=\log5\) | Not obtained |
| Nondecay of the signed prime core-to-tail block at \(\log5\) | Proved, Theorem 27.1 |
| Complete signed Schur residual formula | Proved, Theorem 28.1 |
| Explicit nested finite-matrix RH equivalence | Proved, Theorem 29.1 |
| Exact smoothed prime-error formula for separated entries | Proved, Theorem 29.2 |
| Cofinal lower bound (25.4), (28.3), or (30.4) | Open; RH-strength |
| RH | Not proved |

The proofs in this continuation are analytic. No Lean verification was used or claimed. Independent elementary quadrature checks of the digamma difference formula, the boundary primitive, the pole multiplier, selected shift entries, the spline residual cancellation, and the refinement identity agreed with the derived formulas to numerical precision. These are sanity checks, not positivity certificates.

Primary references used to fix conventions and standard identities:

- [Connes–Consani, *Spectral Triples and Zeta-Cycles*](https://arxiv.org/pdf/2106.01715): the semilocal Weil form and global positivity criterion.
- [NIST DLMF, §5.9](https://dlmf.nist.gov/5.9#E16) and [§5.4](https://dlmf.nist.gov/5.4): the digamma integral representation and special values.
- [Connes–van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://alainconnes.org/wp-content/uploads/quadraticforms-1.pdf): context for structured finite truncations. Its zero-localization results do not provide the cofinal sign estimate needed here.

**Handoff instruction:** Continue from the exact discrepancy matrices in (29.8)–(29.11), or the normalized residual certificate (28.7). Preserve the pole signs and mixed terms. Seek a proved vanishing lower error on an unbounded family; positive margins are not required merely because the earlier handoff requested them. Do not count an enlarged removable endpoint layer, a finite displacement-rank identity, or a fixed collection of positive matrices as the missing arithmetic theorem.

---

# Part IV. Sparse positivity, collective cancellation, and a finite-bound RH criterion

## 32. Main results of the second continuation

Continue with the exact completed form \(\mathcal Q\), archimedean energy \(\mathcal D\), and spline matrices \(\mathsf W_j,\mathsf M_j\) defined above. No pole term or prime-power sign is changed.

The new unconditional estimate is
\[
\boxed{
\mathsf W_j=\ell_j\mathsf M_j+\mathsf Z_j,\qquad
\ell_j=\log(1/h_j),\qquad
\max_{k,l}|(\mathsf Z_j)_{kl}|\le C h_j,
}
\tag{32.1}
\]
with one constant \(C\) for all sufficiently large \(j\). This yields positivity for every coefficient vector involving at most a sufficiently small constant multiple of \(j\) hat functions, wherever those hats are located.

The entry estimate does not control the full operator: exact refinement forces collective directions in \(\mathsf Z_j\) with mass-normalized Rayleigh quotients equal to \(-\ell_j+O(1)\).

A separate analytic argument then strengthens the previous RH reduction:
\[
\boxed{
\exists C<\infty\ \forall f\in C_c^\infty(\mathbb R):
\quad\mathcal Q[f]\ge-C\mathcal D[f]
\quad\Longleftrightarrow\quad \mathrm{RH}.
}
\tag{32.2}
\]
The constant must be independent of support. An \(L^2\)-relative finite lower bound is also equivalent to RH.

The proof of (32.2) uses a single fixed hat width, the exact Laplace transform of its smoothed prime discrepancy, and a proved nonnegative-Laplace-transform lemma. It does not assume positivity of an unknown Schur complement.

## 33. Prove the uniform entry estimate

Recall
\[
h_j=(\log2)2^{-j},\qquad L_j=2j\log2,\qquad
h_je^{L_j/2}=\log2.
\tag{33.1}
\]
All constants below are independent of \(j\). We restrict to sufficiently large \(j\), so \(2h_j<\log2\).

### Lemma 33.1 — Archimedean scaling with a uniform remainder

For every real displacement \(x\), the archimedean hat kernel satisfies
\[
\boxed{
\left|A(\phi_h,\tau_x\phi_h)
-\log(1/h)\,g_h(x)\right|\le C_A h,
\qquad 0<h\le h_0.
}
\tag{33.2}
\]

**Proof.** Let \(\Phi=\phi_1\). Fourier scaling gives
\[
\widehat{\phi_h}(t)=h\widehat\Phi(ht).
\]
Thus the difference in (33.2) is
\[
h\int_{\mathbb R}
\bigl(a(s/h)-\log(1/h)\bigr)
|\widehat\Phi(s)|^2 e^{-isx/h}\,ds.
\]
The standard digamma asymptotic, together with continuity on bounded real intervals, gives
\[
a(t)=\log(2+|t|)+O(1)
\quad(t\in\mathbb R).
\]
See [NIST DLMF, §5.11](https://dlmf.nist.gov/5.11) for the digamma asymptotic.
Consequently
\[
a(s/h)-\log(1/h)=\log(2h+|s|)+O(1).
\]
Also
\[
|\widehat\Phi(s)|^2
=\frac1{2\pi}\left(\frac{\sin(s/2)}{s/2}\right)^4
\le C\min(1,|s|^{-4}).
\]
The absolute value of the integrand has an integrable majorant independent of \(h\): a constant times \(1+|\log|s||\) near zero and a constant times \((1+\log|s|)|s|^{-4}\) at infinity. This proves (33.2), uniformly in \(x\). \(\square\)

### Lemma 33.2 — Uniform local prime-power mass at the chosen scale

For \(h=h_j\) and \(0\le x\le L_j\), put
\[
B_h(x)=
\sum_{|\log q-x|<2h}\frac{\Lambda(q)}{\sqrt q}.
\]
Then
\[
\boxed{\sup_{0\le x\le L_j}B_{h_j}(x)\le C_P.}
\tag{33.3}
\]

**Proof.** Write \(\ell=\log(1/h)\). If the sum is nonempty, \(x\ge\log2-2h\). First suppose \(x\le3\ell/2\). Integer counting gives
\[
B_h(x)\le C(x+1)\bigl(e^{-x/2}+h e^{x/2}\bigr).
\tag{33.4}
\]
The first term is uniformly bounded. The second is bounded by
\(C(\ell+1)e^{-\ell/4}\), so is uniformly bounded as well.

Now suppose \(x>3\ell/2\). Set
\[
X=e^{x-2h},\qquad Y=e^{x+2h}-e^{x-2h}\asymp h e^x.
\]
For large \(j\), \(X,Y\ge2\), and
\[
\log Y=x-\ell+O(1)\ge c x.
\]
The short-interval upper sieve estimate
\[
\pi(X+Y)-\pi(X)\ll\frac{Y}{\log Y}
\tag{33.5}
\]
therefore gives
\[
\sum_{\substack{p\ \mathrm{prime}\\|\log p-x|<2h}}
\frac{\log p}{\sqrt p}
\ll x e^{-x/2}\frac{Y}{\log Y}
\ll h e^{x/2}\le\log2.
\tag{33.6}
\]
Estimate (33.5) follows from the Selberg upper sieve, uniformly in \(X,Y\); see the first application in Section 3, equation (3.3), of [Heath-Brown, *Lectures on sieves*](https://arxiv.org/pdf/math/0209360). Only its order of magnitude is used here.

It remains to retain the higher prime powers. For each exponent \(m\ge2\), the number of possible integer bases is at most
\[
C(h/m)e^{x/m}+1.
\]
There are \(O(x)\) possible exponents. Overcounting all integer bases gives a total of at most
\[
C h x e^{x/2}+C x.
\]
Since each weight is at most \(C x e^{-x/2}\), their contribution is at most
\[
C\bigl(hx^2+x^2e^{-x/2}\bigr).
\tag{33.7}
\]
Here \(3\ell/2<x\le L_j=2\ell+O(1)\), so (33.7) is bounded, and in fact tends to zero uniformly in this range. Combining the two ranges proves (33.3). \(\square\)

This lemma is an upper bound for a positive local prime-power mass. It makes no signed cancellation claim.

### Theorem 33.3 — Uniform entry remainder

For all sufficiently large \(j\), (32.1) holds.

**Proof.** Lemma 33.1 bounds the archimedean remainder by \(C_Ah_j\). The pole entry satisfies
\[
2m_{h_j}^2\cosh(x/2)\le C h_j^2 e^{|x|/2}\le C h_j
\quad(|x|\le L_j),
\tag{33.8}
\]
because \(m_h=O(h)\) and (33.1) holds.

For \(x\ge0\), the term \(g_h(x+\log q)\) vanishes when \(2h<\log2\). Since \(0\le g_h\le2h/3\), Lemma 33.2 bounds the remaining prime entry by
\[
\sum_q\frac{\Lambda(q)}{\sqrt q}g_h(x-\log q)
\le\frac{2h}{3}B_h(x)\le C h.
\]
The kernel is even, so the same estimate applies to negative \(x\). Combining the exact signed entries in (29.8) proves (32.1). \(\square\)

The estimates in this section control entries. They do not replace the full signed remainder by an absolute-value operator in the RH target.

## 34. Unconditional positivity for sparse tests

The mass matrix is tridiagonal:
\[
(\mathsf M_j)_{kk}=\frac{2h_j}{3},\qquad
(\mathsf M_j)_{k,k\pm1}=\frac{h_j}{6}.
\]
Therefore
\[
\boxed{
\frac{h_j}{3}\|c\|_2^2
\le c^*\mathsf M_jc\le h_j\|c\|_2^2.
}
\tag{34.1}
\]
For \(c\ne0\), define its effective coefficient count
\[
s_{\mathrm{eff}}(c)=\frac{\|c\|_1^2}{\|c\|_2^2}.
\tag{34.2}
\]
It is at most the number of nonzero coefficients.

### Theorem 34.1 — Sparse coercivity

There is an absolute constant \(C_*\) such that, for all sufficiently large \(j\) and all
\(f=\sum_kc_k\phi_{j,k}\),
\[
\boxed{
\mathcal Q[f]\ge
\bigl(\ell_j-C_*s_{\mathrm{eff}}(c)\bigr)\|f\|_2^2.
}
\tag{34.3}
\]

**Proof.** By (32.1),
\[
|c^*\mathsf Z_jc|
\le C h_j\|c\|_1^2
=C h_j s_{\mathrm{eff}}(c)\|c\|_2^2
\le3C s_{\mathrm{eff}}(c)c^*\mathsf M_jc.
\]
Now use \(\mathsf W_j=\ell_j\mathsf M_j+\mathsf Z_j\). \(\square\)

In particular, whenever a vector uses at most
\[
m\le\frac{\ell_j}{2C_*}
\]
hat functions,
\[
\boxed{\mathcal Q[f]\ge\frac{\ell_j}{2}\|f\|_2^2.}
\tag{34.4}
\]
The locations of those hats are arbitrary.

Consequences:

- Every fixed-size principal submatrix of \(\mathsf W_j\) is positive definite for all sufficiently large \(j\), uniformly over its location.
- More strongly, this holds for orders up to a sufficiently small constant multiple of \(j\), because \(\ell_j=j\log2-\log\log2\).
- Any coefficient vector with \(\mathcal Q[f]<0\) must satisfy
  \[
  s_{\mathrm{eff}}(c)>\ell_j/C_*.
  \tag{34.5}
  \]

Thus positivity of two-point tests on this shrinking mesh is an unconditional fact at sufficiently large scales. Those tests do not resolve the cofinal matrix inequality.

This is a lower bound on a restricted class of actual legal test functions. It is not a lower bound for unrestricted combinations.

## 35. An unavoidable collective cancellation

It would be incorrect to infer from \(|(\mathsf Z_j)_{kl}|\le Ch_j\) that the mass-normalized remainder is uniformly bounded.

### Theorem 35.1 — The normalized remainder has a negative direction of size \(\ell_j\)

Fix any nonzero \(v\in V_k\). For every \(j\ge k\), let \(c^{(j)}\) be its exact refined coefficient vector in \(V_j\). Then
\[
\boxed{
\frac{(c^{(j)})^*\mathsf Z_jc^{(j)}}
{(c^{(j)})^*\mathsf M_jc^{(j)}}
=-\ell_j+\frac{\mathcal Q[v]}{\|v\|_2^2}.
}
\tag{35.1}
\]
Consequently
\[
\lambda_{\min}
\bigl(\mathsf M_j^{-1/2}\mathsf Z_j\mathsf M_j^{-1/2}\bigr)
\le-\ell_j+O_v(1).
\tag{35.2}
\]

**Proof.** Exact refinement preserves the function \(v\), its norm, and its completed form value. Substitute \(\mathsf Z_j=\mathsf W_j-\ell_j\mathsf M_j\). \(\square\)

This obstruction is unconditional. The collective negative contribution in \(\mathsf Z_j\) is needed to cancel the artificial positive scale \(\ell_j\mathsf M_j\) introduced by fine-mesh normalization.

If
\[
\mathsf K_j^{\mathrm{mesh}}
=-\ell_j^{-1}\mathsf M_j^{-1/2}\mathsf Z_j\mathsf M_j^{-1/2},
\]
then
\[
\liminf_{j\to\infty}\sup\sigma(\mathsf K_j^{\mathrm{mesh}})\ge1.
\tag{35.3}
\]
A uniform spectral gap strictly below \(1\) for this mesh-normalized operator is therefore impossible. This operator is distinct from the archimedean-normalized \(\mathcal K_L\) in (28.1).

The sparse estimates and this obstruction fit together: small collections of fine hats have large positive archimedean cost, while a fixed coarse function uses more and more fine coefficients whose signed interactions cancel that cost.

## 36. Freeze one width and compute the exact Laplace transform

The order of the two limits matters. Now fix
\[
h_*=\frac{\log2}{4}
\]
once and for all, and allow the displacement \(x\) to tend to infinity. In this section write \(h=h_*\). The same argument works for any fixed \(0<h<(\log2)/2\).

Retain the actual discrepancy
\[
\mathcal E_h(x)
=\sum_q\frac{\Lambda(q)}{\sqrt q}g_h(x-\log q)
-m_h^2e^{x/2},\qquad x\ge0.
\tag{36.1}
\]
This is a continuous real function. Elementary integer counting gives
\[
|\mathcal E_h(x)|\le C_h(1+x)e^{x/2}.
\tag{36.2}
\]

Define the entire function
\[
G_h(s)=\int_{\mathbb R}g_h(u)e^{-su}\,du.
\]
The exact hat transform gives
\[
\int_{\mathbb R}\phi_h(u)e^{-su}\,du
=h\left(\frac{\sinh(hs/2)}{hs/2}\right)^2,
\]
and therefore
\[
\boxed{
G_h(s)=h^2\left(\frac{\sinh(hs/2)}{hs/2}\right)^4,
\qquad G_h(1/2)=m_h^2.
}
\tag{36.3}
\]
The singularity suggested by the quotient at \(s=0\) is removable. Every zero of \(G_h\) lies on the imaginary axis:
\[
s=\frac{2\pi i n}{h},\qquad n\in\mathbb Z\setminus\{0\}.
\tag{36.4}
\]
In particular,
\[
G_h(s)\ne0\quad\text{when }\operatorname{Re}s>0.
\tag{36.5}
\]

### Theorem 36.1 — Exact transformed discrepancy

For \(\operatorname{Re}s>1/2\),
\[
\boxed{
\int_0^\infty e^{-sx}\mathcal E_h(x)\,dx
=-G_h(s)\frac{\zeta'}{\zeta}\left(s+\frac12\right)
-\frac{G_h(1/2)}{s-\frac12}.
}
\tag{36.6}
\]

**Proof.** Because \(2h<\log2\), every translate \(g_h(x-\log q)\) is supported entirely in \(x>0\). Thus
\[
\int_0^\infty e^{-sx}g_h(x-\log q)\,dx=q^{-s}G_h(s).
\]
Absolute convergence permits summation for \(\operatorname{Re}s>1/2\). The logarithmic derivative of the absolutely convergent Euler product gives
\[
\sum_q\frac{\Lambda(q)}{q^{s+1/2}}
=-\frac{\zeta'}{\zeta}(s+1/2).
\]
The transform of \(m_h^2e^{x/2}\) is \(m_h^2/(s-1/2)\). These identities prove (36.6). The Euler product and the pole at \(1\) are recorded in [NIST DLMF, §25.2](https://dlmf.nist.gov/25.2). \(\square\)

The apparent pole at \(s=1/2\) on the right of (36.6) cancels exactly:
\[
-G_h(s)\frac{\zeta'}{\zeta}(s+1/2)
-\frac{G_h(1/2)}{s-1/2}
=\frac{G_h(s)-G_h(1/2)}{s-1/2}+O(1).
\tag{36.7}
\]
If \(\rho\) is a zero of multiplicity \(m_\rho\) with \(\operatorname{Re}\rho>1/2\), there is instead a genuine pole at \(s_\rho=\rho-1/2\), with residue
\[
-m_\rho G_h(s_\rho)\ne0.
\tag{36.8}
\]
Thus this fixed smoothing kernel cannot hide an off-critical zero through a zero of its transform.

The right side of (36.6), after the cancellation at \(1/2\), is analytic in a neighborhood of every positive real \(s\). Indeed \(\zeta(\sigma)\ne0\) for real \(\sigma>0\), apart from its pole at \(1\): for \(0<\sigma<1\), the alternating-series representation has positive numerator and negative denominator. See [DLMF (25.2.3)](https://dlmf.nist.gov/25.2#E3).

## 37. A one-sided bound already detects every off-critical zero

### Lemma 37.1 — Nonnegative Laplace transforms have a real boundary singularity

Let \(F(x)\ge0\) be locally integrable on \([0,\infty)\), with finite real abscissa of convergence \(\sigma_c\). Its Laplace transform cannot extend analytically to a neighborhood of the real point \(\sigma_c\).

**Proof.** Suppose such an extension existed. Choose \(s_1>\sigma_c\) close enough that the Taylor series of the transform about \(s_1\) converges at a real point \(s_1-r<\sigma_c\). For \(n\ge0\),
\[
(-1)^n\mathscr L_F^{(n)}(s_1)
=\int_0^\infty x^nF(x)e^{-s_1x}\,dx\ge0.
\]
The convergent Taylor series evaluated to the left is therefore a sum of nonnegative terms. Tonelli yields
\[
\sum_{n=0}^\infty\frac{r^n}{n!}
\int_0^\infty x^nF(x)e^{-s_1x}\,dx
=\int_0^\infty F(x)e^{-(s_1-r)x}\,dx<\infty,
\]
contradicting the definition of \(\sigma_c\). \(\square\)

This is the classical Landau mechanism, with its proof included to make the argument self-contained.

### Theorem 37.2 — One-sided growth bounds give a zero-free half-plane

Fix \(a\ge0\). If either
\[
\mathcal E_h(x)\le C e^{ax}\quad(x\ge0)
\tag{37.1}
\]
or
\[
\mathcal E_h(x)\ge-C e^{ax}\quad(x\ge0)
\tag{37.2}
\]
holds with a finite constant, then
\[
\boxed{\zeta(\rho)=0\ \Longrightarrow\
\operatorname{Re}\rho\le\frac12+a}
\tag{37.3}
\]
for nontrivial zeros in the right half of the critical strip.

**Proof.** If (37.1) holds, let
\[
F(x)=C e^{ax}-\mathcal E_h(x)\ge0.
\]
In the initial half-plane of convergence its Laplace transform is
\[
\frac C{s-a}
+G_h(s)\frac{\zeta'}{\zeta}(s+1/2)
+\frac{G_h(1/2)}{s-1/2}.
\tag{37.4}
\]
Suppose there were a zero with \(\delta=\operatorname{Re}\rho-1/2>a\). Its nonzero residue in (36.8) forces the abscissa \(\sigma_c\) of this nonnegative transform to satisfy \(\sigma_c\ge\delta\); otherwise the integral would define a holomorphic function at that pole. By (36.2), the abscissa is finite.

At the positive real point \(\sigma_c>a\), however, the meromorphic expression (37.4) is analytic. The pole at \(1/2\) cancels, there is no positive real zeta zero, and the added pole at \(a\) is strictly to the left. This contradicts Lemma 37.1.

For (37.2), use \(F(x)=C e^{ax}+\mathcal E_h(x)\); the same proof applies with the opposite sign. \(\square\)

Bounds needed only for sufficiently large \(x\) can be extended to all \(x\ge0\) by enlarging \(C\).

### Corollary 37.3 — Fixed-width boundedness and RH

For this one fixed \(h\), each of the following is equivalent to RH:

1. \(\mathcal E_h\) is bounded on \([0,\infty)\).
2. \(\mathcal E_h\) has a finite upper bound.
3. \(\mathcal E_h\) has a finite lower bound.
4. For every \(a>0\), there is \(C_a<\infty\) such that
   \(\mathcal E_h(x)\le C_a e^{ax}\).
5. The same assertion with the inequality
   \(\mathcal E_h(x)\ge-C_a e^{ax}\).

**Proof of the implications to RH.** Apply Theorem 37.2 with \(a=0\) for 1–3, or with arbitrarily small positive \(a\) for 4–5. The functional equation reflects any zero to the other side of the critical line, so excluding the right half proves RH; see [NIST DLMF, §25.4](https://dlmf.nist.gov/25.4).

**Proof of the converse.** Under RH the completed form is positive semidefinite and translation invariant. Hence Cauchy–Schwarz for that form gives
\[
|\mathcal Q(\phi_h,\tau_x\phi_h)|\le\mathcal Q[\phi_h].
\]
For \(x>2h\), Theorem 29.2 identifies this cross term with
\(-\mathcal E_h(x)-\mathcal J_h(x)\).
The explicit \(\mathcal J_h\) is bounded on \(x\ge3h\), and \(\mathcal E_h\) is bounded on compact intervals. Thus RH implies statement 1. \(\square\)

In particular, even a one-sided polynomial bound
\[
\mathcal E_h(x)\le C(1+x)^A
\quad\text{or}\quad
\mathcal E_h(x)\ge-C(1+x)^A
\tag{37.5}
\]
with some fixed finite \(A\ge0\) would imply RH. Such a polynomial is dominated by \(C_a e^{ax}\) for every \(a>0\).

These are proved implications. None of the required one-sided bounds has been proved unconditionally here.

## 38. Polynomial lower losses suffice for RH

The one-sided criterion strengthens (32.2) further. It is enough to allow a polynomial loss in the logarithmic support diameter.

### 38.1 Two fixed-width hats give the bridge

Keep \(h=h_*\), and set
\[
f_x^+=\phi_h+\tau_x\phi_h,\qquad x>2h.
\]
The two supports are disjoint, so
\[
\|f_x^+\|_2^2=2\|\phi_h\|_2^2=\frac{4h}{3}.
\tag{38.1}
\]
Translation invariance and positivity of \(\mathcal D\) give
\[
\mathcal D[f_x^+]\le4\mathcal D[\phi_h].
\tag{38.2}
\]
Meanwhile the *completed*, signed form gives the exact identity
\[
\boxed{
\mathcal Q[f_x^+]
=2\mathcal Q[\phi_h]-2\mathcal E_h(x)-2\mathcal J_h(x).
}
\tag{38.3}
\]
The pole contribution is included in this identity, through Theorem 29.2.

### Theorem 38.1 — Polynomial semiboundedness criterion

Each of the following is equivalent to RH:

1. There exists \(C<\infty\), independent of support, such that
   \[
   \mathcal Q[f]\ge-C\|f\|_2^2
   \quad\text{for all compactly supported admissible }f.
   \tag{38.4}
   \]
2. The same assertion with \(\mathcal D[f]\) in place of \(\|f\|_2^2\).
3. There exist finite constants \(C,A\ge0\) such that
   \[
   \boxed{
   \mathcal Q_L[f]\ge-C(1+L)^A\mathcal D[f]
   \quad\text{for all }L\ge1\text{ and all admissible }f
   \text{ of support diameter at most }L.
   }
   \tag{38.5}
   \]

Statement 3 is also equivalent to RH when its right side uses the \(L^2\) norm. It is enough in these statements to test only the single family \(f_x^+\).

**Proof.** RH supplies all these bounds with \(C=0\). A bound as in (38.5), applied to \(f_x^+\) with support diameter \(x+2h\), gives by (38.2)–(38.3)
\[
\mathcal E_h(x)
\le \mathcal Q[\phi_h]
+2C(1+x+2h)^A\mathcal D[\phi_h]
-\mathcal J_h(x).
\]
Since \(\mathcal J_h(x)\ge0\), this is a one-sided polynomial upper bound for \(\mathcal E_h\). Corollary 37.3 proves RH. The \(L^2\) version follows from (38.1). Constants and the case \(A=0\) are special cases. \(\square\)

The criterion is specific to this arithmetic form. A general translation-invariant quadratic form can be bounded below without being positive.

For the compact signed operator defined in (28.1), Theorem 38.1 says in particular
\[
\boxed{
\sup_{L\ge1}\sup\sigma(\mathcal K_L)<\infty
\quad\Longleftrightarrow\quad\mathrm{RH}.
}
\tag{38.6}
\]
More generally, even
\[
\boxed{
\sup\sigma(\mathcal K_L)\le C(1+L)^A
\quad(L\ge1)
}
\tag{38.7}
\]
for some finite \(C,A\) would suffice. This follows from (28.2). The spectral quantity is the top eigenvalue or spectral supremum, not the absolute operator norm.

Uniform or polynomial bounds in (38.6)–(38.7) remain unproved here.

### 38.2 The polynomial criterion also applies to the actual finite matrices

Let \(\mathsf D_j\) be the Gram matrix of the fixed positive energy \(\mathcal D\) in the hat basis:
\[
c^*\mathsf D_jc=\mathcal D\!\left[\sum_kc_k\phi_{j,k}\right].
\]
It is positive definite, satisfies \(\mathsf D_j\succeq\mathsf M_j\), and obeys
\[
J_j^*\mathsf D_{j+1}J_j=\mathsf D_j.
\tag{38.8}
\]

### Theorem 38.2 — A weaker finite-matrix RH target

RH is equivalent to the existence of some finite \(C,A\ge0\) for which
\[
\boxed{
\mathsf W_j+C(1+j)^A\mathsf D_j\succeq0
\quad\text{for every sufficiently large }j.
}
\tag{38.9}
\]
The same equivalence holds with \(\mathsf M_j\) in place of \(\mathsf D_j\).

The growing tolerance prevents using the simple fixed-vector limit proof of Theorem 29.1. A quantitative approximation is needed.

**Proof.** Only the implication to RH needs proof. Center the two hats:
\[
F_x=\tau_{-x/2}\phi_{h_*}+\tau_{x/2}\phi_{h_*}.
\]
Its form values are the same as those of \(f_x^+\). Choose
\[
j(x)=\left\lceil\frac{x+2h_*+2}{2\log2}\right\rceil.
\tag{38.10}
\]
Thus \(L_{j(x)}=x+O(1)\), and the support lies at least distance \(1\) inside the endpoints. Let \(v_j\in V_j\) be the nodal linear interpolant of \(F_x\).

Each hat has only three changes of slope. Interpolation is exact away from the cells containing these points; on the exceptional cells the error is \(O(h_j)\). Uniformly in \(x\),
\[
\|v_j-F_x\|_2\le C_{h_*}h_j^{3/2},
\qquad
\|v_j-F_x\|_{H^1}\le C_{h_*}h_j^{1/2}.
\tag{38.11}
\]
Also the \(H^1\) norms of \(F_x\) and \(v_j\) are uniformly bounded.

The archimedean form obeys
\[
|A(f,g)|\le C\|f\|_{H^1}\|g\|_{H^1}.
\]
The remaining prime and pole operator on a window of diameter \(L\) has the elementary bound
\[
\|P_L+R_L\|\le C(1+L)e^{L/2}.
\tag{38.12}
\]
For the prime part this follows from \(\Lambda(q)\le L\) and
\(\sum_{n\le e^L}n^{-1/2}\le2e^{L/2}\); the pole norm is bounded by \(L+2\sinh(L/2)\).

Combining (38.11), (38.12), and \(h_je^{L_j/2}=\log2\) yields
\[
\boxed{
|\mathcal Q[v_j]-\mathcal Q[F_x]|
\le C_{h_*}(1+L_j)\sqrt{h_j}=o(1)
}
\tag{38.13}
\]
as \(x\to\infty\). Moreover \(\mathcal D[v_j]\le C_{h_*}\), by the uniform \(H^1\) bound.

Hypothesis (38.9) consequently gives
\[
\mathcal Q[F_x]\ge-C'(1+x)^A-o(1).
\]
Equations (38.3) and (37.5) imply RH.

If the assumed matrix bound uses \(\mathsf M_j\), it implies the bound using \(\mathsf D_j\), or the same proof can use the uniformly bounded \(L^2\) norms. Under RH both matrix inequalities hold with \(C=0\). \(\square\)

The exponential mesh refinement is doing concrete work in (38.13): it makes the interpolation error small enough to survive the crude exponential bound on the prime and pole operator.

### 38.3 A rigorous spectral dichotomy

Define
\[
\lambda_j=\inf_{c\ne0}\frac{c^*\mathsf W_jc}{c^*\mathsf M_jc},
\qquad
\mu_j=\inf_{c\ne0}\frac{c^*\mathsf W_jc}{c^*\mathsf D_jc}.
\]
Both sequences are nonincreasing, by the exact refinement identities. Then:

- Under RH, \(\lambda_j,\mu_j\ge0\) for every \(j\).
- If RH is false, both sequences tend to \(-\infty\).
- More strongly, if RH is false, then for every fixed \(A\ge0\),
  \[
  \boxed{
  \inf_j\frac{\lambda_j}{(1+j)^A}
  =\inf_j\frac{\mu_j}{(1+j)^A}
  =-\infty.
  }
  \tag{38.14}
  \]

**Proof.** A finite lower bound in either part of (38.14) would give a polynomial certificate of the form covered by Theorem 38.2, hence RH. The constant case and monotonicity give divergence to \(-\infty\). \(\square\)

This does not assert that a negative direction exists. It describes what any failure of RH would force in these exact signed matrices.

## 39. Why fine-scale scalar bounds do not settle the fixed-width criterion

The unconditional sparse theorem and the fixed-width RH criterion are compatible. Their test functions behave differently under refinement.

Let \(H=h_*=\log2/4\), and let \(h=h_j=H/N\), with the integer \(N=2^{j-2}\). Set
\[
\alpha_k=(1-|k|/N)_+.
\]
The exact reconstruction is
\[
\phi_H=\sum_{|k|<N}\alpha_k\,\tau_{kh}\phi_h.
\tag{39.1}
\]
Its coefficients satisfy
\[
\sum_k\alpha_k=N,\qquad
\sum_k\alpha_k^2=\frac{2N^2+1}{3N}.
\tag{39.2}
\]
Thus the effective coefficient count of this one fixed coarse hat is
\[
\frac{3N^3}{2N^2+1}\sim\frac32N.
\tag{39.3}
\]
For two separated coarse hats it is asymptotic to \(3N\), far beyond the \(O(j)\) range in Theorem 34.1.

### Theorem 39.1 — Exact signed discrepancy refinement

With these coefficients,
\[
\boxed{
\mathcal E_H(x)=
\sum_{k,l}\alpha_k\alpha_l
\mathcal E_h\bigl(x+(k-l)h\bigr).
}
\tag{39.4}
\]
The corresponding identity holds for the complete kernel \(\mathcal W_H\). When all shifted arguments exceed \(2h\), it also holds for \(\mathcal J_H\).

**Proof.** Autocorrelation of (39.1) gives
\[
g_H(u)=\sum_{k,l}\alpha_k\alpha_l
g_h\bigl(u+(k-l)h\bigr).
\]
Apply this identity to each prime-power term. For the smooth subtraction, the exponential moments of (39.1) give
\[
m_H^2=m_h^2
\left(\sum_k\alpha_ke^{kh/2}\right)
\left(\sum_l\alpha_le^{-lh/2}\right).
\]
This proves (39.4), including its centering term. The other identities follow from the same convolution calculation. \(\square\)

For \(x\ge3H\) and \(x+2H\le L_j\), the entry estimates imply
\[
|\mathcal E_h(x+(k-l)h)|\le C h
\]
for all relevant \(k,l\). Here the arguments are bounded away from \(2h\); the explicit archimedean remainder is also \(O(h)\).
Taking absolute values in (39.4) would yield only
\[
\boxed{
|\mathcal E_H(x)|\le C hN^2=C\frac{H^2}{h}.
}
\tag{39.5}
\]
The right side grows exponentially with \(j\). It gives neither a fixed-width boundedness result nor a polynomial bound in \(x\) at the largest represented separations.

Equation (39.4) identifies the actual missing cancellation: many signed fine-scale discrepancies must be combined with their exact reconstruction weights. The individual \(O(h)\) estimates do not control that combination.

## 40. Use an increasing polynomial tolerance in the signed Schur induction

Theorem 38.2 removes the decreasing-tolerance difficulty identified in Section 30.3. A polynomial tolerance may increase with the support scale and still suffice for RH.

Choose fixed \(C>0\), \(A\ge1\), and put
\[
\tau_j=C(1+j)^A,\qquad
\mathsf H_j=\mathsf W_j+\tau_j\mathsf D_j.
\tag{40.1}
\]
There is no loss in allowing \(A\ge1\): any smaller admissible polynomial loss can be enlarged.

### Theorem 40.1 — The inherited block has a known positive buffer

If \(\mathsf H_j\succeq0\), then
\[
\boxed{
J_j^*\mathsf H_{j+1}J_j
=\mathsf H_j+(\tau_{j+1}-\tau_j)\mathsf D_j
\succeq(\tau_{j+1}-\tau_j)\mathsf D_j.
}
\tag{40.2}
\]
Moreover
\[
\delta_j:=\tau_{j+1}-\tau_j
=C\bigl((j+2)^A-(j+1)^A\bigr)\ge C.
\tag{40.3}
\]

**Proof.** Use the exact refinement identities for both \(\mathsf W_j\) and \(\mathsf D_j\). The final inequality follows from \(A\ge1\). \(\square\)

This is a genuine positive margin available from the induction hypothesis. It does not depend on resolving a very small unshifted Weil eigenvalue.

### 40.1 Retain the entire new signed block

Use the \(\mathcal D\) inner product to decompose
\[
V_{j+1}=V_j\oplus_{\mathcal D}Y_j
\]
and choose energy-orthonormal bases in both summands. In these bases,
\[
\mathsf H_{j+1}=
\begin{pmatrix}
\mathsf A_j&\mathsf B_j\\
\mathsf B_j^*&\mathsf C_j
\end{pmatrix},
\qquad
\mathsf A_j\succeq\delta_j I.
\tag{40.4}
\]
The off-diagonal block of the added energy term is zero, so \(\mathsf B_j\) is exactly the cross term of the completed signed Weil form. Its prime-power and pole contributions remain included.

The complete new-direction Schur complement is
\[
\mathsf S_j=\mathsf C_j-\mathsf B_j^*\mathsf A_j^{-1}\mathsf B_j.
\tag{40.5}
\]
For any trial map \(X_j:Y_j\to V_j\), define
\[
\mathsf R_j=\mathsf B_j-\mathsf A_jX_j,
\]
\[
\mathsf S_{X,j}
=\mathsf C_j-\mathsf B_j^*X_j-X_j^*\mathsf B_j
+X_j^*\mathsf A_jX_j.
\tag{40.6}
\]
The exact identity is
\[
\boxed{
\mathsf S_j
=\mathsf S_{X,j}-\mathsf R_j^*\mathsf A_j^{-1}\mathsf R_j
\succeq
\mathsf S_{X,j}-\delta_j^{-1}\mathsf R_j^*\mathsf R_j.
}
\tag{40.7}
\]
It follows by the same expansion as Theorem 28.1.

Consequently the following is a sufficient induction target:
\[
\boxed{
\mathsf S_{X,j}\succeq
\delta_j^{-1}\mathsf R_j^*\mathsf R_j
\quad\text{for every }j\ge j_0.
}
\tag{40.8}
\]
Together with one base certificate \(\mathsf H_{j_0}\succeq0\), this proves (38.9) and hence RH.

A base shift can always be made large enough for one finite matrix. The unresolved work is to choose fixed \(C,A\) and establish (40.8) uniformly as the dimension and support grow. The positive buffer in (40.3) does not by itself control either the new diagonal block or the signed coupling.

### 40.2 What has and has not been achieved

| Statement | Status after this continuation |
|---|---|
| \(\mathsf W_j=\ell_j\mathsf M_j+\mathsf Z_j\), with every entry of \(\mathsf Z_j\) bounded by \(Ch_j\) | Proved using the upper sieve and exact archimedean scaling |
| Positivity on all coefficient vectors with sufficiently small \(O(j)\) effective count | Proved unconditionally |
| Uniformly bounded mass-normalized \(\mathsf Z_j\) | Disproved by exact refinement |
| One-sided fixed-width discrepancy bound implies RH | Proved via its exact Laplace transform |
| Any polynomial lower loss in logarithmic support implies RH | Proved |
| Any polynomial lower loss for the actual nested matrices implies RH | Proved, including a quantitative interpolation argument |
| Increasing-tolerance inherited Schur block has margin \(\delta_j\ge C\) | Proved |
| Uniform new-direction inequality (40.8) | Open |
| RH | Not proved |

The upper-sieve input bounds positive local masses only. It does not establish the signed collective estimate (40.8) or the fixed-width bound in Section 37. The decisive missing theorem has therefore not been supplied by the new sparse positivity result.

The newly derived hat transform, discrepancy-refinement identity, and refinement-mask norms were also checked independently by elementary quadrature and finite sums. These were sanity checks of constants and signs; no floating-point positivity test is used as a proof. No Lean work was performed.

**Updated handoff instruction:** Prioritize a polynomial lower bound, or the increasing-tolerance signed Schur estimate (40.8), rather than a vanishing or strictly positive margin. Preserve the completed pole term, the archimedean difference energy, and all cross terms. Use the sparse theorem to identify which directions are already controlled; the unresolved directions combine a growing number of coefficients. A bound for individual discrepancies on the shrinking mesh must not be substituted for the fixed-width discrepancy bound. The exact bridge between those scales is (39.4), and its signed reconstruction cost remains to be controlled.
