# Exact finite Mellin-window laws and the remaining arithmetic estimate

Date: 2026-09-28. Development base: f585c5d69ddc5c9b494259861596d339e9b70d11.

## Scope and verification

The unconditional theorems below concern the actual probability measure
`mellinLaw n`, with exactly n distinct frequencies almost surely. They apply
to every measurable window, hence to every bounded Borel interval. They
assume neither RH nor an infinite determinantal process.

The main application is `RH/MellinWindowCount.lean`. The generic bridge is
weighted Andréief in `Probability/ContinuousProjectionDensity.lean`, followed
by the new compression, generating-function, window-energy, bounded-count-law,
and bounded-count-concentration modules. The count law and moments reuse
`DeterminantalBernoulliCount` and `DeterminantalMoments`: the discrete
site-count theorem is NOT directly applied to a continuum interval.

The complete integrated proof was Lean-checked, including the actual Mellin
specialization. Axiom checks for weighted Andréief, Mellin moments, boundary
variance, Chernoff, and the arithmetic hole bound return only
`propext`, `Classical.choice`, and `Quot.sound`.
The repository checkpoint validates the saved modules and affected dependents.

The general spectral-count principle is classical: Hough, Krishnapur, Peres,
and Virág, *Determinantal Processes and Independence*, Probability Surveys
3 (2006), Theorem 7, DOI 10.1214/154957806000000078,
https://arxiv.org/abs/math/0503110. The contribution here is its proved
continuous-density bridge and specialization to the actual arithmetic
Mellin law, not a claim of a new general DPP theorem.

## Exact law and moments: formalized

Let \(\mu(dt)=dt/(2\pi)\), and let \(\psi_0,\dots,\psi_{n-1}\) be the actual
orthonormal Mellin modes. Set
\[
B_{n,I}(i,j)=\int_I\overline{\psi_i(t)}\psi_j(t)\,d\mu(t),\qquad
K_n(t,u)=\sum_{j<n}\psi_j(t)\overline{\psi_j(u)}.
\]
The matrix is Hermitian and \(0\le B_{n,I}\le1\). Denote its eigenvalues by
\(\lambda_1,\ldots,\lambda_n\in[0,1]\).

If \(X_n(I)\) is the number of sampled frequencies in \(I\), then
\[
\boxed{\mathbb E z^{X_n(I)}
 =\det(1+(z-1)B_{n,I})
 =\prod_{j=1}^n(1-\lambda_j+z\lambda_j).}
\]
The determinant identity is proved for complex z; the spectral count PGF
and distribution transfer use real z. The actual count distribution equals
the distribution of the sum of independent Bernoulli variables with
parameters \(\lambda_j\). Independence is asserted only in this auxiliary
eigenvalue model, not for the sampled spatial positions.

**Proof mechanism.** Multiply the actual density
\(|\det[\psi_i(t_j)]|^2/n!\) by
\(\prod_j(1+(z-1)\mathbf1_I(t_j))\). Expand both determinants, integrate the
coordinate products, and recombine the permutation sums into
\(\det(1+(z-1)B)\). Restricted L² Gram matrices prove positivity; integrating
over the complement proves \(1-B\ge0\). The finite Hermitian spectral theorem
gives the product. Polynomial uniqueness identifies the finite count law.

Consequently, writing \(m=m_{n,I}\) and \(v=v_{n,I}\),
\[
\boxed{
m=\mathbb EX_n(I)=\sum_j\lambda_j
 =\operatorname{tr}B_{n,I}
 =\int_I K_n(t,t)\,d\mu(t),
}
\]
\[
\boxed{
\begin{aligned}
v=\operatorname{Var}X_n(I)
 &=\sum_j\lambda_j(1-\lambda_j)
  =\operatorname{tr}(B_{n,I}-B_{n,I}^2)\\
 &=\int_I K_n(t,t)\,d\mu(t)
   -\int_I\int_I|K_n(t,u)|^2\,d\mu(u)d\mu(t)\\
 &=\int_I\int_{I^c}|K_n(t,u)|^2\,d\mu(u)d\mu(t).
\end{aligned}}
\]
All these identities are formalized. The diagonal is real; the Lean
expectation statement writes its real part explicitly. In particular,
\[
0\le v\le \min\{m,n-m,n/4\}.
\]
The boundary identity is an exact measure of spectral leakage, not an
asymptotic approximation.

The kernel is the repository's actual inverse-Gram kernel. With
\(s(t)=1/2+it\), conductors \(d=2,\dots,n+1\), and
\[
\phi_d(t)=\frac{\zeta(s(t))}{s(t)}(d^{-1}-d^{-s(t)}),
\]
it is
\[
K_n(t,u)=\sum_{d,e}\phi_d(t)(G_n^{-1})_{de}\overline{\phi_e(u)}.
\]
Thus these are exact arithmetic-kernel integrals, not estimates for an
unrelated model matrix.

## Concentration and arithmetic hole bound: formalized

For every \(t\ge0\) and real a,
\[
\boxed{
\mathbb P\{X_n(I)\ge a\}
 \le e^{-ta}\prod_j(1-\lambda_j+e^t\lambda_j),
}
\]
\[
\boxed{
\mathbb P\{X_n(I)\le a\}
 \le e^{ta}\prod_j(1-\lambda_j+e^{-t}\lambda_j).
}
\]
One may take the infimum over t separately in either inequality.
These exact product bounds retain the whole compression spectrum.
They include centered upper/lower tails by putting \(a=m+r\) or \(a=m-r\).
No quantitative arithmetic hypothesis is needed.

The exact hole probability and its convenient upper bound are
\[
\boxed{
\mathbb P\{X_n(I)=0\}=\det(1-B_{n,I})
 =\prod_j(1-\lambda_j)\le e^{-m}.
}
\]
The product equality and exponential inequality are formalized; the
determinant expression is the already formalized PGF at zero.

For every \(n\ge1\), the conductor-two mode gives a bound independent of
the larger rank:
\[
\boxed{
\mathbb P\{X_n(I)=0\}\le
 \exp\left\{-\frac4{\log2}
   \int_I
    \left|\frac{\zeta(1/2+it)}{1/2+it}\right|^2
    \left|\frac12-2^{-1/2-it}\right|^2\,\frac{dt}{2\pi}
 \right\}.}
\]
This uses the checked formula for \(\psi_0\), the inclusion of that mode in
every positive rank, and the newly checked expectation identity. It is
`mellinWindowCount_hole_first_mode`, with
`firstModeWindowMass_eq_arithmetic` identifying the exponent. Its mean
lower-bound counterpart is also proved.

## Relation to the existing covariance and coordinate defect

The covariance identities in
`ArithmeticProjectionDPPDraft20260921.md` use the PHYSICAL-coordinate
cutoff \(R_M\), the completed arithmetic projection \(P_\infty\), and
\[
A_M^P=UR_MP_\infty R_MU^*
 =A_M^0-E_M,\qquad E_M=UR_M(1-P_\infty)R_MU^*\ge0.
\]
This cutoff M is distinct from arithmetic rank n in the new count theorem.
In particular, `windowDeficit M I` must not be identified with the variance
or expectation of \(X_n(I)\).

At the level of finite compressions \(A\) and \(A-E\), the trace variance
functional \(V(A)=\operatorname{tr}(A-A^2)\) satisfies the elementary
paper identity
\[
V(A-E)-V(A)=-\operatorname{tr}E
 +2\operatorname{tr}(AE)-\operatorname{tr}(E^2).
\]
It follows by expanding the square and cyclicity of trace. Thus the same
local arithmetic defect enters both the mean and the variance correction.
This comparison identity is explained on paper here; no additional
continuous nonprojection DPP construction is claimed.

The already checked coordinate identity is
\[
\operatorname{windowDeficit}(1,I)
 =\nu_\infty\,\operatorname{firstModeMass}(I),
\]
where \(\nu_\infty\) is limiting FIRST-PHYSICAL-SITE vacancy.
The firstModeMass in this identity uses the first coordinate feature,
not the conductor-two residue mode \(\psi_0\) above. It is positive on
every positive-measure window, and a zero deficit implies actual
Mathlib RH without a zero-profile provider.

The new checked theorem `first_window_deficit_ge_zero_floor` further gives
\[
\zeta(\rho)=0,\quad\Re\rho>1/2,\quad\rho\ne1
\quad\Longrightarrow\quad
\operatorname{windowDeficit}(1,I)
 \ge \operatorname{siteMellinVacancyFloor}(0,\rho)
       \operatorname{firstModeMass}(I).
\]
The existing explicit formula for this strictly positive floor is
\[
\operatorname{siteMellinVacancyFloor}(0,\rho)
 =\frac{2(2\Re\rho-1)|1-2^{-\rho}|^2}{|\rho|^2}.
\]
This is an unconditional obstruction theorem with the hypothetical zero
explicit in its type, not a claim that an off-critical zero exists.

## Precise remaining arithmetic estimate: rigorous paper reduction, Open

The localization argument in this section is proved on paper below.
Its complete frequency-L² implementation is NOT claimed kernel-verified
by the present commit. Its full-frequency first-site vacancy endpoint and
the implication from that endpoint to RH already exist in Lean.

Let \(e_0\) be the normalized first physical coordinate. Its Mellin image is
\[
h(t)=Ue_0(t)=\sqrt2\,\frac{1-2^{-s(t)}}{s(t)},\qquad\|h\|_{L^2(\mu)}=1.
\]
Let \(P_n\) be the orthogonal projection in the AMBIENT frequency L² space
onto the first n Mellin modes. This ambient interpretation matters because
\(1_Ih\) need not belong to the original Mellin image.

For \(R>0\), set \(I_R=[-R,R]\), \(h_R=1_{I_R}h\),
\[
a_R=\|h_R\|^2,\quad\tau_R=1-a_R,\quad
c_{n,R,d}=\int_{I_R}\overline{\phi_d(t)}h(t)\,d\mu(t).
\]
The finite projection formula gives
\[
J_{n,R}=\|P_nh_R\|^2
 =c_{n,R}^*G_n^{-1}c_{n,R}
 =\int_{I_R^2}\overline{h(t)}K_n(t,u)h(u)\,d\mu(t)d\mu(u),
\]
and
\[
\delta_{n,R}=a_R-J_{n,R}=\|(1-P_n)h_R\|^2\ge0.
\]
These integrals converge by Cauchy--Schwarz and finite rank.

Let \(\nu_n=\|(1-P_n)h\|^2\), the actual finite first-site vacancy.
Reverse triangle inequality and the contraction property give
\[
\left|\sqrt{\nu_n}-\sqrt{\delta_{n,R}}\right|
 \le\|(1-P_n)(h-h_R)\|\le\sqrt{\tau_R}.
\]
Moreover,
\[
|h(t)|^2=\frac{3-2\sqrt2\cos(t\log2)}{t^2+1/4},
\qquad
\tau_R\le\frac{3+2\sqrt2}{\pi R}.
\]
The tail estimate follows by bounding the numerator and integrating \(t^{-2}\)
over \(|t|>R\). Since \(\nu_\infty\le\nu_n\), uniformly in n and R,
\[
\boxed{
\nu_\infty\le
\left(
\sqrt{a_R-c_{n,R}^*G_n^{-1}c_{n,R}}
+\sqrt{\frac{3+2\sqrt2}{\pi R}}
\right)^2.}
\]

**Open sufficient arithmetic estimate.** Find ranks \(n_k\) and radii
\(R_k\to\infty\) such that
\[
\boxed{
a_{R_k}-c_{n_k,R_k}^*G_{n_k}^{-1}c_{n_k,R_k}\longrightarrow0.
}
\]
This would force \(\nu_\infty=0\), and hence RH by the existing first-site
criterion. No rate beyond convergence is necessary here; the omitted tail
already has the displayed unconditional bound.

For comparison,
\[
c_{n,\infty,d}=\langle g_d,e_0\rangle_P=\frac1{\sqrt2\,d},
\qquad
J_{n,\infty}=\frac12\sum_{d,e}\frac{(G_n^{-1})_{de}}{de}
 =\operatorname{integerKernel}(n,0,0).
\]
Thus the open condition is a uniformly localized signed inverse-Gram
saturation estimate. It retains the complex phases and the orientation of
the relevant vector. The eigenvalues/count concentration alone do not
control it. In the eigenbasis of \(B_{n,I_R}\), even the elementary bound
\(J_{n,R}\le\lambda_{\max}(B_{n,I_R})a_R\) shows that saturation requires
eigenvalues near one, but also alignment with their eigenspaces.

Leading sine-kernel behavior or small count variance is therefore
insufficient by itself. The existing `MellinCoordinateScaling` examples
already show that logarithmic normalization can hide a fixed nonzero
coordinate defect. No unconditional RH conclusion is asserted.
