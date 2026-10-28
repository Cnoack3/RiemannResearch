# Single-zero detectors and the full Landau error budget

28 October 2026.

## Status and provenance

This is a paper-level research argument and comparison, not a new Lean-verified theorem or a proof of RH. It records an explicit finite-cutoff detector, a localized infinite-zero detector, and the exact arithmetic estimate still needed. No Lean declaration or existing research status is changed.

The construction responds to the question whether the current uniform Landau and prime-torus Fourier estimates can detect a single horizontal displacement once the complete test norm is included.

Sources and existing project context:

- Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1, supports the uniform scalar comparison:
  https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
- Ford--Zaharescu, On the distribution of imaginary parts of zeros of the Riemann zeta function, Lemma 1, supports the nearest-prime-power kernel and a convenient uniform remainder:
  https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf
- Burnol, The Explicit Formula in simple terms, section Weil's positivity criterion and stochastic processes, explains the classical interpolation mechanism for negative witnesses, including removal of pole contributions:
  https://arxiv.org/pdf/math/9810169
- Bondarenko--Radchenko--Seip, Fourier Interpolation with Zeros of Zeta and L-Functions, equation (1.1), supports the full-zero explicit formula and its test class:
  https://arxiv.org/pdf/2005.02996
- Analysis/ActualUniformRationalLandau.lean supplies the project's unconditional coarser rational Landau bound.
- Analysis/ActualPrimeTorusFMZRate.lean supplies the quantitative moving-test theorem with the explicit UniformSelbergDensity (1/4) premise.
- RH/E4ProofAttempt20261010.md already distinguishes ordinate blindness from horizontal energy and gives a fixed-width, growing-degree Gaussian interpolation argument.
- RH/DivisorReciprocalAndZeroRemoval20260929.md records actual transform zero removal and the remaining negative-witness/positivity obligations.

The arguments below specialize classical finite approximation and Weil interpolation ideas to the current norm question. No mathematical novelty claim is made.

## 1. What a finite exceptional pair changes

Let a positive-height multiset be invariant, with multiplicity, under
\(\rho\mapsto1-\overline\rho\). At height \(\tau>0\), compare two critical-line copies with the pair
\[
\tfrac12+a+i\tau,\qquad \tfrac12-a+i\tau,\qquad 0<a<\tfrac12.
\]
Include conjugate copies below the axis when discussing the full multiset.

For \(T\ge\tau\), the difference in the uncentered Landau sum is exactly
\[
\Delta_a(x,T)
=e^{i\tau\log x}\left(x^{1/2+a}+x^{1/2-a}-2\sqrt x\right)
=x^{1/2+a}(1-x^{-a})^2e^{i\tau\log x}.
\]
It is bounded by \(x\), uniformly in \(x>1\). For fixed \(x\) it is \(O_x(1)\).

For the previously recorded uniform envelope
\[
E(x,T)=x\log^2(2x)+x\log(2T)
+\log(2T)\min\{T,1/\log x\},
\]
one has
\[
|\Delta_a(x,T)|\le E(x,T)/\log(2T).
\]
Consequently every finite synthesis obeys
\[
\left|\sum_j c_j\Delta_a(x_j,T)\right|
\le\frac1{\log(2T)}\sum_j|c_j|E(x_j,T).
\]
The frequencies and coefficients can depend on T. This inequality is an obstruction to beating the full error allowance by termwise bounds and the triangle inequality.

These modified multisets are abstract comparisons, not asserted alternative zero sets of zeta. They do not preserve the exact arithmetic explicit formula. They show what information the stated asymptotic inequalities and ordinate statistics do not resolve.

Every ordinate-only statistic is exactly unchanged by this comparison. Increasing its dimension or Fourier support does not restore the discarded real parts.

## 2. A detector using powers of one prime

Fix a finite positive-height cutoff and put
\[
N=N(T),\qquad
L_T(H)=\sum_{0<\gamma\le T}e^{H(\rho-1/2)},
\]
always with multiplicity.

For any fixed prime p,
\[
\boxed{
\text{every zero in the cutoff is critical}
\iff
|L_T(k\log p)|\le N\quad\text{for every integer }k\ge1.
}
\tag{2.1}
\]

The empty cutoff is immediate. If all real parts equal 1/2, the triangle inequality proves the bound.

For the converse, suppose a pair
\[
\rho_\pm=\tfrac12\pm a+i\tau
\]
occurs with multiplicity m at each point. Thus these selected points account for \(2m\) of the N copies. Let the distinct ordinates in the cutoff be
\(\tau=\gamma_0,\gamma_1,\ldots,\gamma_{J-1}\).

Choose a positive integer K with
\[
\cosh(aK\log p)>\frac{N}{2m}.
\]
For example,
\[
K=\left\lceil\frac{\log(N/m+1)}{a\log p}\right\rceil
\]
suffices.

Apply simultaneous Dirichlet approximation with denominator parameter 6 to
\[
\alpha_j=\frac{K(\gamma_j-\tau)\log p}{2\pi},\qquad 1\le j<J.
\]
There is \(1\le n\le6^{J-1}\) with \(\|n\alpha_j\|_{\mathbb R/\mathbb Z}\le1/6\) for every j. For J=1 use n=1. Set \(k=Kn\) and \(H=k\log p\). Then
\[
\cos((\gamma-\tau)H)\ge\tfrac12
\]
for every zero in the cutoff, with cosine 1 at the target ordinate.

In the exact expression
\[
\Re(e^{-i\tau H}L_T(H))
=\sum_{0<\gamma\le T}e^{H(\beta-1/2)}
 \cos((\gamma-\tau)H),
\]
all terms are nonnegative. The selected pair alone contributes
\(2m\cosh(aH)>N\). Hence \(|L_T(H)|>N\), proving (2.1).

The witness exponent satisfies
\[
k\le K6^{J-1}.
\]
No simplicity assumption or restriction on the other real parts is used.

### Exact quadratic form and its sign

Define
\[
B_H(s)=e^{H(s-1/2-i\tau)}-1
\]
and the finite Hermitian form
\[
Q_T(B_H)=
\sum_{0<\gamma\le T}B_H(\rho)
 \overline{B_H(1-\overline\rho)}.
\]
Reflection preserves the cutoff and multiplicity, so
\[
\boxed{Q_T(B_H)=2N-2\Re(e^{-i\tau H}L_T(H)).}
\tag{2.2}
\]
Equivalently,
\[
Q_T(B_H)=
\sum_{0<\gamma\le T}
\left[2-2\cosh(H(\beta-\tfrac12))
 \cos(H(\gamma-\tau))\right].
\]
The equality is for the complete reflected sum; an individual unsymmetrized summand need not be real.

The selected pair contributes exactly
\[
4m-4m\cosh(aH)=-8m\sinh^2(aH/2).
\]
At the simultaneous-approximation frequency,
\[
Q_T(B_H)\le 2N-4m\cosh(aH)<0.
\]
On the critical line every original summand is
\(|e^{iH(\gamma-\tau)}-1|^2\ge0\).

Equivalently, the two-by-two matrix
\[
G_{T,k}=
\begin{pmatrix}
N&L_T(k\log p)\\
\overline{L_T(k\log p)}&N
\end{pmatrix}
\]
has eigenvalues \(N\pm|L_T(k\log p)|\). Positivity for all k at one fixed prime is exactly the criticality statement in (2.1). The construction is a detector; it does not prove these matrices are positive.

## 3. The exact Fourier norm is one after normalization

Use circle coordinates in turns:
\[
\theta_p(\gamma)=\frac{\gamma\log p}{2\pi}\bmod1.
\]
The associated real-torus energy is
\[
F_H(\theta)=|e^{2\pi i k\theta_p-i\tau H}-1|^2
=2-e^{-i\tau H}\chi_{ke_p}(\theta)
-e^{i\tau H}\chi_{-ke_p}(\theta).
\]
Its only coefficients have magnitudes 2, 1, and 1. Therefore
\[
W_2(F_H)=2+2(1+H)^2=:M_H.
\]
For
\[
\widetilde F_H=F_H/M_H,\qquad
\widetilde B_H=B_H/\sqrt{M_H},
\]
one has exactly
\[
\boxed{W_2(\widetilde F_H)=1.}
\tag{3.1}
\]
The target contribution to the actual Hermitian form is
\[
-\frac{8m\sinh^2(aH/2)}{M_H}
\sim-\frac{2m e^{aH}}{M_H}.
\]

Thus radial amplification survives complete polynomial Fourier-norm normalization. The obstruction is the different analytic norm required off the real torus, not merely growth of W2.

The sample of \(\widetilde F_H\) on actual ordinates is nonnegative and does not equal the actual Hermitian form away from RH. Confusing those two quantities would erase the main difficulty.

## 4. Why the present Landau bounds do not certify the detector

At \(x=p^k=e^H\), the centered formula has the exact decomposition
\[
L_T(H)=
-\frac{T\log p}{2\pi}e^{-H/2}+R_L(H,T).
\]
Ford--Zaharescu Lemma 1 supplies, for example,
\[
|R_L(H,T)|\ll
e^{H/2}(H+\log(2T))^2+
e^{-H/2}\frac{\log(2T)}{H}.
\tag{4.1}
\]
This deliberately convenient published envelope suffices for the comparison; sharper logarithmic factors do not change its exponential rate.

Substitution into (2.2) gives the complete signed identity
\[
Q_T(B_H)=2N+
\frac{T\log p}{\pi}e^{-H/2}\cos(\tau H)
-2\Re(e^{-i\tau H}R_L(H,T)).
\tag{4.2}
\]
After division by \(M_H\), both the signal and the remainder allowance are divided by the same number. Their exponential scales are
\[
\frac{e^{aH}}{M_H}
\quad\hbox{and}\quad
\frac{e^{H/2}}{M_H}\operatorname{poly}(H,\log T).
\]
Since \(a<1/2\), the available allowance grows faster. This does not assert a lower bound on the actual error: it says the supplied upper bound cannot exclude the detected negative value.

The quantitative prime-torus theorem controls the ordinate sample, not \(R_L\) or the radial form (4.2) at arbitrary H. Scaling to W2=1 does not extend a phase-to-Landau comparison beyond its valid range.

A fixed-cutoff estimate of subexponential growth in H for the relevant signed radial remainder would finish this route. Such an estimate for every cutoff is RH-strength and is not presently supplied.

## 5. A localized detector for the complete infinite zero set

The following alternative avoids an enormous simultaneous recurrence and preserves the complete zero sum.

Put
\[
z_\rho=\frac{\rho-1/2}{i}=\gamma-i(\beta-\tfrac12).
\]
An off-line pair at positive height \(\tau\) gives
\(z_\pm=\tau\pm ia\), with multiplicity m at each point.

Let the local window be \(|\Re z-\tau|\le1\). It contains only finitely many distinct spectral points. Work with \(w=z-\tau\). Choose a real polynomial P satisfying:

1. \(P(ia)=i\) and \(P(-ia)=-i\).
2. P vanishes at every other distinct shifted zero in this window.
3. \(P(-\tau+i/2)=P(-\tau-i/2)=0\), which will remove the pole terms.
4. \(P(i/2)=P(-i/2)=1\), which makes the analytic Fourier cost explicit.
5. \(P(0)=0\), if this value has not already been imposed by a critical zero.

These requirements are consistent. Nontrivial shifted zero nodes have imaginary parts strictly between -1/2 and 1/2; the target is distinct from every other selected zero; and the pole nodes differ from the two boundary-normalization nodes because \(\tau>0\). All assigned values respect complex conjugation.

For the finite set D of interpolation nodes with values \(v_z\), the ordinary Lagrange formula
\[
P(w)=\sum_{z\in D}v_z
 \prod_{\substack{y\in D\\y\ne z}}\frac{w-y}{z-y}
\]
has real coefficients by uniqueness and conjugation symmetry. Multiplicities remain in the zero sum; derivative interpolation is unnecessary.

Define, for R>=1,
\[
f_R(z)=P(z-\tau)e^{-R(z-\tau)^2/2},
\qquad
h_R(z)=f_R(z)^2.
\]
On the real axis, \(h_R(t)\ge0\). The target contributes exactly
\[
m h_R(\tau+ia)+m h_R(\tau-ia)
=-2m e^{a^2R}.
\]

All other local zero contributions vanish. Outside the window, write
\(w=\eta-i\delta\), with \(|\eta|>1\) and \(|\delta|<1/2\). Then
\[
|h_R(z_\rho)|=|P(w)|^2e^{-R(\eta^2-\delta^2)}.
\]
Here \(\eta^2-\delta^2>3/4\). For R>=1, factor off
\(e^{-3(R-1)/4}\) and retain one Gaussian factor. Polynomial growth of P and the ordinary zero-count bound \(N(U)=O(U\log(U+2))\) make the remaining sum finite.

Thus, with every nontrivial zero and multiplicity retained,
\[
\boxed{
Q_R:=\sum_\rho h_R(z_\rho)
=-2m e^{a^2R}+O_{P,\tau}(e^{-3R/4}).
}
\tag{5.1}
\]
In particular it is negative for large R. This works even if infinitely many other zeros are off the line. No maximal-displacement zero is selected.

This differs from the older fixed-width/growing-degree interpolation argument: here the interpolation window and degree are fixed after choosing the hypothetical target, while the Gaussian parameter R grows.

## 6. Exact arithmetic expression and pole removal

Use the Fourier convention
\[
g_R(u)=\frac1{2\pi}\int_{\mathbb R}h_R(t)e^{-itu}\,dt,
\qquad
h_R(z)=\int_{\mathbb R}g_R(u)e^{izu}\,du.
\]
A polynomial times a Gaussian and its Fourier transform have all the decay needed here. For each fixed R the relevant sums and integrals converge absolutely.

Apply the classical even explicit formula to
\(h_R^{\rm ev}(z)=(h_R(z)+h_R(-z))/2\). The zero sum is unchanged by the symmetry \(z_\rho\mapsto-z_\rho\). The prime pairing is also unchanged. The archimedean kernel is even, so it can be integrated against the original h_R.

The complete identity is
\[
Q_R=h_R(i/2)+h_R(-i/2)+\mathcal A_R-\mathcal P_R,
\]
where
\[
\mathcal A_R=
\frac1{2\pi}\int_{\mathbb R}h_R(t)
\left[\Re\frac{\Gamma'}{\Gamma}\left(\frac14+\frac{it}{2}\right)
-\log\pi\right]dt,
\]
and
\[
\mathcal P_R=
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\left[g_R(\log n)+g_R(-\log n)\right].
\]
The imposed interpolation values give \(h_R(i/2)=h_R(-i/2)=0\), hence
\[
\boxed{Q_R=\mathcal A_R-\mathcal P_R.}
\tag{6.1}
\]
The identity retains every prime power and the entire archimedean contribution. No passage from an unregularized infinite Landau sum through a Fourier integral is used.

## 7. The analytic norm that must be paid

The ordinary continuous frequency norm can be small:
\[
\int_{\mathbb R}|g_R(u)|(1+|u|)^2\,du=O_P(1)
\quad(R\ge1),
\]
using P(0)=0. To see this, expand \(P(v)^2\) into powers \(v^j\), with j>=2, and differentiate the Fourier transform of \(e^{-Rv^2}\). Its jth derivative has weighted L1 size \(O(R^{-j/2}(1+R))\).

This continuous norm is not automatically the discrete prime-height W2 norm. More importantly, it controls the real spectral axis, not the full strip.

The analytic norm required by the standard absolute centered Landau envelope is
\[
\mathcal N_{1/2}(g_R)=
\int_{\mathbb R}|g_R(u)|e^{|u|/2}\,du.
\]
The boundary normalization gives an exact lower bound:
\[
h_R(\tau+i/2)=e^{R/4},
\]
and therefore
\[
\boxed{\mathcal N_{1/2}(g_R)\ge e^{R/4}.}
\tag{7.1}
\]
For the evenized transform an eventual lower bound \(\tfrac14e^{R/4}\) remains valid, since the extra reflected evaluation is smaller by
\(O_{P,\tau}(e^{-4\tau^2R})\).

For a simple illustrative polynomial \(P(w)=w\),
\[
g_R(u)=\frac{e^{-i\tau u}}{\sqrt{4\pi R}}e^{-u^2/(4R)}
\left(\frac1{2R}-\frac{u^2}{4R^2}\right).
\]
This example illustrates the transform; it does not impose the full interpolation conditions.

In general fixed P only introduces polynomial factors. The exponential cost follows from
\[
\frac u2-\frac{u^2}{4R}
=\frac R4-\frac{(u-R)^2}{4R}.
\]
Thus direct absolute arithmetic or Landau estimates have an allowance at the scale
\(\operatorname{poly}(R)e^{R/4}\), whereas the off-line signal in (5.1) has scale \(e^{a^2R}\). Since \(a^2<1/4\), that allowance cannot certify a contradiction.

## 8. A precise remaining arithmetic target

It suffices to prove, for every fixed \(\tau>0\), every real polynomial P satisfying the pole conditions, and every \(\varepsilon>0\), an eventual bound
\[
\boxed{
\mathcal A_R-\mathcal P_R
\ge -C_{P,\tau,\varepsilon}e^{\varepsilon R}.
}
\tag{8.1}
\]
This asks for subexponential growth of the negative part, not exact positivity at every R.

If an off-line pair exists, use its interpolating P and choose \(0<\varepsilon<a^2\). Equation (5.1) contradicts (8.1). Conversely, RH makes each \(h_R(\gamma)\) nonnegative, so (8.1) holds with zero error. Therefore the assertion for this family is RH-equivalent. It is an Open arithmetic estimate, not a consequence established here.

A potentially useful division is:

- Establish a signed lower bound with exponential rate \(\eta\).
- It would exclude displacements with \(a^2>\eta\) by this construction.
- Rates tending to zero would exclude every nonzero displacement.
- The present absolute method has the boundary rate 1/4 and excludes no point in the open critical strip.

In a fixed-degree polynomial basis the arithmetic expression is a finite real symmetric quadratic form
\[
Q_R(P,\tau)=c^{\mathsf T}M_d(R,\tau)c.
\]
Its entries come from the full explicit formula applied to
\((z-\tau)^{j+k}e^{-R(z-\tau)^2}\). One can restrict to the coefficient subspace satisfying the pole conditions. A lower spectral bound
\[
c^{\mathsf T}M_d(R,\tau)c
\ge-C_{d,\tau,\varepsilon}e^{\varepsilon R}\|c\|_2^2
\]
would supply (8.1). This matrix formulation gives a concrete target for complete signed Schur complements or an arithmetic factorization. Numerical positivity for finitely many matrices is not a proof of this bound.

## 9. Next research obligations and verification boundary

1. Open formalization: the one-prime finite-cutoff criterion, including multiplicity-preserving reflection and simultaneous approximation.
2. Open formalization: the exact three-coefficient W2 calculation and the negative actual Hermitian witness.
3. Open formalization: real polynomial interpolation, complete infinite Gaussian tail, explicit-formula admissibility, and analytic norm lower bound for (5.1)--(7.1).
4. Open analytic result: an independent signed estimate such as (8.1), or a comparable detector-specific bound improving the actual radial remainder.
5. Preserve the full prime/archimedean difference or matrix before estimating; repeated absolute bounds reintroduce the e^(R/4) barrier.
6. The current phase-only theorem and its explicit density hypothesis do not supply the missing radial or arithmetic bound.

The concrete progress in this note is the detector construction and the quantitative location of the obstruction. The scalar Landau and ordinate theorems remain useful inputs, but none of the new missing estimates is asserted as proved.

Documentation-only persistence: no Lean verification was submitted for these paper arguments. Publication of this note must not be reported as kernel verification of them.
