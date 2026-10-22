# Actual uniform rational Landau: rigorous source deduction and stronger operator remainder

This report proves the rational and finite-dimensional consequences of a published unconditional uniform Landau–Gonek theorem. It is a mathematical proof, **not a Lean formalization of that analytic theorem**. The checked repository already supplies the actual multiplicity sums, weighted contour identities, actual Re=2 right-line interchange, count normalization, reflection, and full integer prime-power main operator. The source analytic input and remaining contour estimates are identified explicitly below. The follow-up publication verifies the actual fixed left/horizontal estimates and the arbitrary-height transfer separately; it does not formalize the source analytic theorem.

Source base: Cnoack3/RiemannResearch commit `0944f251e93d6725dbe82188e5bbb0b56d990584`.

## 1. Primary uniform theorem, endpoints, and multiplicity

Baluyot–Gonek, *Explicit formulae and discrepancy estimates for a-points of the Riemann zeta-function*, Pacific J. Math. **303** (2019), 47–74, p.49, reproduces Gonek's actual zeta theorem with absolute implied constants:

<https://msp.org/pjm/2019/303-1/pjm-v303-n1-p02-s.pdf>

For all real \(x,T>1\),

\[
\sum_{0<\gamma\le T}m(\rho)x^\rho
=-\frac{T}{2\pi}\Lambda(x)+O\!\left(x\log(2xT)\log\log(3x)\right)
+O\!\left(\log x\min\{T,x/\delta(x)\}\right)
+O\!\left(\log(2T)\min\{T,1/\log x\}\right).\tag{1}
\]

Here \(\rho=\beta+i\gamma\) runs over actual nontrivial zeta zeros, with their analytic multiplicities, \(\Lambda(x)=\log p\) if \(x=p^a\) for a prime \(p\) and integer \(a\ge1\), and is zero otherwise. The distance \(\delta(x)\) is to the closest prime power **different from \(x\) itself**. The statement uses arbitrary \(T>1\), includes \(\gamma=T\), and imposes no good-height or RH assumption. The multiplicity convention is the usual zero-sum convention and is independently made explicit in the zero-count/contour formulations of these papers.

Equivalently there is one absolute \(C_0>0\) such that the norm of the residual in (1) is at most \(C_0\) times the sum of its three displayed positive error expressions. Increase the three original absolute constants to their maximum to choose \(C_0\).

The original primary source is Gonek, *A Formula of Landau and Mean Values of ζ(s)* (1985), Theorem 1:

<https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf>

It separates the first error as \(O(x\log(2x)\log\log(3x))+O(x\log(2T))\), and gives the other two terms as above with the last \(O(\min(\log T/\log x,T\log T))\). That paper says detailed proofs will appear elsewhere. Its more precise split is useful, but **none of the conclusions proved here relies on that refinement**: the fully readable standard form (1) suffices. The later detailed reference is Gonek, *An explicit formula of Landau and its applications to the theory of the zeta-function*, Contemp. Math. **143** (1993), 395–413.

## 2. Exact rational main term and complete uniform scalar bound

Let \(1\le m<n\le X\), \(X\ge2\), \(x=n/m\), and define

\[
\lambda_{\rm rat}(n,m)=
\begin{cases}\Lambda(n/m),&m\mid n,\\0,&m\nmid n.\end{cases}
\]

The exact centered residual is

\[
E_{nm}(T):=\sum_{0<\gamma\le T}m(\rho)
 \exp\!\left(\log(n/m)(\rho-1/2)\right)
+\frac{T\lambda_{\rm rat}(n,m)}{2\pi\sqrt{n/m}}.\tag{2}
\]

Thus the signed main term in the centered sum is negative. There is no replacement by an absolute-value main term, no selection of only prime frequencies, and no change in the zero set or normalization.

For every eligible prime power \(k\ne x\), the nonzero integer \(n-mk\) has absolute value at least one. Therefore \(\delta(n/m)\ge1/m\), even if \(x\) itself is a prime power, because that exact point is excluded. Also

\[
\log(n/m)\ge\frac{n-m}{n},\qquad
\frac1{\sqrt{n/m}\log(n/m)}
\le\frac{\sqrt{nm}}{n-m}.\tag{3}
\]

Dividing (1) by \(\sqrt{x}\) gives the uniform, more informative bound

\[
|E_{nm}(T)|\le C_0\left[
\sqrt{x}\log(2xT)\log\log(3x)
+\sqrt{nm}\log x
+\frac{\sqrt{nm}}{n-m}\log(2T)\right].\tag{4}
\]

The function \(\log\log(3X)/\sqrt X\) is bounded for \(X\ge2\). Since \(x\le X\), \(\sqrt{nm}\le X\), \(n-m\ge1\), and \(\log(2X),\log(2T)\le\log(2XT)\), (4) proves

\[
\boxed{\ |E_{nm}(T)|\le C X\log(2XT)
\quad(T>1,\ 1\le m<n\le X),\ }\tag{5}
\]

for one absolute \(C\). Quantifiers are uniform in all three parameters; they permit \(X=X(T)\). No reduced-fraction hypothesis is necessary.

## 3. Preserve the actual matrix identity before estimating

For an integer \(d\ge1\), use every frequency \(\log n\), \(1\le n\le d\). Put

\[
N(T)=\sum_{0<\gamma\le T}m(\rho),\qquad
M_{nm}(T)=\sum_{0<\gamma\le T}m(\rho)
 \exp\!\left((\log n-\log m)(\rho-1/2)\right).
\]

The all-integer arithmetic matrix has zero diagonal and

\[
(C_d)_{nm}=
\begin{cases}
\Lambda(n/m)/\sqrt{n/m},&m\mid n,\ n>m,\\
\Lambda(m/n)/\sqrt{m/n},&n\mid m,\ m>n,\\
0,&\text{otherwise}.
\end{cases}
\]

It retains the interactions through every composite integer frequency. It is not a direct sum indexed only by primes.

Define the actual residual matrix, without estimating it, by

\[
\mathcal E_d(T):=M(T)-N(T)I+\frac{T}{2\pi}C_d.\tag{6}
\]

For \(n>m\), its entry is precisely (2), and its diagonal is zero. Positive-height reflection \(\rho\mapsto1-\overline\rho\) preserves analytic multiplicity and exchanges horizontal displacement \(a\) with \(-a\). Consequently \(M_{mn}=\overline{M_{nm}}\), so the other triangle consists of conjugate entries. This uses the correct positive-height reflection; \(\rho\mapsto1-\rho\) changes the sign of the height.

Identity (6) holds for every \(T>1\), including cutoffs with \(N(T)=0\). Only after assuming \(N(T)>0\) define \(H=M/N(T)\) and obtain

\[
\boxed{\ H(T)=I-\frac{T}{2\pi N(T)}C_d+
\frac{\mathcal E_d(T)}{N(T)}.\ }\tag{7}
\]

Every operator norm below is the Euclidean norm on \(\mathbb C^d\), corresponding to the repository's `EuclideanSpace ℂ (Fin d)` after reindexing. Formula (7) retains the original count \(N(T)\).

## 4. A stronger resonance norm: \(O(d^{3/2})\)

Define the integer residue distance

\[
r_m(n)=\begin{cases}
m,&m\mid n,\\
\min\{n\bmod m,\ m-(n\bmod m)\},&m\nmid n.
\end{cases}
\]

If \(n/m\) is nonintegral, every integer is at distance at least \(r_m(n)/m\). If it is integral, every distinct integer is at distance at least one, which is the same bound with \(r_m(n)=m\). Therefore the source's excluded-prime-power convention gives

\[
\delta(n/m)\ge r_m(n)/m.\tag{8}
\]

The centered nearest-prime-power error is consequently bounded by the symmetric nonnegative matrix \(P\), with diagonal zero and, for \(n>m\),

\[
P_{nm}=\frac{\sqrt{nm}\log(n/m)}{r_m(n)}.
\]

The elementary inequality \(\log^2 x\le4\sqrt x\) for \(x\ge1\) follows by writing \(y=\log x\): the maximum of \(y^2e^{-y/2}\) is \(16/e^2<4\). Hence

\[
P_{nm}^2\le\frac{4n^{3/2}m^{1/2}}{r_m(n)^2}.\tag{9}
\]

In one complete residue block modulo \(m\), the reciprocal-square budget is

\[
\frac1{m^2}+\sum_{r=1}^{m-1}\frac1{\min(r,m-r)^2}
\le1+2\sum_{j=1}^{\infty}\frac1{j^2}\le5.\tag{10}
\]

The last inequality uses the integral comparison \(\sum_{j\ge1}j^{-2}\le2\). It also covers \(m=1\), where the budget is exactly one. Among the integers \(m<n\le d\), each nonzero residue \(r\) occurs \(\lfloor(d-r)/m\rfloor\) times and residue zero occurs \(\lfloor d/m\rfloor-1\) times; in particular each occurs at most \(d/m\). Thus

\[
\sum_{m<n\le d}\frac1{r_m(n)^2}\le\frac{5d}{m}.
\]

Use (9), symmetry, and \(\sum_{m=1}^dm^{-1/2}\le2\sqrt d\):

\[
\begin{aligned}
\|P\|_{\rm HS}^2
&=2\sum_{m<n\le d}P_{nm}^2\\
&\le40d^{5/2}\sum_{m=1}^dm^{-1/2}
\le80d^3.
\end{aligned}
\]

Therefore

\[
\boxed{\ \|P\|\le\sqrt{80}\,d^{3/2}.\ }\tag{11}
\]

This bound uses no information about prime-power distribution and no cancellation. It includes \(1<x<2\), exact resonance, and all unreduced rational representations.

## 5. Complete operator error from the standard source formula

Let \(H_d=\sum_{j=1}^d1/j\). Majorize the three errors in (1) entrywise, symmetrically, with zero diagonal. An entrywise nonnegative majorant controls the complex Euclidean operator: for unit vectors \(v,w\), estimate \(|\langle w,\mathcal E v\rangle|\) by the corresponding form in \(|w|,|v|\), then take the supremum. Thus scalar big-O terms need not be assigned an artificial signed matrix decomposition.

**First source error.** Split \(\log(2xT)=\log(2x)+\log T\). For \(x\ge1\),

\[
\log(2x)\log\log(3x)\le9\sqrt x.
\]

Indeed, with \(u=\log x\ge0\), the product is at most \((u+1)(u+2)\); use \(u^2\le4e^{u/2}\), \(u\le e^{u/2}\), and \(1\le e^{u/2}\). The centered T-independent majorant is at most \(9x=9n/m\). Its symmetric Frobenius norm is at most \(18d^{3/2}\), since

\[
2\sum_{m<n\le d}(n/m)^2
\le2\sum_{m\ge1}m^{-2}\sum_{n=1}^dn^2\le4d^3.
\]

For the T-dependent part, the symmetric matrix \(A_{nm}=\sqrt{\max(n,m)/\min(n,m)}\) off the diagonal satisfies

\[
\|A\|_{\rm HS}^2=2\sum_{n=2}^dnH_{n-1}
\le d(d+1)H_d\le2d^2H_d.
\]

Furthermore \(\log\log(3d)\le2\sqrt{H_d}\): use \(\log y\le\sqrt y\), \(\log d\le H_d\), \(H_d\ge1\), and \(1+\log3<4\). This part therefore has norm at most \(2\sqrt2\,dH_d\log T\).

**Second source error.** Equation (11) gives at most \(\sqrt{80}\,d^{3/2}\).

**Third source error.** Equation (3) majorizes it by \(\log(2T)\) times the symmetric matrix \(Q_{nm}=\sqrt{nm}/|n-m|\) off the diagonal. Every absolute row sum is at most

\[
d\sum_{m\ne n}|n-m|^{-1}\le2dH_d.
\]

The symmetric Schur bound gives \(\|Q\|\le2dH_d\).

Combining these three estimates with the common absolute constant \(C_0\) yields the useful explicit relative constant formulation

\[
\boxed{\ \|\mathcal E_d(T)\|
\le C_0\left(27d^{3/2}+5dH_d\log(2T)\right)
\quad(d\ge1,\ T>1).\ }\tag{12}
\]

Here \(18+\sqrt{80}<27\), \(2\sqrt2+2<5\), and \(\log T\le\log(2T)\). The original source constant remains unspecified; 27 and 5 are not claims about an explicit numerical Gonek constant.

For \(N(T)>0\), the **normalized residual** in (7) is exactly \(R=\mathcal E/N(T)\), and

\[
\boxed{\ \|R\|\le\frac{C_0}{N(T)}
\left(27d^{3/2}+5dH_d\log(2T)\right).\ }\tag{13}
\]

Use the checked full-integer arithmetic bound \(\|C_d\|\le\log d+\log4+4\) to obtain

\[
\boxed{\ \|H-I\|\le
\frac{T}{2\pi N(T)}(\log d+\log4+4)
+\frac{C_0}{N(T)}\left(27d^{3/2}+5dH_d\log(2T)\right).\ }\tag{14}
\]

Actual Riemann–von Mangoldt gives \(N(T)\sim T\log T/(2\pi)\). Since \(H_d\le1+\log d\), the asymptotic error is

\[
\|R\|\ll\frac{d^{3/2}}{T\log T}+\frac{d\log(2d)}{T}.
\tag{15}
\]

In particular both terms tend to zero for \(\log d=O(\sqrt{\log T})\); indeed they are exponentially small in \(\log T\) at that scale. The main arithmetic term is \(O(\log d/\log T)\). A sufficient larger pure-Landau regime is simultaneously \(d^{3/2}=o(T\log T)\) and \(d\log(2d)=o(T)\); no density or frame conclusion for that larger regime is asserted here.

## 6. Complete formal sufficient bound and sharper remaining targets

Analysis/ActualUniformRationalLandau.lean now proves, uniformly for T>=9 and 1<=m<n<=X,

\[
|E_{nm}(T)|\le C\left[X^{5/2}+X^{3/2}\log^2(T+3)+X\log(T+3)\right].
\]

The checked declarations are `exists_uniform_rational_landau_bound`, `exists_uniform_rational_landau_rpow_bound` and `rationalLandauMain_eq_vonMangoldt_div_sqrt`. They assume no analytic Landau or density estimate. The full signed contour identity retains the low sum, both horizontal sides, complete upward left side, full right nonresonant series, the window S_B-S_T, and +(A+T-B)*main. The chosen A lies in [8,9], B in [T,T+2], so the correction factor lies in [6,9]. Multiplicities and zeros exactly at the cutoff T are retained.

The actual fixed left, full-strip horizontal and arbitrary-height estimates are supplied by ActualLandauLeftLine.lean, ActualZetaGoodLandauHorizontals.lean and ActualZeroHeightTransfer.lean. With the original N(T) normalization, the elementary d-times-max-entry operator estimate gives a remainder of order

\[
\frac{d^{7/2}}{T\log T}+\frac{d^{5/2}\log T}{T}+\frac{d^2}{T}.
\]

It tends to zero at log d=O(sqrt(log T)). This consequence and the asymptotic operator assembly are mathematical deductions; this module certifies the scalar provider, not a new asymptotic frame theorem. The sharper (1), (5) and (12) remain source-derived bounds, including their unspecified absolute C_0.

### Infrastructure and gaps for the sharper variable-c route

The following checked providers support a direct contour proof, rather than adding (1) or (5) as a hypothesis equivalent to the desired conclusion.

| Source module | Existing actual declaration and scope |
|---|---|
| `Analysis/ActualZeroLandauContour.lean` | `RvM.rectangleIntegral'_mul_logDeriv_riemannZeta_eq_zero_sum`: differentiable entire weight, symmetric rectangle with \(c>1\), positive lower height, good endpoints; exact analytic multiplicities. Exponential specialization already proved. |
| `Analysis/ActualRationalLandauRightLine.lean` | `integral_centered_two_neg_logDeriv_eq_kernel_tsum`, `rightLandauLine_rational_eq_split`: exact Re=2 finite-interval series interchange, signed endpoints, integer resonance; no contour-side estimate supplied by this declaration. |
| `WeilEF/GoodHeights.lean` | `good_heights_at`: actual zero-free \(R\in[j,j+1]\), \(j\ge7\), simultaneous \(\pm R\) bound \(\|\zeta'/\zeta\|\le C\log^2(j+3)\) on \(1/2\le\Re s\le2\). |
| `RvM/LocalCount.lean` | `zetaZeroConfig_local_count`: actual multiplicity count of every unit ordinate window is at most \(A_0\log(|t|+3)\). |
| `XiPrime/Hardy/EFContour.lean` | `norm_logDeriv_Gammaℝ_le_strip`: \(-1/4\le\Re u\le2\), \(|\Im u|\ge2\), bound \(\log(|\Im u|+3)+6\). |
| `XiPrime/Hardy/TwoLine.lean` | `logDeriv_Gammaℝ_shift`: off the real axis, \(\Gamma_\mathbb R'/\Gamma_\mathbb R(u)=\Gamma_\mathbb R'/\Gamma_\mathbb R(u+2)-1/u\). |
| `GammaFacts/StirlingVert.lean` | `digamma_stirling`: for \(\Re w>0\), \(|\Im w|\ge1/2\), explicit remainder \(\|\psi(w)-\log w+1/(2w)\|\le3/(\Im w)^2\). |
| `XiPrime/Hardy/Basic.lean` | `zeta_eq_chiFE_mul`, `logDeriv_chiFE`: exact zeta functional equation off the real axis and \(\chi'/\chi=-\Gamma_\mathbb R'/\Gamma_\mathbb R(1-s)-\Gamma_\mathbb R'/\Gamma_\mathbb R(s)\). |

A convenient sharper contour choice is

\[
c(x)=1+\frac1{4+\log x},\qquad a(x)=1-c(x).
\]

Then \(1<c\le5/4\), \(-1/4\le a<0\), and \(x^c\le e x\). This matches the existing weighted symmetric rectangle and gamma strip bounds. Fix one bottom good height \(A\ge7\) once and for all, take \(T\ge A\), keep its entire finite low-zero sum exactly, and choose a top good height \(R\in[\lfloor T\rfloor+1,\lfloor T\rfloor+2]\). The ordinary oriented contour gives the exact signed identity

\[
S_R(x)-S_A(x)=\frac1{2\pi i}\left(
\int_a^c x^{\sigma+iA-1/2}\frac{\zeta'}\zeta(\sigma+iA)d\sigma
+i\int_A^R x^{c+it-1/2}\frac{\zeta'}\zeta(c+it)dt
-\int_a^c x^{\sigma+iR-1/2}\frac{\zeta'}\zeta(\sigma+iR)d\sigma
-i\int_A^R x^{a+it-1/2}\frac{\zeta'}\zeta(a+it)dt\right).\tag{16}
\]

The right-side series contains exactly

\[
-\frac{x^{c-1/2}}{2\pi}\sum_{k\ge2}\frac{\Lambda(k)}{k^c}
K_{A,R}(\log x-\log k),\quad
K_{A,R}(u)=\int_A^R e^{iut}dt.
\]

Its exact resonance is \(-(R-A)\Lambda(x)/(2\pi\sqrt x)\). The proof should keep all four signed sides, this resonance, \(S_A\), and the exact \(S_T-S_R\) window correction before applying norms.

For the sharper variable-c route, the following results remain to be formalized or exported. The fixed-c=2 horizontal, left-line and height-transfer cases have already been discharged:

1. **General-c finite-line interchange.** Extend the checked Re=2 proof to \(c>1\), using the existing `LSeriesSummable_vonMangoldt`. The exact identity has \(x^{c-1/2}\Lambda(k)k^{-c}K\), not the square coefficients.
2. **Whole-strip good-height bound — now proved.** `Analysis/ActualZetaGoodLandauHorizontals.lean` proves the full actual [-1,2] norm and weighted horizontal estimate. On \(a\le\sigma\le c\), reflect the completed logarithmic derivative and subtract the actual gamma terms. The listed good-height and gamma bounds give \(\|\zeta'/\zeta\|\ll\log^2(R+3)\), uniformly in \(c\le5/4\).
3. **Right-line rational nonresonance bound.** For \(c=c(x)\), split integers into \(k\notin(x/2,2x)\) and \(k\in(x/2,2x)\), excluding exact integer resonance. The far sum uses \(\Lambda(k)\le\log k\) and \(\sum_{k\ge2}\log k/k^{1+\varepsilon}\ll\varepsilon^{-2}\). The near sum uses \(1/|\log(x/k)|\le2x/|x-k|\) and \(\sum_{x/2<k<2x,k\ne x}|x-k|^{-1}\ll m+\log(2x)\). This proves centered error \(O(\sqrt x\log^2(3x)+\sqrt{nm}\log(2x))\) without nearest-prime-power selection.
4. **Left-line archimedean phase bound.** `Analysis/ActualLandauLeftLine.lean` now proves the full fixed c=2 complex chi remainder <=6/t, exact finite oscillatory chi decomposition, reflected actual zeta series and signed left-line split/norm. The sharper variable-c version below remains a separate obligation. Use the exact functional equation, the reflected actual Dirichlet series (frequencies \(\log x+\log k\ge\log2\)), and the gamma shift. The explicit Stirling remainder is absolutely integrable. Integrate the main \(\log(\alpha\pm it/2)\) term by parts; its derivative is \(O(1/t)\). Rational reciprocal terms can likewise be integrated by parts. The centered left error is \(O(\log^2(3x)/\sqrt x+\log(R+3)/(\sqrt x\log x)+1/\sqrt x)\), uniformly in \(c\). No unproved trigamma estimate is needed.
5. **Low-height and arbitrary-height transfer (established).** ActualZeroHeightTransfer.lean and ActualUniformRationalLandau.lean supply these actual bounds with both endpoints retained. `Analysis/ActualZeroHeightTransfer.lean` now proves the exact complete window increment and its sharper `cosh(|u|/2)*Ncount T R` bound, followed by the actual logarithmic short-height bound. The actual finite low sum is \(O(\sqrt x)\) with a fixed constant depending on \(A\). The actual local count gives \(|S_R-S_T|\le\sqrt x\,N(T,R]\ll\sqrt x\log(T+4)\) when \(R-T\le2\). The main-term endpoint change is retained and bounded separately.

Combining these yields a complete sufficient direct rational contour estimate of FZ size, \(O(\sqrt x\log^2(2xT)+\sqrt{nm}\log(2x)+\log(2T)/(\sqrt x\log x))\). This is weaker than the published Gonek bound used for (12), but already sufficient for the requested square-root-log support. The elementary modular HS bounds in Sections 4–5 are separate finite arithmetic obligations. The analytic formalization gap is substantive: the existing right line alone does not certify (1), (5), or (12).

## 7. Independent density audit

`ActualZeroDensityProviderProof20261005.md` was independently checked against Chourasiya–Simonič arXiv:2507.15184v2, Theorem 1, Table 1, and the proof of Corollary 1:

<https://arxiv.org/html/2507.15184v2>

There is no material error in its finite-count retention or uniform moving-endpoint argument. For each \(\sigma>1/2+d/\log T\), choose an admissible lower endpoint between that threshold and \(\sigma\); the paper explicitly states all five parameter functions decrease in this endpoint, so their values at \(1/2\) are uniform upper bounds. The small omitted interval is covered by actual Riemann–von Mangoldt, not a finite RH certificate. The retained \(N(\sigma,H)\le N(H)\) is fixed uniformly in \(\sigma\).

The near-line coefficient \(10.138+\varepsilon\) is therefore an eventual deduction. The full-strip coefficient 44 is valid: for \(s\le3/8\) the main term has uniform minimum \(T^{1/3}(\log T)^{7/3}\), which absorbs the fixed finite count and additive logarithms. For \(s>3/8\), monotonicity clamps the nonlinear rate at \(2/3\), which is still at least \(4s/3\) for \(s\le1/2\). This certifies the paper-level deduction, not a Lean proof of the density theorem's mollifier, fourth-moment, Gabriel, or Littlewood inputs.

Wolfram independently checked the rational logarithm inequality, the \(\log^2x\) growth bound, sample modular HS budgets, and the algebraic density exponent identities. Those checks are auxiliary symbolic/numerical validation; no Wolfram computation is presented as Lean kernel verification or a proof of an actual zeta analytic input.
