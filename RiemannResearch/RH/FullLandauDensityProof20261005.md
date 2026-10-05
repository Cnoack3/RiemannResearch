# Full Landau and density providers: rigorous deductions and Lean boundary

Research date: 5 October 2026. Source base: `0944f251e93d6725dbe82188e5bbb0b56d990584`.

The complete sufficient uniform rational Landau estimate is now proved in Lean from the actual zeta contour and its analytic providers. The sharper classical Landau–Gonek estimate and actual exponential zero-density theorem remain **Open in Lean**. The reports derive stronger mathematical bounds from those published unconditional theorems. No missing analytic input has been introduced as an axiom.

## Full rational Landau provider

Analysis/ActualUniformRationalLandau.lean proves an unconditional bound, uniformly for T>=9 and integers 1<=m<n<=X. It retains every actual zero with analytic multiplicity, the exact negative prime-power main term and every cutoff endpoint:

\[
\left|S_T(n/m)+\frac{T\lambda_{\rm rat}(n,m)}{2\pi\sqrt{n/m}}\right|
\le C\left[X^{5/2}+X^{3/2}\log^2(T+3)+X\log(T+3)\right].
\]

The main declaration is `exists_uniform_rational_landau_rpow_bound`; `rationalLandauMain_eq_vonMangoldt_div_sqrt` certifies its classical normalization. The constant is uniform in T, X, n and m. There is no assumed Landau or density bound. The proof first establishes the complete signed contour identity, including the fixed low-height sum and +(A+T-B)*main, then bounds all terms. The bound already suffices for the intended log X=O(sqrt(log T)) scale.

For the sharper source-derived estimates, see [ActualUniformRationalLandauProof20261005.md](ActualUniformRationalLandauProof20261005.md), Sections 1–5. For every real T>1 and integers 1<=m<n<=X, let x=n/m and let lambda_rat equal the von Mangoldt value of the integer quotient when m divides n, and zero otherwise. With every actual positive-height zero counted with analytic multiplicity,

\[
S_T(x)=\sum_{0<\gamma\le T}m(\rho)e^{\log x(\rho-1/2)},\qquad
E_{nm}=S_T(n/m)+\frac{T\lambda_{\rm rat}(n,m)}{2\pi\sqrt{n/m}}.
\]

There is an absolute C with |E_nm|<=CX log(2XT), uniformly in all three parameters. More strongly, for the complete d by d residual matrix and H_d=sum_{j=1}^d 1/j,

\[
\|\mathcal E_d(T)\|\le C_0\bigl(27d^{3/2}+5dH_d\log(2T)\bigr).
\]

Here C_0 is the absolute constant from the published uniform Landau–Gonek theorem, not a claimed explicit numerical constant. The exact identity is M=N I−T C_d/(2 pi)+E. For N>0, division gives H=I−T C_d/(2 pi N)+E/N. All composite integer interactions are retained. The stronger d^(3/2) error follows from an elementary modular reciprocal-square budget; it needs no prime-power distribution assumption.

## Actual uniform density provider

See [ActualZeroDensityProviderProof20261005.md](ActualZeroDensityProviderProof20261005.md), Sections 1–4. Write L=log T, P=L+log L, and B_>(T,s) for the actual strict multiplicity count |Re rho−1/2|>s. Reflection gives exactly twice the right strict count. The source theorem counts an inclusive right tail, so it bounds this strict tail without removing threshold zeros.

For all sufficiently large T, uniformly in 0<=s<=1/2,

\[
B_>(T,s)\le44TL^3e^{-(4/3)Ps}.
\]

On 0<=s<=1/32, the stronger actual provider is

\[
B_>(T,s)\le10.14TL^3e^{-P\phi(s)},\qquad
\phi(s)=\frac{4s}{3-2s}.
\]

Before absorption, every finite-height zero is retained explicitly through 2N(3*10^12), together with the additive 18.922L^2+335.6L. The source input is Theorem 1, not the corollary that discards a finite count using a computational RH certificate. The small interval s<=0.28/L is covered by unconditional Riemann–von Mangoldt. Hence the eventual statements are uniform even when s=s(T) shrinks to zero.

## Stronger cutoff and support consequences

The exact rate obeys

\[
\phi(s)=\frac43s+\frac{8s^2}{9-6s},\qquad
\phi(s)-\phi(\delta)-\frac{12(s-\delta)}{(3-2\delta)^2}
=\frac{24(s-\delta)^2}{(3-2\delta)^2(3-2s)}.
\]

For M=L+log L, ell=log d, R=ell+p log L and B=4M−3ell+2R, the stable cutoff

\[
\delta=\frac{6R}{B+\sqrt{B^2+24\ell R}}
\]

satisfies exactly M phi(delta)−ell delta=R under the ordinary positive-denominator conditions. Thus the density exponential cancels the dimension factor while keeping the stronger nonlinear gain. The Lean module NonlinearZeroDensityRate proves these scalar identities; it asserts no actual density theorem.

The exact finite cosh layer cake and original N normalization give the bad-operator estimate in the density report, with both endpoints retained. For ell=c sqrt L and c<sqrt((4/3) arcosh 2)=1.325120320033778..., the complete source-derived Landau estimate gives alpha=O(1/sqrt L), and the density cutoff with p>2 gives beta→0. Therefore the already checked finite norm bootstrap yields eventual phase-Gram conditioning at the mathematical level. A uniform positive gap follows because cosh(3c^2/4)<2.

The nonlinear rate does not increase this leading coefficient: phi(s)/s tends to 4/3. It does improve the next-order support budget. For a fixed good correction argument z<arcosh 2,

\[
\ell_{\max}=\sqrt{4z/3}\sqrt L-\frac p2\log L-\frac z6
+O((\log L)^2/\sqrt L),
\]

where the former linear-rate constant term was −z/2. The improvement is z/3 in logarithmic support. The same leading endpoint can also be reached with a subleading dimension loss as described in the density report, but then the spectral gap tends to zero.

## Formal verification status

The publication adds seven modules, including the complete actual uniform rational Landau provider and exact scalar cutoff algebra. The coherent source check passed in 11.529 seconds; all 24 principal axiom audits use only propext, Classical.choice and Quot.sound. The publication checkpoint validates separate imports and affected modules. A critical-line constant-fraction theorem gives a separate uniform actual tail bound; it does not supply shrinking-window exponential density.

The sufficient fixed-c=2 Landau obligation is discharged. The sharper classical Landau source theorem and actual Ingham/Selberg density theorem remain Open in Lean. Density still needs the actual analytic mean-value and Littlewood/Gabriel inputs. Reflection and layer cake alone do not prove that density estimate. The complete source-derived spectral consequence is not claimed as a new kernel-verified asymptotic theorem, and none of these phase-Gram results proves RH or supplies the screened physical Pareto inverse.

Primary sources:

- Gonek, *A Formula of Landau and Mean Values of ζ(s)* (1985), Theorem 1: https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf.
- Baluyot–Gonek, Pacific J. Math. 303 (2019), p.49, readable uniform Landau–Gonek statement: https://msp.org/pjm/2019/303-1/pjm-v303-n1-p02-s.pdf.
- Chourasiya–Simonič, arXiv:2507.15184v2, Theorem 1, Table 1 and proof of Corollary 1: https://arxiv.org/html/2507.15184v2.

Wolfram checked the exponent identities, exact tangent remainder and stable-root quadratic. These are auxiliary algebra checks; Lean verifies the formal declarations, and the published analytic theorems support the paper deductions.
