# Mollifier provider continuation and first-moment refinement

Date: 2026-10-05. Base: 2a903f2531e2efb83c8fc8749db4b546a5e414fa.
Workspace: ws_HMctPKpwVDzbK7S9X1YNddHPFfNlpe3C.

## Scope and verification boundary

The preceding checkpoint already proves compatible logarithm lifts, the complete
Littlewood rectangle identity, actual detector orders, inclusion of the zeta
window in the full finite detector divisor, and outward zero-free rectangles.
Their domain conditions remain visible. This continuation does not add a
source theorem as a Lean axiom.

New kernel proofs:
- Real.log_one_add_sq_le_self_of_nonneg
- Real.log_one_add_sq_le_rpow
- Complex.log_norm_one_sub_sq_le_rpow
- Complex.integral_log_norm_one_sub_sq_le_rpow

All seven new declarations passed an axiom audit with only propext,
Classical.choice, Quot.sound (job_iZtti1BANthRrc2DCXNZmgamUmJU6D1H).
The actual application adds
zetaDetector_left_log_integral_le_moment,
signedLeftRectangleBudget_of_moment_and_horizontal, and
densityDifference_le_of_expandedLeftRectangleBudget_sharpRight.
The last two are conditional reductions, with concrete moment/horizontal
or signed-left inputs in their exact declaration types.

Still Open in Lean: the cited near-line moments, Gabriel interpolation,
compatible horizontal argument estimate, the new integrated-log series
interchange, and their assembled unconditional provider. The paper arguments
below discharge these estimates using published unconditional analytic
theorems, but do not claim their full kernel formalization.

## Signed cancellation gives a height-independent right bound

For integer X>=37 and all real H<=T, put e_X=zeta*M_X-1 and h_X=1-e_X^2.
In Re(s)>1, the exact Dirichlet coefficients are
b_X(n)=sum_{d|n,d<=X} mu(d) for n>1, with b_X(1)=0. Thus b_X(n)=0
for n<=X, and for n>X,
b_X(n)=-sum_{d|n,d>X} mu(d).
Absolute convolution and the p-series integral test imply

    A_X=sum_{n>X}|b_X(n)| n^(-3/2)
       <= zeta(3/2) sum_{d>X} d^(-3/2) <=6/sqrt X.

Let r=36/X<1 and c_k be the 2k-fold Dirichlet convolution of b_X.
Its support lies in n>=(X+1)^(2k), and
sum_n |c_k(n)| n^(-3/2)<=A_X^(2k)<=r^k. Consequently the analytic
principal logarithm has the uniformly absolutely convergent expansion

    Log h_X(3/2+it)=-sum_{k>=1} (1/k) sum_n c_k(n) n^(-3/2-it).

For any finite interval, absolute uniform convergence permits the interchange
with the integral. Integrate the individual nonzero frequencies BEFORE
taking absolute values:

    |integral_H^T exp(-it log n) dt| <=2/log n
      <=1/(k log(X+1)).

Therefore

    |integral_H^T Log h_X(3/2+it) dt|
       <=Li_2(36/X)/log(X+1)
       <=[-log(1-36/X)]/log(X+1) <=1.

The last inequality uses X/(X-36)<=X<X+1. Since
Re(Log h_X)=log|h_X|, the absolute value of the real signed logarithmic
integral obeys the same bound. No T/X growth premise, moment theorem or
finite-height RH certificate is used.

This strengthens the previous pointwise right estimate. Its full
Dirichlet-series formalization remains Open; it is not silently substituted
into the checked finite theorem.

## Source constants and boundary conventions

Keep the original integer X fixed when perturbing a rectangle. Choose H>H_0>=1002,
and make the outward lower perturbation satisfy H_0<H'<H.
For X=ceil(T)+37, choose T<T'<T+1 and
sigma-alpha' between eta/log T and 2eta/log T, with alpha'>1/2.
Then T'<=X<=2T' eventually; all source moment constants below are uniform.
Apply the estimates at T',alpha',H' rather than replacing X by ceil(T')+37.
The resulting extra constant is bounded (for example, increase the
left-shift factor from exp(4eta) to exp(8eta), and the source horizontal
parameter bound from eta to 4eta). Thus an actual finite outward rectangle
satisfies the same profile with a larger FIXED constant. For
p_delta=1-delta/(1-delta) in [0,1], T'<=T+1 and T>=2 imply
T'^p_delta log T'<=4 T^p_delta log T, which is absorbed into that constant.
Continue the top and bottom arguments horizontally from the principal log
on Re(s)=3/2; this is the compatible branch aggregate used by Littlewood.

The exact strict-tail identity stays
strictTail(T,delta)=2(D(T,1/2+delta)-J(T,1/2+delta)).
A window bound D(T,sigma)-D(H,sigma)<=F yields exactly
strictTail<=2(F+D(H,sigma)-J(T,sigma)).
The initial count is retained; no finite-height RH assertion removes it.
The complete actual signed operators still contain both exponential
channels, the negative sinh square, all composite coordinates and analytic
multiplicities, and use the original N(T).

## First-moment refinement


Let
\[
M_X(s)=\sum_{n\leq X}\mu(n)n^{-s},\quad f_X(s)=\zeta(s)M_X(s)-1,
\quad h_X(s)=1-f_X(s)^2.
\]
The argument below estimates the actual detector, including its additional zeros. It does not infer a detector estimate from a zeta zero-count estimate.

Fix \(q,\kappa,\eta>0\), \(H_0\geq1002\), and
\[
T_*\geq\max(3\cdot10^{10},e^e,e^{8\eta},e^{20q}),\quad
L_*=\log T_*,\quad D=1+\frac{\log2}{L_*}.
\]
Assume \(T\geq T_*\), \(H_0\leq H\leq T\), and \(T\leq X\leq2T\). In particular this includes \(X=\lceil T\rceil+37\). Put \(L=\log T\).

## Rigorous constants for the critical-line Gaussian envelope

Set \(B=2000\) and
\[
A=1+\frac{13.803}{B^{1/4}\sqrt{\log B}}+
\frac{83.964}{\sqrt B}+\frac{2000}{B}+
\frac{3691.24}{B\log B}.
\]
Simonič, arXiv:1910.08274v2, Corollary 5, equation (38), implies for every \(V\geq0\)
\[
\mathcal M_1(V):=\int_0^V|\zeta(1/2+it)|^2dt
\leq A(V+B)\log(V+B).
\]
For \(V\geq B\), discard the negative linear main term and replace \(\log(V/(2\pi))\) by \(\log V\). Divide the four remaining error terms by \(V\log V\); each ratio is decreasing for \(V\geq B\). This gives \(\mathcal M_1(V)\leq AV\log V\). For \(V\leq B\), monotonicity gives \(\mathcal M_1(V)\leq\mathcal M_1(B)\leq AB\log B\).

Define
\[
m_0=\sqrt{1+\frac23\sqrt{\frac65}},\quad
c_1=\frac6{\pi^2}+\frac{1.048}{L_*},\quad
c_2=\frac{0.62\pi m_0}{L_*}+\frac{6m_0}{\pi T_*}+
\frac{1.048\pi m_0}{T_*L_*}.
\]
Chourasiya–Simonič, arXiv:2507.15184v2, Lemma 5, gives
\[
\int_0^V|M_X(1/2+it)|^2dt\leq(c_1V+c_2X)\log X.
\]
Set
\[
E=1+\frac{\log B}{L_*}+\frac1{BL_*},
\]
\[
K_c=\sqrt{2AD(1+B/T_*)E(c_1+2c_2)}
\left(1+\kappa^{-3/4}\Gamma(7/4)\right)
+\frac{\Gamma(3/2)}{\sqrt\kappa L_*}.
\]
For \(v=\sqrt{u/\kappa}\), \(V=Tv\), Cauchy–Schwarz gives
\[
\int_0^V|f_X(1/2+it)|dt
\leq\sqrt{\mathcal M_1(V)\int_0^V|M_X(1/2+it)|^2dt}+V.
\]
Since
\[
V+B\leq T(1+B/T_*)(1+v),\quad
\log(V+B)\leq LE(1+v),
\]
\[
\int_0^V|M_X(1/2+it)|^2dt
\leq TDL(c_1+2c_2)(1+v),
\]
the integrand is at most
\[
TL\sqrt{AD(1+B/T_*)E(c_1+2c_2)}(1+v)^{3/2}+Tv.
\]
Integrating against \(e^{-u}du\), using
\((1+v)^{3/2}\leq\sqrt2(1+v^{3/2})\), proves the finite, uniform bound
\[
\int_0^\infty e^{-u}
\int_0^{T\sqrt{u/\kappa}}|f_X(1/2+it)|dt\,du\leq K_cTL.
\tag{A}
\]

## Right-of-one Gaussian envelope

Let \(\beta=1+q/\log X\) and
\[
r_3=\frac{0.54\pi m_0}{2q}e^{2q\gamma/L_*},\quad
r_4=\frac{0.54}{5qe^q}+\frac{0.605e^{-2q}}{L_*},
\]
\[
K_r=D\left[r_3+r_4\left(\frac{\Gamma(3/2)}{\sqrt{2\kappa}}+
\frac{\pi m_0}{T_*}\right)\right].
\]
Lemma 6 of Chourasiya–Simonič, with \(X_0=T_*\), implies
\[
\int_0^\infty e^{-u}
\int_0^{T\sqrt{u/(2\kappa)}}|f_X(\beta+it)|^2dt\,du\leq K_rL.
\tag{B}
\]
Indeed its second-moment bound is
\((r_3+r_4(V+\pi m_0)/X)\log X\); use \(T/X\leq1\), \(1/X\leq1/T_*\), and \(\log X\leq DL\). All parameters satisfy the source conditions because \(q\leq L_*/20\).

## Interpolation and the exact rate

Define
\[
E_0=\frac{\exp\{\kappa[1+((1+2q/L_*)/(4T_*))^2]\}}
{1-H_0^{-1}}.
\]
Use Chourasiya–Simonič Corollary 6 with strip endpoints \(1/2,\beta\), \(\lambda=1\), \(\mu=1/2\), and \(A=0\). For \(s\in[1/2,1]\), define
\[
w_1=\frac{\beta-s}{\beta-1/2},\quad
w_2=\frac{s-1/2}{\beta-1/2},\quad w=w_1+\frac12w_2.
\]
Then \(1/2\leq w\leq1\), and (A)–(B) yield
\[
\int_H^T|f_X(s+it)|^{1/w}dt
\leq E_0^2\max(K_c,K_r)T^{a(s,e)}L,
\]
where \(e=q/\log X\) and
\[
a(s,e)=\frac{2(1-s+e)}{3/2-s+2e}.
\]
For every \(x\geq0\), \(\log(1+x^2)\leq x\): the derivative of \(x-\log(1+x^2)\) equals \((x-1)^2/(1+x^2)\). Consequently \(\log(1+x^2)\leq x^p\) for every \(1\leq p\leq2\), by splitting at \(x=1\). Thus
\[
\log|h_X(s+it)|\leq |f_X(s+it)|^{1/w}.
\]
Here classical \(\log0=-\infty\) is used at isolated zeros, which do not alter Lebesgue integrals; for an ordinary real-valued integrand one can redefine those finitely many points.

Writing \(u=s-1/2\) and \(I_1(s)=2(1-s)/(3/2-s)\),
\[
a(s,e)-I_1(s)=\frac{2eu}{(1-u)(1-u+2e)}\leq4e,
\]
so
\[
\int_H^T\log|h_X(s+it)|dt
\leq E_0^2\max(K_c,K_r)e^{4q}TL
\exp\left(-L\frac{u}{1-u}\right).
\tag{C}
\]
This is a detector-specific bound, not an estimate merely for zeta zeros.

## Leftward shift and horizontal edges

For \(\eta/L<\delta\leq1/2\), set \(\sigma=1/2+\delta\) and \(\alpha=\sigma-\eta/L\). The exact shift identity is
\[
\frac{\delta}{1-\delta}-\frac{\delta-\eta/L}{1-\delta+\eta/L}
=\frac{\eta}{L(1-\delta)(1-\delta+\eta/L)}\leq\frac{4\eta}{L}.
\]
Hence the left-edge bound costs only \(e^{4\eta}\). Lemma 8 of Chourasiya–Simonič bounds the signed horizontal difference in modulus by \(C_aL\), where
\[
C_a=(1+\eta/L_*)\left[\frac{C_6(T_*,H_0)}{L_*}
+\frac4{\log2}+\frac{3\pi D}{\log2}\right]
\]
and \(C_6\) is the source's exact equation (34) expression. Its variable-dependent pieces decrease for \(X\geq T_*\), as follows by differentiating
\(9(\log X+2+\gamma+7/(36X))^2/X\). Since
\[
TL\exp\left(-L\frac\delta{1-\delta}\right)\geq L,
\]
the horizontal term is absorbed. Thus, for safe rectangles,
\[
\boxed{\text{LEFT}+\text{HORIZONTAL}\leq
\left[E_0^2\max(K_c,K_r)e^{4(q+\eta)}+C_a\right]
TL\exp\left(-L\frac\delta{1-\delta}\right).}
\]
The right vertical edge can be appended using the separate Lemma 7 estimate. Holding the original integer \(X\) fixed during outward endpoint perturbations is essential. For \(X=\lceil T\rceil+37\), perturbing the upper height within \(T<T'<T+37\) preserves \(1\leq X/T'\leq2\). For a finite outward rectangle use the enlarged constants and parameter choices specified above; the original count is bounded by its expanded window.

## Quantitative cutoff and comparisons

Littlewood division by \(2\pi(\sigma-\alpha)=2\pi\eta/L\), followed by \(N(T)\gg TL\), gives a normalized strict count bound
\[
C\,L\exp\left(-L\frac\delta{1-\delta}\right)
+O\left(\frac{N(H)}{TL}\right).
\]
For a multiplier \(W\geq1\), put
\[
S_1=\log W+\log L+\omega+\log C,
\qquad \delta_1=\frac{S_1}{L+S_1}.
\]
Then \(L\delta_1/(1-\delta_1)=S_1\), and the multiplied main term is exactly at most \(e^{-\omega}\). Require \(0<S_1\leq L\), and \(\delta_1L>\eta\); both hold eventually for common polylogarithmic \(W\) and an unbounded slowly growing \(\omega\).

The fourth-moment profile instead uses
\[
S_4=\log W+2\log L+\omega+\log C_4,\qquad
\delta_4=\frac{3S_4}{4(L+\log L)+2S_4}.
\]
If \(W=L^a\), \(\omega=o(\log L)\), the leading cutoff coefficients are \(a+1\) and \(3(a+2)/4\), respectively. The first-moment cutoff is smaller when \(a<2\). The explicit Selberg count estimate with exponent \(1/4\) yields leading cutoff coefficient \(4a\), smaller than \(a+1\) when \(a<1/3\). This last comparison concerns the actual zeta count; its Selberg mollifier differs from the present raw Möbius detector.

Sources: https://arxiv.org/html/2507.15184v2 (Corollary 6 and Lemmas 5–8); https://arxiv.org/html/1910.08274v2 (Corollary 5 and the explicit Selberg count theorem).

## Consequence and remaining RH obligation

Let W(T)=harmonicHyperbolicCap(d(T)), with log W(T)/log T ->0.
For the first-moment rate, take
S=log(C W(T) log T)+omega(T),
delta(T)=max(2eta/log T,S/(log T+S)),
where omega->infinity and omega/log T->0. Eventually S>0 and delta<=1/2.
The monotonicity of delta/(1-delta) preserves the exponentially small
majorant after imposing the source margin. The normalized harmonic tail,
actualSignedTailBudget and norm of signedBadHyperbolic all tend to zero.
The retained head term is O(W(T) N(H)/(T log T))->0.
This is an unconditional paper theorem using the explicitly cited
analytic results. The Lean theorem with no analytic premise remains Open.

For fixed or very slowly growing support, the explicit Selberg density
estimate is even more useful because it avoids the log-log penalty:
a retained-head version gives
rightStrictTail(T,delta)<=N(H_*)+C_S T log T exp(-delta log T/4)
uniformly for 0<=delta<=0.331. Choose
delta=4(log(C'_S W)+omega)/log T.
This shrinks under the same subpower support condition. This direct
zeta-count route uses a different Selberg mollifier and is not a proof of
a budget for the raw Mobius detector's additional zeros.

Shrinking normalized tails allow finitely many off-line zeros.
They do not prove RH. The fully screened physical Pareto transfer and
the actual inverse-Gram saturation criterion are still separate Open
obligations; no positivity or simplicity assumption is inserted.
