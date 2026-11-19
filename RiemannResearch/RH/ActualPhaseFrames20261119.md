# Sampling the ordinates of zeta zeros

Write $G_{T,d}$ for the ordinary phase Gram of $e^{i\gamma\log n}$, for $1\le n\le d$. Its normalizer $N(T)$ counts every analytic multiplicity at $0<\gamma\le T$. The reflected Landau operator $H_{T,d}$ includes horizontal displacement. Let $L=\log T$ and $\ell=\log L$.

| Quantity | Bound | Inputs and interpretation |
|---|---|---|
| Rank of $G_{T,d}$ | Full rank when $d-1+T\log(d)/(2\pi)<D(T)$ and $N(T)>0$ | $D(T)$ counts distinct positive ordinates. The proof uses Langer’s open-strip zero count for finite exponential sums. |
| Growing rank | Eventual full rank for $d\le T^b$, $0\le b<\kappa$ | The lower proportion $D(T)/N(T)\ge\kappa-o(1)$ and the actual Riemann–von Mangoldt normalization are sufficient. |
| Growing norm | $\lVert G_{T,d}-I\rVert \to0$ if $\log d=o(\sqrt L)$ | Kernel-proved Ingham tangent of slope $4/3$, the actual Landau residual, the prime-power operator and the signed bad correction. |
| Square-root rank | Eventual full rank for $\log d\le c\sqrt L$, $\cosh(3c^2/4)<2$ | The threshold is $c<1.3251203200337780188\ldots$. The estimate controls operator norms at the cutoff used in the proof. |
| Published RH-conditional comparison | $\lVert G_{T,d}-I\rVert \le b+o(1)$ for $d\le T^b$, $0\le b<1$, and $\lVert G_{T,d}-I\rVert \to0$ for $d=T^{o(1)}$ | Bui, Florea and Milinovich, Theorem 3.1, explicitly assume RH. This also supplies a lower frame bound $1-b-o(1)$. |

## Langer’s exact normalization

For a nonzero sum of $d$ exponentials with real frequencies between zero and $\log d$, the number of zeros in an open vertical strip of width $u$ is at most $d-1+u\log(d)/(2\pi)$. Removing zero coefficients and factoring out the lowest frequency preserves the zeros and can only decrease both terms. Applying the open-strip theorem at upper endpoint $T+\varepsilon$ and taking $\varepsilon\downarrow0$ gives the precise constant for the repository’s half-open cutoff.

A kernel vector of the true Gram yields a Dirichlet exponential sum vanishing at every distinct ordinate. Each sampled contribution to its quadratic form is nonnegative, and every zero in the cutoff has positive multiplicity. Two distinct critical-line zeros always have different ordinates. Distinct off-line zeros can share an ordinate, including reflected partners. The finite projection to the imaginary axis retains this distinction in Lean. The in-tree Montgomery–Taylor proportion gives $b<0.67250\ldots$ directly. The external ten-point critical-line certificate gives $b<0.67363928816\ldots$. The proposed distinct-ordinate construction gives $b<0.83449280$ under its explicit Gram transfer, Conrey stop-loss and numerical certificate premises. With the microscopic zero-excess premise it gives $b<0.83681964408\ldots$.

Langer, *On the zeros of exponential sums and integrals*, Bull. Amer. Math. Soc. 37 (1931), 213–239. Heittokangas et al. give the exact rectangle error in §2.3 of their review, with the coefficient and frequency conventions stated there. Nazarov gives the rotated open-strip version in Lemma 1.3. [Langer](https://doi.org/10.1090/S0002-9904-1931-05133-8) · [Heittokangas et al.](https://doi.org/10.1112/blms.12719) · [Nazarov](https://www.mathnet.ru/eng/aa397)

## Published discrete mean square under RH

Bui, Florea and Milinovich establish their discrete mean-square identity for arbitrary complex coefficients under RH. To compare its normalization to this Gram, set $a_n=\sqrt n\,v_n$. Their diagonal term is $N(T)\sum_n|v_n|^2$. Their prime cross term is the quadratic form of $-T P_d/(2\pi)$, where the off-diagonal matrix entries at integer prime powers $k$ are $\Lambda(k)/\sqrt k$. The printed remainder is $O(d\log^2(dT)\lVert v\rVert^2)$, uniformly in $v$. The individual estimates in its proof sharpen this to $O(d\log d\,\log(dT)\lVert v\rVert^2)$ for $d\ge2$. The second term uses $\sqrt{\log d}\log\log(3d)\ll\log d$. The third and fourth terms use $\log^2d$ and $\log d\log(2T)$, respectively. The Riemann–von Mangoldt normalization and $\lVert P_d\rVert \le\log d+O(1)$ therefore give

$$
\lVert G_{T,d}-I\rVert
\le (1+o(1))\frac{\log d+O(1)}{\log T}
+O\!\left(\frac{d\log d\,\log(dT)}{T\log T}\right).
$$

This comparison gives quantitative conditioning where the Langer argument gives full rank. The source equation is Theorem 3.1. Its upper-triangular reflected sum and arithmetic estimates apply to $H_{T,d}$ with the unconditional Gonek formula in Lemma 3.2. This extends the reflected residual to $d=o(T/\log T)$, including all powers strictly below one. The source mean square uses the complex zeros $\rho=1/2+i\gamma$, so its phase conversion uses RH. [Published theorem](https://doi.org/10.1112/blms.13092)

## Horizontal correction in growing dimension

For the copy at $a=\beta-1/2$, unitary diagonal phase factors leave the singular values of the matrix $C_{ij}=\cosh(a\log(i/j))-1$ unchanged. The normalized Frobenius-square limit for fixed $|a|<1/2$ is

$$
\lim_{d\to\infty}\frac{1}{(d+1)^2}\sum_{i,j\le d}C_{ij}^2
=\frac{6a^4}{(1-4a^2)(1-a^2)}.
$$

For a reference displacement $3/8$, this gives the exact Frobenius coefficient $\sqrt{6144/385}=3.99480181717\ldots$ as $d\to\infty$. For smaller references it approaches $\sqrt6$. A fourth horizontal moment controls the harmonic far contribution for every fixed polynomial dimension range. A cumulative critical-line fraction $\kappa$ gives the central second-moment coefficient $(9/4)(1-\kappa)$ on the scale $(\ell/L)^2$.

A weighted Schur estimate for the true operator uses $x=((d+1)/i)^\eta$, $\eta=10^{-7}$ and a positive weight $A x+B+C/x$. The three rational coefficients solve the continuum row equations with residual $x$. Finite power-sum averages converge, preserving the positive row margin. The rational coefficient $93969262079/50000000000=1.87938524158$ controls the per-copy central norm for sufficiently large dimension and every $|a|\le\eta$. The corresponding full correction satisfies

$$
\lVert H_{T,d}-G_{T,d}\rVert
\le\left(1.87938524158\,\frac94(1-\kappa)+\varepsilon\right)d(\ell/L)^2
$$

for sufficiently large $d,T$, uniformly in $d\le T^b$, with $b\ge0$ fixed. The normalization and the horizontal profile make these constants specific to the complete finite operator correction.

For comparison, the continuum quadratic kernel $(x-y)^2/2$ against the exponential probability measure on $[0,\infty)$ preserves the span of $1,x,x^2$. Its corresponding matrix has characteristic polynomial $z^3-3z-1$ and spectral radius $2\cos(\pi/9)=1.8793852415718167681\ldots$. Wolfram checked the rational Schur residual and strict weight positivity exactly. The numerical comparison pertains to the single-copy continuum model. The averaged zeta operator has additional signed cancellation.


An independent lower comparison uses the same Laurent weight in the continuum Rayleigh quotient. With $X=-\log u$ and $u$ uniform on $(0,1)$, write $W=Ae^{\eta X}+B+Ce^{-\eta X}$ and

$$
m(s)=\mathbb E[We^{sX}]
=\frac{A}{1-s-\eta}+\frac{B}{1-s}+\frac{C}{1-s+\eta}.
$$

The quadratic kernel gives $[m(0)m''(0)-m'(0)^2]/\mathbb E[W^2]$. All inputs are rational. The quotient exceeds $1.87938524157$, while the Schur upper coefficient is $1.87938524158$. This brackets the continuum quadratic comparison within $10^{-11}$ and quantifies the numerical room in the per-copy matrix estimate.

## Exact limiting single-copy operator at every reference displacement

For each fixed $0<a<1/2$, the single-copy continuum operator has rank three. In the ordered basis $(e^{ax},1,e^{-ax})$ for the exponential probability measure, its matrix is
$$
M_a=\begin{pmatrix}
1/2&1/[2(1+a)]&1/[2(1+2a)]\\
-1/(1-a)&-1&-1/(1+a)\\
1/[2(1-2a)]&1/[2(1-a)]&1/2
\end{pmatrix}.
$$
The finite kernel at frequencies $\log n$ has this same three-column factorization. Each matrix entry converges to the displayed integral after division by $d+1$, since its finite shifted power mean with exponent $s<1$ tends to $1/(1-s)$. The three eigenvalues consequently converge with multiplicity. A finite nonnegative symmetric kernel and its integral analogue have norm equal to their largest positive eigenvalue. This follows directly from $|\langle Cf,f\rangle|\le \langle C|f|,|f|\rangle$. For a smaller displacement $|s|\le a$, the pointwise inequality $\cosh(s y)-1\le (s/a)^2[\cosh(a y)-1]$ carries the coefficient uniformly to the entire central strip.

The sharp limiting coefficient for the single-copy operator on that strip is the largest real root $z(a)$ of
$$
z^3-\frac{3z}{(1-4a^2)(1-a^2)}
-\frac{1}{(1-4a^2)(1-a^2)^2}=0.
$$
The lower bound is attained in the limit by the reference displacement itself. The limiting strict rational Schur certificate controls all sufficiently large finite dimensions and lies within $8.14\times10^{-12}$ of the sharp value at $a=10^{-7}$. Wolfram and SymPy independently gave the cubic by exact symbolic computation.

| Reference $a$ | Sharp single-copy coefficient $z(a)$ |
|---|---|
| $3/8$ | $3.001714249896563340069ldots$ |
| $1/4$ | $2.224549218988302507786ldots$ |
| $1/8$ | $1.953054646559388494471ldots$ |
| $10^{-7}$ | $1.879385241571861778085ldots$ |
| $a\downarrow0$ | $2\cos(\pi/9)=1.879385241571816768108ldots$ |

The eigenvalue-continuity and single-copy optimality argument in this section is a paper derivation. The comparison for the zeta-averaged horizontal correction admits signed cancellation, and another mechanism could improve its leading coefficient.

## Verification scope

The focused Lean builds have checked the finite quadratic bound, the harmonic bound for the signed exceptional operator, the sub-square-root-dimension norm theorem, the square-root full-rank theorem and the exact finite Langer rank transfer. Langer's exponential-polynomial zero theorem is a scoped external assumption. The positive-ordinate cardinalities and their kernel implication are proved in Lean. The 83-percent distinct-ordinate improvements additionally have the named Gram-transfer and certificate premises described above.

The componentwise Bui error, Schur-certificate asymptotic and growing-dimension refinements have the analytical derivations recorded here. Their current Lean verification evidence, when available, is listed separately in the repository’s theorem catalog. The cubic for the exact continuum operator is independently checked symbolically.

## Uniform finite-dimensional sharp coefficient

The same sharp coefficient $z(a)$ bounds **every finite dimension**, with $d$ in place of $d+1$. Partition $(0,1)$ into $I_i=((i-1)/d,i/d)$ and let $U_i$ be uniform on $I_i$. The logarithmic bias
$$
b_i=\log(i/d)-\mathbb E\log U_i
=\int_0^1-\log(1-u/i)\,du
$$
decreases with $i$ by pointwise monotonicity, including the integrable first interval. Thus for $i>j$ the independent variables $U_i,U_j'$ satisfy $\mathbb E[\log U_i-\log U_j']\ge \log(i/j)\ge0$. Convexity of $\cosh$, its monotonicity on the positive axis and symmetry give, for all $i,j$,
$$
\cosh(a\log(i/j))-1\le
\mathbb E[\cosh(a\log(U_i/U_j'))-1].
$$
The matrix of the continuum operator compressed to the orthonormal step functions $\sqrt d\,\mathbf1_{I_i}$ is $d^{-1}$ times the matrix on the right. Both matrices are symmetric and entrywise nonnegative. For any complex vector $v$, replace it by its entrywise modulus in the quadratic form to obtain the norm comparison. Consequently for $0<a<1/2$, every $d\ge1$ and all $|s|\le a$,
$$
\big\|(\cosh(s\log(i/j))-1)_{1\le i,j\le d}\big\|\le d\,s^2 z(a).
$$
At $s=a$ the normalized norms converge to $z(a)$ by the three-dimensional factorization, so no smaller uniform coefficient is possible. The diagonal sample phases act by unitary conjugation and preserve this bound. In particular at $a=3/8$ the exact single-copy coefficient $3.00171424989656\ldots$ applies to every $d$, and near the critical line the sharp infimum is $2\cos(\pi/9)$. This proof uses a finite compression of the integral operator and has the paper-proof status of the preceding cubic calculation.
