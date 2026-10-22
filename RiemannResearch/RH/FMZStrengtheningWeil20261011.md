# Strengthened prime-torus FMZ and the exact remaining RH problem

2026-10-11. This note accompanies the strengthened RiemannResearch Lean development.

The finite-prime FMZ theorem now needs one weighted Fourier moment, rather than two. Its conventional sufficient decay condition is B > d + 1. The theorem remains conditional on the explicit Selberg provider in Lean; Selberg's density estimate is unconditional in the literature.

The quantitative estimates, exact Gram identities, growing-prime obstruction and Weil comparison below are proved on paper here. They are not additional checked Lean declarations. Wolfram verifies the displayed finite and rational identities; those checks supplement the proofs.

## 1. Literature and scope

- Ford, Meng and Zaharescu, “Simultaneous distribution of the fractional parts of Riemann zeta zeros,” Theorem 1 and Corollary 1.1, use Fourier decay B > d + 2. Remark 2 explicitly allows the possibility of larger test classes:
  https://arxiv.org/abs/1511.06814
- Ford and Zaharescu, “On the distribution of imaginary parts of zeros of the Riemann zeta function,” Lemmas 1–2, provide uniform Landau and classical Selberg inputs. Their one-dimensional test class is already broader than a simple decay threshold:
  https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf
- Maples and Rodgers, “Bootstrapped zero density estimates and a central limit theorem for the zeros of the zeta function,” Theorem 2.4, record the Selberg–Jutila density estimate with any fixed exponent a < 1. Theorem 2.1 gives the full explicit formula:
  https://arxiv.org/abs/1404.3080
- Burnol, “The Explicit Formula in simple terms,” section “Weil's positivity criterion and stochastic processes,” gives the compactly supported positivity criterion and an interpolation proof of its converse:
  https://arxiv.org/abs/math/9810169

No mathematical novelty or optimal regularity claim is made. The refinement concerns prime-logarithm frequencies, including their reduced rational representations; it is not a theorem for every vector of real frequencies.

## 2. Exact reflection and density endpoints

Every sum retains analytic multiplicity. Write

\[
\delta_\rho=\beta_\rho-\tfrac12,\quad
Z_T(u)=\sum_{0<\gamma_\rho\le T}m_\rho e^{iu\gamma_\rho},\quad
L_T(u)=\sum_{0<\gamma_\rho\le T}m_\rho
 e^{u\delta_\rho+iu\gamma_\rho}.
\]

Reflection across the critical line preserves height and multiplicity. Therefore the exact equality is

\[
L_T(u)-Z_T(u)
 =\sum_{0<\gamma_\rho\le T}m_\rho e^{iu\gamma_\rho}
    \bigl(\cosh(u\delta_\rho)-1\bigr).
\]

It is essential that reflection occurs before an absolute value is taken. Let

\[
D_T(v)=\sum_{\substack{0<\gamma_\rho\le T\\|\delta_\rho|\ge v}}m_\rho,
\qquad
C_T(u)=\sum_{0<\gamma_\rho\le T}m_\rho
  \bigl(\cosh(u\delta_\rho)-1\bigr).
\]

Finite layer cake gives the exact identity

\[
C_T(u)=|u|\int_0^{1/2}\sinh(|u|v)D_T(v)\,dv.
\]

The equality is also valid at u = 0. Inclusive versus strict tail endpoints do not affect this integral. We estimate only after this equality:

\[
|L_T(u)-Z_T(u)|\le C_T(u).
\]

If the right-tail density bound is
\(N^+(\tfrac12+v,T)\le C_D T\log T\,e^{-a v\log T}\), reflection gives
\(D_T(v)\le 2C_D T\log T\,e^{-a v\log T}\).

Put A = a log T, b = |u| and R = 1/2. For 0 < b < A,

\[
I(A,b,R)=\int_0^R e^{-Av}\sinh(bv)\,dv
 =\frac12\left[
  \frac{1-e^{-(A-b)R}}{A-b}
  -\frac{1-e^{-(A+b)R}}{A+b}\right].
\]

Both endpoint terms are retained. Hence

\[
\frac{|L_T(u)-Z_T(u)|}{T}
 \le 2C_D(\log T)b\,I(A,b,1/2)
 \le \frac{2C_D(\log T)u^2}{(a\log T)^2-u^2}.
\]

The last inequality, unlike the finite integral equality, extends the integral to infinity. With a = 1/4 and |u| <= log T/8 this yields exactly

\[
\frac{|L_T(u)-Z_T(u)|}{T}
 \le \frac{128C_D}{3}\frac{u^2}{\log T}.
\]

The Selberg–Jutila version a < 1 widens the admissible comparison band to |u| < a log T. It does not make the positive unnormalized horizontal mass vanish.

## 3. The linear majorant, now checked in Lean

For a rational frequency u = log(n/m), 1 <= m < n, put H = log n and L = log T.

The unconditional rational Landau estimate in the repository supplies, uniformly for H <= L/8,

\[
\left|\frac{L_T(u)}{T}+\lambda(n/m)\right|
 \le C\,T^{-1/2}(1+L^2),\qquad
0\le\lambda(n/m)\le H.
\]

Here \(\lambda(q)=\Lambda(q)/(2\pi\sqrt q)\) if q is an integer prime power, and zero otherwise. The displayed error is a convenient weaker form of the proved rational contour estimate.

In this band the reflected comparison satisfies

\[
\frac{u^2}{L}\le\frac{H^2}{L}\le H/8.
\]

Outside this band, the unconditional zero-count bound gives

\[
|Z_T(u)|/T\le C_N L\le 8C_N H.
\]

These two bounds give one constant K and one lower height T_0, independent of n and m, with

\[
|Z_T(\log(n/m))|/T\le K(1+\log n).
\]

Taking conjugates treats the opposite sign. The constant mode is centered exactly. Thus all centered rational modes satisfy

\[
|A_T(n,m)|\le K(1+\log n+\log m),\qquad n,m\ge1.
\]

This is the crucial improvement over the former quadratic height envelope.

For a finite prime set P and integer mode k, unique factorization gives

\[
h_P(k)=\sum_{p\in P}|k_p|\log p
 =\log n(k)+\log m(k).
\]

Consequently the actual FMZ limit holds for every uniformly convergent Fourier series whose coefficients satisfy

\[
\sum_k|\widehat f(k)|(1+h_P(k))<\infty.
\]

The proof uses the actual rational arithmetic limits and dominated convergence. It supplies the actual zero sum and actual product Haar integral, not assumed provider functionals.

Since \(h_P(k)\le(\sum_{p\in P}\log p)\|k\|_\infty\), conventional decay
\(|\widehat f(k)|\le C(1+\|k\|_\infty)^{-B}\) suffices when B > d + 1, where d = |P|.

The exact limiting density is unchanged:

\[
g_P(x)=-\sum_{p\in P}\frac{\log p}{2\pi}
 \bigl(P_{p^{-1/2}}(x_p)-1\bigr),\qquad
P_r(x)=\frac{1-r^2}{1-2r\cos(2\pi x)+r^2}.
\]

The resulting limit is

\[
\mathcal F_T(f):=
 \frac{\sum_{0<\gamma_\rho\le T}m_\rho
 f((\gamma_\rho\log p/(2\pi))_{p\in P})
       -N(T)\int f\,dH}{T}
 \longrightarrow \int f g_P\,dH.
\]

### Additional regularity consequences on paper

Cauchy–Schwarz and lattice summability imply the same conclusion for
\(f\in H^s(\mathbb T^d)\) when \(s>d/2+1\).
A sufficient logarithmic endpoint coefficient bound is

\[
|\widehat f(k)|\le
 \frac{C}{(1+\|k\|)^{d+1}
  (\log(2+\|k\|))^{1+\eta}},\qquad\eta>0.
\]

These are sufficient conditions; no optimality is asserted.

## 4. Quantitative control for growing tests, on paper

For s >= 0 define the arithmetic Wiener norm

\[
\|f\|_{\mathcal A^s}
 =\sum_k|\widehat f(k)|(1+h_P(k))^s.
\]

For every epsilon > 0, the same two-band proof gives constants independent of P such that

\[
\boxed{
|\mathcal F_T(f)-\mathcal L(f)|
 \le C_\epsilon
 \left[(\log T)^{-\min(\epsilon,1)}
       +(1+\log^2 T)T^{-1/2}\right]
 \|f\|_{\mathcal A^{1+\epsilon}},
}\qquad
\mathcal L(f)=\int f g_P\,dH.
\]

Proof: for h <= L/8, the mode error is at most
\(C h^2/L+C(1+L^2)T^{-1/2}\). Divide by \((1+h)^{1+\epsilon}\).
If epsilon <= 1, the first quotient is at most
\(C L^{-\epsilon}\); if epsilon >= 1, it is at most C/L.
For h > L/8, the count bound and \(|\lambda|\le h\) give mode error at most C(1+h), so its quotient is at most \(C_\epsilon L^{-\epsilon}\).
Summing the absolute coefficients proves the bound.

Thus a finite prime set and test function may both vary with T:
if \(R_\epsilon(T)\|f_T\|_{\mathcal A^{1+\epsilon}}\to0\), with
\(R_\epsilon(T)\) the bracketed expression, then
\(\mathcal F_T(f_T)-\mathcal L(f_T)\to0\).
This does not assert that the varying main term \(\mathcal L(f_T)\) itself converges or vanishes.

The weights are submultiplicative because
\(h(k+l)\le h(k)+h(l)\) and \(1+a+b\le(1+a)(1+b)\). Hence

\[
\|f g\|_{\mathcal A^s}\le
 \|f\|_{\mathcal A^s}\|g\|_{\mathcal A^s},\qquad
\||A|^2\|_{\mathcal A^s}\le\|A\|_{\mathcal A^s}^2.
\]

For finite Fourier polynomials A_T, a useful sufficient condition is therefore

\[
\|A_T\|_{\mathcal A^{1+\epsilon}}
 =o((\log T)^{\min(\epsilon,1)/2}).
\]

This is an explicit growing-test condition to check against a proposed inverse-Gram construction. It has not been proved for the user's Pareto optimizers.

## 5. Exact signed prime Gram matrices

Let \(A(x)=\sum_k a_k e^{2\pi i k\cdot x}\) be a finite polynomial and
\(E=\sum_k|a_k|^2\). For each p, let K_p have entries

\[
(K_p)_{k,l}=
 \mathbf 1_{\{k_q=l_q\text{ for every }q\ne p\}}\,
 r_p^{|k_p-l_p|},\qquad r_p=p^{-1/2}.
\]

Expansion and character orthogonality give the exact identity

\[
\boxed{
\int g_P|A|^2\,dH
 =-\sum_{p\in P}\frac{\log p}{2\pi}
       (a^*K_p a-E).
}
\]

All off-diagonal terms and their signs remain. This is the FMZ bias of the actual finite zero-sampling Gram form:

\[
\frac{\sum_{0<\gamma_\rho\le T}m_\rho
 |A(\theta_\rho)|^2-N(T)E}{T}
 \longrightarrow
 -\sum_{p\in P}\frac{\log p}{2\pi}(a^*K_p a-E).
\]

Pointwise Poisson extrema supply sharp bounds, uniform over polynomials:

\[
-\sum_{p\in P}\frac{\log p}{\pi}\frac{r_p}{1-r_p}\,E
 \le \int g_P|A|^2\,dH
 \le \sum_{p\in P}\frac{\log p}{\pi}\frac{r_p}{1+r_p}\,E.
\]

Sharpness follows by concentrating squared polynomials near the simultaneous extrema x_p = 0 or x_p = 1/2.

For a contiguous one-prime fiber with indices 0,...,M, M >= 1,

\[
K_r=(r^{|j-k|})_{j,k=0}^M,\qquad
\det K_r=(1-r^2)^M,
\]

\[
K_r^{-1}=\frac1{1-r^2}
\begin{pmatrix}
1&-r&&\\
-r&1+r^2&-r&\\
&\ddots&\ddots&\ddots\\
&&-r&1
\end{pmatrix}.
\]

The complete positive square identity is

\[
b^*K_r^{-1}b
 =|b_0|^2+\frac1{1-r^2}\sum_{j=1}^M
       |b_j-rb_{j-1}|^2.
\]

For M = 0 the inverse is (1) and the empty-sum identity gives |b_0|^2.
Multiplying K_r by the displayed tridiagonal matrix proves the inverse at every index. Subtracting r times the preceding row, working from the last row upward, proves the determinant formula. These proofs establish arbitrary M; Wolfram checks sizes 2 through 7 as an additional exact verification.

## 6. Signed fourth moments and the infinite-prime correction

Write \(g_p=-c_p(P_{r_p}-1)\), \(c_p=\log p/(2\pi)\).
Under product Haar, the g_p are independent and have mean zero.

Exact circle integration gives

\[
V_P:=\int g_P^2\,dH
 =\sum_{p\in P}\frac{(\log p)^2}{2\pi^2(p-1)}.
\]

The exact fourth moment retains a signed prime remainder:

\[
\boxed{
\int g_P^4\,dH
 =3V_P^2+
 \sum_{p\in P}
  \frac{(\log p)^4(13-3p)}{8\pi^4(p-1)^3}.
}
\]

Only p = 2 and p = 3 contribute positively to this remainder.
Every prime p >= 5 contributes negatively. In particular

\[
\int g_P^4\,dH\le 3V_P^2+C_{\rm exc},\qquad
C_{\rm exc}=
 \frac{14(\log2)^4+(\log3)^4}{16\pi^4}.
\]

Proof: the exact second and fourth centered Poisson moments are

\[
\int(P_r-1)^2=\frac{2r^2}{1-r^2},\qquad
\int(P_r-1)^4=\frac{2r^4(3+7r^2)}{(1-r^2)^3}.
\]

Independence gives
\(\int g_P^4=\sum_p\int g_p^4+6\sum_{p<q}
 (\int g_p^2)(\int g_q^2)\).
Subtracting \(3V_P^2\) gives precisely the signed remainder above.
Wolfram verified the circle moments by rational contour residues and the prime simplification exactly.

There is a useful obstruction to an ordinary infinite-prime density:
\(V_P\to\infty\) as P exhausts the primes. Indeed the summands dominate a positive multiple of 1/p; Euler's divergent reciprocal-prime sum follows from the finite Euler product dominating the divergent harmonic partial sums.

Hölder gives

\[
\int|g_P|\,dH
 \ge \frac{V_P^{3/2}}
           {\sqrt{\int g_P^4\,dH}}
 \ge \frac{V_P^{3/2}}{\sqrt{3V_P^2+C_{\rm exc}}}
 \longrightarrow\infty.
\]

Consequently there is no finite signed measure on the infinite prime product torus whose every finite-prime marginal has density g_P. Marginal total variation would be bounded by the total variation of that measure, contradicting this inequality.

There is nevertheless a precise infinite-prime Fourier-algebra extension.
On \(\prod_p\mathbb T\), take characters indexed by finitely supported integer prime modes k and coefficients with

\[
\sum_k |a_k|(1+\sum_p|k_p|\log p)<\infty.
\]

The series defines a continuous function by uniform absolute convergence. The rational mode theorem and dominated convergence give the ordinate FMZ functional with limit

\[
\mathcal L(f)
 =-\sum_p\frac{\log p}{2\pi}
       \sum_{j\ne0}p^{-|j|/2}\widehat f(j e_p).
\]

The displayed series is absolutely convergent. This is a functional on the specified Fourier algebra, and the quantitative estimate of Section 4 is dimension independent. It is not an ordinary finite signed correction measure. The literal infinite-product Haar reconstruction has not been added as a Lean declaration.

## 7. The RH-relevant extension is the full Weil form

The prime operators above reappear in the full explicit formula, but the omitted archimedean and pole terms are essential.

For \(\phi\in C_c^\infty(\mathbb R)\), put

\[
\Phi(z)=\int_{\mathbb R}\phi(x)e^{zx}\,dx,\quad
\widetilde\phi(x)=\overline{\phi(-x)},\quad
h=\phi*\widetilde\phi,\quad H(z)=\int h(x)e^{zx}\,dx.
\]

Then \(H(z)=\Phi(z)\overline{\Phi(-\overline z)}\), and
\(H(it)=|\Phi(it)|^2\).
The exact all-zero Weil form is

\[
Q(\phi)=\sum_\rho m_\rho
 \Phi(\rho-\tfrac12)
 \overline{\Phi(\tfrac12-\overline\rho)}.
\]

All ordinate signs occur. Smooth compact support gives absolute zero-sum convergence. With \(\psi=\Gamma'/\Gamma\), the full identity is

\[
\boxed{
\begin{aligned}
Q(\phi)
={}&H(\tfrac12)+H(-\tfrac12)\\
&-\sum_{p}\log p\sum_{j\ge1}p^{-j/2}
       \bigl(h(j\log p)+h(-j\log p)\bigr)\\
&+\frac1{2\pi}\int_{\mathbb R}|\Phi(it)|^2
 \left[\operatorname{Re}\psi(\tfrac14+it/2)-\log\pi\right]\,dt .
\end{aligned}
}
\]

The prime sum is finite because h has compact support. No term on the right is removed or replaced by a coefficient norm.

The prime line can be written exactly as

\[
-\sum_p\log p\,
 \bigl(\langle\phi,\mathcal P_p\phi\rangle-\|\phi\|_2^2\bigr),
\quad
\mathcal P_p=I+\sum_{j\ge1}p^{-j/2}
       (U_{j\log p}+U_{-j\log p}),
\]

where \(U_a\phi(x)=\phi(x-a)\) and the inner product is
\(\langle f,g\rangle=\int f\overline g\).
The operator series converges in norm for each p. Its Fourier multiplier is the same Poisson kernel \(P_{p^{-1/2}}(t\log p/(2\pi))\).

Thus the signed FMZ Gram identity identifies the prime operator structure in the exact RH criterion. It supplies no lower bound for the full three-line expression.

Weil's theorem states

\[
{\rm RH}\quad\Longleftrightarrow\quad
 Q(\phi)\ge0\ \text{for every }\phi\in C_c^\infty(\mathbb R).
\]

The distinction is visible in a single reflected off-line pair.
Writing \(z=\delta+i\gamma\), its contribution is

\[
2m\,\operatorname{Re}
  \bigl(\Phi(z)\overline{\Phi(-\overline z)}\bigr)
 =\frac m2\left(
   |\Phi(z)+\Phi(-\overline z)|^2
   -|\Phi(z)-\Phi(-\overline z)|^2\right).
\]

The reflection block has eigenvalues +1 and -1.
On the line the two evaluations agree and the negative square is zero.
Burnol's interpolation argument constructs a negative test if an off-line zero exists. Finite matrix positivity for Poisson kernels is therefore insufficient to prove full Weil positivity.

A normalized ordinate FMZ statistic is insensitive to finitely many zeros: their contribution is O(1/T) for each fixed test. A growing-test estimate helps only after its norm growth and its relationship to the unnormalized Weil or physical residual form are proved.

## 8. Concrete obligations for the Pareto program

The repository already has a convergent, positive RH detector with exact weights:

\[
E_4=\sum_\rho
  \frac{m_\rho(\beta_\rho-\tfrac12)^2}
       {(1+\gamma_\rho^2)^2},\qquad
M(u)=\sum_\rho
 \frac{m_\rho(\cosh(u(\beta_\rho-\tfrac12))-1)}
      {(1+\gamma_\rho^2)^2}.
\]

The subscript 4 refers to the ordinate denominator; the numerator is the square of the horizontal displacement.

For every actual legal Pareto candidate f, with physical error
\(e=\|1-f\|^2\), the existing checked bridge is

\[
\frac{u^2}{2}E_4\le M(u)
 \le4(\cosh(|u|/2)-1)E_4
 \le(\cosh(|u|/2)-1)eS_2,\qquad
S_2\le C_0=2+\gamma_{\!E}-\log(4\pi).
\]

The checked theorem
ActualZeroCoshMass.regularizedCoshMass_eq_zero_iff_RH gives
\(M(u)=0\Longleftrightarrow{\rm RH}\) for any fixed u != 0.
It proves the equivalence, not the vanishing.

For the discrete optimization, preserve the complete finite identity

\[
e_N=1-2\sum_d c_{N,d}b_d+
         \sum_{d,e}c_{N,d}c_{N,e}G_N(d,e).
\]

At the optimizer it becomes \(e_N=1-b^TG_N^{-1}b=1-Q_N\).
The physical Pareto Gram matrix is not identified with the zero-sampling Poisson Gram matrix in Section 5.

There are two precise RH endpoints for further work:

1. Prove a global lower bound for the complete Weil expression in Section 7, including its signed prime correlations, gamma integral and both pole terms, for every smooth compactly supported test.
2. Construct actual legal Pareto coefficients and prove \(e_N\to0\) using the complete physical identity above. The existing bridge would then give \(M(1)=0\) and RH.

The strengthened FMZ estimate supplies a quantitative tool for a growing Fourier family. Applying it to the inverse-Gram family still needs a checked weighted-norm growth bound and an exact link to the physical residual or full Weil form. Neither obligation is discharged here.

## 9. Lean changes and verification

Four existing modules were strengthened, without adding placeholders or project-local axioms:

- Analysis/ActualRationalFMZDomination.lean: linear simultaneous rational envelope and one-moment weighted synthesis.
- Analysis/ActualPrimeTorusFMZSeries.lean: exact prime weight \(1+\sum_p|k_p|\log p\).
- Analysis/PrimeTorusFourierDecay.lean: lattice summability under B > d + 1.
- Analysis/ActualPrimeTorusFMZContinuous.lean: the final continuous-test theorem under B > card(P) + 1.

The existing theorem name is
ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson_of_selberg.
Its explicit domain-specific premise remains UniformSelbergDensity (1/4).

Core proof verification:
job_lN8d6-DCL6HC3S_E2FxYiEfS0YU8qgOq, succeeded.

Complete final-file and imported dependency verification:
job_bXTEotl9WOMZJz3Wm35qHgWyJYJaLFLp, succeeded.
The axiom report contains only propext, Classical.choice and Quot.sound.
That report does not discharge the Selberg hypothesis.

Final publication is gated by the server checkpoint audit and exported-project validation. The paper deductions above are not represented as additional Lean-checked results.

## 10. Reproducible Wolfram checks

Exact arithmetic and symbolic checks returned True for the geometric Poisson identity, tridiagonal inverses of sizes 2 through 7, finite integral endpoints and the reflected-pair identity.

A compact replay:

    Clear[r,z,c,p,A,b,R];
    K[M_] := Table[r^Abs[j-k],{j,0,M},{k,0,M}];
    J[M_] := Table[
      Which[j==k&&MemberQ[{0,M},j],1,j==k,1+r^2,
            Abs[j-k]==1,-r,True,0],
      {j,0,M},{k,0,M}]/(1-r^2);
    Table[FullSimplify[K[M].J[M]==IdentityMatrix[M+1]],{M,1,6}]

    pp=(1-r^2)z/((1-r z)(z-r));
    moment[q_] := Factor[
      Residue[(pp-1)^q/z,{z,0}]+
      Residue[(pp-1)^q/z,{z,r}]];
    Table[moment[q],{q,1,4}]

    variance=2c^2 r^2/(1-r^2);
    fourth=2c^4 r^4(3+7r^2)/(1-r^2)^3;
    FullSimplify[(fourth-3variance^2) /.
      {r->1/Sqrt[p],c->Log[p]/(2Pi)},Assumptions->p>1]

    endpoints=1/2((1-Exp[-(A-b)R])/(A-b)-
                    (1-Exp[-(A+b)R])/(A+b));
    FullSimplify[
      Integrate[Exp[-A v]Sinh[b v],{v,0,R},
                Assumptions->A>b>0&&R>0]==endpoints,
      Assumptions->A>b>0&&R>0]

The fourth-cumulant result was
\((13-3p)(\log p)^4/[8\pi^4(p-1)^3]\).
The finite integral check returned True, and the Selberg band constant was exactly 128/3. No numerical zero samples are used as a proof.
