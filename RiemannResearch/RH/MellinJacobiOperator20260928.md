# A canonical regularized Mellin operator and its exact spectrum

Date: 2026-09-28.

Status: rigorous paper proof, **not Lean-formalized**. This note does not claim a Hilbert–Pólya operator or a proof of RH. It identifies and completely solves a natural regularized operator suggested by the Pareto Mellin DPP, and proves specific domain obstructions to using it as the desired operator.

## 1. Conventions and the Mellin isometry

Work over the complex Hilbert space

\[
 H=\left\{f:\mathbb N_{\ge1}\to\mathbb C:
 \sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)}<\infty\right\},
 \qquad
 \langle f,g\rangle_H=\sum_{n\ge1}
 \frac{\overline{f(n)}g(n)}{n(n+1)}.
\]

All inner products are conjugate-linear in the first argument. Set

\[
 (Jf)(y)=\mathbf1_{[0,\infty)}(y)e^{-y/2}f(\lfloor e^y\rfloor),
 \qquad U=\mathcal FJ,
 \qquad
 (\mathcal Fh)(t)=\int_{\mathbb R}h(y)e^{-ity}\,dy.
\]

The Fourier transform is understood by its Plancherel extension when the integral is not absolutely convergent; its target measure is \(dt/(2\pi)\). Direct integration gives

\[
 \|Jf\|_{L^2(dy)}^2
 =\sum_{n\ge1}|f(n)|^2
   \int_{\log n}^{\log(n+1)}e^{-y}\,dy
 =\|f\|_H^2.
\]

Thus \(U:H\to L^2(\mathbb R,dt/(2\pi))\) is an isometry onto a closed subspace. For bounded \(f\), its integral is absolutely convergent and

\[
 (Uf)(t)=\int_1^\infty f(\lfloor x\rfloor)x^{-3/2-it}\,dx.
\]

The operator \(M_t\), multiplication by the real coordinate, is selfadjoint on its maximal domain in the full frequency space. The Fourier sign convention means that it corresponds to \(-i\,d/dy\).

## 2. The direct induced operator and its form domain are trivial

**Theorem 1.**

\[
 UH\cap D(|M_t|^{1/2})=\{0\},\qquad
 UH\cap D(M_t)=\{0\}.
\]

**Proof.** If \(f\ne0\), let \(n_0\) be its least nonzero coordinate and put \(a=\log n_0\). For sufficiently small \(\varepsilon>0\), \(Jf\) vanishes on \((a-\varepsilon,a)\), including when \(n_0=1\), where the preceding interval lies in the negative half-line. On \((a,a+\varepsilon)\), it equals \(e^{-y/2}f(n_0)\). Shrinking \(\varepsilon\) if necessary, there is \(c>0\) such that

\[
 |Jf(a+v)-Jf(a-u)|\ge c
 \quad(0<u,v<\varepsilon).
\]

Its order-one-half Sobolev seminorm therefore dominates

\[
 c^2\int_0^\varepsilon\int_0^\varepsilon
       \frac{du\,dv}{(u+v)^2}=\infty.
\]

The Fourier characterization of that seminorm implies

\[
 \int_{\mathbb R}|t|\,|Uf(t)|^2\,\frac{dt}{2\pi}=\infty.
\]

One can obtain the characterization directly from Plancherel applied to translations and Tonelli's theorem: integrate
\(\|h(\cdot+a)-h\|_2^2\) against \(da/a^2\), and use
\(\int_{\mathbb R}|e^{ita}-1|^2a^{-2}\,da=2\pi|t|\).
This proves the first assertion. The second follows from
\(D(M_t)\subset D(|M_t|^{1/2})\). ∎

In particular, the ordinary composition \(U^*M_tU\) has domain \(\{0\}\). The usual absolute first-order form domain is also trivial. This statement concerns these particular constructions; it does not rule out other regularizations, other Hilbert spaces, or other operators.

**DPP consequence.** If a nonzero finite-rank projection DPP has orthonormal one-particle orbitals \(Uf_1,\ldots,Uf_r\), its one-point density is \(K(t,t)=\sum_j|Uf_j(t)|^2\). The first-moment formula for a nonnegative linear statistic and Theorem 1 give

\[
 \boxed{\mathbb E\sum_{t\in\Xi}|t|=\infty.}
\]

This includes every nonzero finite residue-space Mellin projection DPP. No interchange of a signed conditionally convergent integral is involved.

## 3. Symmetric frequency cutoff on finite physical supports

The normalized physical-site basis is

\[
 e_n=\sqrt{n(n+1)}\,\mathbf1_{\{n\}},\qquad n\ge1.
\]

Its exact Mellin transform is

\[
 u_n(t):=(Ue_n)(t)=
 \frac{\sqrt{n+1}e^{-it\log n}-\sqrt n e^{-it\log(n+1)}}{1/2+it}.
\]

For finite-support \(f,g\), define

\[
 q(f,g)=\lim_{T\to\infty}
 \int_{-T}^{T}t\,\overline{Uf(t)}Ug(t)\,\frac{dt}{2\pi}.
\]

This is explicitly a symmetric-cutoff regularization. The following calculation proves existence on the stated domain, without asserting ordinary absolute integrability.

For real \(\delta\), let

\[
 k(\delta)=\lim_{T\to\infty}
 \int_{-T}^{T}\frac{t e^{-it\delta}}{t^2+1/4}\,\frac{dt}{2\pi}.
\]

The standard Fourier integral for \((t^2+1/4)^{-1}\), or direct contour integration followed by differentiation for \(\delta\ne0\), gives

\[
 k(\delta)=-\frac i2\operatorname{sgn}(\delta)e^{-|\delta|/2}
 \quad(\delta\ne0),\qquad k(0)=0.
\]

For \(\delta\ne0\) convergence also follows directly from Dirichlet's test; at zero every symmetric truncation is zero by oddness. These observations avoid relying on a differentiation under a nonabsolute integral.

Put \(A_n=\sqrt{n+1}\), \(B_n=\sqrt n\). Expanding the four terms gives

\[
\begin{aligned}
 q(e_n,e_m)={}&A_nA_m k(\log(m/n))
 -A_nB_m k(\log((m+1)/n))\\
 &-B_nA_m k(\log(m/(n+1)))
 +B_nB_m k(\log((m+1)/(n+1))).
\end{aligned}
\]

If \(m\ge n+2\), all four logarithms are positive. The expression factors as

\[
 -\frac i2
 (A_n\sqrt n-B_n\sqrt{n+1})
 \left(\frac{A_m}{\sqrt m}-\frac{B_m}{\sqrt{m+1}}\right)=0.
\]

If \(m=n+1\), the third logarithm is zero. Artificially assigning its kernel value \(-i/2\) would make the same factorization zero. Its coefficient is \(-B_nA_m\); replacing that artificial value by the actual value zero subtracts \(iB_nA_m/2\). Hence

\[
 q(e_n,e_{n+1})=-\frac i2\sqrt{n(n+2)}.
\]

For \(m=n\), \(|u_n(t)|^2\) is even, so the integrand is odd and every symmetric integral is zero. Finally each finite-cutoff form is Hermitian, which determines the reverse adjacent entry. We have proved:

**Theorem 2.** The regularized form exists on finite physical supports and has matrix

\[
 \boxed{
 q(e_n,e_m)=
 \begin{cases}
 -\dfrac i2\sqrt{n(n+2)},&m=n+1,\\[2pt]
 +\dfrac i2\sqrt{m(m+2)},&n=m+1,\\[2pt]
 0,&\text{otherwise}.
 \end{cases}}
\]

The adjacent signs use precisely the inner-product and Fourier conventions in Section 1.

## 4. Essential selfadjointness and exact spectral measure

Let \(B_0\) be the finite-support operator specified by
\(q(f,g)=\langle f,B_0g\rangle_H\). Change orthonormal basis to

\[
 b_n=i^{n-1}e_n.
\]

The factor \(\overline{i^{n-1}}i^n=i\) converts the upper adjacent coefficient \(-ia_n\) to \(+a_n\). Thus \(B_0\) is unitarily equivalent to the Jacobi operator on \(c_{00}(\mathbb N_{\ge1})\):

\[
 (\mathsf J_0x)_n=a_{n-1}x_{n-1}+a_nx_{n+1},\qquad
 a_n=\frac12\sqrt{n(n+2)},\quad a_0=0.
\]

Its coefficients are positive and

\[
 \sum_{n\ge1}\frac1{a_n}
 =\sum_{n\ge1}\frac2{\sqrt{n(n+2)}}=\infty.
\]

The Jacobi Carleman criterion therefore implies that \(\mathsf J_0\) is essentially selfadjoint. Denote its unique selfadjoint closure by \(\mathsf J\), and the corresponding closure in \(H\) by \(B\).

Here is the short deficiency-index proof in this case. If \(x\in\ell^2\) lies in \(\ker(\mathsf J_0^*-z)\), with \(z=i\) or \(z=-i\), its coordinates satisfy the formal Jacobi recurrence. Multiply it by \(\overline{x_n}\), take imaginary parts, and sum from \(1\) to \(N\). The interior terms cancel, leaving

\[
 a_N\operatorname{Im}(\overline{x_N}x_{N+1})
 =\operatorname{Im}(z)\sum_{n=1}^{N}|x_n|^2.
\]

If \(x\ne0\), the right side has absolute value at least some \(c>0\) for every sufficiently large \(N\). Hence

\[
 |x_N|^2+|x_{N+1}|^2\ge2|x_Nx_{N+1}|
 \ge\frac{2c}{a_N}.
\]

Summing contradicts \(x\in\ell^2\), because \(\sum a_N^{-1}=\infty\). Both deficiency spaces are therefore zero, proving essential selfadjointness directly. In particular, this expression has no alternative selfadjoint extension obtained by a different boundary condition at infinity.

The Jacobi matrix can be diagonalized explicitly. Let
\(P_k^{(3/2)}(t;\pi/2)\) be the standard Meixner–Pollaczek polynomials, and set

\[
 p_k(t)=\sqrt{\frac2{(k+1)(k+2)}}\,
 P_k^{(3/2)}(t;\pi/2),\qquad k\ge0.
\]

The standard Meixner–Pollaczek orthogonality and recurrence specialize to

\[
 d\nu(t)=\frac2\pi|\Gamma(3/2+it)|^2\,dt
 =\frac{2(t^2+1/4)}{\cosh(\pi t)}\,dt,
\]

\[
 \int_{\mathbb R}p_j(t)p_k(t)\,d\nu(t)=\delta_{jk},
 \qquad p_0=1,
\]

and

\[
 tp_k(t)=\frac12\sqrt{(k+1)(k+3)}\,p_{k+1}(t)
       +\frac12\sqrt{k(k+2)}\,p_{k-1}(t),
\]

where the second term is zero at \(k=0\). This matches the Jacobi coefficients with site index \(n=k+1\).

For clarity, the normalization follows from the standard squared norm

\[
 \int_{\mathbb R}\big|P_k^{(3/2)}(t;\pi/2)\big|^2
 |\Gamma(3/2+it)|^2\,dt
 =\frac{\pi}{4}(k+1)(k+2).
\]

Multiplication by \(2/\pi\) makes the squared norm \((k+1)(k+2)/2\), giving exactly the factor defining \(p_k\). In particular \(\nu\) is a probability measure. The elementary gamma recurrence and reflection identity give the displayed hyperbolic-cosine density.

We also verify completeness, rather than merely matching a recurrence. The density of \(\nu\) has exponential decay. If \(F\in L^2(\nu)\) is orthogonal to every polynomial, the finite complex measure \(F\,d\nu\) has Fourier transform

\[
 \Phi(z)=\int_{\mathbb R}e^{izt}F(t)\,d\nu(t)
\]

holomorphic in the strip \(|\operatorname{Im}z|<\pi/2\). This follows from Cauchy–Schwarz and the exponential moments of \(\nu\); the same argument justifies every derivative there. All derivatives at zero vanish by the assumed moment orthogonality. The identity theorem gives \(\Phi\equiv0\), and uniqueness of Fourier transforms of finite measures yields \(F=0\) almost everywhere. Thus the polynomials are complete.

Consequently the map \(\delta_n\mapsto p_{n-1}\) extends to a unitary map from \(\ell^2\) onto \(L^2(\nu)\). It identifies \(\mathsf J_0\) with multiplication by \(t\) on polynomials. Multiplication by \(t\) on its maximal domain is a selfadjoint extension; essential selfadjointness from Carleman's criterion shows that this extension is exactly the image of \(\mathsf J\). Hence:

**Theorem 3.** The first-site spectral measure of \(B\) is

\[
 \boxed{d\nu(t)=\frac{2(t^2+1/4)}{\cosh(\pi t)}\,dt.}
\]

The density is strictly positive on the entire real line. Therefore

\[
 \boxed{\sigma(B)=\mathbb R,\quad
 \sigma_{\mathrm{pp}}(B)=\varnothing,\quad
 \sigma_{\mathrm{sc}}(B)=\varnothing,}
\]

and its spectrum is purely absolutely continuous with multiplicity one.

The spectral transform constructed from \(p_k\) is **not** the original Mellin map \(U\). For example the original Mellin density of \(e_1\) is

\[
 |Ue_1(t)|^2\frac{dt}{2\pi}
 =\frac{3-2\sqrt2\cos(t\log2)}{t^2+1/4}\frac{dt}{2\pi},
\]

which has a polynomial tail, whereas \(\nu\) has an exponential tail. This distinction is necessary: the original map has the domain obstruction of Theorem 1 and cannot implement an ordinary intertwining with \(M_t\).

## 5. Exact domain on bounded periodic vectors

The normalized coordinates of \(f\in H\) in the original basis are
\(x_n=f(n)/\sqrt{n(n+1)}\). The tridiagonal matrix from Theorem 2 therefore has physical-coordinate action

\[
 \boxed{(Bf)(n)=\frac i2\big((n+1)f(n-1)-nf(n+1)\big),\qquad f(0)=0.}
\]

For example, the coefficient of \(f(n+1)\) is obtained from

\[
 \sqrt{n(n+1)}\left(-\frac i2\sqrt{n(n+2)}\right)
 \frac{f(n+1)}{\sqrt{(n+1)(n+2)}}
 =-\frac{i n}{2}f(n+1),
\]

and the previous-coordinate term is checked in the same way.

Here the displayed expression describes the closed operator precisely: its domain consists of the \(f\in H\) for which that formal expression also belongs to \(H\). To see this, the adjoint of the finite-support operator has exactly this maximal domain, by testing against every coordinate vector. Essential selfadjointness says that its closure equals this adjoint.

**Theorem 4.** If \(f\) is bounded and periodic on the positive integers, then

\[
 f\in D(B)\quad\Longleftrightarrow\quad
 f(n+2)=f(n)\quad\text{for every }n\ge1.
\]

**Proof.** Every bounded \(f\) belongs to \(H\). Suppose it has period \(L\). For \(n\ge2\), write

\[
 (Bf)(n)=\frac i2\big(n\Delta_n+f(n-1)\big),
 \qquad \Delta_n=f(n-1)-f(n+1).
\]

The sequence \(\Delta_n\), on indices \(n\ge2\), is periodic. If some \(\Delta_{n_0}\ne0\), take the infinite residue class \(n=n_0+jL\). Along it,

\[
 \frac{|(Bf)(n)|^2}{n(n+1)}
 \longrightarrow\frac{|\Delta_{n_0}|^2}{4}>0.
\]

The series defining \(\|Bf\|_H^2\) diverges, so \(f\notin D(B)\). Therefore domain membership forces \(\Delta_n=0\) for every \(n\ge2\), which is exactly two-periodicity on positive indices.

Conversely, if \(f\) is two-periodic, then for \(n\ge2\),
\((Bf)(n)=i f(n-1)/2\). The first coordinate is \(-if(2)/2\). The formal image is bounded, hence belongs to \(H\), which proves domain membership. ∎

For residue atoms

\[
 g_d(n)=\frac{n\bmod d}{d},\qquad
 V_N=\operatorname{span}_{\mathbb C}\{g_2,\ldots,g_N\},
\]

each \(f\in V_N\) is bounded, has period
\(L_N=\operatorname{lcm}(2,\ldots,N)\), and satisfies \(f(kL_N)=0\) for all positive integers \(k\). If \(N\ge2\), \(L_N\) is even. Two-periodicity then forces all even values to be zero and all odd values to be a common constant. This is exactly a scalar multiple of \(g_2\). Conversely \(g_2\) is bounded and two-periodic. Thus:

\[
 \boxed{V_N\cap D(B)=\operatorname{span}_{\mathbb C}\{g_2\}
 \qquad(N\ge2).}
\]

The real version follows by restriction. In particular \(g_d\notin D(B)\) for every \(d\ge3\).

## 6. Exact connection to the arithmetic density obstruction

Let \(P_N\) be the orthogonal projection onto \(V_N\), and define the
constant-function approximation defect
\(D_N=\|(I-P_N)\mathbf1\|_H^2\). This definition distinguishes \(D_N\)
from the separately normalized first-site vacancy.

Since \(g_2(n)\) is \(1/2\) at odd \(n\) and zero at even \(n\), the
explicit operator action gives, including the first coordinate,

\[
 Bg_2=\frac i4\mathbf1-\frac i2g_2.
\]

Since \(P_Ng_2=g_2\) for every \(N\ge2\), it follows exactly that

\[
 \boxed{\|(I-P_N)Bg_2\|_H^2=\frac1{16}D_N.}
\]

Consequently \(Bg_2\) belongs to the closed arithmetic span if and only if
the constant function does. Under the existing residue-space density
criterion, this is precisely the remaining RH endpoint. The completely
solved spectrum of \(B\) does not prove this approximation property; the
formula identifies exactly where the arithmetic problem reappears.

## 7. Interpretation and precise limitations

The Mellin DPP suggests multiplication by frequency as a first candidate for a one-particle Hamiltonian. For this exact Pareto staircase realization, its direct induced operator and form fail at the domain level. Symmetric frequency cutoff on finite physical supports repairs this in a specific way and produces a completely explicit essentially selfadjoint operator. Its exact spectral law is Meixner–Pollaczek, with no eigenvalues at all, and almost every arithmetic atom is outside its operator domain.

Thus this natural regularization does not provide a Hilbert–Pólya realization of zeta zeros. It is an explicit calculation that any proposed alternative must distinguish itself from. It does not exclude an arithmetic perturbation, a scattering construction, a different domain, or a different underlying Hilbert space; those would need additional independently proved structure. No RH-strength hypothesis was used in any theorem above.

## References

1. NIST DLMF, Section 18.19, equations 18.19.8–18.19.9: Meixner–Pollaczek weight and squared norms. <https://dlmf.nist.gov/18.19>
2. NIST DLMF, Section 18.22, equation 18.22.8: Meixner–Pollaczek recurrence. <https://dlmf.nist.gov/18.22>
3. Gerald Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, AMS, 2000: standard half-line Jacobi operator, maximal-domain, and selfadjointness theory. Author's edition: <https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf>

The new content of this note is the application to the exact Pareto Mellin map, including its trivial induced form domain, the symmetric-cutoff matrix calculation, and the arithmetic periodic-domain characterization. No claim of literature novelty is made.
