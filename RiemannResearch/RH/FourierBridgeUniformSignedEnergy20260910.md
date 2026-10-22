# Full Fourier bridge and uniform signed quotient energy

September 10, 2026. Ordinary mathematical proof, with no Lean execution or new formal verification.

For the exact dyadic quotient remainder \(E_\epsilon\) defined below, this note proves the Fourier identity
\[
a_\ell(E_\epsilon)=\sum_{h\ne0}C_{\ell h}
\left[\frac{N_\epsilon\zeta(1-i\omega_h)}
{\zeta(1+\epsilon-i\omega_h)}-1\right]
\frac{1-z_h}{1-3^{-\epsilon}z_h}
\]
and the unconditional complete signed energy estimate
\[
\boxed{\sup_{0<\epsilon\le1/2}\|E_\epsilon\|^2
=\sup_{0<\epsilon\le1/2}\frac14
\sum_{\ell\ge1}|a_\ell(E_\epsilon)|^2<\infty.}
\]
All boundary coordinates and all mixed terms are included. The proof also gives \(E_\epsilon\rightharpoonup0\). Its analytic input is the classical unconditional Mertens bound; no hypothesis about zeros in the critical strip is assumed.

The canonical Hilbert and coordinate identities are those of the supplied *DyadicTentTerminalVerification20260910(1).md* handoff and its binary logarithmic-mean continuation. The arithmetic family is the one in `DyadicRegularizedNorm.lean`, `DyadicRegularizedBoundaryCoefficients.lean`, and `DyadicSignedBoundaryNormCriterion.lean` of `Cnoack3/RiemannResearch`, at commit `8e6e40f3af91a382bc27d9902ca795f31e230284`. Reading those definitions fixes the target; this document supplies an ordinary analytic proof, not a new formal-verification claim.

Here “complete energy” means the full norm of this zero-mean quotient remainder. The complementary physical component and the full legal witnesses needed for the stated RH route are separate obligations; they are not proved here.

## 1. Conventions and actual vectors

Let \(\mathcal H\) have squared norm
\[
\|f\|^2=\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)},
\]
with \(f(0)=0\). Put
\[
(T_mf)(n)=m f(\lfloor n/m\rfloor),\quad
R_A(n)=n\bmod A,\quad
v_A(k)=1-A\mathbf1_{A\mid k}.
\]
The orthogonal projection \(Q\) onto \(\ker(T_2^*-I)\), unit mean vector \(1\), and boundary coordinates \(a_\ell\), indexed by \(\ell\ge1\), have the canonical normalization
\[
a_\ell(f)=4\langle Qb_\ell,f\rangle,
\qquad s_n(\ell)=a_\ell(QT_n1),
\]
and the complete decomposition on \(Q\mathcal H\) is
\[
\|f\|^2=|\langle1,f\rangle|^2+
\frac14\sum_{\ell\ge1}|a_\ell(f)|^2.
\]
In particular, \(a_\ell(1)=0\), \(Q1=1\), and \(\langle1,QT_n1\rangle=1\).

Block telescoping proves exactly
\[
\|T_mf\|^2=m\|f\|^2.
\]
Indeed, the sum of the physical weights for \(mr\le n<m(r+1)\) is \(1/[mr(r+1)]\).

## 2. Scalar tents and their Fourier expansion

Write \(L=\log2\), \(a=2\ell\), \(c=2\ell+1\), and \(b=2\ell+2\). Define
\[
\tau_\ell(x)=(1-|x-c|)_+,\quad
\Psi_\ell(x)=\sum_{d\in\mathbb Z}\tau_\ell(2^{-d}x),\quad
\phi_\ell(t)=\Psi_\ell(2^t).
\]
The periodization is locally finite; positive interiors of its summands are disjoint because \(b/a\le2\). Hence \(\phi_\ell\) is continuous and periodic with period one.

At integer arguments the negative-depth summands vanish because their arguments are even integers. The remaining finite sums satisfy
\[
u_{2n}=u_n,\quad
u_{2n+1}=\mathbf1_{n=\ell}+(u_n+u_{n+1})/2,
\quad u_0=u_1=0.
\]
The midpoint formula holds because every knot of every remaining dilated tent is an integer. Strong induction identifies this recurrence with the actual boundary steps:
\[
\Psi_\ell(n)=s_n(\ell),\qquad \Psi_\ell(1)=0.
\]

For \(\omega_h=2\pi h/L\), unfolding gives
\[
C_{\ell h}=\int_0^1\phi_\ell(t)e^{-2\pi iht}\,dt
=\frac1L\int_a^b\tau_\ell(x)x^{-1-i\omega_h}\,dx.
\]
Direct integration on the two affine pieces gives
\[
C_{\ell0}=\frac{a\log a-2c\log c+b\log b}{L},
\]
and, for \(h\ne0\),
\[
C_{\ell h}=
\frac{a^{1-i\omega_h}-2c^{1-i\omega_h}+b^{1-i\omega_h}}
{L(-i\omega_h)(1-i\omega_h)}.
\]
In particular,
\[
|C_{\ell h}|\le
\frac{4c}{L|\omega_h|\sqrt{1+\omega_h^2}}\quad(h\ne0).
\]
The Fourier series therefore converges absolutely and uniformly for each fixed \(\ell\). Fourier uniqueness gives
\[
\Psi_\ell(x)=\sum_{h\in\mathbb Z}C_{\ell h}x^{i\omega_h},
\qquad C_{\ell0}+\sum_{h\ne0}C_{\ell h}=0.
\]
The already identified binary mean is exactly \(a_\ell(QR_2)=LC_{\ell0}\).

## 3. The signed residue kernel and dilations

Put
\[
D_{A,K}(\omega)=\sum_{k\le K}v_A(k)k^{i\omega-1}.
\]
Since \(\sum_{k\le n}v_A(k)=n\bmod A\), summation by parts gives convergence for every real \(\omega\), and the bound
\[
\sup_K|D_{A,K}(\omega)|
\le(A-1)[2+\log(2+|\omega|)].
\tag{3.1}
\]
For completeness, choose \(M=\lceil1+|\omega|\rceil\) and \(W=\sqrt{1+\omega^2}\le M\). The first \(\min(K,M)\) terms are bounded by \((A-1)H_M\). For \(K>M\), the tail formula is
\[
R_A(K)K^{i\omega-1}-R_A(M)(M+1)^{i\omega-1}
+\sum_{k=M+1}^{K-1}R_A(k)[k^{i\omega-1}-(k+1)^{i\omega-1}].
\]
Its modulus is at most
\[
(A-1)\left[\frac{1+W}{M+1}+\frac{1-W}{K}\right]\le A-1.
\]
The derivative bound used here is \(|(x^{i\omega-1})'|=W/x^2\). The same identity with \(M\to\infty\), at fixed \(\omega\), proves convergence.

Define \(D_A(\omega)=\lim_KD_{A,K}(\omega)\). Absolute convergence initially on \(\Re s>1\), followed by bounded-partial-sum continuation to \(\Re s>0\), proves
\[
D_A(0)=\log A,\qquad
D_A(\omega)=(1-A^{i\omega})\zeta(1-i\omega)\quad(\omega\ne0).
\tag{3.2}
\]
The value at zero also follows directly from \(D_{A,AN}(0)=H_{AN}-H_N\). There is no subtraction of divergent infinite harmonic sums.

The actual signed residue approximants are
\[
H_{A,K}=\sum_{k\le K}\frac{v_A(k)}kT_k1,
\qquad \|H_{A,K}-R_A\|^2\le\frac{(A-1)^2}{K+1}.
\]
After dilation,
\[
T_mH_{A,K}=\sum_{k\le K}\frac{v_A(k)}kT_{mk}1,
\qquad
\|T_mH_{A,K}-T_mR_A\|^2\le\frac{m(A-1)^2}{K+1}.
\tag{3.3}
\]
There is no additional factor of \(m\) in the displayed sum: the jump size and threshold normalization cancel it.

At a finite \(K\), substitute the scalar Fourier expansion for \(s_{mk}(\ell)\). The sum in \(k\) is finite. Then (3.1) and \(C_{\ell h}=O_\ell(h^{-2})\) justify dominated convergence in \(h\) as \(K\to\infty\), while (3.3) identifies the actual Hilbert limit. Therefore
\[
\boxed{
a_\ell(QT_mR_A)=C_{\ell0}\log A+
\sum_{h\ne0}C_{\ell h}m^{i\omega_h}
(1-A^{i\omega_h})\zeta(1-i\omega_h).
}
\tag{3.4}
\]
This scalar frequency sum converges absolutely. Its dominating sequence is independent of \(m\), at fixed \(A,\ell\).

## 4. Absolute Hilbert convergence at fixed positive damping

Here is an elementary bound which independently supplies the needed convergence of the actual conductor sums. At each nonnegative dyadic depth, the integer tent formula has at most one nonzero boundary coordinate, with magnitude at most one. Negative depths vanish. Consequently
\[
\sum_{\ell\ge1}|s_n(\ell)|^2\le\log_2 n,
\quad
\|QT_n1\|\le\sqrt{1+\tfrac14\log_2 n}.
\tag{4.1}
\]
One may replace \(\log_2 n\) by \(1+\log_2 n\) without changing any following conclusion; the asserted sharper bound follows because the number of possible positive depths is at most \(\lfloor\log_2 n\rfloor\). Disjoint positive supports of the periodization ensure that contributions at distinct depths do not add within a coordinate.

Apply (3.3) with \(A=3\), followed by the contraction \(Q\). Set \(K=m\), use \(|v_3(k)|\le2\), and use (4.1). This proves
\[
\boxed{
\|QT_mR_3\|
\le2+2H_m\sqrt{1+\tfrac12\log_2m}
\ll(1+\log m)^{3/2}.
}
\tag{4.2}
\]

Fix \(\epsilon>0\), and set
\[
q=3^{-\epsilon},\quad
N_\epsilon=\frac{\zeta(1+\epsilon)(1-q)}{\log3}.
\]
The series
\[
G_\epsilon=N_\epsilon
\sum_{m\ge1}\sum_{j\ge0}
\frac{\mu(m)}{m^{1+\epsilon}}q^j QT_{m3^j}R_3
\tag{4.3}
\]
converges absolutely in \(\mathcal H\). Indeed, (4.2) bounds the sum of norms by a constant depending on \(\epsilon\) times
\[
\sum_{m\ge1}m^{-1-\epsilon}(1+\log m)^{3/2}
\sum_{j\ge0}q^j(1+j)^{3/2}<\infty.
\]
Likewise,
\[
A_\epsilon=(1-q)\sum_{j\ge0}q^jQT_{3^{j+1}}1
\]
converges absolutely by (4.1). Define
\[
C_\epsilon=1+QR_2/L-A_\epsilon,\qquad
E_\epsilon=G_\epsilon-C_\epsilon.
\tag{4.4}
\]
All these are actual Hilbert vectors. Block telescoping also gives \(\langle1,T_mf\rangle=\langle1,f\rangle\). The signed residue prefix and (3.2) therefore imply \(\langle1,QT_mR_A\rangle=\log A\). Consequently,
\[
\langle1,G_\epsilon\rangle=
\frac{N_\epsilon\log3}{\zeta(1+\epsilon)(1-q)}=1,
\qquad
\langle1,C_\epsilon\rangle=1+1-1=1.
\]
Thus \(\langle1,E_\epsilon\rangle=0\), and no mean energy is omitted in the energy formula below.

## 5. Exact arithmetic Fourier multiplier

Put \(z_h=e^{i\omega_h\log3}\). The absolute Hilbert sums in Section 4 permit coordinate extraction. For fixed \(\ell\), (3.1) and \(|m^{i\omega_h}|=|z_h|=1\) give an absolutely summable dominating triple series when (3.4), with \(A=3\), is substituted into (4.3). In particular,
\[
\sum_{h\ne0}|C_{\ell h}|\,[2+\log(2+|\omega_h|)]
\sum_m m^{-1-\epsilon}\sum_jq^j<\infty.
\]
Every frequency/conductor/geometric interchange in this step is therefore justified at fixed \(\epsilon,\ell\).

The standard absolutely convergent identity
\[
\sum_{m\ge1}\frac{\mu(m)m^{i\omega}}{m^{1+\epsilon}}
=\frac1{\zeta(1+\epsilon-i\omega)}
\]
and the geometric sum give
\[
a_\ell(G_\epsilon)=C_{\ell0}+
\sum_{h\ne0}C_{\ell h}
\frac{N_\epsilon\zeta(1-i\omega_h)}{\zeta(1+\epsilon-i\omega_h)}
\frac{1-z_h}{1-qz_h}.
\tag{5.1}
\]
The mean term is exactly \(C_{\ell0}\), because
\[
N_\epsilon\log3\,[\zeta(1+\epsilon)(1-q)]^{-1}=1.
\]

The absolutely convergent comparison series gives
\[
a_\ell(C_\epsilon)=C_{\ell0}-(1-q)
\sum_{h\in\mathbb Z}C_{\ell h}\frac{z_h}{1-qz_h}
=-(1-q)\sum_{h\ne0}C_{\ell h}\frac{z_h}{1-qz_h}.
\tag{5.2}
\]
The \(h=0\) contribution was included before it canceled.

Subtracting (5.2) from (5.1), then using the absolutely convergent identity \(C_{\ell0}+\sum_{h\ne0}C_{\ell h}=0\), proves
\[
\boxed{
a_\ell(E_\epsilon)=\sum_{h\ne0}C_{\ell h}F_{\epsilon h},\qquad
F_{\epsilon h}=
\left[\frac{N_\epsilon\zeta(1-i\omega_h)}
{\zeta(1+\epsilon-i\omega_h)}-1\right]
\frac{1-z_h}{1-qz_h}.
}
\tag{5.3}
\]
No \(h=0\) zeta ratio is being evaluated.

The sum in (5.3) is absolutely convergent for every fixed \(\epsilon>0,\ell\). For example, (3.1), \(|1-qz_h|\ge1-q\), and \(|1/\zeta(1+\epsilon-i\omega_h)|\le\zeta(1+\epsilon)\) bound its multiplier by
\[
|F_{\epsilon h}|\le
\frac{2N_\epsilon\zeta(1+\epsilon)}{1-q}
[2+\log(2+|\omega_h|)]+2.
\tag{5.4}
\]
The last constant 2 uses the exact cancellation-preserving inequality \(|(1-z)/(1-qz)|\le2/(1+q)\le2\). None of the constants in (5.4) is asserted uniform in \(\epsilon\).

## 6. Complete boundary energy: the valid order of limits

The actual Hilbert construction and the zero mean yield the exact identity
\[
\boxed{
\|E_\epsilon\|^2=
\frac14\sum_{\ell\ge1}
\left|\sum_{h\ne0}C_{\ell h}F_{\epsilon h}\right|^2<\infty.
}
\tag{6.1}
\]
This equality includes the complete boundary sum and every signed mixed term. It follows from the Hilbert decomposition after the coordinatewise identity, not from an unproved Hilbert-valued Fourier expansion.

For a fully explicit limit convention, let
\[
S_{\epsilon,\ell,H}=\sum_{0<|h|\le H}C_{\ell h}F_{\epsilon h}.
\]
Then
\[
\boxed{
\|E_\epsilon\|^2=
\frac14\lim_{B\to\infty}\lim_{H\to\infty}
\sum_{\ell=1}^{B}|S_{\epsilon,\ell,H}|^2.
}
\tag{6.2}
\]
The inner limit is justified by scalar absolute convergence and a finite coordinate sum. The outer limit is justified by nonnegative summation of the actual squared coordinates. The two limits have not been exchanged.

Equivalently, with the finite-coordinate Gram matrix
\[
\Gamma_B(h,k)=\frac14\sum_{\ell=1}^{B}
C_{\ell h}\overline{C_{\ell k}},
\]
the energy is
\[
\|E_\epsilon\|^2=
\lim_{B\to\infty}\lim_{H\to\infty}
\sum_{0<|h|,|k|\le H}
\Gamma_B(h,k)F_{\epsilon h}\overline{F_{\epsilon k}}.
\tag{6.3}
\]
At fixed \(B\), the double frequency sum is absolutely convergent. All off-diagonal Gram entries are retained.

## 7. Uniform arithmetic coefficients and discrepancy

From now on \(0<\epsilon\le1/2\), and every unspecified constant is
independent of \(\epsilon\), the positive integer \(A\), and the boundary
index. Constants may increase between estimates.

Define the Dirichlet function and its exact coefficients by
\[
\mathscr H_\epsilon(s)
=N_\epsilon\frac{\zeta(s)}{\zeta(s+\epsilon)}-1,\qquad
\alpha_\epsilon(n)=\sum_{d\mid n}\mu(d)d^{-\epsilon}
=\prod_{p\mid n}(1-p^{-\epsilon}),
\]
\[
b_\epsilon(n)=N_\epsilon\alpha_\epsilon(n)-\mathbf1_{n=1},
\qquad
\kappa_\epsilon=\frac{N_\epsilon}{\zeta(1+\epsilon)}
=\frac{1-3^{-\epsilon}}{\log3}.
\tag{7.1}
\]
The product for \(n=1\) is the empty product, equal to one. Multiplication
of absolutely convergent Dirichlet series proves
\(\mathscr H_\epsilon(s)=\sum_n b_\epsilon(n)n^{-s}\) for \(\Re s>1\).
Thus the Möbius cancellation is incorporated exactly, before any estimate.

The Laurent expansion of zeta at one shows that \(N_\epsilon\) extends
smoothly to \(\epsilon=0\), with \(N_0=1\). On the stated interval,
\[
|N_\epsilon|\le C,\quad |N_\epsilon-1|\le C\epsilon,
\quad 0<\kappa_\epsilon\le\epsilon.
\]
For \(n\ge2\), choose a prime divisor \(p\). Every factor in (7.1)
lies in \([0,1]\), and
\[
0\le\alpha_\epsilon(n)\le1-p^{-\epsilon}
\le\epsilon\log p\le\epsilon\log n.
\]
It follows that
\[
\boxed{\quad
\sup_n|b_\epsilon(n)|\le C,\qquad
\sum_{n\ge1}\frac{|b_\epsilon(n)|^2}{n^2}\le C\epsilon^2.
\quad}
\tag{7.2}
\]
The term at \(n=1\) is \(N_\epsilon-1\) and is included.

The one substantive external analytic input is the classical
unconditional Mertens estimate
\[
M(x):=\sum_{n\le x}\mu(n)
\ll x\exp(-c\sqrt{\log(2x)}),\qquad x\ge1.
\tag{7.3}
\]
An explicit modern version is proved by
[Lee and Leong, *New explicit bounds for Mertens function and the reciprocal
of the Riemann zeta-function*, version 4](https://arxiv.org/abs/2208.06141v4).
Only (7.3), with some positive absolute constants, is used here.

We record the uniform consequence rather than treating uniformity in
\(\epsilon\) as automatic. Partial summation gives
\[
M_\epsilon(x):=\sum_{n\le x}\mu(n)n^{-\epsilon}
=x^{-\epsilon}M(x)
+\epsilon\int_1^x M(u)u^{-\epsilon-1}\,du
\ll x^{1-\epsilon}e^{-c_1\sqrt{\log(2x)}}.
\tag{7.4}
\]
This holds uniformly for \(0\le\epsilon\le1/2\): split the integral at
\(\sqrt x\), use \(1-\epsilon\ge1/2\), and decrease \(c_1>0\) if necessary.

Let \(\mathcal A_\epsilon(x)=\sum_{n\le x}\alpha_\epsilon(n)\) and
\(y=\sqrt x\). Splitting the pairs \(dk\le x\) at \(d=y\) gives
\[
\mathcal A_\epsilon(x)
=x\sum_{d\le y}\frac{\mu(d)}{d^{1+\epsilon}}+O(y)
+\sum_{k\le x/y}\bigl[M_\epsilon(x/k)-M_\epsilon(y)\bigr].
\tag{7.5}
\]
Indeed, the \(d\le y\) part uses
\(\lfloor x/d\rfloor=x/d+O(1)\), with total error at most \(y\).
For the last sum, \(x/k\ge y\), so (7.4) and
\[
\sum_{k\le y}k^{-1+\epsilon}
\le y^\epsilon(1+\log y)
\]
bound its modulus by
\[
Cx(1+\log(2x))e^{-c_1\sqrt{\log(2\sqrt x)}}.
\]
For the tail of the first Dirichlet sum, partial summation of (7.4) gives
\[
\left|\sum_{d>y}\frac{\mu(d)}{d^{1+\epsilon}}\right|
\le C y^{-\epsilon}(1+\sqrt{\log(2y)})
e^{-c_1\sqrt{\log(2y)}}.
\tag{7.6}
\]
This is uniform even as \(\epsilon\downarrow0\). For positive
\(\epsilon\), the full sum is \(1/\zeta(1+\epsilon)\).
Absorbing the logarithmic factors by decreasing the exponential constant,
(7.5)–(7.6) prove
\[
\mathcal A_\epsilon(x)
=\frac{x}{\zeta(1+\epsilon)}
+O\!\left(xe^{-c_2\sqrt{\log(2x)}}\right).
\tag{7.7}
\]

For the exact lower-endpoint convention needed below, put
\[
P_\epsilon(x)=\sum_{n\le x}b_\epsilon(n)-\kappa_\epsilon(x-1),
\qquad x\ge1.
\]
It is the cumulative mass, including the atom at one, of
\[
d\nu_\epsilon(x)=\sum_{n\ge1}b_\epsilon(n)\delta_n
-\kappa_\epsilon\mathbf1_{[1,\infty)}(x)\,dx.
\]
Equation (7.7) implies, for a fixed decreasing function
\(\eta(x)=e^{-c_3\sqrt{\log(2x)}}\),
\[
\boxed{|P_\epsilon(x)|\le Cx\eta(x),\qquad
\int_1^\infty\eta(x)\frac{dx}{x}<\infty.}
\tag{7.8}
\]
The change from subtracting \(\kappa_\epsilon x\) to subtracting
\(\kappa_\epsilon(x-1)\) adds a bounded constant, absorbed in (7.8).
In particular \(P_\epsilon(1)=b_\epsilon(1)\).

## 8. The integer-dilation estimate in the complete boundary space

For an integer \(A\ge1\) and \(\lambda>0\), define a shell vector by
\[
D_{\epsilon,\lambda}(\ell)
=\sum_{n\ge1}\frac{b_\epsilon(n)}n\,\tau_\ell(\lambda n)
-\kappa_\epsilon\int_1^\infty\tau_\ell(\lambda x)\frac{dx}{x}.
\tag{8.1}
\]
For each coordinate the sum and integral have compact support. We will
construct the following sum by absolute convergence of its shell norms:
\[
S_\epsilon(A)=\sum_{d\in\mathbb Z}D_{\epsilon,A/2^d}.
\tag{8.2}
\]
There are three regions.

**Negative depths \(d<0\).** Here \(\lambda=A2^{-d}\) is an even integer.
The tents vanish on every even integer, so
\(\tau_\ell(\lambda n)=0\) for all integers \(n,\ell\). The remaining
continuous part is bounded by \(C\kappa_\epsilon/\ell\), because
\[
\int_1^\infty\tau_\ell(\lambda x)\frac{dx}{x}
\le\int_{2\ell}^{2\ell+2}\tau_\ell(u)\frac{du}{u}
\le\frac1{2\ell}.
\]
It vanishes unless \(2\ell+2\ge\lambda\). Consequently
\[
\|D_{\epsilon,\lambda}\|_{\ell^2}
\le C\frac{\kappa_\epsilon}{\sqrt\lambda},\qquad \lambda\ge2,
\]
and the total over \(d<0\) is at most \(C\epsilon/\sqrt A\).

**Nonnegative depths with \(\lambda\ge1\).** There are at most
\(1+\lfloor\log_2 A\rfloor\) of these. The positive support of
\(\tau_\ell(\lambda n)\), as an interval in \(n\), has length
\(2/\lambda\le2\), and hence contains at most two integers. For each \(n\),
at most one \(\ell\) has a positive tent value. Cauchy–Schwarz and (7.2)
therefore give
\[
\sum_{\ell\ge1}
\left|\sum_n\frac{b_\epsilon(n)}n\tau_\ell(\lambda n)\right|^2
\le2\sum_n\frac{|b_\epsilon(n)|^2}{n^2}
\le C\epsilon^2.
\]
The continuous part has norm at most \(C\kappa_\epsilon\), by the preceding
\(1/(2\ell)\) bound. Thus each such shell has norm at most \(C\epsilon\).

**Large depths with \(\lambda<1\).** Put \(t=\lambda^{-1}>1\) and
\[
f_{\ell,t}(x)=\frac{\tau_\ell(x/t)}x.
\]
Its support is \([2\ell t,(2\ell+2)t]\), its endpoint values vanish,
and almost everywhere on its support
\[
|f'_{\ell,t}(x)|\le\frac1{tx}+\frac1{x^2}.
\]
Stieltjes integration by parts, retaining the atom convention of (7.8),
gives
\[
D_{\epsilon,1/t}(\ell)
=-\int_{2\ell t}^{(2\ell+2)t}P_\epsilon(x)f'_{\ell,t}(x)\,dx.
\]
Since \(x\ge2\ell t\ge t\) and the support has length \(2t\), (7.8) implies
\[
|D_{\epsilon,1/t}(\ell)|\le C\eta(t).
\]
Independently, boundedness of \(b_\epsilon\), the at most \(2t+1\)
integers in the support, and \(x\ge2\ell t\) imply
\[
|D_{\epsilon,1/t}(\ell)|\le C/\ell.
\]
Combining these two bounds and splitting the sum at
\(\ell\asymp\eta(t)^{-1}\) yields
\[
\|D_{\epsilon,1/t}\|_{\ell^2}^2
\le C\sum_{\ell\ge1}\min\{\ell^{-2},\eta(t)^2\}
\le C\eta(t).
\tag{8.3}
\]
The successive \(t=2^d/A>1\) form a geometric sequence whose first
term lies in \((1,2]\). Their shell norms have the uniform summable
majorant \(C\exp(-c_4\sqrt{r+1})\), \(r=0,1,\ldots\).

Summing the three regions proves both the norm convergence of (8.2) and
\[
\boxed{\|S_\epsilon(A)\|_{\ell^2}
\le C(1+\epsilon\log A),\qquad A\in\mathbb N_{\ge1}.}
\tag{8.4}
\]
Integer \(A\) is essential in the negative-depth argument.

For each fixed coordinate the shell construction also equals the
compensated arithmetic periodization
\[
S_\epsilon(A)_\ell
=\lim_{X\to\infty}
\left[
\sum_{n\le X}\frac{b_\epsilon(n)}n\Psi_\ell(An)
-\kappa_\epsilon\int_1^X\Psi_\ell(Ax)\frac{dx}{x}
\right].
\tag{8.5}
\]
To see this without an exchange of divergent terms, first truncate at
\(X\), where the periodization has only finitely many relevant shells.
Their positive supports in \(x\) are disjoint, since
\((\ell+1)/\ell\le2\); at most one shell is cut at \(X\).
All complete shells agree with (8.2). For the cut shell, integration
by parts gives a boundary term \(P_\epsilon(X)f(X)\) and an integral
of \(P_\epsilon f'\). At fixed \(\ell,A\), the left endpoint of that
shell is at least \(X/2\), and both contributions are
\(O_\ell(\eta(X/2))\). They tend to zero. The remaining complete-shell
tail tends to zero by the norm convergence already proved.

## 9. Fourier identification with the pole and constant retained

For \(\Re s\ge1\) define the compensated partial transform
\[
J_\epsilon^X(s)=\sum_{n\le X}b_\epsilon(n)n^{-s}
-\kappa_\epsilon\int_1^Xx^{-s}\,dx.
\]
The inclusive atom at one gives the exact formula
\[
J_\epsilon^X(s)=P_\epsilon(X)X^{-s}
+s\int_1^X P_\epsilon(x)x^{-s-1}\,dx.
\tag{9.1}
\]
For \(\Re s=1\), (7.8) makes its limit well defined:
\[
J_\epsilon(s)=s\int_1^\infty P_\epsilon(x)x^{-s-1}\,dx.
\tag{9.2}
\]
For \(\Re s>1\), direct integration shows
\[
J_\epsilon(s)=\mathscr H_\epsilon(s)-\frac{\kappa_\epsilon}{s-1}.
\tag{9.3}
\]
Taking limits from \(\Re s>1\), dominated by (7.8), therefore yields
\[
J_{\epsilon,h}:=J_\epsilon(1-i\omega_h)
=\mathscr H_\epsilon(1-i\omega_h)
+\frac{\kappa_\epsilon}{i\omega_h},\qquad h\ne0.
\tag{9.4}
\]
At \(h=0\), retain the finite part
\[
K_\epsilon:=J_\epsilon(1)
=\int_1^\infty P_\epsilon(x)\frac{dx}{x^2},\qquad |K_\epsilon|\le C.
\tag{9.5}
\]
In particular, the pole is subtracted before taking the zero-frequency
limit. No zeta value at its pole is inserted into a frequency sum.

We need a frequency bound uniform also in the cutoff. The coefficient
bound in (7.2) gives
\[
|J_\epsilon^X(1-i\omega)|\le C(1+\log X).
\]
For \(\Omega=2+|\omega|\), choose
\(Y=\exp(K\log^2\Omega)\), where the absolute constant \(K\) is
sufficiently large. If \(X\le Y\), the preceding estimate is
\(O(1+\log^2\Omega)\). If \(X>Y\), use (9.1) for the tail:
\[
|J_\epsilon^X(1-i\omega)-J_\epsilon^Y(1-i\omega)|
\le C\eta(X)+C\eta(Y)
+C(1+|\omega|)\int_Y^\infty\eta(x)\frac{dx}{x}.
\]
The integral is bounded by
\(C(1+\sqrt{\log(2Y)})e^{-c_3\sqrt{\log(2Y)}}\).
The choice of \(K\) makes the displayed tail uniformly bounded. Hence
\[
\boxed{
\sup_{X\ge1,\,0<\epsilon\le1/2}
|J_\epsilon^X(1-i\omega)|
\le C[1+\log^2(2+|\omega|)].
}
\tag{9.6}
\]

The integral formula and explicit coefficient formula in Section 2 give
the useful simultaneous bound
\[
|C_{\ell h}|\le C\min\{\ell^{-1},\ell/h^2\},\qquad h\ne0,
\quad 0\le C_{\ell0}\le\frac1{2\ell L}.
\tag{9.7}
\]
At finite \(X\), substitute the absolutely and uniformly convergent
scalar Fourier expansion into (8.5). Its result is exactly
\(\sum_h C_{\ell h}A^{i\omega_h}J_\epsilon^X(1-i\omega_h)\).
For fixed \(\ell\), (9.6)–(9.7) give a summable majorant independent of
\(X,\epsilon,A\). Dominated convergence proves
\[
S_\epsilon(A)_\ell
=K_\epsilon C_{\ell0}
+\sum_{h\ne0}C_{\ell h}A^{i\omega_h}
\left[\mathscr H_\epsilon(1-i\omega_h)
+\frac{\kappa_\epsilon}{i\omega_h}\right].
\tag{9.8}
\]
This is a coordinatewise argument. It does not assert absolute
convergence of frequency-column norms in \(\ell^2\).

Let
\[
W(A)_\ell=\sum_{h\ne0}
\frac{C_{\ell h}A^{i\omega_h}}{i\omega_h}.
\]
Splitting at \(|h|=\ell\) in (9.7) gives
\[
|W(A)_\ell|
\le C\sum_{h\ge1}\frac{\min(\ell^{-1},\ell h^{-2})}{h}
\le C\frac{\log(\ell+2)}{\ell}.
\]
Therefore
\[
\sup_{A>0}\|W(A)\|_{\ell^2}<\infty,\qquad
\|(C_{\ell0})_{\ell\ge1}\|_{\ell^2}<\infty.
\tag{9.9}
\]

Define the scalar coordinates
\[
V_\epsilon(A)_\ell
=\sum_{h\ne0}C_{\ell h}A^{i\omega_h}
\mathscr H_\epsilon(1-i\omega_h).
\tag{9.10}
\]
They converge absolutely, by (9.4) and (9.6). Equations (9.8)–(9.9)
identify their complete vector as
\[
V_\epsilon(A)
=S_\epsilon(A)-K_\epsilon(C_{\ell0})_{\ell\ge1}
-\kappa_\epsilon W(A).
\]
We have thus proved the central estimate
\[
\boxed{
\|V_\epsilon(A)\|_{\ell^2}\le C(1+\epsilon\log A),
\qquad 0<\epsilon\le1/2,\quad A\in\mathbb N_{\ge1}.
}
\tag{9.11}
\]
Both the constant Fourier term and the pole correction are present.

## 10. The full signed arithmetic energy bound

By (9.11), the following series converges absolutely in \(\ell^2\):
\[
V_\epsilon(1)
-(1-q)\sum_{j\ge0}q^jV_\epsilon(3^{j+1}).
\tag{10.1}
\]
At each fixed coordinate, (9.6)–(9.7) also justify interchange of the
frequency sum and the geometric sum. The multiplier is exactly
\[
\mathscr H_\epsilon(1-i\omega_h)
\left[1-(1-q)\sum_{j\ge0}q^jz_h^{j+1}\right]
=\mathscr H_\epsilon(1-i\omega_h)\frac{1-z_h}{1-qz_h}.
\]
By (5.3), (10.1) is therefore the actual boundary vector
\[
e_\epsilon=(a_\ell(E_\epsilon))_{\ell\ge1}.
\]
All signed arithmetic and comparison terms were identified before
taking norms. The triangle inequality now applies to actual
\(\ell^2\) vectors, and (9.11) gives
\[
\begin{aligned}
\|e_\epsilon\|_{\ell^2}
&\le C+
C(1-q)\sum_{j\ge0}q^j[1+\epsilon(j+1)\log3]\\
&=C\left[2+\frac{\epsilon\log3}{1-3^{-\epsilon}}\right].
\end{aligned}
\]
For \(u=\epsilon\log3\le(\log3)/2\),
\(1-e^{-u}\ge ue^{-u}\ge u/\sqrt3\). Consequently
\[
\boxed{
\sup_{0<\epsilon\le1/2}
\|E_\epsilon\|_{\mathcal H}^2
=
\sup_{0<\epsilon\le1/2}
\frac14\sum_{\ell\ge1}
\left|\sum_{h\ne0}C_{\ell h}
\left[
\frac{N_\epsilon\zeta(1-i\omega_h)}
{\zeta(1+\epsilon-i\omega_h)}-1
\right]\frac{1-z_h}{1-qz_h}\right|^2
<\infty.
}
\tag{10.2}
\]
The equality uses the zero mean proved in Section 4. This controls
the entire boundary sum, including every off-diagonal Gram term in
(6.3); no frequency diagonalization has been used.

## 11. Vanishing coordinates and the remaining RH obligation

There is also a weak-convergence consequence. For every fixed \(n\),
\(b_\epsilon(n)\to0\) as \(\epsilon\downarrow0\), and
\(\kappa_\epsilon\to0\). Thus \(P_\epsilon(x)\to0\) for each fixed \(x\).
The common integrable majorant in (7.8) and (9.2) imply
\(J_\epsilon(1-i\omega_h)\to0\) for each fixed \(h\). Equation (9.4)
then gives
\(\mathscr H_\epsilon(1-i\omega_h)\to0\) for \(h\ne0\).

By (9.6), these values have the common bound
\(C[1+\log^2(2+|h|)]\). Together with (9.7) and
\[
\left|\frac{1-z_h}{1-qz_h}\right|\le2,
\]
dominated convergence in (5.3) proves
\[
a_\ell(E_\epsilon)\longrightarrow0\qquad\text{for every fixed }\ell.
\]
The complete boundary decomposition and the uniform norm bound
therefore imply
\[
\boxed{E_\epsilon\rightharpoonup0\quad\text{in }Q\mathcal H.}
\tag{11.1}
\]
Indeed, finite boundary combinations have vanishing pairings, and
their density, together with the common norm bound, extends this
to every test vector in \(Q\mathcal H\).

The proved results are the exact arithmetic Fourier bridge, the
complete signed quotient energy bound \(O(1)\), and weak convergence
of the specified remainder. Mazur’s lemma consequently gives convex combinations of arbitrarily
small-\(\epsilon\) tails converging strongly to zero in the quotient
space. The proof gives no \(O(\epsilon)\) energy rate or strong
convergence of the original family \(E_\epsilon\). Nor does it construct the
complementary physical component, the full legal two-seed witnesses,
or the remaining Mellin and separating identifications required by
the RH route in the handoff. Those are separate obligations.
In particular, (10.2) and (11.1) are not a proof of RH.

The integer support used in Section 8 is substantive: for general
real \(x\), the unrestricted vector \((\Psi_\ell(x))_\ell\) need not
belong to \(\ell^2\). For example, at \(x=4/3\), taking
\(\ell_j=\lfloor2^{j+1}/3\rfloor\), \(j\ge1\), gives infinitely many
distinct coordinates with \(\Psi_{\ell_j}(4/3)=2/3\).
The shell proof avoids assuming a boundary-valued Fourier expansion
of that unrestricted continuous family.
