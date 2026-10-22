# A precise Hilbert–Pólya kernel target from the Mellin DPP

Date: 2026-09-28. Status: paper derivations and literature audit, not Lean formalization. No unconditional Hilbert–Pólya operator is constructed here. The kernel positivity condition below is equivalent to RH, so restating it is not partial progress toward RH. Its use is to specify exactly what a DPP-based operator construction would need to prove.

## 1. Conventions and the established shifted operators

Write

\[
\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad X(z)=\xi(\tfrac12-iz).
\]

Thus \(X\) is real entire and even; RH says precisely that all its zeros are real. Define \(E^\#(z)=\overline{E(\bar z)}\). For \(\omega>0\), put

\[
E_\omega(z)=X(z+i\omega)=\xi(\tfrac12+\omega-iz),
\quad
A_\omega=\frac{E_\omega+E_\omega^\#}{2},
\quad
B_\omega=\frac{i(E_\omega-E_\omega^\#)}2.
\]

Lagarias proves the Hermite–Biehler inequality for \(E_\omega\) unconditionally when \(\omega\ge 1/2\). The associated de Branges multiplication operator has self-adjoint extensions with discrete spectra at the zeros of the real boundary combinations of \(A_\omega,B_\omega\). These shifted spectra are not the zeros of \(X\). For each fixed shift greater than 1/2, the limiting normalized spacing is one unconditionally; extension to smaller positive shifts uses RH. See [1], Sections 2, 4 and 6.

Suzuki makes a corresponding canonical system explicit for \(\omega>1\): its Hamiltonian is

\[
H_\omega(a)=\operatorname{diag}(m_\omega(a)^{-2},m_\omega(a)^2),
\qquad
m_\omega(a)=
\frac{\det(1+\mathsf H_{\omega,a})}
{\det(1-\mathsf H_{\omega,a})},
\]

where \(\mathsf H_{\omega,a}\) is a truncated arithmetic Hankel integral operator. Innerness of
\(\Theta_\omega=E_\omega^\#/E_\omega\) for every \(\omega>0\) is RH-equivalent. Modulus one on the real boundary is unconditional and does not establish innerness; analyticity and contractivity in the upper half-plane are essential. See [2], Proposition 1.2 and Theorem 2.3. One must not claim that the explicit Hamiltonian construction is unconditional for arbitrarily small positive shifts.

## 2. Why a direct zero-shift limit degenerates

The algebraic de Branges kernel is

\[
K_\omega(z,w)=
\frac{E_\omega(z)\overline{E_\omega(w)}
-E_\omega^\#(z)\overline{E_\omega^\#(w)}}
{2\pi i(\bar w-z)}.
\]

All removable divided differences in this note are filled in analytically. At \(\omega=0\), \(E_0=E_0^\#=X\), so this kernel is identically zero. A direct claim that the unrenormalized de Branges spaces converge to the desired spectral space would therefore miss the degeneration.

Taylor expansion instead gives a nonzero limit:

\[
\boxed{
\frac{K_\omega(z,w)}\omega\longrightarrow
L(z,w):=
\frac{X'(z)X(\bar w)-X(z)X'(\bar w)}
{\pi(\bar w-z)}.}
\tag{2.1}
\]

The convergence is locally uniform, with error \(O(\omega^2)\) on each compact set. To check it, use
\(X(z\pm i\omega)=X(z)\pm i\omega X'(z)+O(\omega^2)\). The numerator of \(K_\omega\) is odd in \(\omega\), so its first term is
\(2i\omega[X'(z)X(\bar w)-X(z)X'(\bar w)]\), with cubic remainder. Uniformity across the removable diagonal follows from the analytic divided-difference formula or Cauchy's integral formula.

There is an equivalent structure-function renormalization:

\[
F_\omega=A_\omega-i B_\omega/\omega
\longrightarrow E_*(z):=X(z)+iX'(z).
\tag{2.2}
\]

The kernel of \(F_\omega\) equals \(K_\omega/\omega\). Positive rescaling of the second real component preserves the Hermite–Biehler inequality, since the squared-modulus difference scales by \(1/\omega\). Thus \(F_\omega\) is Hermite–Biehler exactly when \(E_\omega\) is. Formula (2.2) avoids the trivial limiting kernel but does not by itself prove any convergence of self-adjoint operator domains or resolvents.

The candidate \(E_*=X+iX'\) is already present in the literature: in the \(s\)-coordinate it is \(\xi(s)+\xi'(s)\), \(s=1/2-iz\). Suzuki [3] discusses this Lagarias structure function and its conditional spectral interpretation. We do not claim its discovery.

## 3. Exact positivity criterion, with proof

**Proposition.** The following are equivalent:

1. RH.
2. \(L\) is a positive semidefinite kernel on \(\mathbb C\).
3. \(L(z,z)\ge0\) for every \(z\) in the upper half-plane.
4. \(E_*=X+iX'\) satisfies strict Hermite–Biehler dominance in the upper half-plane, allowing real common factors to be removed if necessary.

**Proof that RH implies kernel positivity.** Under RH the paired Hadamard product is

\[
X(z)=X(0)\prod_{\gamma>0}
\left(1-\frac{z^2}{\gamma^2}\right)^{m_\gamma},
\qquad
\sum_{\gamma>0}\frac{m_\gamma}{\gamma^2}<\infty,
\]

where \(\gamma\) ranges over distinct positive zeros. Logarithmic differentiation, paired across \(\pm\gamma\), gives

\[
\frac{X'(z)}{X(z)}-
\frac{X'(\bar w)}{X(\bar w)}
=(\bar w-z)\sum_{\gamma\in\Gamma}
\frac{m_\gamma}{(z-\gamma)(\bar w-\gamma)},
\]

where \(\Gamma\) contains the distinct positive and negative real zeros. Hence

\[
\boxed{L(z,w)=\frac1\pi
\sum_{\gamma\in\Gamma}m_\gamma
\frac{X(z)}{z-\gamma}
\overline{\frac{X(w)}{w-\gamma}}.}
\tag{3.1}
\]

Each quotient in (3.1) is entire. The series converges locally uniformly, since its tail is bounded by a compact-dependent constant times \(\sum m_\gamma/\gamma^2\). It is a Gram kernel, proving positivity.

**Proof that diagonal positivity implies RH.** Away from zeros of \(X\), for \(y=\operatorname{Im}z>0\),

\[
L(z,z)=-\frac{|X(z)|^2}{\pi y}
\operatorname{Im}\frac{X'(z)}{X(z)}.
\tag{3.2}
\]

If \(\rho\) is an upper-half-plane zero of multiplicity \(m\), then
\(X'/X(z)=m/(z-\rho)+O(1)\) near \(\rho\). Taking
\(z=\rho-i\varepsilon\) with positive sufficiently small \(\varepsilon<\operatorname{Im}\rho\) yields

\[
\operatorname{Im}(X'/X)(z)=m/\varepsilon+O(1)>0.
\]

Equation (3.2) then gives \(L(z,z)<0\), a contradiction. Real-entire symmetry rules out lower-half-plane zeros as well. This proves RH without a simplicity assumption.

Finally,

\[
|E_*(z)|^2-|E_*^\#(z)|^2
=4\pi(\operatorname{Im}z)L(z,z).
\tag{3.3}
\]

Under RH the right side is strictly positive in the upper half-plane by (3.1). Conversely, strict dominance implies nonnegative diagonal and hence RH. The remaining implication from kernel positivity to diagonal positivity is immediate. QED.

The real diagonal is the first Laguerre expression

\[
L(t,t)=\frac{X'(t)^2-X(t)X''(t)}\pi.
\tag{3.4}
\]

Positivity only of (3.4) on the real line is not asserted to be equivalent to RH here. The proposition requires the complex upper-half-plane diagonal, or the entire positive kernel.

## 4. Operator interpretation and multiplicity boundary

If the positivity problem is solved independently, \(L\) is the de Branges kernel for \(E_*\). Its real components are \(A=X\) and \(B=-X'\). The established de Branges extension theory then supplies the relevant spectral route, with the usual dense-domain verification and boundary choice. Writing this kernel down does not establish the required Hilbert space or self-adjoint realization unconditionally.

Multiplicity requires care. At a real zero \(\gamma\) of \(X\) of order \(m\), both \(X\) and \(X'\) share a factor of order \(m-1\); consequently \(E_*\) also has that real factor. After factoring it out, the real component has a simple zero at \(\gamma\). The scalar de Branges construction therefore records distinct spectral locations, not automatically their original zeta multiplicities. A Hilbert–Pólya claim with multiplicity would require an additional construction. Assuming simplicity silently would be invalid.

The factorization (3.1) is a proof under RH, not a noncircular construction: its feature labels already assume the desired real zeros. A useful arithmetic construction would have to produce the same kernel from prime/conductor data without assuming RH or inserting its spectral zeros.

## 5. The exact mismatch with the existing Mellin DPP

The finite-rank Mellin DPP kernels have the form

\[
\mathcal K_N(t,u)=E(t)\overline{E(u)}\,C_N(t,u),
\qquad
E(t)=\frac{\zeta(1/2+it)}{1/2+it},
\]

with \(C_N\) a finite Gram kernel. At every critical-line zero \(\gamma\),

\[
\mathcal K_N(\gamma,\gamma)=0\quad\text{for every }N.
\]

At a simple zero of \(X\), however,

\[
L(\gamma,\gamma)=X'(\gamma)^2/\pi>0.
\]

Thus no scalar rescaling of the unmodified finite DPP kernels can converge pointwise to \(L\) on a set containing a simple critical zero. This remains true even for divergent scalar rescalings: each finite-stage value at that point is exactly zero. Multiplication by fixed finite weights also preserves the obstruction.

A viable bridge therefore needs to change the features, for example through derivatives or confluent divided differences, rather than merely renormalizing the existing projection kernels. Differentiated Gram kernels remain positive and can remove a simple common zero, but no identity equating such a limit with \(L\) has been proved here.

The concrete research obligation is to find arithmetic feature maps \(\Phi_N(z)\), obtained without knowing the zero set, such that

\[
\langle\Phi_N(z),\Phi_N(w)\rangle\longrightarrow L(z,w)
\]

with justified convergence, ideally locally uniform on complex compact sets. Positivity of the finite Gram matrices is automatic; identifying this particular limit is the difficult missing assertion. Proving that assertion would prove RH, not just an intermediate conditional result.

## References

1. J. C. Lagarias, *Zero Spacing Distributions for Differenced L-Functions*, arXiv:math/0601653, https://arxiv.org/pdf/math/0601653. Sections 2, 4 and 6.
2. M. Suzuki, *A Canonical System of Differential Equations Arising from the Riemann Zeta-Function*, arXiv:1204.1827, https://arxiv.org/pdf/1204.1827. Proposition 1.2 and Theorem 2.3.
3. M. Suzuki, *Li Coefficients as Norms of Functions in a Model Space*, arXiv:2301.05779, https://arxiv.org/pdf/2301.05779. Introduction, including the discussion of Lagarias's structure function.
