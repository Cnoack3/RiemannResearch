# Attempt to prove derivative compatibility vanishing — 29 September 2026

## Status and exact target

The requested unconditional vanishing has not been proved. This continuation
tests arithmetic, adjoint, sieve, and dilation routes against the actual
canonical projections. All results classified below as established are Lean
declarations; none assumes the missing vanishing.

Write \(g_j(k)=(k\bmod j)/j\), with coordinate zero anchored, and
\[
F_N=\sum_{j=2}^N c_{N,j}g_j,\quad c_N=G_N^{-1}b_N,\quad
r_\infty=1-P_V1,\quad D=\|r_\infty\|^2.
\]
The still-open input is, for every fixed \(j\ge2\),
\[
h_N(j)=\langle\Delta g_j,\Delta(1-F_N)\rangle\longrightarrow0.
\]
Repository stage n corresponds to N=n+1. The preceding checked work proves
that this input implies full legal norm convergence and Mathlib's RH.

## 1. Exact adjoint calculation: the normal equation leaves a signed term

DerivativeAdjointRows.lean constructs the actual Hilbert adjoint row.
For k>=1,
\[
(\Delta^*u)(k)=u(k)-\frac{k}{k+2}u(k+1),
\]
and hence
\[
(\Delta^*\Delta g_j)(k)
=\frac{2}{j(k+2)}
-\mathbf1_{j\mid k}+\frac{k}{k+2}\mathbf1_{j\mid k+1}.
\]
The exact mismatch is
\[
h_N(j)=\langle1-F_N,\Delta^*\Delta g_j\rangle.
\]
This test is not supplied as a member of the legal span by the existing
dilation invariance theorems.

At conductor two, the checked endpoint fixedMismatch_first_limit_exact is
\[
\boxed{
h_\infty(2)=-D-\left\langle r_\infty,
  \frac{4g_2-1}{k+2}\right\rangle.}
\]
The displayed sequence is interpreted on positive coordinates and anchored
at zero. The legal normal equation removes the unweighted g2 term.
It does not remove the remaining weighted signed correlation.
No estimate or sign proving its required value -D was obtained.

## 2. Genuine unconditional vanishing for the explicit Möbius source

Let
\[
A_N=-\sum_{d=1}^N\mu(d)g_d,\qquad
\rho_N=1-A_N,\qquad m_N=\sum_{d=1}^N\frac{\mu(d)}d.
\]
NaturalMobiusDerivativeTests.lean retains the complete arithmetic jump:
\[
\Delta\rho_N(1)=m_N,\qquad
\Delta\rho_N(k)=m_N-\sum_{\substack{d\le N\\d\mid k}}\mu(d)
\quad(k\ge2).
\]
For N>=1, \(|\Delta\rho_N(k)|\le1+\tau(k)\). Existing PNT gives pointwise
convergence to zero, and the established divisor-count Dirichlet series
makes \(\sum_k w_k(1+\tau(k))\) finite. Dominated convergence therefore proves
\[
\boxed{\langle\Delta\rho_N,u\rangle\to0}
\]
for every Hilbert vector u with bounded physical coordinates. A more general
summable weighted-test hypothesis is also exposed.

The continuation NaturalMobiusDerivativeConvergence.lean strengthens this to
the actual full Hilbert limit
\[
\boxed{\Delta\rho_N\longrightarrow0,\qquad
\|\Delta\rho_N\|^2\longrightarrow0.}
\]
NumberTheory/DivisorCountSquareSummability.lean proves
\(\tau(k)\le2\sqrt{k}\), hence square summability from the established
divisor-count Dirichlet series at exponent 3/2. In particular,
\(\sum_k w_k(1+\tau(k))^2<\infty\). Dominated convergence now retains
every coordinate, including the first-site boundary, and permits every fixed
Hilbert test without a physical boundedness hypothesis. The endpoint is
rawMobiusDerivativeResidual_tendsto_zero, with no RH assumption.

In particular, the full signed derivative row for coefficients -mu vanishes:
\[
\boxed{
\frac1{2j}+\sum_{d=2}^N\mu(d)
       \langle\Delta g_j,\Delta g_d\rangle\longrightarrow0.}
\]
This is raw_derivative_signed_row_tendsto_zero. The actual optimizer has the
different coefficients \(c_N=-\mu_N+e_N\), where
\(e_N=G_N^{-1}(b_N+G_N\mu_N)\). The checked full matrix comparison is
\[
\boxed{h_N=d_N+D_N\mu_N-D_Ne_N.}
\]
The raw term has a checked vanishing provider. Control of the full signed
correction \(D_Ne_N\) is still missing. The new strong limit identifies the
precise possible obstruction. At repository stage n, write
\(u_n=\Delta(\mathrm{correctionSynthesis}(n))\) and
\(v_n=\mathrm{derivativeResidual}(n)\). The complete exact identities are
\[
\Delta\rho_{n+1}=v_n+u_n,\qquad
\|\Delta\rho_{n+1}\|^2
=\|v_n\|^2+2\langle v_n,u_n\rangle+\|u_n\|^2.
\]
The checked strong limits give
\[
u_n\to-\Delta r_\infty,\qquad
\|u_n\|^2\to q,\qquad
\langle v_n,u_n\rangle\to-q,
\quad q=\|\Delta r_\infty\|^2.
\]
Thus the raw energy vanishes through the exact cancellation q-2q+q=0.
This does not establish q=0. No signed term or norm-square remainder is
discarded.

## 3. Quantitative coercivity specific to the canonical limiting residual

ResidualDerivativeCoercivity.lean first proves, for every Hilbert vector f,
\[
\|\Delta f\|^2=\frac{f(1)^2}{2}
+\|\Delta f-f(1)\delta_1\|^2.
\]
For the actual canonical residual, put
\[
R=\left\|r_\infty-\frac{\sqrt2}{2}T_2r_\infty\right\|^2,\qquad
T=\Delta r_\infty-r_\infty(1)\delta_1.
\]
Combining the established exact dyadic identity with the first-site split gives
\[
\boxed{
\|\Delta r_\infty\|^2
=(3-2\sqrt2)D^2+(\sqrt2-1)DR+\frac{R^2}{4}+\|T\|^2.}
\]
Every term is nonnegative. Consequently
\[
D^2\le(3+2\sqrt2)\|\Delta r_\infty\|^2.
\]
This nonlinear estimate is specific to the actual projection residual. It
does not assert a bounded inverse for differentiation on arbitrary vectors.

For the finite-stage error E_n, derivative-optimal error eps_n^2, and the
complete mismatch cost Q_n, the checked certificate is
\[
D^2\le2(3+2\sqrt2)\bigl[\varepsilon_n^2+Q_n+(E_n-D)\bigr].
\]
The exact finite-stage first-site square also retains the signed dyadic
defect. The known limits eps_n^2->0 and E_n-D->0 do not remove Q_n.

## 4. The derivative sieve cannot directly provide primitive convergence

For the actual factorial sieve S_Y and C_Y=product_{p<=Y}(1-1/p),
PrimeSievePrimitiveEscape.lean proves
\[
S_Y(k)=1-C_Yk\quad(1\le k\le Y),
\]
followed by the exact complete error:
\[
\boxed{
\|1-S_Y\|^2
=C_Y^2\sum_{j<Y}\frac{j+1}{j+2}
+\sum_{k>Y}w_k(1-S_Y(k))^2.}
\]
Therefore \(\|1-S_Y\|^2\ge YC_Y^2/2\) and
\(\|S_Y\|^2+1\ge YC_Y^2/4\). The already established \(YC_Y^2\to\infty\)
proves that both the primitive error and the primitive norm diverge.
This holds for the very same sieves whose full derivative error tends to zero.
It does not refute convergence of the canonical optimal projections.

## Remaining obligation and verification scope

**Open:** establish the signed correction decay needed for the actual
optimal coefficients. Neither the raw Möbius provider nor sieve derivative
density supplies that estimate. No unconditional RH theorem is claimed.

The original four modules and the two strong-convergence continuation modules
are exported from RiemannResearch.lean.
Endpoint axiom audits use only propext, Classical.choice, and Quot.sound.
Source: the user's requested vanishing attempt, continuing the exact
CRTPrimitiveTransferAudit20260929.md Section 6 and existing dyadic/PNT results.
No mathematical novelty claim is made.
