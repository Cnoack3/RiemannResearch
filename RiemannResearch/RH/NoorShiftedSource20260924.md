# Actual shifted sources: exact moments, moving limits, and Schur control

**Date:** September 24, 2026
**Foundation:** commit 3d825c6a7d9b4296580795782660542756045835.
**Status:** Unconditional source identities, moving-index limits, and a source-alignment bound. The divided inverse-Gram rate remains open; no unconditional proof of RH is claimed.

## 1. Preserve the actual arithmetic problem

At stage \(N\), the legal indices are \(d=2,\ldots,N+1\). Write
\[
u_d=Tg_d,\qquad U_N=\operatorname{span}\{u_2,\ldots,u_{N+1}\},
\quad a_N=T(\mathbf1-P_{V_N}\mathbf1),\quad E_N=\|a_N\|^2.
\]
All inner products are the complete infinite Hilbert inner products.
The repository uses \(T\mathbf1=-e_0\), so \(a_N(0)=-E_N\), now explicitly verified.

Retain \(D=I-S\) and the previously proved matrices
\[
G_N(d,e)=\langle u_d,u_e\rangle,\quad
K_N(d,e)=\langle Du_d,Du_e\rangle,\quad
h_N(d)=\langle Du_d,a_N\rangle.
\]
The existing canonical minimum remains
\[
J_N(t)=E_N-h_N^{\mathsf T}(K_N+t^2G_N)^{-1}h_N,\qquad t>0.
\]

## 2. Exact arithmetic source formula

For \(d>0\), set \(M_N(d)=\langle a_N,L_d\rangle\).
The new general theorem computes the complete moment as
\[
\boxed{\quad
\langle a,L_d\rangle=\sum_{m=1}^{\infty}\frac{a(dm)}m.
\quad}
\]
The series is absolutely convergent by Cauchy–Schwarz for the coefficient
\(\ell^2\) vector \(a\) and the reciprocal sequence. Lean indexes from zero;
the zeroth summand is zero by totalized division.

Pairing \(dDu_d=-(\log d)e_0+L_1-L_d\) with \(a_N\) gives
\[
\boxed{\quad d\,h_N(d)=E_N\log d+M_N(1)-M_N(d).\quad}
\]
This retains the full signed source and every tail term.

## 3. Unconditional growing-index source limit

Let \(N_j\to\infty\) and choose legal indices
\(2\le d_j\le N_j+1\) with \(d_j\to\infty\).
Put \(a=T(\operatorname{limitResidual})\) and
\(E_\infty=\|\operatorname{limitResidual}\|_P^2\). Lean proves
\[
M_{N_j}(d_j)\longrightarrow0
\]
and
\[
\boxed{\quad
d_jh_{N_j}(d_j)-E_{N_j}\log d_j
\longrightarrow\langle a,L_1\rangle.
\quad}
\]
Consequently,
\[
\boxed{\quad
\frac{d_jh_{N_j}(d_j)}{\log d_j}\longrightarrow E_\infty.
\quad}
\]
For a concrete instance, take \(N_j=j+1\) and \(d_j=j+2\).

The proof uses \(a_N\to a\) in the actual Hilbert norm, the common norm
of \(L_d\) for \(d>0\), and the already proved weak convergence of \(L_d\)
to zero. It assumes neither \(a=0\) nor a quantitative arithmetic rate.

The same normalized source tending to zero is proved equivalent to
\(\operatorname{limitResidual}=0\). A separate conditional theorem derives
Mathlib RH from that zero-limit premise. The premise is open: the
unconditional theorem identifies its limit but does not prove it is zero.
No RH-to-zero-residual converse is asserted here.

## 4. Mixed matrix and original projection coefficients

Define
\[
B_N(d,e)=\langle Du_d,u_e\rangle,\qquad b_N(d)=\frac{\log d}{d}.
\]
Let \(c_N\) contain the actual coefficients of the original unshifted projection.
They are distinct from the regularized lift coefficients.
Lean proves
\[
\boxed{\quad h_N=b_N-B_Nc_N,\qquad B_N+B_N^{\mathsf T}=K_N.\quad}
\]
Thus the known lcm formula for \(K_N\) determines the symmetric part of \(B_N\).
It does not by itself determine the mixed matrix or the actual source:
the skew-symmetric part must also be retained.

## 5. Source control after projection

For every coefficient array \(x\), put
\[
y=\sum_d x_dDu_d,\qquad P_N=P_{U_N}.
\]
The verified proof uses the exact inverse-Gram projection coefficients and
identifies
\[
\|y-P_Ny\|^2=x^{\mathsf T}K_Nx-
(B_N^{\mathsf T}x)^{\mathsf T}G_N^{-1}(B_N^{\mathsf T}x).
\]
Since \(a_N\perp U_N\), its pairing with \(y-P_Ny\) is \(x^{\mathsf T}h_N\).
Cauchy–Schwarz gives the new unconditional theorem
\[
\boxed{
(x^{\mathsf T}h_N)^2\le E_N
\left[x^{\mathsf T}K_Nx-
(B_N^{\mathsf T}x)^{\mathsf T}G_N^{-1}(B_N^{\mathsf T}x)\right].
}
\]
The quadratic on the right equals
\(x^{\mathsf T}(K_N-B_NG_N^{-1}B_N^{\mathsf T})x\).
Lean's public theorem uses the displayed factored expression; the exact
norm identity is retained in its proof.

Only original-family independence is used to invert \(G_N\).
No inverse or positive-definiteness assumption is imposed on the Schur kernel.
The empty stage \(N=0\) is included.

## 6. What remains for RH

The original divided-rate target is unchanged:
\[
\frac{E_{N_j}-h_{N_j}^{\mathsf T}
(K_{N_j}+t_j^2G_{N_j})^{-1}h_{N_j}}{t_j}
\longrightarrow0,
\qquad N_j\to\infty,\quad t_j>0,\quad t_j\to0.
\]
The new source identities and Schur bound are unconditional inputs.
They do not supply the lower bound on the inverse quadratic needed
for this cancellation.

The next substantive task is joint control of the full mixed matrix \(B_N\),
the actual source, and the regularized inverse on growing coefficient arrays.
Pointwise or moving-coordinate source limits alone do not control a
growing inverse matrix. The exact normalized source limit still contains
\(E_\infty\), which is not known to vanish.

Do not replace \(B_N\) by \(K_N/2\), drop the signed logarithmic moments,
replace \(G_N\) with uniform CRT weights, or infer the divided rate from
unscaled convergence.

## 7. Lean declarations and provenance

Import `RiemannResearch.RH.NoorShiftedSource`.

In namespace `RiemannResearch.Analysis.Noor`, module
`Analysis/NoorLogarithmGram.lean`:

- `inner_logVector_eq_tsum_multiples`.

In namespace `RiemannResearch.RH.Pareto.Noor`, module
`RH/NoorShiftedSource.lean`:

- `finiteTarget_zero`, `sourceLogMoment`
- `finiteShiftedSource_eq_logMoments`
- `sourceLogMoment_moving_tendsto_zero`
- `finiteShiftedSource_centered_tendsto`
- `finiteShiftedSource_log_scaled_tendsto`
- `finiteShiftedSource_log_scaled_zero_iff`
- `riemannHypothesis_of_finiteShiftedSource_log_scaled_zero`
- `finiteMixedShiftGram`, `finiteProjectionCoefficients`, `finiteOneSource`
- `finiteTarget_expansion`, `finiteShiftedFamily_inner_one`
- `finiteShiftedSource_eq_mixed`
- `finiteMixedShiftGram_add_transpose`
- `finiteShiftedSource_schur_bound`.

The coordinate helper `inner_hardyCoordinates_one` belongs to the parent
namespace `RiemannResearch.RH.Pareto`.

These are elementary deductions from the supplied handoff and inspected
repository modules. The existing logarithmic-vector and shifted-density
development cites S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte
criterion for the RH", Theorem 9, https://arxiv.org/abs/1809.09577.
That citation supports the earlier logarithmic/shifted-density argument,
not the open divided rate. No mathematical novelty is asserted.

## 8. Verification record

The complete candidate group passed the Lean kernel with exit code 0 and
no warnings (18.819 seconds). Axiom inspection of the exact moment formula,
source identity, moving-index limit, mixed-matrix identities, Schur bound,
and RH reduction reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced.
The explicit `hsource` hypothesis remains unproved; axiom inspection does
not discharge local theorem hypotheses.

The publication checkpoint validates affected modules and their local
reverse dependents. The accompanying external continuation records its
result and published commit. This is not a fresh full-repository build.
