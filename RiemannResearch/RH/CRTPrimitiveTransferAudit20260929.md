# CRT primitive transfer: exact failure and the remaining optimizer condition

Date: 2026-09-29. Continuation of commit
1d6b1b8ffe66bbd7662f6d10d99b37f64dffd314.

**The RH-strength obstacle is not closed.** This attempt proves that a uniform
sparse-derivative-to-legal-primitive estimate is false, even on a fixed
three-atom pattern with zero Pareto mean. It also verifies that the two
optimization problems do not commute already at the first legal atom.
These are obstructions to proposed shortcuts, not counterexamples to RH or
to convergence of the actual optimal legal sequence.

## 1. Full primitive identity, now checked in Lean

Let \(w_n=1/[n(n+1)]\), \(n\ge1\), and \(w_0=0\). For a bounded real sequence
define \(Sf(n)=f(n-1)\), with natural subtraction at zero, and
\(\Delta f=f-Sf\). Set
\[
E(f)=\sum_{n\ge0}w_n f(n)^2,\qquad
J(f)=\sum_{n\ge0}(w_n-w_{n+1})f(n)^2.
\]
The new module ParetoPrimitiveEnergy.lean proves
\[
\boxed{E(f)-E(Sf)=J(f)}
\]
and
\[
\boxed{4E(f)=E(\Delta f)+E(f+Sf)+2J(f).}
\]
Both are complete equalities for bounded sequences. All summability is
discharged. If \(f(0)=0\), then \(J(f)\ge0\) and \(E(\Delta f)\le4E(f)\).
Without anchoring, the \(n=0\) contribution to \(J\) is retained and can be
negative; it is not silently removed.

The endpoints are **PrimitiveEnergy.energy_sub_backwardShift** and
**PrimitiveEnergy.full_primitive_energy_identity**.

## 2. A two-conductor counterexample to uniform inverse control

Write \(r_d(n)=n\bmod d=d\,g_d(n)\). For \(m\ge1\), put
\[
P_m=r_{2m}-r_m=2m\,g_{2m}-m\,g_m
=m\bigl((\lfloor n/m\rfloor)\bmod2\bigr).
\]
For \(m\ge2\), both atoms are legal. Its reciprocal charge is
\(2m/(2m)-m/m=0\), but its Pareto mean is not zero:
\[
\boxed{\langle1,P_m\rangle=\log2,\qquad E(P_m)=m\log2.}
\]
These exact whole-space identities follow from the existing Pareto dilation
law and binary residue moment. They are formalized as
**binaryPrimitive_mean** and **binaryPrimitive_energy**.

At every positive integer,
\[
\Delta P_m(n)=m\mathbf1_{m\mid n}-2m\mathbf1_{2m\mid n}.
\]
Therefore
\[
E(\Delta P_m)=\sum_{k\ge1}\frac{m^2}{mk(mk+1)},\qquad
R_m=\sum_{k\ge1}\frac1{k^2(mk+1)}.
\]
The exact sparse comparison specializes to
\[
\boxed{E(\Delta P_m)+R_m=\zeta(2),\qquad
0\le R_m\le\frac{\zeta(2)}{m+1}.}
\]
In particular,
\[
\frac m{m+1}\zeta(2)\le E(\Delta P_m)\le\zeta(2).
\]
This is **binaryJump_energy_add_remainder** and
**binaryJump_energy_bounds**; the formal constant is the convergent
reciprocal-square series zetaTwoSeries.

Combining the two full energy identities, Lean additionally proves
\[
\boxed{
4m\log2+R_m
=\zeta(2)+E(P_m+SP_m)+2J(P_m).
}
\]
This is **binaryPrimitive_full_remainder**. The primitive remainders are
explicitly present and grow; they cannot be declared negligible on the
strength of the sparse bound.

It follows that no real constant \(C\), independent of \(m\), can satisfy
\[
E(P_m)\le C E(\Delta P_m)\quad(m\ge2).
\]
The contradiction is the checked theorem **no_uniform_primitive_bound**.

The checked normalization \(u_m=P_m/\sqrt m\) has
\[
E(u_m)=\log2,\qquad E(\Delta u_m)\le\zeta(2)/m,\qquad
u_m(n)=0\quad(n<m).
\]
**normalized_binary_approximate_kernel** gives, for every positive tolerance,
an actual legal member with that fixed nonzero primitive energy and derivative
energy below the tolerance. This is an explicit failure of a bounded inverse
for the difference map on these legal packets.

## 3. The failure persists with actual Pareto mean zero

Define the three-conductor packet
\[
U_m=P_m-P_{2m}
=2r_{2m}-r_m-r_{4m}
=4m\,g_{2m}-m\,g_m-4m\,g_{4m}.
\]
For \(m\ge2\), all three atoms are legal. Both its reciprocal charge and its
Pareto mean vanish. The checked exact identities are
\[
\boxed{\langle1,U_m\rangle=0,\qquad E(U_m)=m\pi/2.}
\]
The constant \(\pi/2\) follows from the existing exact fourth-residue moment
and the parallelogram identity, not a numerical estimate.

The signed derivative is retained as
\(\Delta U_m=\Delta P_m-\Delta P_{2m}\). Its complete energy is
\[
E(\Delta U_m)=E(\Delta P_m)+E(\Delta P_{2m})
-2\langle\Delta P_m,\Delta P_{2m}\rangle.
\]
Bounding this displayed full square by twice each separate square gives the
checked estimate \(E(\Delta U_m)\le4\zeta(2)\).
The module proves **centeredPrimitive_mean**, **centeredPrimitive_energy**,
**centeredJump_eq_binary**, **centeredJump_energy_le**, and
**no_uniform_centered_primitive_bound**.
The estimate is used only to refute uniform inverse control, not to close an
RH argument.

## 4. Why these examples do not refute the optimized Schur route

For the two-atom packet, Lean proves the exact objective polynomial
\[
\boxed{
\|1-aP_m\|^2
=1-\frac{\log2}{m}
+m\log2\left(a-\frac1m\right)^2.
}
\]
Thus its optimal one-direction gain is \(\log2/m\), which tends to zero.
The large primitive norm is accompanied by weak alignment with the target.
For the centered packet, \(\langle1,U_m\rangle=0\), so that single direction
has no target gain at all.

The optimizer can ignore or screen such directions. Consequently the examples
do not rule out special estimates for the actual optimal coefficients.
They rule out controlling every legal primitive by its sparse derivative.

## 5. Actual optimizer incompatibility at the first legal atom

Let \(R_2=r_2=2g_2=P_1\). The target is anchored at zero, so
\(\Delta1=\delta_1\), whose Pareto norm squared is \(1/2\).

The exact legal objective is
\[
\boxed{\|1-tR_2\|^2=1-\log2+\log2(t-1)^2.}
\]
Its minimizer is \(t=1\). The new module ResidueDerivativeOptimization.lean
constructs the actual alternating jump as a vector of the existing Hilbert
space and proves
\[
\boxed{\|\delta_1-t\Delta R_2\|^2
=\frac14+\left(t-\frac12\right)^2.}
\]
Its minimizer is \(t=1/2\). In normalized \(g_2\) coefficients these are
respectively \(2\) and \(1\).

The checked signed mismatch is
\[
\boxed{\langle\delta_1-\Delta R_2,\Delta R_2\rangle=-\frac12.}
\]
The endpoints are **binaryJumpOne_derivative_target_error** and
**binaryJumpOne_optimizer_incompatibility**. Therefore differentiation does
not carry the legal orthogonal projection to the derivative-space orthogonal
projection automatically. The anchored boundary term is part of the proof.

## 6. Formalized compatibility energy and the stronger limit criterion

This section is now formalized in the six modules listed below. Repository
stage n corresponds to the displayed cutoff N=n+1.

For the original normalized legal atoms, let
\[
c_N=G_N^{-1}b_N,\quad F_N=\sum_{j=2}^N c_{N,j}g_j,\quad
D_N(i,j)=\langle\Delta g_i,\Delta g_j\rangle,\quad
d_N(j)=\langle\delta_1,\Delta g_j\rangle=\frac1{2j}.
\]
ThresholdHilbertDifference.lean constructs the actual bounded linear operator
on the entire anchored Pareto Hilbert space. It proves injectivity,
\(\|\Delta f\|\le2\|f\|\), and the boundary identity \(\Delta1=\delta_1\).
Derivative-family independence and positivity of the actual Gram determinant
therefore follow from the established independence of the legal atoms.
There is no postulated matrix inverse or bounded primitive inverse.

Write
\[
a_N=D_N^{-1}d_N,\qquad
\varepsilon_N^2=\min_a\left\|\delta_1-\sum_{j=2}^N a_j\Delta g_j\right\|^2,
\qquad h_N=d_N-D_Nc_N.
\]
The checked endpoint **derivative_error_exact_split** gives
\[
\boxed{\|\Delta(1-F_N)\|^2
=\varepsilon_N^2+h_N^{\mathsf T}D_N^{-1}h_N.}
\]
Analysis/FiniteGramCompatibility.lean proves the underlying identity,
identifies the coefficient correction as \(D_N^{-1}h_N=a_N-c_N\),
and retains the full dual square:
\[
2t^{\mathsf T}h_N-t^{\mathsf T}D_Nt
=h_N^{\mathsf T}D_N^{-1}h_N
-\|U_N(a_N-c_N-t)\|^2,
\quad U_Nt=\sum_jt_j\Delta g_j.
\]
The dual maximum is attained. All signed covariance terms remain present.

### Unconditional derivative approximation, including its exact scale

The implementation uses factorial moduli \(Y!\), which have the same prime
support as the corresponding primorial. Set
\[
C_Y=\sum_{d\mid Y!}\frac{\mu(d)}d
=\prod_{p\le Y}(1-1/p),\qquad
A_Y=-\sum_{d\mid Y!}\mu(d)g_d.
\]
For \(n\ge1\), exact inclusion-exclusion gives
\[
\Delta A_Y(n)=\mathbf1_{(n,Y!)=1}-C_Y.
\]
With \(J_Y=\sum_{n\ge2,\ (n,Y!)=1}w_n\), the checked theorem
**derivativeSieveError_exact** is
\[
\boxed{E_Y:=\|\delta_1-\Delta A_Y\|^2=C_Y^2-2C_YJ_Y+J_Y.}
\]
The complete tail satisfies \(0\le J_Y\le1/(Y+1)\), and the established
finite-prime-product limit gives \(C_Y\to0\). Hence \(E_Y\to0\).
The stronger checked estimates and asymptotic are
\[
|E_Y-C_Y^2|\le\frac1{Y+1},\qquad
\left|\frac{E_Y}{C_Y^2}-1\right|
 \le\frac1{(Y+1)C_Y^2},\qquad
\boxed{\frac{E_Y}{C_Y^2}\longrightarrow1}.
\]
The last step uses the repository's established
\(Y C_Y^2\to\infty\), without an RH assumption.

PrimeSieveDerivativeClosure.lean constructs these same sieves as explicit
finite sums of the actual Hilbert residue atoms and proves the exact norm
identity. Consequently **derivative_target_mem_dictionaryClosure** and
**derivativeBestError_tendsto_zero** establish \(\varepsilon_N^2\to0\)
for the actual exhaustive derivative optimum.

### The compatibility limit exists; its vanishing remains open

Let \(r_\infty=1-P_V1\), using the already established strong convergence
\(F_N\to P_V1\). Boundedness of \(\Delta\), the exact split, and
\(\varepsilon_N^2\to0\) give the unconditional checked limit
\[
\boxed{h_N^{\mathsf T}D_N^{-1}h_N
\longrightarrow\|\Delta r_\infty\|^2.}
\]
Injectivity now yields
\[
h_N^{\mathsf T}D_N^{-1}h_N\to0
\quad\Longleftrightarrow\quad
\|1-F_N\|\to0.
\]
No claim that the compatibility sequence is monotone is made.

There is a stronger formulation of the required arithmetic input. It is
enough to prove, for every fixed \(j\ge2\),
\[
\boxed{\langle\Delta g_j,\Delta(1-F_N)\rangle\longrightarrow0.}
\]
Indeed \(\Delta r_\infty\) belongs to the closed derivative span: the sieve
puts \(\delta_1\) there, while continuity puts \(\Delta P_V1\) there.
The displayed limits make it orthogonal to every generator and hence to
itself. Thus \(\Delta r_\infty=0\), and injectivity gives \(r_\infty=0\).
This is **fixedMismatch_limits_iff_projection_norm_zero**. It needs no
dimension-dependent inverse Gram bound because the actual primitive
projections already converge strongly.

The full limiting primitive identity also remains intact:
\[
4\|r_\infty\|^2
=\|\Delta r_\infty\|^2+\|r_\infty+Sr_\infty\|^2+2J(r_\infty).
\]
Here \(J(r_\infty)\) is the complete shift defect, distinct from the sieve
tail \(J_Y\). The operator module proves this identity for every Hilbert
vector, removing the earlier bounded-sequence restriction.
The compatibility limit lies between zero and \(4\|r_\infty\|^2\);
failure of RH would force it to be strictly positive.

**Conditional research reduction — Open:** prove the fixed signed
compatibility limits for the actual legal optimal coefficients, or prove
the equivalent complete inverse-Gram cost tends to zero.
The checked implication from either condition concludes Mathlib's actual
RiemannHypothesis. Neither decay condition is supplied by the formalization.
Legal normal equations do not imply derivative normal equations, as the
first-atom counterexample already shows. The prime-power Schur saturation
and full Weil positivity obligations also remain open.

## Verification and provenance

The initial transfer results are in ParetoPrimitiveEnergy.lean,
CRTPrimitiveEscape.lean, and ResidueDerivativeOptimization.lean.
Section 6 adds Analysis/FiniteGramCompatibility.lean,
Analysis/ClosedSpanCompatibility.lean, RH/ThresholdHilbertDifference.lean,
RH/PrimeSieveDerivativeApproximation.lean, RH/PrimeSieveDerivativeClosure.lean,
and RH/ResidueDerivativeCompatibility.lean. Combined candidates and endpoint
axiom audits passed Lean using only propext, Classical.choice, and Quot.sound.
The publication checkpoint validates the affected modules and root exports.

Source: direct analysis of the user's CRT transfer question, using existing
exact Pareto dilation, binary/fourth-residue moments, and the previously
published sparse comparison. No novelty claim is made.

For the classical natural-dilation Nyman--Beurling criterion, see L. Báez-Duarte,
[A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis](https://arxiv.org/abs/math/0202141).
That theorem supports the background RH significance of the approximation
target; it does not supply the missing compatibility estimate above.
