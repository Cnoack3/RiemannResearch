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

## 6. The precise remaining compatibility energy: paper reduction

This section is a finite-dimensional paper derivation, not a newly formalized
all-\(N\) matrix theorem.

For the original normalized legal atoms, let
\[
c_N=G_N^{-1}b_N,\quad F_N=\sum_{j=2}^N c_{N,j}g_j,\quad
D_N(i,j)=\langle\Delta g_i,\Delta g_j\rangle,\quad
d_N(j)=\langle\delta_1,\Delta g_j\rangle=\frac1{2j}.
\]
The anchored difference map is injective: \(\Delta f=0\), \(f(0)=0\) implies
\(f=0\) by induction. Hence \(D_N\) is positive definite when the original
finite atoms are independent. Write
\[
a_N=D_N^{-1}d_N,\qquad
\varepsilon_N^2=\min_a\left\|\delta_1-\sum_{j=2}^N a_j\Delta g_j\right\|^2.
\]
Derivative-space orthogonality gives the exact Pythagorean decomposition
\[
\begin{aligned}
\|\Delta(1-F_N)\|^2
&=\varepsilon_N^2+(c_N-a_N)^{\mathsf T}D_N(c_N-a_N)\\
&=\boxed{\varepsilon_N^2+
h_N^{\mathsf T}D_N^{-1}h_N},\qquad
h_N=d_N-D_NG_N^{-1}b_N.
\end{aligned}
\]
All signed cross terms remain inside the complete compatibility quadratic.

Derivative approximability of the target is not the remaining obstacle.
For completeness, let \(Q_y\) be a primorial,
\(C_y=\prod_{p\le y}(1-1/p)\), and
\(A_y=-\sum_{d\mid Q_y}\mu(d)g_d\). Exact inclusion-exclusion gives
\[
\Delta A_y(n)=\mathbf1_{(n,Q_y)=1}-C_y.
\]
With
\(J_y=\sum_{n\ge2,\,(n,Q_y)=1}w_n\),
\[
\boxed{\|\delta_1-\Delta A_y\|^2=C_y^2-2C_yJ_y+J_y.}
\]
Here \(0\le J_y\le1/(\lfloor y\rfloor+1)\) and \(C_y\to0\), so the derivative
error tends to zero. These sieve ingredients are already present in
PrimeSievePointEnergy.lean and the finite prime-product results. The displayed
derivative-error assembly is a paper consequence. Exhausting legal denominators
therefore gives \(\varepsilon_N\to0\).

The actual legal projections already converge strongly to \(P_V1\), with \(V\)
the closed legal span. The difference map is bounded and injective on the
anchored Hilbert space: the shift contraction gives boundedness, and the
coordinate recurrence gives injectivity. It follows that
\[
h_N^{\mathsf T}D_N^{-1}h_N\longrightarrow0
\quad\Longleftrightarrow\quad
F_N\longrightarrow1.
\]
This is an exact reformulation of the same closure target, not a new arithmetic
estimate proving it. Strong convergence of the optimal sequence removes any
need for a uniform inverse bound if derivative consistency can be established.
However, legal normal equations \(G_Nc_N=b_N\) do not imply derivative normal
equations \(D_Nc_N=d_N\); the first-atom calculation exhibits the discrepancy.

**Open:** prove the complete compatibility energy tends to zero for the actual
optimal coefficients, or establish another genuinely sufficient arithmetic
estimate. No such provider was obtained in this attempt. The prime-power Schur
saturation and the full Weil positivity routes remain open as well.

## Verification and provenance

Three new modules carry the established results:
ParetoPrimitiveEnergy.lean, CRTPrimitiveEscape.lean, and
ResidueDerivativeOptimization.lean. The combined candidates and endpoint
axiom audits passed Lean using only propext, Classical.choice, and Quot.sound.
The publication checkpoint validates the affected modules.

Source: direct analysis of the user's CRT transfer question, using existing
exact Pareto dilation, binary/fourth-residue moments, and the previously
published sparse comparison. No novelty claim is made.

For the classical natural-dilation Nyman--Beurling criterion, see L. Báez-Duarte,
[A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis](https://arxiv.org/abs/math/0202141).
That theorem supports the background RH significance of the approximation
target; it does not supply the missing compatibility estimate above.
