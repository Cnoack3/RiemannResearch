# Dimension-independent inverse-Gram correction bounds (2026-09-28)

**Status:** the new inequalities below are unconditional. The requested
vanishing of every fixed correction remains open; no proof of RH is claimed.
These are Hilbert-space estimates for the actual full Pareto Gram matrices,
not an additional arithmetic cancellation theorem.

## Notation and indexing

Use the question's cutoff \(N\), with conductors \(2,\ldots,N\).
The Lean stage is \(n=N-1\). Put
\[
 V_N=\operatorname{span}(g_2,\ldots,g_N),\quad
 V=\overline{\bigcup_N V_N},\quad P_N=P_{V_N},\quad P=P_V,
\]
\[
 r_N=1-P_N1,\quad r_\infty=1-P1,\quad
 D_N=\|r_N\|^2,\quad D_\infty=\|r_\infty\|^2.
\]
The existing coefficient Riesz vectors satisfy
\(\langle g_j,h_d\rangle=\delta_{jd}\) and
\(\langle1,h_d\rangle=-\mu(d)\).
They have finite support and explicit norms; for example
\[
 \|h_2\|^2=14,\qquad \|h_3\|^2=20,\qquad
 \langle h_2,h_3\rangle=-2.
\]
Let
\[
 k_N=G_N^{-1}(b_N+G_N\mu_N).
\]
The existing exact identification with the optimal coefficients gives
\[
 k_{N,d}=-\langle r_N,h_d\rangle
        =-\langle r_N,(I-P_N)h_d\rangle.
\]
No replacement of the full Gram matrix by a truncated tail is made.

## 1. Full signed covariance bound

For \(2\le d,e\le N\), define
\[
 K_{N,de}=\langle h_d,h_e\rangle,\qquad
 Q_N=K_N-G_N^{-1}.
\]
The existing inverse-Gram representation gives
\[
 (G_N^{-1})_{de}=\langle P_Nh_d,P_Nh_e\rangle,\qquad
 Q_{N,de}=\langle(I-P_N)h_d,(I-P_N)h_e\rangle.
\]
Consequently, for **every** real vector \(a\) of the current dimension,
\[
 \boxed{(a^Tk_N)^2\le D_N\,a^TQ_Na.}
\]
Equivalently, in positive-semidefinite order,
\[
 \boxed{k_Nk_N^T\preceq D_N(K_N-G_N^{-1}).}
\]
There is no factor depending on \(N\), no entrywise absolute-value replacement,
and no hypothesis about RH, a zeta zero, or a coefficient-growth estimate.

Proof: set \(u=\sum_da_d(I-P_N)h_d\). Then
\(a^Tk_N=-\langle r_N,u\rangle\) and
\(\|u\|^2=a^TQ_Na\); apply Cauchy--Schwarz.
The constant 1 is sharp for this general Hilbert-space inequality. This does
not assert sharpness for each particular arithmetic Gram matrix.

The individual-coordinate consequence is
\[
 \boxed{|k_{N,d}|^2\le
 D_N\bigl(\|h_d\|^2-(G_N^{-1})_{dd}\bigr).}
\]
For \(N\ge3\), the fully explicit, simultaneous two-coordinate consequence is
\[
 \boxed{20k_{N,2}^2+4k_{N,2}k_{N,3}+14k_{N,3}^2\le276D_N.}
\]
Indeed, the two-vector dual Gram matrix is
\(\begin{pmatrix}14&-2\\-2&20\end{pmatrix}\), whose determinant is 276.
Lean proves the ellipse directly from the Hilbert-space inequality; the
Wolfram calculation was only an independent algebra check.

## 2. A vanishing factor in the stabilization error

Define
\[
 k_{\infty,d}=-\langle r_\infty,h_d\rangle,\qquad
 L_{dd}=\|Ph_d\|^2,\qquad
 T_{N,d}=\|(P-P_N)h_d\|^2.
\]
Unconditionally,
\[
 (G_N^{-1})_{dd}\longrightarrow L_{dd},\quad
 T_{N,d}=L_{dd}-(G_N^{-1})_{dd}\longrightarrow0.
\]
The stronger stabilization bound is
\[
 \boxed{|k_{N,d}-k_{\infty,d}|^2
 \le (D_N-D_\infty)\,
       \bigl(L_{dd}-(G_N^{-1})_{dd}\bigr).}
\]
Proof: \(P-P_N\) is the orthogonal projection onto \(V\cap V_N^\perp\).
Therefore
\[
 k_{N,d}-k_{\infty,d}
 =-\langle(P-P_N)1,(P-P_N)h_d\rangle.
\]
Its first squared norm is \(D_N-D_\infty\) and its second is \(T_{N,d}\).
Another application of Cauchy--Schwarz proves the assertion.

In particular, for each fixed \(d\),
\[
 \boxed{|k_{N,d}-k_{\infty,d}|^2=o(D_N-D_\infty).}
\]
This is understood in the usual epsilon-bound sense, which also covers stages
where \(D_N=D_\infty\): the numerator is then zero. It improves the earlier
bound with the fixed multiplier \(\|h_d\|^2\). It supplies no explicit rate
for the vanishing factor \(T_{N,d}\).

## 3. The surviving obstruction

The limiting correction itself satisfies
\[
 \boxed{|k_{\infty,d}|^2\le
 D_\infty\bigl(\|h_d\|^2-L_{dd}\bigr).}
\]
The right side is not known to vanish. In particular, the fact
\(L_{dd}-(G_N^{-1})_{dd}\to0\) must not be confused with
\(\|h_d\|^2-(G_N^{-1})_{dd}\to0\).

The requested conclusion is exactly
\[
 \forall d\ge2:\quad k_{\infty,d}=0.
\]
The repository already proves its equivalence to \(D_\infty=0\), and derives
RH from that norm-closure condition. In purely matrix terms the single missing
saturation statement is
\[
 \boxed{b_N^TG_N^{-1}b_N\longrightarrow1},
 \qquad D_N=1-b_N^TG_N^{-1}b_N.
\]
Proving that saturation, or proving that every fixed inverse diagonal reaches
its *full* dual norm \(\|h_d\|^2\), would suffice. The new covariance and
two-gap estimates establish neither. Existence of fixed correction limits
and finite total variation were already present in the repository and are
not counted as new results here.

## Lean declarations and provenance

- General projection pairings: Analysis/NestedProjectionPairing.lean.
- Application: RH/ResidueCorrectionCovariance.lean.
- Principal declarations:
  correction_quadratic_le_residual_covariance,
  correction_sq_le_inverse_diagonal_defect,
  correction_error_sq_le_two_gaps,
  correction_error_sq_isLittleO_energy_excess,
  correction_limit_sq_le_dual_defect,
  correction_two_three_ellipse.
- The proofs were developed directly from existing project identities and
  standard Hilbert-space Cauchy--Schwarz. They are not claimed as novel
  mathematical results.
- The principal covariance, little-o, and limiting-defect declarations passed
  executable Lean checks, exit 0, with only propext, Classical.choice, and
  Quot.sound reported by #print axioms. Publication checkpoint validation
  is reported separately in the conversation; no GitHub CI claim is made.

For context, primary sources reviewed were Werner Ehm,
[On certain Gram matrices and their associated series](https://arxiv.org/abs/2405.06349),
and Alouges, Darses, Hillion,
[Polynomial approximations in a generalized Nyman-Beurling criterion](https://arxiv.org/abs/2006.02953).
They motivate attention to Gram formulas and coefficient control; neither is
used as an unproved premise in these Lean inequalities.
