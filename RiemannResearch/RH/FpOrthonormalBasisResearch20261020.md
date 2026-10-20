# Orthonormal coordinates for the logarithmic targets

Research note, 20 October 2026. Source: user-provided suggestions to use prime-power factors and orthonormal bases. The formulas below distinguish formal declarations from arguments awaiting formalization.

## Objects and current status

On positive integers let
\[
 Q(n)=\frac1{\zeta(2)n^2},\qquad F_p(n)=\lfloor\log_p n\rfloor,
 \qquad g_d(n)=\frac{n\bmod d}{d}.
\]
The auxiliary coordinate at zero is anchored to zero. Write
\[
 H=\overline{\operatorname{span}_{\mathbb R}\{g_d:d>1\text{ squarefree}\}},
 \qquad C=\overline{H+\mathbb R1}.
\]
All closures and inner products use the complete Q norm. In Lean the targets are `PrimePowerTarget.qTarget p hp`, and C is `PrimePowerTarget.closureWithConstants`.

**Open:** both `qTarget 2 _ ∈ closureWithConstants` and `qTarget 3 _ ∈ closureWithConstants`. The existing two-target RH criterion remains a conditional research reduction. No orthonormal-basis calculation below supplies either membership automatically.

The additions formalize an orthonormal pair inside C, its exact F₂ coefficient and complete energy decomposition, and an obstruction to nonlinear functions of F_p belonging to C. They do not formalize the full Meixner tensor basis or the complete Gram–Schmidt basis of C. Acceptance of these additions is determined by the server checkpoint, rather than the existence of this note.

## Formal parity component and full remainder

Let
\[
 \eta_2=\frac{4\mathbf1_{\{2\mid n\}}-1}{\sqrt3}
       =\frac{3-8g_2}{\sqrt3}.
\]
The physical constant and \(\eta_2\) belong to C and form an orthonormal pair. The corresponding declarations are `ZetaTwoParitySignal.parityFrame_orthonormal` and the membership results in `QPrimePowerParityBasis.lean`.

The complete weighted-series reindexing yields
\[
 \langle F_2,\mathbf1_{\{2\mid n\}}\rangle_Q
   =\frac{\langle F_2,1\rangle_Q+1}{4},
 \qquad
 \boxed{\langle F_2,\eta_2\rangle_Q=\frac1{\sqrt3}}.
\]
The second identity is `PrimePowerTarget.qTarget_two_inner_parityUnit`.

For arbitrary f, put \(a=\langle f,1\rangle_Q\) and \(b=\langle f,\eta_2\rangle_Q\). The exact orthogonal decomposition is
\[
 \|f\|_Q^2=a^2+b^2+\|f-a1-b\eta_2\|_Q^2.
\]
`ZetaTwoParitySignal.parityApproximation_energy_exact` records the full remainder. Its F₂ specialization, `PrimePowerTarget.qTarget_two_parity_energy_exact`, gives, with \(\mu_2=\langle F_2,1\rangle_Q\),
\[
 \boxed{\|F_2\|_Q^2
  =\mu_2^2+\frac13+
   \left\|F_2-\mu_2 1-\frac1{\sqrt3}\eta_2\right\|_Q^2.}
\]
Thus the first nonconstant legal direction contributes exactly 1/3 to the captured variance. The remaining nonnegative term is retained; it is not asserted to vanish.

## Formal rigidity of functions of F_p

For \(\Delta f(n)=f(n)-f(n-1)\), every f in C satisfies
\[
 \Delta f(a^k)=\Delta f(a)\qquad(a\ge2,\ k\ge1).
\]
`PrimePowerTarget.closureWithConstants_difference_pow` extends the existing squarefree jump relation to the closure with constants.

If x is an actual QHilbert vector with physical coordinates \(\phi(F_p(n))\), membership x in C forces
\[
 \boxed{\phi(k)=\phi(0)+k\bigl(\phi(1)-\phi(0)\bigr)\quad(k\ge0).}
\]
This is `PrimePowerTarget.log_transform_affine_of_mem_closureWithConstants`, valid for every integer p greater than one. Evaluating jumps at successive powers of p proves that all increments of \(\phi\) agree.

In particular, `PrimePowerTarget.geometric_log_transform_base_eq_one` proves that an actual vector with coordinates \(r^{F_p(n)}\) can belong to C only if r=1. The theorem includes the existence of the QHilbert vector as an explicit hypothesis. Separately, the elementary comparison \(n/p<p^{F_p(n)}\le n\) shows that the untempered factor \(p^{F_p}\) is not in L²(Q). These facts explain why exponentiation alone does not produce a legal approximant. The logarithmic target itself is affine and is not excluded by this obstruction.

## Informal valuation basis and sparse target expansion

This section is an ordinary mathematical argument, **not a Lean formalization**. For each prime q, the valuation \(V_q=v_q(N)\) has geometric law
\[
 Q(V_q=v)=(1-q^{-2})q^{-2v},
\]
and the valuations are jointly independent. Note that \(V_p\) and \(F_p\) are different random variables.

For \(0<r<1\), normalized Meixner polynomials are
\[
 e_m^{(r)}(v)=(-\sqrt r)^m
  \sum_{j=0}^{m}\binom mj\binom vj(1-r^{-1})^j.
\]
The standard orthogonality and norm are described in [DLMF §18.19](https://dlmf.nist.gov/18.19). A direct generating function is
\[
 G_v(t)=\frac{(1+t/\sqrt r)^v}{(1+\sqrt r\,t)^{v+1}},
 \qquad \mathbb E[G_V(t)G_V(s)]=\frac1{1-ts}
\]
near zero. Polynomial density follows by applying analytic uniqueness to
\(\sum_v f(v)(1-r)r^v z^v\), analytic on \(|z|<r^{-1/2}\), when f is orthogonal to all polynomials.

Tensoring the local bases gives the ambient basis indexed by positive integers
\[
 E_a(n)=\prod_{q^m\parallel a} e_m^{(q^{-2})}(v_q(n)),\qquad E_1=1.
\]
Its completeness also uses convergence of finite-prime conditional expectations. Neither that tensor completeness nor the actual valuation independence bridge is supplied by a finite abstract Bernoulli product model. The addition `unitMonomial_gram` establishes the normalized finite Boolean product Gram matrix; its scope is that finite abstract model, with final project acceptance determined by checkpoint.

Write \(N=p^{V_p}M_p\). Independence of \(V_p\) and \(M_p\), together with
\(F_p(N)=V_p+F_p(M_p)\), gives the informal expansion
\[
 F_p=\mu_p1+\frac p{p^2-1}E_p+
  \sum_{\substack{a>1\\(a,p)=1}}\alpha_{p,a}E_a,
 \qquad \alpha_{p,a}=\langle F_p,E_a\rangle_Q.
\]
Every coefficient with \(p\mid a\) and \(a\ne p\) is zero. For F₂ the coefficient at E₂ is 2/3; for F₃ the coefficient at E₃ is 3/8.

For any f with coefficients \(\widehat f(a)=\langle f,E_a\rangle_Q\), the full Parseval error is
\[
\begin{aligned}
 \|F_p-f\|_Q^2
 &=|\mu_p-\widehat f(1)|^2
  +\left|\frac p{p^2-1}-\widehat f(p)\right|^2\\
 &\quad+\sum_{\substack{a>1\\(a,p)=1}}
       |\alpha_{p,a}-\widehat f(a)|^2
  +\sum_{\substack{p\mid a\\a\ne p}}|\widehat f(a)|^2.
\end{aligned}
\]
All four terms are required. In particular, projecting onto the target's nonzero coefficient support has not been shown to preserve C. The ambient basis vector
\(E_p=((p^2-1)V_p-1)/p\) itself violates the legal square-jump relation; its defect is \((p^2-1)/p\).

## Remaining legal-basis obligation

Informally, apply Gram–Schmidt to the exhaustive dictionary
\(1,g_2,g_3,g_5,g_6,g_7,g_{10},\ldots\), choosing the first two vectors to be 1 and \(\eta_2\). This produces a complete orthonormal basis \((\psi_j)\) of C. Finite independence follows by evaluating a relation at a common multiple, then at 1, and then examining jumps at its conductors in increasing order.

The exact membership condition is Parseval saturation:
\[
 F_p\in C\quad\Longleftrightarrow\quad
 \sum_{j\ge0}|\langle F_p,\psi_j\rangle_Q|^2=\|F_p\|_Q^2.
\]
For F₂ the outstanding equality becomes
\[
 \boxed{\sum_{j\ge2}|\langle F_2,\psi_j\rangle_Q|^2
       =\operatorname{Var}_Q(F_2)-\frac13.}
\]
This equality remains **Open**. Bessel's inequality, ambient orthonormality, and the first parity coefficient do not discharge it. Further formalization should retain the complete remainder while constructing legal approximants or proving this saturation identity.
