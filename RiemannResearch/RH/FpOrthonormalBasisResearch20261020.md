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

## Actual finite-prime Hilbert transfer (21 October 2026 UTC)

The pre-existing module `PrimeValuationIndependence.lean` already proves the actual geometric marginal, independence of prime valuations, and finite Boolean configuration probabilities. These are not new results of this continuation.

The new module `QFinitePrimeBasis.lean` uses that law to prove
`integral_boolean_observable` and `booleanLift_inner`: every real observable of finitely many distinct-prime divisibility indicators has exactly its finite-product expectation and Gram form under the actual integer Q law. `booleanLift` constructs the corresponding QHilbert vector, with the physical zero coordinate removed and boundedness discharged.

For a finite injective family of primes \(p_i\), let \(q_i=p_i^{-2}\) and let
\(U_A\) be the actual lift of `FinitePrimeCentered.unitMonomial q A`.
`primeUnitVector_orthonormal` proves
\[
 \langle U_A,U_B\rangle_Q=\mathbf1_{\{A=B\}}.
\]
For every actual QHilbert vector f and every finite collection S of subsets,
`primeUnitVector_energy_exact` proves the complete identity
\[
 \boxed{\|f\|_Q^2
 =\sum_{A\in S}|\langle f,U_A\rangle_Q|^2+
 \left\|f-\sum_{A\in S}\langle f,U_A\rangle_Q U_A\right\|_Q^2.}
\]
There is no closure-membership or residual-vanishing hypothesis hidden in this identity. It applies to both logarithmic targets as actual QHilbert vectors.

These Boolean coordinates observe only whether each valuation is positive. They do not resolve higher valuation levels, prove completeness in the full Q space, or assert that the vectors belong to C. The following continuation computes all same-prime wavelet levels; Meixner expansion and legal Parseval saturation remain separate obligations.

## Exact same-prime wavelet coefficients (21 October 2026 UTC)

The existing `QDivisorHilbertBasis.lean` already supplies a complete ambient
arithmetic wavelet basis. This continuation reuses that basis rather than
reproving its orthogonality or claiming that it is a legal basis for C.

Put \(D_{p,k}(n)=\mathbf1_{\{p^k\mid n\}}\), \(W_{p,0}=1\), and
\[
 W_{p,k+1}
 =\frac{p^{2(k+1)}D_{p,k+1}-p^{2k}D_{p,k}}
        {p^k\sqrt{p^2-1}}.
\]
`QPrimePowerHilbertFrame.lean` identifies the numerator with the existing
arithmetic divisor wavelet and proves that all \(W_{p,k}\) form an actual
orthonormal family. It does not claim that this one-prime subfamily spans
the entire ambient space.

For \(\mu_p=\langle F_p,1\rangle_Q\),
`QPrimePowerWaveletCoefficients.lean` proves
\[
 \langle F_p,D_{p,k}\rangle_Q=p^{-2k}(\mu_p+k),\qquad
 \boxed{\langle F_p,W_{p,k+1}\rangle_Q
   =\frac1{p^k\sqrt{p^2-1}}.}
\]
These are coefficients of the floor logarithm `Nat.log p n`; the target
has not been replaced by the valuation. In particular the dyadic
coefficients are \(2^{-k}/\sqrt3\), and the triadic coefficients are
\(3^{-k}/\sqrt8\). These wavelets differ from the informal Meixner
polynomials below, so their coefficient lists differ.

Write \(a_{p,0}=\mu_p\) and
\(a_{p,k+1}=1/(p^k\sqrt{p^2-1})\). For any finite set S of mode indices and
any real, possibly signed trial coefficients \(c_k\), the checked theorem
`qTarget_primePower_error_exact` retains the complete identity
\[
 \boxed{\left\|F_p-\sum_{k\in S}c_kW_{p,k}\right\|_Q^2
 =\sum_{k\in S}(a_{p,k}-c_k)^2+
   \left\|F_p-\sum_{k\in S}a_{p,k}W_{p,k}\right\|_Q^2.}
\]
`qTarget_primePower_energy_exact` gives the corresponding captured-energy
identity with the same residual. No residual is asserted to vanish.
Membership of the wavelets in C, Meixner orthogonality/completeness,
mixed-prime target coefficients, and legal Parseval saturation are not
discharged by these results. The first dyadic coefficient remains
\(1/\sqrt3\), with captured energy \(1/3\).

## Exact mixed-prime cancellation (21 October 2026 UTC)

The modules QPrimePowerMixedWavelet and QPrimePowerMixedCoefficients prove
the coprime factorization and exact target cancellation. Write V_t for the
raw divisor wavelet, U_t for its normalization, and D_d for divisibility by d.
For prime p, k at least zero, r>1, and (p,r)=1,
\[
 V_{p^{k+1}r}=\sum_{d\mid r}\mu(r/d)d^2
 \left(p^{2(k+1)}D_{p^{k+1}d}-p^{2k}D_{p^kd}\right).
\]
Every signed Moebius term is retained. The exact dilation identity is
\[
 p^{2k}\langle F_p,D_{p^kd}\rangle_Q
 =\langle F_p,D_d\rangle_Q+k/d^2\qquad(d>0).
\]
Consequently,
\[
 \boxed{\langle F_p,V_{p^{k+1}r}\rangle_Q
 =\sum_{d\mid r}\mu(r/d)=0.}
\]
Normalization preserves this cancellation. It applies to both F_2 and F_3;
the target remains Nat.log p n, not the prime valuation.

For any finite collection S of these mixed conductors and arbitrary f,
the theorem qTarget_mixed_modes_error_exact gives
\[
 \boxed{\|F_p-f\|_Q^2
 =\sum_{t\in S}\langle f,U_t\rangle_Q^2+
 \left\|F_p-f+\sum_{t\in S}\langle f,U_t\rangle_Q U_t\right\|_Q^2.}
\]
The signed coefficients and full residual are retained.
Ambient removal of these modes has not been shown to preserve C.

Saved-source check job_BkDWoFzxSF1ltu_DvyDoKvPsQrHn_huG succeeded
(exit 0, 39.785 seconds), importing both modules. Axiom inspection of the
factorization, cancellation, and exact-error theorems reported only
propext, Classical.choice, and Quot.sound. Earlier timeout jobs are
terminal and superseded by this successful check.
Final project acceptance and publication remain subject to the checkpoint.
The existing log_mul_power proof is now public for reuse.
Meixner completeness, legal Parseval saturation, and membership of F_2 and
F_3 in closureWithConstants remain open.

## Infinite same-prime projection (21 October 2026, Pacific time)

The module `QPrimePowerInfiniteProjection.lean` now sums the nonconstant
same-prime modes in the actual complete Q Hilbert space. With
\(a_{p,k}=1/(p^k\sqrt{p^2-1})\), define
\[
 P_p=\sum_{k\ge0}a_{p,k}W_{p,k+1}.
\]
The vector series is absolutely summable in norm, its initial finite sums
converge to P_p, and every coefficient is retained:
\[
 \langle P_p,W_{p,k+1}\rangle_Q=a_{p,k},\qquad
 \langle1,P_p\rangle_Q=0,\qquad
 \boxed{\|P_p\|_Q^2=\frac{p^2}{(p^2-1)^2}.}
\]
The residual F_p-P_p is orthogonal to every nonconstant same-prime mode.
Writing \(\mu_p=\langle F_p,1\rangle_Q\), the full exact identity is
\[
 \boxed{\|F_p\|_Q^2=\mu_p^2+\frac{p^2}{(p^2-1)^2}
       +\|F_p-\mu_p1-P_p\|_Q^2.}
\]
For any real signed coefficients c_k whose vector series
\(T_c=\sum_{k\ge0}c_kW_{p,k+1}\) converges unconditionally in QHilbert,
\[
 \boxed{\|F_p-T_c\|_Q^2
       =\|P_p-T_c\|_Q^2+\|F_p-P_p\|_Q^2.}
\]
Both full residuals are retained; no sign restriction or assumed legality
is imposed on the trial coefficients.

The normalized vector \(U_p=(p^2-1)P_p/p\) has unit norm square and
\(\langle F_p,U_p\rangle_Q=p/(p^2-1)\).
Thus all dyadic modes capture 4/9 and all triadic modes capture 9/64;
their normalized sum directions have target coefficients 2/3 and 3/8.
These infinite-sum directions differ from the individual first wavelets.
The already established parity coefficient remains 1/sqrt(3), with energy 1/3.

Open: identify P_p pointwise with the centered valuation
\(v_p-1/(p^2-1)\), identify U_p with the first Meixner polynomial,
formalize higher Meixner orthogonality/completeness, and establish legal
Parseval saturation. None of these projection statements supplies membership
of F_2 or F_3 in closureWithConstants.

The coherent extended candidate passed job_xhIgmpEinD3yDG8yCzNc1X4Vw9CJL1Xl
(exit 0, 8.177 seconds). Saved-source audit job_X7L7Pa-gdRGA1ipw_C70373N-JKbpJT4 also passed
(exit 0, 14.589 seconds); six inspected declarations use only propext,
Classical.choice, and Quot.sound. Final project publication is checkpoint-gated.
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
Its completeness also uses convergence of finite-prime conditional expectations. The actual valuation independence and geometric marginals are already established in `PrimeValuationIndependence.lean`; tensor completeness and Meixner orthogonality are not yet formalized here. `unitMonomial_gram` is the finite abstract Boolean calculation, and `QFinitePrimeBasis.lean` now transfers it into the actual QHilbert space as described above.

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
