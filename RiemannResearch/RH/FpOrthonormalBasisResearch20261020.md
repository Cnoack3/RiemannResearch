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

The additions formalize the legal parity pair, exact target coefficients and residual identities, and the complete legal Gram–Schmidt Hilbert basis described below. The full Meixner tensor basis and target Parseval saturation remain open. Acceptance of each addition is determined by its server checkpoint, rather than the existence of this note.

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

Established below: P_p is the centered valuation and U_p is the first
Meixner polynomial. Higher Meixner orthogonality/completeness and legal
Parseval saturation remain Open. Neither projection supplies membership
of F_2 or F_3 in closureWithConstants.

The coherent extended candidate passed job_xhIgmpEinD3yDG8yCzNc1X4Vw9CJL1Xl
(exit 0, 8.177 seconds). Saved-source audit job_X7L7Pa-gdRGA1ipw_C70373N-JKbpJT4 also passed
(exit 0, 14.589 seconds); six inspected declarations use only propext,
Classical.choice, and Quot.sound. Final project publication is checkpoint-gated.

## Pointwise valuation and first Meixner identification (21 October 2026, Pacific time)

`QPrimePowerValuationProjection.lean` proves the exact adjacent-tail
identity for each weighted wavelet and stabilization at every positive
integer n once the cutoff exceeds v_p(n). Continuity of physical coordinate
evaluation then gives
\[
 \boxed{P_p(n)=v_p(n)-\frac1{p^2-1},\qquad
 U_p(n)=\frac{(p^2-1)v_p(n)-1}{p}.}
\]
The physical coordinate at zero remains anchored to zero.
The first identity is `primePowerProjection_sequence`; the second is
`primePowerProjectionUnit_sequence`. The vector
`primeValuationVector` now supplies an actual Q-Hilbert representative
of v_p, with no assumed square-integrability provider.

Thus the previously checked unit norm, zero mean, and target coefficient
p/(p^2-1) belong to the explicit first Meixner polynomial for parameter
p^(-2). Its F_2/F_3 coefficients are 2/3 and 3/8. The target itself remains
Nat.log p n. Its parity coefficient 1/sqrt(3), energy 1/3, and the full
infinite-projection residual identities are unchanged.

The existing square-jump obstruction now yields unconditional checked
nonmembership of both P_p and U_p in closureWithConstants. This is a
restriction on these ambient basis directions; it is not a nonmembership
theorem for F_p. In particular, separating the centered valuation component
does not prove that either component of a putative legal F_p stays legal.

Saved-source audit job_Le-uksdxS3DuX7sdeqv8fBrU3_jxoPyz passed (exit 0,
12.434 seconds). Six inspected declarations use only propext, Classical.choice,
and Quot.sound. Final project publication is checkpoint-gated.

Open: higher Meixner orthogonality, tensor completeness, exact remaining
cofactor coefficients, legal Parseval saturation, and F_2/F_3 closure membership.

## Prime-free cofactor residual (22 October 2026, Pacific time)

The module `QPrimePowerCofactorResidual.lean` identifies the complete
remaining vector without replacing the floor logarithm by a valuation.
Put \(M_p(n)=n/p^{v_p(n)}\) for \(n>0\), and
\(\mu_p=\langle F_p,1\rangle_Q\). The checked arithmetic split and actual
Q-Hilbert representative give
\[
 F_p(n)=v_p(n)+F_p(M_p(n)),\qquad
 \mathbb E_Q F_p(M_p)=\mu_p-\frac1{p^2-1}.
\]
Consequently the full projection residual is
\[
 \boxed{R_p(n)=F_p(M_p(n))-\left(\mu_p-\frac1{p^2-1}\right),\qquad
 R_p=F_p-\mu_p1-P_p.}
\]
Its physical zero coordinate stays anchored to zero. The declarations
`primeCofactorResidual_sequence` and `primeCofactorResidual_sequence_mul_power`
prove this formula and \(R_p(p^k n)=R_p(n)\) for every positive n.

The exact complete energy and weighted residual are retained:
\[
 \|F_p\|_Q^2=\mu_p^2+\frac{p^2}{(p^2-1)^2}+\|R_p\|_Q^2,\qquad
 \|R_p\|_Q^2=\frac1{\zeta(2)}\sum_{n\ge1}
 \frac{[F_p(M_p(n))-(\mu_p-1/(p^2-1))]^2}{n^2}.
\]
The second equality is `primeCofactorResidual_norm_sq_series`.
Since \(R_p(p+1)-R_p(1)=1\), completing the two weighted squares gives
`primeCofactorResidual_energy_lower_bound`:
\[
 \boxed{\|R_p\|_Q^2\ge\frac1{\zeta(2)(1+(p+1)^2)}>0.}
\]
Thus the respective residual energies for F_2 and F_3 are at least
\(1/(10\zeta(2))\) and \(1/(17\zeta(2))\). These are lower bounds for the
ambient same-prime residual, not distances to the legal squarefree closure.
The parity coefficient and all previously proved signed error identities
remain unchanged. Neither closure membership nor nonmembership of F_p
follows from a nonzero ambient cofactor residual.

Saved-source audit job_N4o66XJr8nz6ncuK5mBkF_FW4tgnS-PP passed (exit 0,
12.964 seconds). Six inspected declarations use only propext, Classical.choice,
and Quot.sound. Final project publication is checkpoint-gated.
Open: higher Meixner orthogonality/completeness, the remaining cofactor
coefficients, legal Parseval saturation, and F_2/F_3 closure membership.

## Complete coprime-conductor expansion (22 October 2026, Pacific time)

`QPrimePowerCofactorExpansion.lean` uses the previously proved complete
ambient arithmetic divisor basis \(B_t=\mathrm{normalizedDivisorWavelet}(t)\).
It does not assume or establish a full Meixner basis. Put
\(S_p=\{t>1:\gcd(p,t)=1\}\) and \(\alpha_{p,t}=\langle F_p,B_t\rangle_Q\).
Exact dilation moments cancel every residual coefficient with p dividing t;
orthogonality removes the mean and valuation terms at every t in S_p:
\[
 \langle R_p,B_t\rangle_Q=\mathbf1_{S_p}(t)\alpha_{p,t}.
\]
`primeCofactorResidual_inner_basis` proves this formula for every
positive conductor, including the constant and all pure prime powers.

Completeness then gives the unconditionally convergent Hilbert-space expansion
and its full Parseval energy:
\[
 \boxed{R_p=\sum_{t\in S_p}\alpha_{p,t}B_t,\qquad
 \|R_p\|_Q^2=\sum_{t\in S_p}\alpha_{p,t}^2.}
\]
These are `primeCofactorResidual_hasSum_coprime` and
`primeCofactorResidual_parseval_coprime`. Lean represents the restricted
series by zero coefficients outside S_p. The full target is therefore
\[
 \boxed{F_p=\mu_p1+P_p+\sum_{t\in S_p}\alpha_{p,t}B_t,\qquad
 \|F_p\|_Q^2=\mu_p^2+\frac{p^2}{(p^2-1)^2}
                  +\sum_{t\in S_p}\alpha_{p,t}^2.}
\]
The complete previously retained residual is now expressed by its exact
infinite coefficient energy; it has not been set to zero.

For arbitrary actual Q-Hilbert trial vector f, put \(g=f-\mu_p1-P_p\).
`qTarget_coprime_expansion_error_exact` proves
\[
 \boxed{\|F_p-f\|_Q^2
 =\sum_{t\ge1}
  [\mathbf1_{S_p}(t)\alpha_{p,t}-\langle g,B_t\rangle_Q]^2.}
\]
Every signed discrepancy and every coefficient outside S_p remains present.
No sign condition, finite support, or legal-closure membership is assumed.

The theorem applies to F_2 and F_3, which remain floor-logarithm targets.
Their existing same-prime unit coefficients remain 2/3 and 3/8; the parity
coefficient remains 1/sqrt(3), with energy 1/3. The continuation
FpCoprimeCoefficientsResearch20261022.md gives exact convergent arithmetic
coefficient formulas and first numerical evaluations. Elementary constant-only
closed forms are not obtained. Higher Meixner completeness,
legal Parseval saturation, and F_2/F_3 membership in closureWithConstants
remain Open. A concrete single-mode ambient projection now fails to preserve
that legal closure (QDivisorModeLegality.lean); no whole-support preservation
claim is used.

Saved-source audit job_DNkLbnBu24d0gJ_Hm4zVpcN_5yEK5Otx passed (exit 0,
13.484 seconds). All six inspected declarations use only propext,
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

The general infinite-basis argument in this section remains informal. The first three local modes are now checked in Lean, as detailed below. For each prime q, the valuation \(V_q=v_q(N)\) has geometric law
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
Its completeness also uses convergence of finite-prime conditional expectations. The actual valuation independence and geometric marginals are already established in `PrimeValuationIndependence.lean`; tensor completeness and general Meixner orthogonality remain open; the degree-zero, degree-one and degree-two family is checked below. `unitMonomial_gram` is the finite abstract Boolean calculation, and `QFinitePrimeBasis.lean` now transfers it into the actual QHilbert space as described above.

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

## Checked quadratic Meixner mode (23 October 2026)

QPrimePowerMeixnerTwo.lean proves the degree-two part of the valuation
proposal in the actual integer Zipf Hilbert space. Put \(x=p^2\),
\(d=x-1\), and \(v=v_p(n)\). The already checked first mode is
\(U_{p,1}=(dv-1)/p\). The new vector has physical coordinates
\[
 U_{p,2}(n)=\frac{d^2v(v-1)/2-2dv+1}{x}\qquad(n>0).
\]
This matches \(e_2^{(p^{-2})}\) in the normalization above.

The construction first sums
\(T_p=\sum_{k\ge0}k\,a_kW_{p,k+1}\), where
\(a_k=1/(p^k\sqrt d)\) and \(W\) is the already checked prime-power
wavelet frame. Absolute Q-norm convergence is proved. Its physical
coordinates are \(v(v-1)/2-v/d\), and the exact identities are
\[
 \langle F_p,T_p\rangle_Q=\langle P_p,T_p\rangle_Q=x/d^3,
 \qquad \|T_p\|_Q^2=x(x+1)/d^4.
\]
The normalized difference \(U_{p,2}=(d^2/x)(T_p-P_p/d)\) is therefore
a unit vector orthogonal to the constant and the first mode.
primeMeixnerTriple_orthonormal proves orthonormality of
\((1,U_{p,1},U_{p,2})\), without an abstract Boolean-law assumption.

qTarget_inner_primeMeixnerTwo gives the exact coefficient
\(\langle F_p,U_{p,2}\rangle_Q=0\) for every prime p, hence for p=2
and p=3. With \(\mu_p=\langle F_p,1\rangle_Q\), the theorem
qTarget_meixner_two_signed_error retains the entire signed trial error:
\[
 \|F_p-(\mu_p1+P_p+aU_{p,2})\|_Q^2
   =\|F_p-\mu_p1-P_p\|_Q^2+a^2
 \qquad(a\in\mathbb R).
\]
Thus this additional valuation mode captures no additional target energy.
The remaining norm is the full previously constructed cofactor residual;
it has not been discarded or identified with a legal distance.

Established here: the quadratic mode, its unit norm, the three-mode Gram
identity, and its zero target coefficient. Open: degrees three and higher,
full local Meixner completeness, tensor completeness, and actual legal
Parseval saturation for F_2 and F_3. No legal-closure membership provider
is supplied, and F_p continues to mean Nat.log p n.

## Complete legal basis and remaining saturation obligation

The module QSquarefreeCompleteBasis.lean formalizes the exhaustive legal
construction (22 October 2026, Pacific time). Its dictionary begins with 1
and the positive parity unit eta_2, then includes every squarefreeAtom in
conductor order. Nonsquarefree slots and dependent innovations are omitted
by indexing the normalized Gram–Schmidt sequence at its nonzero entries.
No unproved independence assumption is used.

legalVector_closed_span proves that these actual Q-Hilbert vectors have
closed span exactly C. legalHilbertBasis is a complete Hilbert basis of C,
indexed by a subtype of the natural numbers. This establishes legal
completeness, separately from ambient divisor or Meixner completeness.
The first two retained vectors are exactly 1 and eta_2, and the F_2 parity
coefficient remains 1/sqrt(3), with energy 1/3.

Write psi_i for these vectors and P_C for the actual orthogonal projection
onto C. legalProjection_hasSum gives unconditional convergence in Q norm:
\[
 P_C f=\sum_i\langle f,\psi_i\rangle_Q\psi_i.
\]
legalBasis_energy_exact and legalBasis_error_exact retain the full identities
\[
 \boxed{\|x\|_Q^2=\sum_i\langle x,\psi_i\rangle_Q^2+\|x-P_Cx\|_Q^2,}
\]
\[
 \boxed{\|x-f\|_Q^2
 =\sum_i(\langle x,\psi_i\rangle_Q-\langle f,\psi_i\rangle_Q)^2
   +\|x-P_Cx\|_Q^2\quad(f\in C).}
\]
Every signed discrepancy remains present. The last norm is the genuine
orthogonal legal residual, distinct from the previously studied ambient
same-prime/cofactor residual.

mem_closureWithConstants_iff_parseval establishes
\[
 F_p\in C\quad\Longleftrightarrow\quad
 \sum_i|\langle F_p,\psi_i\rangle_Q|^2=\|F_p\|_Q^2.
\]
The equivalence is now formal; its right-hand equality for F_2 and F_3 is
still **Open**. No target-membership provider or RH conclusion is supplied.
Meixner degrees three and higher, and full completeness, remain Open.

Candidate job_e3oq28sN_Vq0cgJpLb5SW_0L-43fRiIY passed (exit 0; 8.481 seconds).
Saved-source audit job_-47gYwRlpprwYA2v7t3qWmpxZZRdOH7k passed (exit 0;
14.440 seconds). All six inspected declarations use only propext,
Classical.choice, and Quot.sound. Final project publication is checkpoint-gated.

## Threshold evaluation of the remaining coefficients

QPrimePowerThresholdSeries.lean now proves exact threshold expansions of the
dilated means and the full signed Moebius threshold remainder. For prime-power
conductors it gives convergent finite integer-interval sums, with the entire
nonnegative level tail retained. See the checked-threshold section of
FpCoprimeCoefficientsResearch20261022.md for formulas.
QPrimePowerThresholdTail.lean now proves the explicit geometric truncation
bound, the signed Moebius coefficient-error interval, and a certified error
bound for the finite prime-power interval sums. QPrimePowerRationalCertificates
now certifies exact rational evaluation and outward rational endpoints for
prime-power conductors, with fully discharged examples [0.397, 0.403] for
<F_2,B_3> and [0.141, 0.146] for <F_3,B_2>. QDivisorRationalCertificates now also proves general signed composite-conductor
rational certification, with examples [-0.004, 0.005] for <F_2,B_15> and
[0.059, 0.068] for <F_3,B_10>. Legal Gram/Parseval saturation remains open. These coefficient identities apply to the
actual Zipf law and Nat.log targets. They provide no legal Parseval saturation
or membership provider and do not change any full norm residual above.

## Complete valuation-level basis and exact target projection (23 October 2026)

PrimeValuationHilbertBasis.lean defines the actual closed subspace \(V_p\)
of Q-Hilbert vectors satisfying
\(f(n)=f(p^{v_p(n)})\) for every positive n. This is a physical coordinate
condition; it does not assume the desired dictionary is dense.

Put \(m_{p,k}=p^{-2k}-p^{-2(k+1)}>0\). The normalized exact-level vectors
\[
 L_{p,k}(n)=\frac{\mathbf 1_{\{v_p(n)=k\}}}{\sqrt{m_{p,k}}}
 \qquad(n>0)
\]
form a complete Hilbert basis of \(V_p\).
valuationUnit_orthonormal proves the Gram identity under the actual integer
Zipf law. eq_zero_of_orthogonal_valuationUnit proves totality: pairing with
each level determines the value at \(p^k\), hence every positive coordinate.
valuationHilbertBasis packages completeness, and valuation_hasSum and
valuation_parseval give unconditional reconstruction and the full energy:
\[
 f=\sum_{k\ge0}\sqrt{m_{p,k}}\,f(p^k)L_{p,k},
 \qquad
 \|f\|_Q^2=\sum_{k\ge0}m_{p,k}f(p^k)^2
 \quad(f\in V_p).
\]

QPrimePowerValuationBasisProjection.lean proves that the existing
\(A_p=\mu_p1+P_p\) is optimal among **all** square-integrable valuation-only
approximants, not just finite polynomial or wavelet trials. With
\(\mu_p=\langle F_p,1\rangle_Q\), its coordinates are
\(A_p(n)=v_p(n)+\mu_p-1/(p^2-1)\).
The complete cofactor residual \(R_p=F_p-A_p\) is orthogonal to \(V_p\).
For every \(f\in V_p\), qTarget_valuation_error_exact and
qTarget_valuation_signed_parseval retain the exact identities
\[
 \boxed{\|F_p-f\|_Q^2=\|R_p\|_Q^2+\|A_p-f\|_Q^2}
\]
and
\[
 \boxed{\|F_p-f\|_Q^2=\|R_p\|_Q^2+
 \sum_{k\ge0}m_{p,k}
 \left(k+\mu_p-\frac1{p^2-1}-f(p^k)\right)^2.}
\]
qTarget_valuation_level_coefficient explicitly gives
\[
 \langle F_p,L_{p,k}\rangle_Q
 =\sqrt{m_{p,k}}\left(k+\mu_p-\frac1{p^2-1}\right).
\]
These formulas apply to p=2 and p=3 without replacing Nat.log by valuation.

Finally, qTarget_inner_valuation_higher proves that every \(f\in V_p\)
orthogonal to both 1 and the first normalized valuation mode has
\(\langle F_p,f\rangle_Q=0\). This supplies a general zero-coefficient
criterion for future higher Meixner modes; their orthogonality hypotheses
must still be proved for the proposed polynomials.

Established: a complete **indicator** basis of the physically defined
valuation space and the exact best-approximation error on that space.
Open: general Meixner polynomial orthogonality and completeness, tensor
completeness, and F_2/F_3 legal Parseval saturation. Neither V_p nor its
basis is asserted to be the legal squarefree closure. The positive
cofactor residual remains fully present; it is not a legal-distance bound.

## Complete prime-power wavelet basis of the physical valuation space (2026-10-24)

QPrimePowerWaveletCompleteness.lean proves that the existing primePowerFrame,
restricted to the actual Q-Hilbert subspace V_p, is a complete orthonormal
basis. valuationWaveletBasis bundles this basis. The proof first transfers
annihilation of the normalized wavelets to every prime-power divisibility
tail, using the adjacent-tail recurrence and the constant vector. Differences
of tails then annihilate every exact-level indicator, whose totality was
already proved. No new distributional or independence hypothesis is assumed.

valuationWavelet_hasSum reconstructs every f in V_p unconditionally in the
ambient Q norm. valuationWavelet_signed_parseval proves, for all f,g in V_p,
the exact identity
\[
 \|f-g\|_Q^2=\sum_{k\ge0}
   (\langle f,B_{p^k}\rangle_Q-\langle g,B_{p^k}\rangle_Q)^2.
\]
All signed coefficient differences and the entire infinite series remain.
Combined with the previously proved orthogonality of the cofactor residual,
this identifies a complete coordinate system for valuation-only approximation;
it does not remove that residual from the floor-logarithm expansion.

The coherent candidate passed job_twb3lRa6q-iRwQlNRoroHkBdo0REPo8D
(exit 0, verified=true, 5.454 seconds). Saved-source audit
job_PFlwyt32G7ptFm604tDTmgQwnPHrfqTU passed in 11.282 seconds; all four
inspected declarations use only propext, Classical.choice and Quot.sound.
Aggregate publication validation is required by the containing checkpoint.

This completes the existing wavelet frame inside the physically specified V_p.
It is not a Meixner polynomial completeness theorem. General Meixner and tensor
completeness, and actual F_2/F_3 legal Parseval saturation, remain open.
F_p continues to mean Nat.log p n, not the prime valuation.

## Explicit invertible level/wavelet coordinate transform (2026-10-24)

QPrimePowerCoordinateTransform.lean defines
C_p(k,j)=<B_{p^k},L_{p,j}>_Q, where L is the normalized exact-level basis.
Writing m_j=valuationMass p j and J_2=qJordanTwo, it proves
C_p(0,j)=sqrt(m_j) and, for k>=0,
C_p(k+1,j)=sqrt(m_j)/sqrt(J_2(p^(k+1))) times
[p^(2(k+1))*1_{k+1<=j}-p^(2k)*1_{k<=j}].
The negative boundary contribution is retained.

Both infinite matrix identities are checked with HasSum:
sum_j C_p(k,j) C_p(l,j)=delta(k,l), and
sum_k C_p(k,j) C_p(k,l)=delta(j,l).
For every actual valuation observable f, the forward transform takes
a_j=sqrt(m_j)f(p^j) to its wavelet coefficients; the transpose recovers a_j.
valuationCoordinateEquiv bundles an invertible linear isometry on all real
l2 sequences, and valuationCoordinateEquiv_apply proves its matrix series.
Thus this is a complete infinite transform, without an unproved summability
assumption or a finite-dimensional replacement.

Consumer: candidate Meixner coefficient sequences can now be compared in
either complete basis. This does not prove the proposed polynomials are
orthonormal or complete. General Meixner/tensor completeness and F_2/F_3 legal
saturation remain open. F_p is Nat.log p n, not v_p(n); its existing cofactor
residual is not removed by changing valuation coordinates.

Candidate job_wov3AlEeilkJAQfcrvLW7V7orvO7kzcs passed (5.556 seconds).
Saved-source audit job_o88GHUlOZT-uhBv7aZJdzLcLgb9Q5tro passed in 11.810
seconds. All six inspected declarations use only propext, Classical.choice
and Quot.sound. Aggregate validation and publication are certified by the
containing server checkpoint.

## Complete cross-prime valuation geometry (2026-10-24)

QPrimeValuationCrossGeometry.lean extends cross-prime wavelet orthogonality
to every pair f in V_p and g in V_q, for distinct primes p and q:
<f,g>_Q=<f,1>_Q<1,g>_Q. No boundedness, finite polynomial degree, or finite
wavelet-support hypothesis is imposed. The proof maps each complete wavelet
HasSum through the continuous inner product, rather than exchanging
unjustified infinite sums. Existing measure-theoretic prime independence
remains available separately.

Writing mu_f=<f,1>_Q and mu_g=<g,1>_Q, the exact identities are
||f-g||_Q^2=||f-mu_f*1||_Q^2+||g-mu_g*1||_Q^2+(mu_f-mu_g)^2
and
||f-g||_Q^2=||f-mu_f*1||_Q^2+||g-mu_f*1||_Q^2.
Thus mu_f*1 (which belongs to V_q) is the unique best approximation to f
from the entire V_q. The centered spaces are orthogonal, and any vector
belonging to both physical spaces equals its constant mean. All norm
remainders and the signed mean discrepancy are retained.

This supplies complete-space geometry for future tensor/Meixner work.
It is not a full tensor basis theorem. In particular F_p=Nat.log p n is
not substituted for an arbitrary vector of V_p: its cofactor residual
remains, and neither F_2 nor F_3 legal membership is decided here.
General Meixner/tensor completeness and legal saturation remain Open.

The coherent candidate passed job_mQH4D2WWBp02lwHa3kZkZ8b2KQ6XXVjn
in 5.344 seconds. Saved-source audit job_fodTgTKwaLxIGGvOODLiJeK2qQzrLwwS
passed in 11.380 seconds. All six inspected declarations use only propext,
Classical.choice and Quot.sound. Final publication remains gated by
aggregate-project validation in the containing server checkpoint.

## All-order monomial-weighted valuation lifts (2026-10-24)

QPrimePowerMonomialLift.lean constructs S_(p,m) for every natural m as the
absolutely Q-norm summable series sum_k k^m c_(p,k) B_(p^(k+1)), with the
already computed c_(p,k)=<F_p,B_(p^(k+1))>. Its physical coordinates are
S_(p,m)(n)=sum_(k<v_p(n)) k^m-v_p(n)^m/(p^2-1), for n>0.
The convention at m=0 is the usual Lean power convention 0^0=1.
Every lift is centered and lies in the physically defined valuationSpace.

The exact complete Gram series is
<S_(p,m),S_(p,r)>_Q=sum_k k^(m+r)c_(p,k)^2.
primePowerMonomialLift_gram_hasSum proves convergence, using the previously
established all-order moment summability. The exact target pairing is
<F_p,S_(p,m)>_Q=sum_k k^m c_(p,k)^2, with no truncated tail or dropped term.

For m=2 the checked physical formula is the centered cubic
v(v-1)(2v-1)/6-v^2/(p^2-1).
This is a raw vector for subsequent cubic Meixner orthogonalization, not a
normalized third Meixner mode. More generally the finite power-sum formula
provides all raw orders for higher polynomial Gram calculations.
No polynomial-family orthogonality or completeness has been assumed.

The coherent candidate passed job_T7H0Fn2HBfLaokZCZ4GECZlZyrH7WGlc
in 6.886 seconds. Saved-source audit and aggregate publication validation
remain required by the containing checkpoint.
Open: higher Meixner normalization/orthogonality, polynomial and tensor
completeness, and actual F_2/F_3 legal saturation. All earlier cofactor and
legal residuals remain; F_p still means Nat.log p n.

## All-order orthonormal polynomial innovations (2026-10-24)

QPrimePowerPolynomialOrthonormal.lean now proves that the entire raw family
S_(p,m) is linearly independent. A finite dependence has wavelet coordinates
c_(p,k) times a real polynomial evaluated at k. Since c_(p,k) is nonzero,
that polynomial vanishes at every natural number and hence is zero.

Let E_(p,j)=gramSchmidtNormed(S_(p,*))(j). All innovations have unit norm:
valuationPolynomialMode_orthonormal proves actual-Q orthonormality at every
order, without deleting zero indices or assuming independence.
valuationPolynomialFrame includes qOne followed by every E_(p,j) and is
orthonormal. Every mode is centered and belongs to the physical valuation
space V_p. valuationPolynomialMode_span_Iic preserves each finite initial
span, so the j-th mode uses only raw lifts with indices at most j.
This is an algebraic-span result, not a density theorem.

The positive first mode E_(p,0) is exactly primePowerProjectionUnit.
qTarget_valuationPolynomialMode_coefficient proves
<F_p,E_(p,j)> = if j=0 then p/(p^2-1) else 0.
Thus every higher Gram-Schmidt mode has its zero target coefficient proved
with all orthogonality obligations discharged, for every prime p and hence
for F_2 and F_3. F_p remains Nat.log p n throughout.

For arbitrary real mu, b, all signed coefficients a_j, and every finite s,
qTarget_valuationPolynomial_signed_error proves the complete equality
||F_p - (mu*1 + b*E_(p,0) + sum_(j in s) a_j E_(p,j+1))||^2
= ||R_p||^2 + (mu_p-mu)^2 + (p/(p^2-1)-b)^2 + sum_(j in s) a_j^2.
The full cofactor residual remains. No positivity restriction is imposed on
trial coefficients and no missing mode or tail is declared to vanish.

This discharges all-order normalization and orthogonality for the explicitly
defined Gram-Schmidt family. Open: identification of this family with
classical closed Meixner formulas, polynomial density/completeness in V_p,
tensor completeness, and actual F_2/F_3 legal Parseval saturation.
It does not replace the existing complete wavelet or level-indicator bases,
and it does not assert membership in closureWithConstants.

Coherent candidate job_mb3Iqw9ghMVT9yXTyUS5MlZWljHo4TfZ passed in 7.654 seconds.
Saved-source audit job_UaIovSIcEKbvmxruIk57tpsRmGi6DY5x passed in 14.286
seconds. All six inspected declarations use only propext, Classical.choice,
and Quot.sound. Aggregate-project validation and publication are certified
by the containing Lean-server checkpoint.

## Quadratic Meixner identification of the general family (2026-10-24)

The already exported QPrimePowerPolynomialOrthonormal module now proves
valuationPolynomial_gramSchmidt_one: the second unnormalized innovation is
exactly T_p - P_p/(p^2-1), retaining the signed linear correction.
valuationPolynomialMode_one identifies E_(p,1) with primeMeixnerTwo in the
actual Q Hilbert space, including its positive normalization and sign.
Thus the general family agrees with the explicit normalized valuation
and quadratic Meixner constructions at its first two centered indices.
The physical quadratic formula follows from primeMeixnerTwo_sequence.

The coherent candidate passed job_q49Nuhfk4oHt2RegzIRA-4MbBVkWlOGV
in 7.803 seconds. Saved-source audit job_Z8IObjdhLqmaw4quM78GSpnSY5PO1Pno
passed in 16.667 seconds; both declarations use only propext,
Classical.choice and Quot.sound. Aggregate validation is certified by the
containing publication checkpoint.
Open: closed identification from the cubic onward, polynomial/tensor
completeness, and actual F_2/F_3 legal membership. The complete residual and
signed error identities are unchanged; F_p remains Nat.log p n.

## Explicit normalized cubic Meixner mode (2026-10-24)

QPrimePowerMeixnerThree.lean now closes the cubic identification step.
Write d=p^2-1, P_p=S_(p,0), T_p=S_(p,1), and v=v_p(n). The exact
unnormalized innovation is
C_p=S_(p,2)-(1+4/d)*T_p+(2/d^2)*P_p.
Its checked squared norm is 4*p^6/d^6. Thus the positive normalization
U_(p,3)=d^3/(2*p^3)*C_p has unit norm. For n>0 its full physical formula is
[d^3*v*(v-1)*(v-2)/6 - 3*d^2*v*(v-1)/2 + 3*d*v - 1]/p^3.

valuationPolynomial_gramSchmidt_two identifies the raw innovation with C_p;
valuationPolynomialMode_two identifies E_(p,2) with U_(p,3), including sign.
Consequently the general orthonormal family agrees with the explicit
linear, quadratic, and cubic modes. The proof also supplies exact third
and fourth moments of the squared same-prime wavelet coefficients, using
convergent binomial-geometric HasSum identities with no omitted tail.

qTarget_inner_primeMeixnerThree proves <F_p,U_(p,3)>=0 for every prime p.
For arbitrary real mu,b,c,a, qTarget_meixner_three_signed_error retains
||F_p-(mu*1+b*U_(p,1)+c*U_(p,2)+a*U_(p,3))||^2
=||R_p||^2+(mu_p-mu)^2+(p/d-b)^2+c^2+a^2.
This is the actual integer Q law, and F_p remains Nat.log p n.

Coherent candidate job_ersLHNGROlRBwTWhpnpMlgGqiS8542kN passed in 7.701
seconds. Saved-source audit job_6ZSbUXPUhl6ZRmIgJHc4vu5i9Ws2GCFa passed
in 14.879 seconds; all seven inspected declarations use only propext,
Classical.choice and Quot.sound. Aggregate-project validation and
publication are certified by the containing server checkpoint.
Open: closed formulas from degree four onward, polynomial/tensor
completeness, and actual F_2/F_3 legal Parseval saturation and membership.
The full cofactor residual is retained and is not a distance to the legal
closure; no legal membership follows from this polynomial calculation.

## Infinite signed polynomial trials (2026-10-25)

QPrimePowerPolynomialSeries.lean extends the finite-trial result to every
real sequence a with sum_j a_j^2 finite. valuationPolynomial_summable_iff
proves this is exactly the condition for unconditional Q-norm convergence
of sum_j a_j E_(p,j+1), without requiring absolute coefficient summability.
valuationPolynomial_tsum_coefficient recovers every signed coefficient;
valuationPolynomial_tsum_eq_zero_iff proves injectivity at zero.

For all real mu,b and square-summable a, the exact identity is
||F_p-(mu*1+b*E_(p,0)+sum_j a_j E_(p,j+1))||^2
=||R_p||^2+(mu_p-mu)^2+(p/(p^2-1)-b)^2+sum_j a_j^2.
The proof passes the finite identity through norm-continuous limits.
The entire infinite coefficient energy and the full cofactor residual
are retained; no finite-head truncation or missing tail is asserted zero.

Candidate job_lKXDhf7qO7Bt4tXOCG1YOkHUTuLvUqk3 passed in 6.307 seconds.
Saved-source audit job_si85VkzFYY-13ibGes1B__Vx2Vs-tLtL passed in 13.177
seconds; all four declarations use only propext, Classical.choice and
Quot.sound. Final aggregate validation is certified by the containing
publication checkpoint.
Open: polynomial/tensor completeness, higher closed formulas, and actual
F_2/F_3 legal Parseval saturation. This result describes infinite trials
in the polynomial closed span, not an identification of that span with
all of the valuation space or the legal squarefree closure.

## Polynomial completeness in the physical valuation space (2026-10-25)

The generating-function argument is made rigorous in
[ValuationPolynomialDensity20261025.md](ValuationPolynomialDensity20261025.md).
For c_k = p^(-k)/sqrt(p^2-1), every square-summable sequence annihilating
all c_k k^m vanishes. Consequently these weighted monomials span a dense
subspace of the full wavelet coordinate space. The existing complete
physical wavelet basis and the Gram-Schmidt span identity transfer this
density to the physically defined valuationSpace p.

The new modules are Analysis/GeometricPolynomialDensity.lean,
Analysis/GeometricMonomialCoordinates.lean, and
RH/QPrimePowerPolynomialCompleteness.lean. The geometric atomic measure
has all required square-integrable exponentials; no analytic provider or
density assumption remains in the prime-specialized theorem.
valuationPolynomialHilbertBasis includes qOne at frame index zero and
valuationPolynomialMode p hp j at frame index j+1. It yields unconditional
reconstruction and complete signed Parseval for every physical valuation
observable. Final formal acceptance is certified by the containing server
checkpoint. The general exponential-weight theorem and explicit product
approximation rate in the note are ordinary mathematical proofs.

This resolves one-prime polynomial completeness. Finite/infinite tensor
completeness, higher closed formulas, and legal saturation are distinct.
For the actual floor-log target the entire decomposition remains
F_p = mu_p*1 + p/(p^2-1)*E_(p,0) + R_p, with R_p perpendicular to V_p.
The higher polynomial coefficients vanish and the cofactor residual has
strictly positive energy. Thus polynomial completeness does not improve
the already-optimal valuation-only target error.

RH/QPrimePowerLegalCancellation.lean records the exact remaining arithmetic
condition. With C=closureWithConstants and D=I-P_C, the known nonmembership
of E_(p,0) gives D(E_(p,0)) != 0, and
F_p in C iff D(R_p) = -p/(p^2-1)*D(E_(p,0)).
The complete legal defect energy retains the signed cross term.
If the target is legal, the cofactor defect is nonzero and its pairing with
the valuation defect is strictly negative. Separate membership of the two
components is ruled out by the existing first-mode nonmembership theorem.

Conditional research reduction: the existing two-target RH bridge applies
once the identities D(R_2)=-(2/3)*D(E_(2,0)) and
D(R_3)=-(3/8)*D(E_(3,0)) are proved. Both arithmetic cancellation providers
remain Open. No RH converse or unconditional RH conclusion is asserted.
