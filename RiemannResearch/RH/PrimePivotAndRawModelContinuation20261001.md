# Prime pivots and the next moving-remainder target

Date: October 1, 2026. Base: f5985012b4576f09b61d77f816fc8fbbd7c6a3ef, including the independent b306d93 audit.

The latest GitHub recommendation was executed by checking the complete signed arithmetic model, testing exact finite-support duals with Wolfram, reviewing primary sources, and formalizing the supported results. A separate Deep Research runner was not exposed in this session; the literature work used the available web search and primary papers. The result strengthens the unconditional prime-pivot control, rules out a proposed raw divergent model, and weakens the sufficient analytic transfer condition. RH remains open.

## 1. An unconditional bound for the actual prime pivot

Use physical coordinates k>=1 with norm squared sum f(k)^2/[k(k+1)]. Write t_d for the normalized residue row with its first physical site removed, h_p for its innovation after screening against EVERY conductor 2<=d<p, sigma_p=||h_p||^2, and C_<p for the corresponding old reciprocal-source capacity. In Lean p=n+3 and sigma_p=schurSigma(n+1).

Define the two-site certificate
\[
 Z_p(k)=p(p+1)\mathbf1_{k=p}-p(p-1)\mathbf1_{k=p-1}.
\]
The exact identities are
\[
 \langle t_d,Z_p\rangle=\frac1d-\mathbf1_{d\mid p},
 \qquad \|Z_p\|^2=2p^2.
\]
For prime p, Z_p satisfies ALL old reciprocal-source observations, including composite conductors. If z_<p is the old minimum, then
\[
 2p^2=C_{<p}+\|Z_p-z_{<p}\|^2,
 \qquad \langle h_p,Z_p\rangle=\eta_p-1.
\]
Consequently
\[
 (\eta_p-1)^2\le \sigma_p(2p^2-C_{<p}),
 \qquad
 \frac1{\sigma_p}\le4p^2+2C_{\le p}-4C_{<p}.
\]
The last bound uses the exact step C_<=p=C_<p+eta_p^2/sigma_p and preserves the signed old-capacity credit. No bounded-capacity or negated-RH premise is used.

For a future odd prime r>=p+2, set D_(p,r)=Z_r-Z_p. The supports are disjoint. It has zero observation against every old t_d and observation one against t_p, so
\[
 \langle h_p,D_{p,r}\rangle=1,\qquad
 2p^2+2r^2=\frac1{\sigma_p}
  +\left\|D_{p,r}-\frac{h_p}{\sigma_p}\right\|^2.
\]
This is an equality for the actual full-screened innovation, not a diagonal approximation. Bertrand supplies p<r<=2p; both primes are odd, so r>=p+2. Thus
\[
 \boxed{\frac1{\sigma_p}\le10p^2,\qquad
 \sigma_p\ge\frac1{10p^2}}\quad(p\ge3\text{ prime}).
\]
Formal declarations: primeTwoSiteCertificate_capacity_completion, primeTwoSiteCertificate_pivot_bound, prime_schur_inverse_le_capacity, primeFourSiteDual_inverse_completion, prime_schur_inverse_le_two_primes, prime_schur_inverse_le_ten_sq, prime_schurSigma_ge_tenth in ParetoPrimePivotCertificates.lean. These are unconditional arithmetic bounds and exact completions; they supersede the earlier conditional raw-charge pivot estimate.

## 2. The raw charge plus a fixed vector cannot supply divergence

Let q_p=Q/p^2 for any fixed real Q, B_p=<h_p,z> for any fixed Hilbert vector z, and use the actual weight 1/sigma_p at primes (zero at nonprimes). The exact mixed expansion is
\[
 \frac{(q_p+B_p)^2}{\sigma_p}
 =\frac{q_p^2}{\sigma_p}
  +\frac{2q_pB_p}{\sigma_p}
  +\frac{B_p^2}{\sigma_p}.
\]
The pivot bound gives q_p^2/sigma_p<=10Q^2/p^2. The p-series and fixed-vector Bessel estimate therefore prove, unconditionally, that both the raw-charge energy and the full mixed-row energy are summable.

For the existing source-balanced test f on a block, let E be its actual prime Schur energy and let
\[
 m_j=\frac{\sum_{p\ {\rm in\ block}\ j}
       f^{\rm bal}_{j,p}(q_p+B_p)/\sigma_p}{\sqrt{E_j}}.
\]
Every choice of the existing dyadic block tests gives sum_j m_j^2<infinity. This includes the zero-energy case. The source term a_p=factorialPrimeDelta cancels by the exact source-balance identity; replacing q_p+B_p by q_p+B_p-a_p leaves the pairing unchanged. Thus a raw slope -1+(q_p+B_p)/a_p does not restore divergence where that slope is defined.

The genuine coprime-two raw defect is q_p with Q=1+||infiniteCoprimeCertificate 2||^2/2. The formal theorem coprimePrimeRawCharge_eq connects it to the generic family. No raw/screened identification is asserted: the complete actual moving amplitude c_j retains its moving inverse-Gram correction.

In fact the new checked statement is
\[
 \sum_j(c_j-m_j)^2<\infty
 \quad\Longleftrightarrow\quad
 \sum_jc_j^2<\infty.
\]
Hence this raw family is excluded as a square-nonsummable arithmetic model. It does not show that the actual moving amplitudes are summable unconditionally.

Formal declarations in ParetoPrimeRawChargeModels.lean: primeRawCharge_energy_summable, primeRawModelRow_energy_split, primeRawModelRow_energy_summable, primeRawModelPairing_source_shift, primeRawModelCertificate_dyadic_summable, primeRawModelAmplitude_square_summable, primeMovingCRT_rawModel_error_summable_iff.

## 3. A weaker sufficient transfer target: positive norm saving

For nonnegative weights define the prefix ENERGIES
\[
 M_N=\sum_{j<N}w_jm_j^2,\quad
 A_N=\sum_{j<N}w_jc_j^2,\quad
 T_N=\sum_{j<N}w_j(c_j-m_j)^2,\quad
 X_N=\sum_{j<N}w_jm_jc_j.
\]
Retain the exact signed identity T_N=A_N-2X_N+M_N first. If M_N tends to infinity and, for one delta>0, arbitrarily large N satisfy
\[
 \sqrt{M_N}-\sqrt{T_N}\ge\delta,
\]
then sum_j w_jc_j^2 diverges. This permits T_N/M_N to tend to one and requires neither a uniformly strict relative energy saving nor a summable complete error.

Proof: if A_infinity were finite, the existing head/tail theorem gives X_N^2/M_N ->0. At every sufficiently large cutoff with positive norm saving,
\[
 \delta\sqrt{M_N}
 \le\delta(\sqrt{M_N}+\sqrt{T_N})
 \le M_N-T_N=2X_N-A_N\le2X_N,
\]
contradicting X_N^2/M_N ->0. This argument is formalized as WeightedScalarEnergy.actual_square_not_summable_of_cofinal_norm_defect. With unit weights and the COMPLETE primeMovingCRTAmplitude, riemannHypothesis_of_moving_norm_defect is a conditional RH reduction.

The related limit statement
\[
 \sqrt{M_N}-\sqrt{T_N}\longrightarrow0
\]
for a square-summable actual sequence and any fixed divergent model is an ordinary deduction, not a separately formalized limit theorem here: use (2X_N-A_N)/(sqrt(M_N)+sqrt(T_N)) and head/tail decay.

Keep norms distinct from energies. Unbounded M_N-T_N alone is insufficient. For m_j=1 and c_j=1/(j+1), M_N=N, A_N=H_(N,2), X_N=H_N, and M_N-T_N=2H_N-H_(N,2) tends to infinity, while the norm difference tends to zero and the actual square sum is finite.

## 4. Primary-source research and the remaining obligation

These references support comparisons of statements and hypotheses, not a claim that their proofs have been formalized here.

- [Ehm, On certain Gram matrices and their associated series, arXiv:2405.06349v2](https://arxiv.org/html/2405.06349v2), section 8.1: the decomposition explicitly leaves its inversion-error estimate open. Its Gram identities do not control our cutoff-dependent screened correction.
- [Pyvovarov, A few remarks on the Baez-Duarte Criterion, arXiv:2607.12084v3](https://arxiv.org/html/2607.12084v3), sections 9.5-9.6: this recent preprint uses the same interval weight 1/[k(k+1)] for exponentially damped residue approximants. It retains a complete cotangent remainder and leaves a combined global bilinear cancellation estimate open. Fixed-residue bounds are not uniform in the cutoff; related power savings with different weights require a further transfer argument. This is a useful comparison for keeping every boundary, defect and tail term, not a supplied provider for our theorem.
- [Maier and Rassias, Explicit estimates of sums related to the Nyman-Beurling criterion, arXiv:1806.05070](https://arxiv.org/abs/1806.05070): cotangent/Mobius estimates concern different regions and weights. The canonical record dates the submission to June 2018, despite misleading fresh search-index dates. A precise transfer to the moving inverse-Gram coefficients is still required.
- [Mikhailets and Murach, General forms of the Menshov-Rademacher, Orlicz, and Tandori theorems on orthogonal series, arXiv:1110.4253](https://arxiv.org/abs/1110.4253): Hilbert-valued orthogonal-series convergence is conditional on the applicable weighted coefficient bound and orthogonality. It does not establish those inputs for our arithmetic remainder.
- [Guth and Maynard, New large value estimates for Dirichlet polynomials, arXiv:2405.20552](https://arxiv.org/abs/2405.20552): the coefficient normalization and sampling assumptions must be transferred to the actual inverse-Gram coefficients before the estimates can be used. No such transfer was established here.
- [Suzuki, Weil's quadratic form via the screw function, arXiv:2606.09096v3](https://arxiv.org/html/2606.09096v3), Corollary 1.6 and its following discussion: the RH conclusion requires a locally uniform analytic limit. Finite-window self-adjoint operators alone do not provide it.
- [Mathlib Bertrand documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html): the formal prime-existence theorem is the exact external arithmetic input in section 1. No prime number theorem or RH assumption is imported for that bound.

**Open:** find an explicitly defined arithmetic model outside the summable raw family, prove its divergence with the actual normalization, and prove a positive cofinal saving in prefix NORMS for the complete signed discrepancy. Alternatively, discharge all four hypotheses of the earlier moving-Hilbert representation theorem. A model chosen by setting m=c would make the error vanish but simply rename the unproved actual divergence; it supplies no independent arithmetic estimate.

The most concrete next experiment is to compute the exact centered inverse-Gram correction in the same dyadic blocks as the actual amplitude and model, keeping all older composite conductors and full physical tails. A candidate must have a genuine divergent mechanism; the isolated Q/p^2 charge plus a fixed vector has now been ruled out. Any analytic-number-theory estimate must identify the exact coefficients, endpoints, scale uniformity, source balance and total remainder before a bound is substituted.

## 5. Verification and reproducible diagnostics

A coherent candidate containing all three new module bodies and the new concrete RH consumer passed Lean, exit code 0, in 9.692 seconds. Receipt: job_mR1wYJLDD9ecAVn1NLBwJPm_rfIGnrwC. Code SHA-256: 74ae9c7e1f824f6e1bad1cd616a917cd3d9c956bb5195af5c99d9c11bc4afc39. The five critical axiom audits report only propext, Classical.choice and Quot.sound. The conditional theorem's local model-divergence and norm-saving hypotheses remain open; they are not discharged by an axiom audit.

Environment: Lean v4.33.0-rc2; mathlib 51e6992efd06126df61a496bebf8f49482a4e129. Final publication uses the checkpoint source audit and affected-module validation. No sorry, admit, new project axiom or unsafe declaration is persisted. The construction is independently developed; no claim of literature novelty is made.

See [PrimePivotAndRawModelDiagnostics20261001.md](PrimePivotAndRawModelDiagnostics20261001.md) for the successful Wolfram computations and a self-contained reproduction script. Numerical inversions illustrate finite scales and are not used as proofs of any infinite estimate.
