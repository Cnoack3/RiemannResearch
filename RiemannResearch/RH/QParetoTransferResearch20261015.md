# Pareto results transferred to Q — 15 October 2026

## Mathematical setting

For physical coordinates \(n\ge1\), use
\[
 P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{\zeta(2)n^2},\qquad
 g_d(n)=\frac{n\bmod d}{d}.
\]
The formal Hilbert encodings both use real \(\ell^2\), with different
square-root probability weights. Equal raw \(\ell^2\) coordinates do not
represent equal physical sequences in the two measures.

The new sequence-preserving continuous linear equivalence is
QParetoEquivalence.paretoEquiv. Its forward map is the existing toPareto;
its checked inverse is toQ. It preserves every physical coordinate, the
constant target, and every positive-conductor residue atom.

This development contains 87 theorem declarations and 11 definitions in
eight Lean modules. General transfer statements cover arbitrary vector
families and conductor dictionaries, so they apply to the relevant Pareto
results without duplicating their proofs as renamed wrappers. Numerical
measure-dependent formulas use the actual Q metric.

Source: the user's Pareto-to-Q transfer request and the existing project
declarations. The mathematical methods are standard norm equivalence,
polarization, inverse-Gram duality, and Hilbert-space weak closure; no
novelty claim is made.

## Transfer coverage

| Pareto result family | Q treatment | Formal provider |
| --- | --- | --- |
| Physical identities, finite sums, CRT carries, coefficient recurrences | Encode the identical complete physical sequence; coefficients stay unchanged | QParetoEquivalence.toQ_sequence; existing toPareto_sequence |
| Full, squarefree, and restricted-conductor closure | Exact closure equivalence for every indexed family of positive conductors | QParetoEquivalence.legal_closure_iff |
| Strong convergence under arbitrary filters | Exact equivalence of convergence in the two realizations | QParetoEquivalence.tendsto_toPareto_iff |
| Uniform full-norm boundedness | Exact boundedness equivalence with comparison constants | QParetoEquivalence.uniformly_bounded_iff |
| Bounded coordinate limits and exact growing heads | Membership in the norm-closed Q subspace | QBoundedCoordinateClosure.mem_closure_of_bounded_coordinate_limits; mem_closure_of_bounded_matching_heads |
| Signed inner products and Gram entries | Retain the complete signed reciprocal correction | QParetoMetric.inner_identity; QParetoGramComparison.gramMatrix_entry_identity |
| Finite Gram quadratic energies | Exact correction identity and two-sided comparison for arbitrary finite families | QParetoGramComparison.gram_energy_identity; gram_energy_bounds |
| Inverse-Gram source and capacity forms | Two-sided comparison of genuine matrix inverses for the same source vector | QParetoGramComparison.capacity_bounds; inverse_matrix_quadratic_bounds |
| Finite least-squares errors | Compare the two actual optimizers while retaining their distinct coefficients | QParetoGramComparison.optimizer_error_bounds |
| Gram normal equations, Schur and centered-covariance identities | The general Hilbert theorems instantiate on Q; existing Q modules construct the actual inverse and covariance matrices | QCovarianceInverse; QCovarianceInvertibility; QCovarianceMatrixInverse |
| Continuous Mellin tests and zeta signatures | The same physical step integral, with the exact metric-corrected continuity estimate | QMellinTransfer.qMellin_eq_step_integral; qMellin_residue_zeta |
| Off-line-zero obstructions | Lower Q error bound retaining the entire positive correction | QMellinTransfer.legal_error_lower_with_correction |
| Bounded linear operator algebra and real eigenvectors | Similarity by the physical-sequence equivalence | QParetoOperatorTransfer.transport_mul; transport_pow; eigenvector_iff |
| Continuous separating functionals and annihilators | Compose with the continuous equivalence | QParetoOperatorTransfer.functional_annihilates_iff |
| Canonical Möbius normalized energies and covariance | Sharper head-dependent constants and an unconditional absolute metric-discrepancy limit | QCanonicalMetricAsymptotics |
| Prime-divisibility independence and full divisor Parseval | Reuse the exact Q arithmetic structure and connect its complete coefficient-energy budget to the bounded-head RH criterion | QDivisorHilbertBasis; QBoundedCoordinateClosure.riemannHypothesis_of_bounded_divisor_energy |

The Pareto mean \((\log d)/d\), Pareto periodic weights, numerical Gram
entries, and native self-adjoint spectral data depend on the measure.
For Q, the actual residue means and complete periodic Gram entries are
given by QResidueMoments, with Q-divisibility information from
QDilationMoments and QDivisorHilbertBasis. Similarity preserves the proved
operator identities and real eigenvector relations; self-adjointness in
the Q inner product needs its own verification.

## Exact metric identity and its improvement

The exact weight identity is
\[
 \zeta(2)Q(n)=P(n)+\frac{P(n)}n.
\]
For a Q vector with physical sequence \(f(n)\), define
\[
 R(f)=\sum_{n\ge1}\frac{|f(n)|^2}{n^2(n+1)}.
\]
In Lean, metricCorrection is the reciprocal diagonal quadratic form of
the Pareto encoding; metricCorrection_eq_physical proves this literal
complete series formula.

The principal equality is
\[
 \boxed{\zeta(2)\|f\|_Q^2=\|f\|_P^2+R(f)}.
\]
Here and throughout, the P norm means the same physical sequence encoded
under P. The correction is nonnegative and is zero exactly for the zero
vector. The polarized theorem also retains every signed mixed term.

If \(f(n)=0\) for \(1\le n\le H\), then
\[
 0\le R(f)\le\frac{\|f\|_P^2}{H+1},\qquad
 \boxed{\|f\|_P^2\le\zeta(2)\|f\|_Q^2
 \le\left(1+\frac1{H+1}\right)\|f\|_P^2}.
\]
This replaces the earlier global factor 2 by a factor tending to 1.
For a bounded physical test \(|f(n)|\le A\), the complete Q tail satisfies
\[
 \sum_{n>H}Q(n)|f(n)|^2
 \le \frac{1+1/(H+1)}{\zeta(2)}\,\frac{A^2}{H+1}.
\]

## Gram, inverse-Gram, and optimal error consequences

For the same finite physical family, write \(G_P,G_Q\) for its two actual
Gram matrices. With all mixed terms retained, the exact matrix identity is
\[
 \zeta(2)G_Q=G_P+R_G,\qquad
 (R_G)_{ij}=\langle v_i,Dv_j\rangle_P,
\]
where \(D\) multiplies physical coordinate \(n\) by \(1/n\).
Consequently
\[
 G_P\preceq\zeta(2)G_Q\preceq2G_P.
\]
For every source vector \(b\) and linearly independent finite family,
\[
 \boxed{\frac{\zeta(2)}2\,b^{\mathsf T}G_P^{-1}b
 \le b^{\mathsf T}G_Q^{-1}b
 \le\zeta(2)\,b^{\mathsf T}G_P^{-1}b}.
\]
The inverses are constructed from actual Hilbert independence.
This comparison uses the same \(b\). The metric-specific target pairings
\(b_P\) and \(b_Q\) generally differ.

For any target and the same finite physical span, the actual minimum
squared errors satisfy
\[
 \boxed{D_P\le\zeta(2)D_Q\le2D_P}.
\]
The proof minimizes separately in each metric; it does not assume that
their orthogonal projections commute with the equivalence.

## Continuous Mellin and the retained zero obstruction

The physical step Mellin functional is
\[
 M_Q(f,s)=\int_1^\infty f(\lfloor x\rfloor)x^{-s-1}\,dx.
\]
For \(\operatorname{Re}s>1/2\),
\[
 |M_Q(f,s)|^2
 \le\frac{\zeta(2)\|f\|_Q^2-R(f)}{2\operatorname{Re}s-1}.
\]
For \(d>0,\ \operatorname{Re}s>0,\ s\ne1\),
\[
 M_Q(g_d,s)=\frac{\zeta(s)}s\left(\frac1d-d^{-s}\right).
\]
Thus if \(\zeta(s)=0\), \(\operatorname{Re}s>1/2\), and \(F\) is any
finite legal residue sum, the complete inequality is
\[
 \boxed{\frac{2\operatorname{Re}s-1}{|s|^2}
       +R(1-F)\le\zeta(2)\|1-F\|_Q^2}.
\]
Discarding only the explicitly identified nonnegative correction gives
the weaker normalized Q obstruction
\[
 \|1-F\|_Q^2\ge
 \frac{2\operatorname{Re}s-1}{\zeta(2)|s|^2}.
\]

## Unconditional canonical improvement

Let \(r_N\) be the actual canonical Möbius residual. Its two encodings have
the identical physical sequence and vanish through \(N\). The existing
checked stretched-PNT estimate supplies
\[
 \delta_N=\frac{\|r_N\|_P^2}{N+1}\longrightarrow0.
\]
The new exact equality and estimate are
\[
 \zeta(2)\|r_N\|_Q^2=\|r_N\|_P^2+R(r_N),
 \qquad 0\le R(r_N)\le\delta_N.
\]
Therefore, unconditionally,
\[
 \boxed{\zeta(2)\|r_N\|_Q^2-\|r_N\|_P^2\longrightarrow0}.
\]
No uniform bound on either unnormalized residual energy is used.
The existing logarithmic provider gives
\[
 R(r_N)\le \frac{D}{(6+\log N)^2}
\]
eventually, for an existential nonnegative \(D\) and existential onset.

For a fixed positive canonical index \(K\), the covariance estimate improves to
\[
 |\langle r_K,r_N\rangle_Q|^2\le
 \left(\frac{1+1/(N+1)}{\zeta(2)}\right)^2
 (1+2K)^2\,\delta_N.
\]
The previous transferred constant was \((2/\zeta(2))^2\).

## RH status and exact open obligation

The generic Q bounded-coordinate closure theorem is unconditional.
Its application to legal candidates gives a conditional research reduction:
\[
 F_H\in\operatorname{span}\{g_d:d\ge2\},\quad
 F_H(n)=1\ (1\le n\le H),\quad
 \sup_H\|F_H\|_Q^2<\infty
 \quad\Longrightarrow\quad \mathrm{RH}.
\]
The arbitrary-subspace theorem also applies to squarefree dictionaries.

Using the complete actual Q divisor-wavelet basis, with squared norms
\(J_2(r)\), the exact identity is
\[
 \|F_H\|_Q^2=
 \sum_{r\ge1}\frac{|\langle F_H,w_r\rangle_Q|^2}{J_2(r)}.
\]
Hence a uniform bound on this entire arithmetic coefficient sum is an
equivalent concrete budget for the displayed legal family.

**Open:** construct a legal growing-head family and prove this uniform
complete-energy budget, or discharge one of the existing arithmetic
cancellation providers. The new correction estimates, coordinate matching,
DPP occupation laws, and coefficient stabilization do not discharge it.
The equality of scaled canonical energies up to a vanishing discrepancy
does not assert that either canonical error tends to zero.

## Verification and publication scope

All eight modules were imported together and checked on the user's Lean
server in job job_QVP0iZV0nJKjHjvfMcNnzdAbN75B_Cqb (25.048 seconds).
Eleven representative declarations, including the unconditional canonical
limit, inverse-matrix comparison, Mellin obstruction, bounded-divisor-energy
RH reduction, and operator eigenvector transfer, were inspected with
#print axioms. Each reported only propext, Classical.choice, and Quot.sound.
The RH reduction retains its explicit uniform-energy hypothesis in its type.

After that successful check, the two new-module linter warnings were removed.
The exact final Lean source and aggregate export then passed the full server
command lake build RiemannResearch --quiet in job
job_QMMGE0au3DuXumApl0Bey9csZjn3_gg2 (86.62 seconds, terminal succeeded).
This validates the whole aggregate project, including the new exported modules.
GitHub-hosted CI was not used.

Publication was explicitly authorized by the user on 15 October 2026.
The final checkpoint audits and validates the exact unpublished delta
before committing and pushing to main. Its terminal job record supplies
the publication result and commit; no GitHub-hosted CI is required.

## Module inventory

- Analysis/FiniteGramMetricComparison.lean — inverse-Gram variational comparison.
- RH/QParetoEquivalence.lean — physical-sequence continuous equivalence and closure transfer.
- RH/QParetoMetric.lean — exact signed metric correction and sharp growing-head/tail comparisons.
- RH/QParetoGramComparison.lean — actual Gram matrices, inverse capacities, and optimal error bounds.
- RH/QParetoOperatorTransfer.lean — bounded operator algebra, real eigenvectors, and continuous tests.
- RH/QMellinTransfer.lean — actual physical Mellin integral, zeta signatures, and zero obstructions.
- RH/QBoundedCoordinateClosure.lean — bounded-family closure and the complete Q Parseval RH consumer.
- RH/QCanonicalMetricAsymptotics.lean — unconditional canonical discrepancy and sharper covariance.
