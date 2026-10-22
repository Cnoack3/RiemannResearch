# Dyadic verification advance: exact Gram structure and the repair obstruction

September 10, 2026. Starting published commit:
`496dbcc6a62e3d128dfa3156288466add67eacca`.

Source: the user-supplied DyadicRegularizedVerificationContinuation20260910 (1).md.
The goal remains RH. The results below do not establish unconditional (N2), the
Mellin limits, or full legal approximation.

## Exact off-diagonal refinement and adjacent energies

Write \(V_m=QT_m1\) and \(B_l=Qd_l\). The new module
`RH/DyadicStepGram.lean` proves
\[
\langle V_{2l+1},V_m\rangle
=\tfrac12(\langle V_l,V_m\rangle+\langle V_{l+1},V_m\rangle),
\qquad 0<m\le2l,
\]
and pairwise orthogonality of the actual projected boundaries:
\[
\langle B_l,B_k\rangle=0\quad(l\ne k),\qquad \|B_l\|^2=\tfrac14.
\]

For \(E_m=\|V_m-V_{m+1}\|^2\), the exact signed vector differences give
\[
E_{2l}=E_{2l+1}=\tfrac14+\tfrac14E_l.
\]
Consequently
\[
2^N\le m<2^{N+1}
\quad\Longrightarrow\quad
E_m=\frac{1-4^{-N}}3.
\]
No arithmetic estimate is assumed. This evaluates the negative adjacent
difference term retained in the preceding diagonal recurrence.

For every finite collection of distinct positive boundary indices and
arbitrary real signed coefficients, the complete energy is
\[
\left\|t1+\sum_i a_iB_{m_i}\right\|^2
=t^2+\tfrac14\sum_i a_i^2,
\]
and the complete mixed pairing is \(\tfrac14\sum_i a_i b_i\).
The cross terms vanish by proved physical orthogonality, not by omission.

Endpoints:
- `dyadicProjectedStep_odd_inner_step`
- `dyadicProjectedStep_adjacent_norm_sq_on_annulus`
- `dyadicProjectedBoundary_finite_inner`
- `dyadicProjectedBoundary_finite_mean_energy`

## The boundaries detect the entire completed quotient

`RH/DyadicBoundaryCompleteness.lean` proves
\[
\overline{\operatorname{span}\{1,B_1,B_2,\ldots\}}=QH.
\]
In particular, \(\langle1,f\rangle=0\) and
\(\langle B_l,f\rangle=0\) for every positive \(l\) imply \(Qf=0\).
Equal mean and boundary pairings imply equal quotient vectors.

This establishes completeness of these actual weighted boundary coordinates.
A named infinite Parseval-series formula, its identification with the original
fold/martingale expression (N5), and the required arithmetic estimates are
not supplied by this pass.

Endpoints:
- `dyadicQuotientProjection_eq_zero_of_boundary_inner`
- `dyadicQuotientProjection_eq_of_boundary_inner`
- `dyadicBoundarySpan_closure_eq_quotient`

## Centered repair carries the full residue approximation obstruction

Set \(A=T_2-I\), and let \(C\) be the norm closure of the finite signed span of
the actual centered repairs \(G_m=AR_m\), using every positive integer \(m\).
Let \(L_+\) be the existing actual legal closure with every positive residue
seed allowed.

`RH/DyadicCenteredRepairRigidity.lean` proves
\[
(\sqrt2-1)\|f\|\le\|Af\|,\qquad \|f\|\le3\|Af\|,
\]
and the exact characterization
\[
Af\in C\quad\Longleftrightarrow\quad f\in L_+.
\]
Every finite centered correction has an actual finite positive-residue legal
preimage. Continuity proves the forward image inclusion; the inverse norm
bound transports approximations back to the original physical Hilbert norm.

The single-target consequence is
\[
(T_2-I)1\in C\quad\Longrightarrow\quad\mathrm{RH}.
\]
Since \(Q(T_2-I)1=0\), exhaustion of all of \(\ker Q\) by centered repairs
would imply RH. This is a proved implication, not a supplied repair witness.
It does not establish the converse RH implies centered repair, nor refute the
possibility of the specifically coupled corrections required along legal lifts.

Endpoints:
- `dyadicRepairDifference_mem_centeredClosure_iff`
- `riemannHypothesis_of_difference_one_mem_centeredClosure`
- `riemannHypothesis_of_centeredClosure_exhausts_kernel`

## An elementary spacing ingredient for the remaining prefix estimate

`Analysis/RotationMinimumSpacing.lean` addresses the next arithmetic
provider. For real \(\alpha\), positive integers \(h<q\), and integers \(p_h,p_q\),
if
\[
0<|q\alpha-p_q|\le|h\alpha-p_h|,
\]
then
\[
|h\alpha-p_h|>\frac1{2q}.
\]
This follows from a nonzero integer determinant. Nearest-integer choices and
continued fractions are not assumptions of this lemma.

Endpoint: `integer_approximation_minimum_spacing`.

## Next concrete formalization target

The accompanying ordinary argument
`Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`
derives an exact dyadic tent expansion, a logarithmic Gram majorant, and an
elementary block-packing prefix estimate. It has received an independent
mathematical review, but the complete argument has not been verified in Lean.

For \(\alpha=\log3/\log2\), \(\delta_h=\operatorname{dist}(h\alpha,\mathbb Z)\),
the candidate is
\[
a_0=0,\qquad
a_h=\frac54+
\frac{\log(1/\log2)+\log(1/\delta_h)}{4\log2}\quad(h\ge1).
\]
The proposed constant is
\[
A_0=\frac54+
\frac{\log(1/\log2)+2(1+\log24)}{4\log2},
\qquad
\sum_{h=1}^N a_h\le A_0N.
\]

The next steps are to formalize the exact tent representation, specialize
minimum-denominator spacing to nearest-integer errors, prove the finite
logarithmic block sum and exponential separation of \(3^q\) and \(2^p\), and
connect these to the actual Gram/prefix hypotheses in the existing assembly.
This would bound the actual damped step average uniformly.

The product-index Möbius-series convergence, its arithmetic identification,
the normalization remainder, the Mellin/separating limits, and full legal
two-seed approximation remain separate obligations. The existing norm-assembly
theorem is unchanged and still conditional on its explicit remaining inputs.

## Verification discipline

All verification submissions were serialized. The repaired source candidates
contain no placeholder proofs, project-local axioms, or unsafe declarations.
Kernel checks concern the exact theorem types; in particular the closure
hypothesis of the RH implication remains an ordinary theorem parameter.


The combined source and theorem-type/axiom audit passed in job `job_JmttxrBmzAsPdqXpcp34vDzSyBFwEq4-`: `verified: true`, exit code 0, 5.31 seconds. Source SHA-256: `9b2610554f13be12811ffab80a38c7e9fb92ca72476d7c02b596d68285f379b7`. All eight audited endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`. No warning or error diagnostics were emitted. The repository checkpoint separately validates the separated modules before publication.
