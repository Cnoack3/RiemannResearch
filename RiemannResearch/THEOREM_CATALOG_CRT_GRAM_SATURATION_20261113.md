# CRT decomposition of the actual full-Q inverse Gram matrices

Date: 2026-11-13. Source module:
[RiemannResearch/RH/QCRTGramSaturation.lean](RH/QCRTGramSaturation.lean).

## Scope and target

Let \(g_k(n)=(n\bmod k)/k\), with the repository's Q Hilbert realization,
and let \(V=\overline{\operatorname{span}}\{g_k:k\ge2\}\).
The finite family is **all** conductors \(2,\ldots,N+1\), not only primes
or squarefree conductors. Write
\[
G_N=(\langle g_{i+2},g_{j+2}\rangle_Q)_{i,j<N},\qquad
b_N=(\langle1,g_{i+2}\rangle_Q)_{i<N},\qquad
c_N=G_N^{-1}b_N,\quad s_N=b_N^\top c_N.
\]
The inverse is the complete Q Gram inverse already justified by
QCovarianceInvertibility and QFullResidueProjection. The new module does
not replace it with the inverse of a truncated CRT matrix.

Let \(v=\Pi_V1\), \(r=1-v\). The unconditional limits are
\[
s_N\longrightarrow\|v\|_Q^2=1-\|r\|_Q^2,\qquad
\|v\|_Q^2-s_N\longrightarrow0.
\]
The stronger statement \(s_N\to1\) is equivalent to \(1\in V\).
It is not proved unconditionally here. The density of the augmented family
\(\{g_k,Bg_k\}\) does not identify the closure of the unaugmented family
\(\{g_k\}\).

## CRT and Parseval matrix decomposition

Use the complete Q-orthonormal divisor-wavelet basis
\(\Psi_m=\mathrm{divisorWavelet}(m)/\sqrt{J_2(m)}\), \(m\ge1\), established
in QDivisorHilbertBasis. Put
\[
C_{m,i}=\langle g_{i+2},\Psi_m\rangle_Q
=\frac{\mathrm{qResidueDivisorCoefficient}(i+2,m)}{\sqrt{J_2(m)}}.
\]
For a positive conductor L, split the rows into \(m\mid L\) and \(m\nmid L\).
With \(C_{L,N}\) the retained rows,
\[
G_N=H_{L,N}+T_{L,N},\qquad
H_{L,N}=C_{L,N}^{\top}C_{L,N},\qquad
(T_{L,N})_{ij}=\sum_{m\nmid L}C_{m,i}C_{m,j}.
\]
The Lean statement headGram_parseval uses a tsum supported on the finite
set \(m\mid L\). It is exactly the finite retained-row matrix above.
The complementary matrix remains present. It is positive semidefinite
because its quadratic form is the squared norm of the omitted component.

Writing \(P_L\) for the orthogonal projection onto the divisor CRT cell
space and \(f_N=\sum_i(c_N)_ig_{i+2}\), define the entirely matrix-valued
retained error
\[
h_{L,N}=1-2s_N+c_N^\top H_{L,N}c_N.
\]
The verified identities are
\[
h_{L,N}=\|1-P_Lf_N\|_Q^2,\qquad
c_N^\top T_{L,N}c_N=\|(I-P_L)f_N\|_Q^2,
\]
\[
1-s_N=h_{L,N}+c_N^\top T_{L,N}c_N
=\sum_{m\ge1}\left|\mathbf1_{\{m=1\}}-\sum_i C_{m,i}(c_N)_i\right|^2.
\]
The Q wavelet basis and the full infinite energies are used throughout;
a Haar Fourier basis is not silently treated as Q-orthonormal.

## New moving-cutoff theorem

Suppose \(L_N>0\), \(i\le j\Rightarrow L_i\mid L_j\), and every positive
integer divides some \(L_N\). These are structural cofinality hypotheses,
not an approximation-rate or density hypothesis on the legal residues.
Then
\[
\boxed{c_N^\top T_{L_N,N}c_N\longrightarrow0},
\qquad
\boxed{h_{L_N,N}\longrightarrow\|r\|_Q^2}.
\]
The factorial tower is supplied explicitly. Cofinality here includes
arbitrary prime powers.

Proof: divisor-wavelet density gives strong convergence \(P_{L_N}\to I\).
The actual inverse-Gram candidates satisfy \(f_N\to v\), and
\[
\|(I-P_{L_N})f_N\|_Q
\le\|f_N-v\|_Q+\|(I-P_{L_N})v\|_Q\to0.
\]
The head limit then follows from the exact complete-error decomposition.
No convergence rate, coefficient summability, or interchange of an
uncontrolled infinite tail is assumed.

## Declaration map

All declarations below belong to
RiemannResearch.RH.QCRTGramSaturation.

| Declaration | Statement/status |
| --- | --- |
| saturation_eq_norm_sq; error_identity | Exact inverse-Gram projection energy identities. |
| saturation_tendsto | Unconditional scalar limit to \(\|\Pi_V1\|_Q^2\). |
| projection_energy_gap_tendsto_zero | Unconditional vanishing gap \(\|\Pi_V1\|_Q^2-s_N\). |
| saturation_tendsto_one_iff | \(s_N\to1\) iff \(1\in V\). |
| gram_parseval; error_parseval; limiting_defect_parseval | Complete, Jordan-weighted Parseval formulas. |
| gram_crt_split; headGram_parseval; tail_quadratic | Exact CRT decomposition and nonnegative complementary energy. |
| cell_closure_iSup_eq_top; conditionalProjection_tendsto | Exhaustion of the ambient Q space by a cofinal CRT tower. |
| moving_conditional_tail_tendsto | Moving-cutoff tail convergence for any norm-convergent sequence. |
| candidate_crt_tail_tendsto_zero; candidate_factorial_crt_tail_tendsto_zero | Actual inverse-Gram optimizer tails vanish. |
| candidate_tail_parseval | Omitted-mode energy as the complete complementary Parseval sum. |
| candidate_head_quadratic; candidate_tail_quadratic | Matrix/vector forms of retained and omitted candidate energies. |
| matrix_error_crt_split; headEnergy_eq_norm_sq | Exact complete error and retained error formulas. |
| matrix_tail_tendsto_zero | Literal inverse-Gram quadratic-form tail tends to zero. |
| matrix_head_tendsto | Retained error tends to \(\|1-\Pi_V1\|_Q^2\). |
| matrix_head_tendsto_zero_iff | Retained error tends to zero iff \(1\in V\). |
| riemannHypothesis_of_matrix_head_tendsto_zero | Conditional RH consequence via the existing Q-to-Pareto transfer. |

## Remaining obligation and RH status

For any fixed structural tower as above, prove
\[
1-2b_N^\top G_N^{-1}b_N+
(G_N^{-1}b_N)^\top H_{L_N,N}(G_N^{-1}b_N)\longrightarrow0.
\]
This is an equivalent reformulation of \(s_N\to1\), not an estimate
established by CRT. The new tail theorem removes the omitted-mode tail
as an independent obligation for these actual minimizers. The retained
error can still contain the entire limiting residual.

The conditional consumer explicitly assumes this retained-error zero
limit and deduces RiemannHypothesis using
QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure,
owned by QOptimizerParityRH. No unconditional RH conclusion or
RH converse is asserted.

## Verification

The coherent proof candidate, including every theorem and the four guarded
axiom checks, passed Bazel with BuildBuddy:
job `job_GEp_f5Uwg7nJPX1V41XyT4Zsx3CsKYz-`, exit code 0, verified true,
84.442 seconds of verification.
[BuildBuddy invocation](https://app.buildbuddy.io/invocation/5ddcad31-96d6-49f3-9978-e44286ed97d1).

The persisted module adds its provenance header, direct owner imports,
and this focused catalog. Aggregate publication validation is separate
from the targeted proof check; the checkpoint result is the authority for
the eventual commit and push.

The source includes guarded axiom checks for the matrix decomposition,
the saturation equivalence, the moving-tail theorem, and the conditional
RH consumer. Each permits exactly the standard Lean axioms
propext, Classical.choice, and Quot.sound. The publication checkpoint
also audits source and validates the aggregate project with Bazel and
BuildBuddy before committing or pushing.
