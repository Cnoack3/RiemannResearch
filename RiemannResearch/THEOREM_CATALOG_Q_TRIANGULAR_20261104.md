# Exact triangular residue normalization — 4 November 2026

Source: the user's request for explicit triangular Gram–Schmidt coefficients,
their inverse, eigenvalues, eigenvectors, and Lean verification.

## Objects and indexing

Let v_j = g_(d_j), with distinct conductors d_j > 1, and use the actual
inverse-square Q inner product. Indices in the Lean modules start at zero.
Let G_n be the Gram matrix of v_0,...,v_(n-1), Δ_n = det G_n,
and e_j = gramSchmidtNormed ℝ v j. Write (e_0,...,e_(n-1)) =
(v_0,...,v_(n-1)) A_n, with columns giving coefficients.

## Exact results

For any independent real inner-product-space family, the following hold:

- Δ_n > 0, including Δ_0 = 1 by the empty determinant convention.
- Each e_j is a finite combination of v_0,...,v_j.
- Its coefficient at i ≤ j is
  adj(G_(j+1))_(i,j) / sqrt(Δ_j Δ_(j+1)); later coefficients are zero.
- If s_j is the norm of the unnormalized innovation, then
  s_j² Δ_j = Δ_(j+1) and A_jj = 1/s_j = sqrt(Δ_j/Δ_(j+1)).
- A_nᵀ G_n A_n = I.
- A_n⁻¹ = R_n = A_nᵀ G_n, where R_ij = inner(e_i,v_j).
- G_n = R_nᵀ R_n, and both A_n and R_n are upper triangular.
- The finite eigenvalues of A_n are exactly the displayed diagonal values.
- Inversion preserves eigenvectors and reciprocates nonzero eigenvalues.
- Backward substitution gives an explicit eigenvector when the selected
  diagonal differs from earlier diagonal entries. A separate row-equation
  characterization covers repeated diagonal values without a diagonalizability
  assumption.
- Zero-padding a finite-section eigenvector gives an eigenvector of the
  formal infinite matrix action on finitely supported sequences.

For residues, independence is proved for every injective conductor family
with d_j > 1. The existing complete-tail norm estimate implies

    sqrt(zetaTwo * d_j / 2) ≤ A_jj,

and the diagonal tends to infinity. Consequently no bounded linear operator
on standard coefficient l2 can have these matrix columns. A distinct theorem
also rules out a bounded physical Q-space map sending all escaping atoms to
their normalized innovations. These are different operator statements.

For d_0 = 2, the first coefficient and vector are exactly

    A_00 = 4 / sqrt(3),       e_0 = (4 / sqrt(3)) • g_2.

## Numerical certificates

For the first four conductors 2,3,5,6, rational interval certificates cover
the complete Q Gram entries. Their widths are at most 2·10^(-12).
The enclosure proof uses an exact sixteen-term reciprocal-square head and
telescoping rational tail bounds. The tail width at x is exactly 1/(30 x^9).

The matrix-level certificates propagate those intervals through determinants,
cofactors, square roots, the inverse identity, and backward substitution.
The three displayed tables (A, R, and the coefficient-matrix eigenvectors)
are compared to the original decimal strings with absolute tolerance 10^(-6).
This tolerance does not certify all digits of the original floating-point
display. Eigenvectors are scaled to make their last nonzero coordinate one;
they are not asserted to have Euclidean norm one.

## Modules and main declarations

- `Analysis/GramSchmidtCofactors.lean`: `coefficient_synthesis`,
  `coefficient_unique`, `scale_sq_mul_det`, `scale_eq_sqrt_det_ratio`,
  `coefficient_diagonal_eq_sqrt_det_ratio`,
  `coefficient_eq_normalized_adjugate`, `coefficient_eq_cofactor`.
- `Analysis/OrthonormalGramChange.lean`: `column_synthesis`,
  `cross_mul_coefficients`, `coefficients_mul_cross`, `coefficients_inverse`,
  `cross_inverse`, `transpose_coefficients_mul_gram`,
  `orthonormal_gram_identity`, `gram_eq_transpose_cross_mul_cross`,
  `coefficients_eq_inverse_gram_mul_transpose_cross`.
- `Analysis/GramSchmidtTriangular.lean`: `entry`, `forward`, `reverse`,
  `column_synthesis`, `forward_upper`, `reverse_upper`, `forward_inverse`,
  `reverse_inverse`, `inverse_eq_transpose_mul_gram`, `orthonormal_identity`,
  `gram_factorization`, `diagonal_reciprocal`, `diagonal_det_ratio`,
  `entry_cofactor`, `eigenvalue_iff_det_ratio`.
- `LinearAlgebra/TriangularEigenvectors.lean`: `hasEigenvalue_iff_diagonal`,
  `inverse_hasEigenvector_iff`, `inverse_hasEigenvalue_iff`,
  `mulVec_eigen_iff_rowEquations`, `hasEigenvector_iff_rowEquations`,
  `backSubstitution_isEigenvector`, `backwardVector_hasEigenvector`,
  `padded_eigenequation`.
- `Analysis/TriangularCoefficientBounds.lean`: `norm_gramSchmidt_le`,
  `diagonal_abs_le_opNorm`, `no_bounded_matrix_columns`.
- `RH/QResidueNormalizationBounds.lean`: `inverse_scale_lower`,
  `inverse_scale_tendsto_atTop`, `no_bounded_normalization_matrix`,
  `no_continuous_atom_normalizer`.
- `RH/QResidueTriangular.lean`: `qResidue_linearIndependent_injective`,
  `entry_diagonal_reciprocal`, `entry_diagonal_lower`,
  `entry_diagonal_tendsto_atTop`, `no_bounded_entry_columns`.
- `RH/QResidueFirstNormalization.lean`: `qResidue_two_norm_sq`,
  `qResidue_two_norm`, `first_scale`, `first_coefficient`, `first_mode`.
- `RH/ReciprocalSquareTailBounds.lean`: exact rational difference identities,
  `trigamma_sandwich`, `trigamma_head_sandwich`, `upper_sub_lower`,
  `zetaTwo_eq_trigamma_one`.
- `Analysis/RationalInterval.lean`: exact rational interval operations and
  `contains_*` soundness theorems, including signed products, reciprocals,
  square roots, sums and products; `abs_error_le`.
- `RH/QResidueGramNumerical.lean`: thirty trigamma enclosures, `zeta_bounds`,
  and the ten independent `gram_d_e_bounds` certificates.
- `RH/QResidueMatrixNumerical.lean`: `forward_table_error`,
  `reverse_table_error`, `eigenvector_table_error`, `diagonal_strict`,
  `explicitEigenvector_hasEigenvector`, and `diagonal_isEigenvalue`.

## Scope and open questions

No theorem asserts that the legal squarefree closure equals the ambient Q
Hilbert space, or that qOne lies in it. The original wavelet exclusions remain
unchanged. The finite matrix identities do not imply bounded invertibility on
standard infinite coefficient l2. A full spectrum for an unbounded operator
requires a specified domain and is not asserted here.

The distinct-diagonal premise for backward substitution is explicit; it is
not claimed for all residue indices. Injectivity and d_j > 1 are elementary
dictionary assumptions, not unresolved RH hypotheses.

## Verification and publication

Base revision: `6c217d2b55c7f3091fb640c2958a4eb4dd643a73`.
Toolchain: Lean `v4.33.0-rc2`; pinned Mathlib revision
`51e6992efd06126df61a496bebf8f49482a4e129`.

The exact generic cofactor source passed isolated job
`job_cM7DQHRoST6y663mv_ZulYTQPP1G3SKd` (4.612 server seconds).
The finite triangular specialization, spectral statements and exact first
normalization passed `job_pTmvpqtAxM4JSIRsPSzstSSNewIeKuWL`
(5.890 server seconds).

The saved core modules, complete-tail rational bounds and interval soundness
passed the coherent check `job_QUn5zthWICdufb0_AR3ZPtgrMD3uVa3u`
(14.930 server seconds). Axiom inspection of the no-bounded-realization result,
determinant eigenvalue formula, trigamma sandwich and interval multiplication
reported only `propext`, `Classical.choice`, `Quot.sound`.

Workspace reopening took 116.679 seconds separately. Queue and transport
waiting are not measurements of Lean proof-checking time.

The thirteen principal exact declarations passed a saved-module axiom check
in `job_uwervLLi8xNNaGEFDMtGui5VSr1W_VG9` (13.236 server seconds), each
reporting only the three standard foundational axioms. The complete Gram
numerical certificates passed `job_Ybl-RcCXxFiOIoFZbT9lnRNIYLO8kxzs`
(16.221 server seconds).

The complete numerical matrix module passed
`job__MxdpBAQlLZrUKdX-uIA-ehCiywkt-S3` (14.629 server seconds).
All six principal numerical declarations were axiom-inspected in that check;
each uses only `propext`, `Classical.choice`, and `Quot.sound`.

The complete saved project passed `lake build RiemannResearch --quiet`
in `job_MDuE-8l4yOxEehvnFYV5n5fOwYk1Ag-u` (77.476 seconds including
cache operations). The build reported style and unused-variable warnings,
with no compilation errors.

A saved-module audit of all 487 explicitly named public definitions and
theorems passed `job_gMmxmSc5Gh76zikBa2-nBHqQMP32C6K9`
(6.068 server seconds). It checked that every name exists and rejected any
transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
A source scan of all twelve modules found no `sorry`, `admit`, `unsafe`,
local `axiom`, or `native_decide`.

The user approved publication on 4 November 2026. The approved sources are
integrated with main at `e0a0fcc2609e9c570b9bb564d7c0bd5dd180831f`, preserving
the newer imports. Publication proceeds through the server checkpoint, which
audits and validates the combined project before pushing.
