# Real squarefree residue matrices at infinity

Source: the user's real-matrix and Hilbert–Pólya investigation, 14 October 2026.
This record distinguishes checked finite matrices and limits from an unconstructed
unbounded selfadjoint operator and an unproved zeta identification.

## The exact construction

Write Z = zeta(2). For positive physical indices n,m define

\[
H(n,m)=\frac1Z
\sum_{\substack{d\ge2\\d\text{ squarefree}}}
\frac{(n\bmod d)(m\bmod d)}{d^2}.
\]

The source realizes this as a literal Hilbert Gram kernel:
siteFeature(n) is the conductor-coordinate vector with entries
sqrt(Q(d)) times (n mod d), restricted to squarefree d>=2.
Its square summability is proved from (n mod d)<=n and the full summable Q law.
There is no assumed synthesis bound, finite-tail substitution, or RH hypothesis.

The finite matrix H_N is the principal head on n=1,...,N.
Its entries are real; kernel_one_nonintegral proves 0<H(1,1)<1 and
that H(1,1) is not the cast of any integer. Every finite matrix is positive
semidefinite. The exact quadratic identity is

\[
x^T H_Nx=\left\|\sum_{n=1}^N x_n\,\mathrm{siteFeature}(n)\right\|^2.
\]

The conductor cutoff tends to the complete infinite sum for every fixed entry.
Physical principal entries stabilize exactly as the matrix dimension increases.

This is a change of normalization from the previous real matrix M_N:

\[
H_N=D_N M_N D_N,\qquad D_N=\operatorname{diag}(1,2,\ldots,N).
\]

normalization_congruence proves the exact equality.
A congruence preserves positive semidefiniteness; it does not preserve eigenvalues.
The weighted Schur estimate discussed previously for M_N is not a newly
verified theorem in this development. Unbounded growth below concerns H_N.

## What taking N to infinity proves

Let O_N be the principal submatrix on physical sites 1,3,...,2N-1.
oddMatrix_principal embeds it in H_(2N).

The d=2 summand is exactly 1/(4Z) at every pair of odd sites.
Consequently the constant-vector quadratic form and Rayleigh value satisfy

\[
\mathbf1^T O_N\mathbf1\ge\frac{N^2}{4Z},
\qquad
\frac{\mathbf1^T O_N\mathbf1}{N}\ge\frac{N}{4Z}.
\]

MatrixMaximalRayleigh supplies the actual finite-dimensional eigenvalue
characterization. largestOddEigenvalue_isEigenvalue verifies that the maximal
Rayleigh value is an eigenvalue; largestOddEigenvalue_lower and
largestOddEigenvalue_tendsto_atTop prove

\[
\lambda_{\max}(O_N)\ge\frac{N}{4Z}\longrightarrow+\infty.
\]

These are unconditional theorems. In particular, the finite sections do not
have a common operator bound. The growth is derived from the exact d=2 term.

## The domain obstruction

For all k>=0,

\[
H(2k+1,1)\ge\frac1{4Z}>0.
\]

The first infinite column therefore is not in the counting l2 space.
kernel_first_column_not_l2 proves this directly from coordinate-square
summability. no_operator_on_first_basis proves the following precise statement:

Given a submodule D of l2, a linear map T:D->l2, and e_1 in D, T(e_1)
cannot have the coordinates H(n,1) for every positive n.

truncatedFirstColumn_tendsto proves the scalar entrywise limit.
no_l2_first_column_limit proves that no l2 vector can be the coordinatewise
limit of the truncated first columns. Thus there is no strong l2 limit for
these columns either; this last implication uses the usual continuity of
coordinate evaluation.

This does not prove that every possible smaller domain or alternative
selfadjoint realization is impossible. An unbounded operator can omit e_1
from its domain. Such a domain and realization have not been constructed.
Finite positivity, entrywise convergence, and divergent largest eigenvalues
alone do not supply them.

There is also an exact squarefree row relation:

\[
H(1,m)-H(2,m)-H(3,m)+H(4,m)=0.
\]

kernel_four_relation checks it for every m. It gives the finite null vector
(1,-1,-1,1,0,...), so the raw heads of size at least four are singular.
An inverse construction must explicitly address this nullspace.

## The requested Hilbert–Pólya identification

An operator with eigenvalues gamma_k/(2 pi), for unbounded zeta ordinates
gamma_k, would be unbounded. The factor 2 pi is a scale convention; these
residue calculations do not determine it.
For classical zero infinitude see NIST DLMF 25.10(i):
https://dlmf.nist.gov/25.10.

An equality of eigenvalues with imaginary parts alone would not force RH:
every complex zero has a real imaginary part, even if its real part differs
from one half. A Hilbert–Pólya proof needs a full zero correspondence, including
the real part and multiplicities.

For a positive operator T with eigenvalues lambda_k=gamma_k/(2 pi), an exact
possible target is

\[
\frac{\xi(1/2+2\pi i z)}{\xi(1/2)}
=\det(I-z^2 T^{-2}).
\]

This needs a justified domain, a discrete spectrum, an appropriate inverse-square
determinant, and the completed-zeta identity. The repo's existing
HilbertPolyaMovingSpectralLimit module already gives a conditional RH implication
from an explicit positive-matrix completed-zeta limit; it supplies no provider
identifying these residue matrices.

| Obligation | Status |
|---|---|
| Real entries, non-integer example, full summable kernel | Established in Lean |
| Finite positivity, exact normalization and squarefree row relation | Established in Lean |
| Conductor limit and divergence of an actual largest eigenvalue | Established in Lean |
| First-column domain and l2-limit obstruction | Established in Lean |
| A densely defined selfadjoint operator for a suitable construction | Open |
| Discrete spectrum and convergence of the relevant ordered eigenvalues | Open |
| Exact completed-zeta determinant or full zero correspondence | Open |
| The arithmetic choice of scaling by 2 pi | Open |

The last four rows are research obligations, not assumptions discharged by
the checked results. No new RH theorem or Hilbert–Pólya realization is claimed.

## Source and verification

Three exported modules contain 37 new theorems:

- Analysis/MatrixMaximalRayleigh.lean: 2 general real-matrix Rayleigh theorems.
- RH/SquarefreeResidueMatrix.lean: 25 construction, positivity, normalization,
  non-integrality, and exact relation theorems.
- RH/SquarefreeResidueMatrixGrowth.lean: 10 growth and domain/limit theorems.

The persisted source import check job_sAK4VAYu7k81gOtygxJgY4AyU4PsXv5q
passed: exit code 0, verified=true, 15.878 seconds. It built all three modules
and printed the standard foundational axioms for eleven decisive theorems.
The complete 37-theorem audit job_bHVZoZl1jkRJldh_n0fEC8J5MYvIqKSh passed
(exit 0, verified=true, 5.053 seconds). Every new theorem uses only propext,
Classical.choice, and Quot.sound.
The final publication checkpoint validates the aggregate and changed child
modules; its terminal result and commit are reported with task completion.
