# Q divisor DPPs and positive spectral limits

Source: the user's Q/DPP/Hilbert–Pólya discussion, 13 October 2026.
This record separates structural identities, conditional RH implications,
and unfinished mathematical or formalization obligations.

## The actual Q space

The law is Q(n)=1/(zeta(2)n^2), n>=1; the legal residue atom is
g_d(n)=(n mod d)/d. Existing QDivisorHilbertBasis provides the complete
orthonormal divisor-wavelet basis, Parseval, residue Gram reconstruction,
and exact full error energy. Prime independence is under Q, without
replacing Q by a uniform CRT law.

The existing squarefree capacity modules retain an explicit analytic
RH-to-squarefree-density provider in their equivalence theorem. That
hypothesis is not discharged by this development.

## Complete-basis projection DPP

RH/QDivisorDPP constructs an actual probability measure on integer
occupation configurations from each finite projection onto the complete
divisor basis. Counting coordinate n represents physical integer n+1.

The module proves:
- the exact finite wavelet-sum kernel;
- vacancy probability equals the squared projection error of a counting vector;
- the kernel tends pointwise to the identity;
- occupation of every fixed finite window tends to probability one.

These statements are unconditional for the complete divisor basis. They
do not prove density of the legal residue span, the Möbius limits of its
optimizer coefficients, or a GUE scaling limit. Moving and rescaled windows
require separate analysis.

## Actual complex generating expectations

Probability/DeterminantalComplexGenerating extends the finite-law
generating identity to complex parameters while retaining the real
probability weights. It includes actual Bochner integrals and finite
windows of countable DPP laws.

If the complexified real kernel is A G^(-1) A*, the weighted generating
statistic is exactly

    det(G-z^2 A* diag(v) A) / det(G).

The original Gram matrix and all signs are retained. Invertibility of G
is enough for this ratio identity, but does not itself prove positivity.

For the feature factorization K=A A* and v>=0, the weighted feature Gram
is positive semidefinite. Spectral factorization and the PSD determinant
zero theorem show that every zero of the resulting polynomial is real.
An infinite multiplicative statistic over the full random configuration
is not supplied by a finite-window identity.

## Moving positive spectra: exact identity before estimates

For Im(z) != 0 and t>=0, the exact identity is

    Im((1-t z^2) conjugate(z)) = -Im(z)(1+t|z|^2).

The norm and triangle inequalities then give

    1 <= |1-t z^2| (1+c_z t),  c_z=|z|^3/|Im(z)|.

Choose a natural k>=16 c_z. Bernoulli's inequality, followed by
multiplication over an arbitrary finite nonnegative spectrum, gives

    1 <= |P_N(z)| |P_N(i/4)|^k.

The exponent depends on z, not N, rank, or the spectral weights. Therefore
finite pointwise limits at z and i/4 prevent a nonreal zero in the limit.
This argument permits a different positive spectrum at every stage; it
does not need a coherent fixed infinite spectrum or a general Hurwitz theorem.

Analysis/PositiveSpectralProduct separately supplies convergence and
uniqueness for ordered truncations of a fixed summable nonnegative spectrum.

## Conditional RH consequences

RH/HilbertPolyaMovingSpectralLimit proves that the following hypothesis
implies Mathlib's RiemannHypothesis:

- each A_N is a finite positive semidefinite complex matrix;
- its rank may change with N;
- c is a fixed nonzero complex number;
- for every s in the open critical strip,

    c det(I-(-i(s-1/2))^2 A_N)
        -> s(s-1) completedRiemannZeta(s).

The test point i/4 corresponds to s=1/4, still inside the strip. A zeta
zero off the critical line contradicts the compensated nonvanishing bound.
A locally uniform version follows from pointwise convergence.

RH/HilbertPolyaPositiveProduct gives the fixed-spectrum version and proves
equivalence between its finite-product limit and infinite-product
representation.

**Conditional research reduction. Open:** construct the displayed
zeta-identification limit. Positivity and the DPP identities do not
construct it. No unconditional RH theorem follows from the present work.

## Scalar logarithmic heat sum

Analysis/LogarithmicHeatSum proves summability and the exact identity

    sum_(n>=1) exp(-s log n) = zeta(s), Re(s)>1.

This is a scalar eigenvalue-weight sum. It does not construct a diagonal
unbounded self-adjoint operator, its domain or resolvents, a trace-class
heat operator, or equality with an operator trace. Zeros of a trace are
not thereby identified as eigenvalues.

## Explicit remaining work

1. Construct sampled exact interpolants and prove determinant-weighted
   unbiasedness. Repository audit found deterministic inverse-Gram
   optimizers, actual DPP configuration laws, and general random-coefficient
   bias/variance identities, but no theorem assembling this averaging identity.
2. Prove the integrability or uniform-integrability statements needed for
   coefficient expectations as dimension tends to infinity. Unbiasedness
   alone supplies no Möbius-limit identification.
3. Supply the positive spectral zeta-identification, an infinite DPP product
   limit, or an appropriate operator realization without assuming RH.
4. Keep the full legal residue family distinct from the unconditional complete
   arithmetic basis and from the masked squarefree optimizer stages.

## Verification

Base commit: 916ac4e34fc39271aea3084e284f6b18399e93b3.
Workspace: ws_RvqoC9o3uRkVJrbWBIQO8V067mgzEi4P.

Earlier cache-restoration jobs timed out; job
job_Ya1Ob9eOCzz48Pc0FeADxff2L5-QJIL6 was interrupted when its owner exited.
Those attempts are not verification evidence.

Targeted server verification succeeded in job
`job_yGratk1RXBlHd2-w7KrgI4oWpLJy-5PC`, with exit code 0 and
`verified: true`. It imported the new DPP, Q-DPP, moving-spectrum RH and
heat-sum modules, compiling their changed dependencies. Eight decisive
declarations were checked with `#print axioms`; every report contained
only `propext`, `Classical.choice`, and `Quot.sound`:

- `Matrix.PosSemidef.det_one_sub_sq_smul_zero_im_eq_zero`
- `DPP.finiteLaw_weighted_square_zero_im_eq_zero`
- `QDivisorDPP.basisLaw_finite_occupation_tendsto`
- `HilbertPolya.riemannHypothesis_of_strip_positive_matrix_limit`
- `LogarithmicHeatSum.tsum_heatWeight_eq_riemannZeta`
- `HilbertPolya.riemannHypothesis_of_strip_positive_spectral_limit`
- `HilbertPolya.riemannHypothesis_of_strip_locallyUniform_positive_matrix_limit`
- `DPP.IsDPP.window_generating_complex`

These axiom reports do not discharge the explicit hypotheses in the
conditional RH theorem types. The final source checkpoint
`job_SJgKZ49ohl0L4H0GEXCZ8KrADxf1S3qt` succeeded, validated the full aggregate
project plus all eight changed modules, integrated newer main, revalidated
the integrated source with full scope, and pushed commit
`42803d2da7feb86323bc28116954271f87abd831`.

The research record and theorem-catalog entry are a subsequent
documentation-only correction; they make no additional Lean source change.
