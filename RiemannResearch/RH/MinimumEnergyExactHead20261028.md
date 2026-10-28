# Minimum-energy exact-head adjustment: verification record

28 October 2026. Source: Section 10 of the user's
Squarefree CRT Pointwise Approximation and Research Agenda.

## Checked projection theorem

For a finite residue dictionary V and its zero-head subspace
W = V ∩ {u : u(n) = 0 for 1 ≤ n ≤ H}, define
Fmin = F − P_W F. If F belongs to V, then Fmin belongs to V and
has exactly the same head. For every same-head f in V,

$$
\|f\|_Q^2=\|F_{\min}\|_Q^2+\|f-F_{\min}\|_Q^2,
\qquad
\|F_{\min}\|_Q^2=\|F\|_Q^2-\|P_WF\|_Q^2.
$$

The minimum is attained, unique, and independent of the feasible seed.
These results cover every natural H, including H = 0, and do not
require an anchor conductor above the head.

Declarations in `RH/QResidueHeadSpace.lean`:

- `exactHeadAdjustment_same_head`
- `exactHeadAdjustment_energy`
- `exactHeadAdjustment_completion`
- `exactHeadAdjustment_isLeast`
- `exactHeadAdjustment_unique`
- `exactHeadAdjustment_seed_independent`

## Checked literal matrix formulas

For G positive definite, c0 feasible for A c = e, and independent columns
of B spanning ker A, put S = Bᵀ G B and b = Bᵀ G c0. Then

$$
c_* = c_0-BS^{-1}b,
$$

$$
E(c_0+Bz)
=E(c_0)-b^{\mathsf T}S^{-1}b
 +(z+S^{-1}b)^{\mathsf T}S(z+S^{-1}b).
$$

The minimum is E(c0) − bᵀ S⁻¹ b. It is attained and unique.
The inverse is Mathlib's actual nonsingular matrix inverse;
positive definiteness of S is proved. Empty correction index types
are allowed. No independence of the rows of A is assumed.

See `LinearAlgebra/FiniteAffineGramMinimum.lean`:
`correctionGram_posDef`, `correction_completion`,
`corrected_energy`, `feasible_isLeast`, and `feasible_unique`.

For C = A G⁻¹ Aᵀ and a matrix K satisfying

$$
CKC=C,\qquad (CK)^{\mathsf T}=CK,
$$

the following are also checked:

$$
c_* = G^{-1}A^{\mathsf T}Ke,\qquad
E(c_*)=e^{\mathsf T}Ke,\qquad
E(c)=e^{\mathsf T}Ke+E(c-c_*)\quad(Ac=e).
$$

See `LinearAlgebra/FinitePenroseMinimum.lean`:
`penrose_identity_minimum`, `penrose_identity_completion`,
and `penrose_identity_unique`. These are two defining identities
of the Moore–Penrose inverse, so the result establishes the displayed
dagger formula in Penrose-identity form. This change does not construct
a canonical Moore–Penrose matrix or prove its existence from scratch.
The ordinary inverse correction-space result above is independent
of a pseudoinverse provider.

`Analysis/FiniteHilbertGramMatrix.lean` now explicitly identifies
`inverseCoeff` with multiplication by the actual Gram inverse and
gives `residual_matrix_value`. Thus the matrices use the complete
Hilbert inner product, including the full Q weights.

## Actual legal CRT application

`RH/QCRTMinimumEnergy.lean` applies the correction to the existing
coprime-count seed at L_j = primorial(j + 2), H_j = j + 1.

The resulting `minimumEnergyApproximant j`:

- belongs to the finite squarefree legal span;
- is exactly one on 1 through j + 1;
- converges pointwise to one on the positive integers;
- attains the unique minimum of the full Q norm squared over all
  exact-head vectors in the same divisor stage;
- satisfies the literal compensated-basis inverse-Gram energy formula.

The assumptions of the compensated-basis construction, including an
anchor above the head, are discharged for this actual family.

## Verification and remaining boundary

The combined Lean check succeeded with exit code 0:
`job_6WDnuf1bbVMSqqSk5zDR9f07H6zZkwoB`.
Server-reported checking time was 7.671 seconds; this excludes earlier
development checks and request/queue overhead.

Inspected principal declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
There are no admitted proof steps or new axioms.

The publication checkpoint separately validates the changed modules
and project exports.

**Open:** a uniform bound, or bounded cofinal subsequence, for the
complete energies of these minimum-energy approximants. Pointwise
convergence and individual finite norms do not provide that estimate.
No Riemann Hypothesis conclusion is asserted.
