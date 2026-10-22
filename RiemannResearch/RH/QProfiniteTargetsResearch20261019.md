# Squarefree profinite Q targets: checked finite results and open estimates

Date: 2026-10-19 (UTC).

Source: user-provided
`Squarefree_Profinite_Lattice_Q_Geometry_and_Research_Agenda_2026-10-16(2).md`,
especially Sections 4–10 and Targets 1–5, and
`Q_Conditional_Carries_Energy_Bounds_and_Research_Agenda_2026-10-18.md`.
These sources supply the statements and research priorities. The Lean proofs
use the existing physical Q Hilbert space and literal complete inverse-square
series; no trigamma convergence estimate is used.

## Status

| Target | Established finite results | Remaining obligation |
| --- | --- | --- |
| 1: conditional leakage | All new conductors e p with e dividing L are conditioned at the old L; exact positive alpha weights, signed coarse/innovation Gram decomposition, canonical prime and integer step-carry means, and a positive zero-fiber leakage floor | Estimates on selected growing legal combinations strong enough for approximation |
| 2: bounded exact heads | Exact head costs, period gains and their joint telescope; a nonsquarefree next site costs exactly zero | A specific legal exact-head family with a uniform complete-Q norm bound |
| 3: legal Schur gains | Existing scalar/block Hilbert identities are reused; new literal arithmetic conditional Gram decomposition retains every signed term | An arithmetic estimate proving that legal gains exhaust the initial residual |
| 4: Q Fourier route | Absolute convergence, linear-first character Gram identity, finite DFT Gram formula for legal residues, entrywise bound and complete frequency-block cancellation | An RH-strength estimate for growing legal blocks |
| 5: finite infrastructure | Kernel, quotient/index, explicit integral coordinates; residue-weight consistency and scaling; matching uniform/Q normalized-average limits; constructed canonical CRT coefficients and exact floor carries | Prime-coordinate lattice-basis conversion and the optional profinite inverse-limit formalization |

No bounded-energy provider, legal-density theorem, or RH proof is claimed.
Targets 2 and 3 remain open in their substantive analytic parts.

## Conditional arithmetic and the zero fiber

`RH/QResidueConditional.lean` represents residues by 1,...,L, so L is
residue zero. With w_L(a) the complete progression mass,

    alpha(L,p,a,k) = w_(Lp)(a+Lk) / w_L(a),

`alpha_pos` and `alpha_sum` give positive weights of total mass one.
`conditionalValue_new_residue` handles every e|L, including e=1.
The construction does not replace conditioning at L by conditioning at e.

`carry_sequence` identifies the legal step carry p g_(ep)-g_e with
floor(n/e) mod p. `conditionalValue_step_carry` gives its exact finite
conditional mean. This step carry is distinct from the prime-coordinate
floor carry in Section 4 of the source.

`periodic_conditional_gram` is the complete Q Gram decomposition:

    E_Q[f g] = sum_a w_L(a) E[f|a] E[g|a]
               + sum_(a,k) w_(Lp)(a+Lk)
                   (f(a+Lk)-E[f|a]) (g(a+Lk)-E[g|a]).

No signed cross terms or infinite tails are discarded.

`conditionalValue_multiples` proves the exact Q scaling on multiples of L.
`conditionalValue_not_old_legal` and `conditional_leakage_floor` retain
the residue-zero contribution. For every f in the old divisor stage,

    sum_a w_L(a) (E[g_(Lp)|a] - f(a))^2 >= m_p^2 / L^2,

where m_p=E_Q[g_p]>0 for p>1. The theorem states the literal finite
weighted profile energy; it does not identify a newly defined measure-theoretic
conditional-expectation operator with an orthogonal projection.

## Canonical prime CRT floor carries

`RH/QPrimeCRTCarries.lean` constructs

    a_(d,p) = val((d/p : ZMod p)^(-1))

for squarefree d. It proves 1 <= a_(d,p) < p for p|d and the complete
cleared reciprocal congruence. `canonical_prime_carry` then proves the
source's exact real identity with the integer floor carry; the coefficients
are not left as an unproved existence assumption.

`carryVector_sequence` identifies that integer floor carry with its actual
finite QHilbert combination of legal residues. `carryVector_mem_squarefreeSpan`
proves legality for squarefree d. `conditionalValue_carry_finite` gives
its complete-Q old-modulus conditional formula whenever d divides L r.
Its modular-certificate hypothesis is discharged by the canonical provider
for the prime-factor table.

The finite coefficient bound and period needed by this conditional formula
are proved in the same module. No carry term is discarded by reduction
modulo one.

## Exact-head accounting

The additions to `RH/QSquarefreeAffineHead.lean` prove, under its explicit
finite feasibility hypotheses,

    E_(J,K) + G_(L -> K at H) = E_(H,L) + C_(H -> J at K),
    E_n + sum_(i<n) G_i = E_0 + sum_(i<n) C_i.

Here every G_i and C_i is the actual squared norm of a difference of affine
optimizers. The anchor changes are justified by the existing
anchor-independence theorem.

`exact_head_extend_nonsquarefree` uses the existing radical jump identity.
If a squarefree legal vector equals one at every positive integer below a
nonsquarefree n>=2, it already equals one at n.
`nonsquarefree_boundary_no_cost` consequently proves equality of both the
optimizers and their complete Q minima across that boundary.

The telescope reduces a possible bounded-family construction to controlling
the signed cumulative balance of head costs and period gains. Positivity
alone supplies no such uniform bound.

## Schur and coefficient-recovery results already in the project

`LinearAlgebra/FiniteHilbertSchur.lean` supplies
`finiteSchurResidual_inverse_gain`, with the actual invertible residualized
Gram map, and completion of the square.
`LinearAlgebra/ConditionalSchurDecomposition.lean` supplies
`finite_residual_objective` and `augmented_projection_residual`.
Their hypotheses require the actual normal equations; arbitrary matrix
data are not a substitute.

`RH/NormalizedResidueExactHeadCharges.lean` supplies
`residueFraction_sum_mobiusDifference`, full finite coefficient recovery,
and the exact-head coefficient and reciprocal-charge constraints.
`RH/QSquarefreeExactHeadAverages.lean` supplies
`squarefree_closure_capacity_and_rh_of_bounded_exact_heads`.
That last declaration is a conditional research reduction: the uniformly
bounded family it consumes has not been constructed here.

## Fourier cancellation and the finite lattice

`RH/QFourierKernel.lean` uses an explicitly linear-first pairing and the
complete normalized Q law. `synthesis_gram`, `periodic_gram`, and
`qResidue_gram` express actual finite Gram forms using K_Q(theta-phi).

`complete_block_sum` proves

    sum_(i,j in Z/LZ) K_Q(i/L-j/L) = 1.

The constant-frequency character is included. The corresponding physical
packet is L times the indicator of L dividing n, with squared Q norm one.
This is a complete-block cancellation identity, not a declaration that the
packet is squarefree legal or that the full Gram operator is uniformly bounded.

`NumberTheory/ResidueRelationLattice.lean` defines the actual kernel of the
integer charge modulo L, identifies its quotient with Z/LZ, and proves
index L when the dictionary contains L>0. It also gives existence and
uniqueness of integral expansions in

    L e_0,  e_i - (L/d_i)e_0  (i != 0),

where d_0=L. This is an explicit basis parametrization, not a use of Lean's
`Basis` API. The source's different prime-coordinate basis is not yet
identified with these coordinates.

## Same observables, different approximation limits

`RH/QUniformNormalizedAverages.lean` proves the literal finite uniform
formula, for pairwise coprime d_i>=2 dividing a positive common period L,

    uniform error = (1/M^2) sum_(i<M) (d_i+1)/(3(d_i-1)) <= 1/M.

The sequence bridge identifies this function at every physical coordinate
with the normalized Q vector average. For escaping conductors the Q average
tends to zero in norm. `qUniformNormalizedAverage_two_measure_limits`
therefore gives uniform squared error tending to zero and complete-Q
squared error tending to one for the same averages. Primes also satisfy
the separate squarefree-legality theorem. The uniform side is a finite
common-period statement; no profinite Haar measure construction is needed.

## Verification boundary

All new declarations are intended for server source audit and affected-module
validation through the final push-enabled workspace checkpoint. The resulting
terminal job and published commit are reported in the accompanying response.
The development uses no `sorry`, `admit`, project-local axiom, or unsafe
declaration. Ordinary Mathlib foundations do not discharge the explicitly
listed open analytic obligations.
