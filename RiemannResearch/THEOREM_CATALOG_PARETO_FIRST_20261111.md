# Pareto-first research: Priority 1 review

Source: [Pareto First Projections and Transfer to Q Research Draft](https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e), November 11, 2026, Priority 1 and its detailed acceptance criteria.

Base inspected: `3895041bee07f30260e4eda17ce32371492a2403` in `Cnoack3/RiemannResearch`.

Status: scoped Bazel verification passed. The user has now authorized automatic commits and pushes for Priorities 1–7. Each publication must still pass the complete server checkpoint. Priorities 2–7 remain subsequent work.

## Physical-coordinate interface reused

Physical sites are positive integers. Encoded Hilbert coordinates start at zero, so the encoded multiplier `1/(n+1)` is the physical multiplier `1/k`.

| Paper notation | Existing Lean interface | Meaning |
| --- | --- | --- |
| Physical identification P to Q | `QParetoEquivalence.toQ`, `toQCLM`, `paretoEquiv.symm` | Preserves the physical sequence; it is not an isometry. |
| Physical identification Q to P | `ZetaTwoParetoTransfer.toPareto`, `toParetoCLM`, `QParetoEquivalence.paretoEquiv` | Same physical sequence with Pareto encoding. |
| A, Q to P unitary | `QParetoIsometricTransport.A`, `A_physical` | Multiplies physical values by sqrt((k+1)/(zetaTwo*k)). |
| U, P to Q unitary | `A.symm`, `A_symm_physical` | Multiplies physical values by sqrt(zetaTwo*k/(k+1)). |
| Unitary projection transport | `QParetoIsometricTransport.projection_A`, `projection_conjugacy` | Transports the target AND the subspace. |
| D | `ZetaTwoHilbert.reciprocalD` | Physical multiplication by 1/k. |
| S, reverse metric correction | `QShiftedReciprocal.B` | Physical multiplication by 1/(k+1); this B is not the manuscript's density ratio B. |
| Same-space projections | `QParetoClosedProjectionComparison.qFit`, `pFit` | `hsame` explicitly identifies the common physical dictionary. |
| Exact metric equation | `QParetoMetric.inner_identity`, `norm_identity` | Retains the full reciprocal correction. |
| Strong normal equation | `QParetoClosedProjectionComparison.normal_equation_strong` | d + projection(D d) = projection(D r_P). |

## New declarations

### Sharp complete displacement energy

Module: `RiemannResearch/RH/QParetoDisplacementBounds.lean`.

For r orthogonal to d and the exact normal equation pairing, `sharp_energy_remainder` proves

$$
\|r\|_P^2=8\|d\|_P^2
+\langle r-4d,D(r-4d)\rangle_P
+\bigl(\|r+2d\|_P^2-\langle r+2d,D(r+2d)\rangle_P\bigr).
$$

Both displayed remainders are nonnegative. `sharp_energy_bound` and `sharp_norm_bound` give the manuscript's constant 1/(2 sqrt(2)). `matched_sharp_energy_bound` discharges the normal-equation premises for the actual two projections of any target onto the same physical closed subspace.

`displacement_le_forcing`, `forcing_le_twice_displacement`, and `normal_solution_unique` give stable inversion and uniqueness in the complete Pareto norm.

### Rescaled inverse and finite errors

Module: `RiemannResearch/RH/QParetoDisplacementResolvent.lean`.

`feedback` acts on the subspace as (I-2T)/3, and `feedback_norm_le` proves the contraction factor 1/3. `inverseApprox_error_succ` is the exact signed remainder recursion. `inverseApprox_error_norm` gives

$$\|d-d^{(N)}\|_P\leq 3^{-N}\|a\|_P.$$

`inverseSeries_summable_norm` proves absolute norm summability of this OPERATOR-response series. `inverseSeries_hasSum` identifies its sum with the normal-equation solution. This is not an unconditional residue expansion of the constant target.

`inverseSum_normal_equation`, `inverseSum_norm_bounds`, and `existsUnique_normal_solution` construct the solution for every forcing a in the subspace and prove norm bounds ||a||/2 <= ||d|| <= ||a||. `matched_displacement_eq_inverseSum` and `matched_inverseApprox_error` instantiate the construction with the actual canonical forcing, for arbitrary matched finite or closed dictionaries.

### Finite and global joint annihilators

Module: `RiemannResearch/RH/QParetoJointAnnihilator.lean`.

`jointAnnihilator V W` is the physical Pareto realization of V intersected with the P and Q annihilators of W. Closedness follows from closed V and continuity of the physical identification.

`mean_bound_of_two_orthogonalities` works for ANY positive conductor m, not only primes:

$$|\langle 1,k\rangle_P|\leq m^{-1/2}\|k\|_P.$$

`joint_projection_norm_le`, `joint_projection_fit_eq`, and `joint_projection_fit_norm_le` yield the finite-stage projection bound and the exact nesting equality. `finite_prime_joint_projection_bound` uses the actual largest member of a nonempty finite prime set.

`joint_mean_zero_of_cofinal_conductors` states the cofinality requirement explicitly; `joint_mean_zero_of_all_primes` supplies it from all prime atoms. `joint_qMean_identity` and `joint_qMean_zero_iff` leave the Q-mean question as the explicit extra reciprocal pairing with D1. They do not assert Q-mean zero.

Two existing private lemmas in `QFiniteForcingData.lean` become reusable declarations: `ratioVector_pair_shifted` and `ratioVector_error_norm_sq_le`. Their proofs are unchanged; their in-file uses are renamed.

### CRT representative invariance

Modules: `RiemannResearch/Analysis/ResidualizedProjectionKernel.lean` and `RiemannResearch/RH/QCRTRepresentativeInvariance.lean`.

`residualized_representation` is the general Hilbert-space identity. `carryResidual_eq_neg_residue` applies it to actual canonical CRT carries. `alternative_synthesis_residual`, `carry_gram_representative_invariant`, and `carry_source_representative_invariant` prove invariance of the complete residualized carries, their Gram entries, and their forcing entries under changes of prime synthesis inside the same projected prime space. The realization L may be the identity for Q or `toParetoLinear` for P.

The existing `LinearAlgebra.inner_residualized_eq_schur` and `finiteSchurResidual_inverse_covariance` identify these residualized Gram entries with the complete Schur correction. These are complete Hilbert inner products, including all tails. No numerical Gram interval certificate is claimed here; that is Priority 2. The later block-gain and cumulative-exhaustion obligations remain Priority 4.

## Unresolved research obligations

| Priority | Status after the Priority 1 package |
| --- | --- |
| 1. Transfer interface, finite annihilator, inverse bounds | Implemented; scoped Bazel check passed; full-project checkpoint and publication authorized. |
| 2. Complete Gram and forcing certificates | Open; numerical tail/solve/rounding certificates not supplied by this package. |
| 3. Actual signed arithmetic cancellation | Open; no cofinal vanishing of canonical forcing proved. |
| 4. Cumulative carry gains | Open; representative invariance does not show energy exhaustion. |
| 5. Actual Q-mean and middle-subspace coupling | Open; exact reciprocal obstruction retained. |
| 6. Finite-rank compactness error certificates | Subsequent work; no zero limiting input assumed. |
| 7. Admissible limits and stage dependence | Subsequent work; operator series here is explicitly distinguished from prohibited fixed residue expansions. |

No density, RH, residual-vanishing, or forcing-vanishing premise is introduced into the unconditional structural results. The same-physical-subspace hypothesis in matched projection theorems is explicit. Standard projection-existence/closedness assumptions are functional-analytic assumptions, not unresolved arithmetic providers.

## Verification evidence

- Base commit: `3895041bee07f30260e4eda17ce32371492a2403`.
- Successful source check: `job_d95ybYI2x8RxJlYFmf1Adm2gv3Z2tsPK`.
- Backend: Bazel with `--config=buildbuddy`; `verified=true`, exit code 0.
- Server-reported source-check duration: 63.82 seconds; this excludes earlier setup, proof iteration, and polling delays.
- Scope: Four new Priority 1 modules, two edited supporting modules, existing isometric transport, and their transitive imports; not a full-project checkpoint.
- [Build log](https://app.buildbuddy.io/invocation/13b5216a-210e-48ce-9206-58c346f21c29).
- No commit or push has occurred. The publication checkpoint must validate the complete project and any integration with newer main before pushing.

Proposed commit message: `Formalize Pareto-first transfer bounds and joint-annihilator estimates`.

### Guarded axiom audit

A second Bazel job compiled `#guard_msgs` assertions for the exact `#print axioms` output of twelve main declarations, including the actual matched bounds, inverse construction, finite and global joint-annihilator theorems, CRT Gram invariance, and the existing unitary projection transport. Every guarded declaration uses exactly `propext`, `Classical.choice`, and `Quot.sound`; no project-local axiom or proof placeholder appears in their transitive axiom dependencies. Hypotheses in theorem types are separately described above.

- Audit job: `job_238Mh3hjqor7lO5umJdxT1387lD5HRZg`; Bazel, `verified=true`, exit code 0.
- Audit code SHA-256: `1807c7873245c642bc79fab5a50d39adeb531d8a81ced949d45ece9e61186c1e`.
- [Guarded audit log](https://app.buildbuddy.io/invocation/2f3f8997-b612-4a1e-aa8d-08f0cd5a138a).

Automatic commit and push authorization for Priorities 1–7 is retained. The next action is the complete server checkpoint for this Priority 1 package; Priority 2 follows after that checkpoint succeeds.
