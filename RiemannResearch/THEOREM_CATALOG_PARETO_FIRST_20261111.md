# Pareto-first research: Priorities 1–7

Source: [Pareto First Projections and Transfer to Q Research Draft](https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e), November 11, 2026, Priority 1 and its detailed acceptance criteria.

Base inspected: `3895041bee07f30260e4eda17ce32371492a2403` in `Cnoack3/RiemannResearch`.

Status: Priority 1 passed its full-project checkpoint and was pushed as `93bc04a3c33a85e88a85268e260f72f7c5a05e9d`. The user authorized automatic commits and pushes for Priorities 1–7. Each subsequent publication must pass its own server checkpoint.

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
| 1. Transfer interface, finite annihilator, inverse bounds | Full-project verified and published as `93bc04a3`. |
| 2. Complete Gram and forcing certificates | General complete-norm certification and two-solve error propagation implemented; two numerical stages externally audited. Kernel replay of these numerical instances remains open. |
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
- Priority 1 full-project checkpoint: `job_DzGh2lmF3XTl7jQt5Mkntj_RqbQL7ayq`; succeeded, full scope, Bazel/BuildBuddy, 808.125 seconds build time; committed and pushed `93bc04a3c33a85e88a85268e260f72f7c5a05e9d`.

Proposed commit message: `Formalize Pareto-first transfer bounds and joint-annihilator estimates`.

### Guarded axiom audit

A second Bazel job compiled `#guard_msgs` assertions for the exact `#print axioms` output of twelve main declarations, including the actual matched bounds, inverse construction, finite and global joint-annihilator theorems, CRT Gram invariance, and the existing unitary projection transport. Every guarded declaration uses exactly `propext`, `Classical.choice`, and `Quot.sound`; no project-local axiom or proof placeholder appears in their transitive axiom dependencies. Hypotheses in theorem types are separately described above.

- Audit job: `job_238Mh3hjqor7lO5umJdxT1387lD5HRZg`; Bazel, `verified=true`, exit code 0.
- Audit code SHA-256: `1807c7873245c642bc79fab5a50d39adeb531d8a81ced949d45ece9e61186c1e`.
- [Guarded audit log](https://app.buildbuddy.io/invocation/2f3f8997-b612-4a1e-aa8d-08f0cd5a138a).

Automatic commit and push authorization for Priorities 1–7 is retained.

## Priority 2: complete forcing certificates

New modules:
- `Analysis/FiniteProjectionForcingCertificate.lean`: exact complete inverse-Gram projection energy; two-solve error propagation; the signed six-term backward budget; complete minimum-error intervals.
- `Analysis/ParetoReciprocalTailCertificate.lean`: full Pareto tail at most C/(H+1), reciprocal-weighted tail at most C/(H+1)^2, and signed moment intervals. Existing periodic mean acceleration is reused.
- `RH/QParetoPrimorialForcing.lean`: actual primorial dictionary, signed source z = d - J c_P, complete forcing energy z^T G_P^{-1} z, and certified endpoints with independent normal errors for both solves.

For trial first-fit coefficients c and forcing coefficients t, the complete bound is

$$
\\|a-S t\\|_P\\leq
\\sqrt{\\operatorname{defectEnergy}(D(1-S c),t)}
+\\sqrt{\\operatorname{defectEnergy}(1,c)}.
$$

The second source uses the trial residual, so the first solve error cannot be omitted. Each defect is measured using the actual complete inverse Gram. The backward-budget variant keeps solver residual, source error, Gram-action error, and all signed mixed terms.

### External exact-rational finite-stage audit

Reproduction source: the Python code block in `RH/ParetoFirstFiniteCertificates20261112.md` (NumPy proposes trial vectors; all acceptance arithmetic uses Python Fraction). Data: `RH/ParetoFirstFiniteCertificates20261112.json`.

The executable checks positive rational LDL pivots for a finite-head Gram lower bound, the entire infinite periodic Pareto tail, the reciprocal tail, both full normal residuals, coefficient rounding, and a separate Q solve. Q errors below use the normalized Q measure; the script encloses zeta(2) before division. Serialized interval endpoints are rounded outward.

| Primorial L | Dictionary | Physical head | Complete P error interval | Complete Q error interval | Forcing-energy upper bound |
| --- | --- | --- | --- | --- | --- |
| 6 | 2, 3, 6 | 600 | [0.07818878, 0.07840057] | [0.05469601, 0.05484008] | 0.000547537 |
| 30 | 2, 3, 5, 6, 10, 15, 30 | 1800 | [0.03739645, 0.03757045] | [0.02534381, 0.02545630] | 0.000818519 |

The full normal-residual intervals are recorded coordinate by coordinate in the JSON. The bounds on first-solve norm errors are 0.000408643 and 0.001114032; the second-solve bounds are 0.000041238 and 0.000070466.

**Evidence boundary:** the general certificate theorems are Lean results. These two numerical instances are independently computed exact-rational external audits, not a kernel replay of the finite arithmetic and interval instances. No convergence, monotonicity of forcing energy, or cofinal smallness follows from this table. In particular, its second forcing endpoint is larger than the first.

Priority 2 source verification and guarded axiom-audit job: `job_oDBEjIJk_lAKif0Bhf7MS8bOxVzn5VWX`; Bazel/BuildBuddy, verified=true, exit 0. Eight main declarations were guarded to require exactly propext, Classical.choice, and Quot.sound. [Audit log](https://app.buildbuddy.io/invocation/96bb1dd5-be23-4e47-a7a4-53226aa452f4). Full-project publication checkpoint follows.
