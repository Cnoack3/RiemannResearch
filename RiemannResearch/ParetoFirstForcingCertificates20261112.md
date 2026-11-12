# Pareto-first §9.1–§9.7 Lean continuation — 12 November 2026

Source: *Pareto First Projections and Transfer to Q Research Draft*,
https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e,
the seven research priorities in Section 9 of
`Pareto_First_CRT_Transfer_Research_2026-11-11.tex`.

This change adds eight modules containing 78 named theorems and 13 definitions,
and reuses the current public ratio-vector API, exposing one existing physical-tail pairing lemma.

This is a formalization and improvement of the reductions, not a proof of RH.
The actual cofinal cancellation estimate remains OPEN. Compactness and profinite
CRT do not prove that a limiting forcing vector is zero.

## Main interfaces

- `Analysis/PositiveCompressionCertificate.lean`: coercivity, solution uniqueness,
  two-sided solution bounds, signed forcing energy, and an inexact finite-head
  solve certificate. The tail acts once on `r-v`:
  `‖d-v‖ ≤ ‖P B r-(I+P B)v‖ + δ ‖r-v‖`.
- `Analysis/PositiveCompressionSharp.lean`: the manuscript's
  `8‖d‖² ≤ ‖r‖²` bound and Richardson contraction factor `1/3`, explicit finite rescaled inverse series,
  its complete-norm convergence, and the off-diagonal forcing bound.
  The hypotheses are explicit quadratic-form and orthogonality facts; their
  actual reciprocal-diagonal instances are supplied in the RH module.
- `RH/QParetoForcingCertificates.lean`: actual matched P/Q corrections,
  reciprocal compactness, the exact cutoff constant 1/(H+1), and the specialized sharp
  displacement and solver bounds.
- `NumberTheory/ProfiniteCRTUniversal.lean`: unique compatible all-modulus
  ring-hom lifts, continuity, naturality under precomposition, and unique
  p-adic-product lifts. These express categorical universal properties directly;
  they do not construct a separate bundled `CategoryTheory.Limits.IsLimit`.
- `Analysis/FiniteHilbertGramEnergyCertificate.lean`: complete dual-Gram energy
  and the exact error from an arbitrary coefficient solve:
  `η² = 2 cᵀz - cᵀGc + (z-Gc)ᵀG⁻¹(z-Gc)`.
- `RH/QPrimorialForcingCertificate.lean`: actual primorial rows, canonical Pareto
  coefficients, complete forcing energy, the unconditional bound 4η² ≤ ε_P ≤ 1, cofinal endpoint implication, and
  exact Pareto accumulated-gain accounting.
- `RH/QJointAnnihilatorMeans.lean`: finite and infinite common-annihilator
  mean bounds and the separate Q-mean obstruction.
- `RH/QCRTCarryLimits.lean`: transported carry Gram invariance, finite synthesis,
  and strong limits with changing projections and stage-dependent coefficients.

## Priority-by-priority status

| Section | Formal result or improvement | Remaining obligation |
|---|---|---|
| 9.1 | Actual normal equation reused; sharp displacement bound, inverse-solve error estimates, Richardson iteration, finite K bound and transported carry invariance | No hidden density premise; a fully bundled arbitrary-source inverse is not needed for the actual correction interface |
| 9.2 | Exact complete Gram energy and inexact-solve remainder; explicit complete-tail displacement certificate | Implement shrinking numerical interval endpoints for successive complete stages; no floating-point inverse is certified here |
| 9.3 | Actual signed row `e-Jc_P` and unconditional `4η² ≤ ε_P ≤ 1`; cofinal smallness of certified endpoints implies Mathlib RH | Prove cofinal smallness for the canonical arithmetic residual |
| 9.4 | Existing exact prime-plus-carry gain reused; new Pareto gain accounting and explicit error for moving prime projections | Prove a cumulative lower bound exhausting the initial residual energy |
| 9.5 | Finite projection bound, stronger tail-dependent mean bound, all-prime Pareto mean zero, and a quantitative Q-mean approximation bound | Prove Q mean zero or further control the actual K/middle-space coupling |
| 9.6 | Compact reciprocal diagonal and certified finite-head error, retaining the full infinite remainder | A uniform arithmetic head bound identifying a zero limit |
| 9.7 | Complete-norm limits of finite blocks with arbitrary stage-dependent coefficients; moving projection term displayed | Supply convergence hypotheses in the intended arithmetic construction |

## The two mean questions

If k annihilates an included conductor in both metrics, it annihilates the
physical ratio `(n mod m)/n`. Consequently its Pareto mean squared is at most
`‖k‖_P²/m`, with the stronger norm bound involving only the physical tail at
sites at least m. Every actual common prime annihilator therefore has zero
Pareto mean.

After that conclusion, the remaining identity is
`ζ(2) ⟨1,k⟩_Q = ⟨D1,k⟩_P`. For any *verified* annihilating trial a,
`|ζ(2) ⟨1,k⟩_Q| ≤ ‖D1-a‖_P ‖k‖_P`.
In particular a scalar multiple of 1 is permitted. This is a quantitative
bound on the actual arithmetic pairing, not a claim of symmetry or vanishing.

## Existing gain results deliberately reused

- `Analysis.ExhaustiveWalk.nested_projection_energy` and `accumulated_gain`.
- `RH.QCRTCarryGain.stage_gain_eq_prime_add_block`,
  `literal_scores_le_actual_block_gain`, and
  `prime_gain_add_score_div_le_total_gain`.
- `RH.QPrimorialRelativeGain.error_eq_initial_sub_gain_sum`,
  `closure_iff_relativeGain_not_summable`, and the conditional theorem
  `riemannHypothesis_of_prime_lower_with_summable_defect`.

These retain all old composite conductors, the new-prime gain, and the actual
remaining energy. Positive gains by themselves do not imply exhaustion.

## External computations and literature

Wolfram was used for the scalar identities
`(n+s)^2-8s(n-s)=(n-3s)^2` and invariance of the scalar Schur complement under
a change of representative. The Lean proofs use exact algebra, not oracle
results.

An exploratory complete-period Wolfram computation at L=6, conductors 2,3,6,
using 40-digit evaluation of the positive residue-weight series gave:

| Quantity | Approximate value |
|---|---:|
| Pareto residual energy | 0.07829325400232255 |
| Complete forcing energy | 0.0005266850394822645 |
| Pareto displacement energy | 0.0001878119063302854 |

These numbers are **not interval certificates**, do not enter any theorem,
and supply no asymptotic conclusion. Digamma/trigamma are used only to evaluate
finite-period positive weights, not as an RH convergence argument.

Primary references:
- Gareth Wilkes, *Part III Profinite Groups* (2020), §2.2, Theorem 2.2.1:
  https://www.dpmms.cam.ac.uk/~grw46/LectureNotes.pdf
- Minghua Lin and Gord Sinnamon, *The Generalized Wielandt Inequality in
  Inner Product Spaces* (2012):
  https://www.math.uwo.ca/faculty/sinnamon/pdf/wielandt.pdf

The compactness proof uses finite-rank approximation and Mathlib's closure of
compact operators in operator norm. No external mathematical statement is
introduced as an axiom.

## Representative declarations

| Priority | Named declarations |
|---|---|
| 9.1 | `solution_sharp_sq`, `richardsonIterate_series`, `richardsonIterate_tendsto`, `correction_norm_bounds` |
| 9.2 | `stageForcing_energy`, `stageForcing_inexact_energy`, `inexact_dualEnergy_upper` |
| 9.3 | `forcingRow_signed`, `stageForcing_energy_le`, `riemannHypothesis_of_cofinal_upper_endpoints` |
| 9.4 | `pareto_accumulated_gain`, `pareto_accumulated_gain_tendsto`, `moving_carry_error` |
| 9.5 | `finite_joint_projection_sq_of_pq`, `pareto_mean_tail_bound`, `joint_q_mean_centered_bound` |
| 9.6 | `reciprocalD_compact`, `reciprocalHead_opNorm_error_eq`, `finite_head_trial_error` |
| 9.7 | `finite_transported_screened_carry`, `finite_block_carry_limit` |

## Verification

Scoped verification passed on the server using Bazel with BuildBuddy (exit 0):
- Job `job_AvGxTOPD8pTWFIn_45Kt4K9gnCfxxpN2`.
- Build evidence: https://app.buildbuddy.io/invocation/ebce8dc1-902f-499c-9488-68a116fdcf45
- This build imports all eight modules and the reused Q carry-gain and relative-gain modules.

A guarded axiom audit of 15 selected principal declarations also passed (exit 0):
- Job `job_zvvnG4_no7dwq-nMCaEFc34YJRyfcDro`.
- Build evidence: https://app.buildbuddy.io/invocation/793a728f-4011-4f76-bc81-ee70a9d3dfc1
- Audit snippet SHA256:
  `73e8b39f79f328426d29a0f808d6741cd5f0045525fc39257d1db852b777482f`.
- Each `#guard_msgs` assertion requires exactly
  `[propext, Classical.choice, Quot.sound]`, allowing only whitespace variation.
- The audited declarations include the sharp bound, inverse-series formula and
  limit, exact cutoff constant, finite-head certificate, actual Gram energy,
  unconditional forcing bound, cofinal RH implication, both mean controls,
  stage-dependent carry limit, both CRT universal properties, and reused gain results.

All accepted declarations require queued server-side Bazel/BuildBuddy checking.
The final publication checkpoint additionally audits source and validates the
full project and current-main integration. A scoped success is not a substitute
for that full-project publication gate.

## Integration with current main

The original verified work remains preserved in local commit
`f2ee5145564c08ac7f74036036e8775b45b480e3`.
This integration was prepared against `0478d5dde7ffa1d028d6e40b783d2630574bd668`.
It retains the newer Pareto-priority modules and their public lemma names
`ratioVector_pair_shifted` and `ratioVector_error_norm_sq_le`.
The new joint-annihilator proofs use those names directly, and the existing
physical-tail pairing lemma is made public without changing its statement or proof.
All theorem statements and substantive hypotheses from the preserved work are unchanged.
The publication checkpoint must validate the complete integrated project before pushing.
