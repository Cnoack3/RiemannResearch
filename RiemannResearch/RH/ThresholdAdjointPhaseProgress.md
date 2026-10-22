# RH adjoint and affine phase progress — 8 September 2026

## Conclusion and scope

RH remains unproved. This continuation closes concrete operator and arithmetic
providers in the existing two-seed threshold program, without assuming RH,
legal density, or an RH-equivalent estimate. All statements use the original
Pareto weight w(k)=1/[k(k+1)], the actual complete real Hilbert space, or the
actual previously defined arithmetic branch coefficients.

Four new modules contain 64 public theorem declarations (including supporting
lemmas). This is a count of formal declarations, not a claim of 64 novel
mathematical results. Existing source claims were inspected at published base
ed5fb41264342d2107de7101998c980f43a0648f.

## Strongest new arithmetic result

For positive integers m,j, define
h_m(j)=(1/sqrt(m)) sum_{r<m} c_{m,r,j}, where c is the actual
affineBranchCoefficient, and
E_m(j)=sum_{r,t<m}(c_{m,r,j}c_{m,t,j}-1/m)^2.
Let E_m=sum_{j>=1} E_m(j), and let s be the existing universalPhaseConstant.

The full, actual numerical series satisfies

    0 <= 2*s - E_m <= 2/(3*m^2).

Thus E_m tends to 2*s, with an explicit one-sided quadratic rate. The existing
rational phase certificate gives 11/72 <= 2*s <= 1/6. In particular,
E_m >= 17/216 for every m>=3. No arithmetic tail has been omitted.

Exact identities precede the estimates:

    E_m(j) = 2*(1-h_m(j)^2)
    2*phaseDelta(j)-E_m(j)
      = 2*(h_m(j)-h_infinity(j))*(h_m(j)+h_infinity(j)),

where h_infinity(j)=sqrt(j(j+1))*log(1+1/j).
The overlap difference is the exact finite sum of the nonnegative logarithmic
gaps over the physical m-block. This gives the rate directly, without an
assumed Riemann-sum convergence theorem or an unproved domination provider.

Uniform complete tail and column estimates are also proved:

    sum_{j>N} E_m(j) <= 2*phaseTail(N) <= 1/[6(N+1)],
    sum_{r<m}(c_{m,r,j}-1/sqrt(m))^2
      <= 1/[9j(j+1)] <= 1/[4(j+1)^2].

These are statements about the actual matrix entries and their infinite
numerical sums. Identifying E_m with the Hilbert–Schmidt norm of an infinite
difference operator still requires the uniform comparison operator and its
block assembly. The numerical limit is proved; that operator identification
is not being assumed or reported as proved.

## Exact operators in the complete weighted Hilbert space

ThresholdHilbertAdjoint supplies, for m,k>=1 and arbitrary f in H,

    (T_m^* f)(k)
      = m/w(k) * sum_{n=mk}^{m(k+1)-1} w(n) f(n).

It also proves exact coordinate recovery from consecutive adjoint pairings:

    f(k) = (k+1)<1,T_k^*f> - k<1,T_{k+1}^*f>.

Consequently the vectors fixed by EVERY positive-integer adjoint dilation are
exactly the real multiples of the unit constant target. The signed coordinate
defect and its norm bound are both proved.

This does not prove joint rigidity for only two selected seeds, nor does it
identify the annihilator of the legal two-seed space.

ThresholdHilbertProjection constructs an actual bounded operator, not an
assumed projection provider:

    T_m^* T_m = m I,      P_m = (1/m) T_m T_m^*.

P_m is idempotent and symmetric, fixes the dilation range, and is contractive.
Its coordinates vanish below m and are the exact Pareto-weighted block means
above that exceptional head. It satisfies the full equalities

    ||f||^2 = ||P_m f||^2 + ||f-P_m f||^2,
    ||f-T_m g||^2 = ||f-P_m f||^2 + ||P_m f-T_m g||^2.

This P_m is the infinite dilation-range projection. It must not be confused
with a finite residue-quotient projection or a finite legal synthesis
projection; those application identifications remain separate.

## Source and endpoint index

All endpoints below have prefix RiemannResearch.RH.Pareto.

| Module | Principal endpoints |
|---|---|
| ThresholdHilbertAdjoint | hilbertDilationAdjoint_coordinate; hilbert_coordinate_recovery; hilbertDilationAdjoint_all_fixed_iff; hilbert_coordinate_defect_bound |
| ThresholdHilbertProjection | hilbertDilationAdjoint_dilation; hilbertBlockProjection_coordinate; hilbertBlockProjection_pythagoras; hilbertBlockProjection_best_approximation |
| ThresholdAffineTailBounds | affineProjectionEnergyTail_le; affineColumnEnergy_le_quarter_successor_sq |
| ThresholdAffinePhaseLimit | affineProjection_phase_gap_rate; affineProjectionEnergyTotal_tendsto; affineProjectionEnergyTotal_positive_floor |

Every new file is in RiemannResearch/RH and is exported by RiemannResearch.lean.
Source docstrings identify the motivating paper and independently developed
proofs; absence of an external citation is not a claim of novelty.

## Verification and publication

Verification submissions were serialized. Successful proof/axiom audits:

- Adjoint and coordinate recovery: job_qtDj7uHo_qKfHEoMnSsSOP41r6LCb5sQ,
  verified=true, exit_code=0, 53.914 seconds.
- Actual projection, Pythagoras and coordinate law:
  job_mcG0IY5oVDhuGoVBOI3eKDvjlzs4ZSh8, verified=true, exit_code=0,
  46.262 seconds.
- Projection contraction and exact best approximation:
  job_vRxRk3STs-4bhbR5Howc9hqh-NgHclvT, verified=true, exit_code=0,
  52.106 seconds.
- Uniform arithmetic tails:
  job_G26KSOOuPIGy3wyYkwQoQVe8ZpRR3S09, verified=true, exit_code=0,
  43.160 seconds.
- Quantitative phase rate, actual limit, and positive floor:
  job_6nIVgnBbuqyY6XbNdd2oQnaWk7wBrkGQ, verified=true, exit_code=0,
  46.611 seconds. Combined source SHA-256:
  f6bd83f8f9599586b3af04cfe762f7478ebd835e1274abd8620fe6cb1b436298.

The audited endpoints report only propext, Classical.choice and Quot.sound.
No sorry, admit, project-local axiom, unsafe declaration or unchecked native
computation is used. Ordinary theorem assumptions (positive integer scales
and membership in the actual real H) remain visible in the types.

These snippet audits are distinct from final acceptance: the publication
checkpoint validates the saved modules through their actual imports and
reverse dependents, audits source, and publishes the accepted changes.
The checkpoint receipt and published commit are reported in the task result.

## Remaining RH obligations and next target

1. Construct the uniform affine comparison operator and identify its actual
   block matrices with the verified numerical sum. The weighted projection
   P_m is now available; the positive limiting discrepancy must be retained.
2. Realize the finite legal projections, weighted covariance and legal cutoff
   synthesis on the actual H, with every mixed and boundary term retained.
3. Prove adequate uniform two-seed repair/full-error convergence. Neither
   the new phase limit nor all-integer adjoint rigidity supplies this.
4. Complete two-seed joint rigidity and shrinking-cell recovery, and provide
   the checked strong Nyman–Beurling dependency and exact discrete bridge.

The nonzero affine discrepancy is an arithmetic comparison obstruction, not
a proof against RH or against possible cancellation by legal combinations.
No new conditional wrapper is offered as an unconditional resolution of
these remaining obligations.
