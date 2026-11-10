# Full-conductor dilation and projection audit, November 2026

## Canonical full-conductor divisor projections (9 November 2026)

Module: `RiemannResearch/RH/QFullDivisorProjection.lean`.

- `qOptimizer` and `pOptimizer` are the actual orthogonal projections onto
  the same divisor dictionary in Q and Pareto. The period is a positive L;
  all conductors dividing L are allowed, including prime powers and L itself.
- `iSup_divisorStage_eq_full`, `qOptimizer_tendsto`,
  `pOptimizer_tendsto`, and `lcm_displacement_tendsto` identify the
  unconditional limits with the existing full-family projections and
  `QFullDisplacement.displacement`.
- `sequence_mod_of_mem`, `factors_through_residue`,
  `continuous_profiniteLift`, and `profiniteLift_natCast` construct the
  finite quotient functions and their continuous profinite extensions.
- `positive_site_error_one` retains the exact error of one at the positive
  site equal to the period. `no_uniform_approximation_to_one` shows that
  finite legal fits cannot converge uniformly to one on the positive integers.
- Task A1 remains supplied by
  `QFullDisplacement.displacement_eq_projected_pResidual`,
  `witness_mean_energy`, and
  `witness_mean_eq_residual_energy_difference`; no squarefree closure is
  substituted in their types.

Index distinction: conductors up to M have common period lcm(1,...,M).
Conductors up to L generally do not all divide L. The divisor dictionary
is used to include g_L while preserving period L.

**Open:** a common modulus or boundedness estimate for the actual displacement.
Continuous finite cylinder functions and Hilbert convergence do not establish
continuity of the limit on the profinite integers. Quotient reduction
compatibility is not compatibility of successive scalar projection functions.
The conditional RH consequences remain in `QFullCRTDisplacement.lean`.

## Established finite and Hilbert identities

Module: `RiemannResearch/RH/QFloorDilationEnergy.lean`.
The following additions concern the actual inverse-square Q space and every
integer dilation m > 1, without a squarefree assumption.

- `qBlockWeight_lt`: each positive quotient block has mass strictly below Q(k)/m.
- `qBlockDefect_pos`: every positive block defect is strictly positive.
- `qBlockDefect_energy_summable`: the complete nonnegative energy defect is summable.
- `floorDilation_norm_sq_lt`: for nonzero f, ||T_m f||_Q^2 < ||f||_Q^2/m.
- `floorDilation_sharp_equality_iff`: equality in that bound iff f = 0.

These strengthen the existing weak upper estimate and exact defect identity.
They do not supply a uniform constant smaller than 1/m. They do not imply
that legal approximation error vanishes.

Source: user-requested full-conductor research audit; direct strict
inverse-square block comparison. No mathematical priority claim is made.
The initial coherent snippet passed server job
`job_mU_yRm8NjQrXSTs_Lxa0DDUDlUQRKfHl` (31.249 seconds);
these additions were published in commit 7ec9ee06cb5432a3e96597845f8780523ac2f433.
Their fresh verification is recorded below.

## Finite zeta-zero normal equations on the full residue quotient

The metric here is the physical Pareto norm. The stage modulus can be any
positive integer, including the running LCM with every prime-power divisor.

- [ParetoResidueClassMellin.lean](RH/ParetoResidueClassMellin.lean) proves the class formulas.
  `error_norm_sq_eq_classes` groups the entire error by physical residue
  classes. `multiples_mass_bounds` bounds the compulsory term between
  `1/L²` and `2/(L(L+1))`. `class_pairing_eq_mellin` and
  `error_zero_moment` verify the actual bounded-step zeta coordinate at
  every zero in the positive half-plane, with the entire multiples
  coordinate subtracted from the source.
- [ParetoResidueZeroNormal.lean](RH/ParetoResidueZeroNormal.lean) proves the projection formulas.
  `zero_gram_entry` gives the signed real Gram entries.
  `exists_zero_normal` and `certificate_eq_projection` give consistency
  and uniqueness of the synthesized certificate for a possibly singular
  Gram matrix. `legal_error_completion` gives the compulsory mass, the
  certificate energy, and the complete remaining square. The inverse
  quadratic is available in `legal_error_completion_inverse` when the
  rows are independent. `exists_lcm_critical_line_family` supplies any
  prescribed finite number of distinct simple positive-height critical-line
  zeros, using the existing Lean zero-existence theorem.

The first-difference normalization is `s * Mellin`. The finite equations
apply to every legal competitor at the stage. Quantitative decay of the
remaining square for the actual optimal legal competitors is a separate
obligation.

### Checked critical-line certificate asymptotics

- [ParetoResidueCriticalGram.lean](RH/ParetoResidueCriticalGram.lean) proves
  `critical_class_tail_bound`, `classCrossSum_firstPeriod_bound`, and
  `classCross_tendsto`. The first-difference tail is of order
  `L^(-3/2)`. With the complete progression weights the cross-entry
  perturbation is of order `1/L` per class, uniformly in its representative
  for fixed ordinates. The sum of perturbations is bounded, and the
  existing ungrouped critical-line Gram limit applies.
- [ParetoResidueCriticalNormalLimit.lean](RH/ParetoResidueCriticalNormalLimit.lean)
  proves `normalizedCriticalGram_tendsto` and the canonical
  `legal_error_completion_canonical` at every modulus. For fixed distinct
  positive ordinates, the normalized real Gram tends to the diagonal with
  each `|rho|²/2` appearing twice. The source tends to `(1,0)` for each
  zero. The checked limit `critical_certificate_log_tendsto` is
  `(log L) C_L → 2 sum_{rho in Z} |rho|^(-2)` for actual critical-line zeros.
- [ParetoResidueAtomTests.lean](RH/ParetoResidueAtomTests.lean) gives
  `class_pairing_atom_zeta`, with grouped pairing
  `zeta(s) (1/d - d^(-s))` for every `d | L`.
  `lcm_zero_row_orthogonal_prime` specializes this to every prime
  up to the cutoff. `omitted_six_span_error_floor` proves a squared
  distance of at least `1/92` when conductor six is omitted, which
  applies to prime-only and prime-power-only dictionaries. The
  separating functional is `2 f(1) - f(3) - f(5) + f(6)`.
  `lcm_log_eq_sum_vonMangoldt` identifies `log lcm(1,…,M)` with the
  complete von Mangoldt sum. The exact successive jumps are already
  available in `Nat.log_lcmUpto_succ_sub`.
- [ParetoLCMZeroCertificate.lean](RH/ParetoLCMZeroCertificate.lean) gives
  `lcm_critical_certificate_psi_tendsto` and
  `lcm_critical_certificate_cutoff_tendsto` on every cofinal cutoff
  sequence. Either `psi(M)` or `M` gives the same limiting constant.
  `lcm_critical_certificate_legal_error_floor` gives the corresponding
  lower bound uniformly over all legal trials. `lcm_error_four_terms`
  adds the squared displacement from the actual legal projection to
  the optimum's compulsory mass, certificate energy, and remainder.
  `lcm_remainder_eventually_ge_of_right_zero` bounds the optimized
  remainder away from zero if there is an actual zero with real part
  above one half.

### Published comparison and open remainder

For a fixed critical family, `lcm_remainder_tendsto_zero_iff`
identifies the vanishing of the optimized remainder with membership of the
target in the full Pareto closure. `riemannHypothesis_of_lcm_remainder`
proves the implication to Mathlib's RH. **Open** is the unconditional
upper bound tending to zero for this remainder.

The comparison theorems `lcm_best_error_as_naturalError` and
`lcm_best_error_le_two_naturalError` retain the exact complete norm. With
`d_N` denoting the classical distance through conductor `N` and `E_M`
the optimum squared Pareto error on the LCM divisor dictionary, they give
`d_(lcmUpto M)^2 ≤ E_M ≤ 2 d_M^2` for `M ≥ 1`.
The lower side uses the exact index-one charge correction and the upper
side uses the complete centering bound. The checked equivalence
`lcm_remainder_tendsto_zero_iff_naturalApproximation` identifies the
remainder condition with the classical natural approximation proposition.
Báez-Duarte's published theorem supplies the converse from RH at the
paper level. [Báez-Duarte](https://arxiv.org/abs/math/0202141)

Burnol's classical lower bound uses multiplicity-squared contributions
from zero derivatives. The grouped certificate above uses one complex
value per chosen zero. Published classical upper estimates of Balazard
and de Roton require RH. Bettin, Conrey, and Farmer obtain the logarithmic
order under RH and an additional reciprocal zeta derivative moment
bound. The two comparisons transfer the lower bound and the conditional
upper orders to the LCM optimum.
[Burnol](https://arxiv.org/abs/math/0103058)
[Balazard–de Roton](https://arxiv.org/abs/0812.1689)
[Bettin–Conrey–Farmer](https://arxiv.org/abs/1211.5191)

### Upper-rate inputs and moving zero tests

- `lcmBest_tendsto` and `lcmRemainder_tendsto_limit` identify the
  unconditional limit with the full legal projection and its squared
  residual, respectively. For fixed distinct positive critical ordinates,
  `lcmError_sub_remainder_cutoff_tendsto` gives
  `M (E_M - R_M) → 2 sum_{rho in Z} |rho|^(-2)`.
  `riemannHypothesis_of_cofinal_remainder_upper` needs a vanishing upper
  budget only along a cofinal sequence. The finite
  `right_zero_re_le_of_lcmError_bound` confines a zero with
  `|Im rho| ≤ T` to `Re rho ≤ 1/2 + (1+T²) B/2` whenever `E_M ≤ B`.
  This is the physical Pareto form of a finite distance-based zero exclusion.
  [Delaunay–Fricain–Mosaki–Robert](https://delaunay.perso.math.cnrs.fr/zero_free_regions.pdf)
- `lcm_sum_ramanujan_mean_eq_psi` identifies the total sparse Ramanujan
  source over all LCM divisors with the same Chebyshev scale.
  `certificate_orthogonal_atom` and
  `certificate_shift_preserves_atom_pairing` keep the legal normal source
  intact after removing the zero certificate. `omitted_conductor_error`
  gives the exact dual-norm obstruction at every omitted squarefree
  conductor by taking the square of its Möbius charge.
- [ParetoResidueCriticalGramRate.lean](RH/ParetoResidueCriticalGramRate.lean)
  checks a uniform unnormalized Gram error for each pair of critical
  frequencies. After division by their norms its budget has linear
  dependence on their heights and an inverse-gap term off the diagonal.
  `growing_critical_gram_pairing_error_tendsto_zero` permits a moving
  collection with vanishing explicit coefficient-weighted budget.
  The theorem concerns the Gram error and leaves the legal projection
  remainder as a separate quantity.
- [ParetoLCMAnalyticRates.lean](RH/ParetoLCMAnalyticRates.lean) proves
  `lcmError_le_shifted_zeta_budgets` for the centered version of the
  Balazard--de Roton split, and `bcf_lcm_log_upper_of_natural_budget`
  transfers a complete classical BCF trial budget without a factor-two
  loss in its leading constant. The repository Möbius means supply the
  charge condition `charge² log M → 0` unconditionally. If `E_M` is
  the optimized squared error, `lcm_remainder_mul_log_inv_error_le`
  gives `R_M log(1/E_M) ≤ 1-E_M`, an upper estimate at the error's own scale.

The open Balazard--de Roton inputs are the weighted shifted-quotient and
truncation bounds on a common schedule. The shift-factor condition is
`Re rho ≤ Re s + ε/2` for each zero. The published argument uses RH
for the quotient estimate, the contour evaluation, and the truncation.
The open BCF input is the complete trial budget. Its published
provider assumes RH and the reciprocal zeta derivative second-moment
bound. An off-line zero contributes a horizontal power of the cutoff
in its residue factor. Maier and Rassias analyze that effect under an
exceptional quartet. [Balazard–de Roton](https://arxiv.org/abs/0812.1689)
[Bettin–Conrey–Farmer](https://arxiv.org/abs/1211.5191)
[Maier–Rassias](https://doi.org/10.4153/CMB-2017-070-3)

### Microscopic coefficients and moving certificate energy

- [ParetoResidueMicroscopicGram.lean](RH/ParetoResidueMicroscopicGram.lean)
  proves `phaseStrippedCross_sub_logPhaseKernel_le` and its moving limit.
  After removing the critical-point factors the coefficient is
  `exp(-i v/2) sinc(v/2)` at `v = (t-u) log L`, with an explicit error
  of order `(1+|t|+|u|)/log L` that is uniform in the gap. The limiting
  two-ordinate determinant is positive for nonzero scaled gaps and zero
  at a collision.
- [ParetoResidueMovingCertificate.lean](RH/ParetoResidueMovingCertificate.lean)
  gives the real entry formula with both difference and sum frequencies,
  the finite energy sandwich, and `moving_critical_certificate_tendsto`
  under explicit row and source budgets. The uniform multiples-source
  error retains the `L^(-3/2)` scale.
- [ParetoResidueMovingGrowth.lean](RH/ParetoResidueMovingGrowth.lean)
  proves the harmonic inverse-gap row estimate and
  `lcm_moving_critical_certificate_of_log_spacing`. A family of `m`
  positive ordinates of height at most `T` and signed separation `δ`
  has the moving energy law when
  `[m(1+T) + log(2m)/δ]/psi(M) → 0`. The uniform reciprocal source
  bound follows from the checked actual-zero sum.
- [ParetoLCMRamanujanCertificate.lean](RH/ParetoLCMRamanujanCertificate.lean)
  proves `lcm_packet_inverse_zero_split`. On the complete divisor
  dictionary, `1 - Λᵀ H⁻¹ Λ` equals the compulsory multiples mass plus
  the zero-certificate energy and the optimized remainder.
  `packetClassVector_prime` gives `R_p = p g_p` in the weighted quotient.
  The certificate shift preserves every packet normal source.
- [ParetoShiftedZetaCompactWindow.lean](RH/ParetoShiftedZetaCompactWindow.lean)
  proves `shiftedZetaQuotient_window_le` without RH. On every fixed
  ordinate window the integral is at most `C_T ε` for small positive
  shifts. The moving-height tail and the Möbius truncation budget remain
  Open. [Balazard–de Roton, Proposition 2](https://arxiv.org/abs/0812.1689)

## Full-conductor product distance (agenda A5)

`RH/QFullProductDistance.lean` proves the exact signed product identity,
the Pareto normal pairing limit, and a finite Cauchy–Schwarz lower bound
with the exact harmonic number. All distances use the full legal closure.

- `residueProduct_finite_distance_bound` bounds the squared cheaper harmonic
  sign on every physical head X < m by the complete product distance and
  the exact correction pairing.
- `residueProductDistance_polylog_escape_of_not_RH` proves that the scaled
  product distance divided by (1 + log m)^k tends to infinity under failure
  of RH, for each real k >= 0.
- `naturalApproximation_iff_cofinal_residueProductDistance` identifies the
  cofinal product bound with Báez-Duarte's natural-dilation approximation
  condition. `riemannHypothesis_of_cofinal_residueProductDistance` proves
  the implication to Mathlib RH. The reverse implication in
  `riemannHypothesis_iff_cofinal_residueProductDistance` takes the published
  analytic implication as an explicit premise.

Báez-Duarte, Rend. Lincei Mat. Appl. 14 (2003), 5–11, Theorem 1.
https://arxiv.org/abs/math/0202141

## Open obligations

- Establish a cofinal product-distance bound for the actual full displacement (A6).
- Formalize the analytic RH-to-natural-approximation direction of Báez-Duarte's theorem.
- Prove a quantitative regularity or tail bound for the actual full displacement.

## Full-conductor continuation: checked structure and conditional RH reduction

Source: the attached Full_Conductor_RH_Reproducibility_Supplement.zip and its
companion Full_Conductor_RH_Projection_Machinery.tex, 6 November 2026.
No mathematical priority claim is made.

The continuation adds 41 named theorems in five modules. The distinction
between proved implications and unproved bounds on the actual displacement
is essential.

### Full matched projections (agenda A1)

`RH/QFullDisplacement.lean` uses literally
`QFullResidueProjection.closure`, the closed span of every residue
`qResidue (i + 2)`. Its Pareto closure is the image of the same algebraic
dictionary under the sequence-preserving measure equivalence, followed by
closure. The two projections are not identified.

With r_Q = 1 - f_Q, r_P = 1 - f_P, d = f_Q - f_P, and
B h(n) = h(n)/(n+1), the module proves

- r_P = r_Q + d and d belongs to the full legal closure;
- w = B r_P - d is orthogonal to that full closure;
- zeta(2) <1,w>_Q = zeta(2) <r_Q,B r_Q>_Q + ||d||_P^2;
- `witness_mean_eq_residual_energy_difference` gives the second equality of
  (4.5), zeta(2) <1,w>_Q = zeta(2) ||r_Q||_Q^2 - ||r_P||_P^2;
- zero witness mean forces r_Q = 0;
- d = Pi_Q(B r_P) = Pi_Q(B r_Q) + Pi_Q(B d).

The exact positive energy terms are retained.

### Reversed metric expansion and the remaining projected residual

Source: the user's simultaneous D/R expansion argument, 6 November 2026.
Here the source name B still denotes the reciprocal multiplier R(n)=1/(n+1);
it does not denote the invertible metric operator A* A.

The new module RH/QReciprocalMetric.lean constructs Df(n)=f(n)/n as a bounded
linear operator, retaining the anchored coordinate at zero. It proves

- D - B D = B;
- <Df,g>_P = zeta(2) <Bf,g>_Q;
- <f,g>_Q = (<f,g>_P + <Df,g>_P)/zeta(2).

For the actual full-conductor displacement, RH/QFullDisplacement.lean adds

- displacement_swapped_normal_equation:
  <D r_Q,v>_P = <d,v>_P for every v in the full legal closure;
- displacement_p_energy:
  ||d||_P^2 = zeta(2) <d,B r_Q>_Q;
- displacement_eq_zero_iff_projected_residual_eq_zero:
  d=0 iff Pi_Q(B r_Q)=0.

These are exact identities and an equivalence. They do not prove that d or
the projected reciprocal residual vanishes. Combining the two metric
expansions retains the positive displacement energy; setting the cross term
to zero would add the unresolved hypothesis.

The coherent source candidate passed job job_IFOy2iaN-CHmzokn9q6rEs7aaR2fadxc:
verified=true, exit code 0, server-reported 7.148 seconds. Its two principal
axiom reports contain only propext, Classical.choice, and Quot.sound.
This isolated check is distinct from the final project checkpoint.
The initial candidate had a rewrite-direction error and an incomplete
positivity tactic; both were repaired before this successful check.

Open: establish Pi_Q(B r_Q)=0 using additional arithmetic information, or
supply a bounded full-legal family v_j with B v_j -> B 1. Infinite CRT
coordinate approximation alone does not supply that Hilbert norm bound.

### Reciprocal invariance is an RH-strength hypothesis

Source: the user's positive-square-root/invariant-subspace question,
6 November 2026. The operator called R in the discussion is still named
QShiftedReciprocal.B in the source.

- displacement_eq_zero_iff_reciprocal_mem proves d=0 iff B d belongs to V.
- riemannHypothesis_of_reciprocal_displacement_mem concludes RH from that
  target-specific membership.
- riemannHypothesis_of_reciprocal_invariant concludes RH from B(V) subset V.

The proof retains the exact energy:
||d||_P^2 = zeta(2) <B d,r_Q>_Q.
If B d is legal, residual orthogonality makes this energy zero.

These are conditional research reductions. The membership and invariance
hypotheses remain Open; positivity and existence of a positive square root
do not establish them. No RH-to-density converse is newly formalized here.

The coherent candidate passed job job_RHEXto2B-em3eZmXeaMr7iN5n_yzkbUK:
verified=true, exit code 0, server-reported 33.074 seconds. The audited
declarations use only propext, Classical.choice, and Quot.sound.
This is an isolated source check, distinct from the final project checkpoint.

### Reciprocal compactness argument: checked limits and the missing defect bound

Source: the user's approximation/compactness argument, 6 November 2026.
New module RH/QFullReciprocalLimits.lean uses the actual full-conductor
displacement and the reciprocal operator QShiftedReciprocal.B.

- G_M -> d implies B G_M -> B d; B qOne is nonzero.
- B commutes with an orthogonal projection iff the subspace is B-invariant.
- Commutation at d is equivalent to d=0.
- d=0 iff B G_M - Pi_Q(B G_M) -> 0 for any G_M -> d.
- ||d||_P^2 <= zeta(2) ||r_Q||_Q
  (||B G_M - Pi_Q(B G_M)||_Q + ||G_M-d||_Q/2).
- Every reciprocal orbit converges to zero at rate 2^(-k), including an
  explicitly exhibited nonzero vector with nonzero first image.
- Full projection commutation, or the extra zero-defect limit, implies RH.

The new source does not prove the reciprocal operator compact in Lean.
Its compactness is an elementary paper result via finite-rank truncations,
and would not make its strong limit zero. The missing estimate concerns
the distance of B G_M back to V, not merely the norm or convergence of B G_M.

The coherent extended candidate passed job
job_M1rbJ2q8K8x_LwEBY_BvOQD5FZCxtxjV: verified=true, exit code 0,
22.802 seconds. All four audited declarations use only propext,
Classical.choice, and Quot.sound. This is an isolated source check;
publication uses a separate final project checkpoint. An earlier
triangle-inequality API error was repaired before this successful check.

### Isometric transport of distances, projections, and the RH defect

Source: the user's question comparing dist_Q(R G,V) with dist_P(G,A V),
6 November 2026. The cross-space isometry A is physical multiplication by
sqrt((n+1)/(zeta(2)*n)); it is not the sequence-preserving toPareto map.

RH/QParetoIsometricTransport.lean proves the physical formulas for A and
its inverse, then specializes Mathlib's isometry-distance and projection API:

- dist_Q(R G,V) = dist_P(A R G,A V);
- dist_P(G,A V) = dist_Q(A inverse G,V), with G the same physical sequence;
- Pi_(A V)^P = A Pi_V^Q A inverse;
- the transported projection defects have exactly the same norm.

RH/QFullIsometricTransport.lean retains the actual all-conductor closure.
The Q target 1 transports to A(1), not to the physical constant target 1.
For G_M -> d it proves d=0 iff the P projection defect of A R G_M from A(V)
tends to zero, and derives the conditional RH implication.

Open: prove this transported defect tends to zero for actual legal
approximants. The isometry does not identify A(V) with the original physical
V, does not identify the two original projections, and does not establish RH.

The coherent candidate passed job job_swWmStRRX9ZKVjzjs6UprHl9D1vWaCcX:
verified=true, exit code 0, 11.252 seconds. Four audited declarations
(the physical A formula, reciprocal distance transport, projection conjugacy,
and conditional RH implication) use only propext, Classical.choice,
and Quot.sound. The final project checkpoint separately validates the
persisted module split and imports.

### Exact errors and localized integer tests (agenda A2–A3)

`RH/QMobiusFloorError.lean` gives the actual Q defect's complete signed
floor expansion, including physical site zero, and its exact finite
Mertens hyperbola identity on and beyond the head. It reuses the proved
finite arithmetic identities rather than assuming a new Mertens provider.
The conductor-(N+1) correction is retained with its original sign.
The exact head and its full legal membership are already in
`QMobiusExactHead.exactHead_exact` and
`QMobiusExactHead.exactHead_mem_legalSpan`.

`RH/QFullLocalResiduePairing.lean` proves complete HasSum pairings against
every full annihilator and specializes the localized signed-charge estimate.
Its residue probe is any integer m > Y. Neither primality nor squarefreeness
of N+1 is required. The head cutoffs Y <= X and both complete absolute
charge tails remain explicit. The cheaper sign can be chosen independently.

### Cofinal harmonic criterion for the actual full displacement (agenda A4)

`RH/QFullCofinalHarmonic.lean` defines

H(X) = min_{sigma = +/-1} sum_{1 <= n <= X} max(sigma*d(n),0)/n.

It proves the following exact residual equivalence:

r_Q = 0 iff there exist B,C >= 0 with
H(X) <= C * (log X)^B at arbitrarily large integer X.

`riemannHypothesis_of_cofinal_harmonic_polylog` concludes Mathlib's
RiemannHypothesis from that explicitly stated harmonic budget.
There is no bounded-gap restriction. The sign may change at each cutoff.
No RH-to-natural-approximation converse provider is an input.

The proof uses the already checked generic charge theorem for an arbitrary
squarefree annihilator, after proving inclusion of the smaller dictionary
in the full one. A full annihilator annihilates the smaller dictionary.
The displacement and both projections remain the full-family objects;
they are never replaced by the squarefree displacement.

The module also proves r_Q = 0 iff d = 0, and, if r_Q is nonzero,
H(X)/(log X)^B tends to infinity for every fixed real B >= 0.
These are conditional reductions, not a proof of the actual harmonic budget.

### Optimal lower and upper floor-dilation constants

`RH/QFloorDilationSharpBounds.lean` defines

c_m = sum_{0 <= r < m} 1/(m+r)^2.

For every positive integer m and every f in the actual ambient Q Hilbert
space it proves

c_m ||f||_Q^2 <= ||T_m f||_Q^2 <= ||f||_Q^2/m.

`floorDilation_lower_bound_iff` characterizes every global lower energy
constant: a real c works for all f iff c <= c_m. The minimum ratio is
attained by the physical unit spike at site one.
`floorDilation_opNorm_eq_sharp` proves ||T_m|| = sqrt(1/m).
Unit spikes escaping to infinity give sharpness of the upper constant.
Together with the supplied strict theorem, the operator norm is unattained
by any nonzero f for m > 1. Injectivity is also proved.

These are ambient operator statements. They do not assert that the unit
spikes are legal, or that a legal projection error vanishes.

### Verification and computational evidence

- The supplied five declarations and the new full witness were freshly
  audited in job `job_4beldPE69GAVf4GimzRA6-uvxPQczirN`:
  verified=true, exit code 0, server-reported elapsed 193.156 seconds.
- The sharp bounds, local full pairing, and full cofinal RH implication
  passed job `job_S-BrAmRfbx_w1fB-tweiQaYohWQAP_iu`:
  verified=true, exit code 0, server-reported elapsed 473.615 seconds.
- The final added-source import and axiom audit is recorded in
  `job_u31l_NtZe4_VHb8pgEunXAGo1nQXB15u`: verified=true, exit code 0, server-reported elapsed 373.221 seconds.
- Axiom reports for the audited principal declarations contain only
  propext, Classical.choice, and Quot.sound. The harmonic bound in the
  theorem type remains an explicit substantive hypothesis.
- The archive's 22,214-byte QFloorDilationEnergy.lean matches the repository
  byte-for-byte; SHA-256:
  dfb5eec77fb528c976e71da3743d9b175885c35752a99e0e7c1503791360a82a.
- All nine archived numerical rows were reproduced exactly with the
  supplied NumPy/SciPy script. Maximum absolute discrepancy: zero.
  They remain double-precision diagnostics, not interval or Lean certificates.
- Wolfram independently evaluated the new lower constants for m=2,...,6;
  for example c_2=13/36. These computations support the formulas but do not
  replace the kernel proofs of the general statements.
- An initial 180-second import audit timed out; subsequent successful jobs
  supersede it. Temporary tactic and import errors were repaired.
  Request/transport time and the 60-second polling intervals are not kernel
  execution measurements. Workspace-opening latency was not separately
  measured. Final publication still requires the mandatory changed-source
  and aggregate-project checkpoint.

### What remains open

This does not complete the manuscript's sixty-task research agenda.

- A6 / J2 / J4 / J6: no bound on the actual full displacement's product
  distance, cheaper harmonic sign, or complete legal approximation error
  is established. Such a bound would finish an RH route.
- The manuscript's raw Ramanujan density proof, integration-space
  construction, and categorical full p-adic CRT isomorphism are not newly
  certified by this continuation.
- The analytic RH-to-natural-approximation provider remains open where
  existing iff packages take it explicitly. Nothing here silently
  discharges that provider.
- The L^(8/7) approximation input for the eighth-moment route is not supplied.
- Reproduction of a floating-point Gram solve is not an outward-rounded
  complete-Gram certificate.

For further work on A5, its paper argument can be simplified before
formalization: bound the cross term
m <B r_P, d g_m>_Q uniformly by ||r_P||_Q ||d||_Q, since
(n mod m)/(n+1) <= 1. For the finite-liminf polylogarithmic criterion this
uniform bound suffices; its convergence to zero is unnecessary.
The remaining steps are the actual full product-distance pairing and a
finite weighted Cauchy bound converting it to H(m-1), followed by A4.
This simplification is a paper observation, not a newly checked theorem.

More explicitly, put eta_m = dist_Q(d g_m,V) and
h_{m-1} = sum_{1 <= n < m} 1/n. For m >= 2 the paper calculation gives

4 H(m-1)^2 <= zeta(2) h_{m-1}
  (||r_P||_Q ||d||_Q + m ||w||_Q eta_m).

The nonnegative complete residue energy is bounded above by the bracket
using the exact witness pairing; its head bounds H by weighted finite
Cauchy-Schwarz. A cofinal bound m eta_m = O((log m)^k) would therefore
supply H(m-1) = O((log m)^((k+1)/2)) and feed the checked A4 theorem.
The finite estimate and this product-distance assembly are not yet
kernel-certified.

## Crossed distances and square-root correction: November 6 continuation

Source: Isometric_Transport_Lean_Handoff_2026-11-06.md, Section 5 and
priorities 1--5. Detailed statements and remaining obligations:
RH/CrossedDistanceContinuation20261106.md.

### Established identities and quantitative estimates

Three new modules: Analysis/OrthogonalDistanceBound,
RH/QParetoSquareRootEnergy, and RH/QFullCrossedDistances.

Let T=A^{-1}I, q(f)=<f,Tf>_Q, a(g)=dist_P(Ag,V_P),
b(g)=dist_P(Ig,A V_Q), and Delta(g)=||r_P||_P a(g)+||r_Q||_Q b(g).
Every displacement declaration uses the actual full-conductor residuals.

- signedTest_eq: F(g)=<Ir_P,Ag>_P-<r_Q,Tg>_Q=<d,Tg>_Q.
- inverseEnergy_lower/upper: sqrt(Z/2)||f||_Q^2 <= q(f) <= sqrt(Z)||f||_Q^2.
- two_distance_bound: sqrt(Z/2)||d||_Q^2 <= Delta(d).
- two_distance_trial_bound: the handoff's full linear approximation penalty.
- inverseEnergy_polarization: q(d)+q(g)=2F(g)+q(d-g), retaining all terms.
- quadratic_two_distance_bound:
  sqrt(Z/2)||d||_Q^2+q(g) <= 2 Delta(g)+sqrt(Z)||d-g||_Q^2.
- displacement_eq_zero_iff_crossed_membership:
  d=0 iff both Ad in V_P and Id in A V_Q.
- inversePhysical_square: T^2=Z(1-R).
- displacement_eq_zero_iff_second_inverse_mem: d=0 iff T^2d in V_Q.
- rootDefect=J=1-T/sqrt(Z), with its exact coordinate multiplier.
- rootDefect_norm_le_of_head_zero:
  ||Jf||_Q <= ||f||_Q/(2N+3) when the first N positive coordinates vanish.
- two_distance_head_certificate: explicit legal-correction certificates
  for a shared J-transformed head target, retaining the infinite remainder.

### Conditional research reductions

For G_M -> d, the combined budget and signed-test zero limits are each
equivalent to d=0. The RH implications conclude Mathlib RiemannHypothesis
from the corresponding explicit provider.

- Open: vanishing of both actual crossed distances, or their combined budget.
- Open: signed-test cancellation F(G_M)->0.
- Open: second-inverse membership T^2d in the full legal closure.
- Open: actual legal corrections with vanishing complete J-target errors.

No global invariance, first-inverse-to-second-inverse shortcut, or RH
conclusion without these providers is asserted.

The assembled modules and seven principal axiom reports passed
job_Odin6V3Y3pnftimYSpdTePhqM2miJeiF (verified=true, exit 0,
server-reported 20.679 seconds). Reports contain only propext,
Classical.choice, and Quot.sound. Publication additionally uses the
mandatory aggregate and changed-module checkpoint.

## Compact square-root corrections and explicit Gram fits: November 6 continuation

Source: CrossedDistanceLeanHandoff20261106.md. Detailed account and remaining
providers: RH/CompactCrossedCorrectionResearch20261106.md.

### Established

- QParetoSquareRootEnergy: exact rationalization of the J coefficient;
  rootDefect_norm_le_of_head_zero and both head certificates are strengthened
  from denominator N+2 to 2N+3, retaining every infinite tail term.
- QFullCrossedDistances: for legal g, a(g)=dist_P(A Jg,V_P) and
  b(g)=sqrt(Z) dist_Q(Jg,V_Q), with no identification of A(V_Q) with V_P.
- QParetoSquareRootCompactness: finite-rank J_N, operator error <=1/(2N+3),
  IsCompactOperator J, and bounded coordinatewise/weak convergence giving
  strong convergence JG_M -> Jf. The limit is not asserted to vanish.
- QFullCorrectionCertificates: both full inverse-Gram corrections,
  exact Schur values and completion identities, finite target pairings,
  and explicit matchedApprox N defined by two finite solves with target 1.
  matchedApprox_tendsto proves convergence to the actual full displacement.
- matched_head_certificate instantiates the complete strengthened certificate
  with those approximants and both optimal finite corrections.
- optimized_correction_budget_tendsto gives the actual crossed-budget limit
  for fixed legal targets; it does not give a zero-limit provider.

### Conditional research reductions

- QFullCompactCrossedDistances: legal norm-bounded approximants with coordinate
  limit d suffice for the budget-decay iff and RH implication.
  Open: vanishing of their complete crossed budget.
- QFullCrossedDistances: weak convergence determines the signed-test limit;
  an independently justified nonpositive limit implies d=0 and RH.
  Open: the arithmetic signed nonpositive-limit provider.
- Open: cofinal full correction-error decay, and T(Td) membership in V_Q.
  Compactness and finite-head matching do not discharge either condition.

Assembled-module verification and nine axiom audits succeeded in
job_M5yiY2OyEf3aD5ELvT--00J40dERKUWb (verified=true, exit 0,
server-reported 24.999 seconds). Only propext, Classical.choice, and
Quot.sound occur in those reports. Final publication additionally requires
and uses the source-audited aggregate checkpoint.

## Weak-star finite-head compactness and reciprocal residual-tail costs

Source: the user's weak-star compactness request, November 6, 2026.
Detailed proofs, exact hypotheses, and the remaining arithmetic tasks are in
RH/WeakStarReciprocalHeadResearch20261106.md.

### Established

- Analysis/BoundedWeakInterpolation transports Banach--Alaoglu through Riesz:
  a bounded sequence in a complete separable subspace has an ambient weak
  subsequence with limit in the same subspace and norm ball. Bounded finite
  feasibility of countably many linear tests is equivalent to simultaneous
  bounded feasibility. A continuous-linear-image coordinate version is included.
- QFullResidueProjection now explicitly exposes completeness and separability
  of the actual all-conductor legal closure.
- QFullHeadObstruction.mem_closure_iff_bounded_exact_heads: x belongs to the
  full closure iff all its finite heads admit finite legal interpolants with
  one uniform complete Q-norm bound. The reverse uses weak-star compactness.
- exists_finite_head_norm_obstruction supplies a finite dual witness for any
  proposed norm bound when x is outside the closure. Every increasing-head
  legal interpolation family then has norm tending to infinity.
- QFullReciprocalHeadTail.reciprocal_head_energy_identity: for a legal F_N
  matching the first N coordinates of R d,
  ||I d||_P^2 = Z <R d-F_N,r_Q-H_N r_Q>_Q, retaining both complete factors.
- residual_tail_norm_tendsto_zero is unconditional.
- reciprocal_head_norm_lower: if d is nonzero, tau_N=||r_Q-H_N r_Q|| is
  positive whenever such a repair exists, and
  ||F_N|| >= ||I d||_P^2/(Z tau_N) - ||R d||.

### Conditional research reductions

- displacement_eq_zero_iff_bounded_reciprocal_heads: d=0 iff all finite heads
  of R d admit uniformly bounded finite legal repairs. The consequent RH
  theorem leaves that norm bound explicit and Open.
- reciprocal_head_norm_tendsto_atTop: nonzero actual full displacement forces
  every such family of repair norms to tend to infinity.
- riemannHypothesis_of_repair_norm_tail_product permits unbounded repairs:
  ||F_N|| tau_N -> 0 suffices. The complete-error product criterion also suffices.
  Open: either product-decay estimate for the actual reciprocal-head repairs.
- QFullWeakHeadCorrections: uniformly bounded finite-head corrections h_N,k_N
  satisfying H_N T h_N=H_N Jd and H_N k_N=H_N Jd force d=0 and RH.
  Open: both uniform full-norm bounds. No identification of A(V_Q) with V_P
  or global reciprocal invariance is assumed.

The combined candidate containing all 28 new theorem declarations passed
job_G9PUjB9eFP-jR0EXaLsITvbe2D9crKOJ (verified=true, exit 0, 9.201 seconds).

The persisted modules and nine axiom audits passed
job_CN-XP_8VlGeCnueN-51fITbhAeY-q23n (verified=true, exit 0, 154.211 seconds).
Only propext, Classical.choice, and Quot.sound occur in those reports.
Publication additionally uses the mandatory source-audited aggregate and
changed-module checkpoint. RH and every actual norm/product provider remain Open.
