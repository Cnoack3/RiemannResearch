# Bilinear mean extension and mixed-conductor Rank 1

Date: November 24, 2026.
Module: `RiemannResearch.RH.MixedConductorBilinear`.
Namespace: `RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear`.

## Scope and notation

Work in the real Pareto Hilbert space `ThresholdHilbert`.
Let `V = CoefficientStabilization.closedSpace`,
`M = mixedClosure`, `e = hilbertOne`,
`S = fullScreening = I - P_M`, and `u = normalizedScreenedTwo`.
The mixed conductors are those having at least two distinct prime factors;
they include nonsquarefree mixed conductors. They are not all composite conductors.

The mean is `hilbertMeanContinuous x = inner ℝ e x`.
Its restriction to V is `legalPacketMean`, with the equivalent real-inner-product
ordering `inner ℝ x e`. On M orthogonal, the distinct coefficient functional is
`mixedPacketCoefficient h = inner ℝ u h`. The restricted mean there is
`mixedOrthogonalMean`. No equality between these last two functionals is assumed.

## Direct-sum extension

- `directSumAssembly`: the continuous linear addition map from M orthogonal × M to H.
- `directSumMean_apply`: the mean of h + m is the mean of h.
- `directSumForm`: the ambient inner product pulled back through direct-sum assembly.
- `directSumForm_apply`: its two diagonal blocks are the inner products on the summands.
- `directSumForm_one`: evaluation against (e, 0) recovers the original mean.
- `mixedPairing_eq_zero`: the cross-pairing M orthogonal × M vanishes.

The cross-pairing alone contains no Rank 1 information.

## Independent factorization from arithmetic rigidity

`pairing_factorization_of_rigidity` proves, for h in M orthogonal and v in V,

    inner ℝ h v = inner ℝ u h * inner ℝ v e.

The proof calls the previously proved arithmetic lemma `residuePairing_eq_log`.
It constructs the closed linear subspace on which the pairing with h equals a
scalar multiple of the mean, verifies membership for each residue generator,
and extends to the closed span V. Evaluating at the independently known legal
mean-one vector u identifies the scalar with `inner ℝ u h`.

This proof does not call the existing geometric Rank 1 conclusions.
In particular, it does not assume `fullScreening_eq_mean_smul`, u = e, vanishing
limiting energy, density of V in H, or the Riemann Hypothesis.

- `legalPairing_eq_rankOne`: equality of continuous bilinear maps,
  `legalPairing = mixedPacketCoefficient.smulRight legalPacketMean`.
- `legalPairing_one_seed` and `legalPairing_ne_zero`: the pairing evaluates to one
  at the constant and the legal mean-one seed, and is therefore nonzero.
- `legalPairing_range`: its range is precisely the one-dimensional line spanned
  by the legal mean functional.
- `screening_factorization`: equality of continuous linear maps,
  `fullScreening.comp closedSpace.subtypeL =
  legalPacketMean.smulRight normalizedScreenedTwo`, recovered from that pairing.
- `legalPairing_right_radical`: a vector v in V pairs to zero with every h in
  M orthogonal exactly when v belongs to M.
- `legalPairing_left_radical`: a vector h in M orthogonal pairs to zero with
  every v in V exactly when h belongs to V orthogonal.

## Fekete slopes and screened prime powers

In `RiemannResearch.NumberTheory.FeketePowerSlope`, `lowerIncrement_fekete`
identifies the limiting normalized lower increment with its supremum over
positive lengths. The upper limit is the corresponding infimum. The two
limits use their respective boundedness hypotheses.

`tendsto_powerRate` gives exponent convergence for a subadditive exponent
sequence whose normalized values are bounded below. Under these hypotheses
`powerRate_pow` gives the positive-power reindexing law. With coprime
additivity and the same hypotheses on each of two positive coprime bases,
`powerRate_mul_of_coprime` gives the sum of their rates at the product base.
For logarithmically rigid functions `pow_div_exponent_of_log` gives the
exact ratio at every positive exponent, and `powerRate_div_log_eq_of_log`
recovers the common coefficient at every base greater than one.

For the residue pairing of a vector h in M orthogonal,
`mixedPacketCoefficient_eq_fekete_rate` and `pairing_eq_fekete_rate_at_base`
identify that coefficient with R(h) and give the legal pairing at any base.
`prime_pow_packet_pairing_eq_powerRate` identifies the pairing with every
positive prime-power packet with the rate at the prime base itself.
`fekete_screened_prime_pow` gives S(J_(p^k)) = (log p) u.
`fekete_normalized_screened_prime_pow_set` gives the literal singleton {u}
for normalized screened packets with k ≥ 2. Conductor four realizes u.

## Exact symmetric defect form

Definitions:

    meanProduct x y = C(x) * C(y)
    screenedForm x y = inner ℝ (S x) (S y)
    defectForm x y = screenedForm x y - meanProduct x y
    centeredScreening x = S x - C(x) • e

- `mean_fullScreening`: screening preserves the mean.
- `centeredScreening_mem`: the centered screened vector lies in
  `ambientMixedMeanKernel = M orthogonal ∩ span{e} orthogonal`.
- `centeredScreening_eq_starProjection`: centered screening is precisely the
  orthogonal projection onto that closed subspace. This proof does not use Rank 1.
- `defectForm_eq_inner`: the defect form is the inner product of the centered
  screened vectors.
- `defectForm_self_eq_norm_sq`, `defectForm_nonneg`, `defectForm_symm`:
  exact squared norm, nonnegative diagonal, and symmetry.
- `centeredScreening_legal`: on V, centered screening is C(v) times (u - e).
- `screenedForm_legal`: on V × V, the screened form is
  norm(u)^2 * C(v) * C(w).
- `defectForm_legal`: on V × V, the defect form is
  norm(u - e)^2 * C(v) * C(w).
- `defectForm_normalizedScreenedTwo`: evaluating the defect form at (u, u)
  returns norm(u - e)^2.

## Exact remaining endpoint

- `defectForm_vanishes_iff`: the defect form vanishes on V × V if and only if u = e.
- `legalPairing_eq_meanProduct_iff`: replacing the coefficient functional R by
  the mean C in the mixed-orthogonal/legal pairing is equivalent to u = e.
- `riemannHypothesis_of_defectForm_vanishes`: RH follows conditionally from
  vanishing of the defect form on V × V.

The last theorem has an explicit substantive hypothesis. No unconditional
vanishing of the defect, equality u = e, or unconditional RH result is supplied.

## Stage lifts, dilation Gram matrices, and the unit norm

The module `RiemannResearch.RH.CenteredMeanUnitNorm` uses the actual centered snake for every mixed denominator, including each prime-support stage. The finite determinant tests use the complete Pareto Gram matrix. Its conductor cutoff is independent of the choice of stage in the snake.

- `stage_polarization_defect` computes the bilinear defect of two legal vectors by subtracting the squared boundary norms of the sum and difference of their means.
- `screened_power_dilation_gram` gives the exact nested dilation pairing at every positive integer base. At base p and exponents i ≤ j its value is p^i times the squared norm of u.
- `screened_norm_sq_gram_cut` characterizes the lower cut of the squared norm. A scalar t belongs to the cut exactly when every finite determinant det(G_n − t Λ_n Λ_nᵀ) is nonnegative.
- `stage_lift_unit_norm_tfae` identifies injectivity of the outgoing cokernel map, existence of a unique kernel lift of 1, the bound ‖u‖ ≤ 1, the equality u = 1, and RH. The proof chases exactness on both sides of the connecting map.
- `unit_norm_iff_finite_gram_halving` characterizes the unit bound by a finite extension problem. Write a_n = Λ_nᵀ G_n⁻¹ Λ_n for n ≥ 1. For each such n there must be an m with det(G_m − ((1 + 1/a_n)/2) Λ_m Λ_mᵀ) < 0. The determinant identity turns this sign into 1/a_m − 1 < (1/a_n − 1)/2. Its strictness forces m > n by monotonicity of a_n.

**Open.** Construct a finite extension satisfying that inequality for every nonempty starting dictionary. The five proved declarations give identities and equivalences. They leave this arithmetic existence statement, ‖u‖ ≤ 1, and RH open.

## Verification record

The managed checkpoint receipt is the source of truth for the final publication
SHA, Bazel/BuildBuddy job ID, source audit, and full-project validation.
