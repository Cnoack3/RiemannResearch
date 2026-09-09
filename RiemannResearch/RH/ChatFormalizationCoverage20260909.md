# Chat-to-Lean formalization: Gibbs dynamics and arithmetic repair

9 September 2026

The development adds 54 subject modules to `RiemannResearch`. It formalizes
the actual infinite Gibbs operator, proves its exact mean-zero norm is
\(\pi/4\), proves unconditional convergence of its iterates, and connects
vanishing arithmetic repair errors to convergence in the full legal closure.
It also supplies full wavelet estimates, exact transform identities, and
general arithmetic obstruction results.

This is not a proof of RH. Open constructions are recorded as explicit
propositions, with conditional consumers where available. Defining a
proposition checks its statement; it does not prove it. Some subsidiary
ordinary claims still lack either a proof or a dedicated Lean statement;
the detailed coverage tables identify them. Numerical research diagnostics
are not presented as formal certificates.

## Publication and verification

The complete 54-module combined source passed Lean verification:

- Job: `job_mkFKK4Knr6rEkteer7R24zrmy04V6g5J`; `verified: true`, exit code 0.
- Compiler time: 19.114 seconds.
- Combined-source SHA-256: `8f46da738e3e6bdc23f95d77daa1ff31101e3091677edb35daec292f54606874`.
- The actual norm, strong convergence, step isometry, no-lower-Riesz result,
  legal-wavelet closure, and conditional RH consumer passed endpoint axiom audits.
- A separate 10-module arithmetic check passed with six clean endpoint audits.

Native module compilation and source audit are enforced by the publication
checkpoint before this change is published. The combined source uses ephemeral
linter settings solely to keep diagnostics readable. The published proof files
retain their normal imports and settings.


The submitted sources contain no `sorry`, `admit`, new axioms, or unsafe
declarations. Selected endpoint dependency audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. This axiom check does not erase explicit
hypotheses: the RH consumers still require their stated open arithmetic and
analytic inputs. Proof files retain ordinary module imports; source inlining
was used only for isolated verification.

The previous period-2520/5040 certificates and general fixed-component
obstructions were already published at commit
`36ff009985eb1d16298b6c47c63aa29f378dee49`. They are preserved and are not counted
as new results here.

## Principal completed results

For physical coordinates \(n\ge0\), use
\[
w_n=\frac1{(n+1)(n+2)},\qquad
P_{nm}=\frac{2(n+1)(n+2)}{(n+m+1)(n+m+2)(n+m+3)}.
\]
The operator is built on the actual complete weighted Hilbert space.

1. **Exact infinite dynamics.** The kernel is reversible, positive, mean
   preserving and contractive. The full Dirichlet and conditional-variance
   identities include all infinite terms. Its fixed vectors are constants,
   and \(P^n f\to\langle f,1\rangle1\) for every Hilbert vector.
2. **Exact optimal mean-zero norm.** An actual orthonormal tail basis has
   closure \(1^\perp\). Its full operator matrix is
   \[
   C_{nm}=\frac{2(n+1)(m+1)}{(n+m+1)(n+m+2)(n+m+3)}.
   \]
   Gamma-weighted Schur bounds prove \(\|P|_{1^\perp}\|\le\pi/4\).
   Truncated Gamma vectors have unbounded squared norms and uniformly bounded
   Rayleigh defects, proving the matching lower bound. The resulting Lean
   theorem is `hilbertGibbsMeanZeroContinuous_norm`. No external spectral
   theorem or RH premise is assumed. This does not identify the full spectrum.
3. **Infinite legal wavelet closure.** Telescoping expansions with complete
   geometric tails prove that the wavelet closure equals the actual legal
   closure. Binary wavelets have exact squared norm \(\pi/(4m)\) and mean
   \(\log2/(2m)\). Full signed Gram estimates and adjacent-pair limits rule
   out a positive uniform lower Riesz bound for the raw normalized family.
4. **Repair convergence.** For finite legal mean-one vectors, the actual
   errors \(e_n=F_{n+1}-PF_n\) tending to zero suffice for \(F_n\to1\);
   summability of the errors is unnecessary. The exact mixed energy and
   geometric convolution estimates are retained. Existence of such a legal
   orbit is equivalent to \(1\) belonging to the full legal closure.
5. **Actual integral and transform identities.** Weighted square summability
   implies integrability and the full step-function identity
   \[
   \int_1^\infty\frac{f(\lfloor x\rfloor)^2}{x^2}\,dx
   =\sum_{k\ge1}\frac{f(k)^2}{k(k+1)}.
   \]
   General logarithmic means and the actual geometric transforms of legal
   residue generators and wavelets are proved.
6. **General arithmetic obstructions.** The actual totient jump row yields
   the full-error floor \(2/((A+4)(4B+9))\) for every \(A,B>0\) in the stated
   conductor class. The bounded-number repair obstruction and full
   distributed error completion are proved with their precise balance and
   disjointness hypotheses. Finite balanced component synthesis is genuinely
   legal.

## The remaining mathematical step

The central open construction is `GibbsArithmeticRepairTarget`: produce
finite legal mean-one approximants whose actual full Gibbs repair errors
tend to zero. Neither spectral contraction nor pairwise wavelet decorrelation
constructs this orbit. The analytic tail basis used to prove the gap is not
claimed to lie in the arithmetic legal space.

The separate `ThresholdRiemannHypothesisBridgeTarget` records the actual
approximation-to-RH identification. The theorem
`riemannHypothesis_of_gibbs_repair` proves the implication from those two
explicit inputs; it is not an unconditional proof of RH.

The most useful next work is to prove the actual step-function Mellin bridge
and to seek a legal repair estimate that controls full tails across nearby
dilation blocks. The no-lower-Riesz theorem rules out relying on a uniform
inverse estimate for the raw wavelet family. A block construction must retain
the signed cross terms and quantify its coefficient growth.


# Detailed analytic coverage

Audit of `RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md` and the related `analytic_gibbs_method.md`, against the current Lean sources. Equation numbers refer to the main report. This is a coverage ledger, not an assertion that every ordinary derivation in those notes has become a theorem.

**Status convention.** “Proved” identifies a theorem with a proof in the existing library or the current development. The named providers passed focused checks; the complete publication result is recorded at the start of this document. “Target” means only a definition of a proposition awaiting proof: it supplies no axiom, theorem, or usable provider. “Not yet formalized” means no exact theorem or named target was located in the audited sources. The publication record gives the final verification metadata.

Unless stated otherwise, theorem names are in `RiemannResearch.RH.Pareto`; module filenames lie under `RiemannResearch/RH`. `ThresholdHilbert` is the actual real Hilbert carrier. Index `n` in Gibbs modules represents the physical positive integer `n+1`.

## Operator, geometry, and spectrum

| Exact claim from the report | Lean coverage | Scope and status |
|---|---|---|
| Full weighted space `H`, unit constant, every positive integer dilation and signed two-seed legal span (§1) | Existing `ThresholdHilbertSpace`, `ThresholdHilbertMean`, `ThresholdHilbertDilation`, `ThresholdHilbertLegal`; `hilbertOne_norm_sq`, `hilbertLegalSubspace`, `hilbertLegalClosure` | Proved/defined on the actual Hilbert space. No finite conductor is substituted for the full legal closure. |
| Geometric probabilities have total mass one and Pareto marginal, (1) | `ParetoGeometricMixture.geometricProbability_hasSum`, `geometricProbability_integral`, `geometricProbability_product_integral` | Proved infinite sums and beta integrals. |
| The explicit infinite Gibbs kernel (2), positive entries, unit row sums, detailed balance (3) | `ParetoGibbsOperator.gibbsKernel_formula`, `gibbsKernel_pos`, `gibbsKernel_hasSum`, `gibbsKernel_detailed_balance`, `gibbsAction_eq_tsum` | Proved for the actual kernel. |
| `P` is defined on all of `H`, fixes constants, preserves means, and contracts | `ParetoGibbsOperator.gibbsAction_square_summable`, `gibbsAction_square_contraction`; `ParetoGibbsHilbert.hilbertGibbsContinuous`, `hilbertGibbs_norm_le`, `hilbertGibbs_one`, `hilbertGibbs_mean_inner` | Proved with weighted square summability, not merely bounded inputs. |
| Positivity and self-adjointness of `P` | `ParetoGibbsPositive.gibbsAction_pairing_nonneg`; `ParetoGibbsHilbert.hilbertGibbsContinuous_isSelfAdjoint`; `ParetoGibbsHilbertEnergy.hilbertGibbs_inner_nonneg` | Proved directly from the actual kernel and its beta Gram form. Does not rely on an unconstructed `T* T`. |
| Exact full Dirichlet identity (4), constant fixed space | `ParetoGibbsEnergy.gibbs_dirichlet_identity`, `gibbsAction_fixed_iff_constant`; `ParetoGibbsHilbert.hilbertGibbs_fixed_iff` | Proved, with full double-series convergence. |
| Exact squared-norm loss and strict loss for each nonconstant vector | `ParetoGibbsEnergy.gibbs_conditional_loss_identity`, `gibbsAction_square_eq_iff_constant`; `ParetoGibbsHilbertEnergy.hilbertGibbs_norm_lt_of_nonconstant` | Proved. Strict loss for each vector alone is weaker than a uniform spectral gap. |
| Strong convergence `P^n F → 〈F,1〉1`, (5) | `ParetoGibbsConvergence.hilbertGibbsIterate_tendsto` | Proved for every actual Hilbert vector, with no RH, legal-invariance, or gap hypothesis. The endpoint axiom audit contains only: `propext`, `Classical.choice`, `Quot.sound`. |
| Normalized matrix equals the displayed elementary specialization of `2B(1,1,3)` | `ParetoGibbsHankel.normalizedGibbsHankel_explicit`, `normalizedGibbsHankel_conjugation`; `ParetoGibbsHilbertEnergy.hilbertGibbs_matrix_hasSum` | Proved coordinate formula and actual convergent operator rows. The external weighted-Hankel spectral theorem itself is not imported as a formal theorem. |
| Mean-zero operator bound `‖P F‖ ≤ (π/4)‖F‖` | `ParetoGibbsSpectralGap.hilbertGibbs_meanZero_norm_le`, `paretoGibbsSharpGap` | **Proved.** The proof uses the actual orthonormal tail basis, its full operator matrix, Gamma-weighted Schur estimates, and density. `ParetoGibbsSharpGap` by itself is only the named bound proposition. |
| The constant `π/4` is optimal and the restriction has norm exactly `π/4`, part of (6) | `ParetoGibbsOptimality.hilbertGibbs_meanZero_lower_witness`, `hilbertGibbs_meanZero_optimal_constant_iff`, `hilbertGibbsMeanZeroContinuous_norm` | **Proved.** These are stronger claims than the upper bound. Do not label the upper-bound theorem alone an optimality theorem. |
| Full spectrum `σ(P)=[0,π/4]∪{1}`, including the continuous spectral interval and its type, (6) | `ParetoGibbsSpectrumTarget.paretoGibbsFullSpectrumTarget` | **Target only for the spectral set.** The exact norm theorem does not prove the whole spectral interval; multiplicity and absolute continuity are not represented by this target. |
| Actual continuous linear contraction `T:H→L²(0,1)`, adjoint integral formula, and `P=T* T` (§2) | `GeometricHilbertRealizationResearchTargets.GeometricHilbertRealizationTarget` | **Target only.** Existing bounded scalar transforms and actual full-H `P` do not yet constitute this full operator realization. |

## Means, repair, and logical dependence on RH

| Exact claim from the report | Lean coverage | Scope and status |
|---|---|---|
| Generator mean `〈g_{m,a},1〉=log a`, (7), for all positive integer dilations | `ParetoResidueLogMean.paretoMean_residue`, `paretoMean_digitSequence`; `DilationWaveletAlgebra.digitSequence_generator` | Proved exact full means in equivalent digit/residue form, with `g_{m,a}=m D_{a,m}`. The proof uses harmonic/Abel identities rather than the unproved logarithmic-derivative calculation. |
| Actual finite legal mean-one seed `F₀=g_{1,2}/log 2` | `GibbsLegalSeed.initialLegalMeanOne`, `initialLegalMeanOne_mean`, `initialLegalMeanOne_legal` | Proved for the actual legal space. Its unrestricted Gibbs iterates converge by (5); they are not asserted legal. |
| Actual repair error and mean-zero error, (8) | `Analysis.ContractiveRepair.repairError`, `repairError_mean_zero`, `centered_recurrence` | Proved generic identities; the error is defined as `F(n+1)-P(F n)`. |
| Full one-step energy with the mixed term, (9) | `Analysis.ContractiveRepair.exact_repaired_energy`; `ParetoGibbsRepair.hilbertGibbs_repair_energy` | Proved exact signed identity. |
| Full geometric convolution estimate (10), convergence from vanishing repair errors | `Analysis.ContractiveRepair.fixedPoint_error_le_geometricConvolution`, `tendsto_fixedPoint_of_vanishing_repair`; `ParetoGibbsRepair.hilbertGibbs_tendsto_of_vanishing_repair` | Generic result proved. Actual Gibbs consumer in `ParetoGibbsRepair` takes the explicit gap bound as a hypothesis; `ParetoGibbsSpectralGap.hilbertGibbs_repair_convergence` removes that hypothesis using the now-verified upper gap bound. Existence of suitable legal errors remains open. |
| Relative repair bound (11) yields rate `π/4+η` | `Analysis.ContractiveRepair.norm_le_pow_of_relative_repair`, `tendsto_zero_of_relative_repair`; `GibbsRelativeArithmeticRepairTarget` | Generic implication proved; existence of a legal orbit satisfying the bound is **target only**. |
| Legal mean normalization and its full error bound (§4) | `Analysis.MeanNormalization.normalize_mean`, `normalize_mem`, `normalize_sub`, `norm_normalize_sub_le_of_mean_norm_le_one`; `ThresholdContractiveRepair.hilbertMeanContinuous_norm` | Proved. No reconstruction is obtained from normalization alone. |
| Existence of vanishing-repair legal orbits is equivalent to target membership in the legal closure | `Analysis.ContractiveRepair.vanishing_repair_orbit_iff_mem_closure`; `ParetoGibbsRepair.hilbertGibbs_legal_repair_iff_closure`; unconditional specialization in `ParetoGibbsSpectralGap` | Generic, gap-conditional, and actual unconditional equivalences proved. This is a reduction, not a construction of an orbit. |
| `P` preserves the closed legal space | `GibbsArithmeticResearchTargets.GibbsLegalInvarianceTarget` | **Target only.** `hilbertOne_mem_legalClosure_of_gibbs_invariance` proves that this assumption already implies target membership, using unconditional strong convergence. |
| Actual arithmetic reconstruction with vanishing defect, (20) | `GibbsArithmeticRepairTarget`, `GibbsRelativeArithmeticRepairTarget` | **Targets only.** No explicit arithmetic reconstruction coefficient formula and no vanishing full-tail repair bound have been proved. The individual wavelet reconstruction with its specified coefficient/remainder formula is not separately formalized. |
| Closure criterion is equivalent to RH; legal repair therefore proves RH | `ThresholdRiemannHypothesisBridgeTarget`; `riemannHypothesis_of_gibbs_invariance`, `riemannHypothesis_of_gibbs_repair` | The RH bridge is **target only**. The named RH consumers explicitly require this bridge plus the relevant open arithmetic input. They are not proofs of RH. |

## Wavelets and exact analytic estimates

| Exact claim from the report | Lean coverage | Scope and status |
|---|---|---|
| Actual digits and wavelets, (12), period `a²m`, zero period mean | `DilationWaveletAlgebra.digitSequence`, `dilationWaveletSequence`, `dilationWaveletSequence_periodic`, `dilationWaveletSequence_period_sum_zero` | Proved. The zero period mean is not conflated with the nonzero Pareto weighted mean. |
| Exact step-function energy equality, (13) | `ParetoStepIsometry.paretoStepEnergy_integrable`, `paretoStep_energy_identity` | Proved for every weighted square-summable sequence, including integrability on `(1,∞)`. A continuous-linear isometry into an `Lp` carrier is not separately packaged. |
| Infinite dilation scaling and telescoping remainder, (14) | `DilationWaveletAlgebra.digitHilbert_norm_sq_scale`, `digitHilbert_wavelet_telescope`, `digitHilbert_wavelet_error_sq`; `ParetoResidueLogMean.binary_wavelet_error_sq_log` | Proved exact Hilbert identities. The finite-sum indexing uses `range N`; translate the report's sum through `N` accordingly. |
| Wavelets preserve the entire closed legal span | `DilationWaveletClosure.hilbertWaveletClosure_eq_legal`, `twoSeed_waveletClosure_eq_legal` | Proved for the actual closed Hilbert spans, retaining both seeds and all positive integer dilations. |
| Binary norm `‖W_m‖²=π/(4m)` and mean `log 2/(2m)`, (15) | `DilationWaveletBinaryNorm.binary_wavelet_hilbert_norm_sq`; `GibbsLegalSeed.hilbert_mean_binary_wavelet` | Proved full infinite norm and mean. |
| Primitive is triangular and bounded by `m` | `BinaryWaveletPrimitive.binaryWaveletPrimitive_bounds`, `binaryWaveletPrimitive_step`, `binaryWaveletPrimitive_eq_sum` | Proved for the discrete primitive. The continuous primitive is defined separately in the asymptotic targets module. |
| Full signed continuous integration-by-parts identity (16) | `DilationWaveletAsymptoticTargets.BinaryWaveletContinuousGramTarget` | **Target only for that exact continuous formula.** The full discrete signed identity is proved as `DilationWaveletOffScale.binary_wavelet_gram_abel`, with summability and vanishing endpoint discharged. These two formulas should not be silently identified. |
| Pairwise separated-scale decay (17) | `DilationWaveletOffScale.binary_wavelet_gram_bound_symmetric`, `binary_wavelet_hilbert_gram_bound` | Proved stronger unnormalized bound `|〈W_m,W_n〉| ≤ min(2m/n²,2n/m²)` for every positive pair. Combining it mathematically with (15) gives normalized constant `8/π`, hence the report's `12/π`; a separately named normalized-ratio theorem was not located. This is a pairwise result, not a whole block or Gram-operator bound. |
| Adjacent normalized wavelets approach one another; no positive uniform lower Riesz bound | `DilationWaveletNearbyEnergy.binary_wavelet_nearby_hilbert_energy_bound`; `DilationWaveletNoRiesz.normalizedBinaryWavelet_adjacent_tendsto_zero`, `normalizedBinaryWavelet_no_uniformLowerRiesz` | Proved along all positive integer dilations, with complete tail control and all finite signed coefficient families in the no-Riesz conclusion. |
| Sharp adjacent asymptotic `(6/π)(log m)/m+O(1/m)`, (17a) | `DilationWaveletAsymptoticTargets.BinaryWaveletAdjacentAsymptoticTarget` | **Target only.** The proved adjacent-pair limit does not establish this leading coefficient or remainder order. |
| Intermediate sharp-asymptotic identities: disjoint jump intervals, exact remainder, centered harmonic asymptotic, and normalization correction (§5) | Some support and rough energy bounds in `BinaryWaveletNearbySupport` and `DilationWaveletNearbyEnergy` | The report's complete sharp-asymptotic chain is **not yet formalized**. Its final asymptotic is recorded as the named target above. |
| Exact generator cyclotomic transform and binary wavelet transform (18) | `ParetoCyclotomicTransform.geometricTransform_residue_generator`; `ParetoWaveletTransform.geometricTransform_digitSequence`, `geometricTransform_dilationWavelet`, `geometricTransform_binaryWavelet` | Proved as actual infinite transforms, not candidate rational-function definitions. Includes arbitrary positive seed and dilation. |
| `Tg` equals the derivative of the cyclotomic logarithm (§4) | No exact derivative theorem located | **Not yet formalized.** The rational `Tg` formula and the mean `log a` are independently proved. |
| Explicit `PW_m` beta integral and bilinear `〈W_m,PW_n〉=∫b_m b_n`, (19) | Actual `P`, actual `b_m`, and bounded scalar squared-transform/kernel identity exist | The exact named wavelet integral identities are **not yet separately formalized**. The scalar quadratic ingredients are proved; full-H `T* T` remains a target. |
| Exact jump/divisor formula and nonzero logarithmic flux (23) | Existing `ParetoResidueDuality.residue_difference`; `ParetoCyclotomicTransform.geometricTransform_eq_jump_series`; `ParetoResidueLogMean.pareto_partial_abel`, `residue_pareto_partial_harmonic`, `paretoMean_residue` | Proved algebraic jump and harmonic/mean ingredients retain the boundary signal. The exact general cutoff identity and limit are **target only**, recorded as `ArithmeticFluxResearchTargets.ArithmeticGeneratorLogFluxTarget` using the actual residue-generator jumps. Do not describe formal cancellation of divergent sums as justified. |

## Variance, Mellin, and further claims from the notes

| Exact claim | Lean coverage | Scope and status |
|---|---|---|
| Total squared-transform and error accounting, (21) | Existing `ParetoGeometricTransform.geometricTransform_sq_integral`, `geometricTransform_full_energy`, `geometricTransform_full_error_identity` | Proved for bounded sequences with actual scalar integrals and the full nonnegative kernel double sum. The literal equality of that double sum with an integral of pointwise conditional variances is not separately proved here; full-H `T` remains a target. |
| Covariance derivative `f′(t)=Cov(F,K−1)/t` | `GeometricDifferentialResearchTargets.GeometricCovarianceDerivativeTarget` | **Target only**, including summability of the actual centered covariance series. This is an additional analytic identification beyond generic orthogonal projection algebra. |
| Differential regression variance with the actual derivative and squared residual, (22) | `GeometricDifferentialResearchTargets.GeometricDifferentialVarianceTarget`, using `geometricVariance` and `geometricRegressionResidual` | **Target only**, for bounded inputs and `0<t<1`. |
| Infinite Meixner Parseval expansion with derivative coefficients | `GeometricDifferentialResearchTargets.GeometricMeixnerParsevalTarget`, `geometricMeixnerCoefficient` | **Target only**, stated with `HasSum` for the full infinite expansion. A finite regression identity does not establish it. |
| Meixner generating function, orthogonality, and polynomial completeness | No corresponding formal Meixner system located | **Not yet formalized.** These are the missing proof ingredients behind the expansion target, not consequences of writing down its coefficients. |
| Mixed-radix digits are conditionally independent; exact carry-corrected martingale differences | No actual conditional probability/martingale realization located | **Not yet formalized.** The actual residue/digit algebra exists, but it is not a formal conditional independence or martingale theorem. |
| Two radix orders telescope to `R_(6m)-R_m` | Follows algebraically from actual residue-generator differences | No separately named carry-order theorem located. In any event this algebraic identity supplies no contraction or gain bound. |
| Actual legal step-function Mellin identity underlying (24) | `ArithmeticMellinResearchTargets.ArithmeticMellinIdentityTarget` | **Target only**, including integrability and actual equality on `0<Re(s)<1`. Existing `NymanConductorContinuation.nymanConductorLFunction_eq_conductorZeta` continues periodic Dirichlet data; it is not this actual step-integral bridge. |
| Full Mellin-Plancherel formula (24) | `ArithmeticMellinResearchTargets.ArithmeticPlancherelTarget` | **Target only**, with the integral over all real frequencies. No finite-frequency calculation substitutes for it. |
| Hypothetical off-line zero forces the positive lower bound on every finite legal vector | `ArithmeticMellinResearchTargets.ArithmeticZeroObstructionTarget` | **Target only** for `1/2<Re(ρ)<1`. A generic Cauchy–Schwarz or projection theorem alone does not identify the actual legal annihilator. |
| Exact residual projection identity (25) | `ArithmeticMellinResearchTargets.ArithmeticZeroProjectionTarget`, using the actual continuous `hypotheticalZeroMode` | **Target only.** The continuous mode is not silently treated as a discrete step vector. Its norm, target pairing, and legal-generator orthogonality remain analytic obligations. |
| Wavelet Mellin multiplier (26), removable value at one, and nonvanishing of the extra wavelet factor | No exact actual wavelet Mellin theorem or separate named wavelet multiplier target located | **Not yet formalized.** It should not be inferred from the formal rational geometric transform, which is a different transform. |
| Nearby-scale coherent reconstruction, uniform block estimates, admissible inverse coefficient geometry | No provider or proved bound | **Open research work.** The pairwise off-scale estimate and the no-lower-Riesz theorem constrain this problem; neither solves it. |
| Literature priority or novelty of the proposed combination | Bibliographic discussion in the source notes only | Not a mathematical Lean theorem. No priority claim is established by this development. |

## Remaining Mellin route

A feasible future bridge is to telescope periodic jump coefficients, apply `LSeries_eq_mul_integral` first on `Re(s)>1`, prove analyticity of the bounded step function's Mellin integral on `Re(s)>0`, and continue the identity through the connected half-plane. Mathlib supplies [the summatory-coefficient integral theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/SumCoeff.html) and [Mellin convergence/differentiability from asymptotic bounds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinTransform.html). The actual floor-step local integrability, analytic continuation, and dilation compatibility still need proofs. In particular, `LSeriesSummable` is unconditional summability: bounded signed partial sums cannot justify assuming it in `0<Re(s)≤1`.

This ledger deliberately separates proved infinite-dimensional analysis, explicit unproved propositions, and claims not yet given an exact Lean statement. None of the open arithmetic or RH targets is discharged by the verified Gibbs convergence theorem.

# Detailed arithmetic coverage

This ledger concerns `next5040/construction_research.md` and
`next5040/theory/GENERAL_COMPONENT_RESEARCH.md`. The publication record at the beginning of this document gives the verification status.

## New modules and exact scope

- `FiniteRepairTriangular`: arbitrary finite signed coefficients; triangular L1
  recurrence; floor `1/[72((3/2)^N−1)^2]`; exact signed-share variance identity.
- `FiniteBoundaryRepairObstruction`: actual Möbius-head-plus-floors construction;
  exact normalized divisor-jump relation; proper divisors contribute ratios at
  most 1/2; infinite error extraction; summability from exact total slope balance;
  all smooth endpoint locations allowed. The theorem explicitly retains root
  charge `sum a = −1/3` and total slope balance. It does not claim those inputs
  were inferred merely from the word “legal”. Endpoints are enumerated by a
  strictly increasing sequence; only its first N entries enter the construction.
- `DistributedRepairCompletion`: exact full error split into uniform-share
  contribution, every signed-share fluctuation, every adjacent-pair remainder,
  and the complete unselected infinite tail. The disjointness of selected pairs
  and the stated actual jumps are explicit inputs. The prior module separately
  derives these jumps for antichain repair endpoints.
- `SmoothRepairAntichain`: explicit endpoints `2^j*3^(L−j)` form a divisibility
  antichain on `0≤j≤L`, and each is at least `2^L`.
- `FiniteBalancedRepairSynthesis`: actual legal residue paths from r to
  `r*2^A*3^B`; cancellation after grouping by roots; per-root zero charge implies
  the actual corresponding finite floor sum is in `legalSeedSpan {2,3}`.
  Root/exponent decompositions are supplied as data. The theorem does not need
  roots coprime to 6; that additional condition provides the canonical component
  interpretation in the report. Canonical extraction of these data from an
  arbitrary finitely supported q is not separately formalized here.
- `ComponentJumpGram`: exact general finite Gram identity of consecutive jump
  differences, including the endpoint boundary term; disjoint positive jump
  rows give negative adjacency terms exactly; their signs and the positive
  diagonal upper bound are derived afterward.
- `DivisorComponentJumpRow`: actual Möbius component functional equals
  `sum_(d|D) phi(D/d)/D * Delta F(d)`, derived by Dirichlet-convolution
  associativity. Its original coordinate-spike row is the consecutive difference
  of these explicitly positive jump weights.
- `DivisorComponentNormBound`: bounds the original actual row norm by
  `2*sum_(d|D)(phi(d)/d)^2`, then derives the corresponding full-error bound for
  all signed legal generators and complements coprime to 6.
- `SmoothComponentClosedFloor`: multiplicativity and exact prime-power evaluation
  give the full closed family floor `2/((A+4)(4B+9))` for every A,B>0.
- `SmoothComponentJumpWeights`: identifies the same actual divisor jump weights
  on `2^i3^j` with the displayed alpha_i beta_j formula, including all endpoint
  and interior cases. The general row, norm bound, closed floor, and explicit
  smooth weights all passed the root's combined verification; their endpoint
  axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Earlier accepted content

The published general divisor-component modules establish actual-generator
annihilation, the target signal `phi(D)/D`, positive actual row norm, and the
positive full-error floor for fixed D and all complements coprime to 6. The
published coupled A=4,B=2 two-row certificate gives 272/15927 with all mixed terms.
The published single-boundary module derives its 1/18 floor and smooth divisor
cancellation. The period-2520/5040 certificates were already published. These
should not be submitted as new claims or counted twice.

## Remaining ordinary claims requiring separate formalization

1. For all roots r coprime to 6, the identity
   `eta_r=sum_(t|r) t lambda_t`, its exact target signals, and its identification
   with the proposed sparse jump rows. The generic Gram algebra does not itself
   establish these arithmetic identifications.
2. Disjointness of different canonical component jump supports, the exact
   adjacency condition `|rs-tu|=1`, absence of edges for roots sharing a common
   factor, and the diagonal evaluation
   `K_rr=2*r^2*(A/4+1)*(4B/9+1)` for r>1. The abstract disjoint-support Gram
   identity is now available, but the stated number-theoretic substitutions
   still require proofs.
3. Linear independence of every finite family of the actual component rows;
   positive definiteness of every corresponding Gram matrix; their general
   inverse and Schur-complement extraction; nonnegative optimizer coefficients.
   The A=4,B=2 accepted certificate establishes one genuine arithmetic instance.
4. The cap-boundary jump repetitions `Delta F(2n)=Delta F(n)` and its ternary
   counterpart under the corresponding valuation hypotheses.
5. The exact A=3,B=2 numerical pair 17/804 and the larger rational network trial
   vectors. Their exact-arithmetic scripts are evidence, not Lean certificates.
6. Explicit identification of the smooth Möbius head charge with 1/3, followed
   by inferring all root repair coefficients' sum −1/3 from canonical component
   conservation. The new obstruction states this genuine balance input openly.
7. The explicit antichain adjacent separation
   `T_j−T_(j+1)=2^j3^(L−j−1)≥2` and a single end-to-end instantiation of the full
   distributed completion on all endpoints. The antichain and lower endpoint
   bounds themselves are proved.
8. General coprime-root truncated head charge
   `C_(r,K)=mu(r)/r*[1_(r≤K)−1/2 1_(2r≤K)−1/3 1_(3r≤K)+1/6 1_(6r≤K)]`.
9. The complete distributed construction's exact head interpolation and
    conductor bound `lcm(1,...,K)*6^L`, and nested conductor exhaustion. Its
    finite legal component synthesis is now formalized separately.
10. General positive definiteness of the distinct remainder Gram system and
    every general constrained inverse formula in section 7, including the
    exact constrained minimizer. Generic quadratic-completion results already
    elsewhere in the project may discharge the algebra, but their hypotheses
    must be instantiated with these actual infinite weighted forms.

The listed full-error quadratic identities are ordinary rigorous derivations,
not unconditional RH progress. No vanishing-error claim is proved for the
distributed family. The optimizer comparisons are floating-point diagnostics,
explicitly unsuitable as theorem hypotheses or as evidence of limiting decay.

## Added module index

- [RiemannResearch.Analysis.BoundedPrimitiveAbel](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/BoundedPrimitiveAbel.lean)
- [RiemannResearch.Analysis.ContractiveRepair](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/ContractiveRepair.lean)
- [RiemannResearch.Analysis.MeanNormalization](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MeanNormalization.lean)
- [RiemannResearch.Analysis.ContractiveRepairClosure](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/ContractiveRepairClosure.lean)
- [RiemannResearch.Analysis.NormalizedPairObstruction](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/NormalizedPairObstruction.lean)
- [RiemannResearch.Analysis.PositiveQuadraticNorm](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/PositiveQuadraticNorm.lean)
- [RiemannResearch.RH.DilationWaveletAlgebra](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletAlgebra.lean)
- [RiemannResearch.RH.ParetoResidueLogMean](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoResidueLogMean.lean)
- [RiemannResearch.RH.ArithmeticFluxResearchTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ArithmeticFluxResearchTargets.lean)
- [RiemannResearch.RH.ArithmeticMellinResearchTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ArithmeticMellinResearchTargets.lean)
- [RiemannResearch.RH.BinaryWaveletPrimitive](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/BinaryWaveletPrimitive.lean)
- [RiemannResearch.RH.BinaryWaveletNearbySupport](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/BinaryWaveletNearbySupport.lean)
- [RiemannResearch.RH.ComponentJumpGram](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ComponentJumpGram.lean)
- [RiemannResearch.RH.DilationWaveletOffScale](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletOffScale.lean)
- [RiemannResearch.RH.DilationWaveletNearbyEnergy](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletNearbyEnergy.lean)
- [RiemannResearch.RH.DilationWaveletBinaryNorm](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletBinaryNorm.lean)
- [RiemannResearch.RH.DilationWaveletNoRiesz](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletNoRiesz.lean)
- [RiemannResearch.RH.DilationWaveletAsymptoticTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletAsymptoticTargets.lean)
- [RiemannResearch.RH.DilationWaveletClosure](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DilationWaveletClosure.lean)
- [RiemannResearch.RH.FiniteRepairTriangular](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/FiniteRepairTriangular.lean)
- [RiemannResearch.RH.FiniteBoundaryRepairObstruction](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/FiniteBoundaryRepairObstruction.lean)
- [RiemannResearch.RH.DistributedRepairCompletion](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DistributedRepairCompletion.lean)
- [RiemannResearch.RH.DivisorComponentJumpRow](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DivisorComponentJumpRow.lean)
- [RiemannResearch.RH.DivisorComponentNormBound](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/DivisorComponentNormBound.lean)
- [RiemannResearch.RH.FiniteBalancedRepairSynthesis](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/FiniteBalancedRepairSynthesis.lean)
- [RiemannResearch.RH.GeometricDifferentialResearchTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/GeometricDifferentialResearchTargets.lean)
- [RiemannResearch.RH.ParetoGibbsOperator](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsOperator.lean)
- [RiemannResearch.RH.ParetoGibbsEnergy](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsEnergy.lean)
- [RiemannResearch.RH.ParetoGibbsHankel](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsHankel.lean)
- [RiemannResearch.RH.ParetoGibbsHilbert](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsHilbert.lean)
- [RiemannResearch.RH.GeometricHilbertRealizationResearchTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/GeometricHilbertRealizationResearchTargets.lean)
- [RiemannResearch.RH.ParetoGibbsTailBasis](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsTailBasis.lean)
- [RiemannResearch.RH.ParetoGibbsSchur](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsSchur.lean)
- [RiemannResearch.RH.ParetoGibbsTailMatrix](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsTailMatrix.lean)
- [RiemannResearch.RH.ParetoGibbsSchurGamma](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsSchurGamma.lean)
- [RiemannResearch.RH.ParetoGibbsSchurEnergy](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsSchurEnergy.lean)
- [RiemannResearch.RH.ParetoGibbsPositive](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsPositive.lean)
- [RiemannResearch.RH.ParetoGibbsHilbertEnergy](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsHilbertEnergy.lean)
- [RiemannResearch.RH.ThresholdContractiveRepair](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ThresholdContractiveRepair.lean)
- [RiemannResearch.RH.ParetoGibbsRepair](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsRepair.lean)
- [RiemannResearch.RH.ParetoGibbsSpectralGap](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsSpectralGap.lean)
- [RiemannResearch.RH.ParetoGibbsConvergence](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsConvergence.lean)
- [RiemannResearch.RH.GibbsLegalSeed](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/GibbsLegalSeed.lean)
- [RiemannResearch.RH.GibbsArithmeticResearchTargets](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/GibbsArithmeticResearchTargets.lean)
- [RiemannResearch.RH.ParetoCyclotomicTransform](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoCyclotomicTransform.lean)
- [RiemannResearch.RH.ParetoGibbsGammaTruncation](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsGammaTruncation.lean)
- [RiemannResearch.RH.ParetoGibbsGammaDefect](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsGammaDefect.lean)
- [RiemannResearch.RH.ParetoGibbsOptimality](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsOptimality.lean)
- [RiemannResearch.RH.ParetoGibbsSpectrumTarget](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoGibbsSpectrumTarget.lean)
- [RiemannResearch.RH.ParetoStepIsometry](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoStepIsometry.lean)
- [RiemannResearch.RH.ParetoWaveletTransform](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/ParetoWaveletTransform.lean)
- [RiemannResearch.RH.SmoothComponentClosedFloor](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/SmoothComponentClosedFloor.lean)
- [RiemannResearch.RH.SmoothComponentJumpWeights](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/SmoothComponentJumpWeights.lean)
- [RiemannResearch.RH.SmoothRepairAntichain](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/SmoothRepairAntichain.lean)
