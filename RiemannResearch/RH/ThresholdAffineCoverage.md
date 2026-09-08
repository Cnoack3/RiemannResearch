# RH Two-Seed Threshold: affine extension and weighted Hilbert coverage

This is a **partial formalization** of Christian Noack's September 8, 2026, 32-page `RH_Two_Seed_Threshold.pdf`. The support listed below has passed the coordinator's Lean checks; the saved-module checkpoint additionally validates the actual import graph before publication. Exact types and substantive hypotheses govern coverage. Neither the full paper nor RH is proved.

## Source and verification evidence

- Source: September 8 `RH_Two_Seed_Threshold.tex`, SHA-256 `76ccf4ff222b633e41779a8a80052743549b80fd8a2206ee0260222f8de7e21a`.
- Inventory: 195 labels, including all 44 labels of new Section 11; 35 theorem/lemma/proposition/corollary environments, five research problems and two remarks. Section 11 adds eight named mathematical claims. The former research Section 11 is now Section 12.
- New module manifest: 22 modules and 166 public theorem declarations, with definitions recorded in their source modules. No project-local axiom, `sorry`, `admit`, `unsafe`, or unchecked native computation is part of the formalization.
- Combined proof/axiom audit job: `job_02lJqvW03kvAk9rjjNhbJf3lzssIVPJW`, succeeded with `verified: true`, exit code 0. Combined source SHA-256 `96fa197992f9a1cc37a242562a13ea66751ee822d497709a0c0077fad1747e9c`. One endpoint from every new module was audited with `#print axioms`; only ordinary foundations `propext`, `Classical.choice`, and `Quot.sound` occur.
- Saved-source correspondence: `ThresholdVerification.json` records the exact SHA-256 of every new module. The successful combined check inlines those exact module bodies and their existing project dependencies. The publication checkpoint checks the saved modules through their real imports and their reverse dependents.
- Publication evidence is the checkpoint receipt and the Git commit containing these files; its hash is reported with the delivered result. A checked snippet is distinct from checkpoint acceptance.

The earlier `RH/ThresholdPaperCoverage.md` remains the historical source-to-Lean audit. Its established nine-module contributions and actual period-36 upper witness remain valid. This document updates only the explicitly covered components; all other historical obligations remain open.

## Checked support by module

Module names below omit the common prefix `RiemannResearch.`. All integer dilations mean every positive integer, with no restriction to products of 2 and 3.

| Module | Exact proved support and scope |
|---|---|
| `RH.ThresholdLegalIntegrability` | Every finite legal synthesis from positive seeds is bounded; actual weighted means, mixed products and full errors are summable. |
| `RH.ThresholdSeedEuclidean` | Common-base powers admit exact Euclidean/gcd synthesis, including arbitrary finite exponent lists. Collective gcd one suffices without a coprime pair. |
| `RH.ThresholdPrimePackets` | Actual prime-seed span equals the divisible-conductor packet span; the two-prime span is their sum. Auxiliary conductor primes and all integer dilations remain available. |
| `RH.ThresholdHilbertSpace` | Complete real H, represented by `lp` with exponent 2; exact original weighted norm and a bijective physical-coordinate encoding of all anchored weighted-square-summable sequences. |
| `RH.ThresholdHilbertDilation` | Actual bounded `T_m`, exact norm scaling and composition, genuine Hilbert adjoints, normalized linear isometries and mean preservation. |
| `RH.ThresholdHilbertMean` | Exact actual weighted inner product, unit target `hilbertOne`, expectation as pairing with that target, and `T_m* hilbertOne = hilbertOne` for every positive integer. This is one inclusion in the fixed-space statement, not joint rigidity. |
| `RH.ThresholdHilbertLegal` | Actual legal subspaces and closures in the weighted H norm; all-integer invariance and common-base finite-list classification after closure. |
| `RH.ThresholdPhaseConstant` | Actual logarithmic phase summands: positivity, summability, exact head/tail splitting; scalar phase floor strictly between zero and one for every base at least two. |
| `RH.ThresholdPhaseSharpBound` | Actual bound `delta_k <= 1/[12k(k+1)]`, infinite upper tail and `s <= 1/12`. |
| `RH.ThresholdPhaseLowerBound` | Matching lower correction and finite telescoping certificate with its full terminal boundary. |
| `RH.ThresholdPhaseTail` | Actual two-sided infinite tail certificate; stronger cubic denominator `144(N+1)^3`, valid at `N=0`; exact rational enclosure `11/144 <= s <= 1/12`. |
| `Analysis.PhaseWitnessGeometry` | Exact witness norm, error = floor + full excess, and unique equality vector. **Conditional research reduction:** actual extremal vector, its norm/pairing and legal annihilation remain required providers. |
| `LinearAlgebra.WeightedFiniteQuotient` | Actual finite averaging/repetition matrices, weighted adjoint, tower identity, residual orthogonality and full error decomposition; nonzero fiber masses are explicit. |
| `RH.ThresholdWeightedCRT` | Concrete specialization to genuine infinite arithmetic-progression weights: positive normalized refinement masses, exact weighted conditional formula, mean preservation and full coarse/fine error equality. |
| `LinearAlgebra.WeightedQuotientDefectRank` | Actual ambient defect range equals the averaging kernel; rank is fine cardinality minus coarse cardinality when all fiber masses are nonzero. This is not the rank of the legal coarse map. |
| `RH.ThresholdAffineBranches` | Arithmetic branch composition, injectivity, disjointness and exact missing head; genuine weighted coefficient normalization and signed column discrepancy. |
| `LinearAlgebra.RankOneProjectionDistance` | Complete finite real rank-one matrix discrepancy; unit columns give twice one minus squared overlap. |
| `RH.ThresholdAffineProjectionBlocks` | Actual Pareto branch coefficients instantiate that finite projection discrepancy on each physical block. No infinite HS sum is asserted. |
| `LinearAlgebra.CompressionProductDefect` | Exact ordered compression identity, monoid difference cocycle, self-adjoint square factorization and full finite mixed Gram expansion. General ordered products are not asserted positive. |
| `LinearAlgebra.SpectralCutoffRepair` | Finite spectral error/norm accounting and cutoff bounds, allowing zero eigenvalues; numerical implication from an explicit `<53/1000` model error. |
| `LinearAlgebra.SpectralRepeatedFit` | Exact geometric repeated-fit error and increment; full error increases after the first optimal step although the coarse residual decreases. |
| `LinearAlgebra.SpectralDiagonalRealization` | Explicit cutoff amplitudes derive the profile, norm and error formulas from the diagonal quadratic model, including the factor-two bound. Actual weighted legal covariance/synthesis realization remains open. |

The actual real Hilbert construction is now supplied, including its exact mixed inner product and fixed unit target. The remaining adjoint obligations are the explicit weighted-block coordinate law, phase fixed-space theory and joint rigidity. Complex analytic and profinite realizations are also separate.

The finite spectral inequalities have no unresolved arithmetic input as statements about their explicit finite data. Their hypotheses include nonnegative masses, eigenvalues at most one, positive cutoff, and target normalization where used. Identifying those data with the paper's actual covariance and constructing the stated legal vector is a substantive missing application provider.

## Every Section 11 label

“Partial” means the named checked component is available while the complete paper assertion remains open. “Model” means the finite diagonal quadratic calculation is checked; its actual weighted legal realization remains open. “Open” records no provider for the stated analytic claim. Endpoint spellings are exact; namespaces are explained after the table.

| Source label | Checked support | Remaining obligation |
|---|---|---|
| `sec:affine` | Partial section coverage below. | All eight named claims retain the gaps specified below. |
| `prop:affine-algebra` | Partial: `affineBranch_comp`, `affineBranch_disjoint`, `affineBranch_positive_partition`. | Actual operator/C*-algebra construction, compact ideal, quotient isomorphism, Cuntz simplicity and vector state. |
| `eq:affine-relations` | Partial: exact arithmetic composition and disjointness. | Actual bounded branch operators and their adjoints. |
| `eq:affine-boundary` | Partial: `affineBranch_positive_partition`. | Range-projection identity and exact weighted state mass. |
| `eq:conditional-rank-one` | Open. | Actual conditional projection as weighted rank-one sum, its rank and quotient image. |
| `eq:affine-average` | Partial: `hilbertNormalizedDilation`. | Uniform branch average `L_m`, its isometry and semigroup laws. |
| `thm:affine-compact` | Partial: branch normalization and `Ring.hom_difference_cocycle`. | Operator assembly, uniform tail, compact/Schatten membership and non-trace-class asymptotic. |
| `eq:weighted-branches` | Partial: `affineBranchCoefficient_sq_sum`, `Ring.hom_difference_cocycle`. | Concrete operator sum and diagonal normalization identity. |
| `eq:compact-tail` | Open. | Uniform operator tail `1/[2(J+1)]`. |
| `eq:affine-singular-asymptotic` | Open. | Precise fixed-scale singular-value expansion and class consequences. |
| `thm:affine-phase-constant` | Partial: `affineProjection_block_discrepancy` and actual phase summability. | Infinite HS identification and its limit/rate. |
| `eq:affine-projection-HS` | Partial: exact actual finite physical-block discrepancy. | Infinite orthogonal-block norm assembly and stated overlap formula. |
| `eq:affine-phase-limit` | Partial: `phaseDelta_summable`, `universalPhaseConstant_certificate`. | Actual limit `2s` and nonnegative `m^-2` error bound. |
| `eq:affine-seed-limit` | Partial: `affineBranchCoefficient_uniform_defect`. | Seed assembly, dominated convergence and positive lower limit. |
| `thm:affine-transfer` | Partial: actual legal integrability and finite mixed Gram algebra. | Concrete correction vectors and coefficient-sensitive retained-head/tail estimates. |
| `eq:affine-exact-error` | Partial: complete quadratic/Gram accounting infrastructure. | Concrete affine and legal vector identification in H. |
| `eq:affine-transfer-tail` | Open. | Coefficient-budget norm tail and reverse-triangle comparison. |
| `eq:affine-finite-Gram` | Partial: `StarRing.compression_finite_gram`. | Actual finite coordinate formula with all overlapping branches. |
| `eq:affine-rectangular` | Partial: actual Hilbert isometry and dilation composition. | Anchored finite spaces, refinement restrictions and their exact identities. |
| `thm:affine-compression` | Partial: actual weighted quotients and progression tails. | Anchored operator/witness identity, zeta bounds and defect norm limit one. |
| `eq:affine-compression-bound` | Open. | Both stated operator-norm inequalities with the exact constant. |
| `eq:affine-product-defect` | Checked: `Ring.compression_product_defect`; square and full finite Gram variants. | No missing arithmetic input for the general ring identity; arbitrary ordered products have no sign claim. |
| `eq:affine-weighted-defect-matrix` | Partial: actual weighted quotient adjoint and error identity. | Legal basis/Gram inverse and covariance `D G^-1 D^T Omega_N`. |
| `prop:affine-information` | Open. | Actual covariance, monotonicity, cofinal limit and RH equivalence. |
| `eq:affine-information-split` | Open. | Actual coarse legal/complement block decomposition. |
| `eq:affine-information-increment` | Open. | Actual nested legal projections and positive covariance increment. |
| `eq:affine-information-gain` | Open. | Exact target gain for the actual increment projection. |
| `eq:affine-target-spectrum` | Model: `diagonalError_exact`, `repeatedError_first`. | Actual target spectral masses and legal optimum identification. |
| `eq:affine-exact-spectral-lift` | Model: all-retained amplitudes. | Full-rank legal right inverse and minimum-norm property. |
| `eq:affine-negative-moment` | Model: `cutoffError_of_all_retained`, `cutoffNorm_of_all_retained`. | Actual lift norm/error as these inverse moments. |
| `thm:affine-cutoff` | Model: `diagonal_half_cutoff`. | Actual covariance eigenbasis, legal synthesis and true H norm/error. |
| `eq:affine-cutoff-vector` | Model: explicit `cutoffAmplitude`. | Construct its image in the actual finite two-seed legal space. |
| `eq:affine-cutoff-profile` | Model: `cutoffAmplitude_profile`. | Actual coarse projection and retained eigenspace identification. |
| `eq:affine-cutoff-identities` | Model: `diagonalError_cutoff`, `diagonalNorm_cutoff`. | Actual spectral masses and vector realization. |
| `eq:affine-cutoff-bounds` | Model: `cutoffError_le`, `cutoffNorm_le`. | Actual legal application provider; no convergence follows from the finite bound. |
| `eq:affine-half-cutoff` | Model: `half_cutoff_bounds`, `diagonal_half_cutoff`. | Actual legal cutoff vector and normalization identification. |
| `cor:affine-certified-cutoff` | Model: `certified_half_cutoff_bounds`; prior actual witness `<53/1000`. | Connect the witness to covariance optimum and legal cutoff; exact-fit lower bound `>22`. |
| `eq:affine-cutoff-example` | Model: implication giving `<106/1000` and `<1106/1000`. | Actual period-36 cutoff existence with both bounds. |
| `eq:affine-iteration-cost` | Model: `repeatedError_exact`, `repeatedError_nondecreasing`. | Actual covariance/synthesis identification of the legal iteration. |
| `eq:affine-legal-transport` | Partial: actual all-integer legal invariance and normalized Hilbert isometry. | Finite-level innovation projection and exact distance improvement. |
| `eq:affine-information-transport` | Partial: same actual invariance/isometry infrastructure. | Anchored covariance and its exact transported increment. |
| `eq:affine-spectral-regularity` | Open hypothesis. | Uniform target-specific regularity across growing coarse moduli. |
| `eq:affine-regularity-cost` | Open conditional implication. | Formal inverse-moment/Tonelli estimate, with regularity retained as hypothesis. |
| `eq:affine-regularity-rate` | Open conditional implication. | Formal integration-by-parts/cutoff estimate, with regularity retained as hypothesis. |

Arithmetic and Hilbert endpoints are in `RiemannResearch.RH.Pareto`; phase-series endpoints are in `RiemannResearch.RH.TwoSeedThreshold`; finite spectral endpoints are in `RiemannResearch.LinearAlgebra.SpectralCutoff`. Compression identities use `Ring` and `StarRing`, and finite rank-one identities use `Real`. The actual prior witness is `RiemannResearch.RH.TwoSeedThreshold.legalWitness36_full_error_lt`. In `RH.ThresholdWeightedCRT`, only `pushforward_fst` is in `RiemannResearch.LinearAlgebra.WeightedFiniteQuotient`; its arithmetic refinement endpoints are in `RH.Pareto`. A module name is not automatically a declaration namespace.

## Preserved substantive obligations

1. **Full RH criteria remain open.** Strong Nyman–Beurling must be a checked dependency, with the exact discrete step-function bridge. Full-span density, primitive common-base classification of arbitrary rank-one seed data, joint rigidity for independent seeds and shrinking-cell recovery are unfinished. Proving the adjoints fix the constant does not prove that their joint fixed space contains only constants.
2. **The phase distance is not yet established.** Actual phase laws/conditional operators, martingale spectrum, fixed-space classification, extremal vector and its arithmetic moments/annihilation remain open. Scalar phase-floor positivity and conditional Hilbert witness geometry do not discharge these providers. Exact one-base distance/RH equivalence, witness asymptotics, Mellin continuation, removable values, nonvanishing and off-line-zero penalties remain unfinished.
3. **The numerical certificate scope remains limited.** The actual phase tail and rational enclosure are checked, but the paper's narrow decimal intervals, finite witness interval, coarse-6 determinant, constrained norm `(22,23)`, and unconstrained optimum lower bound `>0.051` remain open. The prior actual infinite-tail legal upper witness `<0.053` remains established; it does not itself identify a covariance optimizer or the cutoff vector.
4. **The affine quotient does not replace the weight or legality.** Cuntz's quotient/simplicity theorem, weighted vector state/non-descent, conditional rank-one formula, rank-one cyclicity of the full affine algebra, actual compact/Schatten comparison, infinite HS limit, positive seed discrepancy and non-collective compactness remain open. Atomic/Haar singularity, profinite topology, nonclosability and projection strong convergence also remain historical gaps.
5. **Finite legal synthesis still needs its operator provider.** Actual finite legal projections, dimensions, coarse surjectivity, multicolumn Gram/Schur inverse identities, exact second-seed gain, constrained-lift minimum, covariance diagonalization, spectral target masses, legal cutoff synthesis and innovation transport remain unfinished. Ambient weighted quotient defect rank is not legal surjectivity.
6. **No uniform repair or vanishing error is proved.** A bounded sequence of exact two-seed lifts, a uniform target negative-moment estimate, and full legal error tending to zero remain open. The paper's bounded-lift RH criterion itself still needs formalization. The spectral regularity assumption is not a checked arithmetic theorem.

The next direct provider is the actual weighted Hilbert realization of finite quotient and legal projections, followed by covariance diagonalization and legal synthesis. This would connect the checked finite cutoff calculation to the paper's factor-two theorem. A second independent target is to assemble the checked physical-block identities into the infinite HS norm, using the actual phase summability and retaining the complete affine correction. These are specific missing bridges; neither can be replaced by ordinary inverse-limit convergence.
