# Theorem catalog

This catalog is an orientation layer. Lean source files and successful builds
remain authoritative.

For the complete result ledger of the attached 5 August 2026 E8 Serre II
manuscript, see `E8/SERRE_II_2026_08_05_THEOREM_LEDGER.md`. For the broader
mathematical audit across program revisions, including citation-dependent and
unreproduced computer-assisted claims, see `E8/SERRE_II_PROOF_AUDIT.md`.

## Status conventions

- **Kernel checked** means Lean has verified a proof of the declaration's exact
  type.
- **Established local declaration** means the result is not currently serving
  as a stand-in for an unfinished named research theorem. It may still have the
  ordinary hypotheses appropriate to a general reusable lemma.
- **Conditional research reduction** means Lean has checked the implication,
  but domain-specific inputs needed for the motivating theorem remain
  unresolved.
- **Open obligation** means no project declaration currently supplies that
  input. Local hypotheses do not appear in `#print axioms`, so a clean axiom
  report alone does not make a result unconditional.

## Established local declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `sanity_check` | `RiemannResearch.Basic` | Confirms arithmetic tactics and mathlib are available | Kernel checked |
| `Nat.zero_add_concurrency_b` | `RiemannResearch.Basic` | Zero is a left identity for natural-number addition; isolated publication concurrency check B | Kernel checked |
| `Nat.add_zero_concurrency_a` | `RiemannResearch.Basic` | Adding zero on the right leaves a natural number unchanged; concurrency branch A verification | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equality of rational-point predicates implies equality of the set-gcd indices of all finite point-field degrees | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.closedPointIndex_eq_pointFieldIndex` | `RiemannResearch.AlgebraicGeometry.PointFields` | Identifies the traditional closed-point gcd with the splitting-field gcd under the residue-field and closed-image divisibility hypotheses | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.point_iff_of_fixedLocus_coproduct` | `RiemannResearch.AlgebraicGeometry.PointFields` | A proper-limit map, coproduct fixed locus, and fixed-component inclusion give equality of point fields | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.comp` | `RiemannResearch.Logic.PointedKernel` | Trivial neutral fibers compose through a tower of pointed maps | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTensorDecomposition` | The canonical finite-Galois equivalence `L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L)` evaluates `x ⊗ y` at `σ` as `x * σ y` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTripleTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTripleTensorDecomposition` | The triple-overlap equivalence evaluates `x ⊗ (y ⊗ z)` at independent `(σ, ρ)` as `x * σ y * ρ z` | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.classOf_eq_neutral_iff_isCoboundary` | `RiemannResearch.GaloisCohomology.NonabelianH1` | A discrete nonabelian cocycle represents the neutral class exactly when it is a coboundary | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.restrict_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | Restriction of discrete nonabelian first cohomology to a subgroup preserves the neutral class | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.map_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | An equivariant group homomorphism sends neutral nonabelian cohomology classes to neutral classes | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Conjugation_hom_inv` | `RiemannResearch.GroupCohomology.Conjugation` | Additive H¹ conjugation between a subgroup and its conjugate is an isomorphism, with explicit inverse law | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_tower` | `RiemannResearch.GroupCohomology.Restriction` | Additive first-cohomology restriction through nested subgroups equals direct restriction | Kernel checked |
| `RiemannResearch.GroupCohomology.h1_subsingleton_of_isUnit_fintype_card` | `RiemannResearch.GroupCohomology.StableElements` | Averaging makes additive (H^1) of a finite group trivial when its order is a unit in the coefficient ring | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_injective_of_normal_finiteIndex` | `RiemannResearch.GroupCohomology.StableElements` | Restriction to a normal finite-index subgroup is injective when the index is a unit | Kernel checked |
| `RiemannResearch.LinearAlgebra.regularFunctional_exists_adaptedBase` | `RiemannResearch.LinearAlgebra.RootSystem.AdaptedBase` | A functional nonzero on every root admits a base on whose simple roots it is positive; corrects the PDF's sign-only chamber step | Kernel checked |
| `RiemannResearch.LinearAlgebra.exists_lift_of_rightInverse` | `RiemannResearch.LinearAlgebra.SplitLift` | A split module quotient lifts every map; over a group algebra this is the equivariant lift used by the valuation packet | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_coprime_restrictions` | `RiemannResearch.GroupTheory.CoprimeRestriction` | Two additive restriction maps satisfying coprime restriction--corestriction index formulas jointly detect zero | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_gcd_one_annihilators` | `RiemannResearch.GroupTheory.CoprimeRestriction` | A finite family of annihilating natural degrees with integer gcd one detects zero in an additive commutative group; abstract kernel for PDF Lemma 6.36 | Kernel checked |
| `RiemannResearch.GroupTheory.not_mem_addSubgroup_closure_of_mark` | `RiemannResearch.GroupTheory.BurnsideTopMark` | A class with mark one is not in the additive subgroup generated by classes with mark zero; abstract top-mark kernel for PDF Proposition 6.32 | Kernel checked |
| `RiemannResearch.GroupTheory.fixed_of_fixed_on_join_eq_top` | `RiemannResearch.GroupTheory.GeneratedFixedPoint` | A common point fixed by two generating subgroups is fixed by the whole group; separate local fixed points are not enough | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_cocycle` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | A divisible half-difference `(ell - g·ell)/2` satisfies the one-cocycle identity | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_at_involution` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | At an element acting by minus one, the half-difference cocycle restricts to its chosen lift | Kernel checked |
| `RiemannResearch.GroupTheory.exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one` | `RiemannResearch.GroupTheory.PGroupFixedPoints` | A finite `p`-group acting additively on finite `V` has a nonzero fixed point when `Nat.card V ≢ 1 [MOD p]` | Kernel checked |
| `RiemannResearch.E8.a8Normalizer_bezout` | `RiemannResearch.E8.A8NormalizerArithmetic` | Verifies the exact identity `-27·15 + 2·35 + 336 = 1` | Kernel checked |
| `RiemannResearch.E8.eq_zero_of_a8_annihilators` | `RiemannResearch.E8.A8NormalizerArithmetic` | An abelian class killed by the three A8 cover degrees 15, 35, and 336 is zero | Kernel checked |
| `RiemannResearch.E8.oddHalfSpinResidues_perm` | `RiemannResearch.E8.A9TrialityArithmetic` | One half-spin parity of a nine-cycle gives all eight nonzero residues modulo nine | Kernel checked by finite decision |
| `RiemannResearch.E8.evenHalfSpinResidues_perm` | `RiemannResearch.E8.A9TrialityArithmetic` | The other parity gives two zero residues and the six primitive ninth-root residues | Kernel checked by finite decision |
| `RiemannResearch.E8.a9Triality_determinant_order` | `RiemannResearch.E8.A9TrialityArithmetic` | Verifies `Φ₃(1)Φ₉(1)=9` for the fixed-point-free order-nine packet | Kernel checked |
| `RiemannResearch.E8.sp6Packet_sylowIndex` | `RiemannResearch.E8.SylowSevenArithmetic` | Verifies the factorization, coprimality to seven, and mod-seven residue for the Sp6 packet index 34560 | Kernel checked |
| `RiemannResearch.E8.a8Packet_sylowIndex` | `RiemannResearch.E8.SylowSevenArithmetic` | Verifies the factorization, coprimality to seven, and mod-seven residue for the A8 packet index 61440 | Kernel checked |
| `RiemannResearch.E8.a9Packet_sylowIndex` | `RiemannResearch.E8.SylowSevenArithmetic` | Verifies the factorization, coprimality to seven, and mod-seven residue for the A9 packet index 4320 | Kernel checked |
| `RiemannResearch.E8.trialityPacket_sylowIndex_arithmetic` | `RiemannResearch.E8.SylowSevenArithmetic` | The packet indices 34560, 61440, and 4320 are prime to seven and congruent to one modulo seven | Kernel checked |
| `RiemannResearch.E8.trialityPacket_normalizer_index_products` | `RiemannResearch.E8.SylowSevenArithmetic` | Verifies the three normalizer-order times index calculations in the triality-packet table | Kernel checked |
| `RiemannResearch.E8.weylIndexPacket_bezout` | `RiemannResearch.E8.WeylIndexPacket` | Verifies `-73·135 + 26·2240 - 48384 = 1` for the three maximal-rank reduction degrees | Kernel checked |
| `RiemannResearch.E8.weylIndexPacket_gcd` | `RiemannResearch.E8.WeylIndexPacket` | The three packet degrees have gcd one | Kernel checked |
| `RiemannResearch.E8.exists_odd_of_sum_eq_135` | `RiemannResearch.E8.WeylIndexPacket` | A finite family of degrees summing to 135 contains an odd degree | Kernel checked |
| `RiemannResearch.E8.eq_zero_of_weylIndexPacket_annihilators` | `RiemannResearch.E8.WeylIndexPacket` | An abelian class killed by 135, 2240, and 48384 is zero | Kernel checked |
| `RiemannResearch.E8.exists_bounded_weylIndexPacket_residue` | `RiemannResearch.E8.WeylIndexPacket` | Every residue modulo 135 is represented by `2240a+48384b` with `a<27`, `b<5` | Kernel checked by finite decision |
| `RiemannResearch.E8.weylIndexPacket_residue_bound` | `RiemannResearch.E8.WeylIndexPacket` | The residue representatives are bounded by 251776 | Kernel checked |
| `RiemannResearch.E8.a2Coroot_sign_normalization_counterexample` | `RiemannResearch.E8.SerreIIProgramChecks` | The A2 simple coroot is regular but neither it nor its negative has both simple-root pairings positive; refutes the sign-only normalization in PDF Theorem 3.2 | Kernel checked counterexample |
| `RiemannResearch.E8.serreIIProgram_fullWeylSubsystem_index_products` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks the three E8 Weyl stabilizer index products for PDF Theorem 5.16 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_threeSubsystem_bezout` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks `-1417·135 + 16·11200 + 12096 = 1` from PDF Corollary 5.17 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_threeSubsystem_gcd` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks that 135, 11200, and 12096 have gcd one | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_field_degrees` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks the degree-105 overlap and degree-4032 Sylow-five fields in PDF Proposition 6.7 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_bezout` | `RiemannResearch.E8.SerreIIProgramChecks` | Supplies an exact integral Bezout identity for 15, 35, and 4032 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_gcd` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks that 15, 35, and 4032 have gcd one | Kernel checked arithmetic |
| `RiemannResearch.E8.eq_zero_of_serreIIProgram_a8Gauge_annihilators` | `RiemannResearch.E8.SerreIIProgramChecks` | An abelian class killed by 15, 35, and 4032 is zero | Kernel checked additive shadow |
| `RiemannResearch.E8.serreIIProgram_survivorEnvelope_bezout` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks all five displayed Bezout rows in PDF Theorem 6.9 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_survivorEnvelope_gcd` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks the gcd-one assertion for all five degree rows in PDF Theorem 6.9 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_binaryIcosahedral_index_arithmetic` | `RiemannResearch.E8.SerreIIProgramChecks` | Checks the elementary order and index arithmetic in PDF Proposition 6.15 | Kernel checked arithmetic |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.OmegaEightPlusTwo` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.OmegaEightPlusTwo` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.E8.attractingRank_properties` | `RiemannResearch.E8.WonderfulFixedLocus` | The length-plus-descent formula and Coxeter complement identities imply unique zero rank and rank duality | Kernel checked |
| `RiemannResearch.E8.e8AttractingRank_eq_zero_iff` | `RiemannResearch.E8.WonderfulFixedLocus` | On Mathlib's E8 Coxeter group, length plus the number of right descents vanishes exactly at the identity | Kernel checked unconditionally |
| `RiemannResearch.E8.e8_total_attracting_rank` | `RiemannResearch.E8.WonderfulFixedLocus` | Checks the E8 total attracting-rank arithmetic `120 + 8 = 128` | Kernel checked |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Conditional research reductions

These declarations are complete proofs of implications, but they are not
unconditional proofs of the motivating named theorems.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | From the inputs listed below, proves parts (i)--(iii), nonabelianness of the simple core, and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked implication; open obligations remain |
| `RiemannResearch.E8.universalFixedLocusAndSplittingField` | `RiemannResearch.E8.WonderfulFixedLocus` | From the inputs listed below, proves the assembled fixed-locus, motivic, point-field, splitting-spectrum, and set-gcd-index conclusions | Kernel checked corrected implication; literal PDF cocharacter normalization fails; open obligations remain |

### Open obligations: `quasisimpleCoreOfFullWeylDescent`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `restriction_preserves_neutrality` | Restriction from the base field preserves neutrality | Generic discrete nonabelian (H^1) logic is kernel checked by `NonabelianH1.restrict_preserves_neutrality`; the finite-Galois/fpqc torsor comparison and E8 instantiation remain **open** |
| `quadratic_restriction_kernel` | Neutrality after the quadratic extension descends to the base | **Open** |
| `central_torus_splitting` | The relevant central torus is split by the cyclic quadratic extension | **Open** |
| `cyclic_prime_torus_kernel` | The cyclic-prime torus kernel theorem neutralizes the class over the central field | **Open** |
| `gal_equiv_evenQuotient` | Identification of the Galois group with the even Weyl quotient | **Open** |
| `evenQuotient_equiv_omega` | Identification of the even Weyl quotient with `Ω₈⁺(2)` | **Open** |
| `omega_order` | Order formula for the supplied `Ω` group | **Open** |
| `omega_simple` | Simplicity of the supplied `Ω` group | **Open** |
| `smallPrime_card` | Cardinalities of the fixed-vector modules for `p = 2, 3, 5` | **Open** |
| `seven_card` | Cardinality of the fixed-vector module for `p = 7` | **Open** |
| `diagonalizable_subgroup_criterion` | A nonzero fixed lattice vector implies neutrality over the Sylow fixed field | **Open** |

### Open obligations: `universalFixedLocusAndSplittingField`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `fixed_locus_decomposition` | Universal scheme-level decomposition of the fixed locus into twisted Borel components | **Open** |
| `fixed_locus_on_points` | Point-level consequence of the fixed-locus coproduct | **Open** |
| `rank_formula` | Chamber-normalized attracting-rank formula | Adapted-chamber existence is kernel checked by `regularFunctional_exists_adaptedBase`; tangent weights, fixed-scheme geometry, and the rank formula remain **open** |
| `length_zero_iff` | Coxeter length vanishes only at the identity in the supplied model | **Open** |
| `rightDescent_one` | The identity has no right descents in the supplied model | **Open** |
| `length_duality` | Complementary Coxeter-length identity | **Open** |
| `rightDescent_duality` | Complementary right-descent identity | **Open** |
| `bialynickiBirula_motive` | Integral motivic Białynicki–Birula decomposition | **Open** |
| `bialynickiBirula_chowZero` | Degree-compatible `CH₀` comparison from the zero-rank component | **Open** |
| `properLimit` | A compactification point specializes to a fixed-locus point | **Open** |
| `fixedComponentInclusion` | A twisted Borel component point gives a compactification point | **Open** |
| `borelReduction_iff_neutral` | A Borel reduction is equivalent to neutrality of the torsor | **Open** |

## Planned research areas

| Area | Initial target |
|---|---|
| Nyman–Beurling | Define the fractional-part generators in `L²(0,1)` |
| de Branges theory | Hermite–Biehler functions and reproducing-kernel spaces |
| Hilbert–Pólya | A precise conditional spectral formulation |
| Operator theory | Closed, densely defined, and self-adjoint operators |
| Spectral triples | Finite-dimensional prototype, then compact resolvent |
| Noncommutative geometry | C*-algebra representations and commutators |
| Field with one element | Select and encode a precise F₁ framework |
| Serre S₂ | Depth-based formulation for rings and schemes |
