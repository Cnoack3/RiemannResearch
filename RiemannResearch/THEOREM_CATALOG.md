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
| `RiemannResearch.AlgebraicGeometry.FpqcCover.Refinement.pullbackH1_one` | `RiemannResearch.AlgebraicGeometry.FpqcCechH1` | Refinement pullback on fixed-cover nonabelian Čech H¹ preserves the neutral class | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcCechH1.IsNeutral.pullback` | `RiemannResearch.AlgebraicGeometry.FpqcCechH1` | A neutral affine-group-scheme Čech class remains neutral after refining its witnessed fpqc cover | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcCover.commonRefinementData` | `RiemannResearch.AlgebraicGeometry.FpqcCoverCommonRefinement` | Any two witnessed indexed fpqc covers of `Spec R` have a pairwise-pullback common cover and refinement maps to both inputs | Kernel checked construction |
| `RiemannResearch.AlgebraicGeometry.FpqcCover.Refinement.pullbackH1_eq` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Any two refinement maps with the same source and target induce the same map on nonabelian Čech H¹ | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1Representative.equivalent_trans` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Equality of fixed-cover classes after witnessed common refinement is transitive | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1.classOf_eq_iff` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Two fixed-cover classes define the same global fpqc Čech H¹ class exactly when they agree on a witnessed common refinement | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1.classOf_neutral` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | The neutral class on every witnessed fpqc cover maps to the distinguished global neutral class | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equality of rational-point predicates implies equality of the set-gcd indices of all finite point-field degrees | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq_one_of_two_point_degrees` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | Two actual finite point fields of coprime degrees force the point-field index to equal one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq_one_of_three_point_degrees` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | Three actual finite point fields with gcd one force the point-field index to equal one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.one_mem_of_setGcd_eq_one_of_prime_powers` | `RiemannResearch.AlgebraicGeometry.PrimePowerIndex` | A prime-power degree set with gcd one contains degree one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.degree_one_pointField_exists_of_prime_power_degrees` | `RiemannResearch.AlgebraicGeometry.PrimePowerIndex` | Prime-power finite point degrees and point-field index one produce an actual degree-one point field | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.closedPointIndex_eq_pointFieldIndex` | `RiemannResearch.AlgebraicGeometry.PointFields` | Identifies the traditional closed-point gcd with the splitting-field gcd under the residue-field and closed-image divisibility hypotheses | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.point_iff_of_fixedLocus_coproduct` | `RiemannResearch.AlgebraicGeometry.PointFields` | A proper-limit map, coproduct fixed locus, and fixed-component inclusion give equality of point fields | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.comp` | `RiemannResearch.Logic.PointedKernel` | Trivial neutral fibers compose through a tower of pointed maps | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.tower` | `RiemannResearch.Logic.PointedKernel` | Trivial neutral fibers iterate through every finite dependent tower of pointed maps | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTensorDecomposition` | The canonical finite-Galois equivalence `L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L)` evaluates `x ⊗ y` at `σ` as `x * σ y` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTripleTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTripleTensorDecomposition` | The triple-overlap equivalence evaluates `x ⊗ (y ⊗ z)` at independent `(σ, ρ)` as `x * σ y * ρ z` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisDoubleOverlapPointMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | Affine-group points on the finite-Galois double overlap are multiplicatively equivalent to Galois-indexed L-points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.galoisTripleOverlapPointMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | Affine-group points on the triple overlap are multiplicatively equivalent to two-variable Galois-indexed L-points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.galoisCechFace12_point` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | The one-two affine Čech face is the twisted Galois projection `σ • f (σ⁻¹ρ)` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisCechFace12_eval` | `RiemannResearch.GaloisCohomology.GaloisCechComparison` | In Galois coordinates, the twisted Čech face evaluates as `σ (f (σ⁻¹ρ))` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisCechCocycleEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechComparison` | The coordinate Čech cocycle equation is equivalent to the inhomogeneous nonabelian group-cocycle equation | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.GaloisCechH1.equivNonabelian` | `RiemannResearch.GaloisCohomology.GaloisCechComparison` | Coordinate finite-Galois Čech H¹ is pointed-equivalent to discrete nonabelian H¹ | Kernel checked equivalence |
| `RiemannResearch.AlgebraicGeometry.finiteGaloisFpqcCover` | `RiemannResearch.GaloisCohomology.GaloisCechComparison` | A finite Galois field extension supplies the witnessed singleton fpqc cover of affine spectra | Kernel checked construction |
| `RiemannResearch.AlgebraicGeometry.finiteGaloisH1EquivNonabelian` | `RiemannResearch.GaloisCohomology.GaloisCechComparison` | The actual fixed-cover Čech H¹ is equivalent to discrete nonabelian H¹ once the explicit Yoneda cocycle-comparison datum is supplied | Kernel checked conditional equivalence |
| `RiemannResearch.GaloisCohomology.finiteGaloisDoubleOverlapIso` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | The chosen categorical double overlap of Spec L over Spec K is canonically the spectrum of `L ⊗[K] L` | Kernel checked scheme isomorphism |
| `RiemannResearch.GaloisCohomology.finiteGaloisDoubleOverlapSectionMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | Sections of the represented affine group on the chosen double overlap are multiplicatively equivalent to algebra maps into `L ⊗[K] L` | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.finiteGaloisTripleOverlapIso` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | The chosen right-associated categorical triple overlap is canonically the spectrum of `L ⊗[K] (L ⊗[K] L)` | Kernel checked scheme isomorphism |
| `RiemannResearch.GaloisCohomology.finiteGaloisTripleOverlapSectionMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | Sections on the chosen triple overlap are multiplicatively equivalent to algebra maps into the tensor cube | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.finiteGaloisDoubleOverlapGaloisMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | Sections on the chosen double overlap are directly equivalent to Galois-indexed affine-group points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.finiteGaloisTripleOverlapGaloisMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge` | Sections on the chosen triple overlap are directly equivalent to two-variable Galois-indexed affine-group points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.singletonOneCochainMulEquiv` | `RiemannResearch.GaloisCohomology.SingletonCechH1` | One-cochains on a singleton cover are multiplicatively equivalent to sections over its double overlap | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.singleton_oneCohomologyRelation_iff` | `RiemannResearch.GaloisCohomology.SingletonCechH1` | Mathlib's singleton-cover gauge relation is equivalent to one universal equation on the double overlap | Kernel checked |
| `RiemannResearch.GaloisCohomology.singletonOneCocycleEquiv` | `RiemannResearch.GaloisCohomology.SingletonCechH1` | Singleton-cover Čech cocycles are equivalent to double-overlap sections satisfying one triple-overlap equation | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.differenceCocycle_isCoboundary_iff` | `RiemannResearch.GaloisCohomology.DifferenceCocycle` | The difference cocycle of two representations is a coboundary exactly when the representations are globally conjugate | Kernel checked |
| `RiemannResearch.GaloisCohomology.restrict_differenceCocycle_isCoboundary_iff` | `RiemannResearch.GaloisCohomology.DifferenceCocycle` | The restricted difference cocycle is a coboundary exactly when the restricted representations are conjugate | Kernel checked |
| `RiemannResearch.GaloisCohomology.transition_fixed_on_subgroup` | `RiemannResearch.GaloisCohomology.TwoGaugeDescent` | Two gauges for the same restricted nonabelian cocycle differ by an element fixed by that subgroup | Kernel checked |
| `RiemannResearch.GaloisCohomology.isCoboundary_iff_transition_factorization` | `RiemannResearch.GaloisCohomology.TwoGaugeDescent` | For two generating subgroups, global coboundary status is equivalent to factorization of the local-gauge transition through the two fixed-point groups | Kernel checked exact reduction; factorization existence remains open in the E8 application |
| `RiemannResearch.GaloisCohomology.NonabelianH1.classOf_eq_neutral_iff_isCoboundary` | `RiemannResearch.GaloisCohomology.NonabelianH1` | A discrete nonabelian cocycle represents the neutral class exactly when it is a coboundary | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.restrict_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | Restriction of discrete nonabelian first cohomology to a subgroup preserves the neutral class | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.map_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | An equivariant group homomorphism sends neutral nonabelian cohomology classes to neutral classes | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianCocycle.transition_fixed_on_inf` | `RiemannResearch.GaloisCohomology.LocalGaugeTransporter` | Local gauges of one nonabelian cocycle have an ordinarily fixed transition on every pairwise subgroup overlap | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianCocycle.isCoboundary_iff_exists_fixedGaugeCorrections` | `RiemannResearch.GaloisCohomology.LocalGaugeTransporter` | For local gauges on a generating family of subgroups, global neutrality is equivalent to factorization of every transition by subgroup-fixed gauge corrections; abstract transporter kernel for full-Weyl EVIII descent | Kernel checked; does not assert that the E8 corrections exist |
| `RiemannResearch.GroupCohomology.h1Conjugation_hom_inv` | `RiemannResearch.GroupCohomology.Conjugation` | Additive H¹ conjugation between a subgroup and its conjugate is an isomorphism, with explicit inverse law | Kernel checked |
| `RiemannResearch.GroupCohomology.h1RestrictionBetween_conjugation` | `RiemannResearch.GroupCohomology.Conjugation` | Canonically transported additive H¹ restriction commutes with subgroup conjugation | Kernel checked |
| `RiemannResearch.GroupCohomology.h1InnerConjugation_eq_id` | `RiemannResearch.GroupCohomology.Conjugation` | Inner conjugation acts trivially on additive first group cohomology | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_conjugation` | `RiemannResearch.GroupCohomology.Conjugation` | Ambient additive H¹ restriction is equivariant for subgroup conjugation after canonical coefficient transport | Kernel checked |
| `RiemannResearch.GroupCohomology.quotientDefect_mul` | `RiemannResearch.GroupCohomology.Corestriction` | The defect of chosen quotient representatives satisfies the multiplicative identity needed by normal corestriction | Kernel checked |
| `RiemannResearch.GroupCohomology.normalCorestrictionCochain_mem_cocycles₁` | `RiemannResearch.GroupCohomology.Corestriction` | The explicit normal finite-index corestriction cochain sends additive one-cocycles to one-cocycles | Kernel checked; descent to H¹ remains open |
| `RiemannResearch.GroupCohomology.h1Restriction_tower` | `RiemannResearch.GroupCohomology.Restriction` | Additive first-cohomology restriction through nested subgroups equals direct restriction | Kernel checked |
| `RiemannResearch.GroupCohomology.h1RestrictionBetween_tower` | `RiemannResearch.GroupCohomology.Restriction` | Restriction between nested subgroup coefficient objects satisfies the transported tower law | Kernel checked |
| `RiemannResearch.GroupCohomology.h1_subsingleton_of_isUnit_fintype_card` | `RiemannResearch.GroupCohomology.StableElements` | Averaging makes additive (H^1) of a finite group trivial when its order is a unit in the coefficient ring | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_injective_of_normal_finiteIndex` | `RiemannResearch.GroupCohomology.StableElements` | Restriction to a normal finite-index subgroup is injective when the index is a unit | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_isStable` | `RiemannResearch.GroupCohomology.StableElements` | Every ambient additive H¹ class restricts to a class satisfying all conjugation/intersection stability equations | Kernel checked |
| `RiemannResearch.GroupCohomology.range_h1Restriction_le_h1StableElements` | `RiemannResearch.GroupCohomology.StableElements` | The image of ambient H¹ restriction lies in the Brown stable-elements submodule | Kernel checked; forward inclusion only |
| `RiemannResearch.LinearAlgebra.regularFunctional_exists_adaptedBase` | `RiemannResearch.LinearAlgebra.RootSystem.AdaptedBase` | A functional nonzero on every root admits a base on whose simple roots it is positive; corrects the PDF's sign-only chamber step | Kernel checked |
| `RiemannResearch.LinearAlgebra.exists_lift_of_rightInverse` | `RiemannResearch.LinearAlgebra.SplitLift` | A split module quotient lifts every map; over a group algebra this is the equivariant lift used by the valuation packet | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_coprime_restrictions` | `RiemannResearch.GroupTheory.CoprimeRestriction` | Two additive restriction maps satisfying coprime restriction--corestriction index formulas jointly detect zero | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_gcd_one_annihilators` | `RiemannResearch.GroupTheory.CoprimeRestriction` | A finite family of annihilating natural degrees with integer gcd one detects zero in an additive commutative group; abstract kernel for PDF Lemma 6.36 | Kernel checked |
| `RiemannResearch.GroupTheory.not_mem_addSubgroup_closure_of_mark` | `RiemannResearch.GroupTheory.BurnsideTopMark` | A class with mark one is not in the additive subgroup generated by classes with mark zero; abstract top-mark kernel for PDF Proposition 6.32 | Kernel checked |
| `RiemannResearch.GroupTheory.BurnsideAdditive.unit_not_mem_span_properTransitiveOrbits` | `RiemannResearch.GroupTheory.BurnsideTopMark` | In the free transitive-orbit presentation of the additive Burnside group of a finite group, the unit `[G/G]` is not generated by the proper orbit classes `[G/H]` with `H < G` | Kernel checked instantiation of PDF Proposition 6.32's top-mark argument |
| `RiemannResearch.GroupTheory.fixed_of_fixed_on_join_eq_top` | `RiemannResearch.GroupTheory.GeneratedFixedPoint` | A common point fixed by two generating subgroups is fixed by the whole group; separate local fixed points are not enough | Kernel checked |
| `RiemannResearch.GroupTheory.iSup_eq_top_of_setGcd_indices` | `RiemannResearch.GroupTheory.GeneratedSubgroupsOfCoprimeIndex` | A family of subgroups whose indices have gcd one generates the whole group | Kernel checked |
| `RiemannResearch.GroupTheory.iSup_comap_eq_top_of_surjective` | `RiemannResearch.GroupTheory.GeneratedSubgroupsOfCoprimeIndex` | Full inverse images of a nonempty generating family under a surjective homomorphism generate the source group | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_cocycle` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | A divisible half-difference `(ell - g·ell)/2` satisfies the one-cocycle identity | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_at_involution` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | At an element acting by minus one, the half-difference cocycle restricts to its chosen lift | Kernel checked |
| `RiemannResearch.GroupTheory.eq_one_of_dvd_three_partition_degrees` | `RiemannResearch.GroupTheory.OrbitDegreeGcd` | A common divisor of three finite degree packets is one when their three total cardinalities have gcd one | Kernel checked |
| `RiemannResearch.GroupTheory.exists_mem_ker_conjugator` | `RiemannResearch.GroupTheory.KernelConjugator` | A source-subgroup element cancelling a conjugator's image moves the conjugator into a homomorphism kernel without changing the conjugated subgroup | Kernel checked |
| `RiemannResearch.GroupTheory.centralSplitMulEquiv` | `RiemannResearch.GroupTheory.CentralExtension` | A section with central kernel identifies the source group with the product of its kernel and target | Kernel checked construction |
| `RiemannResearch.GroupTheory.no_section_of_isPerfect_of_nontrivial_central_ker` | `RiemannResearch.GroupTheory.CentralExtension` | A perfect central extension with nontrivial kernel admits no group-homomorphic section | Kernel checked |
| `RiemannResearch.GroupTheory.stable_derivedSeries_isPerfect` | `RiemannResearch.GroupTheory.PerfectCore` | A stable term of the derived series is perfect | Kernel checked |
| `RiemannResearch.GroupTheory.quotient_isSolvable_of_derivedSeries_le` | `RiemannResearch.GroupTheory.PerfectCore` | A normal subgroup containing a derived-series term has solvable quotient | Kernel checked |
| `RiemannResearch.GroupTheory.stable_derivedSeries_le_of_isSolvable_quotient` | `RiemannResearch.GroupTheory.PerfectCore` | A stable derived-series term lies in every normal subgroup with solvable quotient | Kernel checked |
| `RiemannResearch.GroupTheory.exists_stable_derivedSeries_of_finite_subgroups` | `RiemannResearch.GroupTheory.PerfectCore` | Finiteness of the subgroup type forces adjacent terms of the derived series to stabilize | Kernel checked |
| `RiemannResearch.GroupTheory.exists_nonzero_fixed_modTwo_of_neg_fixed_mod_even` | `RiemannResearch.GroupTheory.ModTwoFixedReduction` | A nonzero negation-fixed class at even modulus in a torsion-free lattice produces a nonzero fixed class modulo two | Kernel checked |
| `RiemannResearch.GroupTheory.fixed_mod_eq_zero_of_negation_and_fixed_modTwo_eq_zero` | `RiemannResearch.GroupTheory.ModTwoFixedReduction` | Central negation and mod-two fixed-space vanishing force fixed-space vanishing at every modulus at least two | Kernel checked |
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
| `RiemannResearch.E8.binaryIcosahedral_orders_and_indices` | `RiemannResearch.E8.BinaryIcosahedralArithmetic` | Checks the order factorization, subgroup product formula, fixed-field degrees 5, 6, and 30, and coprimality | Kernel checked arithmetic |
| `RiemannResearch.E8.not_solvable_of_nontrivial_perfect` | `RiemannResearch.E8.BinaryIcosahedralArithmetic` | A nontrivial perfect group is nonsolvable, guarding against a prime-cyclic normal-tower reduction for `2.A5` | Kernel checked generic implication |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.w_eq_AB_word` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The explicit Appendix-A matrix `w` equals its stated word in `A` and `B` | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.rootGram_eq_d4d4` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The eight certified roots have Gram matrix `D4 ⊕ D4` | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.w_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `w` is a product of reflections in the two certified D4 components | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.j_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `j` is a product of reflections in the two certified D4 components | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.r_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `r` is a product of reflections in the two certified D4 components, disproving uniform triality for this row | Kernel checked finite certificate |
| `RiemannResearch.E8.binaryIcosahedralSubsystemOrbitData_certificate` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks the four projective A5 row labels, complete (D4)^2 and (A4)^2 orbit-histogram totals, and distinct degree keys | Kernel checked embedded certificate; TomLib row/action identification is external |
| `RiemannResearch.E8.binaryIcosahedral_degreeFiveOrbit_multiplicities` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks degree-five orbit multiplicities `[5,5,1,1]` for the four projective A5 rows | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedral_degreeSixOrbit_multiplicities` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks six degree-six (A4)^2 orbits in every projective A5 row | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedral_degreeFiveOrbit_total` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks that the four projective A5 rows have twelve degree-five (D4)^2 orbits in total | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedralSubsystemOrbitData_has_small_orbits` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Every certified projective A5 row has both a degree-five (D4)^2 orbit and a degree-six (A4)^2 orbit | Kernel checked embedded certificate; outer triality is not asserted |
| `RiemannResearch.E8.omegaEightPlusTwoSubsystemFreeClassPositions_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks the 313-to-303 row counts, distinctness, disjointness, and valid TomLib-position range of the embedded sieve data | Kernel checked data consistency; geometric column identification is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreClassData_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks 31 distinct perfect-core rows, total multiplicity 153, 14 distinct orders, and membership among the 303 survivors | Kernel checked data consistency; TomLib association is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks 31 distinct aligned lift rows, doubled orders, perfect lift data, and zero mod-two fixed dimensions | Kernel checked data consistency; cover/module association is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData_order_floor` | `RiemannResearch.E8.SubgroupSieve` | The smallest actual residual lift in the embedded joint certificate has order 120 | Kernel checked data consistency |
| `RiemannResearch.E8.omegaEightPlusTwo_subsystemOrbitDegree_commonDivisor_eq_one` | `RiemannResearch.E8.SubgroupSieve` | Orbit packets summing to 135, 11200, and 12096 have no common degree divisor other than one | Kernel checked conditional packet theorem |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.OmegaEightPlusTwo` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.OmegaEightPlusTwo` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.E8.attractingRank_properties` | `RiemannResearch.E8.WonderfulFixedLocus` | The length-plus-descent formula and Coxeter complement identities imply unique zero rank and rank duality | Kernel checked |
| `RiemannResearch.E8.isRightDescent_longestMul_iff_not` | `RiemannResearch.E8.WonderfulFixedLocus` | A Coxeter length-complement identity exchanges right descents of `w₀w` with right ascents of `w` | Kernel checked |
| `RiemannResearch.E8.coxeterRightDescentCount_one` | `RiemannResearch.E8.WonderfulFixedLocus` | The identity has zero simple right descents in every finitely generated Coxeter system | Kernel checked |
| `RiemannResearch.E8.coxeterRightDescentCount_longestMul_add` | `RiemannResearch.E8.WonderfulFixedLocus` | The length-complement identity forces complementary right-descent counts | Kernel checked |
| `RiemannResearch.E8.coxeterAttractingRank_properties_of_lengthComplement` | `RiemannResearch.E8.WonderfulFixedLocus` | One length-complement identity plus the rank formula gives unique zero rank and full attracting-rank duality | Kernel checked |
| `RiemannResearch.E8.e8AttractingRank_properties_of_lengthComplement` | `RiemannResearch.E8.WonderfulFixedLocus` | For Mathlib's E8 Coxeter group, the single explicit length-complement input implies all Coxeter-rank conclusions of corrected Theorem 3.2 | Kernel checked conditional Coxeter specialization |
| `RiemannResearch.E8.e8AttractingRank_eq_zero_iff` | `RiemannResearch.E8.WonderfulFixedLocus` | On Mathlib's E8 Coxeter group, length plus the number of right descents vanishes exactly at the identity | Kernel checked unconditionally |
| `RiemannResearch.E8.e8_total_attracting_rank` | `RiemannResearch.E8.WonderfulFixedLocus` | Checks the E8 total attracting-rank arithmetic `120 + 8 = 128` | Kernel checked |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Conditional research reductions

These declarations are complete proofs of implications, but they are not
unconditional proofs of the motivating named theorems.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | From the inputs listed below, proves parts (i)--(iii), nonabelianness of the simple core, and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked implication; open obligations remain |
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent_nonabelianH1` | `RiemannResearch.E8.FullWeylCore` | Specializes the conditional assembly to actual discrete nonabelian H¹ and proves the forward restriction-neutrality implication rather than assuming it | Kernel checked implication; remaining E8-specific hypotheses are load-bearing |
| `RiemannResearch.E8.universalFixedLocusAndSplittingField` | `RiemannResearch.E8.WonderfulFixedLocus` | From the inputs listed below, proves the assembled fixed-locus, motivic, point-field, splitting-spectrum, and set-gcd-index conclusions | Kernel checked corrected implication; literal PDF cocharacter normalization fails; open obligations remain |

### Open obligations: `quasisimpleCoreOfFullWeylDescent`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `restriction_preserves_neutrality` | Restriction from the base field preserves neutrality | Removed by `quasisimpleCoreOfFullWeylDescent_nonabelianH1` for actual discrete nonabelian H¹, using `NonabelianH1.restrict_preserves_neutrality`; the finite-Galois/fpqc torsor comparison and algebraic E8 instantiation remain **open** |
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
| `length_zero_iff` | Coxeter length vanishes only at the identity in the supplied model | E8 provider: `e8CoxeterSystem.length_eq_zero_iff` |
| `rightDescent_one` | The identity has no right descents in the supplied model | Provider: `coxeterRightDescentCount_one` |
| `length_duality` | Complementary Coxeter-length identity | **Open** for Mathlib's presented E8 group: no finiteness/longest-element instance currently supplies the required `w₀` |
| `rightDescent_duality` | Complementary right-descent identity | Derived from `length_duality` by `coxeterRightDescentCount_longestMul_add`; no independent obligation remains |
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
