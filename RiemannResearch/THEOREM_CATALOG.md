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

## Open problems

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `RiemannResearch.AlgebraicGeometry.SerreII.Conjecture` | `RiemannResearch.AlgebraicGeometry.SerreIIConjecture` | For every perfect field of cohomological dimension at most two and every semisimple simply connected group, every fpqc H1 class is neutral | **Open problem**; proposition definition only, not asserted as a theorem or axiom |
| `RiemannResearch.AlgebraicGeometry.SerreII.conjecture_iff_subsingleton` | `RiemannResearch.AlgebraicGeometry.SerreIIConjecture` | Identifies the every-class-neutral formulation with H1 being a subsingleton | Kernel-checked formulation lemma; Serre II remains open |

## Established local declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `RiemannResearch.AlgebraicGeometry.SerreII.DynkinFamily.classical_or_exceptional` | `RiemannResearch.AlgebraicGeometry.SerreIINonE8` | Every irreducible Dynkin family in the supplied finite interface is classical or exceptional | Kernel checked finite classification |
| `RiemannResearch.AlgebraicGeometry.SerreII.DynkinFamily.exceptional_iff_e8_or_remainingExceptional` | `RiemannResearch.AlgebraicGeometry.SerreIINonE8` | The exceptional families split into `E8` and the four remaining exceptional types | Kernel checked finite classification |
| `RiemannResearch.AlgebraicGeometry.SerreII.DynkinFamily.ne_e8_iff_classical_or_remainingExceptional` | `RiemannResearch.AlgebraicGeometry.SerreIINonE8` | A family is not `E8` exactly when it is classical or one of `E6`, `E7`, `F4`, `G2` | Kernel checked finite classification; this does not construct a classifier for algebraic groups |
| `RiemannResearch.AlgebraicGeometry.affineGroupSchemeObject_hasGroupObject` | `RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange` | A commutative Hopf algebra represents an affine group object over the spectrum of its base | Kernel checked construction; does not assert smoothness or reductivity |
| `RiemannResearch.AlgebraicGeometry.affineGroupBaseChangeSchemeObject_hasGroupObject` | `RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange` | Tensor-product scalar extension of a commutative Hopf algebra again represents an affine group object | Kernel checked construction |
| `RiemannResearch.E8.BasedE8RootDatum.simpleCartanMatrix_eq_E8` | `RiemannResearch.E8.GroupSchemeFoundation` | A supplied reduced crystallographic root datum with an E8-labelled base has simple-root pairing matrix exactly `CartanMatrix.E₈` | Kernel checked interface theorem; no inhabitant is claimed |
| `RiemannResearch.E8.e8Cartan_mul_inverse` | `RiemannResearch.E8.GroupSchemeFoundation` | The displayed integral matrix is an exact right inverse of Mathlib's E8 Cartan matrix | Kernel checked finite certificate |
| `RiemannResearch.E8.e8Cartan_inverse_mul` | `RiemannResearch.E8.GroupSchemeFoundation` | The displayed integral matrix is an exact left inverse of Mathlib's E8 Cartan matrix | Kernel checked finite certificate |
| `RiemannResearch.E8.e8Cartan_det_isUnit` | `RiemannResearch.E8.GroupSchemeFoundation` | The E8 Cartan determinant is a unit over the integers | Kernel checked consequence |
| `RiemannResearch.E8.e8CartanLinearEquiv` | `RiemannResearch.E8.GroupSchemeFoundation` | The E8 Cartan matrix defines an integral linear automorphism | Kernel checked construction |
| `RiemannResearch.E8.e8CartanDuality_isPerfPair` | `RiemannResearch.E8.GroupSchemeFoundation` | The integral E8 Cartan pairing is a perfect pairing of the coordinate root lattice with its dual | Kernel checked lattice foundation; not a constructed root datum |
| `RiemannResearch.E8.e8CartanDuality_apply` | `RiemannResearch.E8.GroupSchemeFoundation` | The perfect pairing evaluates as E8 Cartan matrix multiplication followed by the standard dot product | Kernel checked formula |
| `RiemannResearch.E8.e8SimpleRoot_pairing_self` | `RiemannResearch.E8.GroupSchemeFoundation` | Every coordinate simple root has E8 Cartan self-pairing two | Kernel checked coordinate calculation |
| `RiemannResearch.E8.e8SimpleReflection_apply` | `RiemannResearch.E8.GroupSchemeFoundation` | The integral simple reflections attached to the coordinate roots satisfy the standard root-datum reflection formula | Kernel checked lattice construction; no Weyl-group or group-scheme identification is claimed |
| `RiemannResearch.E8.e8SerreLieAlgebra_eq_toLieAlgebra` | `RiemannResearch.E8.GroupSchemeFoundation` | Mathlib's E8 Lie algebra is the Serre quotient for the explicit E8 Cartan matrix | Kernel checked definitional equality; not an integration to a group scheme |
| `sanity_check` | `RiemannResearch.Basic` | Confirms arithmetic tactics and mathlib are available | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcCover.Refinement.pullbackH1_one` | `RiemannResearch.AlgebraicGeometry.FpqcCechPullback` | Refinement pullback on fixed-cover nonabelian Čech H¹ preserves the neutral class | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcCechH1.IsNeutral.pullback` | `RiemannResearch.AlgebraicGeometry.FpqcCechH1` | A neutral affine-group-scheme Čech class remains neutral after refining its witnessed fpqc cover | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcCover.commonRefinementData` | `RiemannResearch.AlgebraicGeometry.FpqcCoverCommonRefinement` | Any two witnessed indexed fpqc covers of `Spec R` have a pairwise-pullback common cover and refinement maps to both inputs | Kernel checked construction |
| `RiemannResearch.AlgebraicGeometry.FpqcCover.Refinement.pullbackH1_eq` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Any two refinement maps with the same source and target induce the same map on nonabelian Čech H¹ | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1Representative.equivalent_trans` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Equality of fixed-cover classes after witnessed common refinement is transitive | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1.classOf_eq_iff` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | Two fixed-cover classes define the same global fpqc Čech H¹ class exactly when they agree on a witnessed common refinement | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1.classOf_neutral` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | The neutral class on every witnessed fpqc cover maps to the distinguished global neutral class | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.FpqcH1.classOf_eq_neutral_iff_exists_refinement` | `RiemannResearch.AlgebraicGeometry.FpqcH1` | A fixed-cover class is globally neutral exactly when it becomes neutral on one witnessed refinement | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.isSimplyTransitive_iff` | `RiemannResearch.AlgebraicGeometry.FpqcTorsor` | A group action is simply transitive exactly when a unique group element carries any generalized torsor point to any other | Kernel checked; `FpqcTorsor` packages this with flat, surjective, quasi-compact structure morphism |
| `CategoryTheory.ModObj.orbitMap_isModHom` | `RiemannResearch.AlgebraicGeometry.FpqcTorsor` | The orbit map determined by a global point is equivariant for the regular action on the acting monoid | Kernel checked |
| `CategoryTheory.ModObj.isIso_orbitMap` | `RiemannResearch.AlgebraicGeometry.FpqcTorsor` | A global point of a simply transitive internal module object has an isomorphic orbit map | Kernel checked |
| `CategoryTheory.ModObj.orbitModIso` | `RiemannResearch.AlgebraicGeometry.FpqcTorsor` | A chosen global point gives an equivariant isomorphism from the regular module to a simply transitive internal module object | Kernel checked construction |
| `RiemannResearch.AlgebraicGeometry.fpqcTorsorTrivializationOfSection` | `RiemannResearch.AlgebraicGeometry.FpqcTorsor` | A global section of an fpqc scheme torsor gives an equivariant trivialization by the regular torsor | Kernel checked construction; effective fpqc descent and the global torsor/Čech-`H¹` equivalence remain open |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equality of rational-point predicates implies equality of the set-gcd indices of all finite point-field degrees | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointDescentAt` | `RiemannResearch.AlgebraicGeometry.PointFields` | Packages descent of a point from every extension in a specified admissible class back to a fixed base | Established local definition |
| `RiemannResearch.AlgebraicGeometry.pointDescentAt_iff_of_pointwise_iff` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equivalent point predicates have equivalent descent properties along any specified class of extensions | Kernel checked with no axioms |
| `RiemannResearch.AlgebraicGeometry.setGcd_eq_one_of_forall_prime_exists_not_dvd` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | A natural-number degree set has gcd one when every prime is avoided by some member | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq_one_of_prime_avoidance` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | Avoiding each prime by some finite point-field degree forces point-field index one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq_one_of_two_point_degrees` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | Two actual finite point fields of coprime degrees force the point-field index to equal one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq_one_of_three_point_degrees` | `RiemannResearch.AlgebraicGeometry.PointFieldIndexOne` | Three actual finite point fields with gcd one force the point-field index to equal one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.one_mem_of_setGcd_eq_one_of_prime_powers` | `RiemannResearch.AlgebraicGeometry.PrimePowerIndex` | A prime-power degree set with gcd one contains degree one | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.degree_one_pointField_exists_of_prime_power_degrees` | `RiemannResearch.AlgebraicGeometry.PrimePowerIndex` | Prime-power finite point degrees and point-field index one produce an actual degree-one point field | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.closedPointIndex_eq_pointFieldIndex` | `RiemannResearch.AlgebraicGeometry.PointFields` | Identifies the traditional closed-point gcd with the splitting-field gcd under the residue-field and closed-image divisibility hypotheses | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.point_iff_of_fixedLocus_coproduct` | `RiemannResearch.AlgebraicGeometry.PointFields` | A proper-limit map, coproduct fixed locus, and fixed-component inclusion give equality of point fields | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.comp` | `RiemannResearch.Logic.PointedKernel` | Trivial neutral fibers compose through a tower of pointed maps | Kernel checked |
| `RiemannResearch.Logic.IsPointedExact.hasTrivialKernel_of_subsingleton_left` | `RiemannResearch.Logic.PointedKernel` | Pointed exactness with a subsingleton left term gives a trivial neutral fiber; abstract step in Gille survey Proposition 3.2(1) | Kernel checked |
| `RiemannResearch.Logic.IsPointedExact.surjective_left_of_subsingleton_right` | `RiemannResearch.Logic.PointedKernel` | Pointed exactness with a subsingleton right term makes the left map surjective | Kernel checked |
| `RiemannResearch.Logic.IsPointedExact.of_injective_vertical` | `RiemannResearch.Logic.PointedKernel` | Pulls pointed exactness up a commutative diagram along an injective vertical map; abstract diagram chase from Gille survey Lemma 6.4 | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.invariant_eq_iff_of_twist` | `RiemannResearch.Logic.PointedKernel` | A compatible twisting equivalence transports a trivial boundary fiber into invariant-based basepoint detection; abstract step in Gille survey Proposition 3.2(2) | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.subsingleton_domain_of_subsingleton_codomain` | `RiemannResearch.Logic.PointedKernel` | A trivial-kernel invariant with subsingleton target has subsingleton source | Kernel checked |
| `RiemannResearch.Logic.eq_basepoint_of_gcd_one_annihilated_invariant` | `RiemannResearch.Logic.PointedInvariant` | Gcd-one annihilation plus a trivial-kernel additive invariant detects the distinguished point | Kernel checked |
| `RiemannResearch.Logic.HasTrivialKernel.tower` | `RiemannResearch.Logic.PointedKernel` | Trivial neutral fibers iterate through every finite dependent tower of pointed maps | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTensorDecomposition` | The canonical finite-Galois equivalence `L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L)` evaluates `x ⊗ y` at `σ` as `x * σ y` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisTripleTensorEquiv_tmul_apply` | `RiemannResearch.GaloisCohomology.GaloisTripleTensorDecomposition` | The triple-overlap equivalence evaluates `x ⊗ (y ⊗ z)` at independent `(σ, ρ)` as `x * σ y * ρ z` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisDoubleOverlapPointMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | Affine-group points on the finite-Galois double overlap are multiplicatively equivalent to Galois-indexed L-points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.galoisTripleOverlapPointMulEquiv` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | Affine-group points on the triple overlap are multiplicatively equivalent to two-variable Galois-indexed L-points | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.galoisCechFace12_point` | `RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates` | The one-two affine Čech face is the twisted Galois projection `σ • f (σ⁻¹ρ)` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisCechFace12_eval` | `RiemannResearch.GaloisCohomology.GaloisCechCoordinates` | In Galois coordinates, the twisted Čech face evaluates as `σ (f (σ⁻¹ρ))` | Kernel checked |
| `RiemannResearch.GaloisCohomology.galoisCechCocycleEquiv` | `RiemannResearch.GaloisCohomology.GaloisCechCoordinates` | The coordinate Čech cocycle equation is equivalent to the inhomogeneous nonabelian group-cocycle equation | Kernel checked equivalence |
| `RiemannResearch.GaloisCohomology.GaloisCechH1.equivNonabelian` | `RiemannResearch.GaloisCohomology.GaloisCechCoordinates` | Coordinate finite-Galois Čech H¹ is pointed-equivalent to discrete nonabelian H¹ | Kernel checked equivalence |
| `RiemannResearch.AlgebraicGeometry.finiteGaloisFpqcCover` | `RiemannResearch.AlgebraicGeometry.FiniteGaloisFpqcCover` | A finite Galois field extension supplies the witnessed singleton fpqc cover of affine spectra | Kernel checked construction |
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
| `RiemannResearch.GaloisCohomology.differenceCocycle_twoGaugeCounterexample` | `RiemannResearch.GaloisCohomology.DifferenceCocycle` | Two local simultaneous conjugacies together with failure of global conjugacy give a nonneutral nonabelian H¹ class whose two restrictions are neutral | Kernel checked exact deduction |
| `RiemannResearch.GaloisCohomology.transition_fixed_on_subgroup` | `RiemannResearch.GaloisCohomology.TwoGaugeDescent` | Two gauges for the same restricted nonabelian cocycle differ by an element fixed by that subgroup | Kernel checked |
| `RiemannResearch.GaloisCohomology.isCoboundary_iff_transition_factorization` | `RiemannResearch.GaloisCohomology.TwoGaugeDescent` | For two generating subgroups, global coboundary status is equivalent to factorization of the local-gauge transition through the two fixed-point groups | Kernel checked exact reduction; factorization existence remains open in the E8 application |
| `RiemannResearch.GaloisCohomology.NonabelianH1.classOf_eq_neutral_iff_isCoboundary` | `RiemannResearch.GaloisCohomology.NonabelianH1` | A discrete nonabelian cocycle represents the neutral class exactly when it is a coboundary | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.restrict_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | Restriction of discrete nonabelian first cohomology to a subgroup preserves the neutral class | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianH1.map_preserves_neutrality` | `RiemannResearch.GaloisCohomology.NonabelianH1` | An equivariant group homomorphism sends neutral nonabelian cohomology classes to neutral classes | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianCocycle.transition_fixed_on_inf` | `RiemannResearch.GaloisCohomology.LocalGaugeTransporter` | Local gauges of one nonabelian cocycle have an ordinarily fixed transition on every pairwise subgroup overlap | Kernel checked |
| `RiemannResearch.GaloisCohomology.NonabelianCocycle.isCoboundary_iff_exists_fixedGaugeCorrections` | `RiemannResearch.GaloisCohomology.LocalGaugeTransporter` | For local gauges on a generating family of subgroups, global neutrality is equivalent to factorization of every transition by subgroup-fixed gauge corrections; abstract transporter kernel for full-Weyl EVIII descent | Kernel checked; does not assert that the E8 corrections exist |
| `RiemannResearch.GaloisCohomology.NonabelianCocycle.isCoboundary_iff_exists_anchoredFixedGaugeCorrection` | `RiemannResearch.GaloisCohomology.LocalGaugeTransporter` | After choosing one anchor gauge, global neutrality is equivalent to one anchor element whose translate by each local transition is fixed by the corresponding subgroup; all pairwise correction equations then follow automatically | Kernel checked exact reduction; existence of the anchor for the 135 E8/D8 gauges remains open |
| `RiemannResearch.GroupCohomology.h1Conjugation_hom_inv` | `RiemannResearch.GroupCohomology.Conjugation` | Additive H¹ conjugation between a subgroup and its conjugate is an isomorphism, with explicit inverse law | Kernel checked |
| `RiemannResearch.GroupCohomology.h1RestrictionBetween_conjugation` | `RiemannResearch.GroupCohomology.Conjugation` | Canonically transported additive H¹ restriction commutes with subgroup conjugation | Kernel checked |
| `RiemannResearch.GroupCohomology.h1InnerConjugation_eq_id` | `RiemannResearch.GroupCohomology.Conjugation` | Inner conjugation acts trivially on additive first group cohomology | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_conjugation` | `RiemannResearch.GroupCohomology.Conjugation` | Ambient additive H¹ restriction is equivariant for subgroup conjugation after canonical coefficient transport | Kernel checked |
| `RiemannResearch.GroupCohomology.exists_mackey_decomposition` | `RiemannResearch.GroupCohomology.Mackey` | Every group element is a left-right translate of the chosen representative of its Mackey double coset | Kernel checked |
| `RiemannResearch.GroupCohomology.mackeyIntersectionEquiv` | `RiemannResearch.GroupCohomology.Mackey` | Conjugation identifies `H ∩ g⁻¹Kg` with `K ∩ gHg⁻¹`, the two intersection groups in a Mackey summand | Kernel checked equivalence |
| `RiemannResearch.GroupCohomology.conjugateSubgroup_eq_self_of_normal` | `RiemannResearch.GroupCohomology.Mackey` | A normal subgroup is fixed by the explicit conjugate-subgroup construction | Kernel checked |
| `RiemannResearch.GroupCohomology.quotientDefect_mul` | `RiemannResearch.GroupCohomology.Corestriction` | The defect of chosen quotient representatives satisfies the multiplicative identity needed by normal corestriction | Kernel checked |
| `RiemannResearch.GroupCohomology.normalCorestrictionCochain_mem_cocycles₁` | `RiemannResearch.GroupCohomology.Corestriction` | The explicit normal finite-index corestriction cochain sends additive one-cocycles to one-cocycles | Kernel checked |
| `RiemannResearch.GroupCohomology.normalCorestrictionCochain_d₀₁_apply` | `RiemannResearch.GroupCohomology.Corestriction` | Corestriction of an additive one-coboundary is the coboundary of the explicit transferred potential | Kernel checked |
| `RiemannResearch.GroupCohomology.normalCorestrictionCochain_mem_coboundaries₁` | `RiemannResearch.GroupCohomology.Corestriction` | The normal finite-index additive corestriction formula sends one-coboundaries to one-coboundaries | Kernel checked |
| `RiemannResearch.GroupCohomology.normalCorestrictionCocyclesLinearMap_maps_toCyclesRange` | `RiemannResearch.GroupCohomology.Corestriction` | Additive normal corestriction respects the coboundary ranges in the explicit short-complex models | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Corestriction` | `RiemannResearch.GroupCohomology.Corestriction` | Normal finite-index corestriction descends to Mathlib's additive first group cohomology | Kernel checked; this is not a transfer on nonabelian H¹ |
| `RiemannResearch.GroupCohomology.normalCorestrictionCochain_restrict_apply` | `RiemannResearch.GroupCohomology.Corestriction` | On additive cocycles, corestriction after restriction is index multiplication plus an explicit coboundary | Kernel checked; cochain-level restriction–corestriction identity |
| `RiemannResearch.GroupCohomology.h1RestrictionViaCocycles_comp_h1Corestriction` | `RiemannResearch.GroupCohomology.Corestriction` | Restriction followed by normal corestriction is multiplication by the subgroup index on additive first group cohomology | Kernel checked; quotient-level restriction–corestriction identity, not a nonabelian H¹ operation |
| `RiemannResearch.GroupCohomology.h1Restriction_tower` | `RiemannResearch.GroupCohomology.Restriction` | Additive first-cohomology restriction through nested subgroups equals direct restriction | Kernel checked |
| `RiemannResearch.GroupCohomology.h1RestrictionBetween_tower` | `RiemannResearch.GroupCohomology.Restriction` | Restriction between nested subgroup coefficient objects satisfies the transported tower law | Kernel checked |
| `RiemannResearch.GroupCohomology.h1_subsingleton_of_isUnit_fintype_card` | `RiemannResearch.GroupCohomology.StableElements` | Averaging makes additive (H^1) of a finite group trivial when its order is a unit in the coefficient ring | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_injective_of_normal_finiteIndex` | `RiemannResearch.GroupCohomology.StableElements` | Restriction to a normal finite-index subgroup is injective when the index is a unit | Kernel checked |
| `RiemannResearch.GroupCohomology.h1Restriction_isStable` | `RiemannResearch.GroupCohomology.StableElements` | Every ambient additive H¹ class restricts to a class satisfying all conjugation/intersection stability equations | Kernel checked |
| `RiemannResearch.GroupCohomology.range_h1Restriction_le_h1StableElements` | `RiemannResearch.GroupCohomology.StableElements` | The image of ambient H¹ restriction lies in the Brown stable-elements submodule | Kernel checked; forward inclusion only |
| `RiemannResearch.LinearAlgebra.regularFunctional_exists_adaptedBase` | `RiemannResearch.LinearAlgebra.RootSystem.AdaptedBase` | A functional nonzero on every root admits a base on whose simple roots it is positive; formalizes the equivalent adapted-base/reindexing convention | Kernel checked |
| `RiemannResearch.LinearAlgebra.exists_lift_of_rightInverse` | `RiemannResearch.LinearAlgebra.SplitLift` | A split module quotient lifts every map; over a group algebra this is the equivariant lift used by the valuation packet | Kernel checked |
| `RiemannResearch.LinearAlgebra.mapQ_comp_eq_nsmul_id` | `RiemannResearch.LinearAlgebra.QuotientMap` | A composite induced on submodule quotients is index multiplication when its lift differs from index multiplication by the source submodule | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_coprime_restrictions` | `RiemannResearch.GroupTheory.CoprimeRestriction` | Two additive restriction maps satisfying coprime restriction--corestriction index formulas jointly detect zero | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_gcd_one_annihilators` | `RiemannResearch.GroupTheory.CoprimeRestriction` | A finite family of annihilating natural degrees with integer gcd one detects zero in an additive commutative group; abstract kernel for PDF Lemma 6.36 | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_gcd_one_restrictions` | `RiemannResearch.GroupTheory.CoprimeRestriction` | A finite family of additive restrictions with gcd-one restriction--corestriction degrees jointly detects zero | Kernel checked |
| `RiemannResearch.GroupTheory.hasTrivialKernel_restrictionFamily_of_gcd_one` | `RiemannResearch.GroupTheory.CoprimeRestriction` | The joint finite-family additive restriction map has trivial pointed kernel under a gcd-one index formula | Kernel checked |
| `RiemannResearch.GroupTheory.not_mem_addSubgroup_closure_of_mark` | `RiemannResearch.GroupTheory.BurnsideTopMark` | A class with mark one is not in the additive subgroup generated by classes with mark zero; abstract top-mark kernel for PDF Proposition 6.32 | Kernel checked |
| `RiemannResearch.GroupTheory.BurnsideAdditive.unit_not_mem_span_properTransitiveOrbits` | `RiemannResearch.GroupTheory.BurnsideTopMark` | In the free transitive-orbit presentation of the additive Burnside group of a finite group, the unit `[G/G]` is not generated by the proper orbit classes `[G/H]` with `H < G` | Kernel checked instantiation of PDF Proposition 6.32's top-mark argument |
| `RiemannResearch.GroupTheory.fixed_of_fixed_on_join_eq_top` | `RiemannResearch.GroupTheory.GeneratedFixedPoint` | A common point fixed by two generating subgroups is fixed by the whole group; separate local fixed points are not enough | Kernel checked |
| `RiemannResearch.GroupTheory.quotientGeneration_counterexample` | `RiemannResearch.GroupTheory.QuotientGeneration` | A two-primary lift maps onto a finite quotient without generating the ambient group; adjoining the quotient kernel restores generation, exposing and repairing the omitted-kernel step after PDF Proposition 7.5 | Kernel checked finite counterexample |
| `RiemannResearch.GroupTheory.iSup_eq_top_of_setGcd_indices` | `RiemannResearch.GroupTheory.GeneratedSubgroupsOfCoprimeIndex` | A family of subgroups whose indices have gcd one generates the whole group | Kernel checked |
| `RiemannResearch.GroupTheory.iSup_comap_eq_top_of_surjective` | `RiemannResearch.GroupTheory.GeneratedSubgroupsOfCoprimeIndex` | Full inverse images of a nonempty generating family under a surjective homomorphism generate the source group | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_cocycle` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | A divisible half-difference `(ell - g·ell)/2` satisfies the one-cocycle identity | Kernel checked |
| `RiemannResearch.GroupTheory.halfDifference_at_involution` | `RiemannResearch.GroupTheory.HalfDifferenceCocycle` | At an element acting by minus one, the half-difference cocycle restricts to its chosen lift | Kernel checked |
| `RiemannResearch.GroupTheory.eq_one_of_dvd_three_partition_degrees` | `RiemannResearch.GroupTheory.OrbitDegreeGcd` | A common divisor of three finite degree packets is one when their three total cardinalities have gcd one | Kernel checked |
| `RiemannResearch.GroupTheory.exists_mem_ker_conjugator` | `RiemannResearch.GroupTheory.KernelConjugator` | A source-subgroup element cancelling a conjugator's image moves the conjugator into a homomorphism kernel without changing the conjugated subgroup | Kernel checked |
| `RiemannResearch.GroupTheory.exists_mem_ker_pointwiseConjugator` | `RiemannResearch.GroupTheory.KernelConjugator` | A centralizer element with cancelling image moves a simultaneous pointwise conjugator into a homomorphism kernel | Kernel checked |
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
| `RiemannResearch.E8.A11BurnsideCertificate.burnsideRestriction_certificate` | `RiemannResearch.E8.A11BurnsideCertificate` | Checks both printed Burnside restriction-kernel equations entry by entry | Kernel checked embedded certificate |
| `RiemannResearch.E8.A11BurnsideCertificate.actionOrbitData_certificate` | `RiemannResearch.E8.A11BurnsideCertificate` | Checks that the two eleven-point actions have distinct global orbit packets | Kernel checked embedded certificate |
| `RiemannResearch.E8.A11BurnsideCertificate.globalActionGenerators_certificate` | `RiemannResearch.E8.A11BurnsideCertificate` | Checks validity and even parity of every printed global action generator | Kernel checked embedded certificate |
| `RiemannResearch.E8.A11BurnsideCertificate.localEvenConjugators_certificate` | `RiemannResearch.E8.A11BurnsideCertificate` | Checks odd-centralizer parity corrections and explicit simultaneous even local conjugators | Kernel checked embedded certificate; GAP row/action identification remains external |
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
| `RiemannResearch.E8.RationalInvolutionsAudit.incidence_row_sum` | `RiemannResearch.E8.RationalInvolutionsAudit` | Every row of the 15 by 15 complement-incidence matrix has sum eight | Kernel checked by finite decision |
| `RiemannResearch.E8.RationalInvolutionsAudit.incidence_gram` | `RiemannResearch.E8.RationalInvolutionsAudit` | Entrywise certificate for B B-transpose = 4(I+J) in Proposition 16.1(1) | Kernel checked by finite decision |
| `RiemannResearch.E8.RationalInvolutionsAudit.tits_binary_certificate` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the five-row XOR certificate (14.3) | Kernel checked by finite decision |
| `RiemannResearch.E8.RationalInvolutionsAudit.s4_overlap_binary_certificate` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the S4 overlap XOR certificate (14.4), whose value is 2^32 | Kernel checked by finite decision |
| `RiemannResearch.E8.RationalInvolutionsAudit.kleinFour_binary_certificate` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the minimal Klein-four inconsistency certificate (14.9) | Kernel checked by finite decision |
| `RiemannResearch.E8.RationalInvolutionsAudit.degree56OrbitDeterminant_divisible_by_sixteen` | `RiemannResearch.E8.RationalInvolutionsAudit` | The determinant polynomial (14.5) is always divisible by 16 | Kernel checked |
| `RiemannResearch.E8.RationalInvolutionsAudit.degree56OrbitDeterminant_minimizer` | `RiemannResearch.E8.RationalInvolutionsAudit` | The printed vector (-1,-1,0,-2) attains determinant 16 | Kernel checked |
| `RiemannResearch.E8.RationalInvolutionsAudit.cartanTransporter_dimension_arithmetic` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks all numerical dimension identities in Propositions 6.7-6.8 | Kernel checked arithmetic |
| `RiemannResearch.E8.RationalInvolutionsAudit.cartanTransporter_cubicEquation_count` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the count 1,255,296 of displayed cubic transporter equations | Kernel checked arithmetic |
| `RiemannResearch.E8.RationalInvolutionsAudit.finiteCohomology_rank_arithmetic` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the dimension subtractions in the finite cohomology audit | Kernel checked arithmetic; matrix-rank inputs remain external |
| `RiemannResearch.E8.RationalInvolutionsAudit.packetStabilizer_order_arithmetic` | `RiemannResearch.E8.RationalInvolutionsAudit` | Checks the degree-15 and degree-35 stabilizer orders and factor-of-ten correction | Kernel checked arithmetic; group identifications remain external |
| `RiemannResearch.E8.RationalInvolutionsAudit.sylowSeven_order` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | The explicit hyperbolic-model isometry (14.12) has exact order seven | Kernel checked exhaustive certificate |
| `RiemannResearch.E8.RationalInvolutionsAudit.nonzero_singular_card` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | The packed plus-type eight-space has 135 nonzero singular vectors | Kernel checked exhaustive certificate |
| `RiemannResearch.E8.RationalInvolutionsAudit.singular_fixed_points` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | The order-seven element fixes exactly two singular points | Kernel checked exhaustive certificate |
| `RiemannResearch.E8.RationalInvolutionsAudit.seven_orbit_sum_distribution` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | Checks the exact 5,5,5,4 seven-orbit sum distribution (14.13) | Kernel checked exhaustive certificate |
| `RiemannResearch.E8.RationalInvolutionsAudit.balanced_orbits_orthogonal_to_r` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | Every zero-sum seven-orbit is perpendicular to the fixed nonsingular vector | Kernel checked exhaustive certificate |
| `RiemannResearch.E8.RationalInvolutionsAudit.atomic_partition_card` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | Checks the 15 + 120 singular-vector partition in the displayed U plus U-dual model | Kernel checked exhaustive certificate; transitivity is not asserted |
| `RiemannResearch.E8.RationalInvolutionsAudit.atomic_partition_vector_sums` | `RiemannResearch.E8.SylowSevenHyperbolicModel` | Both pieces of the 15 + 120 partition have vector sum zero | Kernel checked exhaustive certificate |
| `RiemannResearch.GroupTheory.commutative_of_two_factor_norm` | `RiemannResearch.GroupTheory.TwoFactorNorm` | Proposition 10.7: a two-factor norm restricting to each identity map forces commutativity | Kernel checked |
| `RiemannResearch.GroupCohomology.odd_degree_restriction_injective_mod_two` | `RiemannResearch.GroupCohomology.OddDegreeRestrictionModTwo` | Additive restriction-corestriction proof of odd-degree injectivity modulo two (Theorem 10.35) | Kernel checked |
| `RiemannResearch.GroupCohomology.boundary_fiber_is_kernel_torsor` | `RiemannResearch.GroupCohomology.BoundaryFiber` | A nonempty boundary fiber is freely and transitively parametrized by the kernel, the formal torsor core of Theorem 10.51 | Kernel checked |
| `RiemannResearch.E8.a2Coroot_sign_normalization_counterexample` | `RiemannResearch.E8.A2ChamberNormalization` | The A2 simple coroot is regular but neither sign is positive on both fixed simple roots; this guards against a literal arbitrary-cocharacter reading, while Theorem 3.2 uses a cocharacter chosen in the Borel chamber | Kernel checked finite calculation |
| `RiemannResearch.GroupTheory.alternatingGroup_fin_five_card` | `RiemannResearch.GroupTheory.AlternatingFiveObstruction` | The alternating group on five letters has order 60 | Kernel checked |
| `RiemannResearch.GroupTheory.alternatingGroup_fin_five_card_prime_support` | `RiemannResearch.GroupTheory.AlternatingFiveObstruction` | The order of A5 is `2^2 · 3 · 5`, within Gille's printed prime support | Kernel checked |
| `RiemannResearch.GroupTheory.alternatingGroup_fin_five_not_solvable` | `RiemannResearch.GroupTheory.AlternatingFiveObstruction` | A5 is nonsolvable, so a cyclic-prime tower induction does not cover every Galois group allowed by the printed degree hypothesis | Kernel checked proof-gap certificate; not a counterexample to the cohomological theorem |
| `RiemannResearch.E8.serreIIProgram_fullWeylSubsystem_index_products` | `RiemannResearch.E8.SubgroupSieve` | Checks the three E8 Weyl stabilizer index products for PDF Theorem 5.16 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_threeSubsystem_bezout` | `RiemannResearch.E8.SubgroupSieve` | Checks `-1417·135 + 16·11200 + 12096 = 1` from PDF Corollary 5.17 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_threeSubsystem_gcd` | `RiemannResearch.E8.SubgroupSieve` | Checks that 135, 11200, and 12096 have gcd one | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_field_degrees` | `RiemannResearch.E8.A8NormalizerArithmetic` | Checks the degree-105 overlap and degree-4032 Sylow-five fields in PDF Proposition 6.7 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_bezout` | `RiemannResearch.E8.A8NormalizerArithmetic` | Supplies an exact integral Bezout identity for 15, 35, and 4032 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_a8Gauge_gcd` | `RiemannResearch.E8.A8NormalizerArithmetic` | Checks that 15, 35, and 4032 have gcd one | Kernel checked arithmetic |
| `RiemannResearch.E8.eq_zero_of_serreIIProgram_a8Gauge_annihilators` | `RiemannResearch.E8.A8NormalizerArithmetic` | An abelian class killed by 15, 35, and 4032 is zero | Kernel checked additive shadow |
| `RiemannResearch.E8.serreIIProgram_survivorEnvelope_bezout` | `RiemannResearch.E8.SubgroupSieve` | Checks all five displayed Bezout rows in PDF Theorem 6.9 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_survivorEnvelope_gcd` | `RiemannResearch.E8.SubgroupSieve` | Checks the gcd-one assertion for all five degree rows in PDF Theorem 6.9 | Kernel checked arithmetic |
| `RiemannResearch.E8.serreIIProgram_binaryIcosahedral_index_arithmetic` | `RiemannResearch.E8.BinaryIcosahedralArithmetic` | Checks the elementary order and index arithmetic in PDF Proposition 6.15 | Kernel checked arithmetic |
| `RiemannResearch.E8.sectionSevenAppendix_arithmetic` | `RiemannResearch.E8.SectionSevenAppendixAudit` | Checks the printed Section 7 and Appendix A count, orbit-cardinality, and binary-icosahedral order arithmetic | Kernel checked arithmetic; GAP enumeration inputs remain external |
| `RiemannResearch.E8.sectionSevenAppendix_bezout_and_gcd` | `RiemannResearch.E8.SectionSevenAppendixAudit` | Checks the full-Weyl and survivor-envelope Bezout identities and all five corresponding gcd-one calculations | Kernel checked arithmetic |
| `RiemannResearch.E8.binaryIcosahedral_orders_and_indices` | `RiemannResearch.E8.BinaryIcosahedralArithmetic` | Checks the order factorization, subgroup product formula, fixed-field degrees 5, 6, and 30, and coprimality | Kernel checked arithmetic |
| `RiemannResearch.E8.not_solvable_of_nontrivial_perfect` | `RiemannResearch.E8.BinaryIcosahedralArithmetic` | A nontrivial perfect group is nonsolvable, guarding against a prime-cyclic normal-tower reduction for `2.A5` | Kernel checked generic implication |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.w_eq_AB_word` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The explicit Appendix-A matrix `w` equals its stated word in `A` and `B` | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.rootGram_eq_d4d4` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The eight certified roots have Gram matrix `D4 ⊕ D4` | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.w_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `w` is a product of reflections in the two certified D4 components | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.j_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `j` is a product of reflections in the two certified D4 components | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.r_eq_reflections` | `RiemannResearch.E8.BinaryIcosahedralAtlas` | The generator `r` is a product of reflections in the two certified D4 components, disproving uniform triality for this row | Kernel checked finite certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.a_preserves_Q` | `RiemannResearch.E8.BinaryIcosahedralTrialityCounterexample` | The first ATLAS generator preserves the displayed integral E8 form | Kernel checked matrix certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.b_preserves_Q` | `RiemannResearch.E8.BinaryIcosahedralTrialityCounterexample` | The second ATLAS generator preserves the displayed integral E8 form | Kernel checked matrix certificate |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.binaryTetrahedralMatrixMonoid_le_certifiedInnerD4xD4` | `RiemannResearch.E8.BinaryIcosahedralTrialityCounterexample` | Every matrix generated by the displayed binary-tetrahedral stabilizer generators lies in the inner `W(D4) × W(D4)` reflection image | Kernel checked exact matrix implication |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.r_orderThree_innerD4xD4_counterexample` | `RiemannResearch.E8.BinaryIcosahedralTrialityCounterexample` | The nonidentity order-three stabilizer matrix lies in the inner reflection image, contradicting universal outer triality | Kernel checked matrix counterexample; GAP/TomLib narrows the row to `{4015,4017}`, each with a unique degree-five orbit |
| `RiemannResearch.E8.BinaryIcosahedralAtlas.not_all_nontrivial_orderThree_stabilizerElements_outer` | `RiemannResearch.E8.BinaryIcosahedralTrialityCounterexample` | Not every nonidentity order-three stabilizer element lies outside the certified inner image | Kernel checked formal negation |
| `RiemannResearch.E8.binaryIcosahedralSubsystemOrbitData_certificate` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks the four projective A5 row labels, complete (D4)^2 and (A4)^2 orbit-histogram totals, and distinct degree keys | Kernel checked embedded certificate; TomLib row/action identification is external |
| `RiemannResearch.E8.binaryIcosahedral_degreeFiveOrbit_multiplicities` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks degree-five orbit multiplicities `[5,5,1,1]` for the four projective A5 rows | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedral_degreeSixOrbit_multiplicities` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks six degree-six (A4)^2 orbits in every projective A5 row | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedral_degreeFiveOrbit_total` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Checks that the four projective A5 rows have twelve degree-five (D4)^2 orbits in total | Kernel checked embedded certificate |
| `RiemannResearch.E8.binaryIcosahedralSubsystemOrbitData_has_small_orbits` | `RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits` | Every certified projective A5 row has both a degree-five (D4)^2 orbit and a degree-six (A4)^2 orbit | Kernel checked embedded certificate; universal outer triality is separately refuted |
| `RiemannResearch.E8.omegaEightPlusTwoSubsystemFreeClassPositions_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks the 313-to-303 row counts, distinctness, disjointness, and valid TomLib-position range of the embedded sieve data | Kernel checked data consistency; geometric column identification is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreClassData_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks 31 distinct perfect-core rows, total multiplicity 153, 14 distinct orders, and membership among the 303 survivors | Kernel checked data consistency; TomLib association is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData_certificate` | `RiemannResearch.E8.SubgroupSieve` | Checks 31 distinct aligned lift rows, doubled orders, perfect lift data, and zero mod-two fixed dimensions | Kernel checked data consistency; cover/module association is external |
| `RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData_order_floor` | `RiemannResearch.E8.SubgroupSieve` | The smallest actual residual lift in the embedded joint certificate has order 120 | Kernel checked data consistency |
| `RiemannResearch.E8.omegaEightPlusTwo_subsystemOrbitDegree_commonDivisor_eq_one` | `RiemannResearch.E8.SubgroupSieve` | Orbit packets summing to 135, 11200, and 12096 have no common degree divisor other than one | Kernel checked conditional packet theorem |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.OmegaEightPlusTwo` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.OmegaEightPlusTwo` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.GroupTheory.attractingRank_properties` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | The length-plus-descent formula and Coxeter complement identities imply unique zero rank and rank duality | Kernel checked |
| `RiemannResearch.GroupTheory.coxeter_exists_maximalLength_of_finite` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | Every finite Coxeter group has an element of maximal Coxeter length | Kernel checked |
| `RiemannResearch.GroupTheory.coxeter_isRightInversion_of_maximalLength` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | Every reflection is a strict right inversion of any maximal-length element | Kernel checked |
| `RiemannResearch.GroupTheory.coxeter_isLeftInversion_of_maximalLength` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | Every reflection is a strict left inversion of any maximal-length element | Kernel checked |
| `RiemannResearch.GroupTheory.coxeter_isRightDescent_of_maximalLength` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | Every simple generator is a right descent of any maximal-length element | Kernel checked |
| `RiemannResearch.GroupTheory.coxeter_isLeftDescent_of_maximalLength` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | Every simple generator is a left descent of any maximal-length element | Kernel checked |
| `RiemannResearch.GroupTheory.isRightDescent_longestMul_iff_not` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | A Coxeter length-complement identity exchanges right descents of `w₀w` with right ascents of `w` | Kernel checked |
| `RiemannResearch.GroupTheory.coxeterRightDescentCount_one` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | The identity has zero simple right descents in every finitely generated Coxeter system | Kernel checked |
| `RiemannResearch.GroupTheory.coxeterRightDescentCount_longestMul_add` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | The length-complement identity forces complementary right-descent counts | Kernel checked |
| `RiemannResearch.GroupTheory.coxeterAttractingRank_properties_of_lengthComplement` | `RiemannResearch.GroupTheory.CoxeterAttractingRank` | One length-complement identity plus the rank formula gives unique zero rank and full attracting-rank duality | Kernel checked |
| `RiemannResearch.E8.e8AttractingRank_properties_of_lengthComplement` | `RiemannResearch.E8.CoxeterAttractingRank` | For Mathlib's E8 Coxeter group, the single explicit length-complement input implies all Coxeter-rank conclusions of corrected Theorem 3.2 | Kernel checked conditional Coxeter specialization |
| `RiemannResearch.E8.e8AttractingRank_eq_zero_iff` | `RiemannResearch.E8.CoxeterAttractingRank` | On Mathlib's E8 Coxeter group, length plus the number of right descents vanishes exactly at the identity | Kernel checked unconditionally |
| `RiemannResearch.E8.e8_total_attracting_rank` | `RiemannResearch.E8.CoxeterAttractingRank` | Checks the E8 total attracting-rank arithmetic `120 + 8 = 128` | Kernel checked |
| `RiemannResearch.LinearAlgebra.bilinearMapQ` | `RiemannResearch.LinearAlgebra.QuotientMap` | A bilinear map that sends both relation submodules into a target relation descends to the three quotient modules | Kernel checked generic construction |
| `RiemannResearch.LinearAlgebra.bilinearMapQ_assoc` | `RiemannResearch.LinearAlgebra.QuotientMap` | Representative-level associativity of a relation-compatible bilinear operation descends to its quotient | Kernel checked |
| `RiemannResearch.Motives.integralCycleQuotientMap_comp` | `RiemannResearch.Motives.IntegralCycleQuotients` | Relation-preserving linear maps on Mathlib integral algebraic cycles descend functorially to supplied cycle quotients | Kernel checked; the supplied relation is not asserted to be rational equivalence |
| `RiemannResearch.Motives.IntegralProductCycleCompositionData.onClasses` | `RiemannResearch.Motives.IntegralCorrespondenceComposition` | A supplied bilinear composition on actual cycles over scheme products descends when it preserves the supplied relations in both variables | Kernel checked conditional construction; intersection, proper pushforward, grading, and rational equivalence are not supplied |
| `RiemannResearch.Motives.IntegralProductCycleCompositionData.onClasses_assoc` | `RiemannResearch.Motives.IntegralCorrespondenceComposition` | Compatible representative-level product-cycle compositions induce associative composition on the quotient modules | Kernel checked implication |
| `RiemannResearch.Motives.IntegralProductCycleCompositionData.onClasses_left_identity` | `RiemannResearch.Motives.IntegralCorrespondenceComposition` | A supplied diagonal representative acting as a left identity remains a left identity after quotienting | Kernel checked implication |
| `RiemannResearch.Motives.IntegralProductCycleCompositionData.onClasses_right_identity` | `RiemannResearch.Motives.IntegralCorrespondenceComposition` | A supplied diagonal representative acting as a right identity remains a right identity after quotienting | Kernel checked implication |
| `RiemannResearch.Motives.lift_integralProductCycle_idempotent` | `RiemannResearch.Motives.IntegralProjectorLifting` | Rost nilpotence lifts an image projector between supplied correspondence-ring structures on concrete integral product-cycle quotient carriers | Kernel checked implication; ring structures, rational equivalence, geometric base change, and Rost nilpotence are explicit inputs |
| `RiemannResearch.Motives.lift_complete_integralProductCycle_projectorFamily` | `RiemannResearch.Motives.IntegralProjectorLifting` | A complete orthogonal family of split projectors in the base-change image lifts on concrete integral product-cycle quotient carriers | Kernel checked implication with the same explicit geometric inputs |
| `RiemannResearch.Motives.isRostNilpotent_comp` | `RiemannResearch.Motives.RostNilpotence` | Elementwise nilpotence of kernels composes through a tower of noncommutative ring maps | Kernel checked |
| `RiemannResearch.Motives.hasKernelExponent_comp` | `RiemannResearch.Motives.RostNilpotence` | Uniform kernel exponents multiply through a tower | Kernel checked |
| `RiemannResearch.Motives.lift_idempotent_of_isRostNilpotent` | `RiemannResearch.Motives.RostNilpotence` | A projector in the image of a ring map with elementwise nilpotent kernel lifts to a projector | Kernel checked |
| `RiemannResearch.Motives.endomorphismMapRingHom` | `RiemannResearch.Motives.RostNilpotence` | An additive functor induces a ring homomorphism on every endomorphism ring | Kernel checked construction |
| `RiemannResearch.Motives.isRostNilpotentAt_comp` | `RiemannResearch.Motives.RostNilpotence` | Objectwise Rost-nilpotence composes along additive functors | Kernel checked |
| `RiemannResearch.Motives.lift_complete_projector_family_of_isRostNilpotentAt` | `RiemannResearch.Motives.RostNilpotence` | A finite complete orthogonal projector family in the image lifts along an additive functor with Rost-nilpotent endomorphism kernel | Kernel checked abstract categorical theorem; no Chow-motive geometry asserted |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |
| `RiemannResearch.GroupCohomology.finiteEtaleKernelNorm_of_subsingleton_target` | `RiemannResearch.GroupCohomology.FiniteEtaleKernelNorm` | If the target pointed set is a subsingleton, every finite-etale kernel-norm conclusion is automatic | Kernel checked reverse implication underlying Proposition 6.35 |
| `RiemannResearch.GroupCohomology.zmodTwo_diagonalKernelNorm_counterexample` | `RiemannResearch.GroupCohomology.FiniteEtaleKernelNorm` | Degree-three restriction--corestriction, a two-torsion class, Bezout congruence, and local neutrality do not force diagonal neutrality for an arbitrary pointed classifier | Kernel checked abstract countermodel; explicitly not an E8 counterexample |

## Conditional research reductions

These declarations are complete proofs of implications, but they are not
unconditional proofs of the motivating named theorems.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `RiemannResearch.AlgebraicGeometry.SerreII.conjecture_nonE8_of_family_providers` | `RiemannResearch.AlgebraicGeometry.SerreIINonE8` | Classical, `E6`, `E7`, `F4`, and `G2` fpqc-neutrality providers assemble to the project Serre-II conjecture on the supplied non-`E8` Dynkin-family scope | Kernel checked assembly theorem; the concrete predicates, classifier, and all five providers below remain open in the project |
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | From the inputs listed below, proves parts (i)--(iii), nonabelianness of the simple core, and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked implication; open obligations remain |
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent_nonabelianH1` | `RiemannResearch.E8.FullWeylCore` | Specializes the conditional assembly to actual discrete nonabelian H¹ and proves the forward restriction-neutrality implication rather than assuming it | Kernel checked implication; remaining E8-specific hypotheses are load-bearing |
| `RiemannResearch.AlgebraicGeometry.universalFixedLocusAndSplittingField` | `RiemannResearch.AlgebraicGeometry.FixedLocusSplitting` | For a regular cocharacter chosen in the chamber determined by the fixed Borel, the supplied geometric inputs imply the fixed-locus and motivic conclusions, unconditional compactification/Borel point-field and index equality, and—only for inner torsors—neutrality and torsor-index comparisons | Kernel checked implication matching the intended chamber convention and revised scope of Theorem 3.2(iii) |
| `RiemannResearch.AlgebraicGeometry.exactProjectiveResidual` | `RiemannResearch.AlgebraicGeometry.FixedLocusSplitting` | The compactification/Borel and inner Borel/neutrality point equivalences propagate torsor index one to both projective varieties, formalizing PDF Corollary 3.4 | Kernel checked implication; Theorems 2.1 and 3.2 supply the external mathematical inputs |
| `RiemannResearch.AlgebraicGeometry.neutral_of_oddDegreePointDescent` | `RiemannResearch.AlgebraicGeometry.OddDegreePointDescent` | Odd-degree splitting, an all-extension point/neutrality equivalence, and odd-degree point descent imply neutrality of every candidate class | Kernel checked implication; the E8-specific inputs below remain open |
| `RiemannResearch.GaloisCohomology.isCoboundary_of_compatibleLocalGauges` | `RiemannResearch.GaloisCohomology.CompatibleLocalGauges` | A common gauge on a generating family makes every selected nonabelian cocycle a global coboundary | Kernel checked implication; existence of the E8 common gauges remains open |
| `RiemannResearch.GaloisCohomology.nonabelianH1_family_subsingleton_of_compatibleLocalGauges` | `RiemannResearch.GaloisCohomology.CompatibleLocalGauges` | Compatible common gauges for every cocycle in every member of a family make each discrete nonabelian H¹ a subsingleton | Kernel checked family-level implication; the fpqc/E8 comparison and E8 common gauges remain open |
| `RiemannResearch.GroupCohomology.eq_neutral_of_diagonalKernelNorm` | `RiemannResearch.GroupCohomology.FiniteEtaleKernelNorm` | One diagonal toral restriction--corestriction value in the neutral fiber, with the index formulas and a positive Bezout congruence, forces the original toral class to map to the neutral class | Kernel checked implication; the E8 diagonal kernel-norm input remains open |
| `RiemannResearch.GroupCohomology.eq_neutral_of_finiteEtaleKernelNorm` | `RiemannResearch.GroupCohomology.FiniteEtaleKernelNorm` | Componentwise neutrality in a repeated finite-etale product, the product kernel-norm principle, index formulas, and a positive Bezout congruence force the original toral class to map to the neutral class | Kernel checked finite-etale formulation of Proposition 6.34; the E8 product kernel-norm input remains open |

### Open obligations: `conjecture_nonE8_of_family_providers`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `IsPerfectFieldCdAtMostTwo` | Intrinsic predicate for perfect fields of cohomological dimension at most two | **Open** as a concrete project predicate; supplied abstractly here |
| `IsSemisimpleSimplyConnected` | Intrinsic predicate for semisimple simply connected affine group schemes | **Open** as a concrete project predicate; supplied abstractly here |
| `family` | Correct Dynkin-family classifier for every group scheme in scope | **Open**; the finite codomain is defined, but no algebraic-group classifier is constructed |
| `classical` | Fpqc Serre-II neutrality for the `A`, `B`, `C`, and `D` series | **Open** in the project; arbitrary trialitarian `D4` is not known uniformly, so this binder is stronger than the current arbitrary-form literature |
| `e6` | Fpqc Serre-II neutrality for family `E6` | **Open**; the generic arbitrary-form case is not known, while the quasi-split case is published but not formalized here |
| `e7` | Fpqc Serre-II neutrality for family `E7` | **Open**; the generic arbitrary-form case is not known, while the quasi-split case is published but not formalized here |
| `f4` | Fpqc Serre-II neutrality for family `F4` | Published mathematics exists for the stated field scope; an algebraic-group/fpqc project provider remains **open** |
| `g2` | Fpqc Serre-II neutrality for family `G2` | Published mathematics exists for the stated field scope; an algebraic-group/fpqc project provider remains **open** |

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
| `chosen_chamber_rank_formula` | Attracting-rank formula for the regular cocharacter chosen in the fixed Borel chamber | This is not an extra condition on the cocharacter. The tangent-weight and fixed-scheme proof of the formula remains **open**; `regularFunctional_exists_adaptedBase` supplies the equivalent reindexing convention. |
| `length_zero_iff` | Coxeter length vanishes only at the identity in the supplied model | E8 provider: `e8CoxeterSystem.length_eq_zero_iff` |
| `rightDescent_one` | The identity has no right descents in the supplied model | Provider: `coxeterRightDescentCount_one` |
| `length_duality` | Complementary Coxeter-length identity | `coxeter_exists_maximalLength_of_finite` constructs a maximal element from `[Finite W]`, and the inversion lemmas make every reflection a strict inversion. For Mathlib's presented E8 group, a `Finite` instance, the longest-element complement theorem, and the maximal-length calculation `120` remain **open**. |
| `rightDescent_duality` | Complementary right-descent identity | Derived from `length_duality` by `coxeterRightDescentCount_longestMul_add`; no independent obligation remains |
| `bialynickiBirula_motive` | Integral motivic Białynicki–Birula decomposition | **Open** |
| `bialynickiBirula_chowZero` | Degree-compatible `CH₀` comparison from the zero-rank component | **Open** |
| `properLimit` | A compactification point specializes to a fixed-locus point | **Open** |
| `fixedComponentInclusion` | A twisted Borel component point gives a compactification point | **Open** |
| `inner_borelReduction_iff_neutral` | For an inner torsor, a Borel reduction is equivalent to neutrality | **Open** |

### Open obligations: `neutral_of_oddDegreePointDescent`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `oddSplitting` | Every E8 class becomes neutral over a finite odd-degree extension | Published input in the memorandum; a project declaration supplying the algebraic E8 statement remains **open** |
| `point_iff_neutral` | Points on the chosen Borel, EVIII, or wonderful variety are equivalent to neutrality over every extension | Borel/wonderful abstract providers are fields of `UniversalFixedLocusConclusion`; their algebraic E8 geometric inputs remain **open**. No EVIII project provider exists. |
| `oddPointDescent` | A point over the odd-degree extension descends to the base | **Open**; this is completion target A |

### Open obligations: compatible-local-gauge completion targets

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `commonGauge` | The prime-local E8 trivialization cosets have a nonempty total intersection for every candidate cocycle, uniformly for every family member in the family-level theorem | **Open**; this is completion target B |
| E8 specialization | Identify algebraic E8 torsors with the discrete nonabelian cocycles selected by `Candidate`, and supply the generating prime-local gauges | **Open** |

### Open obligations: diagonal kernel-norm completion targets

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `hindex` | Torus-H¹ restriction followed by corestriction is multiplication by the field degree | The abstract additive formula is kernel checked elsewhere; the algebraic torus-H¹ specialization remains **open** |
| `he` | The selected torus-H¹ class has a positive annihilator | Standard finite-splitting-field input; a project provider remains **open** |
| `hcoefficient` | Nonnegative multiplicities give total degree congruent to one modulo the annihilator | Arithmetic datum; supplied case-by-case from gcd-one subsystem degrees |
| `hrestrictedKernel` | Every selected subsystem-field restriction of the toral class maps to the local neutral E8 class | Claimed by the subsystem-field construction; algebraic E8 providers remain **open** |
| `hkernelNorm` | The single diagonal corestriction value maps to the neutral E8 class | **Open**; this is completion target C |
| `finiteEtaleKernelNorm` | Componentwise local kernel membership is preserved by corestriction from the repeated finite-etale product | **Open**; this is Conjecture 6.33. The abstract countermodel `zmodTwo_diagonalKernelNorm_counterexample` proves it does not follow from the additive transfer and Bezout data alone. |

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
| `RiemannResearch.GroupCohomology.corestrictionCochain_mem_cocycles₁` | `RiemannResearch.GroupCohomology.ArbitraryCorestriction` | The explicit left-coset corestriction sends additive one-cocycles to one-cocycles | Kernel checked |
| `RiemannResearch.GroupCohomology.corestrictionCochain_mem_coboundaries₁` | `RiemannResearch.GroupCohomology.ArbitraryCorestriction` | The same cochain sends coboundaries to coboundaries, so it descends to H¹ | Kernel checked |
| `RiemannResearch.GroupCohomology.h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex` | `RiemannResearch.GroupCohomology.ArbitraryCorestriction` | Restriction followed by arbitrary finite-index corestriction is multiplication by the index on additive H¹ | Kernel checked; additive transfer only |
| `RiemannResearch.E8.serreIIProgram_fourField_gcd` | `RiemannResearch.E8.SylowLocalSplitting` | A divisor common to a degree dividing 2880 and to degrees avoiding 2, 3, and 5 is one; exact arithmetic endpoint of PDF Theorem 2.2 | Kernel checked |
| `RiemannResearch.E8.sylowLocalFourFieldSplittingPackage` | `RiemannResearch.E8.SylowLocalSplitting` | Chooses the four splitting fields in PDF Theorem 2.2, proves their degree gcd is one, and derives point-field index one from explicit Totaro and prime-avoidance inputs | Kernel checked conditional reduction; construction of the input fields remains source dependent |
