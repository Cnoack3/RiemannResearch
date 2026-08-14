# Theorem ledger for the 5 August 2026 E8 Serre II memorandum

Artifact: serre_ii_e8_program_2026-08-05.pdf, 51 pages.

This ledger covers every labeled result in the attached artifact: 61 theorems,
propositions, corollaries, and lemmas; four conjectures; and Question 5.22.
It records the strongest evidence currently available. It is not a claim that
the E8 case of Serre's Conjecture II has been solved.

For the declaration-level implementation target attached to every bibliography
entry, see `SERRE_II_CITATION_FORMALIZATION_PLAN.md`.

## Status key

- **Lean exact fragment**: the cited declaration proves the stated arithmetic
  or abstract implication without placeholders.
- **Lean conditional**: Lean proves the consequence only after named
  domain-specific hypotheses are supplied.
- **Primary-source checked**: the exact external result and hypotheses have
  been inspected and support the cited use; this is not a Lean formalization.
- **Source dependent**: the manuscript proof materially invokes external
  results not formalized in this project.
- **Manuscript only**: an informal proof is printed, but no kernel proof exists.
- **Unreproduced computation**: required scripts or raw output are absent.
- **Open**: explicitly conjectural or equivalent to the unresolved E8 case.

## Sections 2--4

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 2.1 | Primary-source checked | Izquierdo--Lucchini Arteche Corollary 4.14, Garibaldi--Semenov (1.1)--(1.2), and Totaro Theorem 0.1 exactly support the three parts; none is formalized here. |
| Theorem 2.2 | Manuscript deduction from checked sources | The co-p closure and finite-descent argument is coherent; ILA Corollary 4.14 validates the p-special step and no nonabelian Bezout conclusion is drawn. |
| Proposition 3.1 | Fixed-cover fpqc foundations in Lean; geometry source dependent | Witnessed fpqc covers, refinement pullback, neutral Čech H¹, and pairwise common refinements are kernel checked. The wonderful compactification, orbit geometry, effective descent, and torsor classification remain absent. |
| Theorem 3.2 | **Revised implication and Borel-chamber convention formalized conditionally** | The regular cocharacter is chosen in the chamber determined by the fixed Borel; changing sign selects the attracting convention and imposes no extra rank condition. The 8 August revision makes compactification/Borel point equivalence unconditional and restricts Borel/neutrality and torsor-index equivalences to inner torsors; `universalFixedLocusAndSplittingField` enforces that scope. Its `chosen_chamber_rank_formula` binder records the still-unformalized tangent-weight and fixed-scheme proof, not another condition on the cocharacter. The finite-Coxeter lemmas derive the rank consequences once that formula and the E8 length-complement identity are supplied. The scheme geometry, tangent weights, motive comparison, descent, E8 finiteness/complement theorem, and length-120 calculation remain open inputs. |
| Corollary 3.4 | Lean exact implication at the point-field interface | `exactProjectiveResidual` proves that Theorem 3.2's compactification/Borel and inner Borel/neutrality point equivalences propagate Theorem 2.1's torsor index-one conclusion to both projective varieties. The geometric inputs to Theorem 3.2 and the cited source for Theorem 2.1 remain external. |
| Proposition 4.1 | Manuscript only | The localization calculation CH0(Gm)=0 is not formalized here. |
| Proposition 4.2 | Source dependent | Uses rationality of the split EVIII space, compactification, and localization. |
| Theorem 4.3 | Primary-source checked; not Lean-formalized | Gille Corollary 9.3.6 has exactly the stated invertibility and separable-cohomological-dimension hypotheses. Proposition 9.3.5 supplies a solvable splitting extension, so the nonsolvable gap in Theorem 8.4.1 does not affect this use. |
| Corollary 4.4 | Source-checked consequence | Depends on Theorem 4.3. |
| Theorem 4.5 | Primary-source checked; not Lean-formalized | Gille Corollary 9.3.7 exactly says that an E8 form containing a k-subgroup mu_n, n at least 2, is split under the stated hypotheses. |
| Theorem 4.6 | Primary-source checked; citation pinpoints incomplete | Sansuc Proposition 6.10 supplies the Picard--Brauer sequence, and Bayer-Fluckiger--Parimala covers the split nontrialitarian D8 classical-group input. The memorandum should state the standing characteristic-zero hypothesis and cite exact results. |
| Proposition 4.7 | Source checked; missing citation | The deduction from Proposition 4.6, rationality, and Brauer purity is valid; Česnavičius Theorem 1.1 is an explicit source for the uncited purity step. |
| Proposition 4.8 | Lean exact abstract kernel; Chow-motive instantiation open | `UnitRetractDegreeData.hasUnitRetract_iff_hasDegreeOneZeroCycle` proves the unit-object retract iff degree-one zero-cycle criterion from a preadditive correspondence interface. `degree_zeroCycleOfHom_eq_one_or_neg_one_of_retract` and `degree_signedZeroCycleOfRetract` handle the integral sign explicitly. Instantiating the interface with integral Chow motives of a smooth projective geometrically integral variety remains open. |
| Theorem 4.9 | Primary-source checked; not Lean-formalized | CGM Theorem 8.2 supplies integral Rost nilpotence and Sechin--Semenov Lemma 7.8 supplies the split-motive criterion. |
| Theorem 4.11 | Source-checked manuscript proof; citation correction needed | The prime-to-p transfer proof is valid using oriented Rost nilpotence and Sechin--Semenov Lemma 7.8. Semenov Theorem 6.16 is only an independent p=2, height-at-least-4 check, not the uniform all-prime/all-height source. |
| Corollary 4.12 | Source-checked consequence; not Lean-formalized | Depends on Theorems 4.9 and 4.11. |

## Section 5

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 5.4 | Primary-source checked; citation theorem not Lean-formalized | Gille 2001 Theorem 11 exactly gives cyclic degree 2, 3, and 5 injectivity under the standing hypotheses. `HasTrivialKernel.comp` now kernel-checks the pointed-set iteration logic through a solvable tower; the cyclic E8 kernel theorem itself remains external. |
| Theorem 5.6 | Manuscript only; setup citation incomplete | An explicit finite quadratic-space construction is printed, but the A5 action is not formalized here. Totaro's table indirectly identifies the index-135 D8 stabilizer; it does not itself prove the setup sentence that every nonzero singular mod-2 vector is a toral involution with connected centralizer D8. |
| Theorem 5.7 | Additive normal-transfer foundation in Lean; theorem still source dependent | `h1Restriction_injective_of_normal_finiteIndex` proves normal finite-index restriction injectivity by averaging. `h1Corestriction` descends the quotient-transversal formula to additive H¹, and `h1RestrictionViaCocycles_comp_h1Corestriction` proves the subgroup-index identity. Brown's arbitrary-Sylow theorem still requires the Mackey formula, reverse stable-elements inclusion, and the E8 lattice/linking-form instantiation. |
| Corollary 5.8 | Source-checked consequence; not Lean-formalized | Depends on Theorems 4.3, 5.6, and 5.7. |
| Theorem 5.9 | Manuscript only | The explicit S5 lattice construction and its mod-p invariant calculation are not formalized. |
| Corollary 5.10 | Source dependent | Depends on Theorem 5.7 and quadratic cyclic descent. |
| Theorem 5.11 | Corrected source checked; not Lean-formalized | Gille's 26 May 2026 correction to Lemma 1.6.5 exactly supports the R1-marker deduction; the lattice assertions are not instantiated in Lean. |
| Proposition 5.12 | Manuscript only | Inflation--restriction deduction from Theorem 5.11. |
| Theorem 5.13 | Primary-source checked; not Lean-formalized | Harari--Szamuely Theorem 5.6 contains the exact Poitou--Tate segment used; the local norm and totally-imaginary global-neutrality deductions are coherent. Platonov--Rapinchuk Theorem 6.6 supplies the Hasse principle, but the nonarchimedean local-vanishing input should also be pinpointed. |
| Corollary 5.14 | Unverified | Depends on Theorems 5.11 and 5.13. |
| Theorem 5.16 | Source-correct packet named; arithmetic exact in Lean; geometry source dependent | Totaro's table gives `K_D8` of degree 135, `K_(A2)^4` of degree 11200, and `K_(A4)^2` of degree 12096; the distinct `A2E6` row has index 1120. `FullWeylSubsystem.splittingDegree` records the 135/11200/12096 packet and `corrected_bezout` checks its signed relation. Lean does not construct the three fields. |
| Corollary 5.17 | Source-correct signed cycle exact in Lean; geometric providers open | `fullWeylDegreeOneCycle_degree` proves that `-1417 z_D8 + 16 z_(A2)^4 + z_(A4)^2` has degree one from degrees 135, 11200, and 12096. Existence and neutralizing properties of the three splitting cycles still depend on Theorem 5.16's geometric providers. |
| Theorem 5.19 | Lean conditional with discrete-H¹ restriction and double/triple scheme-overlap foundations | `quasisimpleCoreOfFullWeylDescent_nonabelianH1` specializes the assembly theorem to actual discrete nonabelian H¹ and kernel-checks forward restriction neutrality. The chosen scheme-level double and triple overlaps are now transported directly to Galois-indexed affine-group points. The converse quadratic kernel, cyclic-prime torus kernel, Weyl-quotient/Ω identifications, Ω order and simplicity, module cardinalities, and the E8 diagonalizable-subgroup criterion remain load-bearing. Compatibility of the categorical face maps, fpqc torsor classification, algebraic E8 instantiation, and existence of the 135 simultaneous D8 fixed corrections remain open. |

## Section 6

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 6.1 | Primary-source inputs checked; not Lean-formalized | Chernousov Theorem 3.1/Gille Corollary 1(b), Gille Theorem 11, Totaro's page-21 table, and Gille Corollary 9.3.6 all have the required scope. |
| Proposition 6.2 | Manuscript only | The finite orbit and marker data are not reproduced in Lean. |
| Theorem 6.3 | Manuscript only | The finite quadratic-module and Fourier calculations are not formalized. |
| Theorem 6.5 | Source-checked Gille input; manuscript geometry | Gille Corollary 9.3.6 is confirmed; the building-geometric construction is not formalized. |
| Theorem 6.6 | Manuscript only; statement ambiguous | Gauge independence is proved only after fixing the flag. Changing the flag requires an explicit conjugacy identification of the fields and double-coset spaces. |
| Proposition 6.7 | Exact arithmetic/additive shadow in Lean; nonabelian statement unverified | serreIIProgram_a8Gauge_field_degrees, serreIIProgram_a8Gauge_bezout, serreIIProgram_a8Gauge_gcd, and eq_zero_of_serreIIProgram_a8Gauge_annihilators check the numerical and abelian core. The PDF also contains the literal token qquad in the statement. |
| Theorem 6.9 | Arithmetic exact; finite certificate reproduced; field realization open | `serreIIProgram_survivorEnvelope_bezout` and `serreIIProgram_survivorEnvelope_gcd` check all five rows. The committed GAP/TomLib certificate reproduces the orbit decompositions, while the row-to-E8 geometry and actual point fields remain external. |
| Theorem 6.10 | Finite sieve certificate reproduced; geometry bridge open | `Certificates/O8_PLUS_2_SUBGROUP_SIEVE_CERTIFICATE.md` records the rerunnable GAP 4.16/TomLib calculation and raw 11171 to 313 to 303 counts. Lean checks the embedded data and the uniform gcd-one deduction; Totaro-column matching remains a source-level boundary. |
| Theorem 6.11 | Perfect-core compression certificate reproduced | The committed certificate reproduces 303 = 150 solvable + 153 nonsolvable and compression to 31 perfect cores. Lean's `omegaEightPlusTwoPerfectCoreLiftData_certificate` checks the 31 embedded rows, not their algebraic E8 realization. |
| Proposition 6.12 | Cover/marker numerical certificate reproduced; E8 realization open | `Certificates/O8_PLUS_2_COVER_MARKER_CERTIFICATE.md` and the embedded 31-row data check lift orders, derived orders, and fixed mod-two dimensions. Fusion and certificate-to-geometric-action identifications remain external. |
| Corollary 6.13 | Projective and lifted order floors exact in Lean; group identification external | `omegaEightPlusTwoPerfectCoreClassData_order_floor` checks that the smallest embedded perfect projective core order is 60, and `omegaEightPlusTwoPerfectCoreLiftData_order_floor` checks that the smallest actual lift order is 120. Identifying all four order-60 rows with `A5`, their nonsplit lifts with `2.A5 ≃ SL2(5)`, and the certificate rows with algebraic E8 monodromy remains external. |
| Corollary 6.14 | Citation/computation conditional | Depends on Proposition 6.12 and the corrected Gille marker lemma. |
| Proposition 6.15 | Exact double-coset reduction and order arithmetic in Lean; E8 factorization open | `serreIIProgram_binaryIcosahedral_index_arithmetic` checks the displayed orders and indices. `isCoboundary_iff_one_mem_fixedPointDoubleCoset` proves the coefficient-free two-gauge statement: neutrality is exactly identity membership in the fixed-point double coset. The nonsplit `2.A5` lift, actual degree-5/degree-6 field gauges, and the E8 factorization are not constructed. |
| Proposition 6.16 | Finite subsystem-orbit input reproduced; theorem still citation conditional | `binaryIcosahedralSubsystemOrbitData_has_small_orbits` checks that every certified projective A5 row has a degree-five (D4)^2 orbit and a degree-six (A4)^2 orbit. The TomLib row/action identification is an external certificate; classical Serre II and the descent argument remain unformalized. |
| Proposition 6.17 | **Corrected theorem kernel checked: numerical orbit count exact; universal outer-triality assertion false** | `correctedProposition617` packages the surviving twelve-orbit count, an explicit nonidentity order-three stabilizer element in the inner `W(D4)×W(D4)` reflection image, and the formal negation of the universal outer assertion. The reproducible GAP/TomLib countercertificate narrows the ATLAS matrix class to `{4015,4017}`; each manuscript row has one degree-five `(D4)^2` orbit. The other eleven diagram actions remain unverified, so Research Target 8.2 must be orbitwise. |
| Proposition 6.19 | Abstract transporter incidence formalized; geometric E8 specialization open | `orientedSubgroupTransporter` and `mem_orientedSubgroupTransporter_iff` formalize the strict oriented subgroup transporter. `isCoboundary_iff_orientedTransporter_and_doubleCoset` combines its supplied incidence with the exact factorization criterion. Lean does not yet construct the 8-dimensional E8 torus transporter, prove its bitorsor/descent geometry, or produce a point yielding the required factorization. |
| Proposition 6.21 | Additive restriction, normal corestriction, index formula, and gcd-one kernels checked | `h1Restriction_tower` gives additive H¹ restriction and its tower law; `h1Corestriction` and `h1RestrictionViaCocycles_comp_h1Corestriction` give normal finite-index transfer and the subgroup-index identity; and the finite-family gcd-one restriction theorems package the Bézout detection step. The required nonabelian/field-specific comparison remains unformalized. |
| Proposition 6.22 | Dimension arithmetic exact in Lean; geometry unformalized | `binaryIcosahedral_weilRestriction_dimension_gap` proves the general `11 d < 30 d` comparison for positive dimension, and `serreIIProgram_proposition622_dimension_arithmetic` checks `2728 < 7440` for `dim E8 = 248`. Dimensions of Weil restrictions, constructible-image properness, and density of rational points remain algebraic-geometric inputs. |
| Proposition 6.24 | Euler-characteristic and rank arithmetic exact in Lean; Bass--Serre theory unformalized | `serreIIProgram_proposition624_eulerCharacteristic` checks `1/24 + 1/20 - 1/4 = -19/120`, and `serreIIProgram_proposition624_freeKernelRank_arithmetic` checks the index-120 and rank-20 deductions. Freeness of the amalgam kernel and the finite-subgroup nonsplitting argument remain outside the current API. |
| Proposition 6.26 | Finite GAP certificate reproduced; Lean checks embedded data and H¹ deduction | The deterministic GAP/TomLib/CTblLib certificate checks the rank-10 restriction matrix, Burnside kernel vector, distinct global orbit packets, odd centralizer corrections, even simultaneous conjugators over both gauge groups, failure of a global conjugator, and joint image `A11`. `A11BurnsideCertificate.lean` checks the embedded matrices and permutation equations; `differenceCocycle_twoGaugeCounterexample` derives the nonneutral class with two neutral restrictions. GAP row/action identification remains an explicit external certificate boundary. |
| Corollary 6.28 | Finite premise reproduced; field realization open | Proposition 6.26's finite group and cohomological kernel data are now reproducible. The Riemann-existence construction, cohomological-dimension claim, and finite-étale descent realizing the example over a field are not formalized. |
| Theorem 6.30 | **Corrected title and exact common-gauge criterion kernel checked; computation conditional** | The corrected title is “Generating subsystem family and exact common-gauge criterion.” `correctedTheorem630` packages projective generation from gcd-one indices, lifted generation through the quotient, and the exact equivalence between global neutrality and nonemptiness of the total local-gauge intersection. `isCoboundary_iff_exists_commonLocalGauge` gives the equivalent one-common-element formulation. No common gauge is produced from separately nonempty local gauge sets; its existence remains exactly the E8 neutrality problem. The concrete subgroup indices still depend on Theorem 6.10's certificate-to-geometry interface. |
| Corollary 6.31 | Unverified | Depends on Theorems 6.10 and 6.30. |
| Proposition 6.32 | Exact additive Burnside-basis top-mark obstruction in Lean | `not_mem_addSubgroup_closure_of_mark` proves the abstract mark argument, while `BurnsideAdditive.unit_not_mem_span_properTransitiveOrbits` instantiates it in the free abelian group on conjugacy classes of transitive finite orbit types `G/H`. The multiplicative Burnside ring and its comparison with a categorical finite-`G`-set Grothendieck completion remain unformalized. |
| Proposition 6.34 | **Finite-etale assembly kernel checked; decisive input open** | `diagonalCorestriction_eq_of_annihilator_bezout` proves that the selected repeated corestriction is exactly the original class, and `diagonalKernelNorm_iff_neutral` proves that its required kernel membership is therefore equivalent to the desired neutrality. `eq_neutral_of_finiteEtaleKernelNorm` and `all_classes_neutral_of_universalFiniteEtaleKernelNormPrinciple` package the remaining conditional deductions. Conjecture 6.33 and its E8 providers remain open. |
| Proposition 6.35 | **Abstract equivalence kernel checked; E8 instance open** | `universalFiniteEtaleKernelNormPrinciple_iff_all_classes_neutral` proves both directions from exact restriction-corestriction and local Bezout data. Thus the full E8 statement is still a reformulation equivalent to E8 Serre II, not independent progress or a proof of Conjecture 6.33. |
| Lemma 6.36 | **Lean exact abstract kernel** | `eq_zero_of_gcd_one_annihilators` proves the finite Bezout-annihilator argument, and `h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex` supplies abstract additive H¹ restriction--corestriction for arbitrary finite-index subgroups. The algebraic torus-H¹ specialization remains open. |

## Section 7

| Result | Current status | Evidence or blocker |
|---|---|---|
| Lemma 7.1 | Manuscript only | Requires finite-presentation descent for torsors over filtered field unions. |
| Theorem 7.2 | Prime-power endpoint implication in Lean; ILA theorem unformalized | ILA Corollary 4.14 supplies index one only at the cited-source level. PrimePowerIndex.lean proves that a prime-power point-degree spectrum of index one contains an actual degree-one point field. |
| Corollary 7.3 | Source checked with wording correction | The endpoint exclusion follows from Theorem 7.2. Merkurjev Theorem 4 preserves its specially constructed quaternion tensor product and associated anisotropic form, not arbitrary pre-chosen examples. |
| Proposition 7.4 | Manuscript only | The specialization argument for affine torsors over a pure transcendental extension is not formalized. |
| Proposition 7.5 and following paragraph | **Criterion partially kernel checked; following generation step false as written** | `fixed_of_fixed_on_join_eq_top` checks the common-fixed-point implication. `quotientGeneration_counterexample` shows that lifts whose images generate a finite presentation quotient need not generate the ambient group. The Galois repair is to include the presentation kernel `N = Gal(k_s/E)` and its known splitting-field coset together with the prime-local lifts. The full Galois/gauge-coset realization is not formalized. |

## Explicitly open items

| Item | Status |
|---|---|
| Conjecture 5.1 | Open odd-degree wonderful descent. |
| Conjecture 5.2 | Open odd-degree Borel descent. The cited E6 comparison is an index-one-to-point theorem for selected flags, not literally a single-extension odd-degree theorem. |
| Conjecture 5.3 | Open odd-degree EVIII descent. |
| Question 5.22 | Open full-Weyl toral neutrality question. |
| Conjecture 6.33 | Open E8 finite-etale kernel norm principle. `universalFiniteEtaleKernelNormPrinciple_iff_all_classes_neutral` kernel-checks its abstract equivalence with all-class neutrality once exact local Bezout data are supplied; `zmodTwo_diagonalKernelNorm_counterexample` shows that additive transfer, annihilation, Bezout, and local neutrality alone do not prove the principle. |

## Artifact conventions and defects

1. In Theorem 3.2, the regular cocharacter is chosen in the chamber determined
   by the fixed Borel; the optional sign selects the attracting convention.
   The A2 calculation only rules out a literal reading that begins with an
   arbitrary cocharacter outside that chamber.
2. Proposition 6.7 contains the literal malformed token qquad where a spacing
   command was intended.
3. Theorem 6.6's phrase “independent of every choice” is only justified after
   fixing the flag.
4. Appendix A names computations but does not include the executable scripts,
   row maps, fusion witnesses, package snapshots, or raw output. The repository
   now contains independent GAP scripts and raw certificates for the finite
   computations used in Sections 6.1--6.4; TomLib geometric column matching
   and the field realization of Corollary 6.28 remain external.
5. WeylIndexPacket.lean checks the distinct packet 135, 2240, 48384, not the
   attached PDF's 135, 11200, 12096. A8NormalizerArithmetic.lean checks
   15, 35, 336, not Proposition 6.7's 15, 35, 4032.
6. Almost abelian, R1 H1, the motive categories, normalized abelian invariant,
   and the product-algebra neutral fiber in Conjecture 6.33 need exact
   definitions before literal formalization.
7. Theorem 4.11 cites Semenov Theorem 6.16 too broadly; its uniform proof
   instead uses the manuscript's prime-to-p transfer argument and the
   oriented-motive formalism in Sechin--Semenov.
8. Reference [14] is unused in the manuscript body, while references [1] and
   [29] are invoked without exact result numbers.
9. Totaro's table only indirectly supports the singular-vector/D8-centralizer
   setup used before Theorem 5.6; that sentence needs a direct proof or source.
10. The E6 comparison near Conjecture 5.2 and the Merkurjev endpoint description
    in Corollary 7.3 both state their cited sources more broadly than warranted.
11. The paragraph after Proposition 7.5 passes from generation of a finite
    presentation quotient to generation of the full absolute Galois group.
    This omits the quotient kernel. Include `Gal(k_s/E)` for a finite Galois
    splitting field `E/k`, together with its trivialization coset, before
    applying the proposition; Research Target 8.7 must include that coset.

## Subsequent Lean transfer

- Theorem 2.2 now has the conditional finite-point-field realization `sylowLocalFourFieldSplittingPackage`: it chooses the four displayed fields from explicit Totaro and prime-avoidance inputs, proves their degree gcd is one, and derives point-field index one. Construction of the prime-avoiding fields remains source dependent.
- Proposition 7.5's omitted-kernel issue now has the finite Lean countermodel `quotientGeneration_counterexample`; it also checks that adjoining the projection kernel repairs generation.
