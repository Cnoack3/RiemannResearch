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
| Theorem 3.2 | **Literal statement defective; Lean conditional after correction** | Changing the sign of an arbitrary regular cocharacter does not normalize its Weyl chamber in rank greater than one. `a2Coroot_sign_normalization_counterexample` proves the defect, while `regularFunctional_exists_adaptedBase` kernel-checks the correct chamber-change replacement. Evens--Jones supports the subsequent weight calculation only after this choice (and is written over C); the characteristic-zero fixed-scheme descent and rank formula remain open. |
| Corollary 3.3 | Unverified | Depends on Theorems 2.1 and 3.2. |
| Proposition 4.1 | Manuscript only | The localization calculation CH0(Gm)=0 is not formalized here. |
| Proposition 4.2 | Source dependent | Uses rationality of the split EVIII space, compactification, and localization. |
| Theorem 4.3 | Primary-source checked; not Lean-formalized | Gille Corollary 9.3.6 has exactly the stated invertibility and separable-cohomological-dimension hypotheses. Proposition 9.3.5 supplies a solvable splitting extension, so the nonsolvable gap in Theorem 8.4.1 does not affect this use. |
| Corollary 4.4 | Source-checked consequence | Depends on Theorem 4.3. |
| Theorem 4.5 | Primary-source checked; not Lean-formalized | Gille Corollary 9.3.7 exactly says that an E8 form containing a k-subgroup mu_n, n at least 2, is split under the stated hypotheses. |
| Theorem 4.6 | Primary-source checked; citation pinpoints incomplete | Sansuc Proposition 6.10 supplies the Picard--Brauer sequence, and Bayer-Fluckiger--Parimala covers the split nontrialitarian D8 classical-group input. The memorandum should state the standing characteristic-zero hypothesis and cite exact results. |
| Proposition 4.7 | Source checked; missing citation | The deduction from Proposition 4.6, rationality, and Brauer purity is valid; Česnavičius Theorem 1.1 is an explicit source for the uncited purity step. |
| Proposition 4.8 | Manuscript only | The correspondence proof is standard but Chow motives are not formalized here. |
| Theorem 4.9 | Primary-source checked; not Lean-formalized | CGM Theorem 8.2 supplies integral Rost nilpotence and Sechin--Semenov Lemma 7.8 supplies the split-motive criterion. |
| Theorem 4.11 | Source-checked manuscript proof; citation correction needed | The prime-to-p transfer proof is valid using oriented Rost nilpotence and Sechin--Semenov Lemma 7.8. Semenov Theorem 6.16 is only an independent p=2, height-at-least-4 check, not the uniform all-prime/all-height source. |
| Corollary 4.12 | Source-checked consequence; not Lean-formalized | Depends on Theorems 4.9 and 4.11. |

## Section 5

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 5.4 | Primary-source checked; citation theorem not Lean-formalized | Gille 2001 Theorem 11 exactly gives cyclic degree 2, 3, and 5 injectivity under the standing hypotheses. `HasTrivialKernel.comp` now kernel-checks the pointed-set iteration logic through a solvable tower; the cyclic E8 kernel theorem itself remains external. |
| Theorem 5.6 | Manuscript only; setup citation incomplete | An explicit finite quadratic-space construction is printed, but the A5 action is not formalized here. Totaro's table indirectly identifies the index-135 D8 stabilizer; it does not itself prove the setup sentence that every nonzero singular mod-2 vector is a toral involution with connected centralizer D8. |
| Theorem 5.7 | Partial Brown foundation in Lean; theorem still source dependent | `h1Restriction_injective_of_normal_finiteIndex` proves the normal finite-index restriction-injectivity case by averaging and inflation--restriction. Brown's arbitrary-Sylow stable-elements image theorem still requires cohomological transfer/Mackey theory; Gille Corollary 9.3.7 and the E8 lattice/linking-form instantiation remain unformalized. |
| Corollary 5.8 | Source-checked consequence; not Lean-formalized | Depends on Theorems 4.3, 5.6, and 5.7. |
| Theorem 5.9 | Manuscript only | The explicit S5 lattice construction and its mod-p invariant calculation are not formalized. |
| Corollary 5.10 | Source dependent | Depends on Theorem 5.7 and quadratic cyclic descent. |
| Theorem 5.11 | Corrected source checked; not Lean-formalized | Gille's 26 May 2026 correction to Lemma 1.6.5 exactly supports the R1-marker deduction; the lattice assertions are not instantiated in Lean. |
| Proposition 5.12 | Manuscript only | Inflation--restriction deduction from Theorem 5.11. |
| Theorem 5.13 | Primary-source checked; not Lean-formalized | Harari--Szamuely Theorem 5.6 contains the exact Poitou--Tate segment used; the local norm and totally-imaginary global-neutrality deductions are coherent. Platonov--Rapinchuk Theorem 6.6 supplies the Hasse principle, but the nonarchimedean local-vanishing input should also be pinpointed. |
| Corollary 5.14 | Unverified | Depends on Theorems 5.11 and 5.13. |
| Theorem 5.16 | Source checked; arithmetic exact in Lean | Totaro's page-21 table supplies the three subsystem stabilizer indices and Gille Corollary 9.3.6 supplies neutralization. The algebraic descent is informal. The exact index products and gcd for 135, 11200, 12096 are checked in SerreIIProgramChecks. |
| Corollary 5.17 | Exact arithmetic and index implication in Lean; geometry unverified | serreIIProgram_threeSubsystem_bezout and serreIIProgram_threeSubsystem_gcd check the degree calculation; pointFieldIndex_eq_one_of_three_point_degrees proves that actual point fields with those degrees force index one. Their existence still depends on Theorem 5.16. |
| Theorem 5.19 | Lean conditional with global fpqc, Galois-coordinate, scheme-level double-overlap, and abstract transporter foundations | `quasisimpleCoreOfFullWeylDescent` remains conditional. Discrete nonabelian H¹, global fpqc Čech H¹ across witnessed covers, finite-Galois tensor overlaps, the generic singleton-cover Yoneda/gauge equivalence, affine overlap point/face formulas, scheme-level double-overlap section transport, and the coordinate Čech/discrete H¹ equivalence are kernel checked. The generating-family fixed-correction transporter criterion is also kernel checked. Triple-overlap/face scheme compatibility, fpqc torsor classification, ten E8/group-identification inputs, and existence of the 135 simultaneous D8 fixed corrections remain open. |

## Section 6

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 6.1 | Primary-source inputs checked; not Lean-formalized | Chernousov Theorem 3.1/Gille Corollary 1(b), Gille Theorem 11, Totaro's page-21 table, and Gille Corollary 9.3.6 all have the required scope. |
| Proposition 6.2 | Manuscript only | The finite orbit and marker data are not reproduced in Lean. |
| Theorem 6.3 | Manuscript only | The finite quadratic-module and Fourier calculations are not formalized. |
| Theorem 6.5 | Source-checked Gille input; manuscript geometry | Gille Corollary 9.3.6 is confirmed; the building-geometric construction is not formalized. |
| Theorem 6.6 | Manuscript only; statement ambiguous | Gauge independence is proved only after fixing the flag. Changing the flag requires an explicit conjugacy identification of the fields and double-coset spaces. |
| Proposition 6.7 | Exact arithmetic/additive shadow in Lean; nonabelian statement unverified | serreIIProgram_a8Gauge_field_degrees, serreIIProgram_a8Gauge_bezout, serreIIProgram_a8Gauge_gcd, and eq_zero_of_serreIIProgram_a8Gauge_annihilators check the numerical and abelian core. The PDF also contains the literal token qquad in the statement. |
| Theorem 6.9 | Exact table arithmetic and index implication in Lean; field claims unreproduced | serreIIProgram_survivorEnvelope_bezout and serreIIProgram_survivorEnvelope_gcd check all five rows; the two- and three-degree point-field lemmas turn each certified gcd-one row into index one once actual point fields exist. The Gille input is source checked, but the GAP double-coset certificate is missing. |
| Theorem 6.10 | Unreproduced computation | The 11171 to 313 to 303 sieve requires absent GAP, CTblLib, and TomLib scripts and raw output. |
| Theorem 6.11 | Unreproduced computation | The 303 to 150 plus 153 to 31 compression depends on the missing table-of-marks computation. |
| Proposition 6.12 | Unreproduced computation | Nonsplitting, fusion, marker, and H1 data for all 31 lifts have not been rerun. |
| Corollary 6.13 | Unverified | Depends on Theorems 6.11 and 6.12. |
| Corollary 6.14 | Citation/computation conditional | Depends on Proposition 6.12 and the corrected Gille marker lemma. |
| Proposition 6.15 | Exact order arithmetic in Lean; group/gauge statement unverified | serreIIProgram_binaryIcosahedral_index_arithmetic checks the displayed orders and indices. The nonsplit lift and descent inputs remain external. |
| Proposition 6.16 | Finite subsystem-orbit input reproduced; theorem still citation conditional | `binaryIcosahedralSubsystemOrbitData_has_small_orbits` checks that every certified projective A5 row has a degree-five (D4)^2 orbit and a degree-six (A4)^2 orbit. The TomLib row/action identification is an external certificate; classical Serre II and the descent argument remain unformalized. |
| Proposition 6.17 | Numerical orbit count reproduced; outer-triality action unverified | The compressed certificate and `binaryIcosahedral_degreeFiveOrbit_total` check the twelve degree-five orbits. They do not prove that the order-three action on a D4 factor is outer trialitarian. |
| Proposition 6.19 | Manuscript only | The oriented transporter and bitorsor descent are not formalized. |
| Proposition 6.21 | Additive restriction and abstract kernel checked | `h1Restriction_tower` instantiates additive (H^1) restriction and its tower law; `eq_zero_of_coprime_restrictions` checks the coprime detection step. Cohomological corestriction and the restriction--corestriction index formula remain unformalized. |
| Proposition 6.22 | Manuscript only | The Weil-restriction dimension and density argument is not formalized. |
| Proposition 6.24 | Manuscript only | The Bass--Serre amalgam and Euler-characteristic calculation are not formalized. |
| Proposition 6.26 | Difference-cocycle and conjugacy logic exact in Lean; computation unreproduced | DifferenceCocycle.lean proves the displayed formula is a nonabelian cocycle and that global or subgroup neutrality is exactly conjugacy of the two representations. The A11 Burnside relation, nonisomorphism, and even local conjugators still require the absent GAP certificate. |
| Corollary 6.28 | Computation conditional | Depends on Proposition 6.26 before the field-theoretic realization. |
| Theorem 6.30 | Abstract projective/lifted generation and common-fixed-point implications in Lean; computation conditional | iSup_eq_top_of_setGcd_indices proves projective generation from gcd-one indices; iSup_comap_eq_top_of_surjective lifts any nonempty generating family through the central quotient; GeneratedFixedPoint.lean proves the common-fixed-point step. The concrete subgroup indices still depend on Theorem 6.10's unreproduced GAP data. |
| Corollary 6.31 | Unverified | Depends on Theorems 6.10 and 6.30. |
| Proposition 6.32 | Exact additive Burnside-basis top-mark obstruction in Lean | `not_mem_addSubgroup_closure_of_mark` proves the abstract mark argument, while `BurnsideAdditive.unit_not_mem_span_properTransitiveOrbits` instantiates it in the free abelian group on conjugacy classes of transitive finite orbit types `G/H`. The multiplicative Burnside ring and its comparison with a categorical finite-`G`-set Grothendieck completion remain unformalized. |
| Proposition 6.34 | Conditional on an open conjecture | The implication uses Conjecture 6.33, Theorems 6.1 and 6.10, and quadratic descent. |
| Proposition 6.35 | Open-equivalence reformulation | The printed equivalence is not independent progress beyond the unresolved E8 case. |
| Lemma 6.36 | **Lean exact abstract kernel** | eq_zero_of_gcd_one_annihilators proves the finite Bezout-annihilator argument. Applying it to H1 still requires the stated restriction--corestriction maps and formulas. |

## Section 7

| Result | Current status | Evidence or blocker |
|---|---|---|
| Lemma 7.1 | Manuscript only | Requires finite-presentation descent for torsors over filtered field unions. |
| Theorem 7.2 | Prime-power endpoint implication in Lean; ILA theorem unformalized | ILA Corollary 4.14 supplies index one only at the cited-source level. PrimePowerIndex.lean proves that a prime-power point-degree spectrum of index one contains an actual degree-one point field. |
| Corollary 7.3 | Source checked with wording correction | The endpoint exclusion follows from Theorem 7.2. Merkurjev Theorem 4 preserves its specially constructed quaternion tensor product and associated anisotropic form, not arbitrary pre-chosen examples. |
| Proposition 7.4 | Manuscript only | The specialization argument for affine torsors over a pure transcendental extension is not formalized. |
| Proposition 7.5 | Partial abstract kernel only | fixed_of_fixed_on_join_eq_top checks the common-fixed-point implication; the Galois and gauge-coset realization is not formalized. |

## Explicitly open items

| Item | Status |
|---|---|
| Conjecture 5.1 | Open odd-degree wonderful descent. |
| Conjecture 5.2 | Open odd-degree Borel descent. The cited E6 comparison is an index-one-to-point theorem for selected flags, not literally a single-extension odd-degree theorem. |
| Conjecture 5.3 | Open odd-degree EVIII descent. |
| Question 5.22 | Open full-Weyl toral neutrality question. |
| Conjecture 6.33 | Open finite-etale kernel norm principle; the product-algebra kernel and componentwise corestriction conventions need formal definitions. |

## Artifact and version defects

1. Theorem 3.2's sign-only chamber normalization is false. The corrected
   statement must choose a chamber-normalized cocharacter or conjugate and
   reindex.
2. Proposition 6.7 contains the literal malformed token qquad where a spacing
   command was intended.
3. Theorem 6.6's phrase “independent of every choice” is only justified after
   fixing the flag.
4. Appendix A names computations but does not include the executable scripts,
   row maps, fusion witnesses, package snapshots, or raw output.
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
