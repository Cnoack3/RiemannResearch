# E8 Serre II proof audit

Last audited: 2026-08-08.

This ledger separates proved mathematics from citation-dependent inputs,
unreproduced finite computations, and open descent targets. It accompanies the
Lean kernels in this repository; it is not a claim that the E8 case of Serre's
Conjecture II has been solved.

For the complete result-by-result status of the attached 5 August 2026 PDF,
see SERRE_II_2026_08_05_THEOREM_LEDGER.md. That artifact has 61 labeled
theorems, propositions, corollaries, and lemmas, plus four conjectures and one
question. Notes below also record checks from other revisions of the program;
packet degrees must therefore be matched to the exact artifact before a Lean
certificate is credited to it.

For exact external statements, hypotheses, URLs, and the result-to-source map,
see SERRE_II_2026_08_05_CITATION_AUDIT.md.

## Theorem 3.2 chamber convention

The intended convention is to choose the regular cocharacter in the chamber
determined by the fixed Borel. Changing its sign then selects which of the
attracting and repelling Bialynicki--Birula conventions is used.

If the sentence is instead read as starting from an arbitrary regular
cocharacter, the kernel-checked A2 calculation
`a2Coroot_sign_normalization_counterexample` shows that neither sign need be
positive on both fixed simple roots. This does not affect the chamber-chosen
theorem used here.

The 8 August revision also corrects the scope of part (iii):
compactification points are equivalent to Borel reductions over every field
extension, whereas Borel reduction detects neutrality only for inner torsors.
The conditional declaration `universalFixedLocusAndSplittingField` now
formalizes this distinction. Its chosen-chamber rank-formula input records the
unformalized tangent-weight calculation, not an extra condition on lambda.

## Lean found a second problem in the binary-icosahedral audit

The universal outer-triality assertion in Proposition 6.17 is false. For the
exact ATLAS integral matrices `2A5G1-Zr8bB0`, the reconstructed certificate
checks that `G=<A,B>` is `2.A5`, that `H=<w,j,r>` is the exact order-24
stabilizer of a degree-five `D4 ⊕ D4` subsystem, and that
`H ≤ W(D4) × W(D4)`. Lean checks the form isometries, subsystem Gram matrix,
reflection factorizations, and the nonidentity order-three element
`r_orderThree_innerD4xD4_counterexample`.

Using the geometrically designated 120-root-pair and 135-singular-vector
TomLib actions across all nine projective A5 rows narrows the matrix class to
`{4015,4017}`. Both are manuscript rows and each has exactly one degree-five
`(D4)^2` orbit. Hence the certified inner orbit is one of those two singleton
orbits, contradicting the claim that all twelve have an outer action on at
least one component. The other eleven root actions remain unverified. TomLib
column geometry remains an explicit external certificate boundary.

The degree-five `A4 ⊕ A4` side and the final two-gauge factorization problem
remain separate. The trialitarian cubic kernel, Allen index, and residual
triality-orbit argument cannot be applied uniformly as printed.

Accordingly, corrected Research Target 8.2 is orbitwise: compute each
degree-five orbit's actual diagram-action image; use an inner/classical
`D4 × D4` source when that image is trivial, and introduce the
orbit-specific cyclic-cubic kernel and centrality target only when the image
is cyclic of order three. After local neutrality is established for every
projective-A5 row, the degree-five/degree-six gauge factorization is still a
separate E8 descent problem. The certificate currently settles one singleton
orbit in `{4015,4017}`; the other eleven diagram actions remain open.

An additional interface audit found that the former existential
`D4PairCentralReduction` was circular: its quotient types, induction map,
and reduced class varied with the point, so a corrected package could be
built exactly when the desired neutrality equality was already available.
That interface and its downstream theorems have been removed.

The replacement `BinaryD4OrbitProvider` chooses one
`D4PairCentralGeometry` for the whole pointed set. Each binary realization
must then select a degree-five orbit from the finite histogram, identify its
inner or cyclic-cubic action branch, realize the class in the fixed quotient,
and prove the matching lift/correction. This repairs the theorem boundary but
does not discharge any of those geometric obligations or the final bilateral
factorization.

## Lean found an omitted kernel after Proposition 7.5

Proposition 7.5 itself is correct: a single point fixed by closed subgroups
which topologically generate the absolute Galois group is rational. The next
paragraph, however, only chooses pro-p lifts whose images generate the finite
presentation quotient. Those lifts need not generate the full absolute Galois
group.

`GroupTheory/QuotientGeneration.lean` gives a finite exact countermodel. The first
factor of `ZMod 2 × ZMod 3` maps onto the quotient `ZMod 2`, but is a proper
subgroup of the ambient group. Adjoining the projection kernel `ZMod 3`
restores generation. The general theorem
`kernel_sup_iSup_eq_top_of_iSup_map_eq_top` now proves that quotient-generating
lifts together with the homomorphism kernel generate the source, and
`fixed_of_fixed_on_kernel_and_quotient_generators` proves the corrected
fixed-point implication. In the Galois application, if `E/k` is the finite
Galois splitting field and `N = Gal(k_s/E)`, Proposition 7.5 must be applied
to `N` together with the pro-p lifts. The known trivialization over `E`
supplies the extra fixed-locus coset. The exact theorem
`isCoboundary_iff_exists_commonLocalGauge_with_kernel` says that neutrality
is equivalent to the intersection of this splitting-field coset and all
prime-local cosets.

## Verified proof kernels

- `GroupTheory/CoprimeRestriction.lean` proves that an element killed by two
  coprime integers is zero, and that a finite family of annihilating degrees
  with integer gcd one detects zero. These are the exact additive
  restriction--corestriction steps used in Lemma 6.36 and the gauge audits.
- `GroupTheory/BurnsideTopMark.lean` proves both the abstract top-mark
  obstruction and its additive Burnside-group instantiation: `[G/G]` is not
  generated by the proper transitive orbit classes `[G/H]`. The model is the
  free transitive-orbit basis; multiplication and comparison with a categorical
  finite-`G`-set Grothendieck completion remain outside the current API.
- `GroupTheory/GeneratedFixedPoint.lean` proves that a *single common point*
  fixed by subgroups whose join is the whole group is globally fixed. It does
  not infer a common point from separately nonempty fixed loci.
- `GaloisCohomology/CompatibleLocalGauges.lean` proves the exact corrected
  Theorem 6.30 criterion: a cocycle is a global coboundary if and only if one
  element is a local gauge on every subgroup of the generating family. This
  equivalence characterizes the missing common gauge; it does not produce one
  from the separately existing local gauges. Its kernel-restored variant
  `isCoboundary_iff_exists_commonLocalGauge_with_kernel` incorporates the
  finite splitting-field gauge required after Proposition 7.5.
- `GroupTheory/GeneratedSubgroupsOfCoprimeIndex.lean` proves that a family of
  subgroups with gcd-one indices generates the whole group and that nonempty
  generating families lift through surjective group homomorphisms.
- `AlgebraicGeometry/PointFieldIndexOne.lean` proves that two coprime or three
  gcd-one actual finite point-field degrees force point-field index one.
- `AlgebraicGeometry/PrimePowerIndex.lean` proves that a degree spectrum made
  of powers of one prime and having gcd one contains degree one, including the
  corresponding finite point-field existence statement used in Theorem 7.2.
- `LinearAlgebra/SplitLift.lean` proves that an explicit module section lifts
  every map into the quotient. Over `F₂[H]` this is exactly the equivariant
  lifting step in the generic 120-place valuation packet.
- `GroupTheory/HalfDifferenceCocycle.lean` verifies the cocycle identity for
  `a_g=(ell-g·ell)/2` and its restriction at an element acting by minus one.
  The field-theoretic existence of the required halves remains a separate input.
- `GroupTheory/OrbitDegreeGcd.lean` proves that if all degrees in three
  finite orbit partitions share a divisor, then that divisor divides the gcd of
  the three total cardinalities. Applied to totals 135, 11200, and 12096, this
  replaces the original 303 row-by-row gcd calculations by one uniform proof.
- `GroupTheory/PerfectCore.lean` proves that a stable derived-series term is
  perfect, has solvable quotient, and is contained in every normal subgroup
  with solvable quotient. It also proves existence of a stable term when the
  subgroup type is finite.
- `GroupTheory/KernelConjugator.lean` proves the even-conjugator correction:
  multiplying a subgroup conjugator on the right by a suitable source-subgroup
  element preserves the conjugated subgroup while moving the conjugator into a
  homomorphism kernel.
- `GroupTheory/CentralExtension.lean` proves that a perfect group cannot
  admit a group-homomorphic splitting over a nontrivial central kernel. This is
  the generic deduction applied to the perfect Weyl lifts in the joint
  certificate.
- `GroupTheory/ModTwoFixedReduction.lean` proves that for a torsion-free
  integral lattice with a central negation action, vanishing of the fixed space
  modulo two forces vanishing at every modulus greater than one. This
  kernel-checks the all-moduli reduction used by the marker certificate.
- `E8/SubgroupSieve.lean` records the reconstructed TomLib class data and
  kernel-checks the 313-to-303 row counts, the 150+153-to-31 perfect-core
  compression, the 14 distinct core orders, the 31 joint lift rows, and the
  uniform subsystem-orbit common-divisor theorem. The association of table
  positions with actual subgroups remains the explicitly documented external
  certificate boundary.
- `E8/A8NormalizerArithmetic.lean` verifies
  `-27 * 15 + 2 * 35 + 336 = 1` and the corresponding annihilator theorem.
- `E8/WeylIndexPacket.lean` verifies the arithmetic of the newly proposed
  maximal-rank reduction packet: `-73 * 135 + 26 * 2240 - 48384 = 1`, gcd one,
  the parity step from total degree 135 to an odd residue degree, and the
  associated additive annihilator theorem. These declarations do not supply
  the geometric fixed-locus or central-reduction inputs.
- `E8/SylowSevenArithmetic.lean` verifies the three packet indices
  `34560`, `61440`, and `4320`, their displayed prime factorizations,
  their congruence to one modulo seven, and the normalizer-index products.
  It does not identify the packet groups or prove the torsor-splitting claim.
- `E8/A9TrialityArithmetic.lean` checks both signed half-spin residue lists
  for the order-nine calculation and verifies `Φ₃(1)Φ₉(1)=9`. It assumes the
  triality model and does not construct the `A₉` Weyl embedding.
- Application-specific numerical certificates live with their subjects:
  `E8/SubgroupSieve.lean` owns the subsystem and survivor-envelope rows, and
  `E8/A8NormalizerArithmetic.lean` owns the A8 gauge calculations.
- `E8/A2ChamberNormalization.lean` and `E8/SylowLocalSplitting.lean`
  isolate the chamber counterexample and finite four-field package.
- `E8/SectionSevenAppendixAudit.lean` checks the printed Section 7 and
  Appendix arithmetic. `GroupTheory/QuotientGeneration.lean` supplies the
  quotient-generation countermodel and kernel-adjoining repair for the
  paragraph after Proposition 7.5.
- `E8/BinaryIcosahedralArithmetic.lean` checks the orders and fixed-field
  degrees `5`, `6`, and `30`, their coprimality, the Proposition 6.22
  dimension inequality `11 d < 30 d` (including `2728 < 7440` at
  `dim E8 = 248`), and the Proposition 6.24 Euler-characteristic and
  rank-`20` arithmetic. It also proves the generic guard that a nontrivial
  perfect group is nonsolvable. The geometric and Bass--Serre inputs remain open.
- `E8/BinaryIcosahedralAtlas.lean` checks the Appendix-A words and relations
  and the `D4 ⊕ D4` Gram matrix. `E8/BinaryIcosahedralTrialityCounterexample.lean`
  checks the form isometries, inner reflection image, and the nonidentity
  order-three counterexample used in the Proposition 6.17 audit.
- `LinearAlgebra/RootSystem/AdaptedBase.lean` proves the equivalent reindexing
  convention: a functional regular on every root admits a base on which all
  simple-root values are positive.
- `GroupTheory/CoxeterAttractingRank.lean` constructs a maximal-length element
  in every finite Coxeter group and proves the general inversion, descent-count,
  unique-zero, and rank-duality results. `E8/CoxeterAttractingRank.lean` contains
  only the E8 specialization. Mathlib still lacks a `Finite` instance for its
  presented E8 group, the complement theorem, and the E8 maximal-length
  calculation `120`.
- `AlgebraicGeometry/FpqcCover.lean` defines witnessed covers and refinements;
  `FpqcCechPullback.lean` contains generic refinement pullback; and
  `FpqcCechH1.lean` contains only the affine-group fixed-cover H¹ API.
- `AlgebraicGeometry/FpqcCoverCommonRefinement.lean` proves that two arbitrary
  indexed witnessed fpqc covers have a witnessed common refinement formed by
  pairwise fiber products, together with refinement maps to both inputs.
- `AlgebraicGeometry/FpqcH1.lean` proves refinement-map independence and forms
  the global universe-indexed Čech H¹ quotient across witnessed fpqc covers,
  with refinement invariance and a canonical neutral class.
- `AlgebraicGeometry/FpqcTorsor.lean` defines fpqc torsors as simply
  transitive group actions with flat, surjective, quasi-compact structure maps
  and proves the generalized-point criterion for simple transitivity. Effective
  fpqc descent, torsor classification, and cross-universe comparison remain open.
- `GaloisCohomology/GaloisTensorDecomposition.lean` constructs the canonical
  finite-Galois equivalence `L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L)` and proves
  the pure-tensor formula `(x ⊗ y)(σ) = x * σ y`. This is the first
  scheme-overlap prerequisite for comparing Čech and discrete cocycles.
- `GaloisCohomology/GaloisTripleTensorDecomposition.lean` iterates that
  equivalence on the triple overlap and proves the independent-coordinate
  formula `(x ⊗ (y ⊗ z))(σ,ρ) = x * σ(y) * ρ(z)`, the algebraic identity
  needed to translate the Čech cocycle equation.
- `GaloisCohomology/GaloisAffineCechCoordinates.lean` transports affine
  group points through the finite-Galois double and triple tensor
  decompositions and proves all three face formulas, including the twisted
  `σ • f(σ⁻¹ρ)` face.
- `GaloisCohomology/GaloisCechSchemeBridge.lean` identifies the chosen
  scheme-level double and right-associated triple overlaps with the spectra of
  `L ⊗[K] L` and `L ⊗[K] (L ⊗[K] L)`. It transports represented affine-group
  sections first to convolution algebra maps and then directly to one- and
  two-variable Galois-indexed points. Compatibility of the three categorical
  face morphisms with the checked algebraic face maps remains open.
- `GaloisCohomology/GaloisCechComparison.lean` computes all three Čech face
  maps in Galois coordinates, proves coordinate Čech cocycles and gauge classes
  equivalent to discrete nonabelian cocycles and H¹, and constructs the actual
  singleton fpqc cover. The remaining specialization must prove that the
  chosen overlap isomorphisms intertwine the three categorical face morphisms.
- `GaloisCohomology/SingletonCechH1.lean` proves the generic Yoneda step for
  every presheaf of groups: cochains are sections on the double overlap,
  cocycles satisfy one equation on the triple overlap, and cohomology is the
  universal gauge relation. The final scheme-over-pullback transport and
  global torsor classification remain separate inputs.
- `GaloisCohomology/NonabelianH1.lean` constructs discrete nonabelian
  one-cocycles modulo gauge, their neutral class, subgroup restriction, and
  coefficient pushforward. It proves that both operations preserve neutrality;
  it does not yet identify these classes with fpqc algebraic-group torsors.
- `E8/FullWeylCore.lean` now specializes the conditional Theorem 5.19
  assembly to actual discrete nonabelian H¹. The forward restriction-neutrality
  implication is supplied by the generic checked restriction theorem, not a
  local hypothesis. The converse quadratic kernel and every E8/group-specific
  input remain explicit and load-bearing.
- `GaloisCohomology/LocalGaugeTransporter.lean` proves the exact abstract
  transporter criterion: local gauges on subgroups generating the Galois group
  glue to a global gauge exactly when their transitions factor through
  subgroup-fixed corrections. It also proves overlap fixedness, gauge
  covariance, and triple-overlap composition. Its anchored criterion reduces
  the 135-`D8` system to one element `c₀`: for every stabilizer `H i`,
  `transition u i i₀ * c₀` must be fixed by `H i`. In the full-Weyl EVIII
  specialization, existence of this `E8`-valued anchor remains open.
- `GaloisCohomology/DifferenceCocycle.lean` proves the representation-difference
  cocycle used in Proposition 6.26, identifies global and subgroup
  coboundaries with conjugacy, and proves that two local simultaneous
  conjugacies plus failure of global conjugacy give a nonneutral H¹ class with
  two neutral restrictions.
- `GaloisCohomology/TwoGaugeDescent.lean` proves the exact nonabelian
  two-gauge criterion: when two subgroups generate the Galois group, a cocycle
  with local gauges is a global coboundary exactly when their transition
  factors through the two fixed-point groups. It deliberately does not assert
  that the distinguished E8 transition factors.
- `GaloisCohomology/TwoGaugeDoubleCoset.lean` repackages that criterion as
  identity membership in an explicit subgroup double coset and defines the
  strict oriented subgroup transporter used by Proposition 6.19. It proves
  the combined transporter-and-double-coset equivalence, but deliberately
  leaves the actual E8 transporter incidence and Research Target 8.1
  factorization as open providers.
- `GroupCohomology/Conjugation.lean` constructs the additive H¹ isomorphism
  for conjugate subgroups, proves restriction--conjugation naturality after
  canonical coefficient transport, and proves that inner conjugation acts
  trivially on H¹. It does not assume transfer or the Mackey formula.
- `GroupCohomology/Restriction.lean` packages Mathlib's additive
  group-cohomology map as (H^1) restriction, proves identity and composition,
  and supplies explicit comparison isomorphisms and tower laws for nested
  `Rep.res` coefficient objects.
- `GroupCohomology/Corestriction.lean` constructs quotient representatives
  and their subgroup-valued defects, defines the normal finite-index additive
  corestriction, proves preservation of cocycles and coboundaries, and descends
  it to additive H¹. It also proves the cocycle formula
  `Cor (Res z) = [G:S] • z + d(potential)` and hence
  `Cor ∘ Res = [G:S]` on additive H¹. The nonnormal Mackey formula and the
  reverse stable-elements inclusion remain open. None of these declarations
  defines a corestriction on nonabelian H¹, which is only a pointed set.
- `GroupCohomology/StableElements.lean` proves by explicit averaging that
  additive `H^1` of a finite group vanishes when its order is a unit, then
  combines this with inflation--restriction to prove injectivity on `H^1`
  for normal finite-index subgroups of unit index. It also defines the
  stable-elements submodule and proves that the image of ambient restriction
  is contained in it. The reverse inclusion, and hence Brown's full
  stable-elements characterization, still needs cohomological transfer and
  Mackey theory.
- `Logic/PointedKernel.lean` proves that trivial neutral fibers compose and
  iterates them through arbitrary finite dependent towers. This is the exact
  pointed-set step for cyclic kernel theorems along a solvable composition
  series; it does not prove the cyclic E8 theorem.

All supporting files build in the full project and use no `sorry` or new
axioms.

## Source-audited advances across manuscript revisions

These items are mathematical/source audits, not claims of complete Lean
formalization. The attached artifact's exact status is in the theorem ledger.

0. A general fixed-packet lemma is now isolated: if a connected maximal-rank
   subgroup H has neutral H1-image after every finite extension, the maximal-
   torus fixed locus in the twisted reduction variety is finite etale of degree
   [W(G):W(H)], and every one of its residue fields splits the torsor. Applied
   to D8, (A2)^4, and (A4)^2 in the source-correct Theorem 5.16 packet, this
   yields splitting cycles of degrees 135, 11200, and 12096. Totaro's separate
   A2E6 row has index 1120. The named Lean cycle
   `-1417 z_D8 + 16 z_(A2)^4 + z_(A4)^2` has degree one. The geometric proof
   is informal/source-audited; the degrees, labels, and signed identity are
   audited against Totaro Section 8 and kernel checked arithmetically in
   E8/SubgroupSieve.lean.
1. After choosing a chamber-normalized cocharacter and supplying the
   characteristic-zero descent, the one-sided wonderful compactification has
   the same point fields as the twisted Borel variety. For inner torsors these
   are also exactly the neutralizing fields, and the compactification, Borel,
   and torsor indices agree. The fixed locus consists of Weyl-indexed copies
   of the twisted Borel variety, with attracting rank
   `length(w) + rightDescent(w)`. This uses the intended convention that
   `lambda` was chosen in the chamber determined by the fixed Borel.
2. More generally, for any split connected semisimple group in characteristic
   zero, index one splits the integral Chow motive of every associated twisted
   flag into the same Tate summands as the split flag. If a torsor has a finite
   separable splitting field of degree prime to p, the analogous statement
   holds for every positive-height free p-local algebraic Morava K-motive.
3. Every actual A5 subgroup of the E8 Weyl group has a finite toral marker. A
   central-twisted S5 embedding shows that a rational marker need not exist
   before a quadratic base change.
4. In the A8 envelope, the point, plane, and Sylow-5-normalizer fields have
   degrees 15, 35, and 336. The normalizer has order 60 and is solvable, so the
   three fields neutralize the class under the cited cyclic-descent theorem.
   Their degrees have gcd one, but this does not solve the nonabelian gauge
   intersection.
5. The explicit SL(2,5)/A11 construction is a genuine finite nonabelian H1
   countermodel to formal two-gauge gluing. Its Burnside restriction relation,
   global orbit mismatch, parity corrections, local even conjugators, and
   joint A11 image are now reproducible. It is not an E8 counterexample.
6. The uniform binary-triality claim is invalid. The ATLAS matrix class is
   narrowed to `{4015,4017}` by the designated root-pair and singular-vector
   actions; both rows have one degree-five orbit. Its exact stabilizer
   `H ≃ 2.A4` acts through `W(D4) × W(D4)`, so one of those singleton orbits
   has trivial outer image. The other eleven root actions remain unverified.

## Primary-source citation audit

The exact text of Gille, LNM 2238, Corollaries 9.3.6 and 9.3.7 has now been
checked. Both have the hypotheses used in the memorandum: 2, 3, and 5 are
invertible and scd_l(k) <= 2 for l = 2, 3, 5. Corollary 9.3.6 says that a
non-almost-abelian E8 form is split; Corollary 9.3.7 says that an E8 form
containing a k-subgroup mu_n, n >= 2, is split. Thus the external Gille inputs
in Theorems 4.3 and 4.5, and in their subsystem and finite-marker descendants,
are source confirmed. They are still not formalized in Lean.

The printed LNM Theorem 8.4.1(2) has a separate proof-scope problem: its
reduction to cyclic layers does not justify nonsolvable A5 or S5 Galois groups.
The official 26 May 2026 errata repairs characteristic and degree-five inputs
but not that reduction. This does not infect Corollary 9.3.6: Proposition
9.3.5 first supplies a solvable splitting extension, and Gille 2001 Theorem 11
can then be iterated along a composition series.

The motivic citations in Theorem 4.9 are also exact: CGM Theorem 8.2 gives
integral Rost nilpotence and Sechin--Semenov Lemma 7.8 gives the split-motive
criterion. The uniform prime-to-p transfer proof of Theorem 4.11 is valid with
the oriented version of this formalism. Its citation to Semenov Theorem 6.16
is too broad, however: that theorem's E8 clause treats p=2 and heights at least
4, not all primes and positive heights.

The Lean bridge now reaches Mathlib's actual integral algebraic-cycle type:
`IntegralCycleQuotients` constructs quotients by supplied linear relations and
descends relation-preserving maps. `IntegralCorrespondenceComposition`
contains supplied bilinear composition on cycles over scheme products,
including associativity and diagonal identity laws. Given additionally supplied
correspondence-ring structures, a geometric base-change ring homomorphism, and
Rost nilpotence, `IntegralProjectorLifting` specializes projector and
complete-projector-family lifting to those concrete quotient carriers. This is not yet a construction of Chow groups or motives. Mathlib
currently supplies weighted proper pushforward of cycles but not the
rational-equivalence subgroup, codimension grading, flat pullback, intersection
product, or the proof that intersection--pushforward composition preserves
rational equivalence. Those are the precise geometric inputs still separating
the new quotient interface from CGM's Chow-correspondence endomorphism rings.

Evens--Jones supports the wonderful-compactification tangent weights over the
complex numbers, but not, by itself, the arbitrary characteristic-zero
descent. Theorem 3.2 is read with its regular cocharacter chosen in the chamber
determined by the fixed Borel. The Lean A2 calculation only guards against a
literal arbitrary-cocharacter reading, while the adapted-base theorem checks
the equivalent reindexing convention.
`e8AttractingRank_properties_of_lengthComplement` reduces the remaining
Coxeter duality package to one explicit E8 length-complement identity. Mathlib
does not yet supply a finite/longest-element instance for its presented E8
Coxeter group, and the fixed-scheme, tangent-weight, motive, and descent
arguments remain conditional.

## Restored computer-assisted certificates

The previously omitted exhaustive subgroup-sieve and perfect-core computations
have now been independently reconstructed, rerun, and committed with their raw
output.

- `Certificates/O8_PLUS_2_SUBGROUP_SIEVE_CERTIFICATE.md` contains the exact
  GAP script, raw output, compact JSON, package versions, source-data hashes,
  and the maximal-overgroup argument. It exhausts all 11,171 TomLib classes
  relative to the eight source-matched stabilizer columns, verifies the three
  triality-correlated sieves `11171 -> 313 -> 303`, and checks the compression
  `303 = 150 + 153 -> 31` with 14 distinct core orders. The script does not
  itself construct the eight E8 root-subsystem actions and derive those TomLib
  column positions.
- `Certificates/O8_PLUS_2_COVER_MARKER_CERTIFICATE.md` contains the joint
  Weyl-cover/module script, raw output, compact JSON, and abstract-type
  validation. A single shared TomLib identification avoids triality
  misalignment and verifies that all 31 aligned perfect-core lifts are
  nonsplit and have zero fixed space on the E8 lattice modulo two. The generic
  passage from mod-two fixed-freeness to every modulus is kernel checked in
  `GroupTheory/ModTwoFixedReduction.lean`; the nonsplitting deduction from a
  perfect lift with nontrivial central kernel is kernel checked in
  `GroupTheory/CentralExtension.lean`.
- `Certificates/A5_SUBSYSTEM_ORBITS_CERTIFICATE.md` contains the rerunnable
  table-of-marks script and raw output for the four triality-aligned projective
  A5 rows. `BinaryIcosahedralSubsystemOrbits.lean` checks the compressed
  orbit histograms, the degree-five multiplicities `[5,5,1,1]`, six
  degree-six orbits in every row, and the total of twelve degree-five orbits.
  It does not assert the outer-triality action on either D4 factor.
- `Certificates/A5_TRIALITY_COUNTERCERTIFICATE.md` contains the exact ATLAS
  matrices and GAP/TomLib script comparing the designated root-pair and
  singular-vector actions. It narrows the class to `{4015,4017}`, proves the
  displayed `2.A4` is the exact degree-five `(D4)^2` stabilizer, and checks
  that it lies in `W(D4) × W(D4)`. Lean independently checks the matrix
  counterexample. Thus the universal outer-triality assertion is false.
- `Certificates/A11_BURNSIDE_GLUING_CERTIFICATE.md` contains the deterministic
  GAP 4.16/TomLib/CTblLib script and raw output for Proposition 6.26. It checks
  the rank-10 combined restriction matrix, the Burnside kernel vector, the
  distinct global orbit packets, odd centralizer corrections, even local
  simultaneous conjugators, failure of a global conjugator, and joint image
  A11. `A11BurnsideCertificate.lean` checks the embedded matrices and every
  printed permutation equation. The GAP row/action identification remains
  external, and Corollary 6.28's field realization is not formalized.
- The old 303 row-by-row orbit gcd computation is no longer needed. The Lean
  theorem
  `omegaEightPlusTwo_subsystemOrbitDegree_commonDivisor_eq_one` proves the
  conclusion uniformly from the three orbit-partition totals 135, 11200, and
  12096.

These statements are now reproducible computer-assisted inputs rather than
unreproduced premises. Their finite numerical content is still deliberately
separated from the Lean trust boundary: Lean checks the general deductions and
the embedded data; GAP/TomLib certifies the table computations; and Totaro's
classification plus source-level matching supplies the geometric identification
of the eight subsystem-stabilizer columns.

The Appendix-A matrix row remains reproduced by exact integer computation and
Lean reflection certificates. The subsystem-orbit data for all four projective
A5 rows are reproduced, so Proposition 6.16's finite orbit input and the count
of twelve orbits in Proposition 6.17 are no longer missing. The stronger
universal outer-triality assertion is false: the ATLAS certificate narrows the
row to `{4015,4017}`, each with one degree-five orbit, and its exact stabilizer
acts inner on both factors. The other eleven root actions are not certified.

### Rational-involutions / Weyl-7 audit (27 July 2026 draft)

`E8/RationalInvolutionsAudit.lean` contains the incidence, binary, determinant,
and dimension certificates. `E8/SylowSevenHyperbolicModel.lean` contains the
256-vector computation. The reusable norm, odd-degree restriction, and boundary
fiber arguments live in focused GroupTheory and GroupCohomology modules:

- the 15 by 15 complement-incidence row sums, trace, and Gram identity;
- all three printed XOR inconsistency certificates;
- the universal factor-16 determinant formula and its minimizing vector;
- the Cartan-transporter dimension and equation-count arithmetic;
- the finite cohomology rank and packet-stabilizer order arithmetic;
- the complete order-seven action on the 256-vector hyperbolic model,
  including the 135 singular vectors, two fixed points, nineteen
  seven-orbits, the 5/5/5/4 sum distribution, and perpendicularity of every
  balanced orbit;
- the 15 + 120 atomic partition and both vector-sum certificates;
- the no-symmetric-nonabelian-norm argument, odd-degree injectivity modulo
  two, and the affine-kernel-torsor argument for transgression witnesses.

The exhaustive proofs use decide with increased reduction depth, not
native_decide; theorem source scans therefore show no generated
compiler-trust axioms. Wolfram Language independently reproduced the
incidence Gram identity, determinant, and XOR values.

This does not turn the paper's algebraic-group, finite-group identification,
Galois-cohomology, or packet-compatibility assertions into Lean theorems.
They remain source-level mathematical inputs or open research obligations;
none has been hidden behind a project-local axiom, sorry, or admit.

## Exact remaining gap and scope

No counterexample and no proof of the general E8 case is currently certified.
The zero-cycle/index theorem supplies index one for the relevant E8 torsors.
The irreducible remaining proposition is index-one effectivity:

```
pointFieldIndex isFinite degree (splitsOver ξ) = 1
  → ξ = FpqcH1.neutral R A.
```

Under the index-one theorem this proposition is equivalent to E8 Serre II;
it is not a consequence of triple-overlap bookkeeping, fpqc torsor
classification, additive H¹ transfer, group-scheme geometry, or motivic
splitting. A general proof would resolve the still-open coprime-degree
injectivity question for this case.

The abstract full-Weyl transporter criterion is kernel checked, but the
assertion that its 135 local `D8` gauges admit simultaneous fixed corrections
is open and is equivalent to neutrality on the full-Weyl stratum.

For the bounded binary floor, let `H ≃ 2.A4`, `K ≃ Dic5`,
`C = H ∩ K ≃ C4`, and let `L5`, `L6`, and `M` be their fixed fields.
The subgroup calculation gives degrees `5`, `6`, and `30`. Cyclic
relative E8 vanishing along solvable towers neutralizes the class over `L5`
and `L6`.

For local gauges `g5` and `g6`, put
`δ = g5 * g6⁻¹ ∈ G(M)`. The exact unresolved theorem is

```
ξ = 1  ↔  δ ∈ G(L5) G(L6).
```

Equivalently, the factorization fiber `Xδ` is the original E8 torsor. It has
points over extensions of degrees five and six, hence point-field index one,
but producing an F-point is precisely the unresolved E8 effectivity problem.
The theorem `isCoboundary_iff_transition_factorization` kernel-checks this
equivalence at the discrete cocycle level.

The D2E restriction--corestriction identity is exact but tautological at its
last step: the resulting difference is the original torus class, and asking it
to lie in the pointed torus kernel is exactly asking that `ξ` be neutral.
The same boundary is now kernel checked for the finite-etale formulation.
`eq_neutral_of_finiteEtaleKernelNorm` proves the repeated-product diagonal
assembly of Proposition 6.34, while
`finiteEtaleKernelNorm_of_subsingleton_target` proves the reverse direction
of Proposition 6.35 once the E8 cohomology target is a subsingleton.
`zmodTwo_diagonalKernelNorm_counterexample` supplies an abstract model in
which the restriction--corestriction degree formula, a positive annihilator,
the Bezout congruence, and local neutral fibers all hold but the diagonal
corestriction is nonneutral. Thus the missing kernel-norm hypothesis cannot be
recovered from additive transfer alone. Thang proves it over local/global
characteristic-zero fields; the cited norm-principle results do not extend it
to arbitrary cohomological-dimension-two fields in type E8.
Likewise finite-module cohomology does not remove the same-field Kummer defect
`κ_{E,120}(α)`; multiplication by 120 on `T(E)` need not be surjective.

Gille, LNM 2238, Theorem 8.4.1(2), is printed with a scope that would kill the
binary case immediately, since `[E:F] = 120 = 2^3 * 3 * 5`. Its proof,
however, reduces by induction to cyclic degrees two, three, and five. That
reduction proves the solvable case but does not cover the perfect nonsolvable
group `SL2(5)`. The official errata dated 26 May 2026 repairs other inputs
but not this reduction. Thus the binary case is a literal consequence of the
printed statement if accepted, but is not independently secured by the proof
given there.

Finally, solving the binary floor would not settle full split E8 Serre II. The
reported sieve leaves 31 perfect projective-core classes, with `2.A5` only
the smallest and no valid reduction of all remaining cores to it. Conversely,
a point-free distinguished `Xδ` in this row would be a genuine index-one E8
torsor and hence a full Serre-II counterexample.

## Checkpoints

- `39351922`: coprime restriction detection.
- `504301ef`: generated-subgroup common-fixed-point theorem.
- `d97f23fe`: A8 normalizer Bezout detection.
