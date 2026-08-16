# Serre II E8 formalization: open questions and remaining interfaces

This ledger separates mathematical questions from formalization work. A
missing Lean proof is not called an open mathematical problem when the cited
literature already contains a proof. The exact finite completion route and
its reference list are in `SERRE_II_COMPLETION_PROOF_OBLIGATIONS.md`.

## A. Mathematical questions stated by the manuscript

1. **Conjecture 5.1:** odd-degree descent for the wonderful compactification.
2. **Conjecture 5.2:** odd-degree descent for E8 Borel varieties.
3. **Conjecture 5.3:** odd-degree descent for EVIII.
4. **Question 5.22:** full-Weyl toral neutrality. After choosing one of the
   135 D8 gauges as an anchor, the exact remaining transporter input is one
   E8-valued element satisfying the 135 anchored fixedness conditions.
5. **Conjecture 6.33:** the diagonal finite-etale kernel norm.
6. **Research Target 8.1:** binary-icosahedral constrained factorization. For
   the degree-five and degree-six local gauges, prove that the transition
   `delta = g5 * g6⁻¹` lies in the product of their two fixed-point groups;
   in the intended E8 field realization this is `delta ∈ E8(L5) E8(L6) ⊆ E8(M)`.
7. **Certified-survivor common gauge:** for each of the 31 perfect subsystem-
   free lifts, prove simultaneous E8-gauge compatibility on the admissible
   toral-cocycle locus. Binary Target 8.1 and full-Weyl Question 5.22 are the
   smallest and largest instances. After the four binary rows and the full-
   Weyl row, 26 cases remain.

Lean's `pointDescentAt_iff_of_pointwise_iff`, together with the pointwise
equivalences assembled in `universalFixedLocusAndSplittingField`, verifies
that the wonderful, Borel, and neutral-class odd-descent formulations are
equivalent once their geometric inputs are supplied. It does not prove any
one of them. The declarations `alternatingGroup_fin_five_card_prime_support`
and `alternatingGroup_fin_five_not_solvable` certify that A5 satisfies the
printed `{2,3,5}` prime support but cannot be reached by a solvable cyclic-
prime tower; hence the displayed induction in the cited source is insufficient.

The declarations `isCoboundary_iff_one_mem_fixedPointDoubleCoset` and
`isCoboundary_iff_orientedTransporter_and_doubleCoset` now verify the exact
coefficient-free reduction behind Research Target 8.1. They do not prove
that the distinguished E8 double coset contains the identity. That remaining
existence statement requires the actual `2.A5` field/gauge realization, the
oriented E8 torus transporter, and a geometric factorization or section.
The declarations `normalizedTwoGauge_values`,
`normalizedTwoGauge_value_of_eq_mul`, and
`transition_isAdmissibleTwoGaugeTransition` sharpen the target further. A
genuine transition is fixed by the overlap and satisfies every crossing
relation obtained from a refactorization `k * h = h' * k'`; after one gauge
normalization it determines the cocycle on every supplied `H * K`
factorization. Consequently
`isCoboundary_of_admissible_orientedTransition_factorization` reduces the
missing E8 input to factorization on the intersection of this admissible locus
with the oriented transporter. It still does not prove that restricted
factorization.

The sharper declarations
`mem_orientedSubgroupTransporter_iff_leftQuotient_mem_centralizer` and
`isCoboundary_of_selfCentralizing_conjugateTarget` identify the final
basepoint obstruction. Once the target maximal torus is self-centralizing and
H-fixed, neutrality follows from one K-fixed point of the strict oriented
transporter. In the intended field realization this asks for an
`L6`-rational oriented conjugator; equivalently, the associated
maximal-torus torsor class in `H^1(L6,T5)` must vanish. Self-centralization
is standard for maximal tori in connected reductive groups
([SGA 3, Expose XII](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo12.pdf)).
By contrast, [Beli--Gille--Lee, Proposition
2.5.3](https://arxiv.org/pdf/1411.6808) reduces the oriented transporter to a
torus torsor but does not produce a rational point. Cohomological dimension
two alone does not force first cohomology of tori to vanish, so this rational
basepoint is the remaining E8/EVIII arithmetic theorem, not a formal
group-theoretic consequence.

Moreover, Proposition 6.17's corrected countercertificate shows that a
cyclic-cubic outer-triality kernel is not uniformly unavoidable: at least one
degree-five `(D4)^2` orbit has inner order-three action.

Proposition 6.35 is an equivalence with E8 Serre II, not independent evidence.
Lean checks the abstract two-way implication in
`universalFiniteEtaleKernelNormPrinciple_iff_all_classes_neutral`, under
explicit restriction-corestriction and local Bezout data. Moreover,
`diagonalKernelNorm_iff_neutral` verifies that after the Proposition 6.34
Bezout choice, the requested diagonal kernel membership is exactly neutrality
of the original class, not an independent additive lemma. The E8 instance of
the kernel-norm principle—Conjecture 6.33—remains open.
Thang's corestriction theorem proves the required kernel principle over local
and global characteristic-zero fields, not arbitrary fields of cohomological
dimension at most two. Barquero--Merkurjev's norm principle is tautological for
centerless E8, and Bhaskhar's injectivity theorem explicitly excludes E8.

## B. Resolved convention and statements requiring correction

**Theorem 3.2 convention (resolved).** Choose the regular cocharacter in the
chamber determined by the fixed Borel; changing its sign only selects the
attracting convention. Lean now records this interpretation. The rank-formula
binder represents the tangent-weight proof still to be formalized, not an
additional hypothesis on the cocharacter.

The remaining statement-level corrections are:

1. **Proposition 6.17.** The universal outer-triality assertion for all twelve
   degree-five `(D4)^2` orbits is false. The numerical orbit count survives.
2. **Theorem 6.6.** “Independent of every choice” is only established after
   fixing the flag; changing it needs an explicit conjugacy identification.
3. **Theorem 6.30.** Retitle it “Generating subsystem family and exact
   common-gauge criterion.” Its conclusions are: the subsystem groups
   generate; every local gauge coset is separately nonempty; and global
   neutrality is equivalent to nonemptiness of their total intersection. It
   does not assert that this intersection is nonempty. Lean checks the exact
   equivalence in `correctedTheorem630`.

### Corrected Research Target 8.2: orbitwise `(D4)^2` source

For each of the twelve degree-five subsystem orbits `O`, determine the actual
image of its stabilizer in the diagram automorphism group and use the
orbit-specific extension `L_O^inn/L_{5,O}` which kills that image.

- If the action is already inner, treat the source as inner/classical
  `D4 × D4` over `L_{5,O}`; no cyclic-cubic triality kernel is available or
  needed.
- If the image is cyclic of order three, retain an orbit-specific centrality
  target for the toral-source part of
  `ker(H¹(L_{5,O}, M_sc) → H¹(L_O^inn, M_sc))`.
- Establish a locally neutral `(D4)^2` source for every projective-A5 row,
  then separately prove the bilateral degree-five/degree-six E8 gauge
  factorization.

The exact ATLAS countercertificate resolves one singleton orbit in the row
pair `{4015,4017}` as inner; the diagram actions on the other eleven orbits
remain unverified. Consequently the original Target 8.2 cannot assume a
trialitarian cyclic-cubic kernel uniformly across all twelve orbits.

Lean now separates the four projective-order-60 survivors—table classes
`4013`, `4014`, `4015`, and `4017`—from the other twenty-seven rows.
`eq_neutral_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions`
replaces common-gauge existence on those four rows by an explicit D4-pair
central reduction whose two-torsion residue has a cubic correction. This is
a conditional reduction, not a construction of the D4-pair subgroup, its
H2 boundary, or the orbit-specific cubic correction.

## C. Published-proof layers still to formalize

These are formalization tasks, not claims that the mathematics is open.

- A split reductive E8 Chevalley group scheme: full root datum, Chevalley Hopf
  algebra, integration of the Serre Lie algebra, smoothness, reductivity,
  Borels, tori, centralizers, normalizers, and Weyl-group identification.
- Effective fpqc descent and the equivalence among affine-group torsors,
  global Cech H1, and finite-Galois nonabelian H1.
- Arbitrary-subgroup cohomological corestriction, Mackey's double-coset
  formula, and the reverse Brown stable-elements inclusion.
- Wonderful-compactification fixed loci, tangent calculations,
  chamber-corrected attracting ranks, and descent over the ground field.
- Rational equivalence, Chow groups, intersection products, correspondences,
  Chow motives, Tate twists, geometric Rost nilpotence,
  Bialynicki-Birula decomposition, and algebraic Morava K-theory.
- EVIII/HSpin16 geometry, Picard-Brauer boundary, and purity.
- The cited cyclic kernel, toral lifting, Gille, transfer/index-one, Totaro,
  Poitou-Tate, Hasse-principle, Chebotarev, and cohomological-dimension
  theorems.
- Filtered field descent/specialization and field realization connecting
  finite group certificates to E8 torsors.

## D. Certificate-to-geometry interfaces

The GAP/TomLib certificates reproduce the finite subgroup sieve, A5 subsystem
orbit counts, the triality counterexample, and A11 Burnside-gluing data. The
external boundary is the identification of rows/actions with the intended E8
subsystems, flags, gauges, fusion, nonsplitting, and H1 meanings.

- Proposition 6.12 still needs all 31 lifts connected to their claimed data.
- Theorem 6.9 still needs the point fields and double-coset geometry.
- Corollary 6.28 still needs field realization and cohomological dimension.
- Concrete E8 meanings in 6.10–6.14, 6.21, and 6.30 remain conditional.

## E. Three completion routes

The project kernel-checks the implication from each sufficient package, but
not its E8 hypotheses:

1. odd-degree point descent for the corrected wonderful compactification;
2. compatible simultaneous fixed corrections for full-Weyl descent;
3. the diagonal finite-etale kernel norm.

Older prose saying the Section 6 scripts or raw outputs are absent is stale.
Current documentation must record the certificate-to-geometry boundary above.
