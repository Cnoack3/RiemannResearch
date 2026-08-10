# Serre II E8 formalization: open questions and remaining interfaces

This ledger separates mathematical questions from formalization work. A
missing Lean proof is not called an open mathematical problem when the cited
literature already contains a proof.

## A. Mathematical questions stated by the manuscript

1. **Conjecture 5.1:** odd-degree descent for the wonderful compactification.
2. **Conjecture 5.2:** odd-degree descent for E8 Borel varieties.
3. **Conjecture 5.3:** odd-degree descent for EVIII.
4. **Question 5.22:** full-Weyl toral neutrality. After choosing one of the
   135 D8 gauges as an anchor, the exact remaining transporter input is one
   E8-valued element satisfying the 135 anchored fixedness conditions.
5. **Conjecture 6.33:** the diagonal finite-etale kernel norm.

Lean's `pointDescentAt_iff_of_pointwise_iff`, together with the pointwise
equivalences assembled in `universalFixedLocusAndSplittingField`, verifies
that the wonderful, Borel, and neutral-class odd-descent formulations are
equivalent once their geometric inputs are supplied. It does not prove any
one of them. The declarations `alternatingGroup_fin_five_card_prime_support`
and `alternatingGroup_fin_five_not_solvable` certify that A5 satisfies the
printed `{2,3,5}` prime support but cannot be reached by a solvable cyclic-
prime tower; hence the displayed induction in the cited source is insufficient.

Proposition 6.35 is an equivalence with E8 Serre II, not independent evidence.
Lean checks the abstract two-way implication in
`universalFiniteEtaleKernelNormPrinciple_iff_all_classes_neutral`, under
explicit restriction-corestriction and local Bezout data. The E8 instance of
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
