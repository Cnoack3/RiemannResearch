# Serre II E8 formalization: open questions and remaining interfaces

This ledger separates mathematical questions from formalization work. A
missing Lean proof is not called an open mathematical problem when the cited
literature already contains a proof.

## A. Mathematical questions stated by the manuscript

1. **Conjecture 5.1:** odd-degree descent for the wonderful compactification.
2. **Conjecture 5.2:** odd-degree descent for E8 Borel varieties.
3. **Conjecture 5.3:** odd-degree descent for EVIII.
4. **Question 5.22:** full-Weyl toral neutrality and simultaneous fixed
   corrections.
5. **Conjecture 6.33:** the diagonal finite-etale kernel norm.

Proposition 6.35 is an equivalence with E8 Serre II, not independent evidence.

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
