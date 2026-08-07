# E8 Serre II proof audit

Last audited: 2026-08-06.

This ledger separates proved mathematics from citation-dependent inputs,
unreproduced finite computations, and open descent targets. It accompanies the
Lean kernels in this repository; it is not a claim that the E8 case of Serre's
Conjecture II has been solved.

## Verified proof kernels

- `GroupTheory/CoprimeRestriction.lean` proves that an element killed by two
  coprime integers is zero. This is the exact additive
  restriction--corestriction step used in the A8 and binary gauge audits.
- `GroupTheory/GeneratedFixedPoint.lean` proves that a *single common point*
  fixed by subgroups whose join is the whole group is globally fixed. It does
  not infer a common point from separately nonempty fixed loci.
- `LinearAlgebra/SplitLift.lean` proves that an explicit module section lifts
  every map into the quotient. Over `F₂[H]` this is exactly the equivariant
  lifting step in the generic 120-place valuation packet.
- `GroupTheory/HalfDifferenceCocycle.lean` verifies the cocycle identity for
  `a_g=(ell-g·ell)/2` and its restriction at an element acting by minus one.
  The field-theoretic existence of the required halves remains a separate input.
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

All six files build in the full project and use no `sorry` or new axioms.

## Mathematically verified manuscript advances

0. A general fixed-packet lemma is now isolated: if a connected maximal-rank
   subgroup H has neutral H1-image after every finite extension, the maximal-
   torus fixed locus in the twisted reduction variety is finite etale of degree
   [W(G):W(H)], and every one of its residue fields splits the torsor. Applied
   to D8, A2E6, and A4A4 in E8, this yields effective splitting cycles of
   degrees 135, 2240, and 48384 and an odd splitting field of degree at most
   135. The geometric proof is informal/source-audited; its numerical
   consequences are kernel checked in E8/WeylIndexPacket.lean.
1. The one-sided wonderful compactification has the same point fields as the
   E8 torsor. Its fixed locus consists of Weyl-indexed copies of the twisted
   Borel variety, with attracting rank `length(w) + rightDescent(w)`.
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
   countermodel to formal two-gauge gluing. It is not an E8 counterexample.
6. Conditional on the reported D4-root action, E8 lattice gluing forces
   diagonal triality and pairs the two degree-eight Allen algebras over the
   common cubic field. Common Allen index at most two is eliminated by the
   published trialitarian theorem; only paired indices four and eight remain
   unexcluded, and their existence is not asserted.

## Citation-dependent input

The broad proper-semisimple normalizer-source theorem is a complete formal
deduction from the statement attributed to Gille, LNM 2238, Corollary 9.3.6:
every non-almost-abelian E8 form under the stated separable-cohomological-
dimension hypotheses is split. The exact text of that corollary was not
available in the audited artifact or public preview. Every subsystem-envelope
neutralization using this result remains explicitly conditional until the exact
source statement and hypotheses are inserted.

The half-spin source-image theorem does not depend on this broad input: the
twist contains a split central `mu_2`, and Gille's separately corroborated
torsion criterion (Corollary 9.3.7) neutralizes the ambient E8 class.

## Unreproduced computer-assisted input

The manuscript reports, but the supplied artifact does not contain, the GAP,
CTblLib, TomLib, and root-action scripts needed for:

- the subgroup counts `11171 -> 313 -> 303` and all gcd-one orbit assertions;
- the `303 = 150 + 153 -> 31` perfect-core compression;
- nonsplitting of all 31 central Weyl lifts; and
- the binary subsystem-orbit and triality tests.

Formal deductions from these data have been checked, but the numerical premises
must remain conditional until the exact scripts, package versions, row maps,
fusion witnesses, and raw output are committed and rerun.

## Open targets

No counterexample and no proof of the E8 case is currently certified. The
smallest conditional finite target is constrained two-gauge factorization for
an actual `2.A5` Weyl lift. The geometric global target is odd-degree (or
index-one) effectivity on the E8 twisted Borel variety. The full finite-etale
kernel-norm statement over all fields in scope is equivalent to E8 Serre II and
must not be advertised as an independently proved shortcut.

## Checkpoints

- `39351922`: coprime restriction detection.
- `504301ef`: generated-subgroup common-fixed-point theorem.
- `d97f23fe`: A8 normalizer Bezout detection.
