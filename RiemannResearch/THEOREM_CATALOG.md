# Theorem catalog

This catalog is an orientation layer. Lean source files and successful builds
remain authoritative.

For the theorem-by-theorem mathematical audit of the E8 Serre II manuscript,
including citation-dependent and unreproduced computer-assisted claims, see
`E8/SERRE_II_PROOF_AUDIT.md`.

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
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equality of rational-point predicates implies equality of the set-gcd indices of all finite point-field degrees | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.closedPointIndex_eq_pointFieldIndex` | `RiemannResearch.AlgebraicGeometry.PointFields` | Identifies the traditional closed-point gcd with the splitting-field gcd under the residue-field and closed-image divisibility hypotheses | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.point_iff_of_fixedLocus_coproduct` | `RiemannResearch.AlgebraicGeometry.PointFields` | A proper-limit map, coproduct fixed locus, and fixed-component inclusion give equality of point fields | Kernel checked |
| `RiemannResearch.GroupTheory.eq_zero_of_coprime_restrictions` | `RiemannResearch.GroupTheory.CoprimeRestriction` | Two additive restriction maps satisfying coprime restriction--corestriction index formulas jointly detect zero | Kernel checked |
| `RiemannResearch.GroupTheory.fixed_of_fixed_on_join_eq_top` | `RiemannResearch.GroupTheory.GeneratedFixedPoint` | A common point fixed by two generating subgroups is fixed by the whole group; separate local fixed points are not enough | Kernel checked |
| `RiemannResearch.GroupTheory.exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one` | `RiemannResearch.GroupTheory.PGroupFixedPoints` | A finite `p`-group acting additively on finite `V` has a nonzero fixed point when `Nat.card V ≢ 1 [MOD p]` | Kernel checked |
| `RiemannResearch.E8.a8Normalizer_bezout` | `RiemannResearch.E8.A8NormalizerArithmetic` | Verifies the exact identity `-27·15 + 2·35 + 336 = 1` | Kernel checked |
| `RiemannResearch.E8.eq_zero_of_a8_annihilators` | `RiemannResearch.E8.A8NormalizerArithmetic` | An abelian class killed by the three A8 cover degrees 15, 35, and 336 is zero | Kernel checked |
| `RiemannResearch.E8.weylIndexPacket_bezout` | `RiemannResearch.E8.WeylIndexPacket` | Verifies `-73·135 + 26·2240 - 48384 = 1` for the three maximal-rank reduction degrees | Kernel checked |
| `RiemannResearch.E8.weylIndexPacket_gcd` | `RiemannResearch.E8.WeylIndexPacket` | The three packet degrees have gcd one | Kernel checked |
| `RiemannResearch.E8.exists_odd_of_sum_eq_135` | `RiemannResearch.E8.WeylIndexPacket` | A finite family of degrees summing to 135 contains an odd degree | Kernel checked |
| `RiemannResearch.E8.eq_zero_of_weylIndexPacket_annihilators` | `RiemannResearch.E8.WeylIndexPacket` | An abelian class killed by 135, 2240, and 48384 is zero | Kernel checked |
| `RiemannResearch.E8.exists_bounded_weylIndexPacket_residue` | `RiemannResearch.E8.WeylIndexPacket` | Every residue modulo 135 is represented by `2240a+48384b` with `a<27`, `b<5` | Kernel checked by finite decision |
| `RiemannResearch.E8.weylIndexPacket_residue_bound` | `RiemannResearch.E8.WeylIndexPacket` | The residue representatives are bounded by 251776 | Kernel checked |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.OmegaEightPlusTwo` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.OmegaEightPlusTwo` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.E8.attractingRank_properties` | `RiemannResearch.E8.WonderfulFixedLocus` | The length-plus-descent formula and Coxeter complement identities imply unique zero rank and rank duality | Kernel checked |
| `RiemannResearch.E8.e8AttractingRank_eq_zero_iff` | `RiemannResearch.E8.WonderfulFixedLocus` | On Mathlib's E8 Coxeter group, length plus the number of right descents vanishes exactly at the identity | Kernel checked unconditionally |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Conditional research reductions

These declarations are complete proofs of implications, but they are not
unconditional proofs of the motivating named theorems.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | From the inputs listed below, proves parts (i)--(iii), nonabelianness of the simple core, and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked implication; open obligations remain |
| `RiemannResearch.E8.universalFixedLocusAndSplittingField` | `RiemannResearch.E8.WonderfulFixedLocus` | From the inputs listed below, proves the assembled fixed-locus, motivic, point-field, splitting-spectrum, and set-gcd-index conclusions | Kernel checked implication; open obligations remain |

### Open obligations: `quasisimpleCoreOfFullWeylDescent`

| Hypothesis binder | Required mathematical input | Provider / status |
|---|---|---|
| `restriction_preserves_neutrality` | Restriction from the base field preserves neutrality | **Open** |
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
| `rank_formula` | Chamber-normalized attracting-rank formula | **Open** |
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
