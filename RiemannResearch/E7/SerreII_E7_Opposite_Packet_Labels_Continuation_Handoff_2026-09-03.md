# Full Serre II / E7 continuation handoff — opposite packet labels

Date: 3 September 2026

## Outcome

The hard E7 construction has been reduced to a strictly weaker dual-quartic
incidence than the previous aligned-layer target.

Put

    α = q₂ + q₃,
    β = q₁ + q₂.

For a Tignol cross-orbit dual quartic pair (U, check U), it is sufficient that

    β|U = 0,
    α|check U = 0.

This directly constructs the required corestriction-linked quaternion lift and,
with the existing common-discriminant constructor, proves effectivity of the
original labelled E7 Brauer packet. No assumption that a prescribed quadratic
field splits q₂ is needed, and q₁ need not split separately on U.

## Direct proof

The fixed-pair Tignol identity is represented by

    cor_M/F(ker(res_U)) = ker(res_checkU).

Hence α|checkU = 0 supplies r with

    r|U = 0,
    cor_M/F(r) = α.

Since β|U = 0, both r and r + res_M/F(β) lie in the quadratic-layer kernel.
The kernel-index bound makes both quaternion classes. They are precisely the
linked pair needed by the existing effectivity bridge.

The new Lean declarations are:

- hasCorestrictionLinkedQuaternionLift_of_oppositeLabelledDualQuartic
- BoundaryRealization.isEffective_of_oppositeLabelledDualQuarticSplitting

## Exact LLT residual

Apply Lam--Leep--Tignol to

    B = q₂ + q₃,
    Q = q₁,

and choose a quadratic maximal subfield M/F of Q. Over a field with I³(F) = 0,
LLT Theorems 4.16 and 5.12 yield a quartic 2-extension L/F of discriminant M
that splits B.

In the index-eight row L can be neither biquadratic nor cyclic. Its Galois hull
is therefore D₈ of degree eight. Let U = check L be its Tignol cross-orbit dual.
Then

    q₁|U = 0,
    (q₂ + q₃)|L = 0.

The new endpoint asks for (q₁ + q₂)|U = 0. Because q₁|U = 0, this is exactly

    q₂|U = 0.

After the half-spin reflection, the alternate sufficient condition is q₃|U=0.
Thus the remaining field theorem is the single disjunction

    q₂|U = 0  or  q₃|U = 0

for a suitable member of the LLT family.

Lean formalizes the disjunctive endpoint as

- hasCorestrictionLinkedQuaternionLift_of_dualSplitting_and_eitherCliffordSide
- hasCorestrictionLinkedLiftForTriple_of_firstAndEitherRemainingSplit

## No-go reductions

Lean proves that a quadratic extension cannot split q₁ and q₂ simultaneously
when q₃ has index at most two and

    index(q₁ + q₂ + q₃) = 8.

Otherwise q₁+q₂ has index at most two and index submultiplicativity bounds the
total index by four. This shows that the previous prescribed-middle condition
is actually incompatible with the LLT orientation in the hard row.

The declaration is

- totalIndexEight_excludes_quadratic_commonSplitter_of_thirdIndexTwo

Same-packet diagonal translation also cannot improve the incidence. Every
representative has the affine form

    (β + s, s, α + s).

If M splits the middle entry s, then upper-layer splitting of β+s is exactly
splitting of β itself. Setting s=q₁ forces the third entry to be the
index-eight total class, so it cannot be quaternion.

The corresponding declarations are:

- samePacket_middleSplitter_firstSide_iff_packetLabelSplits
- samePacket_middle_eq_first_forces_third_eq_total
- no_quaternion_samePacket_rep_with_first_as_middle_of_totalIndexEight

## Embedded common slot

In LLT coordinates

    M = F(sqrt(m)),
    z = b + 2c sqrt(m),
    f = m e² + b e + c²,

put u = e sqrt(m) - c. Lean proves

    f = u² + e z.

The Steinberg relation then gives

    (q₁)_M = (-e,f) = (z,f).

If r=(z,y) and cor(r)=α, the linked complement is explicitly (z,yf). The
earlier norm identity proves cor(z,f)=0. Thus the final quaternion factors are
completely explicit once the dual-quartic incidence is supplied.

The new declaration is

- llt_embeddedSlot_polynomial_identity

## Packet universality

Lean also proves:

    IsBalanced(P) iff P = ofTriple(q₁,q₂,q₃) for some q₁,q₂,q₃,

and the corresponding universal-property equivalence. Therefore balance is the
entire additive content of a packet. Any proof of the remaining incidence must
use field geometry, norm structure, or genuine trialitarian realization rather
than a further exponent-two group identity.

The declarations are:

- BrauerPacket.isBalanced_iff_exists_ofTriple
- BrauerPacket.forall_ofTriple_iff_forall_balanced

## Verification

Both affected Lean modules elaborate successfully. All eleven principal new
declarations pass targeted verification with source scanning enabled, no
warnings, and only the standard propext/Quot.sound foundations. No sorry,
admit, local axiom, unsafe declaration, or native shortcut was introduced.

The theorem catalog has been updated with every new reduction.

## Literature boundary

No published theorem was found that forces the remaining cross-orbit
synchronization for every balanced (4,4,4) packet.

- LLT Theorem 5.12 controls one biquaternion label with one prescribed
  discriminant, but does not synchronize a second label on the dual quartic.
- Tignol Corollary 3.5 and Example 5.3 solve the relative Brauer fibre for a
  fixed dual pair, not existence of a suitable pair.
- Sivatski Proposition 4 gives a common biquadratic splitter when the sum has
  index two; here the sum has index four.
- Dolphin--Quéguiner-Mathieu Proposition 5.4 constructs triality from an
  already supplied four-quaternion affine square; their converse coverage does
  not include the hard (4,4,4) row.
- A degree-four unitary-centralizer construction is excluded because its
  unitary discriminant algebra is quaternion, forcing one Clifford component
  to have index at most two.

No genuine field-theoretic counterexample was found.

## Primary sources

- Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*:
  https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf
- Tignol, *Tores associés à une algèbre étale quartique*:
  https://arxiv.org/html/1704.04072v1
- Stacks Project, Brauer groups, Tag 074X:
  https://stacks.math.columbia.edu/tag/074X
- Dolphin--Quéguiner-Mathieu, trialitarian triples:
  https://arxiv.org/pdf/1905.12526
- Sivatski, common splitting fields:
  https://www.math.uni-bielefeld.de/lag/man/249.pdf
- Becher--Grenier-Boley--Tignol, unitary discriminant algebras:
  https://arxiv.org/html/2008.08953v3/
- Bingöl--Quéguiner-Mathieu, trialitarian isotropy:
  https://arxiv.org/html/2312.10442v2

## Next target

Study the LLT parameter space of quartic splitters L of q₂+q₃ and prove or
disprove that its dual member U=check L can be chosen with

    q₂|U = 0  or  q₃|U = 0.

Independent existence results for the two splitting loci may not be combined
unless the quartics are proved to be the same cross-orbit dual pair.
